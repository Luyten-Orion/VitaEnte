## A minimal sparse ECS implementation for Nimskull

import std/[
  importutils,
  typetraits,
  algorithm,
  sequtils,
  strutils,
  genasts,
  macros,
  tables
]

from std/sugar import `=>`

import ./[
  sparsesets,
  core
]

# Exporting core is important
export core

proc sparseSetFieldName(field: NimNode): string =
  var name = field.repr
  name[0] = toLowerAscii(name[0])
  name & "Components"

proc getTupleConstrNode(node: NimNode): tuple[node: NimNode, success: bool] =
  result = (node, false)

  while result.node.kind != nnkTupleConstr:
    if result.node.kind == nnkBracketExpr:
      result.node = result.node[1].getTypeImpl
      continue
    elif result.node.kind == nnkSym:
      result.node = result.node.getImpl
      continue
    elif result.node.kind == nnkTypeDef:
      result.node = result.node[2]
      continue
    else:
      return

  result.success = true

proc typToTup(n: NimNode): NimNode =
  if n.kind == nnkTupleConstr:
    return n
  result = newNimNode(nnkTupleConstr)
  for i in n.getType[1].getType[1..^1]:
    result.add i

var
  sparseSetCache {.compileTime.}: Table[LineInfo, NimNode]

macro genSparseSetField[T](components: typedesc[T]): untyped {.used.} =
  var (componentsNode, success) = getTupleConstrNode(components.getTypeImpl)

  if not success:
    error("Expected a tuple of components, such as `(Position, Velocity)`.")

  for component in componentsNode:
    if component.kind != nnkSym:
      error("`genSparseSetField` doesn't work with generics for now.")

  result = newNimNode(nnkTupleTy)

  for component in componentsNode:
    # TODO: Support generic types in the future
    result.add(newIdentDefs(
      ident(sparseSetFieldName(component)),
      newNimNode(nnkBracketExpr).add(
        bindSym"SparseSet",
        component
      )
    ))


type
  ConcurrentWorldAccessDefect* = object of Defect
  MissingComponentDefect* = object of Defect

  World*[T: tuple] = object
    entities*: seq[Entity]
    sparseSets*: genSparseSetField(T)
    # TODO: Replace with proper lock?
    lock*: bool

  Not*[T] = distinct T
  Mut*[T] = distinct T

  # TODO: Make a more efficient command buffer
  Command*[T: tuple] = proc (w: var World[T]) {.closure.}
  CommandBuffer*[T: tuple] = seq[Command[T]]

proc accessSparseSet*[T: tuple, U](w: var World[T], _: typedesc[U]): var SparseSet[U] =
  for _, sparseSet in w.sparseSets.fieldPairs:
    when sparseSet is SparseSet[U]:
      return sparseSet

  raise newException(MissingComponentDefect, "There is no `" & $U & "` component in `" & $T & "`")

proc accessSparseSet*[T: tuple, U](w: World[T], _: typedesc[U]): SparseSet[U] =
  for _, sparseSet in w.sparseSets.fieldPairs:
    when sparseSet is SparseSet[U]:
      return sparseSet

  raise newException(MissingComponentDefect, "There is no `" & $U & "` component in `" & $T & "`")

template addComponent[T: tuple, U](w: World[T], e: Entity, component: U) =
  accessSparseSet(w, typeof(U)).add(e, component)

template addComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) =
  accessSparseSet(w, typeof(U)).add(e)

template delComponent[T: tuple, U](w: World[T], e: Entity) =
  accessSparseSet(w, typeof(U)).del(e)

template hasComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]): bool =
  when T is Mut:
    e in accessSparseSet(w, typeof(U.distinctBase))
  elif T is Not:
    not (e in accessSparseSet(w, typeof(U.distinctBase)))
  else:
    e in accessSparseSet(w, typeof(U))

template hasComponent[T: tuple, U](w: World[T], e: Entity, _: U): bool =
  hasComponent(w, e, typeof(U))

template getComponent[T: tuple, U](w: var World[T], e: Entity, _: typedesc[U]): var U =
  accessSparseSet(w, typeof(U))[e]

template getComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]): U =
  accessSparseSet(w, typeof(U))[e]

macro addComponents*[T: tuple](
  w: World[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  result = newStmtList()

  for component in components:
    result.add quote do:
      `w`.addComponent(`e`, `component`)

macro delComponents*[T: tuple](
  w: World[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  result = newStmtList()

  for component in components:
    result.add quote do:
      `w`.delComponent(`e`, `component`)

macro addComponents*[T: tuple](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  var
    stmts = newStmtList()
    wSym = genSym("w")

  for component in components:
    stmts.add quote do:
      `wSym`.addComponent(`e`, `component`)

  result = quote do:
    `cb`.add (proc(`wSym`: var World[`T`]) =
      `stmts`
    )

macro delComponents*[T: tuple](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  var
    stmts = newStmtList()
    wSym = genSym("w")

  for component in components:
    stmts.add quote do:
      `wSym`.delComponent(`e`, `component`)

  result = quote do:
    `cb`.add (proc(`wSym`: var World[`T`]) =
      `stmts`
    )

proc apply*[T: tuple](w: var World[T], cb: var CommandBuffer[T]) =
  # Uhhh how to wait?
  if w.lock: raise newException(ConcurrentWorldAccessDefect, "Trying to apply while world is locked.")
  w.lock = true
  for command in cb:
    command(w)
  cb.setLen(0)
  w.lock = false

proc spawn*[T: tuple](w: var World[T], count: Natural = 1): seq[Entity] =
  # TODO: Make this check happen in release builds?
  if w.lock: raise newException(ConcurrentWorldAccessDefect, "Trying to spawn while world is locked.")
  w.lock = true
  when sizeof(int) == 8:
    assert w.entities.len + count <= high(uint32).int
  else:
    {.error: "Only 64-bit builds are supported."}

  result = newSeq[Entity](count)
  for i in 0..<count:
    result[i] = Entity.init(uint32(w.entities.len))
    w.entities.add(result[i])
  w.lock = false

proc despawn*[T: tuple](w: var World[T], entities: seq[Entity]) =
  if w.lock: raise newException(ConcurrentWorldAccessDefect, "Trying to despawn while world is locked.")
  w.lock = true
  for e in entities:
    # TODO: Find a better way to mass-delete entities, perhaps find all the indices and delete in reverse?
    w.entities.del(w.entities.find(e))
    for name, field in w.sparseSets.fieldPairs:
      field.del(e) # no-op if not present
    
  w.lock = false

proc makeSystemFnType*(
  a: NimNode, b: NimNode
): NimNode =
  result = newNimNode(nnkProcTy).add(
    newNimNode(nnkFormalParams).add(
      newNimNode(nnkBracketExpr).add(
        bindSym"CommandBuffer",
        a
      ),
      newIdentDefs(
        ident("e"),
        bindSym"Entity"
      )
    ),
    newEmptyNode()
  )

  var i = 0

  template getTyp(typ: NimNode): NimNode =
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Mut":
      newNimNode(nnkVarTy).add(typ[1])
    else:
      typ

  for typ in b:
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Not":
      continue
    inc i

    result[0].add(
      newIdentDefs(
        ident("a" & $i),
        getTyp(typ)
      )
    )

macro unrollRange(rn: static HSlice[int, int], body: untyped) =
  result = newNimNode(nnkStmtList)

  for i in rn:
    result.add newBlockStmt(
      genSym("i"),
      quote do:
        const idx = `i`
        `body`
    )
    

proc filterEntities*(w: World[tuple], components: typedesc[tuple]): seq[Entity] =
  var
    hasPositive = false
    candidateSet: seq[Entity]
  unrollRange(0..<tupleLen(components)):
    type Comp = components.get(idx)
    when not (Comp is Not):
      hasPositive = true
      type TupBase = (when Comp is Mut: Comp.distinctBase else: Comp)
      privateAccess(SparseSet[TupBase])
      let currentSet = accessSparseSet(w, TupBase).dmap
      if candidateSet.len == 0:
        candidateSet = currentSet
      else:
        # Intersect
        var newSet: seq[Entity]
        for e in candidateSet:
          if e in currentSet:
            newSet.add(e)
        candidateSet = newSet
  if not hasPositive:
    candidateSet = w.entities

  unrollRange(0..<tupleLen(components)):
    type Comp = components.get(idx)
    when Comp is Not:
      type TupBase = Comp.distinctBase
      privateAccess(SparseSet[TupBase])
      let negativeSet = accessSparseSet(w, TupBase).dmap
      var newSet: seq[Entity]
      for e in candidateSet:
        if e notin negativeSet:
          newSet.add(e)
      candidateSet = newSet

  result = candidateSet

proc isVoid(T: NimNode): bool =
  if T == Tag.getTypeInst:
    return true

  if T.kind == nnkBracketExpr and (T[0] == bindSym"Mut" or T[0] == bindSym"Not"):
    return false

  # Unfortunately, `getType` isn't very friendly to symbols
  if T.kind == nnkIdent: return false
  var Ti = T.getImpl

  if Ti.kind != nnkTypeDef: return false
  if Ti[2].kind != nnkDistinctTy: return false

  return Ti[2][0].isVoid


macro callSystemFn(
  w: var World[tuple],
  e: Entity,
  components: typedesc[tuple],
  f: proc
): CommandBuffer[tuple] =
  let fSym = genSym("f")
  var fCall = newCall(fSym, e)

  for typ in typToTup(components):
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Not":
      continue
    var base = if typ.kind == nnkBracketExpr and typ[0] == bindSym"Mut":
      typ[1]
    else:
      typ

    if base.isVoid():
      continue

    fCall.add newCall(
      bindSym"getComponent",
      w,
      e,
      newCall(bindSym"typeof", base)
    )

  result = genAst(fSym, fCall, f):
    let fSym = f
    fCall

macro runSystem*(
  w: var World[tuple],
  components: typedesc[tuple],
  orderedIteration: bool,
  f: proc
) =
  var
    worldTuple = getTupleConstrNode(w.getTypeInst[1]).node
    componentsTuple = getTupleConstrNode(components).node

  var fnTyp = makeSystemFnType(worldTuple, componentsTuple)

  result = genAst(w, f, fnTyp, worldTuple, componentsTuple, orderedIteration):
    when not compiles(fnTyp(f)):
      {.error: "`f` `" & $typeof(f) & "` is not of type: `" & $fnTyp & "`".}
    var
      entities = filterEntities(w, componentsTuple)
      cmdBuf: CommandBuffer[worldTuple]
    when orderedIteration:
      entities.sort()
    for e in entities:
      cmdBuf &= callSystemFn(w, e, componentsTuple, f)
    
    w.apply(cmdBuf)

template runSystem*(
  w: var World[tuple],
  components: typedesc[tuple],
  f: proc
) = runSystem(w, components, false, f)

type
  Position = object
    x, y: int

  Velocity = object
    dx, dy: int

  IsAlive = distinct Tag

type MyComponents = (Position, Velocity, IsAlive)

var world = World[MyComponents]()

let
  e1 = world.spawn()[0]
  e2 = world.spawn()[0]
  e3 = world.spawn()[0]
  e4 = world.spawn()[0]

world.addComponents(e1, Position(x: 0, y: 0), Velocity(dx: 1, dy: 2), IsAlive)
world.addComponents(e2, Position(x: 10, y: 10), Velocity(dx: -1, dy: 0))
world.addComponent(e3, Position(x: 5, y: 5))

world.runSystem((Mut[Position], Mut[Velocity]),
  proc(e: Entity, pos: var Position, vel: var Velocity): CommandBuffer[MyComponents] =
    pos.x += vel.dx
    pos.y += vel.dy
)

world.runSystem((Position,), true,
  proc(e: Entity, pos: Position): CommandBuffer[MyComponents] =
    echo "Entity ", e.id, " at (", pos.x, ", ", pos.y, ")"
)

world.runSystem((Not[Position],), true,
  proc(e: Entity): CommandBuffer[MyComponents] =
    echo "Entity has no Position component."
)