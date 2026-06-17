## A minimal sparse ECS implementation for Nimskull

import std/[
  typetraits,
  algorithm,
  sequtils,
  strutils,
  genasts,
  macros,
  tables
]

from std/sugar import `=>`

import vitaente/[
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

macro genSparseSetField(components: typedesc[tuple]): untyped {.used.} =
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

macro accessSparseSet*(w: World[tuple], U: typedesc): SparseSet[U] =
  block checkComponentExists:
    for typ in typToTup(w):
      if U.getType[1] == typ:
        break checkComponentExists
    
    error("There is no `" & `U`.getType[1].repr & "` component in `" & `w`.getTypeInst.repr & "`", callsite())

  let sparseSet = sparseSetFieldName(U.getType[1])

  result = newNimNode(nnkDotExpr).add(
    newNimNode(nnkDotExpr).add(
      w,
      ident("sparseSets"),
    ),
    ident(sparseSet)
  )

template addComponent[T: tuple, U](w: World[T], e: Entity, component: U) =
  accessSparseSet(w, typedesc[U]).add(e, component)

template addComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) =
  accessSparseSet(w, typedesc[U]).add(e)

template delComponent[T: tuple, U](w: World[T], e: Entity) =
  accessSparseSet(w, U).del(e)

template hasComponent[T: tuple, U](w: World[T], e: Entity): bool =
  e in accessSparseSet(w, U)

template getComponent[T: tuple, U](w: World[T], e: Entity): U =
  accessSparseSet(w, U)[e]

macro addComponents*(
  cb: CommandBuffer[tuple],
  e: Entity,
  components: varargs[untyped]
): untyped =
  var T = typToTup(cb)
  result = genAst:
    cb.add (proc(w: var World[T]) =
      for component in components:
        w.addComponent(e, component))

macro delComponents*(
  cb: CommandBuffer[tuple],
  e: Entity,
  components: varargs[untyped]
): untyped =
  var T = typToTup(cb)
  result = genAst:
    cb.add (proc(w: var World[T]) =
      for component in components:
        w.delComponent(e, component))

proc apply*[T: tuple](w: var World[T], cb: CommandBuffer[T]) =
  # Uhhh how to wait?
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
  w.lock = true
  for command in cb:
    command(w)
  cb.setLen(0)
  w.lock = false

proc spawn*(w: var World, count: Natural = 1): seq[Entity] =
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

proc despawn*(w: var World, entities: seq[Entity]) =
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

proc smallestSetOfEntities(w: NimNode, U: NimNode): NimNode =
  var c = 0

  for typ in typToTup(U):
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Not":
      continue
    inc c

  if c < 1:
    error("System requires at least one iterable component.")
    return

  let smallestSetSym = genSym("smallestSet")

  result = newNimNode(nnkStmtList).add(
    newNimNode(nnkVarSection).add(
      newIdentDefs(
        smallestSetSym,
        (quote do: ptr seq[Entity]),
        newNilLit()
      )
    ),
    newNimNode(nnkIfStmt)
  )

  for typ in typToTup(U):
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Not":
      continue
      
    var r = genAst:
      if smallestSetSym == nil or smallestSetSym[].len > accessSparseSet(w, typ).len:
        smallestSetSym = addr accessSparseSet(w, typ).dmap
    
    while r.kind != nnkElifBranch:
      r = r[0]

    result[^1].add(r)

  result.add newNimNode(nnkIfStmt).add(
    newNimNode(nnkElifBranch).add(
      newNimNode(nnkInfix).add(
        ident"==",
        smallestSetSym,
        newNilLit()
      ),
      newStmtList(
        newNimNode(nnkVarSection).add(
          newIdentDefs(
            smallestSetSym,
            (quote do: seq[Entity]),
            prefix(newNimNode(nnkBracket), "@")
          )
        )
      )
    )
  )

  result.add newNimNode(nnkDerefExpr).add(smallestSetSym)
    


proc isVoid(T: NimNode): bool =
  if T == void.getTypeInst:
    return true

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
  var
    excl: seq[NimNode]
    incl: seq[NimNode]
    condStmts: seq[NimNode]
    cond: NimNode

  for typ in typToTup(components):
    if typ.kind == nnkBracketExpr and typ[0] == bindSym"Not":
      excl.add(typ[1])
    else:
      incl.add(typ)

  for i in excl:
    condStmts.add prefix(
      newCall(
        bindSym"hasComponent",
        w,
        e,
        i
      ),
      "not"
    )
  
  for i in incl:
    condStmts.add newCall(
      bindSym"hasComponent",
      w,
      e,
      i
    )

  if condStmts.len > 0:
    cond = condStmts[0]
    for i in 1..condStmts.high:
      cond = infix(cond, "and", condStmts[i])
  else:
    cond = newLit(true)

  var fCall: NimNode
  if condStmts.len == 0:
    fCall = genAst: f(w, e)
  else:
    fCall = newNimNode(nnkCall)
    fCall.add(f)
    fCall.add(w)
    fCall.add(e)

    for i in incl:
      if i.isVoid():
        continue
      fCall.add newCall(
        bindSym"hasComponent",
        w,
        e,
        i
      )

  result = genAst:
    if cond:
      fCall

macro runSystem*(
  w: var World[tuple],
  components: typedesc[tuple],
  orderedIteration: bool,
  f: proc
) =
  var
    worldTuple = typToTup(w)
    componentsTuple = typToTup(components)

    fnTyp = makeSystemFnType(worldTuple, componentsTuple)
    smallestSet = smallestSetOfEntities(w, componentsTuple)

  result = genAst(f, fnTyp):
    when not compiles(fnTyp(f)):
      {.error: "`f` `" & $typeof(f) & "` is not of type: `" & $fnTyp & "`".}
    var
      entities = smallestSet
      cmdBuf: CommandBuffer[worldTuple]
    if orderedIteration:
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

  # Optional: a tag component (no data)
  # In Nim, use `void` for tags
  IsAlive = distinct void

# 2. Declare the tuple of all components your world can contain
# Order doesn't matter, but must list every component type you'll use.
type MyComponents = (Position, Velocity, IsAlive)

# 3. Create the world
var world = World[MyComponents]()

# 4. Spawn some entities
let e1 = world.spawn()[0]
let e2 = world.spawn()[0]
let e3 = world.spawn()[0]

# 5. Add components (data and tags)
world.addComponent(e1, Position(x: 0, y: 0))
world.addComponent(e1, Velocity(dx: 1, dy: 2))
world.addComponent(e1, IsAlive)  # tag, no value

world.addComponent(e2, Position(x: 10, y: 10))
world.addComponent(e2, Velocity(dx: -1, dy: 0))

world.addComponent(e3, Position(x: 5, y: 5))
# e3 has no Velocity or IsAlive

# 6. Define a system (using `runSystem` with a proc)
# The proc signature: (world, entity, var comp1, var comp2, ...) -> CommandBuffer[MyComponents]
# The system will run for every entity that has **all** the listed components.
# Here we iterate over entities with both Position and Velocity.
world.runSystem((Mut[Position], Mut[Velocity]),
  proc(e: Entity, pos: var Position, vel: var Velocity): CommandBuffer[MyComponents] =
    # Update position
    pos.x += vel.dx
    pos.y += vel.dy
)

# 7. After running, check results
for e in [e1, e2, e3]:
  if world.hasComponent(e, Position):
    let pos = world.getComponent(e, Position)
    echo "Entity ", e.id, " at (", pos.x, ", ", pos.y, ")"
  else:
    echo "Entity ", e.id, " has no Position"