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

macro genSparseSetField(components: typedesc[tuple]): untyped {.used.} =
  var componentsNode = components.getTypeImpl
  componentsNode.expectKind(nnkBracketExpr)
  if componentsNode[1].kind != nnkTupleConstr:
    error("`genSparseSetField` only works for unnamed tuples.")
  for component in componentsNode[1]:
    if component.kind != nnkSym:
      error("`genSparseSetField` doesn't work with generics for now.")

  result = newNimNode(nnkTupleTy)

  for component in componentsNode[1]:
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

  # TODO: Make a more efficient command buffer
  Command*[T: tuple] = proc (w: var World[T]) {.closure.}
  CommandBuffer*[T: tuple] = seq[Command[T]]

macro accessSparseSet*[T: tuple, U](w: World[T], _: typedesc[U]): SparseSet[U] =
  block checkComponentExists:
    for typ in T.getTypeInst:
      if U.getTypeInst == typ:
        break checkComponentExists
    
    error("There is no `" & `U`.getTypeInst.repr & "` component in `" & `T`.getTypeInst.repr & "`", callsite())

  let sparseSet = sparseSetFieldName(U.getTypeInst)

  result = newNimNode(nnkDotExpr).add(
    newNimNode(nnkDotExpr).add(
      w,
      ident("sparseSets"),
    ),
    ident(sparseSet)
  )

template addComponent[T: tuple, U](w: World[T], e: Entity, component: U) =
  accessSparseSet(w, U).add(e, component)

template addComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) =
  accessSparseSet(w, U).add(e)

template delComponent[T: tuple, U](w: World[T], e: Entity) =
  accessSparseSet(w, U).del(e)

template hasComponent[T: tuple, U](w: World[T], e: Entity): bool =
  e in accessSparseSet(w, U)

template getComponent[T: tuple, U](w: World[T], e: Entity): U =
  accessSparseSet(w, U)[e]

macro addComponents*[T: tuple, U](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  result = genAst:
    cb.add (proc(w: var World[T]) =
      for component in components:
        w.addComponent(e, component))

macro delComponents*[T: tuple, U](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
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
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
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
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
  w.lock = true
  for e in entities:
    # TODO: Find a better way to mass-delete entities, perhaps find all the indices and delete in reverse?
    w.entities.del(w.entities.find(e))
    for name, field in w.sparseSets.fieldPairs:
      field.del(e) # no-op if not present
    
  w.lock = false

macro makeSystemFnType*[T: tuple, U: distinct tuple](
  a: typedesc[T], b: typedesc[U]
): typedesc =
  result = newNimNode(nnkProcTy).add(
    newNimNode(nnkFormalParams).add(
      CommandBuffer[T].getTypeInst()
    )
  )

  var i = 0
  for typ in U.getTypeInst:
    if typ.kind == nnkBracketExpr and typ[0] == Not.getTypeInst():
      continue
    inc i

    result[0].add(
      newIdentDefs(
        ident("a" & $i),
        typ
      )
    )

macro smallestSetOfEntities[T: tuple, U: distinct tuple](w: var World[T], _: typedesc[U]): seq[Entity] =
  var c = 0

  for typ in U.getTypeInst:
    if typ.kind == nnkBracketExpr and typ[0] == Not.getTypeInst():
      continue
    inc c

  if c < 1:
    error("System requires at least one iterable component.")
    return

  let smallestSetSym = genSym("smallestSet")

  var result = newNimNode(nnkStmtList).add(
    newVarStmt(smallestSetSym, newLit(nil))
    newNimNode(nnkIfStmt)
  )

  for typ in U.getTypeInst:
    if typ.kind == nnkBracketExpr and typ[0] == Not.getTypeInst():
      continue
      
    var r = genAst:
      if smallestSetSym == nil or smallestSetSym[].len > accessSparseSet(w, typ).len:
        smallestSetSym = addr accessSparseSet(w, typ).dmap
    
    while r.kind != nnkElifBranch:
      r = r[0]

    result[^1].add(r)

  result.add genAst: smallestSetSym[]
    


proc isVoid(T: NimNode): bool =
  if T == void.getTypeInst:
    return true

  var Ti = T.getImpl

  if Ti.kind != nnkTypeDef: return false
  if Ti[2].kind != nnkDistinctTy: return false

  return Ti[2][0].isVoid


macro callSystemFn[T: tuple, U: distinct tuple](
  w: var World[T],
  e: Entity,
  components: varargs[typedesc],
  f: makeSystemFnType(T, U)
): CommandBuffer[T] =
  var
    excl: seq[NimNode]
    incl: seq[NimNode]
    condStmts: seq[NimNode]
    cmpts: seq[NimNode]
    cond: NimNode

  for typ in U.getTypeInst:
    if typ.kind == nnkBracketExpr and typ[0] == Not.getTypeInst():
      excl.add(typ[1])
    else:
      incl.add(typ)

  for i in excl:
    condStmts.add genAst(typ=i): not w.hasComponent(e, typ)
  
  for i in incl:
    condStmts.add genAst(typ=i): w.hasComponent(e, typ)

  if condStmts.len > 0:
    cond = condStmts[0]
    for i in 1..condStmts.high:
      cond = infix("and", cond, condStmts[i])
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
      fCall.add genAst(typ=i): w.getComponent(e, typ)

  result = genAst:
    if cond:
      fCall

macro runSystem*[T: tuple, U: distinct tuple](
  w: var World[T],
  components: tuple[U],
  orderedIteration: bool
  f: makeSystemFnType(T, U)
) =
  result = genAst:
    var
      entities = smallestSetOfEntities(w, U)
      cmdBuf: CommandBuffer[T]
    if orderedIteration:
      entities.sort()
    for e in entities:
      cmdBuf &= callSystemFn(w, e, components, f)
    
    w.apply(cmdBuf)

template runSystem*[T: tuple, U: distinct tuple](
  w: var World[T],
  components: tuple[U],
  f: makeSystemFnType(T, U)
) = runSystem(w, components, false, f)

