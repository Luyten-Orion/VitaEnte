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

import ./[
  sparsesets,
  core
]

# Exporting core is important
export sparsesets, core

proc sparseSetFieldName(field: NimNode): string =
  var name = field.repr
  name[0] = toLowerAscii(name[0])
  name & "Components"

proc getTupleBody(n: NimNode): NimNode =
  case n.kind
  of nnkTupleConstr, nnkTupleTy:
    return n
  of nnkSym:
    return getTupleBody(n.getImpl)
  of nnkTypeDef:
    return getTupleBody(n[2])
  of nnkBracketExpr:
    if n[0].kind == nnkSym and n[0].repr in ["typeDesc", "type"]:
      return getTupleBody(n[1])
    else:
      error("Expected a tuple type, got generic: " & n.repr)
  else:
    error("Expected a tuple type, got " & n.repr)

macro genSparseSetField*[T](components: typedesc[T]): untyped {.used.} =
  ## Impl detail, do not use.
  let tupleBody = getTupleBody(components.getTypeImpl)

  result = newNimNode(nnkTupleTy)
  for child in tupleBody:
    var typ: NimNode
    if child.kind == nnkIdentDefs:
      typ = child[1]          # named field
    else:
      typ = child             # unnamed field (the type itself)

    # Allow common type nodes; generics may still be limited
    if typ.kind notin {nnkSym, nnkIdent, nnkBracketExpr}:
      error("Generic components not fully supported yet: " & typ.repr)

    let fieldName = ident(sparseSetFieldName(typ))
    let fieldType = newNimNode(nnkBracketExpr).add(bindSym"SparseSet", typ)
    result.add(newIdentDefs(fieldName, fieldType))

type
  ConcurrentWorldAccessDefect* = object of Defect
  MissingComponentDefect* = object of Defect

  World*[T: tuple] = object
    entities*: seq[Entity]
    # Dead ids, ready for recycling. Each entry carries the generation its id
    # should wear when reborn (its slot in `entities` already wears that value).
    freeList*: seq[Entity]
    sparseSets*: genSparseSetField(T)
    # Reentrancy tripwire only; worlds stay thread-owned
    lock*: bool

  Not*[T] = distinct T
  Mut*[T] = distinct T

  # TODO: Make a more efficient command buffer
  Command*[T: tuple] = proc (w: var World[T]) {.closure.}
  CommandBuffer*[T: tuple] = seq[Command[T]]

# distinctBase resolves through every distinct layer at once, so a Not/Mut
# wrapper around a distinct component would land on the base's sparse set
# instead (or find nothing at all). componentType unwraps the single wrapper
# layer it needs and stops there.
template componentType[T](x: typedesc[Mut[T]]): untyped = T
template componentType[T](x: typedesc[Not[T]]): untyped = T
template componentType[T](x: typedesc[T]): untyped = T

proc findComponentIndex(tupleType: NimNode, compType: NimNode): int =
  var i = 0

  for child in getTupleBody(tupleType):
    let typ = if child.kind == nnkIdentDefs: child[1] else: child
    if sameType(compType, typ):
      return i
    inc i

  error("Component type not found", compType)

macro accessSparseSet*[T: tuple, U](w: var World[T], _: typedesc[U]): var SparseSet[U] =
  let
    tupleType = nnkTupleConstr.newTree(w.getType[1][1..^1])
    idx = findComponentIndex(tupleType, U.getTypeInst)
  result = quote: `w`.sparseSets[`idx`]

macro accessSparseSet*[T: tuple, U](w: World[T], _: typedesc[U]): SparseSet[U] =
  let
    tupleType = nnkTupleConstr.newTree(w.getType[1][1..^1])
    idx = findComponentIndex(tupleType, U.getTypeInst)
  result = quote: `w`.sparseSets[`idx`]

template checkLive[T: tuple](w: World[T], e: Entity) =
  # A dead handle can only get worse once it's inside a sparse set, so the
  # world itself has to veto it
  if not w.live(e):
    raise newException(StaleEntityDefect,
      "component op on dead entity, id " & $e.id)

template addComponent*[T: tuple, U](w: World[T], e: Entity, component: U) =
  checkLive(w, e)
  accessSparseSet(w, typeof(U)).add(e, component)

template addComponent*[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) =
  checkLive(w, e)
  accessSparseSet(w, typeof(U)).add(e)

template delComponent*[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) {.used.} =
  accessSparseSet(w, typeof(U)).del(e)

template hasComponent*[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]): bool =
  when U is Mut:
    e in accessSparseSet(w, componentType(typeof(U)))
  elif U is Not:
    not (e in accessSparseSet(w, componentType(typeof(U))))
  else:
    e in accessSparseSet(w, typeof(U))

#template hasComponent[T: tuple, U](w: World[T], e: Entity, _: U): bool =
#  hasComponent(w, e, typeof(U))

template getComponent*[T: tuple, U](w: var World[T], e: Entity, _: typedesc[U]): var U =
  accessSparseSet(w, typeof(U))[e]

template getComponent*[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]): U =
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
  try:
    for command in cb:
      command(w)
    cb.setLen(0)
  finally:
    w.lock = false

# Ids are slot indices, the entities seq never shrinks, and despawned slots
# wait at gen 0 to be recycled. Stale handles can never match a live entity
# again, so spawn/despawn are also safe inside command buffers (nothing
# shifts under a running sweep)
proc live*[T: tuple](w: World[T], e: Entity): bool {.inline.} =
  e.id < w.entities.len.uint32 and w.entities[e.id.int].gen == e.gen

proc spawn*[T: tuple](w: var World[T], count: Natural = 1): seq[Entity] =
  when sizeof(int) == 8:
    assert w.entities.len + count <= high(uint32).int
  else:
    {.error: "Only 64-bit builds are supported."}

  result = newSeq[Entity](count)
  for i in 0..<count:
    if w.freeList.len > 0:
      let recycled = w.freeList.pop()
      w.entities[recycled.id.int].revive(recycled.gen)
      result[i] = recycled
    else:
      result[i] = Entity.init(uint32(w.entities.len))
      w.entities.add(result[i])

proc despawnOne*[T: tuple](w: var World[T], e: Entity) =
  if not w.live(e): return # unknown or stale id is a no-op
  w.freeList.add(w.entities[e.id.int].kill()) # carries its next generation
  for name, field in w.sparseSets.fieldPairs:
    field.del(e) # no-op if not present

proc despawn*[T: tuple](w: var World[T], entities: seq[Entity]) =
  for e in entities:
    w.despawnOne(e)

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
    candidateSetInit = false
  unrollRange(0..<tupleLen(components)):
    type Comp = components.get(idx)
    when not (Comp is Not):
      hasPositive = true
      type TupBase = componentType(Comp)
      privateAccess(SparseSet[TupBase])
      let currentSet = accessSparseSet(w, TupBase).dmap
      if not candidateSetInit:
        candidateSet = currentSet
        candidateSetInit = true
      elif candidateSet.len > 0:
        # Intersect
        var newSet: seq[Entity]
        for e in candidateSet:
          if e in currentSet:
            newSet.add(e)
        candidateSet = newSet
  if not hasPositive: candidateSet = w.entities

  unrollRange(0..<tupleLen(components)):
    type Comp = components.get(idx)
    when Comp is Not:
      type TupBase = componentType(Comp)
      privateAccess(SparseSet[TupBase])
      let negativeSet = accessSparseSet(w, TupBase).dmap
      var newSet: seq[Entity]
      for e in candidateSet:
        if e notin negativeSet:
          newSet.add(e)
      candidateSet = newSet

  result = candidateSet


macro callSystemFn(
  w: var World[tuple],
  e: Entity,
  components: typedesc[tuple],
  f: proc
): CommandBuffer[tuple] =
  let
    fnType = f.getTypeImpl
    formal = fnType[0]

  var paramTypes: seq[NimNode]

  for i in 1 ..< formal.len:
    paramTypes.add(formal[i][1])

  if paramTypes.len == 0:
    error("System proc must take at least one parameter (`Entity`)")

  let fSym = genSym("f")
  var call = newCall(fSym, e)

  for i in 1..<paramTypes.len:
    let ptype = paramTypes[i]
    let baseType = if ptype.kind == nnkVarTy: ptype[0] else: ptype
    call.add newCall(
      bindSym"getComponent",
      w,
      e,
      newCall(bindSym"typeof", baseType)
    )

  result = newNimNode(nnkBlockStmt).add(
    newEmptyNode(),
    newStmtList(
      newLetStmt(fSym, f),
      call
    )
  )

macro runSystem*(
  w: var World[tuple],
  components: typedesc[tuple],
  orderedIteration: bool,
  f: proc
) =
  let worldTuple = w.getTypeInst[1]
  result = genAst(w, f, components, orderedIteration, worldTuple):
    var
      entities = filterEntities(w, components)
      cmdBuf: CommandBuffer[worldTuple]
    when orderedIteration:
      entities.sort()
    for e in entities:
      cmdBuf &= callSystemFn(w, e, components, f)
    w.apply(cmdBuf)

template runSystem*(
  w: var World[tuple],
  components: typedesc[tuple],
  f: proc
) = runSystem(w, components, false, f)
