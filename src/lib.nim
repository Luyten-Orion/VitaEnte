## A minimal sparse ECS implementation for Nimskull

import std/[
  strutils,
  sequtils,
  genasts,
  macros,
  locks
]

type
  # Internal types
  ComponentInfo = object
    name: NimNode     # Field name in the tuple
    kind: NimNode # The enum kind
    typ: NimNode  # The type it represents

  # Public types
  Entity* = object
    id: uint32
    gen: uint32

  SparseSet*[T] = object 
    smap: seq[int32]   # Entity -> Dense
    dmap: seq[Entity]  # Dense -> Entity
    when T isnot void:
      components: seq[T] # Data

# SparseSet helpers
proc contains*[T](ss: SparseSet[T], e: Entity): bool {.inline.} =
  ## Check if an entity exists within this specific component set.
  assert e.id < uint32(ss.smap.len), "The `id` of Entity is bigger than what we support!"
  e.id in ss.smap

proc add*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Add a component to an entity. Adjusts sparse map lazily.
  if e in ss: return

  # Grow sparse map if necessary
  if e.id >= ss.smap.len.uint32:
    let oldLen = ss.smap.len
    ss.smap.setLen(e.id + 1)
    for i in oldLen .. e.id.int:
      ss.smap[i] = -1

  # Link Sparse -> Dense
  ss.smap[e.id] = ss.dmap.len.int32
  ss.dmap.add(e)
  
  when T isnot void:
    ss.components.add(val)

proc del*[T](ss: var SparseSet[T], e: Entity) =
  if e notin ss: return

  let 
    idxToRemove = ss.smap[e.id]
    lastEntity = ss.dmap[^1]

  ss.dmap[idxToRemove] = lastEntity
  ss.smap[lastEntity.id] = idxToRemove
  
  when T isnot void:
    ss.components[idxToRemove] = ss.components[^1]
    ss.components.setLen(ss.components.len - 1)

  ss.dmap.setLen(ss.dmap.len - 1)
  ss.smap[e.id] = -1

template `[]`*[T](ss: SparseSet[T], e: Entity): T =
  ## Access a component. Asserts existance in debug builds.
  assert e in ss, "Entity does not possess this component"
  ss.components[ss.smap[e.id]]

template `[]=`*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Update a component value.
  assert e in ss, "Entity does not possess this component"
  ss.components[ss.smap[e.id]] = val


proc grabUppercase(s: string): string = s.filter(isUpperAscii).join()

macro declareWorld*[T: tuple](
  worldName: static string,
  mt: static bool,
  _: typedesc[T]
): untyped =
  ## Declares the world type as well as various helpers for the world.
  ## - `worldName` is the name of the generated type and its corrosponding enum
  ## - `mt` is whether the world will be used in a multithreaded context
  ##   (so a `lock` field can be created for thread safety)
  ## - `T` is components, passed as a tuple type. Component names are generated
  ##   from the tuple field names, with the corrosponding type.
  let 
    tupleTy = T.getTypeImpl
    enumName = ident(worldName & "ComponentKind")
    worldTy = ident(worldName)
    sparseSetTy = bindSym"SparseSet"
    prefix = grabUppercase(worldName).toLowerAscii
  
  var components: seq[ComponentInfo]

  for i in 0..<tupleTy.len:
    let 
      f = tupleTy[i]
      fName = f[0].strVal
      kindName = ident(prefix & "c" & fName[0].toUpperAscii() & fName[1..^1])
    
    components.add ComponentInfo(
      name: f[0],
      kind: kindName,
      typ: f[1]
    )

  if components.len == 0:
    error("A World requires at least one component to justify its existence.", tupleTy)

  let enumFields = newNimNode(nnkEnumTy).add(newEmptyNode())
  for c in components:
    enumFields.add c.kind

  let
    recList = newNimNode(nnkRecList).add(
      newIdentDefs(ident("generations"), genAst(seq[uint32])),
      newIdentDefs(ident("freeIdxs"),    genAst(seq[uint32])),
      newIdentDefs(ident("sigs"),        genAst(enumName, seq[set[enumName]]))
    )

    worldObj = newNimNode(nnkObjectTy).add(
      newEmptyNode(),
      newEmptyNode(),
      recList
    )

  if mt:
    recList.add(newIdentDefs(
      ident("wlock"),
      bindSym"Lock"
    ))

  for c in components:
    recList.add newIdentDefs(
      c.name, 
      newNimNode(nnkBracketExpr).add(sparseSetTy, c.typ)
    )

  result = genAstOpt(
    {kDirtyTemplate}, enumName, enumFields, worldTy, worldObj, isMtWorld=mt
  ):
    type
      enumName* = enumFields
      worldTy* = worldObj

    proc spawn*(w: var worldTy): Entity =
      ## Creates or reuses a dead entity in the world.
      var id = 0'u32

      when isMtWorld:
        w.wlock.acquire()

      if w.freeIdxs.len > 0:
        id = w.freeIdxs.pop()
      else:
        id = w.generations.len.uint32
        w.generations.add(0)
        w.sigs.add({})
      
      when isMtWorld:
        w.wlock.release()

      result = Entity(id: id, gen: w.generations[id])
      inc w.generations[id]

    proc contains*(w: worldTy, e: Entity): bool {.inline.} =
      e.id < w.generations.len.uint32 and e.gen == w.generations[e.id]

  echo treeRepr(result)
  echo repr(result)


declareWorld("Test", true, tuple[a: int, b, c: string])