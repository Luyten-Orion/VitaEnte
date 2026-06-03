## A minimal sparse ECS implementation for Nimskull

import std/[
  typetraits,
  strutils,
  macros,
  tables
]

import vitaente/[
  core
]

type
  SparseSet*[T] = object
    smap: seq[int]       # Entity -> Dense
    dmap: seq[Entity]   # Dense -> Entity
    when T isnot void or T.distinctBase isnot void:
      components: seq[T] # Data

const Sentinel = int(uint32.high)

proc contains*[T](ss: SparseSet[T], e: Entity): bool {.inline.} =
  ## Check if the entity is in the SparseSet
  assert ss.smap.len < Sentinel
  int(e.id) < ss.smap.len and ss.smap[e.id] != Sentinel

# TODO: Add a simple guard that you can't add duplicate entities
template sparseAddImpl(ss: var SparseSet, e: Entity, body) =
  if e in ss: return

  # Init empty slots with the sentinel
  if int(e.id) >= ss.smap.len:
    let oldLen = ss.smap.len
    ss.smap.setLen(int(e.id) + 1)
    for i in oldLen..<int(e.id):
      ss.smap[i] = Sentinel

  # Map the Entity ID to the current end of the dense array
  ss.smap[e.id] = ss.dmap.len
  ss.dmap.add(e)
  body

proc add*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Add a component to an entity.
  when T is void or T.distinctBase is void:
    # This shouldn't compile anyway
    {.error: "Can't accept a void value when a value is required.".}

  sparseAddImpl(ss, e):
    ss.components.add(val)

proc add*[T](ss: var SparseSet[T], e: Entity) =
  ## Add a 'tag' component (no data) to an entity.
  when T isnot void or T.distinctBase isnot void:
    {.error: "Can't accept a value when no value is required.".}
  sparseAddImpl(ss, e):
    discard

proc del*[T](ss: var SparseSet[T], e: Entity) =
  ## Swap-and-pop entity deletion.
  if e notin ss: return

  let 
    # TODO: Raise an IndexDefect
    idxToRemove = ss.smap[e.id]
    lastEntity = ss.dmap[^1]

  ss.dmap[idxToRemove] = lastEntity
  ss.smap[lastEntity.id] = idxToRemove
  
  when T isnot void or T.distinctBase isnot void:
    ss.components[idxToRemove] = ss.components[^1]
    ss.components.setLen(ss.components.len - 1)

  ss.dmap.setLen(ss.dmap.len - 1)
  ss.smap[e.id] = Sentinel

template `[]`*[T](ss: var SparseSet[T], e: Entity): var T =
  ## Direct access to component data.
  when T is void or T.distinctBase is void:
    {.error: "Cannot access void value in a SparseSet that requires data."}
  assert e in ss, "Attempted to access non-existent component for Entity " & $e.id
  ss.components[ss.smap[e.id]]

template `[]`*[T](ss: SparseSet[T], e: Entity): T =
  ## Direct access to component data.
  when T is void or T.distinctBase is void:
    {.error: "Cannot access void value in a SparseSet that requires data."}
  assert e in ss, "Attempted to access non-existent component for Entity " & $e.id
  ss.components[ss.smap[e.id]]

template `[]=`*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Direct update of component data.
  when T is void or T.distinctBase is void:
    # Should never be possible anyway
    {.error: "Cannot access void value in a SparseSet that requires data."}
  assert e in ss, "Attempted to assign to non-existent component for Entity " & $e.id
  ss.components[ss.smap[e.id]] = val

template len*[T](ss: SparseSet[T]): int = ss.dmap.len