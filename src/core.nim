when sizeof(int) != sizeof(int64):
  # TODO: Look into making this work on 32-bit targets...? Maybe?
  {.error: "Only 64-bit builds are supported."}

type
  # Placeholder until unit type comes along
  Unit* = tuple[]

  Entity* = object
    id: uint32
    gen: uint16

# Simple constructor
template init*(T: typedesc[Entity], eId: T.id): T = T(id: eId, gen: 1)
# Recycled ids carry the gen they'll spawn with
template init*(T: typedesc[Entity], eId: T.id, eGen: T.gen): T = T(id: eId, gen: eGen)
# Read only fields
template id*(e: Entity): Entity.id = e.id
template gen*(e: Entity): Entity.gen = e.gen
# Sentinel entity
template sentinel*(T: typedesc[Entity]): T = T(id: high(T.id), gen: high(T.gen))

# Gen 0 is reserved for vacant slots, so a zero-initialised Entity starts dead
template deadGen*: uint16 = uint16(0)

# Bump the gen so old handles of this entity can never match a fresh spawn
proc advanceGen*(e: var Entity) {.inline.} =
  e.gen += 1
  if e.gen == deadGen: e.gen = 1 # hop over the reserved 0

# Vacate the slot, gives back the id+gen to hand to the next spawn
proc kill*(e: var Entity): Entity =
  result = e
  e.gen = deadGen
  result.advanceGen()

# Move a fresh gen into a vacant slot
proc revive*(e: var Entity, eGen: uint16) {.inline.} =
  e.gen = eGen

proc `<`*(a, b: Entity): bool {.inline.} =
  if a.id != b.id: a.id < b.id
  else: a.gen < b.gen
proc cmp*(a, b: Entity): int {.inline.} =
  result = cmp(a.id, b.id)
  if result == 0: result = cmp(a.gen, b.gen)
