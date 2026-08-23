when sizeof(int) != sizeof(int64):
  # TODO: Look into making this work on 32-bit targets...? Maybe?
  {.error: "Only 64-bit builds are supported."}

type
  # Placeholder until unit type comes along
  Unit* = tuple[]

  Entity* = object
    id: uint32

# Simple constructor
template init*(T: typedesc[Entity], eId: T.id): T = T(id: eId)
# Read only field
template id*(e: Entity): Entity.id = e.id

proc `<`*(a, b: Entity): bool {.inline.} = a.id < b.id
proc cmp*(a, b: Entity): int {.inline.} = cmp(a.id, b.id)