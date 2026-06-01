when sizeof(int) != sizeof(int64):
  # TODO: Look into making this work on 32-bit targets...? Maybe?
  {.error: "Only 64-bit builds are supported."}

type
  Entity* = object
    id: uint32

# Simple constructor
template init*(T: typedesc[Entity], eId: T.id): T = T(id: eId)
# Read only field
template id*(e: Entity): Entity.id = e.id