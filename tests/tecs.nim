import std/[
  strutils
]

import vitaente

type
  Position = object
    x, y: int

  Velocity = object
    dx, dy: int

  IsAlive = distinct Unit

type MyComponents = (Position, Velocity, IsAlive, seq[string])

var world = World[MyComponents]()

let
  e1 = world.spawn()[0]
  e2 = world.spawn()[0]
  e3 = world.spawn()[0]
  e4 = world.spawn()[0]

world.addComponents(e1, Position(x: 0, y: 0), Velocity(dx: 1, dy: 2), IsAlive)
world.addComponents(e2, Position(x: 10, y: 10), Velocity(dx: -1, dy: 0))
world.addComponent(e3, Position(x: 5, y: 5))
world.addComponents(e4, @["hello", "world", "all!"])

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
    echo "Entity ", e.id, " has no Position component."
)

world.runSystem((Mut[seq[string]],), true,
  proc(e: Entity, msgs: var seq[string]): CommandBuffer[MyComponents] =
    msgs.setLen(1)
)

world.runSystem((seq[string],), true,
  proc(e: Entity, msgs: seq[string]): CommandBuffer[MyComponents] =
    echo $e.id & ": " & msgs.join(", ")
)