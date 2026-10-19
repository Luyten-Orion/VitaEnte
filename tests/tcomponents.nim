import std/[unittest]

import vitaente/[
  lib,
  components
]

type
  Cost = object
    value*: int
  Dep = distinct Entity # this entity depends on that one
  Name = distinct string
  CW = (Changed, Cost, Dep, Name, Parent, Children,)

suite "Generational entities":
  test "despawn makes the handle dead, recycling revives the id not the handle":
    var w = World[CW]()
    let a = w.spawn()[0]
    w.addComponent(a, Cost(value: 1))
    w.despawnOne(a)
    check not w.live(a)

    let b = w.spawn()[0]
    check b.id == a.id # id recycled
    check b.gen != a.gen # but the old handle stays dead
    check not w.live(a)
    check w.live(b)
    # the recycled entity starts with a clean slate
    check not w.hasComponent(b, Cost)

  test "stale handles read as absent, not as the recycled neighbour":
    var w = World[CW]()
    let
      a = w.spawn()[0]
      b = w.spawn()[0]
    w.addComponent(a, Name("first"))
    w.despawnOne(a)
    w.addComponent(b, Name("second"))
    check w.hasComponent(a, Name) == false
    check w.hasComponent(b, Name) == true

  test "double despawn and despawning the dead are no-ops":
    var w = World[CW]()
    let
      a = w.spawn()[0]
      b = w.spawn()[0]
    w.despawnOne(a)
    w.despawnOne(a) # must not enqueue a second free slot
    w.despawn(@[b, b])
    let s = w.spawn(3)
    check w.live(s[0]) and w.live(s[1]) and w.live(s[2])
    # a and b's ids each recycled exactly once
    check s[0].gen != a.gen and s[1].gen != b.gen

  test "despawn inside a command buffer":
    var w = World[CW]()
    let
      a = w.spawn()[0]
      b = w.spawn()[0]
    var cb: CommandBuffer[CW]
    cb.add proc(w: var World[CW]) =
      w.despawnOne(a)
      let fresh = w.spawn()[0] # spawn too
      w.addComponent(fresh, Name("phoenix"))
    w.apply(cb)
    check not w.live(a)
    check w.hasComponent(b, Name) == false

  test "generation wraps past the reserved zero":
    # cycle one entity through spawn/despawn until its gen reaches the top
    var w = World[CW]()
    var e = w.spawn()[0] # gen 1
    for _ in 1 ..< high(Entity.gen).int:
      w.despawnOne(e)
      e = w.spawn()[0]
    check uint16(e.gen) == high(Entity.gen)
    w.despawnOne(e)
    let f = w.spawn()[0]
    check uint16(f.gen) == 1 # wrapped past the reserved 0

suite "Tree edges":
  test "setChildren maintains Parent back-pointers":
    var w = World[CW]()
    let
      root = w.spawn()[0]
      kids = w.spawn(2)
    w.setChildren(root, @[kids[0], kids[1]])
    check w.parent(kids[0]) == root
    check w.parent(kids[1]) == root
    check w.hasParent(root) == false
    check w.parent(root) == Entity.sentinel

  test "reparenting overwrites the old edge":
    var w = World[CW]()
    let
      a = w.spawn()[0]
      b = w.spawn()[0]
      k = w.spawn()[0]
    w.setChildren(a, @[k])
    w.setChildren(b, @[k])
    check w.parent(k) == b

  test "traversals skip dead children, keeping partial graphs usable":
    var w = World[CW]()
    let
      root = w.spawn()[0]
      kids = w.spawn(2)
    w.setChildren(root, @[kids[0], kids[1]])
    w.despawnOne(kids[0])
    var seen: seq[Entity]
    for k in w.children(root):
      seen.add(k)
    check seen == @[kids[1]]

  test "descendants iterate post-order":
    var w = World[CW]()
    let
      root = w.spawn()[0]
      mid = w.spawn(2)
      leaf = w.spawn(2)
    w.setChildren(root, @[mid[0], mid[1]])
    w.setChildren(mid[0], @[leaf[0]])
    w.setChildren(mid[1], @[leaf[1]])
    var order: seq[Entity]
    for e in w.descendants(root):
      order.add(e)
    # the start node is not its own descendant
    check order.find(root) == -1
    # children strictly before parents
    check order.find(leaf[0]) < order.find(mid[0])
    check order.find(leaf[1]) < order.find(mid[1])
    check order.len == 4
suite "settle":
  test "propagates along a dependency chain and reports rounds":
    var w = World[CW]()
    let s = w.spawn(3)
    w.addComponents(s[0], Cost(value: 10))
    w.addComponents(s[1], Cost(value: 0), Dep(s[0]))
    w.addComponents(s[2], Cost(value: 0), Dep(s[1]))

    let (rounds, settled) = w.settle:
      w.runSystem((Cost, Dep,),
        proc(e: Entity, cost: var Cost, dep: Dep): CommandBuffer[CW] =
          let target = w.getComponent(Entity(dep), Cost).value + 1
          if target > cost.value: # mark on value-difference only
            result.add proc(w: var World[CW]) =
              w.getComponent(e, Cost).value = target
              w.addComponent(e, Changed)
      )
    check settled
    check rounds == 2
    check w.getComponent(s[1], Cost).value == 11
    check w.getComponent(s[2], Cost).value == 12
    # marks swept: nothing carries Changed afterwards
    var leftover = 0
    w.runSystem((Changed,),
      proc(e: Entity): CommandBuffer[CW] = leftover += 1)
    check leftover == 0

  test "a pass that marks nothing exits after a single round":
    var w = World[CW]()
    let s = w.spawn(2)
    w.addComponents(s[0], Cost(value: 1))
    let (rounds, settled) = w.settle:
      discard # marks nothing
    check settled
    check rounds == 0

  test "an unguarded pass hits the cap without crashing":
    var w = World[CW]()
    let s = w.spawn(2)
    w.addComponents(s[0], Cost(value: 0))
    # marks Changed unconditionally, so no round is ever quiet
    let (rounds, settled) = w.settle(5):
      w.runSystem((Cost,),
        proc(e: Entity): CommandBuffer[CW] =
          result.add proc(w: var World[CW]) =
            w.addComponent(e, Changed))
    check not settled
    check rounds == 5
