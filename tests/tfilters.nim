import std/[unittest]

import vitaente/
  [lib]

type
  DistInt = distinct int
  SiblingInt = int
  IsTag = distinct Unit
  IsObj = object
  Pair = object
    x, y: int

  TF = (DistInt, SiblingInt, IsTag, IsObj, Pair,)

suite "Filter wrappers (Not/Mut) resolve to the wrapped type":
  test "Not[distinct] finds its own sparse set even when the base is a component":
    var w = World[TF]()
    let
      e1 = w.spawn()[0]
      e2 = w.spawn()[0]
    w.addComponent(e1, DistInt(7))
    w.addComponent(e2, SiblingInt(7))

    # e1 has DistInt; only e2 lacks it
    var matched: seq[Entity]
    w.runSystem((Not[DistInt],),
      proc(e: Entity): CommandBuffer[TF] = matched.add(e))
    check matched == @[e2]

  test "Not[distinct Unit] tag is negatable":
    var w = World[TF]()
    let
      tagged = w.spawn()[0]
      plain = w.spawn()[0]
    w.addComponent(tagged, IsTag)

    var matched: seq[Entity]
    w.runSystem((Not[IsTag],),
      proc(e: Entity): CommandBuffer[TF] = matched.add(e))
    check matched == @[plain]

  test "Mut[distinct] positive filter iterates its own set":
    var w = World[TF]()
    let
      e1 = w.spawn()[0]
      e2 = w.spawn()[0]
    w.addComponent(e1, DistInt(1))
    w.addComponent(e2, SiblingInt(1))

    var mutated = 0
    w.runSystem((Mut[DistInt],),
      proc(e: Entity, v: var DistInt): CommandBuffer[TF] =
        mutated.inc
        v = DistInt(99))
    check mutated == 1
    check int(w.getComponent(e1, DistInt)) == 99
    check w.getComponent(e2, SiblingInt) == 1

suite "Unit-shaped components survive deletion":
  test "del on a distinct Unit component does not touch a data column":
    var w = World[TF]()
    let e = w.spawn()[0]
    w.addComponent(e, IsTag)
    w.delComponent(e, IsTag)
    check not w.hasComponent(e, IsTag)

  test "despawn with distinct Unit components":
    var w = World[TF]()
    let e = w.spawn()[0]
    w.addComponent(e, IsTag)
    w.despawn(@[e])
    check not w.live(e)

suite "Public component deletion":
  test "add with a stale handle of a recycled id raises":
    var w = World[TF]()
    let
      a = w.spawn()[0]
      _ = w.spawn()[0] # a second entity so ids differ from len bookkeeping
    w.despawn(@[a])
    let fresh = w.spawn()[0] # recycles a's id
    check fresh.id == a.id
    expect StaleEntityDefect:
      w.addComponent(a, Pair(x: 0, y: 0))

  test "delComponent takes the type explicitly":
    var w = World[TF]()
    let e = w.spawn()[0]
    w.addComponent(e, Pair(x: 1, y: 2))
    w.delComponent(e, Pair)
    check not w.hasComponent(e, Pair)

  test "delComponents forwards to delComponent":
    var w = World[TF]()
    let e = w.spawn()[0]
    w.addComponents(e, DistInt(3), IsObj(), Pair(x: 0, y: 0))
    w.delComponents(e, DistInt, IsObj, Pair)
    check not w.hasComponent(e, DistInt)
    check not w.hasComponent(e, IsObj)
    check not w.hasComponent(e, Pair)
    # deletion is per-component, neighbours stay
    let e2 = w.spawn()[0]
    w.addComponents(e2, DistInt(1), SiblingInt(2))
    w.delComponent(e2, DistInt)
    check w.hasComponent(e2, SiblingInt)
