import std/[
  importutils,
  unittest
]

import vitaente/[
  sparsesets,
  core
]

suite "SparseSet[non-void]":
  setup:
    privateAccess(SparseSet)

  test "add and contains":
    var ss = SparseSet[int]()
    let
      e1 = Entity.init(0)
      e2 = Entity.init(5)

    ss.add(e1, 100)
    ss.add(e2, 200)

    check e1 in ss
    check e2 in ss
    check Entity.init(1) notin ss
    check Entity.init(10) notin ss

  test "add duplicate entity does nothing":
    var ss = SparseSet[int]()
    let e = Entity.init(42)

    ss.add(e, 123)
    ss.add(e, 456)  # silently ignores

    check ss[e] == 123
    check ss.smap.len == 43
    check ss.dmap.len == 1
    check ss.components.len == 1

  test "indexing and assignment":
    var ss = SparseSet[int]()
    let e = Entity.init(7)

    ss.add(e, 10)
    check ss[e] == 10

    ss[e] = 42
    check ss[e] == 42

  test "delete entity (middle)":
    var ss = SparseSet[int]()
    let
      e0 = Entity.init(0)
      e1 = Entity.init(1)
      e2 = Entity.init(2)

    ss.add(e0, 100)
    ss.add(e1, 200)
    ss.add(e2, 300)

    ss.del(e1)

    check e1 notin ss
    check e0 in ss
    check e2 in ss
    check ss[e0] == 100
    check ss[e2] == 300

    # Dense arrays should be compacted: last element (e2) moved to slot of e1
    check ss.dmap.len == 2
    check ss.components.len == 2
    check ss.dmap[0] == e0
    check ss.dmap[1] == e2
    check ss.components[0] == 100
    check ss.components[1] == 300

  test "delete last element":
    var ss = SparseSet[int]()
    let
      e0 = Entity.init(0)
      e1 = Entity.init(1)

    ss.add(e0, 100)
    ss.add(e1, 200)

    ss.del(e1)

    check not ss.contains(e1)
    check ss.contains(e0)
    check ss[e0] == 100
    check ss.dmap.len == 1
    check ss.components.len == 1
    check ss.dmap[0] == e0
    check ss.components[0] == 100

  test "delete first element":
    var ss = SparseSet[int]()
    let
      e0 = Entity.init(0)
      e1 = Entity.init(1)

    ss.add(e0, 100)
    ss.add(e1, 200)

    ss.del(e0)

    check e0 notin ss
    check e1 in ss
    check ss[e1] == 200
    check ss.dmap.len == 1
    check ss.dmap[0] == e1
    check ss.components[0] == 200

  test "delete non-existent entity does nothing":
    var ss = SparseSet[int]()
    let e = Entity.init(99)
    ss.add(e, 123)
    ss.del(Entity.init(999))
    check e in ss
    check ss[e] == 123
    check ss.dmap.len == 1

suite "SparseSet[void] (tag components)":
  setup:
    privateAccess(SparseSet)
    type Tag = void

  test "add and contains":
    var ss = SparseSet[Tag]()
    let
      e1 = Entity.init(0)
      e2 = Entity.init(3)

    ss.add(e1)
    ss.add(e2)

    check e1 in ss
    check e2 in ss
    check Entity.init(1) notin ss

  test "add duplicate does nothing":
    var ss = SparseSet[Tag]()
    let e = Entity.init(5)

    ss.add(e)

    check e in ss
    check ss.dmap.len == 1

  test "delete":
    var ss = SparseSet[Tag]()
    let
      e1 = Entity.init(0)
      e2 = Entity.init(1)

    ss.add(e1)
    ss.add(e2)

    ss.del(e1)

    check e1 notin ss
    check e2 in ss
    check ss.dmap.len == 1
    check ss.dmap[0] == e2

  test "delete last element":
    var ss = SparseSet[Tag]()
    let e = Entity.init(0)

    ss.add(e)
    ss.del(e)

    check e notin ss
    check ss.dmap.len == 0

suite "SparseSet invariants after many operations":
  setup:
    privateAccess(SparseSet)

  test "dense arrays stay in sync after random adds and deletes":
    var
      ss = SparseSet[int]()
      present = newSeq[bool](10)

    for id in 0..9:
      let e = Entity.init(id.uint32)
      ss.add(e, id * 10)
      present[id] = true

    # Delete a few
    for id in [2, 5, 7]:
      ss.del(Entity.init(id.uint32))
      present[id] = false

    let
      newId1 = Entity.init(20)
      newId2 = Entity.init(30)
    ss.add(newId1, 200)
    ss.add(newId2, 300)
    present.setLen(31)
    present[20] = true
    present[30] = true

    # Verify dense array matches presence
    var count = 0
    for i, p in present:
      if p:
        count.inc
        let e = Entity.init(i.uint32)
        check e in ss
        if i < 10:
          check ss[e] == i * 10
        elif i == 20:
          check ss[e] == 200
        elif i == 30:
          check ss[e] == 300

    check ss.dmap.len == count
    check ss.components.len == count

    # Verify that every dense entry points to the correct component
    for idx, ent in ss.dmap:
      check ss.components[idx] == ss[ent]