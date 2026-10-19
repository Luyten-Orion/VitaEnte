## Opt-in components. Put them in your tuple, get the helpers. lib.nim
## doesn't know any of this exists.
import ./[
  core,
  lib
]

type
  # Marks entities a pass just rewrote. The pass adds it, `settle` clears it
  # between rounds.
  Changed* = distinct Unit

  # Tree edges. Nodes hold their children in order, kids point back at their
  # parent (sentinel for roots). Half-built graphs are fine: traversals skip
  # dead ids, so an edge to something that doesn't exist yet just resolves
  # later on its own.
  Parent* = distinct Entity
  Children* = distinct seq[Entity]

template parentOf*(p: Parent): Entity = Entity(p)
template childrenOf*(c: Children): seq[Entity] = seq[Entity](c)

proc parent*[T: tuple](w: World[T], e: Entity): Entity =
  ## Parent of the entity, or sentinel if it has none.
  if w.hasComponent(e, Parent): parentOf(w.getComponent(e, Parent))
  else: Entity.sentinel

proc hasParent*[T: tuple](w: World[T], e: Entity): bool =
  w.hasComponent(e, Parent) and w.parent(e) != Entity.sentinel

proc setChildren*[T: tuple](w: var World[T], p: Entity, kids: seq[Entity]) =
  ## Set p's children, keeping the Parent back-pointers in sync.
  w.addComponent(p, Children(kids))
  for k in kids:
    if not w.live(k): continue # dangling edges stay dangling
    if w.hasComponent(k, Parent):
      w.getComponent(k, Parent) = Parent(p)
    else:
      w.addComponent(k, Parent(p))

proc addChild*[T: tuple](w: var World[T], p, k: Entity) =
  ## Append one child.
  var kids: seq[Entity]
  if w.hasComponent(p, Children):
    kids = childrenOf(w.getComponent(p, Children))
  kids.add(k)
  w.setChildren(p, kids)

iterator children*[T: tuple](w: World[T], p: Entity): Entity =
  ## Live children, in order.
  if w.hasComponent(p, Children):
    for k in childrenOf(w.getComponent(p, Children)):
      if w.live(k):
        yield k

iterator descendants*[T: tuple](w: World[T], p: Entity): Entity =
  ## Everything under p, children before parents. p itself isn't included.
  var
    stack = @[p]
    order: seq[Entity]
  while stack.len > 0:
    let e = stack.pop()
    for k in w.children(e):
      stack.add(k)
      order.add(k)
  while order.len > 0:
    yield order.pop() # reversing the pre-order gives post-order

template settle*[T: tuple](
  w: var World[T],
  maxRounds: int = high(uint8).int,
  pass: untyped
): tuple[rounds: int, settled: bool] =
  ## Run `pass` until a round marks nothing, give back the round count and
  ## whether it actually settled. Mark what you rewrite with `Changed`, only
  ## when the value actually changed (an unconditional mark never quiets
  ## down). Hitting the cap is a result, not a crash, so the caller gets to
  ## complain instead of the whole compiler dying.
  block:
    var
      rounds = 0
      settled = false
    while true:
      pass
      var swept = 0
      w.runSystem((Changed,),
        proc(e: Entity): CommandBuffer[T] =
          swept += 1
          result.add proc(w: var World[T]) =
            w.delComponent(e, Changed)
      )
      if swept == 0:
        settled = true
        break
      rounds += 1
      if rounds >= maxRounds: break
    (rounds, settled)
