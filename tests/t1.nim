import std/[
  importutils
]

import vitaente

# 1. Define the World
# 'pos' and 'vel' have data, 'isHero' is a void/tag component.
declareWorld("Game", tuple[pos: float, vel: float, isHero: void])

proc main() =
  echo "=== [Sovereign ECS: Test Suite] ==="
  
  var world = Game()
  var entities: seq[Entity]

  # --- Test 1: Spawning & Generation Logic ---
  echo "\n[Test 1] Spawning 5 Entities..."
  for i in 0..<5:
    let e = world.spawn()
    entities.add(e)
    # Generations should start at 0
    assert e.gen == 0
    assert world.contains(e)
  
  assert world.generations.len == 5
  echo "Successfully spawned 5 entities with unique IDs."

  # --- Test 2: Component CRUD ---
  echo "\n[Test 2] Adding Components..."
  # Every entity gets a position
  for i, e in entities:
    world.add(e, gcPos, i.float * 10.0)
  
  # Only even entities get velocity
  world.add(entities[0], gcVel, 1.5)
  world.add(entities[2], gcVel, 2.5)
  world.add(entities[4], gcVel, 3.5)

  # Only the first is a Hero
  world.add(entities[0], gcIsHero)

  # Verification via signatures
  assert gcPos in world.signature(entities[0])
  assert gcIsHero in world.signature(entities[0])
  assert gcVel notin world.signature(entities[1])
  echo "Signatures and component storage verified."

  # --- Test 3: The Query Macro (Read-Only) ---
  echo "\n[Test 3] Testing Query (pos)..."
  var posCount = 0
  # Note: The query yields (Entity, ComponentA, ComponentB...)
  for e, p in world.query({gcPos}):
    assert p == e.id.float * 10.0
    posCount.inc
  assert posCount == 5

  echo "[Test 3b] Testing Join Query (pos + vel)..."
  var joinCount = 0
  for e, p, v in world.query({gcPos, gcVel}):
    # Should only find 0, 2, 4
    assert e.id in {0'u32, 2'u32, 4'u32}
    joinCount.inc
  assert joinCount == 3

  echo "[Test 3c] Testing Tag Query (isHero)..."
  var heroCount = 0
  # Void components are skipped in the tuple yield, but filter the join!
  for e in world.query({gcIsHero}):
    assert e.id == 0
    heroCount.inc
  assert heroCount == 1

  # --- Test 4: Destruction & Recycling ---
  echo "\n[Test 4] Testing Kill & LIFO Recycling..."
  let targetId = entities[2].id # ID 2
  let targetGen = entities[2].gen # 0
  
  world.kill(entities[2])
  assert not world.contains(entities[2])
  
  # When we spawn again, it should grab ID 2 from the freeIdxs stack
  let recycled = world.spawn()
  echo "Recycled ID: ", recycled.id, " | New Gen: ", recycled.gen
  
  assert recycled.id == targetId
  assert recycled.gen == targetGen + 1
  assert world.contains(recycled)
  
  # The signature should be empty for the new entity
  assert world.signature(recycled) == {}

  echo "\n=== [ALL TESTS PASSED] ==="

# Execute
main()