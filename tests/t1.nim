import vitaente

# 1. Define the World
declareWorld("Game", tuple[pos: float, vel: float, isHero: void])

proc main() =
  echo "=== [VitaEnte ECS: Test Suite] ==="
  
  var world = Game()
  var entities: seq[Entity]

  # --- Test 1: Spawning & Generation Logic ---
  echo "\n[Test 1] Spawning 5 Entities..."
  for i in 0..<5:
    let e = world.spawn()
    entities.add(e)
    assert e.gen == 0
    assert world.contains(e)
  
  assert world.generations.len == 5
  echo "Successfully spawned 5 entities."

  # --- Test 2: Component CRUD ---
  echo "\n[Test 2] Adding Components..."
  # Every entity (0, 1, 2, 3, 4) gets a position
  for i, e in entities:
    world.add(e, gcPos, i.float * 10.0)
  
  # Only even entities (0, 2, 4) get velocity
  world.add(entities[0], gcVel, 1.5)
  world.add(entities[2], gcVel, 2.5)
  world.add(entities[4], gcVel, 3.5)

  # Only the first (0) is a Hero
  world.add(entities[0], gcIsHero)
  echo "Setup: 0:{P,V,H}, 1:{P}, 2:{P,V}, 3:{P}, 4:{P,V}"

  # --- Test 3: The Query Macro (Basic) ---
  echo "\n[Test 3] Testing Basic Queries..."
  var joinCount = 0
  for e, p, v in world.query(readOnly = [gcPos, gcVel]):
    assert e.id in {0'u32, 2'u32, 4'u32}
    joinCount.inc
  assert joinCount == 3
  echo "Join query (pos + vel) passed."

  # --- Test 4: Destruction & Recycling ---
  echo "\n[Test 4] Killing Entity 2..."
  # Entity 2 was {pos, vel}. After kill, it's empty.
  world.kill(entities[2])
  assert not world.contains(entities[2])
  
  let recycled = world.spawn()
  echo "Recycled ID 2. New Gen: ", recycled.gen
  # Current state: 0:{P,V,H}, 1:{P}, 2:{}, 3:{P}, 4:{P,V}

  # --- Test 5: Exclusion Logic (The New "Not" Filter) ---
  echo "\n[Test 5] Testing Exclusion (NOT) Logic..."

  # Scenario A: Find entities with Position but NOT Velocity
  # Expects: Entity 1 and Entity 3. (Entity 0 and 4 have Vel, Entity 2 is empty)
  var nonFlyers = 0
  for e, p in world.query(readOnly = [gcPos], exclude = [gcVel]):
    assert e.id == 1 or e.id == 3
    nonFlyers.inc
  assert nonFlyers == 2
  echo "Query (pos NOT vel) passed: found IDs 1 and 3."

  # Scenario B: Find entities with Position AND Velocity but NOT Hero
  # Expects: Entity 4. (Entity 0 is a Hero, Entity 2 is empty, 1 & 3 lack Vel)
  var grunts = 0
  for e, p, v in world.query(readOnly = [gcPos, gcVel], exclude = [gcIsHero]):
    assert e.id == 4
    grunts.inc
  assert grunts == 1
  echo "Query (pos, vel NOT isHero) passed: found ID 4."

  # Scenario C: Find entities with Position but NOT (Hero OR Velocity)
  # Expects: Entity 1 and 3.
  var civilians = 0
  for e, p in world.query(readOnly = [gcPos], exclude = [gcIsHero, gcVel]):
    assert e.id in {1'u32, 3'u32}
    civilians.inc
  assert civilians == 2
  echo "Multi-exclusion query (pos NOT isHero, NOT vel) passed."

  echo "\n=== [ALL TESTS PASSED] ==="

main()