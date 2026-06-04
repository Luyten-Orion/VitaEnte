## A minimal sparse ECS implementation for Nimskull

import std/[
  typetraits,
  strutils,
  genasts,
  macros,
  tables
]

from std/sugar import `=>`

import vitaente/[
  sparsesets,
  core
]

# Exporting core is important
export core

proc sparseSetFieldName(field: NimNode): string =
  var name = field.repr
  name[0] = toLowerAscii(name[0])
  name & "Components"

macro genSparseSetField(components: typedesc[tuple]): untyped {.used.} =
  var componentsNode = components.getTypeImpl
  componentsNode.expectKind(nnkBracketExpr)
  if componentsNode[1].kind != nnkTupleConstr:
    error("`genSparseSetField` only works for unnamed tuples.")
  for component in componentsNode[1]:
    if component.kind != nnkSym:
      error("`genSparseSetField` doesn't work with generics for now.")

  result = newNimNode(nnkTupleTy)

  for component in componentsNode[1]:
    # TODO: Support generic types in the future
    result.add(newIdentDefs(
      ident(sparseSetFieldName(component)),
      newNimNode(nnkBracketExpr).add(
        bindSym"SparseSet",
        component
      )
    ))    


type
  ConcurrentWorldAccessDefect* = object of Defect

  World*[T: tuple] = object
    entities*: seq[Entity]
    sparseSets*: genSparseSetField(T)
    # TODO: Replace with proper lock?
    lock*: bool

  Not*[T] = distinct T

  # TODO: Make a more efficient command buffer
  Command*[T: tuple] = proc (w: var World[T]) {.closure.}
  CommandBuffer*[T: tuple] = seq[Command[T]]

macro accessSparseSet*[T: tuple, U](w: World[T], _: typedesc[U]): SparseSet[U] =
  block checkComponentExists:
    for typ in T.getTypeInst:
      if U.getTypeInst == typ:
        break checkComponentExists
    
    error("There is no `" & `U`.getTypeInst.repr & "` component in `" & `T`.getTypeInst.repr & "`", callsite())

  let sparseSet = sparseSetFieldName(U.getTypeInst)

  result = newNimNode(nnkDotExpr).add(
    newNimNode(nnkDotExpr).add(
      w,
      ident("sparseSets"),
    ),
    ident(sparseSet)
  )

template addComponent[T: tuple, U](w: World[T], e: Entity, component: U) =
  accessSparseSet(w, U).add(e, component)

template addComponent[T: tuple, U](w: World[T], e: Entity, _: typedesc[U]) =
  accessSparseSet(w, U).add(e)

template delComponent[T: tuple, U](w: World[T], e: Entity) =
  accessSparseSet(w, U).del(e)

macro addComponents*[T: tuple, U](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  result = genAst:
    cb.add (proc(w: var World[T]) =
      for component in components:
        w.addComponent(e, component))

macro delComponents*[T: tuple, U](
  cb: CommandBuffer[T],
  e: Entity,
  components: varargs[untyped]
): untyped =
  result = genAst:
    cb.add (proc(w: var World[T]) =
      for component in components:
        w.delComponent(e, component))

proc apply*[T: tuple](w: var World[T], cb: CommandBuffer[T]) =
  # Uhhh how to wait?
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
  w.lock = true
  for command in cb:
    command(w)
  cb.setLen(0)
  w.lock = false

proc spawn*(w: var World, count: Natural = 1): seq[Entity] =
  # TODO: Make this check happen in release builds?
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
  w.lock = true
  when sizeof(int) == 8:
    assert w.entities.len + count <= high(uint32).int
  else:
    {.error: "Only 64-bit builds are supported."}

  result = newSeq[Entity](count)
  for i in 0..<count:
    result[i] = Entity.init(uint32(w.entities.len))
    w.entities.add(result[i])
  w.lock = false

proc despawn*(w: var World, entities: seq[Entity]) =
  if w.lock: raise newException(ConcurrentWorldAccessDefect)
  w.lock = true
  for e in entities:
    # TODO: Find a better way to mass-delete entities, perhaps find all the indices and delete in reverse?
    w.entities.del(w.entities.find(e))
    for name, field in w.sparseSets.fieldPairs:
      field.del(e) # no-op if not present
    
  w.lock = false


macro query*[T: tuple, U: distinct tuple](
  w: var World[T],
  components: varargs[typedesc],
  f: proc
) = discard