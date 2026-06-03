## A minimal sparse ECS implementation for Nimskull

import std/[
  typetraits,
  strutils,
  macros,
  tables
]

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
  World*[T: tuple] = object
    sparseSets*: genSparseSetField(T)

  Not*[T] = distinct T

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
