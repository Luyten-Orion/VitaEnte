## A minimal sparse ECS implementation for Nimskull

import std/[
  strutils,
  macros
]

import vitaente/[
  sparsesets,
  core
]

# Exporting core is important
export core

macro genSparseSetField(components: typedesc[tuple]): untyped =
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
    var name = component.repr
    name[0] = toLowerAscii(name[0])
    result.add(newIdentDefs(
      ident(component.repr & "SparseSet"),
      newNimNode(nnkBracketExpr).add(
        bindSym"SparseSet",
        component
      )
    ))

  echo componentsNode.treeRepr

type
  World*[T: tuple] = object
    sparseSets*: genSparseSetField(T)
  
  WorldA = World[(int, string)]

# I thought I remembered there being a weird bug with type aliases but... nope?
#template WorldT[T: tuple](w: typedesc[World[T]]): typedesc[T] = T