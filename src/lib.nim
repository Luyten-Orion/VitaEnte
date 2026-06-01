## A minimal sparse ECS implementation for Nimskull

import std/[
  typetraits,
  sequtils,
  strutils,
  genasts,
  macros,
  tables
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

  result = newNimNode(nnkTupleTy)

  echo componentsNode.treeRepr

type
  World*[T: tuple] = object
    sparseSets*: genSparseSetField(T)
  
  WorldA = World[(int, string)]