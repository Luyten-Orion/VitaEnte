## A minimal sparse ECS implementation for Nimskull

import std/[
  macros,
  strutils
]

type
  # Internal types

  # Public types
  Entity* = object
    id: uint32
    gen: uint32

  SparseSet*[T] = object 
    smap: seq[int32]   # Entity -> Dense
    dmap: seq[Entity]  # Dense -> Entity
    when T isnot void:
      components: seq[T] # Data

proc grabUppercase(s: string): string =
  for c in s:
    if c.isUpperAscii():
      result.add c.toLowerAscii()

macro World[T: tuple](compEnumName: static string, _: typedesc[T]): untyped =
  const sparseSetTy = bindSym"SparseSet"

  var
    enumName = ident(compEnumName & "ComponentKind")
    fieldList = newNimNode(nnkRecList).add(
      newIdentDefs(
        ident("generations"),
        quote do: seq[uint32]
      ),
      newIdentDefs(
        ident("freeIdxs"),
        quote do: seq[uint32]
      ),
      newIdentDefs(
        ident("sigs"),
        quote do: seq[set[`enumName`]]
      )
    )
    enumTy = newNimNode(nnkEnumTy).add(newEmptyNode())

  let tupleTy = T.getTypeImpl
  for identDef in tupleTy:
    enumTy.add(ident(
      [grabUppercase(compEnumName), "c", $identDef[0].strVal[0].toUpperAscii(),
      identDef[0].strVal[1..^1]].join()
    ))
    fieldList.add newIdentDefs(
      identDef[0],
      newNimNode(nnkBracketExpr).add(sparseSetTy, identDef[1])
    )

  let innerWorld = genSym("InnerWorld")

  if enumTy.len == 1:
    error("World must have at least one component!", T.getTypeImpl)
    return

  result = newStmtList(
    newNimNode(nnkTypeSection).add(
      newNimNode(nnkTypeDef).add(
        newNimNode(nnkPostfix).add(
          ident("*"),
          enumName
        ),
        newEmptyNode(),
        enumTy
      ),
      newNimNode(nnkTypeDef).add(
        innerWorld,
        newEmptyNode(),
        newNimNode(nnkObjectTy).add(
          newEmptyNode(), newEmptyNode(), fieldList
        )
      )
    ),
    innerWorld
  )

  echo treeRepr(result)
  echo repr(result)

type
  Test = World("Test", tuple[a: int, b, c: string])

