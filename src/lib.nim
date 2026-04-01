## A minimal sparse ECS implementation for Nimskull

import std/[
  strutils,
  sequtils,
  genasts,
  macros
]

type
  # Internal types
  ComponentInfo = object
    name: NimNode     # Field name in the tuple
    kind: NimNode # The enum kind
    typ: NimNode  # The type it represents

  # Public types
  Entity* = object
    id: uint32
    gen: uint32

  SparseSet*[T] = object 
    smap: seq[int32]   # Entity -> Dense
    dmap: seq[Entity]  # Dense -> Entity
    when T isnot void:
      components: seq[T] # Data

proc grabUppercase(s: string): string = s.filter(isUpperAscii).join()

macro declareWorld*[T: tuple](worldName: static string, _: typedesc[T]): untyped =
  let 
    tupleTy = T.getTypeImpl
    enumName = ident(worldName & "ComponentKind")
    worldTy = ident(worldName)
    sparseSetTy = bindSym"SparseSet"
    prefix = grabUppercase(worldName).toLowerAscii
  
  var components: seq[ComponentInfo]

  for i in 0..<tupleTy.len:
    let 
      f = tupleTy[i]
      fName = f[0].strVal
      kindName = ident(prefix & "c" & fName[0].toUpperAscii() & fName[1..^1])
    
    components.add ComponentInfo(
      name: f[0],
      kind: kindName,
      typ: f[1]
    )

  if components.len == 0:
    error("A World requires at least one component to justify its existence.", tupleTy)

  let enumFields = newNimNode(nnkEnumTy).add(newEmptyNode())
  for c in components:
    enumFields.add c.kind

  let
    recList = newNimNode(nnkRecList).add(
      newIdentDefs(ident("generations"), genAst(seq[uint32])),
      newIdentDefs(ident("freeIdxs"),    genAst(seq[uint32])),
      newIdentDefs(ident("sigs"),        genAst(enumName, seq[set[enumName]]))
    )

    worldObj = newNimNode(nnkObjectTy).add(
      newEmptyNode(),
      newEmptyNode(),
      recList
    )

  for c in components:
    recList.add newIdentDefs(
      c.name, 
      newNimNode(nnkBracketExpr).add(sparseSetTy, c.typ)
    )

  result = genAst(enumName, enumFields, worldTy, worldObj):
    type
      enumName* = enumFields

      worldTy* = worldObj


  echo treeRepr(result)
  echo repr(result)

declareWorld("Test", tuple[a: int, b, c: string])