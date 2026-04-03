## A minimal sparse ECS implementation for Nimskull

import std/[
  strutils,
  sequtils,
  genasts,
  macros,
  tables
]

type
  # Internal types
  ComponentInfo = object
    name: NimNode # Field name in the tuple
    kind: NimNode # The enum kind
    typ: NimNode  # The type it represents

  # Public types
  Entity* = object
    id*: uint32
    gen*: uint32

  SparseSet*[T] = object 
    smap: seq[uint32]   # Entity -> Dense
    dmap: seq[Entity]  # Dense -> Entity
    when T isnot void:
      components: seq[T] # Data

const Sentinel = high(uint32)

# SparseSet helpers
proc contains*[T](ss: SparseSet[T], e: Entity): bool {.inline.} =
  ## Determine if the entity exists within this component storage.
  e.id < ss.smap.len.uint32 and ss.smap[e.id] != Sentinel

proc add*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Add a component to an entity.
  if e in ss: return

  # Lazy growth: Fill new slots with the Sentinel
  if e.id >= ss.smap.len.uint32:
    let oldLen = ss.smap.len
    ss.smap.setLen(e.id + 1)
    for i in oldLen .. e.id.int:
      ss.smap[i] = Sentinel

  # Map the Entity ID to the current end of the dense array
  ss.smap[e.id] = ss.dmap.len.uint32
  ss.dmap.add(e)
  
  when T isnot void:
    ss.components.add(val)

proc add*[T: void](ss: var SparseSet[T], e: Entity) =
  ## Add a 'tag' component (no data) to an entity.
  if e in ss: return

  if e.id >= ss.smap.len.uint32:
    let oldLen = ss.smap.len
    ss.smap.setLen(e.id + 1)
    for i in oldLen .. e.id.int:
      ss.smap[i] = Sentinel

  ss.smap[e.id] = ss.dmap.len.uint32
  ss.dmap.add(e)

proc del*[T](ss: var SparseSet[T], e: Entity) =
  ## Remove the component via swap-and-pop to maintain a packed dense array.
  if e notin ss: return

  let 
    idxToRemove = ss.smap[e.id]
    lastEntity = ss.dmap[^1]

  # Move the last entity's metadata to the hole we just created
  ss.dmap[idxToRemove] = lastEntity
  ss.smap[lastEntity.id] = idxToRemove
  
  when T isnot void:
    # Move the last component data to the hole
    ss.components[idxToRemove] = ss.components[^1]
    ss.components.setLen(ss.components.len - 1)

  # Shrink the dense map and reset the sparse entry
  ss.dmap.setLen(ss.dmap.len - 1)
  ss.smap[e.id] = Sentinel

template `[]`*[T](ss: SparseSet[T], e: Entity): T =
  ## Direct access to component data.
  assert e in ss, "Attempted to access non-existent component for Entity " & $e.id
  ss.components[ss.smap[e.id]]

template `[]=`*[T](ss: var SparseSet[T], e: Entity, val: T) =
  ## Direct update of component data.
  assert e in ss, "Attempted to assign to non-existent component for Entity " & $e.id
  ss.components[ss.smap[e.id]] = val

# Helpers
proc grabUppercase(s: string): string = s.filter(isUpperAscii).join()

proc newLit(n: NimNode): NimNode =
  newCall(bindSym"quote", newStmtList(n))

# The main meat
macro declareWorld*[T: tuple](
  worldName: static string,
  _: typedesc[T]
): untyped =
  ## Declares the world type as well as various helpers for the world.
  ## - `worldName` is the name of the generated type and its corrosponding enu
  ## - `T` is components, passed as a tuple type. Component names are generated
  ##   from the tuple field names, with the corrosponding type.
  let 
    tupleTy = T.getTypeImpl
    enumName = ident(worldName & "ComponentKind")
    worldTy = ident(worldName)
    sparseSetTy = bindSym"SparseSet"
    prefix = grabUppercase(worldName).toLowerAscii
  
  var
    components: seq[ComponentInfo]
    componentEnumMap: seq[(string, string)]

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
    componentEnumMap.add (kindName.strVal, fName)

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

  let scem = genSym("compEnumMap")

  result = genAstOpt(
    {kDirtyTemplate}, enumName, enumFields, worldTy, worldObj, componentEnumMap,
    scem, components
  ):
    when not declared(tables):
      import std/tables
    when not defined(macros):
      import std/macros
    when not defined(genasts):
      import std/genasts
    when not defined(sequtils):
      import std/sequtils

    type
      enumName* {.pure.}  = enumFields
      worldTy* = worldObj

    const scem = componentEnumMap.toTable

    proc spawn*(w: var worldTy): Entity =
      ## Creates or reuses a dead entity in the world.
      var id = 0'u32

      if w.freeIdxs.len > 0:
        id = w.freeIdxs.pop()
      else:
        id = w.generations.len.uint32
        w.generations.add(0)
        w.sigs.add({})

      result = Entity(id: id, gen: w.generations[id])

    proc contains*(w: worldTy, e: Entity): bool {.inline.} =
      ## Returns whether the entity exists in the world.
      e.id < w.generations.len.uint32 and e.gen == w.generations[e.id]

    proc signature*(w: worldTy, e: Entity): set[enumName] {.inline.} =
      ## Returns the signature (the component set) of an entity
      assert e in w, "Attempted to access a dead entity: " & $e.id
      w.sigs[e.id]

    template add*(w: var worldTy, e: Entity, enm: static enumName, val) =
      ## Add a component to an entity, with a given value.
      w.sigs[e.id].incl(enm)
      for name, field in w.fieldPairs:
        when scem[$enm] == name:
          field.add(e, val)

    template add*(w: var worldTy, e: Entity, enm: static enumName) =
      ## Add a component to an entity, without a value.
      w.sigs[e.id].incl(enm)
      for name, field in w.fieldPairs:
        when scem[$enm] == name:
          field.add(e)
    
    proc kill*(w: var worldTy, e: Entity) =
      ## Remove an entity from the world.
      w.generations[e.id] += 1
      w.sigs[e.id] = {}

      for name, field in w.fieldPairs:
        when field is SparseSet:
          field.del(e)

      w.freeIdxs.add(e.id)

    macro queryImpl(w: var worldTy, ro, rw: static set[enumName]): untyped =
      const cmpts = components
      let mask = ro + rw
      var tupleConstr = nnkTupleConstr.newTree(bindSym"Entity")

      for c in ro:
        let ttyp = cmpts.filterIt(it.kind.strVal == $c)[0].typ
        if ttyp.kind in {nnkIdent, nnkSym} and ttyp.strVal != "void":
          tupleConstr.add ttyp
      
      for c in rw:
        let ttyp = cmpts.filterIt(it.kind.strVal == $c)[0].typ
        if ttyp.kind in {nnkIdent, nnkSym} and ttyp.strVal != "void":
          tupleConstr.add ttyp
      
      macro makeTupleRet(w: var worldTy, ro, rw: static set[enumName], i: uint32): untyped =
        var
          entitySym = genSym("ent")
          entDecl = genAst(entitySym, i):
            let entitySym = Entity(id: i, gen: w.generations[i])
          tupRetNode = newNimNode(nnkTupleConstr).add(entitySym)

        for c in ro:
          let componentInfo = cmpts.filterIt(it.kind.strVal == $c)[0]
          if (componentInfo.typ.kind in {nnkIdent, nnkSym} and
            componentInfo.typ.strVal != "void"):
            let componentAccess = newNimNode(nnkDotExpr).add(
              w,
              ident(componentInfo.name.strVal)
            )
            tupRetNode.add quote do:
              `componentAccess`[`entitySym`]
        
        for c in rw:
          let componentInfo = cmpts.filterIt(it.kind.strVal == $c)[0]
          if (componentInfo.typ.kind in {nnkIdent, nnkSym} and
            componentInfo.typ.strVal != "void"):
            let componentAccess = newNimNode(nnkDotExpr).add(
              w,
              ident(componentInfo.name.strVal)
            )
            tupRetNode.add quote do:
              `componentAccess`[`entitySym`]

        if tupRetNode.len == 1:
          tupRetNode = tupRetNode[0]

        newNimNode(nnkStmtList).add(
          entDecl,
          quote do: yield `tupRetNode`
        )

      result = genAst(w, ro, rw, mask):
        for entityIdx in 0'u32..<uint32(w.sigs.len):
          if w.sigs[entityIdx] * mask == mask:
            makeTupleRet(w, ro, rw, entityIdx)

    iterator query*(
      w: var worldTy,
      readOnly, readWrite: static set[enumName] = {}
    ): auto = w.queryImpl(readOnly, readWrite)

  echo repr(result)