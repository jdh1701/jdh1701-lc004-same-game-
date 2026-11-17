import Lean

open Lean

structure CliOptions where
  moduleName : Option Name := none
  declaration : Option Name := none
  allowed : List Name := []

def parseNames (value : String) : List Name :=
  (value.splitOn ",").filterMap fun item =>
    let normalized := item.foldl (fun result char =>
      if char.isWhitespace then result else result.push char) ""
    if normalized.isEmpty then none else some normalized.toName

partial def parseArgs : List String → CliOptions → Except String CliOptions
  | [], options => .ok options
  | "--module" :: value :: rest, options =>
      parseArgs rest { options with moduleName := some value.toName }
  | "--declaration" :: value :: rest, options =>
      parseArgs rest { options with declaration := some value.toName }
  | "--allow" :: value :: rest, options =>
      parseArgs rest { options with allowed := parseNames value }
  | argument :: _, _ => .error s!"unknown or incomplete argument: {argument}"

def errorJson (message : String) : Json :=
  Json.mkObj [
    ("ok", Json.bool false),
    ("error", Json.str message),
    ("axioms", Lean.toJson (#[] : Array String)),
    ("unresolved_assumptions", Lean.toJson (#[] : Array String))
  ]

partial def declarationUsesSorry (environment : Environment) (declaration : Name) :
    StateM NameSet Bool := do
  if declaration == ``sorryAx then
    return true
  let visited ← get
  if visited.contains declaration then
    return false
  modify fun names => names.insert declaration
  let visitExpression (expression : Expr) : StateM NameSet Bool := do
    if expression.hasSorry then
      return true
    for dependency in expression.getUsedConstants do
      if ← declarationUsesSorry environment dependency then
        return true
    return false
  let visitDeclaration (type value : Expr) : StateM NameSet Bool := do
    if ← visitExpression type then
      return true
    visitExpression value
  match environment.checked.get.find? declaration with
  | some (.axiomInfo info) => visitExpression info.type
  | some (.defnInfo info) => visitDeclaration info.type info.value
  | some (.thmInfo info) => visitDeclaration info.type info.value
  | some (.opaqueInfo info) => visitDeclaration info.type info.value
  | some (.quotInfo _) => return false
  | some (.ctorInfo info) => visitExpression info.type
  | some (.recInfo info) => visitExpression info.type
  | some (.inductInfo info) =>
      if ← visitExpression info.type then
        return true
      for constructor in info.ctors do
        if ← declarationUsesSorry environment constructor then
          return true
      return false
  | none => return false

def dependsOnSorry (environment : Environment) (declaration : Name) : Bool :=
  (declarationUsesSorry environment declaration).run' {}

unsafe def audit (moduleName declaration : Name) (allowed : List Name) : IO String := do
  let diagnostic ← IO.getStderr
  diagnostic.putStrLn s!"audit-stage: import-start {declaration}"
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{ module := moduleName }] {} (trustLevel := 0) fun environment => do
    diagnostic.putStrLn "audit-stage: import-complete"
    let theoremInfo ← match environment.find? declaration with
    | some (.thmInfo info) => pure info
    | some _ => throw <| IO.userError s!"'{declaration}' is not a theorem declaration"
    | none => throw <| IO.userError s!"theorem declaration '{declaration}' was not found"
    -- Evaluating a proof that depends on `sorryAx` is intentionally unsafe in Lean and can
    -- crash a native executable. Scan the declaration dependency graph syntactically before
    -- invoking the transitive collector; the collector remains authoritative for other axioms.
    diagnostic.putStrLn "audit-stage: theorem-found"
    let hasSorry := dependsOnSorry environment declaration
    diagnostic.putStrLn s!"audit-stage: sorry-scan-complete {hasSorry}"
    let axioms ← if hasSorry then
      pure #[``sorryAx]
    else
      let context : Core.Context := { fileName := "<alexandria-lean-audit>", fileMap := default }
      let state : Core.State := { env := environment }
      let (axioms, _) ← Core.CoreM.toIO (collectAxioms declaration) (ctx := context) (s := state)
      pure axioms
    diagnostic.putStrLn "audit-stage: axioms-collected"
    let axioms := axioms.qsort Name.lt
    let allowedSet : NameSet := allowed.foldl (fun result name => result.insert name) {}
    let unresolved := axioms.filter fun name => !allowedSet.contains name
    let strings := axioms.map toString
    let unresolvedStrings := unresolved.map toString
    let report := Json.mkObj [
      ("ok", Json.bool unresolved.isEmpty),
      ("declaration", Json.str (toString declaration)),
      ("declaration_kind", Json.str "theorem"),
      ("kernel_checked", Json.bool true),
      ("axioms", Lean.toJson strings),
      ("unresolved_assumptions", Lean.toJson unresolvedStrings)
    ]
    -- Serialize while the imported environment is alive: names/strings obtained
    -- from imported declarations must not escape through a borrowed JSON tree.
    let serialized := report.compress
    diagnostic.putStrLn s!"audit-stage: serialized {serialized}"
    pure serialized

unsafe def main (args : List String) : IO UInt32 := do
  let options ← match parseArgs args {} with
    | .ok value => pure value
    | .error message =>
        IO.println (errorJson message).compress
        return 2
  let some moduleName := options.moduleName | do
    IO.println (errorJson "--module is required").compress
    return 2
  let some declaration := options.declaration | do
    IO.println (errorJson "--declaration is required").compress
    return 2
  try
    let serialized ← audit moduleName declaration options.allowed
    IO.println serialized
    let report ← match Json.parse serialized with
      | .ok value => pure value
      | .error message => throw <| IO.userError message
    match report.getObjValAs? Bool "ok" with
    | .ok true => return 0
    | _ => return 1
  catch error =>
    IO.println (errorJson (toString error)).compress
    return 2
