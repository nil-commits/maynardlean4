import Lean
import Lean.Util.CollectAxioms

/-!
Trustless verification helper: loads the compiled environments of `Challenge` and `Solution`
separately and verifies that:
1. Every target theorem exists in both environments as a `thmInfo`.
2. Its universe parameters and type `Expr` in `Solution` are syntactically identical to those
   in `Challenge`.
3. Its transitive axiom dependencies in `Solution` are a subset of
   `{propext, Classical.choice, Quot.sound}` (rejecting `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`, and any custom axiom).
-/

open Lean

def targetTheorems : List Name :=
  [ `unconditional_prime_gap_le_246
  , `bounded_prime_gaps_246_unconditional
  , `frequently_consecutive_prime_gap_le_246
  ]

def permittedAxioms : List Name :=
  [ `propext
  , `Classical.choice
  , `Quot.sound
  ]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let envC ← importModules #[{ module := `Challenge }] {} (trustLevel := 0)
  let envS ← importModules #[{ module := `Solution }] {} (trustLevel := 0)
  for name in targetTheorems do
    let some infoC := envC.find? name
      | throw <| IO.userError s!"Challenge missing theorem: {name}"
    let some infoS := envS.find? name
      | throw <| IO.userError s!"Solution missing theorem: {name}"
    match infoC, infoS with
    | .thmInfo tC, .thmInfo tS =>
      if tC.levelParams != tS.levelParams then
        throw <| IO.userError s!"Level params mismatch for {name}: {tC.levelParams} vs {tS.levelParams}"
      if tC.type != tS.type then
        throw <| IO.userError s!"Type mismatch for {name}!"
      let (axioms, _) ← Core.CoreM.toIO (Lean.collectAxioms name)
        { fileName := "<verify_challenge>", fileMap := default }
        { env := envS }
      let bad := axioms.toList.filter (fun ax => !permittedAxioms.contains ax)
      if !bad.isEmpty then
        throw <| IO.userError s!"Disallowed axioms for {name}: {bad}"
      IO.println s!"OK {name}: exact type match, axioms = {axioms.toList}"
    | _, _ =>
      throw <| IO.userError s!"Expected theorem info for {name}"
  IO.println "ALL CHALLENGE THEOREMS VERIFIED."
