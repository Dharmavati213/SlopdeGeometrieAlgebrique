import SGA
import Lean.Util.CollectAxioms

/-!
Audit every declaration defined in an `SGA.SGA1.*` or `SGA.Foundations.*` module
(foundation files use mathlib namespaces, so declarations are selected by module,
not by name). Run with `lake env lean CheckSGA1Axioms.lean` from `lean/`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted; this rejects
`sorryAx`, additional axioms and native evaluation.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let audited (m : Name) : Bool := (`SGA.SGA1).isPrefixOf m || (`SGA.Foundations).isPrefixOf m
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless audited env.header.moduleNames[idx.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    let extra := axioms.filter fun axiomName ↦ !allowed.contains axiomName
    unless extra.isEmpty do
      throwError "{name} depends on unapproved axioms: {extra}"
  unless count > 0 do
    throwError "No SGA 1 declarations were imported."
  logInfo m!"Audited {count} SGA 1 and foundation declarations: only propext, Classical.choice, and Quot.sound."
