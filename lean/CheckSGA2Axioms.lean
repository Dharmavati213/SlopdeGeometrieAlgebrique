import SGA
import Lean.Util.CollectAxioms

/-!
Audit every imported declaration in the `SGA.SGA2` namespace, including
private declarations from SGA2 modules and transitive dependencies.
Run with `lake env lean CheckSGA2Axioms.lean`.
Only Lean's standard logical axioms are permitted; in particular this rejects
`sorryAx`, additional mathematical axioms, and native evaluation axioms.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`SGA.SGA2).isPrefixOf name || name.toString.startsWith "_private.SGA.SGA2." then
      count := count + 1
      let axioms ← collectAxioms name
      let extra := axioms.filter fun axiomName ↦ !allowed.contains axiomName
      unless extra.isEmpty do
        throwError "{name} depends on unapproved axioms: {extra}"
  unless count > 0 do
    throwError "No SGA2 declarations were imported."
  logInfo m!"Audited {count} SGA2 declarations: only propext, Classical.choice, and Quot.sound."
