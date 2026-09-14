/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.InjectiveHomology
import Mathlib.Algebra.Homology.LocalCohomology

/-!
# SGA 2, Exposé II, Lemma 9: injective acyclicity of algebraic local cohomology

Higher module-valued Ext vanishes on injective coefficient modules. Taking
the direct limit over ideal powers proves the same vanishing for mathlib's
algebraic local cohomology. These results require no noetherian hypothesis
and provide the Ext-vanishing input for II.9(a) ⇒ (b).
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- Higher Ext, defined by projective resolutions in the first argument,
vanishes on injective coefficient modules. -/
theorem isZero_Ext_succ_of_injective (X E : ModuleCat.{u} R) [Injective E] (n : ℕ) :
    IsZero (((Ext R (ModuleCat.{u} R) (n + 1)).obj (op X)).obj E) := by
  let P := projectiveResolution X
  apply IsZero.of_iso _ (P.isoExt (n + 1) E)
  apply IsZero.of_iso _ (linearYonedaObjHomologyIso P.complex E (n + 1))
  have h : IsZero (P.complex.homology (n + 1)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (P.complex_exactAt_succ n)
  exact ((linearYoneda R (ModuleCat.{u} R)).obj E).map_isZero h.op

/-- Positive-degree Ext vanishes for injective coefficients. -/
theorem isZero_Ext_of_injective (X E : ModuleCat.{u} R) [Injective E]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Ext R (ModuleCat.{u} R) n).obj (op X)).obj E) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isZero_Ext_succ_of_injective X E n

/-- Positive-degree algebraic local cohomology vanishes on injective
modules, since every Ext module in its defining direct system vanishes. -/
theorem isZero_localCohomology_succ_of_injective (I : Ideal R)
    (E : ModuleCat.{u} R) [Injective E] (n : ℕ) :
    IsZero ((_root_.localCohomology I (n + 1)).obj E) := by
  let D := localCohomology.diagram (localCohomology.idealPowersDiagram I) (n + 1)
  let G := D ⋙ (evaluation _ _).obj E
  have hG : ∀ j, IsZero (G.obj j) := fun j =>
    isZero_Ext_succ_of_injective
      ((localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).obj j.unop)
      E n
  have h : IsZero (colimit G) := by
    apply isZero_colimit_of_zero_transitions
    intro j
    exact ⟨j, 𝟙 j, (hG j).eq_of_src _ _⟩
  exact h.of_iso (colimitObjIsoColimitCompEvaluation D E)

/-- Injective modules are acyclic for algebraic local cohomology in every
strictly positive degree. -/
theorem isZero_localCohomology_of_injective (I : Ideal R)
    (E : ModuleCat.{u} R) [Injective E] (n : ℕ) (hn : 0 < n) :
    IsZero ((_root_.localCohomology I n).obj E) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isZero_localCohomology_succ_of_injective I E n

end SGA.SGA2.ExposeII
