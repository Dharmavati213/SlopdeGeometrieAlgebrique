/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatResidueExtensionGeneral
import SGA.SGA1.ExposeIX.EtaleEffectiveDescent
import SGA.SGA1.ExposeIX.StrictlyLocalDescent

/-!
# SGA 1, Exposé IX, 4.6 in SGA's form (algebraically closed residue fields)

IX.4.6: under the hypotheses of IX.4.4, with `S` locally noetherian and `X'` separated over `S'`,
a descent datum on an étale `S'`-scheme of finite presentation is effective iff it is effective
after base change to the spectrum of every complete noetherian local ring with algebraically
closed residue field (`isEffectiveIffStrictlyLocal : IsEffectiveIffStrictlyLocalStatement`).

`SGA.SGA1.ExposeIX.StrictlyLocalDescent` proves the criterion with *separably* closed residue
fields (`DescentDatum.isEffective_iff_forall_isSepClosed`). To pass to algebraically closed
residue fields we use, as SGA does, EGA 0_III 10.3.1 (`IsLocalRing.flatResidueExtensionStatement`):
a complete noetherian local ring `R` has a faithfully flat local extension `R → R'`, with `R'`
complete noetherian local with algebraically closed residue field
(`IsLocalRing.exists_flat_isAlgClosed_residueField`). A descent datum that is effective over
`Spec R'` is effective over `Spec R` (faithfully flat descent, IX.4.2 in the form
`DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated`).
-/

universe u

open CategoryTheory Limits MorphismProperty IsLocalRing AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

/-- IX.4.6 (as stated in SGA): under the hypotheses of IX.4.4 (`g` universally submersive, of
finite presentation, quasi-compact and quasi-separated), with `S` locally noetherian and
`X'` separated over `S'`, a descent datum on an étale `S'`-scheme `X'` of finite presentation is
effective iff it is effective after base change to the spectrum of every complete noetherian
local ring with algebraically closed residue field. -/
theorem isEffectiveIffStrictlyLocal : IsEffectiveIffStrictlyLocalStatement.{u} := by
  intro S' S X' g _ _ _ _ _ a _ D ha
  refine ⟨fun h R _ _ _ _ _ t ↦ h.baseChange t, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_isSepClosed ha]
  intro R _ _ _ _ _ t
  obtain ⟨R', _, _, _, _, _, hloc, hflat, halg⟩ := exists_flat_isAlgClosed_residueField R
  have : Module.FaithfullyFlat R R' := .of_flat_of_isLocalHom
  obtain ⟨hφf, hφs⟩ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›)
  set φ := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  have hx : ((D.baseChange t).baseChange φ).IsEffective etaleFinitePresentation :=
    (DescentDatum.isEffective_baseChange_baseChange_iff D _ _).mpr (h R' _)
  exact DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated
    (D.baseChange t) (MorphismProperty.pullback_snd _ _ ha) φ hx

end SGA.SGA1.ExposeIX
