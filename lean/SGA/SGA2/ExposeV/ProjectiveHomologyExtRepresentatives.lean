/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ModuleHomologyRepresentatives
import SGA.SGA2.ExposeIV.ModuleExtDerivedLinear

/-! # Original Hom-cohomology representatives under the existing Ext comparison -/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite
open SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] {N : ModuleCat.{u} R}
  (P : ProjectiveResolution N) (M : ModuleCat.{u} R)

/-- The existing positive-degree linear comparison sends the class of the
original Hom cocycle to exactly its original `extMk` class. -/
theorem projectiveModuleHomologyLinearIsoExtSucc_mk (n : ℕ)
    (f : P.complex.X (n + 1) ⟶ M) (hf : P.complex.d (n + 2) (n + 1) ≫ f = 0) :
    (projectiveModuleHomologyLinearIsoExtSucc P M n).hom
        (moduleCohomologyMk (P.complex.linearYonedaObj R M) (n + 1) f hf) =
      P.extMk f (n + 2) rfl hf := by
  let K := P.complex.linearYonedaObj R M
  let D := projectiveModuleExtLinearHomologyData P M n
  let e := K.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)
  let x := moduleCocycleLift K (n + 1) f hf
  have hi : e.hom ≫ D.cyclesIso.hom ≫ D.i = K.iCycles (n + 1) := by
    rw [D.cyclesIso_hom_comp_i]
    exact K.cyclesIsoSc'_hom_iCycles n (n + 1) (n + 2) (by simp) (by simp)
  have hx : D.cyclesIso.hom (e.hom x) = (⟨f, hf⟩ : D.K) := by
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom hi x).trans (moduleCocycleLift_iCycles K (n + 1) f hf)
  have hπ : K.homologyπ (n + 1) ≫ (projectiveModuleHomologyLinearIsoExtSucc P M n).hom =
      e.hom ≫ D.cyclesIso.hom ≫ D.π := by
    dsimp only [projectiveModuleHomologyLinearIsoExtSucc, Iso.trans_hom]
    rw [← Category.assoc, K.π_homologyIsoSc'_hom n (n + 1) (n + 2) (by simp) (by simp),
      Category.assoc, D.homologyπ_comp_homologyIso_hom]
  change (projectiveModuleHomologyLinearIsoExtSucc P M n).hom (K.homologyπ (n + 1) x) =
    D.π (⟨f, hf⟩ : D.K)
  rw [← hx]
  exact ConcreteCategory.congr_hom hπ x

end SGA.SGA2.ExposeV
