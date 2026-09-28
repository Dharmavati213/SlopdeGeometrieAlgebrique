/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-! # Naturality of the existing first-page computation -/

noncomputable section

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

section

variable {C ι : Type*} [Category C] [Abelian C] [Category ι]
  {S T : Abelian.SpectralObject C ι} (φ : S ⟶ T)

@[reassoc]
lemma EMap_EIsoH_hom {i j : ι} (f : i ⟶ j) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    EMap φ (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫ (T.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (S.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (φ.hom n₁).app (mk₁ f) := by
  rw [← cancel_epi (S.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂), πE_EMap_assoc]
  rw [← S.cyclesIsoH_hom_EIsoH_inv n₀ n₁ n₂ hn₁ hn₂ f,
    ← T.cyclesIsoH_hom_EIsoH_inv n₀ n₁ n₂ hn₁ hn₂ f]
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  rw [← cancel_epi (S.toCycles (𝟙 i) f f (by simp) n₁), toCycles_cyclesMap_assoc]
  simp

end

section

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  {S T : Abelian.SpectralObject C ι} (φ : S ⟶ T)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)
  [data.HasFirstPageComputation] [S.HasSpectralSequence data] [T.HasSpectralSequence data]

unseal Abelian.SpectralObject.spectralSequence in
/-- The original first-page isomorphism intertwines the actual page morphism
with the corresponding coefficient map of the spectral object. -/
@[reassoc]
lemma firstPageMap_hom (pq : κ) (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq) (n : ℤ) (hn : n = data.deg pq) :
    ((spectralSequenceMap φ data).hom r₀ (by rfl)).f pq ≫
        (T.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n hn).hom =
      (S.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n hn).hom ≫
        (φ.hom n).app (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) := by
  dsimp only [spectralSequenceFirstPageXIso, Iso.trans_hom, spectralSequencePageXIso,
    spectralSequenceMap, pageMap]
  rw [← cancel_epi
    (SpectralSequence.pageXIso S data r₀ (by rfl) pq i₁ i₁ i₂ i₂
      (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃])
      (n - 1) n (n + 1) hn).inv]
  rw [← Category.assoc, pageXIso_inv_pageXMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact EMap_EIsoH_hom φ _ _ _ _ _ _

end

end SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps
