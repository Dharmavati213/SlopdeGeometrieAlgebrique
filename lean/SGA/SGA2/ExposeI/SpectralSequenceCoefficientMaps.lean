/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

/-! # Actual page maps induced by spectral-object coefficient morphisms -/

noncomputable section

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  {S T : Abelian.SpectralObject C ι} (φ : S ⟶ T)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

/-- The coefficient map on the actual term of any page. -/
def pageXMap (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    SpectralSequence.pageX S data r pq hr ⟶ SpectralSequence.pageX T data r pq hr :=
  EMap φ (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by lia) rfl

@[reassoc]
lemma pageXIso_inv_pageXMap (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (SpectralSequence.pageXIso S data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
      n₀ n₁ n₂ h hn₁ hn₂).inv ≫ pageXMap φ data r hr pq =
    EMap φ (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
      (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂ ≫
      (SpectralSequence.pageXIso T data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
        n₀ n₁ n₂ h hn₁ hn₂).inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst h₀ h₁ h₂ h₃ h hn₂
  simp [SpectralSequence.pageXIso, pageXMap, SpectralSequence.pageX]

/-- Coefficient maps commute with the actual differentials on every page. -/
@[reassoc]
lemma pageXMap_d (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    pageXMap φ data r hr pq ≫ SpectralSequence.pageD T data r pq pq' hr =
      SpectralSequence.pageD S data r pq pq' hr ≫ pageXMap φ data r hr pq' := by
  classical
  dsimp only [SpectralSequence.pageD]
  split_ifs with h
  · rw [Category.assoc, pageXIso_inv_pageXMap]
    exact EMap_d_assoc φ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp

/-- An actual morphism of the full page complexes, preserving all
differentials. -/
def pageMap (r : ℤ) (hr : r₀ ≤ r) :
    SpectralSequence.page S data r hr ⟶ SpectralSequence.page T data r hr where
  f pq := pageXMap φ data r hr pq
  comm' pq pq' _ := pageXMap_d φ data r hr pq pq'

section

variable [S.HasSpectralSequence data] [T.HasSpectralSequence data]

/-- The existing page-homology data, with canonical index choices. -/
abbrev pageHomologyData (S : Abelian.SpectralObject C ι) [S.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ((SpectralSequence.page S data r hr).sc pq).HomologyData :=
  SpectralSequence.homologyData S data r r' hrr' hr
    ((c r).prev pq) pq ((c r).next pq) rfl rfl
    (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq) (data.i₃ r' pq)
    rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl

/-- The coefficient map on the actual cycles used in the page-homology
construction. -/
def pageHomologyCyclesMap (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    (pageHomologyData data S r r' hrr' hr pq).left.K ⟶
      (pageHomologyData data T r r' hrr' hr pq).left.K :=
  EMap φ (homOfLE (data.le₀₁ r' pq (by lia))) (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq)) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by lia) rfl

@[reassoc]
lemma pageHomologyCyclesMap_i (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    pageHomologyCyclesMap φ data r r' hrr' hr pq ≫
        (pageHomologyData data T r r' hrr' hr pq).left.i =
      (pageHomologyData data S r r' hrr' hr pq).left.i ≫ pageXMap φ data r hr pq := by
  change EMap φ _ _ _ _ _ _ _ _ ≫
      (T.mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _ ≫
        (SpectralSequence.pageXIso T data r hr pq _ _ _ _ rfl rfl rfl rfl
          _ _ _ rfl).inv) =
    (S.mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _ ≫
        (SpectralSequence.pageXIso S data r hr pq _ _ _ _ rfl rfl rfl rfl
          _ _ _ rfl).inv) ≫ pageXMap φ data r hr pq
  rw [Category.assoc, pageXIso_inv_pageXMap]
  exact EMap_map_assoc φ _ _ _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
lemma pageHomology_π_pageXMap (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    (pageHomologyData data S r r' hrr' hr pq).left.π ≫ pageXMap φ data r' (by lia) pq =
      pageHomologyCyclesMap φ data r r' hrr' hr pq ≫
        (pageHomologyData data T r r' hrr' hr pq).left.π := by
  exact (EMap_map φ _ _ _ _ _ _ _ _ _ _ _ _).symm

/-- The genuine coefficient maps respect the homology data that defines the
existing next-page isomorphism. -/
def pageHomologyMapData (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (pageMap φ data r hr))
      (pageHomologyData data S r r' hrr' hr pq).left
      (pageHomologyData data T r r' hrr' hr pq).left where
  φK := pageHomologyCyclesMap φ data r r' hrr' hr pq
  φH := pageXMap φ data r' (by lia) pq
  commi := pageHomologyCyclesMap_i φ data r r' hrr' hr pq
  commπ := pageHomology_π_pageXMap φ data r r' hrr' hr pq
  commf' := by
    rw [← cancel_mono (pageHomologyData data T r r' hrr' hr pq).left.i,
      Category.assoc, pageHomologyCyclesMap_i]
    simp only [ShortComplex.LeftHomologyData.f'_i_assoc, Category.assoc,
      ShortComplex.LeftHomologyData.f'_i]
    exact ((pageMap φ data r hr).comm _ _).symm

/-- The actual homology-to-next-page isomorphisms commute with coefficient
maps. No replacement isomorphism or compatibility hypothesis is introduced. -/
@[reassoc]
lemma pageMap_homologyIso (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    HomologicalComplex.homologyMap (pageMap φ data r hr) pq ≫
        (SpectralSequence.homologyIso T data r r' hrr' hr pq).hom =
      (SpectralSequence.homologyIso S data r r' hrr' hr pq).hom ≫
        pageXMap φ data r' (by lia) pq := by
  simp only [SpectralSequence.homologyIso, SpectralSequence.homologyIso',
      SpectralSequence.pageXIso, SpectralSequence.pageX,
      Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_inv, Category.assoc]
  erw [Category.comp_id, Category.id_comp]
  exact (pageHomologyMapData φ data r r' hrr' hr pq).homologyMap_comm

unseal Abelian.SpectralObject.spectralSequence in
/-- An actual morphism of the existing spectral sequences, with the original
pages, differentials, and homology-to-next-page isomorphisms. -/
def spectralSequenceMap : S.spectralSequence data ⟶ T.spectralSequence data where
  hom r hr := pageMap φ data r hr
  comm r r' pq hrr' hr := pageMap_homologyIso φ data r r' hrr' hr pq

end

end SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps
