/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SpectralObjectModuleDifferentials
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientMaps

/-! # Canonical comparisons of whole module-valued and additive pages -/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject
open SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps (pageHomologyData)

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B] {ι κ : Type*} [Preorder ι]
  (S : Abelian.SpectralObject AddCommGrpCat.{v} ι) (ρ : B →+* End S)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)

/-- The canonical comparison of page terms for an arbitrary spectral-sequence core. -/
def spectralObjectModulePageTermForgetIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj
        (SpectralSequence.pageX (spectralObjectModuleLift S ρ) data r pq hr) ≅
      SpectralSequence.pageX S data r pq hr :=
  spectralObjectModuleEForgetIso S ρ
    (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by lia) rfl

@[reassoc]
lemma spectralObjectModulePageXIso_inv_forget (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        (SpectralSequence.pageXIso (spectralObjectModuleLift S ρ) data r hr pq
          i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
        (spectralObjectModulePageTermForgetIso S ρ data r hr pq).hom =
      (spectralObjectModuleEForgetIso S ρ
        (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (SpectralSequence.pageXIso S data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
          n₀ n₁ n₂ h hn₁ hn₂).inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst h₀ h₁ h₂ h₃ h hn₂
  simp only [SpectralSequence.pageXIso, eqToIso_refl, Iso.refl_inv]
  rfl

/-- The canonical comparisons intertwine every original page differential. -/
@[reassoc]
lemma spectralObjectModulePageD_forget (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        (SpectralSequence.pageD (spectralObjectModuleLift S ρ) data r pq pq' hr) ≫
        (spectralObjectModulePageTermForgetIso S ρ data r hr pq').hom =
      (spectralObjectModulePageTermForgetIso S ρ data r hr pq).hom ≫
        SpectralSequence.pageD S data r pq pq' hr := by
  classical
  dsimp only [SpectralSequence.pageD]
  split_ifs with h
  · rw [Functor.map_comp, Category.assoc, spectralObjectModulePageXIso_inv_forget]
    exact spectralObjectModuleD_forget_assoc S ρ _ _ _ _ _ _ _ _ _ _ _ _ _
  · rw [Functor.map_zero, zero_comp, comp_zero]

/-- Forgetting module structure recovers each original page as a whole complex. -/
def spectralObjectModulePageForgetIso (r : ℤ) (hr : r₀ ≤ r) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (c r)).obj
        (SpectralSequence.page (spectralObjectModuleLift S ρ) data r hr) ≅
      SpectralSequence.page S data r hr :=
  HomologicalComplex.Hom.isoOfComponents
    (fun pq ↦ spectralObjectModulePageTermForgetIso S ρ data r hr pq)
    (fun pq pq' _ ↦ (spectralObjectModulePageD_forget S ρ data r hr pq pq').symm)

section

variable [S.HasSpectralSequence data] [(spectralObjectModuleLift S ρ).HasSpectralSequence data]

/-- The retained scalar comparison on the cycles of the actual page homology data. -/
def spectralObjectModulePageHomologyCyclesForgetIso
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj
        (pageHomologyData data (spectralObjectModuleLift S ρ) r r' hrr' hr pq).left.K ≅
      (pageHomologyData data S r r' hrr' hr pq).left.K :=
  spectralObjectModuleEForgetIso S ρ (homOfLE (data.le₀₁ r' pq (by lia)))
    (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by lia) rfl

@[reassoc]
lemma spectralObjectModulePageHomologyCyclesForgetIso_hom_i
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    (spectralObjectModulePageHomologyCyclesForgetIso S ρ data r r' hrr' hr pq).hom ≫
        (pageHomologyData data S r r' hrr' hr pq).left.i =
      (forget₂ (ModuleCat B) AddCommGrpCat).map
        (pageHomologyData data (spectralObjectModuleLift S ρ) r r' hrr' hr pq).left.i ≫
        (spectralObjectModulePageTermForgetIso S ρ data r hr pq).hom := by
  change (spectralObjectModuleEForgetIso S ρ _ _ _ _ _ _ _ _).hom ≫
      (S.mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ≫
        (SpectralSequence.pageXIso S data r hr pq _ _ _ _ rfl rfl rfl rfl
          _ _ _ rfl).inv) =
    (forget₂ (ModuleCat B) AddCommGrpCat).map
      ((spectralObjectModuleLift S ρ).mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ≫
        (SpectralSequence.pageXIso (spectralObjectModuleLift S ρ) data r hr pq
          _ _ _ _ rfl rfl rfl rfl _ _ _ rfl).inv) ≫ _
  rw [Functor.map_comp, Category.assoc, spectralObjectModulePageXIso_inv_forget]
  exact (spectralObjectModuleMap_forget_assoc S ρ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

@[reassoc]
lemma spectralObjectModulePageHomologyπ_forget
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        (pageHomologyData data (spectralObjectModuleLift S ρ) r r' hrr' hr pq).left.π ≫
        (spectralObjectModulePageTermForgetIso S ρ data r' (by lia) pq).hom =
      (spectralObjectModulePageHomologyCyclesForgetIso S ρ data r r' hrr' hr pq).hom ≫
        (pageHomologyData data S r r' hrr' hr pq).left.π :=
  spectralObjectModuleMap_forget S ρ _ _ _ _ _ _ _ _ _ _ _ _

/-- The original mapped page-homology data, with its original next-page object and maps. -/
def spectralObjectModulePageHomologyMapData
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (c r) pq).map
        (spectralObjectModulePageForgetIso S ρ data r hr).hom)
      ((pageHomologyData data (spectralObjectModuleLift S ρ) r r' hrr' hr pq).left.map
        (forget₂ (ModuleCat B) AddCommGrpCat))
      (pageHomologyData data S r r' hrr' hr pq).left where
  φK := (spectralObjectModulePageHomologyCyclesForgetIso S ρ data r r' hrr' hr pq).hom
  φH := (spectralObjectModulePageTermForgetIso S ρ data r' (by lia) pq).hom
  commi := spectralObjectModulePageHomologyCyclesForgetIso_hom_i S ρ data r r' hrr' hr pq
  commπ := spectralObjectModulePageHomologyπ_forget S ρ data r r' hrr' hr pq
  commf' := by
    rw [← cancel_mono (pageHomologyData data S r r' hrr' hr pq).left.i,
      Category.assoc, spectralObjectModulePageHomologyCyclesForgetIso_hom_i]
    simp only [ShortComplex.LeftHomologyData.map_f', ← Functor.map_comp_assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc]
    exact ((spectralObjectModulePageForgetIso S ρ data r hr).hom.comm _ _).symm

/-- Forgetting module structure preserves the original homology-to-next-page isomorphism. -/
@[reassoc]
lemma spectralObjectModulePageForgetIso_homologyIso
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    HomologicalComplex.homologyMap (spectralObjectModulePageForgetIso S ρ data r hr).hom pq ≫
        (SpectralSequence.homologyIso S data r r' hrr' hr pq).hom =
      (((SpectralSequence.page (spectralObjectModuleLift S ρ) data r hr).sc pq).mapHomologyIso
        (forget₂ (ModuleCat B) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat B) AddCommGrpCat).map
          (SpectralSequence.homologyIso (spectralObjectModuleLift S ρ) data r r' hrr' hr pq).hom ≫
        (spectralObjectModulePageTermForgetIso S ρ data r' (by lia) pq).hom := by
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  let h := (pageHomologyData data (spectralObjectModuleLift S ρ) r r' hrr' hr pq).left
  simp only [SpectralSequence.homologyIso, SpectralSequence.homologyIso',
    SpectralSequence.pageXIso, Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_inv]
  erw [Category.comp_id, Category.comp_id]
  change HomologicalComplex.homologyMap (spectralObjectModulePageForgetIso S ρ data r hr).hom pq ≫
      (pageHomologyData data S r r' hrr' hr pq).left.homologyIso.hom =
    (((SpectralSequence.page (spectralObjectModuleLift S ρ) data r hr).sc pq).mapHomologyIso
      F).hom ≫
      F.map h.homologyIso.hom ≫
        (spectralObjectModulePageTermForgetIso S ρ data r' (by lia) pq).hom
  rw [h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  exact (spectralObjectModulePageHomologyMapData S ρ data r r' hrr' hr pq).homologyMap_comm

end

/-- The actual exact-forgetful image of a module-valued spectral sequence. -/
def moduleSpectralSequenceForget
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} B) c r₀) :
    CategoryTheory.SpectralSequence AddCommGrpCat.{v} c r₀ where
  page r hr := ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (c r)).obj
    (E.page r hr)
  iso r r' pq hrr' hr := ((E.page r hr).sc pq).mapHomologyIso
    (forget₂ (ModuleCat B) AddCommGrpCat) ≪≫
      (forget₂ (ModuleCat B) AddCommGrpCat).mapIso (E.iso r r' pq hrr' hr)

variable [S.HasSpectralSequence data] [(spectralObjectModuleLift S ρ).HasSpectralSequence data]

unseal Abelian.SpectralObject.spectralSequence in
/-- The original spectral sequence is recovered, including its original next-page isomorphisms. -/
def spectralObjectModuleForgetMap :
    moduleSpectralSequenceForget ((spectralObjectModuleLift S ρ).spectralSequence data) ⟶
      S.spectralSequence data where
  hom r hr := (spectralObjectModulePageForgetIso S ρ data r hr).hom
  comm r r' pq hrr' hr := spectralObjectModulePageForgetIso_homologyIso S ρ data r r' hrr' hr pq

private def spectralSequenceIsoOfPageIsos {C : Type*} [Category C] [Abelian C]
    {E E' : CategoryTheory.SpectralSequence C c r₀} (a : E ⟶ E')
    (ha : ∀ (r : ℤ) (hr : r₀ ≤ r), IsIso (a.hom r hr)) : E ≅ E' where
  hom := a
  inv :=
    { hom r hr := by
        haveI := ha r hr
        exact inv (a.hom r hr)
      comm r r' pq hrr' hr := by
        have := ha r hr
        have := ha r' (by lia)
        rw [← cancel_epi (HomologicalComplex.homologyMap (a.hom r hr) pq),
          ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          IsIso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp,
          a.comm_assoc r r' pq hrr' hr]
        simp only [← HomologicalComplex.comp_f,
          IsIso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]
    }
  hom_inv_id := by
    apply CategoryTheory.SpectralSequence.hom_ext
    intro r hr
    have := ha r hr
    exact IsIso.hom_inv_id (a.hom r hr)
  inv_hom_id := by
    apply CategoryTheory.SpectralSequence.hom_ext
    intro r hr
    have := ha r hr
    exact IsIso.inv_hom_id (a.hom r hr)

unseal Abelian.SpectralObject.spectralSequence in
/-- The canonical comparison is an isomorphism of the whole spectral sequences. -/
def spectralObjectModuleForgetIso :
    moduleSpectralSequenceForget ((spectralObjectModuleLift S ρ).spectralSequence data) ≅
      S.spectralSequence data :=
  spectralSequenceIsoOfPageIsos (spectralObjectModuleForgetMap S ρ data) (fun r hr ↦ by
    change IsIso (spectralObjectModulePageForgetIso S ρ data r hr).hom
    infer_instance)

end SGA.SGA2.ExposeV
