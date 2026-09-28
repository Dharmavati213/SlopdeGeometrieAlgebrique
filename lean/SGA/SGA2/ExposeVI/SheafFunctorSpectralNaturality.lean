/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.SheafFunctorSpectralFunctor
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# Naturality of E₂ and abutment for the sheaf-valued spectral construction

The unchanged E₂ comparison carries the original page morphisms to supported
cohomology of the original right-derived coefficient maps. The flasque total
comparison likewise carries the actual total-interval map to the original
right-derived composite map. These are proved for every augmented resolution
lift, hence for the canonical coefficient spectral functor.
-/

noncomputable section

universe u v w

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C] [Abelian C]
  [HasInjectiveResolutions C] (T : C ⥤ Sheaf AddCommGrpCat.{u} X) [T.Additive]

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

variable {G H : C} {I : InjectiveResolution G} {J : InjectiveResolution H}

/-- The original derived-homology comparison retains every augmented coefficient lift. -/
@[reassoc]
theorem sheafFunctorDerivedHomologyIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
        (sheafFunctorDerivedObjectMap T α) ≫ (sheafFunctorDerivedHomologyIso T J q).hom =
      (sheafFunctorDerivedHomologyIso T I q).hom ≫ (T.rightDerived q).map a := by
  have hQ := (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} X)
    (q : ℤ)).hom.naturality (sheafFunctorResolutionIntMap T α)
  simp only [Functor.comp_map] at hQ
  dsimp only [sheafFunctorDerivedHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [← Category.assoc, hQ, Category.assoc]
  exact congrArg
    (fun f ↦ (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} X)
      (q : ℤ)).hom.app (sheafFunctorResolutionInt T I) ≫ f)
    (ExposeI.injectiveResolutionIntHomologyIso_naturality T a I J α hα q)

/-- The normalized one-degree truncation comparison retains the original derived map. -/
@[reassoc]
theorem sheafFunctorSpectralE2TruncationIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    ExposeI.derivedSingleDegreeTruncationMap (q : ℤ) (sheafFunctorDerivedObjectMap T α) ≫
        (sheafFunctorSpectralE2TruncationIso T J q).hom =
      (sheafFunctorSpectralE2TruncationIso T I q).hom ≫
        (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
          ((T.rightDerived q).map a) := by
  dsimp only [sheafFunctorSpectralE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [ExposeI.derivedSingleDegreeTruncationIsoSingle_naturality_assoc,
    ← Functor.map_comp, sheafFunctorDerivedHomologyIso_naturality T a α hα, Functor.map_comp]
  simp only [Category.assoc]

/-- The original shifted E₂ comparison is natural in the actual coefficient map. -/
@[reassoc]
theorem sheafFunctorSpectralE2TotalShiftIso_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ) :
    (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (sheafFunctorDerivedObjectMap T α))⟦(p : ℤ) + (q : ℤ)⟧' ≫
        (sheafFunctorSpectralE2TotalShiftIso T J p q).hom =
      (sheafFunctorSpectralE2TotalShiftIso T I p q).hom ≫
        ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
          ((T.rightDerived q).map a))⟦(p : ℤ)⟧' := by
  dsimp only [sheafFunctorSpectralE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, sheafFunctorSpectralE2TruncationIso_naturality T a α hα,
    Functor.map_comp_assoc, ExposeI.supportedSingleTotalShiftIso_naturality]
  simp only [Category.assoc]

variable (Z : Closeds X)

omit [HasInjectiveResolutions C] in
/-- The actual interval map is postcomposition by the original truncation map. -/
theorem sheafFunctorSpectralIntervalMap_apply
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (q : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (ExposeI.zZX_closed Z) ⟶
      (ExposeI.derivedSingleDegreeTruncation (sheafFunctorDerivedObject T I) (q : ℤ))⟦n⟧) :
    ((sheafFunctorSpectralAbelianSpectralObjectMap T Z α).hom n).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) x =
      x ≫ (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (sheafFunctorDerivedObjectMap T α))⟦n⟧' := rfl

section

omit [HasInjectiveResolutions C]
set_option maxHeartbeats 800000 in
-- Comparing the original first-page map expands the spectral-object page construction.
/-- The original first-page comparison commutes with actual page coefficient maps. -/
theorem sheafFunctorSpectralE2FirstPageIso_naturality_apply
    (α : I.cocomplex ⟶ J.cocomplex) (p q : ℕ)
    (x : ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    (sheafFunctorSpectralE2FirstPageIso T Z J p q).hom
        (((sheafFunctorSpectralSequenceMap T Z α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (sheafFunctorSpectralE2FirstPageIso T Z I p q).hom x ≫
        (ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
          (sheafFunctorDerivedObjectMap T α))⟦(p : ℤ) + (q : ℤ)⟧' := by
  have hm : ((sheafFunctorSpectralSequenceMap T Z α).hom 2).f ((p : ℤ), (q : ℤ)) ≫
        (sheafFunctorSpectralE2FirstPageIso T Z J p q).hom =
      (sheafFunctorSpectralE2FirstPageIso T Z I p q).hom ≫
        ((sheafFunctorSpectralAbelianSpectralObjectMap T Z α).hom
          ((p : ℤ) + (q : ℤ))).app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))) :=
    ExposeI.SpectralObjectCoefficientMaps.firstPageMap_hom
      (sheafFunctorSpectralAbelianSpectralObjectMap T Z α)
      Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
      (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  erw [sheafFunctorSpectralIntervalMap_apply] at h
  exact h

end

/-- The original E₂ equivalence has precisely its declared first-page and shift factors. -/
theorem sheafFunctorSpectralSequenceE2Equiv_apply (I : InjectiveResolution G) (p q : ℕ)
    (x : ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    sheafFunctorSpectralSequenceE2Equiv T Z I p q x =
      Abelian.Ext.homAddEquiv.symm
        ((sheafFunctorSpectralE2FirstPageIso T Z I p q).hom x ≫
          (sheafFunctorSpectralE2TotalShiftIso T I p q).hom) := rfl

/-- Supported Ext in the original sheaf category retains the original derived Hom map. -/
private theorem supportedExtHomEquiv_naturality
    {A B : Sheaf AddCommGrpCat.{u} X} (a : A ⟶ B) (p : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (ExposeI.zZX_closed Z) ⟶
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj A)⟦(p : ℤ)⟧) :
    Abelian.Ext.homAddEquiv.symm
        (x ≫ ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map a)⟦(p : ℤ)⟧') =
      ExposeI.H_Z_map Z a p (Abelian.Ext.homAddEquiv.symm x) := by
  apply (Abelian.Ext.homAddEquiv (X := ExposeI.zZX_closed Z) (Y := B) (n := p)).injective
  change (Abelian.Ext.homAddEquiv.symm _).hom =
    ((Abelian.Ext.homAddEquiv.symm x).comp (Abelian.Ext.mk₀ a) (add_zero p)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) =
    Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm x) ≫ _
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The genuine E₂ page morphism is supported cohomology of the original derived map. -/
theorem sheafFunctorSpectralSequenceE2Equiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    sheafFunctorSpectralSequenceE2Equiv T Z J p q
        (((sheafFunctorSpectralSequenceMap T Z α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      ExposeI.H_Z_map Z ((T.rightDerived q).map a) p
        (sheafFunctorSpectralSequenceE2Equiv T Z I p q x) := by
  rw [sheafFunctorSpectralSequenceE2Equiv_apply,
    sheafFunctorSpectralSequenceE2Equiv_apply,
    sheafFunctorSpectralE2FirstPageIso_naturality_apply,
    Category.assoc, sheafFunctorSpectralE2TotalShiftIso_naturality T a α hα,
    ← Category.assoc]
  exact supportedExtHomEquiv_naturality Z _ p _

/-- Every proved natural identification of derived values retains the original E₂ maps. -/
theorem sheafFunctorSpectralSequenceE2ComparedEquiv_naturality
    (U : C ⥤ Sheaf AddCommGrpCat.{u} X) (q : ℕ) (e : T.rightDerived q ≅ U)
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p : ℕ)
    (x : ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    sheafFunctorSpectralSequenceE2ComparedEquiv T Z U q e J p
        (((sheafFunctorSpectralSequenceMap T Z α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      ExposeI.H_Z_map Z (U.map a) p
        (sheafFunctorSpectralSequenceE2ComparedEquiv T Z U q e I p x) := by
  let P := Abelian.extFunctorObj (ExposeI.zZX_closed Z) p
  have hm := congrArg P.map (e.hom.naturality a)
  simp only [Functor.map_comp] at hm
  change P.map (e.hom.app H)
      (sheafFunctorSpectralSequenceE2Equiv T Z J p q
        (((sheafFunctorSpectralSequenceMap T Z α).hom 2).f ((p : ℤ), (q : ℤ)) x)) =
    P.map (U.map a) (P.map (e.hom.app G) (sheafFunctorSpectralSequenceE2Equiv T Z I p q x))
  rw [sheafFunctorSpectralSequenceE2Equiv_naturality T Z a α hα]
  generalize sheafFunctorSpectralSequenceE2Equiv T Z I p q x = y
  have hy := ConcreteCategory.congr_hom hm y
  simpa only [ConcreteCategory.comp_apply, P, Abelian.extFunctorObj, ExposeI.H_Z_map,
    AddCommGrpCat.hom_ofHom] using hy

/-- The actual map on the total interval, hence on its canonical image filtration. -/
def sheafFunctorSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :
    sheafFunctorSpectralTotal T Z I n ⟶ sheafFunctorSpectralTotal T Z J n :=
  ExposeI.SpectralObjectConvergence.totalMap (sheafFunctorSpectralAbelianSpectralObjectMap T Z α) n

/-- The actual total comparison intertwines original derived-composite coefficient maps. -/
theorem sheafFunctorSpectralAbutmentEquiv_naturality
    [∀ j, ExposeI.IsFlasque ((sheafFunctorResolutionInt T I).X j)]
    [∀ j, ExposeI.IsFlasque ((sheafFunctorResolutionInt T J).X j)]
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ)
    (x : sheafFunctorSpectralTotal T Z I n) :
    sheafFunctorSpectralAbutmentEquiv T Z J n (sheafFunctorSpectralTotalMap T Z α n x) =
      ((T ⋙ ExposeI.gammaZSectionsFunctor Z ⊤).rightDerived n).map a
        (sheafFunctorSpectralAbutmentEquiv T Z I n x) := by
  let eI := ExposeI.flasqueGammaComplexDerivedHomEquiv Z (sheafFunctorResolutionInt T I) 0 n
  let eJ := ExposeI.flasqueGammaComplexDerivedHomEquiv Z (sheafFunctorResolutionInt T J) 0 n
  let z := eI.symm x
  have he := ExposeI.flasqueGammaComplexDerivedHomEquiv_naturality Z
    (sheafFunctorResolutionIntMap T α) 0 n z
  change eJ _ = eI z ≫ (sheafFunctorDerivedObjectMap T α)⟦(n : ℤ)⟧' at he
  rw [AddEquiv.apply_symm_apply] at he
  change (ExposeI.injectiveResolutionIntHomologyIso
      (T ⋙ ExposeI.gammaZSectionsFunctor Z ⊤) J n).hom
      (eJ.symm (x ≫ (sheafFunctorDerivedObjectMap T α)⟦(n : ℤ)⟧')) = _
  rw [← he, AddEquiv.symm_apply_apply]
  exact ConcreteCategory.congr_hom
    (ExposeI.injectiveResolutionIntHomologyIso_naturality
      (T ⋙ ExposeI.gammaZSectionsFunctor Z ⊤) a I J α hα n) z

end SGA.SGA2.ExposeVI
