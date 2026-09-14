/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSpectralAbutment
import SGA.SGA2.ExposeV.RingedModuleSpectralCoefficientFunctor
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# Coefficient maps on V.3.2's original abutment and filtration

The actual module spectral-object maps act on the canonical total object and
its finite submodule filtration. The unchanged stable-page comparisons commute
with the resulting genuine associated-graded maps. Supported-complex homology
and source supported cohomology retain the original coefficient maps.
-/

noncomputable section

universe u v

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat ComposableArrows

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

private theorem moduleHomologyForgetIso_inv_naturality_apply
    {B : Type u} [Ring B] {K L : CochainComplex (ModuleCat.{v} B) ℤ} (a : K ⟶ L)
    (n : ℤ) (x : K.homology n) :
    (ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
        (ComplexShape.up ℤ) L n).inv (homologyMap a n x) =
      homologyMap (((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex _).map a) n
        ((ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
          (ComplexShape.up ℤ) K n).inv x) := by
  have hm := (ExposeI.complexHomologyMapNatIso (forget₂ (ModuleCat B) AddCommGrpCat)
    (ComplexShape.up ℤ) n).inv.naturality a
  simp only [CategoryTheory.Functor.comp_map] at hm
  have h := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance abutmentNaturalityHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

variable {M N : SheafOfModules.{u} R} {I : InjectiveResolution M} {J : InjectiveResolution N}

/-- The original supported-section complex map of a module resolution map. -/
def ringedModulePushforwardSupportedComplexMap (α : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardSupportedComplex f φ Z I ⟶
      ringedModulePushforwardSupportedComplex f φ Z J :=
  ((moduleGammaZSectionsFunctor S Z ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (ringedModulePushforwardResolutionIntMap f φ α)

/-- The actual module-linear coefficient map on the canonical total interval. -/
def ringedModulePushforwardSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :
    ringedModulePushforwardSpectralTotal f φ Z I n ⟶
      ringedModulePushforwardSpectralTotal f φ Z J n :=
  ExposeI.SpectralObjectConvergence.totalMap
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z α) n

/-- The total coefficient map is original derived postcomposition. -/
theorem ringedModulePushforwardSpectralTotalMap_apply
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) 0).obj (ExposeI.zZX_closed Z) ⟶
      (ringedModulePushforwardDerivedObject f φ I)⟦n⟧) :
    ringedModulePushforwardSpectralTotalMap f φ Z α n x =
      x ≫ (ringedModulePushforwardDerivedObjectMap f φ α)⟦n⟧' := rfl

/-- The genuine map between the actual finite-filtration subobjects. -/
def ringedModulePushforwardSpectralFiniteFiltrationMap
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n q :
        ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y)))) ⟶
      (ringedModulePushforwardSpectralFiniteFiltration f φ Z J n q :
        ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y)))) :=
  ExposeI.SpectralObjectConvergence.filtrationSubobjectMap
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z α) n (q.1 : ℤ)

/-- The actual total map restricts to every original finite-filtration term. -/
@[reassoc]
theorem ringedModulePushforwardSpectralFiniteFiltrationMap_arrow
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    ringedModulePushforwardSpectralFiniteFiltrationMap f φ Z α n q ≫
        (ringedModulePushforwardSpectralFiniteFiltration f φ Z J n q).arrow =
      (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n q).arrow ≫
        ringedModulePushforwardSpectralTotalMap f φ Z α n :=
  ExposeI.SpectralObjectConvergence.filtrationSubobjectMap_arrow
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z α) n (q.1 : ℤ)

/-- Coefficients induce the original cokernel map on each genuine associated-graded quotient. -/
def ringedModulePushforwardSpectralGradedPieceMap
    (α : I.cocomplex ⟶ J.cocomplex) (n q : ℤ) :
    ringedModulePushforwardSpectralGradedPiece f φ Z I n q ⟶
      ringedModulePushforwardSpectralGradedPiece f φ Z J n q :=
  ExposeI.SpectralObjectConvergence.gradedPieceMap
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z α) n q

/-- The unchanged stable-page isomorphisms commute with the original associated-graded maps. -/
@[reassoc]
theorem ringedModulePushforwardModuleStablePageIsoGraded_naturality
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1))
    (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((ringedModulePushforwardModuleSpectralSequenceMap f φ Z α).hom r (by lia)).f
        ((n : ℤ) - q, q) ≫ (ringedModulePushforwardModuleStablePageIsoGraded f φ Z J n q r hr).hom =
      (ringedModulePushforwardModuleStablePageIsoGraded f φ Z I n q r hr).hom ≫
        ringedModulePushforwardSpectralGradedPieceMap f φ Z α n q :=
  ExposeI.SpectralObjectConvergence.stablePageIsoGradedTotal_naturality
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z α) n q r hr

set_option maxHeartbeats 800000 in
-- The original forgetful homology and derived-Hom comparisons use the same complex carriers.
/-- The original module-linear supported-homology comparison respects every coefficient map. -/
theorem ringedModulePushforwardSupportedHomologyTotalLinearEquiv_naturality
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ)
    (x : (ringedModulePushforwardSupportedComplex f φ Z I).homology n) :
    ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z J n
        (homologyMap (ringedModulePushforwardSupportedComplexMap f φ Z α) n x) =
      ringedModulePushforwardSpectralTotalMap f φ Z α n
        (ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z I n x) := by
  let KI := ringedModulePushforwardAdditiveResolutionInt f φ I
  let KJ := ringedModulePushforwardAdditiveResolutionInt f φ J
  let F := forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat
  let eI := ExposeI.complexHomologyMapIso F (ComplexShape.up ℤ)
    (ringedModulePushforwardSupportedComplex f φ Z I) n
  let eJ := ExposeI.complexHomologyMapIso F (ComplexShape.up ℤ)
    (ringedModulePushforwardSupportedComplex f φ Z J) n
  change ExposeI.flasqueGammaComplexDerivedHomEquiv Z KJ 0 n
      (eJ.inv (homologyMap (ringedModulePushforwardSupportedComplexMap f φ Z α) n x)) =
    ExposeI.flasqueGammaComplexDerivedHomEquiv Z KI 0 n (eI.inv x) ≫
      (ringedModulePushforwardDerivedObjectMap f φ α)⟦n⟧'
  rw [moduleHomologyForgetIso_inv_naturality_apply]
  exact ExposeI.flasqueGammaComplexDerivedHomEquiv_naturality Z
    (ringedModulePushforwardAdditiveResolutionIntMap f φ α) 0 n (eI.inv x)

/-- The original supported-complex-to-source comparison retains actual coefficient maps. -/
@[reassoc]
theorem ringedModulePushforwardSupportedHomologyIsoSource_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ) :
    homologyMap (ringedModulePushforwardSupportedComplexMap f φ Z α) (n : ℤ) ≫
        (ringedModulePushforwardSupportedHomologyIsoSource f φ Z J n).hom =
      (ringedModulePushforwardSupportedHomologyIsoSource f φ Z I n).hom ≫
        (ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).map
          ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).map a) := by
  dsimp only [ringedModulePushforwardSupportedHomologyIsoSource, Iso.trans_hom]
  erw [← Category.assoc, ExposeI.injectiveResolutionIntHomologyIso_naturality
    (ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤) a I J α hα n,
    Category.assoc]
  exact congrArg (fun k ↦ (ExposeI.injectiveResolutionIntHomologyIso
    (ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤) I n).hom ≫ k)
    ((ringedModuleSupportedGlobalRightDerivedIso f φ Z n).hom.naturality a)

set_option maxHeartbeats 800000 in
-- Expand only the original total/homology/source composite.
set_option maxRecDepth 2048 in
/-- The original abutment equivalence written using its unchanged comparison factors. -/
theorem ringedModulePushforwardSpectralAbutmentLinearEquiv_apply
    (I : InjectiveResolution M) (n : ℕ)
    (x : ringedModulePushforwardSpectralTotal f φ Z I n) :
    ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n x =
      (ringedModulePushforwardSupportedHomologyIsoSource f φ Z I n).hom
        ((ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z I n).symm x) := rfl

set_option maxHeartbeats 800000 in
-- The original total and source objects lie in different module universes.
/-- V.3.2's unchanged module-linear abutment comparison retains original source coefficient maps. -/
theorem ringedModulePushforwardSpectralAbutmentLinearEquiv_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ)
    (x : ringedModulePushforwardSpectralTotal f φ Z I n) :
    ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z J n
        (ringedModulePushforwardSpectralTotalMap f φ Z α n x) =
      ((ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).map
        ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).map a))
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n x) := by
  have hh := congrArg (ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z J n).symm
    (ringedModulePushforwardSupportedHomologyTotalLinearEquiv_naturality f φ Z α n
      ((ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z I n).symm x))
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at hh
  have hs := ConcreteCategory.congr_hom
    (ringedModulePushforwardSupportedHomologyIsoSource_naturality f φ Z a α hα n)
    ((ringedModulePushforwardSupportedHomologyTotalLinearEquiv f φ Z I n).symm x)
  simp only [ConcreteCategory.comp_apply] at hs
  rw [ringedModulePushforwardSpectralAbutmentLinearEquiv_apply,
    ringedModulePushforwardSpectralAbutmentLinearEquiv_apply, ← hh]
  exact hs

/-- The canonical total map of a coefficient morphism, using the same resolution lift
as the original module spectral-sequence coefficient functor. -/
def ringedModulePushforwardSpectralTotalCoefficientMap (a : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (n : ℤ) :
    ringedModulePushforwardSpectralTotal f φ Z I n ⟶
      ringedModulePushforwardSpectralTotal f φ Z J n :=
  ringedModulePushforwardSpectralTotalMap f φ Z (InjectiveResolution.desc a J I) n

/-- On the abutment, the coefficient functor is original source supported cohomology
with the prescribed restriction of global scalars. -/
theorem ringedModulePushforwardSpectralTotalCoefficientMap_abutment
    (a : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N) (n : ℕ)
    (x : ringedModulePushforwardSpectralTotal f φ Z I n) :
    ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z J n
        (ringedModulePushforwardSpectralTotalCoefficientMap f φ Z a I J n x) =
      ((ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).map
        ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).map a))
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n x) := by
  dsimp only [ringedModulePushforwardSpectralTotalCoefficientMap]
  exact ringedModulePushforwardSpectralAbutmentLinearEquiv_naturality f φ Z a
    (InjectiveResolution.desc a J I) (InjectiveResolution.desc_commutes_zero a J I) n x

/-- The original source filtration is the actual range of each transported filtration arrow. -/
theorem ringedModulePushforwardSourceFiniteFiltration_eq_range
    (I : InjectiveResolution M) (n : ℕ) (q : Fin (n + 2)) :
    ringedModulePushforwardSourceFiniteFiltration f φ Z I n q =
      LinearMap.range
        ((ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n).toLinearMap.comp
          (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n q).arrow.hom) := by
  change (LinearMap.range
      (ringedModulePushforwardSpectralFiniteFiltration f φ Z I n q).arrow.hom).map
        (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z I n).toLinearMap = _
  exact (LinearMap.range_comp _ _).symm

set_option maxHeartbeats 800000 in
-- Transport the genuine filtration arrows across the original cross-universe abutment maps.
/-- Original source supported-cohomology coefficient maps preserve the actual finite filtration. -/
theorem ringedModulePushforwardSourceFiniteFiltration_map_le
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ) (q : Fin (n + 2)) :
    Submodule.map
        (((ModuleCat.restrictScalars (ringedGlobalRingHom f φ)).map
          ((derivedModuleGammaZSections R (Z.preimage f.hom.continuous) ⊤ n).map a)).hom)
        (ringedModulePushforwardSourceFiniteFiltration f φ Z I n q) ≤
      ringedModulePushforwardSourceFiniteFiltration f φ Z J n q := by
  rw [ringedModulePushforwardSourceFiniteFiltration_eq_range,
    ringedModulePushforwardSourceFiniteFiltration_eq_range]
  rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
  refine ⟨ringedModulePushforwardSpectralFiniteFiltrationMap f φ Z α n q t, ?_⟩
  have hf := ConcreteCategory.congr_hom
    (ringedModulePushforwardSpectralFiniteFiltrationMap_arrow f φ Z α n q) t
  simp only [ConcreteCategory.comp_apply] at hf
  have ht := ringedModulePushforwardSpectralAbutmentLinearEquiv_naturality f φ Z a α hα n
    ((ringedModulePushforwardSpectralFiniteFiltration f φ Z I n q).arrow t)
  exact (congrArg (ringedModulePushforwardSpectralAbutmentLinearEquiv f φ Z J n) hf).trans ht

/-- The actual finite filtration on original source cohomology is independent of resolution. -/
theorem ringedModulePushforwardSourceFiniteFiltration_eq
    (I J : InjectiveResolution M) (n : ℕ) :
    ringedModulePushforwardSourceFiniteFiltration f φ Z I n =
      ringedModulePushforwardSourceFiniteFiltration f φ Z J n := by
  have h (I J : InjectiveResolution M) (q : Fin (n + 2)) :
      ringedModulePushforwardSourceFiniteFiltration f φ Z I n q ≤
        ringedModulePushforwardSourceFiniteFiltration f φ Z J n q := by
    have hh := ringedModulePushforwardSourceFiniteFiltration_map_le f φ Z (𝟙 M)
      (InjectiveResolution.desc (𝟙 M) J I) (InjectiveResolution.desc_commutes_zero (𝟙 M) J I) n q
    simpa only [CategoryTheory.Functor.map_id, ModuleCat.hom_id, Submodule.map_id] using hh
  apply OrderHom.ext
  funext q
  exact le_antisymm (h I J q) (h J I q)

end SGA.SGA2.ExposeV
