/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleDerivedCoefficientMaps
import SGA.SGA2.ExposeV.RingedModuleSpectralModuleLift
import SGA.SGA2.ExposeV.SpectralObjectModuleCoefficientMaps

/-!
# V.3.2: the actual module spectral sequence is functorial in coefficients

Module resolution maps act on the original derived direct-image object and
its truncation spectral object, commuting with the retained global scalars.
Their module lifts give genuine maps of the entire original spectral sequence.
Actual resolution homotopies prove lift-independence, identity and composition
laws, and canonical change-of-resolution isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R) (Z : Closeds Y)

local instance spectralCoefficientsHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

variable {M N P : SheafOfModules.{u} R}
  {I : InjectiveResolution M} {J : InjectiveResolution N} {K : InjectiveResolution P}

/-- The original coefficient map on the canonical additive truncation spectral objects. -/
def ringedModulePushforwardAbelianSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardAbelianSpectralObject f φ Z I ⟶
      ringedModulePushforwardAbelianSpectralObject f φ Z J :=
  (ExposeI.truncationAbelianSpectralObjectFunctor
    (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y))
    (ringedDerivedSupportedHom Z)).map (ringedModulePushforwardDerivedObjectMap f φ a)

@[simp]
theorem ringedModulePushforwardAbelianSpectralObjectMap_id :
    ringedModulePushforwardAbelianSpectralObjectMap f φ Z (𝟙 I.cocomplex) = 𝟙 _ := by
  dsimp only [ringedModulePushforwardAbelianSpectralObjectMap]
  rw [ringedModulePushforwardDerivedObjectMap_id, CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
theorem ringedModulePushforwardAbelianSpectralObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex) :
    ringedModulePushforwardAbelianSpectralObjectMap f φ Z (a ≫ b) =
      ringedModulePushforwardAbelianSpectralObjectMap f φ Z a ≫
        ringedModulePushforwardAbelianSpectralObjectMap f φ Z b := by
  dsimp only [ringedModulePushforwardAbelianSpectralObjectMap]
  rw [ringedModulePushforwardDerivedObjectMap_comp, Functor.map_comp]

@[reassoc]
theorem ringedModulePushforwardAbelianSpectralObjectMap_scalar
    (a : I.cocomplex ⟶ J.cocomplex) (r : S.obj.obj (op (⊤ : Opens Y))) :
    ringedModulePushforwardAbelianSpectralObjectMap f φ Z a ≫
        ringedModulePushforwardSpectralScalarRingHom f φ Z J r =
      ringedModulePushforwardSpectralScalarRingHom f φ Z I r ≫
        ringedModulePushforwardAbelianSpectralObjectMap f φ Z a := by
  let T := ExposeI.truncationAbelianSpectralObjectFunctor
    (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} Y)) (ringedDerivedSupportedHom Z)
  change T.map (ringedModulePushforwardDerivedObjectMap f φ a) ≫
      T.map (ringedModulePushforwardDerivedScalarRingHom f φ J r) =
    T.map (ringedModulePushforwardDerivedScalarRingHom f φ I r) ≫
      T.map (ringedModulePushforwardDerivedObjectMap f φ a)
  rw [← Functor.map_comp, ringedModulePushforwardDerivedObjectMap_scalar, Functor.map_comp]

/-- The actual coefficient morphism of module spectral objects, with all connecting maps. -/
def ringedModulePushforwardModuleSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardModuleSpectralObject f φ Z I ⟶
      ringedModulePushforwardModuleSpectralObject f φ Z J :=
  spectralObjectModuleMap (ringedModulePushforwardSpectralScalarRingHom f φ Z I)
    (ringedModulePushforwardSpectralScalarRingHom f φ Z J)
    (ringedModulePushforwardAbelianSpectralObjectMap f φ Z a)
    (ringedModulePushforwardAbelianSpectralObjectMap_scalar f φ Z a)

@[simp]
theorem ringedModulePushforwardModuleSpectralObjectMap_id :
    ringedModulePushforwardModuleSpectralObjectMap f φ Z (𝟙 I.cocomplex) = 𝟙 _ := by
  unfold ringedModulePushforwardModuleSpectralObjectMap
  simp only [ringedModulePushforwardAbelianSpectralObjectMap_id, spectralObjectModuleMap_id]
  rfl

@[reassoc]
theorem ringedModulePushforwardModuleSpectralObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex) :
    ringedModulePushforwardModuleSpectralObjectMap f φ Z (a ≫ b) =
        ringedModulePushforwardModuleSpectralObjectMap f φ Z a ≫
        ringedModulePushforwardModuleSpectralObjectMap f φ Z b := by
  unfold ringedModulePushforwardModuleSpectralObjectMap
  simp only [ringedModulePushforwardAbelianSpectralObjectMap_comp]
  exact spectralObjectModuleMap_comp _ _ _ _ _ _ _

/-- Retaining the global scalar action preserves addition of resolution maps. -/
@[simp]
theorem ringedModulePushforwardModuleSpectralObjectMap_add
    (a b : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardModuleSpectralObjectMap f φ Z (a + b) =
      ringedModulePushforwardModuleSpectralObjectMap f φ Z a +
        ringedModulePushforwardModuleSpectralObjectMap f φ Z b := by
  unfold ringedModulePushforwardModuleSpectralObjectMap
    ringedModulePushforwardAbelianSpectralObjectMap
  simp only [ringedModulePushforwardDerivedObjectMap_add, Functor.map_add]
  exact spectralObjectModuleMap_add _ _ _ _ _ _

/-- Homotopic module lifts give exactly the same module spectral-object morphism. -/
theorem ringedModulePushforwardModuleSpectralObjectMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    ringedModulePushforwardModuleSpectralObjectMap f φ Z a =
      ringedModulePushforwardModuleSpectralObjectMap f φ Z b := by
  unfold ringedModulePushforwardModuleSpectralObjectMap
    ringedModulePushforwardAbelianSpectralObjectMap
  congr 1
  exact congrArg _ (ringedModulePushforwardDerivedObjectMap_eq_of_homotopy f φ h)

/-- The genuine module-linear coefficient map on every page and every next-page isomorphism. -/
def ringedModulePushforwardModuleSpectralSequenceMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardModuleSpectralSequence f φ Z I ⟶
      ringedModulePushforwardModuleSpectralSequence f φ Z J :=
  ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
    (ringedModulePushforwardModuleSpectralObjectMap f φ Z a)
    Abelian.SpectralObject.coreE₂Cohomological

@[simp]
theorem ringedModulePushforwardModuleSpectralSequenceMap_id :
    ringedModulePushforwardModuleSpectralSequenceMap f φ Z (𝟙 I.cocomplex) = 𝟙 _ := by
  dsimp only [ringedModulePushforwardModuleSpectralSequenceMap]
  rw [ringedModulePushforwardModuleSpectralObjectMap_id,
    ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_id]
  rfl

@[reassoc]
theorem ringedModulePushforwardModuleSpectralSequenceMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex) :
    ringedModulePushforwardModuleSpectralSequenceMap f φ Z (a ≫ b) =
      ringedModulePushforwardModuleSpectralSequenceMap f φ Z a ≫
        ringedModulePushforwardModuleSpectralSequenceMap f φ Z b := by
  dsimp only [ringedModulePushforwardModuleSpectralSequenceMap]
  rw [ringedModulePushforwardModuleSpectralObjectMap_comp,
    ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_comp]

/-- Addition of resolution maps induces addition on every whole page complex. -/
@[simp]
theorem ringedModulePushforwardModuleSpectralSequenceMap_add
    (a b : I.cocomplex ⟶ J.cocomplex) (r : ℤ) (hr : 2 ≤ r) :
    (ringedModulePushforwardModuleSpectralSequenceMap f φ Z (a + b)).hom r hr =
      (ringedModulePushforwardModuleSpectralSequenceMap f φ Z a).hom r hr +
        (ringedModulePushforwardModuleSpectralSequenceMap f φ Z b).hom r hr := by
  dsimp only [ringedModulePushforwardModuleSpectralSequenceMap]
  rw [ringedModulePushforwardModuleSpectralObjectMap_add]
  exact spectralSequenceMap_hom_add _ _ r hr

theorem ringedModulePushforwardModuleSpectralSequenceMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    ringedModulePushforwardModuleSpectralSequenceMap f φ Z a =
      ringedModulePushforwardModuleSpectralSequenceMap f φ Z b := by
  dsimp only [ringedModulePushforwardModuleSpectralSequenceMap]
  rw [ringedModulePushforwardModuleSpectralObjectMap_eq_of_homotopy f φ Z h]

/-- The original coefficient map between arbitrary chosen module-injective resolutions. -/
def ringedModulePushforwardModuleSpectralSequenceCoefficientMap (a : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    ringedModulePushforwardModuleSpectralSequence f φ Z I ⟶
      ringedModulePushforwardModuleSpectralSequence f φ Z J :=
  ringedModulePushforwardModuleSpectralSequenceMap f φ Z (InjectiveResolution.desc a J I)

/-- Any augmentation-compatible module lift computes the same entire spectral-sequence map. -/
theorem ringedModulePushforwardModuleSpectralSequenceMap_eq_coefficientMap
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι ≫ α = (CochainComplex.single₀ (SheafOfModules.{u} R)).map a ≫ J.ι) :
    ringedModulePushforwardModuleSpectralSequenceMap f φ Z α =
      ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I J :=
  ringedModulePushforwardModuleSpectralSequenceMap_eq_of_homotopy f φ Z
    (InjectiveResolution.descHomotopy a α (InjectiveResolution.desc a J I) hα
      (InjectiveResolution.desc_commutes a J I))

@[simp]
theorem ringedModulePushforwardModuleSpectralSequenceCoefficientMap_id
    (I : InjectiveResolution M) :
    ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) I I = 𝟙 _ :=
  (ringedModulePushforwardModuleSpectralSequenceMap_eq_of_homotopy f φ Z
    (InjectiveResolution.descIdHomotopy M I)).trans
      (ringedModulePushforwardModuleSpectralSequenceMap_id f φ Z)

@[reassoc]
theorem ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp (a : M ⟶ N) (b : N ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (K : InjectiveResolution P) :
    ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (a ≫ b) I K =
      ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I J ≫
        ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z b J K :=
  (ringedModulePushforwardModuleSpectralSequenceMap_eq_of_homotopy f φ Z
    (InjectiveResolution.descCompHomotopy a b I J K)).trans
      (ringedModulePushforwardModuleSpectralSequenceMap_comp f φ Z _ _)

/-- Every page is additive in the original coefficient morphism, independently of its lift. -/
@[simp]
theorem ringedModulePushforwardModuleSpectralSequenceCoefficientMap_add (a b : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (r : ℤ) (hr : 2 ≤ r) :
    (ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (a + b) I J).hom r hr =
      (ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I J).hom r hr +
        (ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z b I J).hom r hr := by
  rw [← ringedModulePushforwardModuleSpectralSequenceMap_eq_coefficientMap f φ Z (a + b)
    (InjectiveResolution.desc a J I + InjectiveResolution.desc b J I)
    (by simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp])]
  exact ringedModulePushforwardModuleSpectralSequenceMap_add f φ Z _ _ r hr

/-- V.3.2's actual module spectral sequence, functorial in the original coefficient module. -/
def ringedModulePushforwardModuleSpectralSequenceFunctor :
    SheafOfModules.{u} R ⥤
      E₂CohomologicalSpectralSequence (ModuleCat.{u + 1} (S.obj.obj (op (⊤ : Opens Y)))) where
  obj M := ringedModulePushforwardModuleSpectralSequence f φ Z (injectiveResolution M)
  map a := ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a _ _
  map_id _ := ringedModulePushforwardModuleSpectralSequenceCoefficientMap_id f φ Z _
  map_comp a b := ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp f φ Z a b _ _ _

/-- Each page of V.3.2 is an additive functor of the coefficient module sheaf. -/
instance ringedModulePushforwardModuleSpectralSequencePageFunctor_additive
    (r : ℤ) (hr : 2 ≤ r) :
    (ringedModulePushforwardModuleSpectralSequenceFunctor f φ Z ⋙
      CategoryTheory.SpectralSequence.pageFunctor _ _ _ r hr).Additive where
  map_add := ringedModulePushforwardModuleSpectralSequenceCoefficientMap_add f φ Z _ _ _ _ r hr

/-- Canonical module-linear change of resolution, induced by the original identity coefficient. -/
def ringedModulePushforwardModuleSpectralSequenceResolutionIso
    (I J : InjectiveResolution M) :
    ringedModulePushforwardModuleSpectralSequence f φ Z I ≅
      ringedModulePushforwardModuleSpectralSequence f φ Z J where
  hom := ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) I J
  inv := ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) J I
  hom_inv_id := by
    rw [← ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp]
    simp
  inv_hom_id := by
    rw [← ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp]
    simp

/-- Canonical change of resolution commutes with all original coefficient maps. -/
@[reassoc]
theorem ringedModulePushforwardModuleSpectralSequenceResolutionIso_naturality
    (a : M ⟶ N) (I I' : InjectiveResolution M) (J J' : InjectiveResolution N) :
    (ringedModulePushforwardModuleSpectralSequenceResolutionIso f φ Z I I').hom ≫
        ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I' J' =
      ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z a I J ≫
        (ringedModulePushforwardModuleSpectralSequenceResolutionIso f φ Z J J').hom := by
  change ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) I I' ≫ _ =
    _ ≫ ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 N) J J'
  rw [← ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp,
    ← ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp]
  simp

/-- Canonical change of resolution satisfies the cocycle identity as module spectral sequences. -/
@[simp]
theorem ringedModulePushforwardModuleSpectralSequenceResolutionIso_trans
    (I J K : InjectiveResolution M) :
    ringedModulePushforwardModuleSpectralSequenceResolutionIso f φ Z I J ≪≫
        ringedModulePushforwardModuleSpectralSequenceResolutionIso f φ Z J K =
      ringedModulePushforwardModuleSpectralSequenceResolutionIso f φ Z I K := by
  apply Iso.ext
  change ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) I J ≫
    ringedModulePushforwardModuleSpectralSequenceCoefficientMap f φ Z (𝟙 M) J K = _
  rw [← ringedModulePushforwardModuleSpectralSequenceCoefficientMap_comp]
  simp only [Category.id_comp]
  rfl

/-- The original additive page comparisons commute with every coefficient resolution map. -/
@[reassoc]
theorem ringedModulePushforwardModulePageXForgetIso_naturality
    (a : I.cocomplex ⟶ J.cocomplex) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens Y)))) AddCommGrpCat).map
        (((ringedModulePushforwardModuleSpectralSequenceMap f φ Z a).hom r hr).f pq) ≫
        (ringedModulePushforwardModulePageXForgetIso f φ Z J r hr pq).hom =
      (ringedModulePushforwardModulePageXForgetIso f φ Z I r hr pq).hom ≫
        ((ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
          (ringedModulePushforwardAbelianSpectralObjectMap f φ Z a)
          Abelian.SpectralObject.coreE₂Cohomological).hom r hr).f pq :=
  spectralObjectModulePageXForgetIso_naturality
    (ringedModulePushforwardSpectralScalarRingHom f φ Z I)
    (ringedModulePushforwardSpectralScalarRingHom f φ Z J)
    (ringedModulePushforwardAbelianSpectralObjectMap f φ Z a)
    (ringedModulePushforwardAbelianSpectralObjectMap_scalar f φ Z a) r hr pq

end SGA.SGA2.ExposeV
