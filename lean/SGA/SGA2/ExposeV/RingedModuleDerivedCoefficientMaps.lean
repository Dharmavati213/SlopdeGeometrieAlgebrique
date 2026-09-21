/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModulePushforwardSpectralSequence
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Original coefficient maps on the derived module direct image

Actual module resolution maps give equivariant maps of the original derived
additive direct-image objects. Resolution homotopies prove independence of
lifts and the coefficient functor laws, before passing to spectral sequences.
The unchanged higher-direct-image homology comparison is natural for these maps.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

local instance derivedCoefficientsHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

variable {M N P : SheafOfModules.{u} R}
  {I : InjectiveResolution M} {J : InjectiveResolution N} {K : InjectiveResolution P}

/-- The integer-indexed direct image of an actual module resolution map. -/
def ringedModulePushforwardResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardResolutionInt f φ I ⟶ ringedModulePushforwardResolutionInt f φ J :=
  ((ringedModulePushforward f φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (extendMap a ComplexShape.embeddingUpNat)

/-- Its original underlying additive cochain map. -/
def ringedModulePushforwardAdditiveResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardAdditiveResolutionInt f φ I ⟶
      ringedModulePushforwardAdditiveResolutionInt f φ J :=
  ((SheafOfModules.toSheaf S).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (ringedModulePushforwardResolutionIntMap f φ a)

/-- Localization of the original additive direct-image cochain map. -/
def ringedModulePushforwardDerivedObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardDerivedObject f φ I ⟶ ringedModulePushforwardDerivedObject f φ J :=
  DerivedCategory.Q.map (ringedModulePushforwardAdditiveResolutionIntMap f φ a)

@[simp]
theorem ringedModulePushforwardDerivedObjectMap_id :
    ringedModulePushforwardDerivedObjectMap f φ (𝟙 I.cocomplex) = 𝟙 _ := by
  simp only [ringedModulePushforwardDerivedObjectMap,
    ringedModulePushforwardAdditiveResolutionIntMap,
    ringedModulePushforwardResolutionIntMap, extendMap_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
theorem ringedModulePushforwardDerivedObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex) :
    ringedModulePushforwardDerivedObjectMap f φ (a ≫ b) =
      ringedModulePushforwardDerivedObjectMap f φ a ≫
        ringedModulePushforwardDerivedObjectMap f φ b := by
  simp [ringedModulePushforwardDerivedObjectMap, ringedModulePushforwardAdditiveResolutionIntMap,
    ringedModulePushforwardResolutionIntMap]

/-- The derived direct-image map is additive in the resolution map. -/
@[simp]
theorem ringedModulePushforwardDerivedObjectMap_add
    (a b : I.cocomplex ⟶ J.cocomplex) :
    ringedModulePushforwardDerivedObjectMap f φ (a + b) =
      ringedModulePushforwardDerivedObjectMap f φ a +
        ringedModulePushforwardDerivedObjectMap f φ b := by
  simp [ringedModulePushforwardDerivedObjectMap, ringedModulePushforwardAdditiveResolutionIntMap,
    ringedModulePushforwardResolutionIntMap]

/-- Homotopic module resolution maps give the same actual derived direct-image map. -/
theorem ringedModulePushforwardDerivedObjectMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    ringedModulePushforwardDerivedObjectMap f φ a =
      ringedModulePushforwardDerivedObjectMap f φ b :=
  DerivedCategory.Q_map_eq_of_homotopy _
    ((SheafOfModules.toSheaf S).mapHomotopy
      ((ringedModulePushforward f φ).mapHomotopy (h.extend ComplexShape.embeddingUpNat)))

/-- Every actual resolution map is equivariant for the original global target scalars. -/
@[reassoc]
theorem ringedModulePushforwardDerivedObjectMap_scalar
    (a : I.cocomplex ⟶ J.cocomplex) (r : S.obj.obj (op (⊤ : Opens Y))) :
    ringedModulePushforwardDerivedObjectMap f φ a ≫
        ringedModulePushforwardDerivedScalarRingHom f φ J r =
      ringedModulePushforwardDerivedScalarRingHom f φ I r ≫
        ringedModulePushforwardDerivedObjectMap f φ a :=
  moduleUnderlyingDerivedGlobalScalar_naturality S
    (ringedModulePushforwardResolutionIntMap f φ a) r

/-- The original coefficient morphism, computed using a module-injective resolution lift. -/
def ringedModulePushforwardDerivedCoefficientMap (a : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    ringedModulePushforwardDerivedObject f φ I ⟶ ringedModulePushforwardDerivedObject f φ J :=
  ringedModulePushforwardDerivedObjectMap f φ (InjectiveResolution.desc a J I)

/-- Any augmentation-compatible lift computes this same derived coefficient map. -/
theorem ringedModulePushforwardDerivedObjectMap_eq_coefficientMap
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι ≫ α = (CochainComplex.single₀ (SheafOfModules.{u} R)).map a ≫ J.ι) :
    ringedModulePushforwardDerivedObjectMap f φ α =
      ringedModulePushforwardDerivedCoefficientMap f φ a I J :=
  ringedModulePushforwardDerivedObjectMap_eq_of_homotopy f φ
    (InjectiveResolution.descHomotopy a α (InjectiveResolution.desc a J I) hα
      (InjectiveResolution.desc_commutes a J I))

@[simp]
theorem ringedModulePushforwardDerivedCoefficientMap_id (I : InjectiveResolution M) :
    ringedModulePushforwardDerivedCoefficientMap f φ (𝟙 M) I I = 𝟙 _ :=
  (ringedModulePushforwardDerivedObjectMap_eq_of_homotopy f φ
    (InjectiveResolution.descIdHomotopy M I)).trans
      (ringedModulePushforwardDerivedObjectMap_id f φ)

@[reassoc]
theorem ringedModulePushforwardDerivedCoefficientMap_comp (a : M ⟶ N) (b : N ⟶ P)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (K : InjectiveResolution P) :
    ringedModulePushforwardDerivedCoefficientMap f φ (a ≫ b) I K =
      ringedModulePushforwardDerivedCoefficientMap f φ a I J ≫
        ringedModulePushforwardDerivedCoefficientMap f φ b J K :=
  (ringedModulePushforwardDerivedObjectMap_eq_of_homotopy f φ
    (InjectiveResolution.descCompHomotopy a b I J K)).trans
      (ringedModulePushforwardDerivedObjectMap_comp f φ _ _)

/-- Additivity is independent of the choices of injective-resolution lifts. -/
@[simp]
theorem ringedModulePushforwardDerivedCoefficientMap_add (a b : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    ringedModulePushforwardDerivedCoefficientMap f φ (a + b) I J =
      ringedModulePushforwardDerivedCoefficientMap f φ a I J +
        ringedModulePushforwardDerivedCoefficientMap f φ b I J := by
  rw [← ringedModulePushforwardDerivedObjectMap_eq_coefficientMap f φ (a + b)
    (InjectiveResolution.desc a J I + InjectiveResolution.desc b J I)
    (by simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp])]
  exact ringedModulePushforwardDerivedObjectMap_add f φ _ _

/-- The original derived additive direct-image objects form a coefficient functor. -/
def ringedModulePushforwardDerivedObjectFunctor :
    SheafOfModules.{u} R ⥤ DerivedCategory (Sheaf AddCommGrpCat.{u} Y) where
  obj M := ringedModulePushforwardDerivedObject f φ (injectiveResolution M)
  map a := ringedModulePushforwardDerivedCoefficientMap f φ a _ _
  map_id _ := ringedModulePushforwardDerivedCoefficientMap_id f φ _
  map_comp a b := ringedModulePushforwardDerivedCoefficientMap_comp f φ a b _ _ _

instance : (ringedModulePushforwardDerivedObjectFunctor f φ).Additive where
  map_add := ringedModulePushforwardDerivedCoefficientMap_add f φ _ _ _ _

/-- The unchanged derived homology comparison respects every compatible coefficient lift. -/
@[reassoc]
theorem ringedModulePushforwardDerivedObjectHomologyIso_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).map
        (ringedModulePushforwardDerivedObjectMap f φ α) ≫
        (ringedModulePushforwardDerivedObjectHomologyIso f φ J q).hom =
      (ringedModulePushforwardDerivedObjectHomologyIso f φ I q).hom ≫
        (SheafOfModules.toSheaf S).map ((derivedRingedModulePushforward f φ q).map a) := by
  have hQ := (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} Y)
    (q : ℤ)).hom.naturality (ringedModulePushforwardAdditiveResolutionIntMap f φ α)
  simp only [Functor.comp_map] at hQ
  have hI := ExposeI.injectiveResolutionIntHomologyIso_naturality
    (ringedModulePushforward f φ ⋙ SheafOfModules.toSheaf S) a I J α hα q
  have hP := (ExposeI.rightDerivedPostcomposeIso (ringedModulePushforward f φ)
    (SheafOfModules.toSheaf S) q).hom.naturality a
  dsimp only [ringedModulePushforwardDerivedObjectHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [← Category.assoc, hQ, Category.assoc]
  simp only [Category.assoc]
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} Y)
    (q : ℤ)).hom.app (ringedModulePushforwardAdditiveResolutionInt f φ I))).mpr
  erw [← Category.assoc, hI, Category.assoc, hP]
  rfl

/-- The original normalized E₂ truncation comparison is natural for coefficient maps. -/
@[reassoc]
theorem ringedModulePushforwardE2TruncationIso_naturality
    (a : M ⟶ N) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (q : ℕ) :
    ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedObjectMap f φ α) ≫
        (ringedModulePushforwardE2TruncationIso f φ J q).hom =
      (ringedModulePushforwardE2TruncationIso f φ I q).hom ≫
        (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).map
          ((SheafOfModules.toSheaf S).map ((derivedRingedModulePushforward f φ q).map a)) := by
  dsimp only [ringedModulePushforwardE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [ExposeI.derivedSingleDegreeTruncationIsoSingle_naturality_assoc,
    ← Functor.map_comp, ringedModulePushforwardDerivedObjectHomologyIso_naturality f φ a α hα,
    Functor.map_comp, Category.assoc]

end SGA.SGA2.ExposeV
