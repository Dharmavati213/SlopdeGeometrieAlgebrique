/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.SheafFunctorSpectralSequence
import SGA.SGA2.ExposeI.TruncationSpectralObjectAdditive
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientFunctor
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Coefficient functoriality of the sheaf-valued truncation spectral sequence

Maps of injective resolutions give maps of the original Hom complexes
and hence of their entire spectral sequences. Homotopies prove independence
of the chosen lifts, the functor laws, and canonical change of resolution.
-/

noncomputable section

universe u v w

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C] [Abelian C]
  [HasInjectiveResolutions C] (T : C ⥤ Sheaf AddCommGrpCat.{u} X) [T.Additive]

omit [HasInjectiveResolutions C]

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

variable {G H K : C}
  {I : InjectiveResolution G} {J : InjectiveResolution H} {L : InjectiveResolution K}

/-- The actual sheaf Hom complex map induced by a resolution map. -/
def sheafFunctorResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :
    sheafFunctorResolutionInt T I ⟶ sheafFunctorResolutionInt T J :=
  ((T).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (extendMap a ComplexShape.embeddingUpNat)

/-- Localization of the original sheaf Hom cochain map. -/
def sheafFunctorDerivedObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    sheafFunctorDerivedObject T I ⟶ sheafFunctorDerivedObject T J :=
  DerivedCategory.Q.map (sheafFunctorResolutionIntMap T a)

@[simp]
theorem sheafFunctorDerivedObjectMap_id :
    sheafFunctorDerivedObjectMap T (𝟙 I.cocomplex) = 𝟙 _ := by
  simp only [sheafFunctorDerivedObjectMap, sheafFunctorResolutionIntMap, extendMap_id]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
theorem sheafFunctorDerivedObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    sheafFunctorDerivedObjectMap T (a ≫ b) =
      sheafFunctorDerivedObjectMap T a ≫ sheafFunctorDerivedObjectMap T b := by
  simp [sheafFunctorDerivedObjectMap, sheafFunctorResolutionIntMap]

/-- The genuine derived map is independent of the resolution representative. -/
theorem sheafFunctorDerivedObjectMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    sheafFunctorDerivedObjectMap T a = sheafFunctorDerivedObjectMap T b :=
  DerivedCategory.Q_map_eq_of_homotopy _
    ((T).mapHomotopy
      (h.extend ComplexShape.embeddingUpNat))

variable (Z : Closeds X)

/-- The genuine truncation spectral-object map induced by a resolution map. -/
def sheafFunctorSpectralAbelianSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    sheafFunctorSpectralAbelianSpectralObject T Z I ⟶
      sheafFunctorSpectralAbelianSpectralObject T Z J :=
  (ExposeI.truncationAbelianSpectralObjectFunctor
    (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X))
    (sheafFunctorDerivedSupportedHom Z)).map (sheafFunctorDerivedObjectMap T a)

/-- A map of all actual page complexes and all original next-page homology isomorphisms. -/
def sheafFunctorSpectralSequenceMap (a : I.cocomplex ⟶ J.cocomplex) :
    sheafFunctorSpectralSequence T Z I ⟶ sheafFunctorSpectralSequence T Z J :=
  ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
    (sheafFunctorSpectralAbelianSpectralObjectMap T Z a) Abelian.SpectralObject.coreE₂Cohomological

@[simp]
theorem sheafFunctorSpectralSequenceMap_id :
    sheafFunctorSpectralSequenceMap T Z (𝟙 I.cocomplex) = 𝟙 _ := by
  dsimp only [sheafFunctorSpectralSequenceMap, sheafFunctorSpectralAbelianSpectralObjectMap]
  rw [sheafFunctorDerivedObjectMap_id]
  erw [CategoryTheory.Functor.map_id]
  exact ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_id _

@[reassoc]
theorem sheafFunctorSpectralSequenceMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    sheafFunctorSpectralSequenceMap T Z (a ≫ b) =
      sheafFunctorSpectralSequenceMap T Z a ≫ sheafFunctorSpectralSequenceMap T Z b := by
  dsimp only [sheafFunctorSpectralSequenceMap, sheafFunctorSpectralAbelianSpectralObjectMap]
  rw [sheafFunctorDerivedObjectMap_comp, Functor.map_comp,
    ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_comp]

/-- Homotopic resolution maps induce equal maps on every page simultaneously. -/
theorem sheafFunctorSpectralSequenceMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    sheafFunctorSpectralSequenceMap T Z a = sheafFunctorSpectralSequenceMap T Z b := by
  dsimp only [sheafFunctorSpectralSequenceMap, sheafFunctorSpectralAbelianSpectralObjectMap]
  rw [sheafFunctorDerivedObjectMap_eq_of_homotopy T h]

/-- The genuine coefficient morphism, computed with any chosen injective resolutions. -/
def sheafFunctorSpectralSequenceCoefficientMap (a : G ⟶ H)
    (I : InjectiveResolution G) (J : InjectiveResolution H) :
    sheafFunctorSpectralSequence T Z I ⟶ sheafFunctorSpectralSequence T Z J :=
  sheafFunctorSpectralSequenceMap T Z (InjectiveResolution.desc a J I)

/-- Every augmentation-compatible lift gives the same entire coefficient morphism. -/
theorem sheafFunctorSpectralSequenceMap_eq_coefficientMap
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι ≫ α = (CochainComplex.single₀ (C)).map a ≫ J.ι) :
    sheafFunctorSpectralSequenceMap T Z α =
      sheafFunctorSpectralSequenceCoefficientMap T Z a I J :=
  sheafFunctorSpectralSequenceMap_eq_of_homotopy T Z
    (InjectiveResolution.descHomotopy a α (InjectiveResolution.desc a J I) hα
      (InjectiveResolution.desc_commutes a J I))

@[simp]
theorem sheafFunctorSpectralSequenceCoefficientMap_id (I : InjectiveResolution G) :
    sheafFunctorSpectralSequenceCoefficientMap T Z (𝟙 G) I I = 𝟙 _ :=
  (sheafFunctorSpectralSequenceMap_eq_of_homotopy T Z
    (InjectiveResolution.descIdHomotopy G I)).trans (sheafFunctorSpectralSequenceMap_id T Z)

@[reassoc]
theorem sheafFunctorSpectralSequenceCoefficientMap_comp (a : G ⟶ H) (b : H ⟶ K)
    (I : InjectiveResolution G) (J : InjectiveResolution H) (L : InjectiveResolution K) :
    sheafFunctorSpectralSequenceCoefficientMap T Z (a ≫ b) I L =
      sheafFunctorSpectralSequenceCoefficientMap T Z a I J ≫
        sheafFunctorSpectralSequenceCoefficientMap T Z b J L :=
  (sheafFunctorSpectralSequenceMap_eq_of_homotopy T Z
    (InjectiveResolution.descCompHomotopy a b I J L)).trans
      (sheafFunctorSpectralSequenceMap_comp T Z _ _)

/-- genuine coefficient maps of the entire spectral sequence. -/
def sheafFunctorSpectralSequenceFunctor :
    C ⥤ E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} where
  obj G := sheafFunctorSpectralSequence T Z (injectiveResolution G)
  map a := sheafFunctorSpectralSequenceCoefficientMap T Z a _ _
  map_id _ := sheafFunctorSpectralSequenceCoefficientMap_id T Z _
  map_comp a b := sheafFunctorSpectralSequenceCoefficientMap_comp T Z a b _ _ _

/-- Canonical change of injective resolution for the entire spectral sequence. -/
def sheafFunctorSpectralSequenceResolutionIso (I J : InjectiveResolution G) :
    sheafFunctorSpectralSequence T Z I ≅ sheafFunctorSpectralSequence T Z J where
  hom := sheafFunctorSpectralSequenceCoefficientMap T Z (𝟙 G) I J
  inv := sheafFunctorSpectralSequenceCoefficientMap T Z (𝟙 G) J I
  hom_inv_id := by rw [← sheafFunctorSpectralSequenceCoefficientMap_comp]; simp
  inv_hom_id := by rw [← sheafFunctorSpectralSequenceCoefficientMap_comp]; simp

end SGA.SGA2.ExposeVI
