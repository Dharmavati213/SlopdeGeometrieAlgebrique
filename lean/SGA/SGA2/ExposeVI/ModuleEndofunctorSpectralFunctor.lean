/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralSequence
import SGA.SGA2.ExposeI.TruncationSpectralObjectAdditive
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientFunctor
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Coefficient functoriality of the module-endofunctor spectral sequence

Actual resolution maps act on the mapped complexes and their complete
spectral sequences. Resolution homotopies prove independence of lifts and
the original coefficient functor laws, including canonical change of
injective resolution.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R) [T.Additive]
  (F : SheafOfModules.{u} R)


local instance moduleEndofunctorCoefficientHasDerivedCategory :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable {G H K : SheafOfModules.{u} R}
  {I : InjectiveResolution G} {J : InjectiveResolution H} {L : InjectiveResolution K}

/-- The actual mapped module complex map induced by a resolution map. -/
def moduleEndofunctorResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleEndofunctorResolutionInt R T I ⟶ moduleEndofunctorResolutionInt R T J :=
  (T.mapHomologicalComplex
    (ComplexShape.up ℤ)).map (extendMap a ComplexShape.embeddingUpNat)

/-- Localization of the original mapped module cochain map. -/
def moduleEndofunctorDerivedObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleEndofunctorDerivedObject R T I ⟶ moduleEndofunctorDerivedObject R T J :=
  DerivedCategory.Q.map (moduleEndofunctorResolutionIntMap R T a)

@[simp]
theorem moduleEndofunctorDerivedObjectMap_id :
    moduleEndofunctorDerivedObjectMap R T (𝟙 I.cocomplex) = 𝟙 _ := by
  simp only [moduleEndofunctorDerivedObjectMap, moduleEndofunctorResolutionIntMap, extendMap_id]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
theorem moduleEndofunctorDerivedObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    moduleEndofunctorDerivedObjectMap R T (a ≫ b) =
      moduleEndofunctorDerivedObjectMap R T a ≫ moduleEndofunctorDerivedObjectMap R T b := by
  simp [moduleEndofunctorDerivedObjectMap, moduleEndofunctorResolutionIntMap]

/-- The genuine derived map is independent of the resolution representative. -/
theorem moduleEndofunctorDerivedObjectMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    moduleEndofunctorDerivedObjectMap R T a = moduleEndofunctorDerivedObjectMap R T b :=
  DerivedCategory.Q_map_eq_of_homotopy _
    (T.mapHomotopy
      (h.extend ComplexShape.embeddingUpNat))


/-- The genuine truncation spectral-object map induced by a resolution map. -/
def moduleEndofunctorAbelianSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleEndofunctorAbelianSpectralObject R T F I ⟶
      moduleEndofunctorAbelianSpectralObject R T F J :=
  (ExposeI.truncationAbelianSpectralObjectFunctor
    (DerivedCategory.TStructure.t (C := SheafOfModules.{u} R))
    (moduleSupportDerivedHom R F)).map (moduleEndofunctorDerivedObjectMap R T a)

/-- A map of all actual page complexes and all original next-page homology isomorphisms. -/
def moduleEndofunctorSpectralSequenceMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleEndofunctorSpectralSequence R T F I ⟶ moduleEndofunctorSpectralSequence R T F J :=
  ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
    (moduleEndofunctorAbelianSpectralObjectMap R T F a) Abelian.SpectralObject.coreE₂Cohomological

@[simp]
theorem moduleEndofunctorSpectralSequenceMap_id :
    moduleEndofunctorSpectralSequenceMap R T F (𝟙 I.cocomplex) = 𝟙 _ := by
  dsimp only [moduleEndofunctorSpectralSequenceMap, moduleEndofunctorAbelianSpectralObjectMap]
  rw [moduleEndofunctorDerivedObjectMap_id]
  erw [CategoryTheory.Functor.map_id]
  exact ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_id _

@[reassoc]
theorem moduleEndofunctorSpectralSequenceMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    moduleEndofunctorSpectralSequenceMap R T F (a ≫ b) =
      moduleEndofunctorSpectralSequenceMap R T F a ≫
        moduleEndofunctorSpectralSequenceMap R T F b := by
  dsimp only [moduleEndofunctorSpectralSequenceMap, moduleEndofunctorAbelianSpectralObjectMap]
  rw [moduleEndofunctorDerivedObjectMap_comp, Functor.map_comp,
    ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_comp]

/-- Homotopic resolution maps induce equal maps on every page simultaneously. -/
theorem moduleEndofunctorSpectralSequenceMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    moduleEndofunctorSpectralSequenceMap R T F a =
      moduleEndofunctorSpectralSequenceMap R T F b := by
  dsimp only [moduleEndofunctorSpectralSequenceMap, moduleEndofunctorAbelianSpectralObjectMap]
  rw [moduleEndofunctorDerivedObjectMap_eq_of_homotopy R T h]

/-- The genuine coefficient morphism, computed with any chosen injective resolutions. -/
def moduleEndofunctorSpectralSequenceCoefficientMap (a : G ⟶ H)
    (I : InjectiveResolution G) (J : InjectiveResolution H) :
    moduleEndofunctorSpectralSequence R T F I ⟶ moduleEndofunctorSpectralSequence R T F J :=
  moduleEndofunctorSpectralSequenceMap R T F (InjectiveResolution.desc a J I)

/-- Every augmentation-compatible lift gives the same entire coefficient morphism. -/
theorem moduleEndofunctorSpectralSequenceMap_eq_coefficientMap
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι ≫ α = (CochainComplex.single₀ (SheafOfModules.{u} R)).map a ≫ J.ι) :
    moduleEndofunctorSpectralSequenceMap R T F α =
      moduleEndofunctorSpectralSequenceCoefficientMap R T F a I J :=
  moduleEndofunctorSpectralSequenceMap_eq_of_homotopy R T F
    (InjectiveResolution.descHomotopy a α (InjectiveResolution.desc a J I) hα
      (InjectiveResolution.desc_commutes a J I))

@[simp]
theorem moduleEndofunctorSpectralSequenceCoefficientMap_id (I : InjectiveResolution G) :
    moduleEndofunctorSpectralSequenceCoefficientMap R T F (𝟙 G) I I = 𝟙 _ :=
  (moduleEndofunctorSpectralSequenceMap_eq_of_homotopy R T F
    (InjectiveResolution.descIdHomotopy G I)).trans (moduleEndofunctorSpectralSequenceMap_id R T F)

@[reassoc]
theorem moduleEndofunctorSpectralSequenceCoefficientMap_comp (a : G ⟶ H) (b : H ⟶ K)
    (I : InjectiveResolution G) (J : InjectiveResolution H) (L : InjectiveResolution K) :
    moduleEndofunctorSpectralSequenceCoefficientMap R T F (a ≫ b) I L =
      moduleEndofunctorSpectralSequenceCoefficientMap R T F a I J ≫
        moduleEndofunctorSpectralSequenceCoefficientMap R T F b J L :=
  (moduleEndofunctorSpectralSequenceMap_eq_of_homotopy R T F
    (InjectiveResolution.descCompHomotopy a b I J L)).trans
      (moduleEndofunctorSpectralSequenceMap_comp R T F _ _)

/-- The genuine coefficient functor: genuine coefficient maps of the entire spectral sequence. -/
def moduleEndofunctorSpectralSequenceFunctor :
    SheafOfModules.{u} R ⥤ E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} where
  obj G := moduleEndofunctorSpectralSequence R T F (injectiveResolution G)
  map a := moduleEndofunctorSpectralSequenceCoefficientMap R T F a _ _
  map_id _ := moduleEndofunctorSpectralSequenceCoefficientMap_id R T F _
  map_comp a b := moduleEndofunctorSpectralSequenceCoefficientMap_comp R T F a b _ _ _

/-- Canonical change of injective resolution for the entire spectral sequence. -/
def moduleEndofunctorSpectralSequenceResolutionIso (I J : InjectiveResolution G) :
    moduleEndofunctorSpectralSequence R T F I ≅ moduleEndofunctorSpectralSequence R T F J where
  hom := moduleEndofunctorSpectralSequenceCoefficientMap R T F (𝟙 G) I J
  inv := moduleEndofunctorSpectralSequenceCoefficientMap R T F (𝟙 G) J I
  hom_inv_id := by rw [← moduleEndofunctorSpectralSequenceCoefficientMap_comp]; simp
  inv_hom_id := by rw [← moduleEndofunctorSpectralSequenceCoefficientMap_comp]; simp

end SGA.SGA2.ExposeVI
