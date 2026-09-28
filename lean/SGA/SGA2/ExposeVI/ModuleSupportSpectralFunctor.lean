/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportSpectralSequence
import SGA.SGA2.ExposeI.TruncationSpectralObjectAdditive
import SGA.SGA2.ExposeI.SpectralSequenceCoefficientFunctor
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# SGA 2, VI.1.6.3: the actual coefficient spectral functor

Maps of injective resolutions give maps of the original supported module complexes
and hence of their entire spectral sequences. Homotopies prove independence
of the chosen lifts, the functor laws, and canonical change of resolution.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)
  (F : SheafOfModules.{u} R)


local instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable {G H K : SheafOfModules.{u} R}
  {I : InjectiveResolution G} {J : InjectiveResolution H} {L : InjectiveResolution K}

/-- The actual module-support complex map induced by a resolution map. -/
def moduleSupportResolutionIntMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleSupportResolutionInt R Z I ⟶ moduleSupportResolutionInt R Z J :=
  ((moduleGammaZSheafFunctor R Z).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (extendMap a ComplexShape.embeddingUpNat)

/-- Localization of the original module-support cochain map. -/
def moduleSupportDerivedObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleSupportDerivedObject R Z I ⟶ moduleSupportDerivedObject R Z J :=
  DerivedCategory.Q.map (moduleSupportResolutionIntMap R Z a)

@[simp]
theorem moduleSupportDerivedObjectMap_id :
    moduleSupportDerivedObjectMap R Z (𝟙 I.cocomplex) = 𝟙 _ := by
  simp only [moduleSupportDerivedObjectMap, moduleSupportResolutionIntMap, extendMap_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
theorem moduleSupportDerivedObjectMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    moduleSupportDerivedObjectMap R Z (a ≫ b) =
      moduleSupportDerivedObjectMap R Z a ≫ moduleSupportDerivedObjectMap R Z b := by
  simp [moduleSupportDerivedObjectMap, moduleSupportResolutionIntMap]

/-- The genuine derived map is independent of the resolution representative. -/
theorem moduleSupportDerivedObjectMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    moduleSupportDerivedObjectMap R Z a = moduleSupportDerivedObjectMap R Z b :=
  DerivedCategory.Q_map_eq_of_homotopy _
    ((moduleGammaZSheafFunctor R Z).mapHomotopy
      (h.extend ComplexShape.embeddingUpNat))


/-- The genuine truncation spectral-object map induced by a resolution map. -/
def moduleSupportAbelianSpectralObjectMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleSupportAbelianSpectralObject R Z F I ⟶
      moduleSupportAbelianSpectralObject R Z F J :=
  (ExposeI.truncationAbelianSpectralObjectFunctor
    (DerivedCategory.TStructure.t (C := SheafOfModules.{u} R))
    (moduleSupportDerivedHom R F)).map (moduleSupportDerivedObjectMap R Z a)

/-- A map of all actual page complexes and all original next-page homology isomorphisms. -/
def moduleSupportSpectralSequenceMap (a : I.cocomplex ⟶ J.cocomplex) :
    moduleSupportSpectralSequence R Z F I ⟶ moduleSupportSpectralSequence R Z F J :=
  ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap
    (moduleSupportAbelianSpectralObjectMap R Z F a) Abelian.SpectralObject.coreE₂Cohomological

@[simp]
theorem moduleSupportSpectralSequenceMap_id :
    moduleSupportSpectralSequenceMap R Z F (𝟙 I.cocomplex) = 𝟙 _ := by
  dsimp only [moduleSupportSpectralSequenceMap, moduleSupportAbelianSpectralObjectMap]
  rw [moduleSupportDerivedObjectMap_id]
  erw [CategoryTheory.Functor.map_id]
  exact ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_id _

@[reassoc]
theorem moduleSupportSpectralSequenceMap_comp
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ L.cocomplex) :
    moduleSupportSpectralSequenceMap R Z F (a ≫ b) =
      moduleSupportSpectralSequenceMap R Z F a ≫ moduleSupportSpectralSequenceMap R Z F b := by
  dsimp only [moduleSupportSpectralSequenceMap, moduleSupportAbelianSpectralObjectMap]
  rw [moduleSupportDerivedObjectMap_comp, Functor.map_comp,
    ExposeI.SpectralObjectCoefficientMaps.spectralSequenceMap_comp]

/-- Homotopic resolution maps induce equal maps on every page simultaneously. -/
theorem moduleSupportSpectralSequenceMap_eq_of_homotopy
    {a b : I.cocomplex ⟶ J.cocomplex} (h : Homotopy a b) :
    moduleSupportSpectralSequenceMap R Z F a = moduleSupportSpectralSequenceMap R Z F b := by
  dsimp only [moduleSupportSpectralSequenceMap, moduleSupportAbelianSpectralObjectMap]
  rw [moduleSupportDerivedObjectMap_eq_of_homotopy R Z h]

/-- The genuine coefficient morphism, computed with any chosen injective resolutions. -/
def moduleSupportSpectralSequenceCoefficientMap (a : G ⟶ H)
    (I : InjectiveResolution G) (J : InjectiveResolution H) :
    moduleSupportSpectralSequence R Z F I ⟶ moduleSupportSpectralSequence R Z F J :=
  moduleSupportSpectralSequenceMap R Z F (InjectiveResolution.desc a J I)

/-- Every augmentation-compatible lift gives the same entire coefficient morphism. -/
theorem moduleSupportSpectralSequenceMap_eq_coefficientMap
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι ≫ α = (CochainComplex.single₀ (SheafOfModules.{u} R)).map a ≫ J.ι) :
    moduleSupportSpectralSequenceMap R Z F α =
      moduleSupportSpectralSequenceCoefficientMap R Z F a I J :=
  moduleSupportSpectralSequenceMap_eq_of_homotopy R Z F
    (InjectiveResolution.descHomotopy a α (InjectiveResolution.desc a J I) hα
      (InjectiveResolution.desc_commutes a J I))

@[simp]
theorem moduleSupportSpectralSequenceCoefficientMap_id (I : InjectiveResolution G) :
    moduleSupportSpectralSequenceCoefficientMap R Z F (𝟙 G) I I = 𝟙 _ :=
  (moduleSupportSpectralSequenceMap_eq_of_homotopy R Z F
    (InjectiveResolution.descIdHomotopy G I)).trans (moduleSupportSpectralSequenceMap_id R Z F)

@[reassoc]
theorem moduleSupportSpectralSequenceCoefficientMap_comp (a : G ⟶ H) (b : H ⟶ K)
    (I : InjectiveResolution G) (J : InjectiveResolution H) (L : InjectiveResolution K) :
    moduleSupportSpectralSequenceCoefficientMap R Z F (a ≫ b) I L =
      moduleSupportSpectralSequenceCoefficientMap R Z F a I J ≫
        moduleSupportSpectralSequenceCoefficientMap R Z F b J L :=
  (moduleSupportSpectralSequenceMap_eq_of_homotopy R Z F
    (InjectiveResolution.descCompHomotopy a b I J L)).trans
      (moduleSupportSpectralSequenceMap_comp R Z F _ _)

/-- **VI.1.6.3, spectral functor:** genuine coefficient maps of the entire spectral sequence. -/
def moduleSupportSpectralSequenceFunctor :
    SheafOfModules.{u} R ⥤ E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} where
  obj G := moduleSupportSpectralSequence R Z F (injectiveResolution G)
  map a := moduleSupportSpectralSequenceCoefficientMap R Z F a _ _
  map_id _ := moduleSupportSpectralSequenceCoefficientMap_id R Z F _
  map_comp a b := moduleSupportSpectralSequenceCoefficientMap_comp R Z F a b _ _ _

/-- Canonical change of injective resolution for the entire spectral sequence. -/
def moduleSupportSpectralSequenceResolutionIso (I J : InjectiveResolution G) :
    moduleSupportSpectralSequence R Z F I ≅ moduleSupportSpectralSequence R Z F J where
  hom := moduleSupportSpectralSequenceCoefficientMap R Z F (𝟙 G) I J
  inv := moduleSupportSpectralSequenceCoefficientMap R Z F (𝟙 G) J I
  hom_inv_id := by rw [← moduleSupportSpectralSequenceCoefficientMap_comp]; simp
  inv_hom_id := by rw [← moduleSupportSpectralSequenceCoefficientMap_comp]; simp

end SGA.SGA2.ExposeVI
