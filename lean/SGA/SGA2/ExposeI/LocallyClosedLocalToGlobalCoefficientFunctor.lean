/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageExt

/-!
# Resolution-independent coefficient functoriality for ambient locally closed support

The actual supported spectral-sequence maps are determined by ordinary
cohomology of the original derived supported-sheaf map on E₂. Thus they do
not depend on the lift of a coefficient morphism to resolutions. Choosing
one resolution per sheaf gives a genuine functor to the original category
of spectral sequences, and changing resolutions gives canonical isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}} (W : LocallyClosedIn X)

attribute [local instance] supportedE2_hasDerivedCategory

/-- First-quadrant support reduces uniqueness to the nonnegative E₂ terms. -/
theorem locallyClosedTruncationSpectralSequence_hom_ext
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    {α β : locallyClosedTruncationSpectralSequence W I ⟶
      locallyClosedTruncationSpectralSequence W J}
    (h : ∀ p q : ℕ, (α.hom 2).f ((p : ℤ), (q : ℤ)) =
      (β.hom 2).f ((p : ℤ), (q : ℤ))) : α = β := by
  apply spectralSequence_hom_ext_firstPage_f
  rintro ⟨p, q⟩
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact h p q
    · exact (locallyClosedTruncationSpectralSequence_isZero_of_second_neg W I 2 (by lia)
        p q (by lia)).eq_of_src _ _
  · exact (locallyClosedTruncationSpectralSequence_isZero_of_first_neg W I 2 (by lia)
      p q (by lia)).eq_of_src _ _

/-- Two compatible resolution lifts of the same coefficient map give the
same actual morphism on every page, including all next-page identifications. -/
theorem locallyClosedTruncationSpectralSequenceMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) :
    locallyClosedTruncationSpectralSequenceMap W φ =
      locallyClosedTruncationSpectralSequenceMap W ψ := by
  apply locallyClosedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (locallyClosedTruncationSpectralSequenceE2Equiv W J p q).injective
  rw [locallyClosedTruncationSpectralSequenceE2Equiv_naturality W f I J φ hφ,
    locallyClosedTruncationSpectralSequenceE2Equiv_naturality W f I J ψ hψ]

/-- The coefficient map between any two chosen injective resolutions. -/
def locallyClosedTruncationSpectralSequenceCoefficientMap
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    locallyClosedTruncationSpectralSequence W I ⟶ locallyClosedTruncationSpectralSequence W J :=
  locallyClosedTruncationSpectralSequenceMap W (InjectiveResolution.desc f J I)

lemma locallyClosedTruncationSpectralSequenceCoefficientMap_eq
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    locallyClosedTruncationSpectralSequenceCoefficientMap W f I J =
      locallyClosedTruncationSpectralSequenceMap W (InjectiveResolution.desc f J I) := rfl

/-- Any compatible lift computes the canonical coefficient map. -/
theorem locallyClosedTruncationSpectralSequenceMap_eq_coefficientMap
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    locallyClosedTruncationSpectralSequenceMap W φ =
      locallyClosedTruncationSpectralSequenceCoefficientMap W f I J :=
  (locallyClosedTruncationSpectralSequenceMap_eq_of_lifts W f I J φ
    (InjectiveResolution.desc f J I) hφ (InjectiveResolution.desc_commutes_zero f J I)).trans
      (locallyClosedTruncationSpectralSequenceCoefficientMap_eq W f I J).symm

theorem locallyClosedTruncationSpectralSequenceCoefficientMap_E2
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (p q : ℕ)
    (x : ((locallyClosedTruncationSpectralSequence W I).page 2).X ((p : ℤ), (q : ℤ))) :
    locallyClosedTruncationSpectralSequenceE2Equiv W J p q
        (((locallyClosedTruncationSpectralSequenceCoefficientMap W f I J).hom 2).f
          ((p : ℤ), (q : ℤ)) x) =
      CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaLocallyClosed W q).map f) p
        (locallyClosedTruncationSpectralSequenceE2Equiv W I p q x) := by
  calc
    _ = locallyClosedTruncationSpectralSequenceE2Equiv W J p q
        (((locallyClosedTruncationSpectralSequenceMap W
          (InjectiveResolution.desc f J I)).hom 2).f ((p : ℤ), (q : ℤ)) x) :=
      congrArg (fun α : locallyClosedTruncationSpectralSequence W I ⟶
          locallyClosedTruncationSpectralSequence W J =>
        locallyClosedTruncationSpectralSequenceE2Equiv W J p q
          ((α.hom 2).f ((p : ℤ), (q : ℤ)) x))
        (locallyClosedTruncationSpectralSequenceCoefficientMap_eq W f I J)
    _ = _ := locallyClosedTruncationSpectralSequenceE2Equiv_naturality W f I J
      (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) p q x

@[simp]
theorem locallyClosedTruncationSpectralSequenceCoefficientMap_id
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) I I = 𝟙 _ := by
  apply locallyClosedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (locallyClosedTruncationSpectralSequenceE2Equiv W I p q).injective
  rw [locallyClosedTruncationSpectralSequenceCoefficientMap_E2]
  simp only [SpectralSequence.id_hom, HomologicalComplex.id_f,
    ConcreteCategory.id_apply]
  erw [CategoryTheory.Functor.map_id]
  exact CategoryTheory.Sheaf.H.map_id_apply
    (F := (derivedUnderlineGammaLocallyClosed W q).obj F) _

@[reassoc]
theorem locallyClosedTruncationSpectralSequenceCoefficientMap_comp
    {F G K : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (g : G ⟶ K)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (L : InjectiveResolution K) :
    locallyClosedTruncationSpectralSequenceCoefficientMap W (f ≫ g) I L =
      locallyClosedTruncationSpectralSequenceCoefficientMap W f I J ≫
        locallyClosedTruncationSpectralSequenceCoefficientMap W g J L := by
  apply locallyClosedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (locallyClosedTruncationSpectralSequenceE2Equiv W L p q).injective
  simp only [SpectralSequence.comp_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  rw [locallyClosedTruncationSpectralSequenceCoefficientMap_E2,
    locallyClosedTruncationSpectralSequenceCoefficientMap_E2,
    locallyClosedTruncationSpectralSequenceCoefficientMap_E2]
  rw [Functor.map_comp, CategoryTheory.Sheaf.H.map_comp_apply]

/-- The original locally closed ambient local-to-global spectral sequence is
functorial in its coefficient sheaf. -/
def locallyClosedTruncationSpectralSequenceFunctor :
    Sheaf AddCommGrpCat.{u} X ⥤ E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} where
  obj F := locallyClosedTruncationSpectralSequence W (injectiveResolution F)
  map f := locallyClosedTruncationSpectralSequenceCoefficientMap W f _ _
  map_id _F := locallyClosedTruncationSpectralSequenceCoefficientMap_id W _
  map_comp f g := locallyClosedTruncationSpectralSequenceCoefficientMap_comp W f g _ _ _

/-- Any two resolutions give canonically isomorphic actual spectral
sequences; both directions are the coefficient maps of the identity. -/
def locallyClosedTruncationSpectralSequenceResolutionIso
    {F : Sheaf AddCommGrpCat.{u} X} (I J : InjectiveResolution F) :
    locallyClosedTruncationSpectralSequence W I ≅ locallyClosedTruncationSpectralSequence W J where
  hom := locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) I J
  inv := locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) J I
  hom_inv_id := by rw [← locallyClosedTruncationSpectralSequenceCoefficientMap_comp]; simp
  inv_hom_id := by rw [← locallyClosedTruncationSpectralSequenceCoefficientMap_comp]; simp

/-- The canonical change-of-resolution isomorphisms commute with every
coefficient map. -/
@[reassoc]
theorem locallyClosedTruncationSpectralSequenceResolutionIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I I' : InjectiveResolution F) (J J' : InjectiveResolution G) :
    (locallyClosedTruncationSpectralSequenceResolutionIso W I I').hom ≫
        locallyClosedTruncationSpectralSequenceCoefficientMap W f I' J' =
      locallyClosedTruncationSpectralSequenceCoefficientMap W f I J ≫
        (locallyClosedTruncationSpectralSequenceResolutionIso W J J').hom := by
  change locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) I I' ≫ _ =
    _ ≫ locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 G) J J'
  rw [← locallyClosedTruncationSpectralSequenceCoefficientMap_comp,
    ← locallyClosedTruncationSpectralSequenceCoefficientMap_comp]
  simp

/-- Canonical change of resolution satisfies the cocycle identity. -/
@[simp]
theorem locallyClosedTruncationSpectralSequenceResolutionIso_trans
    {F : Sheaf AddCommGrpCat.{u} X} (I J L : InjectiveResolution F) :
    locallyClosedTruncationSpectralSequenceResolutionIso W I J ≪≫
        locallyClosedTruncationSpectralSequenceResolutionIso W J L =
      locallyClosedTruncationSpectralSequenceResolutionIso W I L := by
  apply Iso.ext
  change locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) I J ≫
    locallyClosedTruncationSpectralSequenceCoefficientMap W (𝟙 F) J L = _
  rw [← locallyClosedTruncationSpectralSequenceCoefficientMap_comp]
  simp only [Category.id_comp]
  rfl

end SGA.SGA2.ExposeI
