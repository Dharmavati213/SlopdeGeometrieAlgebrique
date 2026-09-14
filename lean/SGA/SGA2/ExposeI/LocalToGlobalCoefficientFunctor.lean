/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageExt

/-!
# Resolution-independent coefficient functoriality

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

variable {X : TopCat.{u}} (Z : Closeds X)

attribute [local instance] supportedE2_hasDerivedCategory

/-- First-quadrant support reduces uniqueness to the nonnegative E₂ terms. -/
theorem supportedTruncationSpectralSequence_hom_ext
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    {α β : supportedTruncationSpectralSequence Z I ⟶ supportedTruncationSpectralSequence Z J}
    (h : ∀ p q : ℕ, (α.hom 2).f ((p : ℤ), (q : ℤ)) =
      (β.hom 2).f ((p : ℤ), (q : ℤ))) : α = β := by
  apply spectralSequence_hom_ext_firstPage_f
  rintro ⟨p, q⟩
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact h p q
    · exact (supportedTruncationSpectralSequence_isZero_of_second_neg Z I 2 (by lia)
        p q (by lia)).eq_of_src _ _
  · exact (supportedTruncationSpectralSequence_isZero_of_first_neg Z I 2 (by lia)
      p q (by lia)).eq_of_src _ _

/-- Two compatible resolution lifts of the same coefficient map give the
same actual morphism on every page, including all next-page identifications. -/
theorem supportedTruncationSpectralSequenceMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) :
    supportedTruncationSpectralSequenceMap Z φ =
      supportedTruncationSpectralSequenceMap Z ψ := by
  apply supportedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (supportedTruncationSpectralSequenceE2Equiv Z J p q).injective
  rw [supportedTruncationSpectralSequenceE2Equiv_naturality Z f I J φ hφ,
    supportedTruncationSpectralSequenceE2Equiv_naturality Z f I J ψ hψ]

/-- The coefficient map between any two chosen injective resolutions. -/
def supportedTruncationSpectralSequenceCoefficientMap
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    supportedTruncationSpectralSequence Z I ⟶ supportedTruncationSpectralSequence Z J :=
  supportedTruncationSpectralSequenceMap Z (InjectiveResolution.desc f J I)

lemma supportedTruncationSpectralSequenceCoefficientMap_eq
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    supportedTruncationSpectralSequenceCoefficientMap Z f I J =
      supportedTruncationSpectralSequenceMap Z (InjectiveResolution.desc f J I) := rfl

/-- Any compatible lift computes the canonical coefficient map. -/
theorem supportedTruncationSpectralSequenceMap_eq_coefficientMap
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    supportedTruncationSpectralSequenceMap Z φ =
      supportedTruncationSpectralSequenceCoefficientMap Z f I J :=
  (supportedTruncationSpectralSequenceMap_eq_of_lifts Z f I J φ
    (InjectiveResolution.desc f J I) hφ (InjectiveResolution.desc_commutes_zero f J I)).trans
      (supportedTruncationSpectralSequenceCoefficientMap_eq Z f I J).symm

theorem supportedTruncationSpectralSequenceCoefficientMap_E2
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (p q : ℕ)
    (x : ((supportedTruncationSpectralSequence Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    supportedTruncationSpectralSequenceE2Equiv Z J p q
        (((supportedTruncationSpectralSequenceCoefficientMap Z f I J).hom 2).f
          ((p : ℤ), (q : ℤ)) x) =
      CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaZ Z q).map f) p
        (supportedTruncationSpectralSequenceE2Equiv Z I p q x) := by
  calc
    _ = supportedTruncationSpectralSequenceE2Equiv Z J p q
        (((supportedTruncationSpectralSequenceMap Z
          (InjectiveResolution.desc f J I)).hom 2).f ((p : ℤ), (q : ℤ)) x) :=
      congrArg (fun α : supportedTruncationSpectralSequence Z I ⟶
          supportedTruncationSpectralSequence Z J =>
        supportedTruncationSpectralSequenceE2Equiv Z J p q
          ((α.hom 2).f ((p : ℤ), (q : ℤ)) x))
        (supportedTruncationSpectralSequenceCoefficientMap_eq Z f I J)
    _ = _ := supportedTruncationSpectralSequenceE2Equiv_naturality Z f I J
      (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) p q x

@[simp]
theorem supportedTruncationSpectralSequenceCoefficientMap_id
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) I I = 𝟙 _ := by
  apply supportedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (supportedTruncationSpectralSequenceE2Equiv Z I p q).injective
  rw [supportedTruncationSpectralSequenceCoefficientMap_E2]
  simp only [SpectralSequence.id_hom, HomologicalComplex.id_f,
    ConcreteCategory.id_apply]
  erw [CategoryTheory.Functor.map_id]
  exact CategoryTheory.Sheaf.H.map_id_apply
    (F := (derivedUnderlineGammaZ Z q).obj F) _

@[reassoc]
theorem supportedTruncationSpectralSequenceCoefficientMap_comp
    {F G K : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (g : G ⟶ K)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (L : InjectiveResolution K) :
    supportedTruncationSpectralSequenceCoefficientMap Z (f ≫ g) I L =
      supportedTruncationSpectralSequenceCoefficientMap Z f I J ≫
        supportedTruncationSpectralSequenceCoefficientMap Z g J L := by
  apply supportedTruncationSpectralSequence_hom_ext
  intro p q
  ext x
  apply (supportedTruncationSpectralSequenceE2Equiv Z L p q).injective
  simp only [SpectralSequence.comp_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
  rw [supportedTruncationSpectralSequenceCoefficientMap_E2,
    supportedTruncationSpectralSequenceCoefficientMap_E2,
    supportedTruncationSpectralSequenceCoefficientMap_E2]
  rw [Functor.map_comp, CategoryTheory.Sheaf.H.map_comp_apply]

/-- The original closed-support local-to-global spectral sequence is
functorial in its coefficient sheaf. -/
def supportedTruncationSpectralSequenceFunctor :
    Sheaf AddCommGrpCat.{u} X ⥤ E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} where
  obj F := supportedTruncationSpectralSequence Z (injectiveResolution F)
  map f := supportedTruncationSpectralSequenceCoefficientMap Z f _ _
  map_id _F := supportedTruncationSpectralSequenceCoefficientMap_id Z _
  map_comp f g := supportedTruncationSpectralSequenceCoefficientMap_comp Z f g _ _ _

/-- Any two resolutions give canonically isomorphic actual spectral
sequences; both directions are the coefficient maps of the identity. -/
def supportedTruncationSpectralSequenceResolutionIso
    {F : Sheaf AddCommGrpCat.{u} X} (I J : InjectiveResolution F) :
    supportedTruncationSpectralSequence Z I ≅ supportedTruncationSpectralSequence Z J where
  hom := supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) I J
  inv := supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) J I
  hom_inv_id := by rw [← supportedTruncationSpectralSequenceCoefficientMap_comp]; simp
  inv_hom_id := by rw [← supportedTruncationSpectralSequenceCoefficientMap_comp]; simp

/-- The canonical change-of-resolution isomorphisms commute with every
coefficient map. -/
@[reassoc]
theorem supportedTruncationSpectralSequenceResolutionIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I I' : InjectiveResolution F) (J J' : InjectiveResolution G) :
    (supportedTruncationSpectralSequenceResolutionIso Z I I').hom ≫
        supportedTruncationSpectralSequenceCoefficientMap Z f I' J' =
      supportedTruncationSpectralSequenceCoefficientMap Z f I J ≫
        (supportedTruncationSpectralSequenceResolutionIso Z J J').hom := by
  change supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) I I' ≫ _ =
    _ ≫ supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 G) J J'
  rw [← supportedTruncationSpectralSequenceCoefficientMap_comp,
    ← supportedTruncationSpectralSequenceCoefficientMap_comp]
  simp

/-- Canonical change of resolution satisfies the cocycle identity. -/
@[simp]
theorem supportedTruncationSpectralSequenceResolutionIso_trans
    {F : Sheaf AddCommGrpCat.{u} X} (I J L : InjectiveResolution F) :
    supportedTruncationSpectralSequenceResolutionIso Z I J ≪≫
        supportedTruncationSpectralSequenceResolutionIso Z J L =
      supportedTruncationSpectralSequenceResolutionIso Z I L := by
  apply Iso.ext
  change supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) I J ≫
    supportedTruncationSpectralSequenceCoefficientMap Z (𝟙 F) J L = _
  rw [← supportedTruncationSpectralSequenceCoefficientMap_comp]
  simp only [Category.id_comp]
  rfl

end SGA.SGA2.ExposeI
