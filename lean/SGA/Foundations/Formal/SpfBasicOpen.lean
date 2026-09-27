/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Formal.OpenImmersion
import SGA.Foundations.Formal.Spf

/-!
# Basic open subsets of formal spectra

For `f ∈ A`, the formal spectrum `Spf (A_f)` (for the ideal `I A_f`) is an open formal subscheme of
`Spf A` (EGA I, §10.1): the morphism `Spf A_f ⟶ Spf A` induced by `A → A_f` is an open immersion
(`Spf.isOpenImmersion_map_localizationAway`). Indeed `A_f ⧸ Iⁿ⁺¹ A_f` is the localization of
`A ⧸ Iⁿ⁺¹` at `f` (`Spf.isLocalization_away_quotient`), so the components
`Spec (A_f ⧸ Iⁿ⁺¹ A_f) ⟶ Spec (A ⧸ Iⁿ⁺¹)` are open immersions.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Spf

variable {A : Type u} [CommRing A] (I : Ideal A) (f : A)

local notation "A_f" => Localization.Away f

lemma pow_le_comap_map_pow (n : ℕ) :
    I ^ n ≤ ((I.map (algebraMap A A_f)) ^ n).comap (algebraMap A A_f) := by
  rw [← Ideal.map_pow]
  exact Ideal.le_comap_map

/-- The map `A ⧸ Iⁿ⁺¹ → A_f ⧸ Iⁿ⁺¹ A_f`. -/
noncomputable def quotientMapAway (n : ℕ) :
    A ⧸ I ^ (n + 1) →+* A_f ⧸ (I.map (algebraMap A A_f)) ^ (n + 1) :=
  Ideal.quotientMap _ (algebraMap A A_f) (pow_le_comap_map_pow I f (n + 1))

@[simp]
lemma quotientMapAway_mk (n : ℕ) (a : A) :
    quotientMapAway I f n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A A_f a) :=
  rfl

/-- `A_f ⧸ Iⁿ⁺¹ A_f` is the localization of `A ⧸ Iⁿ⁺¹` away from `f`. -/
lemma isLocalization_away_quotient (n : ℕ) :
    letI := (quotientMapAway I f n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f)
      (A_f ⧸ (I.map (algebraMap A A_f)) ^ (n + 1)) := by
  let _ := (quotientMapAway I f n).toAlgebra
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hy
    rw [map_pow]
    refine IsUnit.pow _ ?_
    change IsUnit (quotientMapAway I f n (Ideal.Quotient.mk _ f))
    rw [quotientMapAway_mk]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj f w
    refine ⟨⟨Ideal.Quotient.mk _ a, ⟨Ideal.Quotient.mk _ f ^ k, k, rfl⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ w * quotientMapAway I f n (Ideal.Quotient.mk _ f ^ k) =
      quotientMapAway I f n (Ideal.Quotient.mk _ a)
    rw [← map_pow, quotientMapAway_mk, quotientMapAway_mk, ← map_mul, map_pow, ha]
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change quotientMapAway I f n (Ideal.Quotient.mk _ a) =
      quotientMapAway I f n (Ideal.Quotient.mk _ b) at h
    rw [quotientMapAway_mk, quotientMapAway_mk, Ideal.Quotient.eq, ← map_sub, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)] at h
    obtain ⟨⟨⟨c, hc⟩, ⟨_, k, rfl⟩⟩, hck⟩ := h
    simp only at hck
    rw [← map_mul, ← sub_eq_zero, ← map_sub, IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
      at hck
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hck
    refine ⟨⟨Ideal.Quotient.mk _ f ^ (m + k), m + k, rfl⟩, ?_⟩
    simp only
    rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have : f ^ (m + k) * (a - b) = f ^ m * c := by
      rw [pow_add]
      linear_combination hm
    rw [this]
    exact Ideal.mul_mem_left _ _ hc

instance isOpenImmersion_SpecMap_quotientMapAway (n : ℕ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientMapAway I f n))) := by
  let _ := (quotientMapAway I f n).toAlgebra
  have := isLocalization_away_quotient I f n
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk (I ^ (n + 1)) f)

/-- The open immersions `Spec (A_f ⧸ Iⁿ⁺¹ A_f) ⟶ Spec (A ⧸ Iⁿ⁺¹)`, as a morphism of thickening
sequences. -/
noncomputable def diagramMapAway : diagram A_f (I.map (algebraMap A A_f)) ⟶ diagram A I where
  app n := Spec.map (CommRingCat.ofHom (quotientMapAway I f n))
  naturality {m n} g := by
    dsimp only [diagram]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    rfl

/-- The basic open subset `Spf A_f ⟶ Spf A` of a formal spectrum (EGA I, §10.1). -/
noncomputable def basicOpenMap :
    Spf A_f (I.map (algebraMap A A_f)) ⟶ Spf A I :=
  Scheme.formalColimit.map (diagramMapAway I f)

instance : LocallyRingedSpace.IsOpenImmersion (basicOpenMap I f) := by
  have (n : ℕ) : IsOpenImmersion ((diagramMapAway I f).app n) :=
    isOpenImmersion_SpecMap_quotientMapAway I f n
  exact Scheme.formalColimit.isOpenImmersion_map _

/-- The basic open immersion is the morphism induced by `A → A_f`. -/
lemma basicOpenMap_eq :
    basicOpenMap I f = map (algebraMap A A_f) ⟨1, by rw [pow_one]; exact Ideal.le_comap_map⟩ := by
  refine hom_ext fun n ↦ ?_
  rw [ι_map]
  change Scheme.formalColimit.ι _ n ≫ Scheme.formalColimit.map _ = _
  rw [Scheme.formalColimit.ι_map]
  have h : I ^ (n + 1) ≤ RingHom.ker
      ((Ideal.Quotient.mk ((I.map (algebraMap A A_f)) ^ (n + 1))).comp (algebraMap A A_f)) :=
    fun a ha ↦ by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact pow_le_comap_map_pow I f (n + 1) ha
  exact fromSpec_eq _ n _ h _

end AlgebraicGeometry.Spf
