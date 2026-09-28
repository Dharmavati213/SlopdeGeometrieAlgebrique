/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# SGA 1, Exposé III, §3: local infinitesimal extension of morphisms

Theorem III.3.1: a morphism `X → Y` locally of finite type is smooth if and only if morphisms
`Y'₀ → X` extend (locally on `Y'`) along closed immersions `Y'₀ ⊆ Y'` with the same underlying
space, i.e. along nil ideals. Corollary III.3.2 characterises étale morphisms by existence and
uniqueness of the extension, and Corollary III.3.3 gives sections of a smooth scheme over a
complete local ring through rational points of the closed fibre.

Here in the affine case (`X = Spec A`, `Y' = Spec C`, `Y'₀ = Spec (C ⧸ J)` with `J` nil):

* III.3.1 (i) ⇒ (ii): `Smooth.exists_lift_of_le_nilradical`. SGA uses the local structure of
  smooth morphisms; we use a finite presentation, which reduces a nil ideal to a nilpotent one;
* III.3.2 (i) ⇒ (ii): `Etale.existsUnique_lift_of_le_nilradical`, and the infinitesimal
  characterisation of formally étale algebras;
* III.3.3: `exists_section_of_isAdicComplete`.

The converse III.3.1 (iii) ⇒ (i) is, at the level of local rings,
`isSmoothAt_iff_adicFormallySmooth` in `SmoothLocal.lean`.
-/

universe u v w

namespace SGA.SGA1.ExposeIII

open IsLocalRing

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  {C : Type w} [CommRing C] [Algebra R C]

/-- III.3.1, (i) ⇒ (ii) (affine case): maps from a smooth `R`-algebra into `C ⧸ J`, with `J` a
nil ideal (so that `Spec (C ⧸ J) → Spec C` is a homeomorphism), lift to `C`. -/
theorem Smooth.exists_lift_of_le_nilradical [Algebra.Smooth R A] (J : Ideal C)
    (hJ : J ≤ nilradical C) (g₀ : A →ₐ[R] C ⧸ J) :
    ∃ g : A →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = g₀ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (g₀ (f (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) R →ₐ[R] C := MvPolynomial.aeval c
  have hφ : (Ideal.Quotient.mkₐ R J).comp φ = g₀.comp f :=
    MvPolynomial.algHom_ext fun i ↦ by simp [φ, hc]
  set J' := (RingHom.ker f.toRingHom).map φ
  have hJ'J : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    have := congr($hφ a)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this, show f a = 0 from ha, map_zero]
  have hJ' : IsNilpotent J' :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (hker.map _)).mpr (hJ'J.trans hJ)
  have hlift : ∀ a ∈ RingHom.ker f.toRingHom, (Ideal.Quotient.mkₐ R J').comp φ a = 0 :=
    fun a ha ↦ by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha
  let g₁ : A →ₐ[R] C ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) ((Ideal.Quotient.mkₐ R J').comp φ)
      hlift).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J' hJ' g₁
  refine ⟨g, AlgHom.ext fun x ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hf x
  have h1 := congr($hg (f p))
  have h2 : g₁ (f p) = Ideal.Quotient.mk J' (φ p) := by
    change (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) ((Ideal.Quotient.mkₐ R J').comp φ)
      hlift) ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1 ⊢
  rw [h2, Ideal.Quotient.eq] at h1
  have h3 : g₀ (f p) = Ideal.Quotient.mk J (φ p) := (congr($hφ p)).symm
  rw [h3, Ideal.Quotient.eq]
  exact hJ'J h1

/-- III.3.1, (i) ⇒ (ii) (affine case), in terms of a surjection `C → D` with nil kernel. -/
theorem Smooth.exists_lift_of_surjective [Algebra.Smooth R A] {D : Type*} [CommRing D]
    [Algebra R D] (ρ : C →ₐ[R] D) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ ≤ nilradical C) (g₀ : A →ₐ[R] D) :
    ∃ g : A →ₐ[R] C, ρ.comp g = g₀ := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hρ
  obtain ⟨g, hg⟩ := exists_lift_of_le_nilradical (RingHom.ker ρ) hker (e.symm.toAlgHom.comp g₀)
  refine ⟨g, AlgHom.ext fun x ↦ ?_⟩
  have := congr(e ($hg x))
  simpa [e, Ideal.quotientKerAlgEquivOfSurjective_mk] using this

/-- III.3.2, (i) ⇒ (ii), uniqueness (affine case): two maps from an unramified algebra of finite
type which agree modulo a nil ideal are equal. -/
theorem FormallyUnramified.ext_of_le_nilradical [Algebra.FormallyUnramified R A]
    [Algebra.FiniteType R A] (J : Ideal C) (hJ : J ≤ nilradical C) {g₁ g₂ : A →ₐ[R] C}
    (h : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂) : g₁ = g₂ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  set J' := Ideal.span ((fun x ↦ g₁ x - g₂ x) '' (s : Set A))
  have hJ'J : J' ≤ J := Ideal.span_le.mpr <| by
    rintro _ ⟨x, -, rfl⟩
    rw [SetLike.mem_coe, ← Ideal.Quotient.eq]
    exact congr($h x)
  have hJ' : IsNilpotent J' :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (s.finite_toSet.image _))).mpr
      (hJ'J.trans hJ)
  refine Algebra.FormallyUnramified.ext J' hJ' fun x ↦ ?_
  have : x ∈ AlgHom.equalizer ((Ideal.Quotient.mkₐ R J').comp g₁)
      ((Ideal.Quotient.mkₐ R J').comp g₂) := by
    refine (Algebra.adjoin_le fun y hy ↦ ?_) (hs ▸ Algebra.mem_top : x ∈ Algebra.adjoin R ↑s)
    change Ideal.Quotient.mk J' (g₁ y) = Ideal.Quotient.mk J' (g₂ y)
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  exact this

/-- III.3.2, (i) ⇒ (ii) (affine case): maps from an étale algebra lift uniquely along nil
ideals. -/
theorem Etale.existsUnique_lift_of_le_nilradical [Algebra.Etale R A] (J : Ideal C)
    (hJ : J ≤ nilradical C) (g₀ : A →ₐ[R] C ⧸ J) :
    ∃! g : A →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = g₀ := by
  obtain ⟨g, hg⟩ := Smooth.exists_lift_of_le_nilradical J hJ g₀
  exact ⟨g, hg, fun g' hg' ↦ FormallyUnramified.ext_of_le_nilradical J hJ (hg'.trans hg.symm)⟩

/-- III.3.2, (i) ⇔ (iii), infinitesimal form: `A` is formally étale over `R` if and only if maps
into `C ⧸ J`, `J² = 0`, lift uniquely to `C` (this is mathlib's definition). -/
theorem formallyEtale_iff_comp_bijective {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] : Algebra.FormallyEtale R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
        Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  Algebra.FormallyEtale.iff_comp_bijective

/-- III.3.3 (affine case): if `B` is formally smooth over a complete local ring `A`, every
`A`-algebra map `B → k` to the residue field (a rational point of the closed fibre of
`Spec B`) lifts to a section `B → A`. -/
theorem exists_section_of_isAdicComplete {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing B] [Algebra A B] [Algebra.FormallySmooth A B]
    (x : B →ₐ[A] ResidueField A) :
    ∃ s : B →ₐ[A] A, (IsScalarTower.toAlgHom A A (ResidueField A)).comp s = x :=
  Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete x

end SGA.SGA1.ExposeIII
