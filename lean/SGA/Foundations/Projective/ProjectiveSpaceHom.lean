/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.ToProj

/-!
# Morphisms to projective space defined by sections of a line bundle

A line bundle `L` on an `S`-scheme `X` together with sections `sᵢ` of `L` (`i ∈ σ`) without common
zero defines an `S`-morphism `X ⟶ ℙ(σ; S)`, the inverse image of `D₊(xᵢ)` being the
non-vanishing locus of `sᵢ` (EGA II 4.2.3, Hartshorne II.7.1, Stacks 01NE).

## Main definitions and results

- `MvPolynomial.IsHomogeneous.eval₂_mul_left`: `P(c x) = cᵈ P(x)` for `P` homogeneous of degree
  `d`.
- `AlgebraicGeometry.Scheme.LineBundle.gradedHomOfSections`: the graded homomorphism
  `ℤ[xᵢ : i ∈ σ] → ⊕ₙ Γ(X, L^{⊗n})` sending `xᵢ` to `sᵢ`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections`: the `S`-morphism `X ⟶ ℙ(σ; S)` defined by
  sections of a line bundle without common zero, with
  `ProjectiveSpace.homOfSections_preimage_basicOpen` and, more generally,
  `ProjectiveSpace.homOfSections_preimage_nonvanishingLocus`.
-/

universe u

open CategoryTheory Limits MvPolynomial Opposite

namespace MvPolynomial

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- A homogeneous polynomial `P` of degree `d` satisfies `P(c x) = cᵈ P(x)`. -/
lemma IsHomogeneous.eval₂_mul_left {P : MvPolynomial σ R} {d : ℕ} (hP : P.IsHomogeneous d)
    (f : R →+* S) (c : S) (x : σ → S) :
    MvPolynomial.eval₂ f (fun i ↦ c * x i) P = c ^ d * MvPolynomial.eval₂ f x P := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp hm)
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [show ∑ i ∈ m.support, m i = d from hdeg]
  ring

end MvPolynomial

namespace AlgebraicGeometry

open ProjectiveSpace

set_option hygiene false in
local notation3 "ℤ'" => ULift.{u} ℤ

namespace Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle) {σ : Type u}

/-- Evaluation of integral polynomials at the local expressions `sᵢ,ₐ ∈ Γ(Uₐ, 𝒪_X)` of sections
`sᵢ` of `L`. -/
noncomputable def evalSections (s : σ → L.sections 1) (a : L.ι) :
    MvPolynomial σ ℤ' →+* Γ(X, L.U a) :=
  eval₂Hom ((algebraMap ℤ _).comp ULift.ringEquiv.toRingHom) fun i ↦ (s i).1 a

set_option backward.isDefEq.respectTransparency false in
/-- The graded homomorphism `ℤ[xᵢ : i ∈ σ] → ⊕ₙ Γ(X, L^{⊗n})` sending `xᵢ` to `sᵢ`. -/
noncomputable def gradedHomOfSections (s : σ → L.sections 1) :
    L.GradedHom (grading σ ℤ') where
  app := L.evalSections s
  app_mem a b d P hP := by
    rw [mem_grading] at hP
    change (X.presheaf.map _).hom (eval₂ _ _ P) = _ * (X.presheaf.map _).hom (eval₂ _ _ P)
    rw [eval₂_comp_left, eval₂_comp_left]
    have hf : ∀ (U V : X.Opens) (i : V ⟶ U),
        (X.presheaf.map i.op).hom.comp ((algebraMap ℤ Γ(X, U)).comp ULift.ringEquiv.toRingHom) =
          (algebraMap ℤ Γ(X, V)).comp ULift.ringEquiv.toRingHom := fun U V i ↦ by
      rw [← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_int _ _
    have hs : (X.presheaf.map (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op).hom ∘
        (fun i ↦ (s i).1 a) = fun i ↦ (L.g a b : Γ(X, L.U a ⊓ L.U b)) *
          (X.presheaf.map (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op).hom ((s i).1 b) := by
      funext i
      simpa using (s i).2 a b
    rw [hs, hf, hf, hP.eval₂_mul_left]
    rfl

lemma evalSections_X (s : σ → L.sections 1) (a : L.ι) (i : σ) :
    L.evalSections s a (MvPolynomial.X i) = (s i).1 a :=
  eval₂Hom_X' _ _ _

lemma gradedHomOfSections_sec_X (s : σ → L.sections 1) (i : σ) :
    (L.gradedHomOfSections s).sec (X_mem_grading i) = s i :=
  Subtype.ext (funext fun a ↦ L.evalSections_X s a i)

end Scheme.LineBundle

namespace ProjectiveSpace

variable {X S : Scheme.{u}} {σ : Type u}

lemma exists_nonvanishingLocus_gradedHomOfSections (L : X.LineBundle) (s : σ → L.sections 1)
    (hs : ∀ x, ∃ i, x ∈ L.nonvanishingLocus (s i)) (x : X) :
    ∃ (d : ℕ) (t : MvPolynomial σ ℤ') (_ : 0 < d) (ht : t ∈ grading σ ℤ' d),
      x ∈ L.nonvanishingLocus ((L.gradedHomOfSections s).sec ht) := by
  obtain ⟨i, hi⟩ := hs x
  exact ⟨1, MvPolynomial.X i, one_pos, X_mem_grading i, by rwa [L.gradedHomOfSections_sec_X]⟩

/-- EGA II 4.2.3, Hartshorne II.7.1, Stacks 01NE: the `S`-morphism `X ⟶ ℙ(σ; S)` defined by a
morphism `f : X ⟶ S` and sections `sᵢ` (`i ∈ σ`) of a line bundle `L` on `X` without common zero;
it is `x ↦ (s_i(x))ᵢ`, and the inverse image of `D₊(xᵢ)` is the non-vanishing locus of `sᵢ`. -/
noncomputable def homOfSections (f : X ⟶ S) (L : X.LineBundle) (s : σ → L.sections 1)
    (hs : ∀ x, ∃ i, x ∈ L.nonvanishingLocus (s i)) : X ⟶ ℙ(σ; S) :=
  pullback.lift f ((L.gradedHomOfSections s).toProj
    (exists_nonvanishingLocus_gradedHomOfSections L s hs)) (terminal.hom_ext _ _)

variable (f : X ⟶ S) (L : X.LineBundle) (s : σ → L.sections 1)
  (hs : ∀ x, ∃ i, x ∈ L.nonvanishingLocus (s i))

@[reassoc (attr := simp)]
lemma homOfSections_over : homOfSections f L s hs ≫ ℙ(σ; S) ↘ S = f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma homOfSections_toProj :
    homOfSections f L s hs ≫ toProj σ S = (L.gradedHomOfSections s).toProj
      (exists_nonvanishingLocus_gradedHomOfSections L s hs) :=
  pullback.lift_snd _ _ _

/-- The inverse image under `homOfSections` of the non-vanishing locus `D₊(p)` of a homogeneous
polynomial `p` of positive degree is the non-vanishing locus of `p(s)`. -/
lemma homOfSections_preimage_toProj_preimage {d : ℕ} {p : MvPolynomial σ ℤ'}
    (hp : p ∈ grading σ ℤ' d) (hd : 0 < d) :
    homOfSections f L s hs ⁻¹ᵁ toProj σ S ⁻¹ᵁ Proj.basicOpen (grading σ ℤ') p =
      L.nonvanishingLocus ((L.gradedHomOfSections s).sec hp) := by
  rw [← Scheme.Hom.comp_preimage, homOfSections_toProj,
    Scheme.LineBundle.GradedHom.toProj_preimage_basicOpen _ _ hp hd]

/-- The inverse image of `D₊(xᵢ)` under `homOfSections` is the non-vanishing locus of `sᵢ`. -/
lemma homOfSections_preimage_basicOpen (i : σ) :
    homOfSections f L s hs ⁻¹ᵁ basicOpen S i = L.nonvanishingLocus (s i) := by
  rw [basicOpen, homOfSections_preimage_toProj_preimage f L s hs (X_mem_grading i) one_pos,
    L.gradedHomOfSections_sec_X]

end ProjectiveSpace

end AlgebraicGeometry
