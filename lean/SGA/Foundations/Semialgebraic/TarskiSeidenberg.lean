/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import SGA.Foundations.Semialgebraic.Basic
import SGA.Foundations.Semialgebraic.ParametricHormander

/-!
# The Tarski–Seidenberg theorem

The projection of a semialgebraic subset of `ℝⁿ⁺¹` to `ℝⁿ` is semialgebraic
(`IsSemialgebraic.exists_real`, for `ℝ^(Option κ) → ℝ^κ`). Consequently the semialgebraic sets are
stable under projections along finitely many coordinates (`IsSemialgebraic.exists_sumElim`), under
universal quantification (`IsSemialgebraic.forall_real`), and images of semialgebraic sets under
polynomial maps between finite-dimensional spaces are semialgebraic
(`IsSemialgebraic.image_polynomialMap`).

The proof is Hörmander's. A semialgebraic set `S` is a union of *sign classes* of a finite set
`F` of polynomials: membership in `S` depends only on the signs of the members of `F`
(`IsSemialgebraic.exists_finset_mem_iff_of_sign_eq`), and conversely such unions are
semialgebraic (`IsSemialgebraic.of_sign_eq`). Writing the members of `F` as polynomials in the
last variable with coefficients in `ℝ[y₁, …, yₙ]`, the sign diagram of their specializations at
`y` depends only on the signs at `y` of finitely many polynomials `T`
(`Polynomial.exists_finset_signEquiv_map`, Hörmander's theorem with parameters); the existence of
`x` with `(y, x) ∈ S` depends only on that sign diagram, so the projection is a union of sign
classes of `T`.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §2.2][BCR]
* [L. Hörmander, *The analysis of linear partial differential operators II*, Appendix A.2]
-/

open Set MvPolynomial

variable {ι κ : Type*}

namespace IsSemialgebraic

/-- The set where a polynomial has a given sign is semialgebraic. -/
protected lemma sign_eq (p : MvPolynomial ι ℝ) (s : SignType) :
    IsSemialgebraic {x : ι → ℝ | SignType.sign (eval x p) = s} := by
  rcases s with _ | _ | _
  · simpa only [SignType.zero_eq_zero, sign_eq_zero_iff] using IsSemialgebraic.zero p
  · simpa only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff] using IsSemialgebraic.neg p
  · simpa only [SignType.pos_eq_one, sign_eq_one_iff] using IsSemialgebraic.pos p

/-- A union of sign classes of finitely many polynomials is semialgebraic: if membership in `S`
only depends on the signs of the members of a finite set `T` of polynomials, then `S` is
semialgebraic. -/
theorem of_sign_eq {S : Set (ι → ℝ)} (T : Finset (MvPolynomial ι ℝ))
    (hS : ∀ x y, (∀ p ∈ T, SignType.sign (eval x p) = SignType.sign (eval y p)) → x ∈ S → y ∈ S) :
    IsSemialgebraic S := by
  classical
  let v : (ι → ℝ) → T → SignType := fun x p ↦ SignType.sign (eval x p.1)
  have hSv : S = ⋃ σ ∈ v '' S, v ⁻¹' {σ} := by
    ext y
    simp only [mem_iUnion, mem_image, mem_preimage, mem_singleton_iff, exists_prop]
    refine ⟨fun hy ↦ ⟨v y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    exact hS x y (fun p hp ↦ (congrFun hxy ⟨p, hp⟩).symm) hx
  rw [hSv]
  refine IsSemialgebraic.biUnion (toFinite _) fun σ _ ↦ ?_
  have : v ⁻¹' {σ} = ⋂ p : T, {x | SignType.sign (eval x p.1) = σ p} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
    exact funext_iff
  rw [this]
  exact IsSemialgebraic.iInter fun p ↦ IsSemialgebraic.sign_eq _ _

/-- A semialgebraic set is a union of sign classes of finitely many polynomials. -/
theorem exists_finset_mem_iff_of_sign_eq {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    ∃ T : Finset (MvPolynomial ι ℝ), ∀ x y,
      (∀ p ∈ T, SignType.sign (eval x p) = SignType.sign (eval y p)) → (x ∈ S ↔ y ∈ S) := by
  classical
  refine IsSemialgebraic.induction (P := fun S ↦ ∃ T : Finset (MvPolynomial ι ℝ), ∀ x y,
    (∀ p ∈ T, SignType.sign (eval x p) = SignType.sign (eval y p)) → (x ∈ S ↔ y ∈ S))
    (fun p ↦ ?_) ⟨∅, fun _ _ _ ↦ Iff.rfl⟩ (fun S T hS hT ↦ ?_) (fun S hS ↦ ?_) hS
  · refine ⟨{p}, fun x y h ↦ ?_⟩
    have := h p (Finset.mem_singleton_self p)
    simp only [mem_ofPred_eq, ← sign_eq_one_iff, this]
  · obtain ⟨F, hF⟩ := hS
    obtain ⟨G, hG⟩ := hT
    refine ⟨F ∪ G, fun x y h ↦ ?_⟩
    rw [mem_union, mem_union, hF x y fun p hp ↦ h p (Finset.mem_union_left _ hp),
      hG x y fun p hp ↦ h p (Finset.mem_union_right _ hp)]
  · obtain ⟨F, hF⟩ := hS
    exact ⟨F, fun x y h ↦ (hF x y h).not⟩

/-- A subset of `ℝ^ι` is semialgebraic if and only if it is a union of sign classes of finitely
many polynomials. -/
theorem iff_exists_finset {S : Set (ι → ℝ)} :
    IsSemialgebraic S ↔ ∃ T : Finset (MvPolynomial ι ℝ), ∀ x y,
      (∀ p ∈ T, SignType.sign (eval x p) = SignType.sign (eval y p)) → (x ∈ S ↔ y ∈ S) :=
  ⟨exists_finset_mem_iff_of_sign_eq, fun ⟨T, hT⟩ ↦ of_sign_eq T fun x y h ↦ (hT x y h).mp⟩

/-- **Tarski–Seidenberg theorem**: the projection `ℝ^(Option κ) → ℝ^κ` (forgetting the coordinate
`none`) of a semialgebraic set is semialgebraic. -/
theorem exists_real {S : Set (Option κ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {y : κ → ℝ | ∃ x : ℝ, (fun o ↦ Option.elim o x y) ∈ S} := by
  classical
  obtain ⟨F, hF⟩ := hS.exists_finset_mem_iff_of_sign_eq
  obtain ⟨T, hT⟩ := Polynomial.exists_finset_signEquiv_map
    (F.val.map (optionEquivLeft ℝ κ))
  refine of_sign_eq T fun y y' hyy' ⟨x, hx⟩ ↦ ?_
  obtain ⟨h, hh⟩ := hT (eval y) (eval y') hyy'
  refine ⟨h x, (hF _ _ fun p hp ↦ ?_).mp hx⟩
  rw [optionEquivLeft_elim_eval, optionEquivLeft_elim_eval]
  exact (hh ⟨optionEquivLeft ℝ κ p, Multiset.mem_map_of_mem _ hp⟩ x).symm

/-- The set of `y` such that `(y, x) ∈ S` for all `x ∈ ℝ` is semialgebraic if `S ⊆ ℝ^(Option κ)`
is. -/
theorem forall_real {S : Set (Option κ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic {y : κ → ℝ | ∀ x : ℝ, (fun o ↦ Option.elim o x y) ∈ S} := by
  have := hS.compl.exists_real
  rw [← compl_iff]
  convert this using 1
  ext y
  simp

universe u v

/-- **Tarski–Seidenberg theorem**, projection along finitely many coordinates: if
`S ⊆ ℝ^(κ ⊕ ι)` is semialgebraic and `ι` is finite, the set of `y ∈ ℝ^κ` such that `(y, z) ∈ S`
for some `z ∈ ℝ^ι` is semialgebraic. -/
theorem exists_sumElim {ι : Type u} [Finite ι] {κ : Type v} {S : Set (κ ⊕ ι → ℝ)}
    (hS : IsSemialgebraic S) : IsSemialgebraic {y : κ → ℝ | ∃ z : ι → ℝ, Sum.elim y z ∈ S} := by
  refine Finite.induction_empty_option (P := fun ι ↦ ∀ (κ : Type v) (S : Set (κ ⊕ ι → ℝ)),
    IsSemialgebraic S → IsSemialgebraic {y : κ → ℝ | ∃ z : ι → ℝ, Sum.elim y z ∈ S})
    (fun {α β} e hα κ S hS ↦ ?_) (fun κ S hS ↦ ?_) (fun {α} _ hα κ S hS ↦ ?_) ι κ S hS
  · -- invariance under equivalences
    convert hα κ _ (hS.preimage_comp (Sum.map id e.symm)) using 1
    ext y
    simp only [mem_ofPred_eq, mem_preimage]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e, ?_⟩
      convert hz using 1
      ext (k | b) <;> simp
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e.symm, ?_⟩
      convert hz using 1
      ext (k | b) <;> simp
  · -- no coordinates
    convert hS.preimage_comp (Sum.elim id PEmpty.elim : κ ⊕ PEmpty → κ) using 1
    ext y
    simp only [mem_ofPred_eq, mem_preimage]
    constructor
    · rintro ⟨z, hz⟩
      convert hz using 1
      ext (k | b)
      · rfl
      · exact b.elim
    · intro h
      refine ⟨fun b ↦ b.elim, ?_⟩
      convert h using 1
      ext (k | b)
      · rfl
      · exact b.elim
  · -- one more coordinate
    let c : κ ⊕ Option α → Option (κ ⊕ α) := Sum.elim (fun k ↦ some (Sum.inl k))
      (fun o ↦ o.map Sum.inr)
    have hS₁ := (hS.preimage_comp c).exists_real
    convert hα κ _ hS₁ using 1
    ext y
    simp only [mem_ofPred_eq, mem_preimage]
    have key (x : ℝ) (z : α → ℝ) :
        (fun o ↦ Option.elim o x (Sum.elim y z)) ∘ c = Sum.elim y fun o ↦ Option.elim o x z := by
      ext (k | _ | a) <;> rfl
    simp only [key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ some, z none, ?_⟩
      convert hz using 2
      ext (_ | a) <;> rfl
    · rintro ⟨z, x, hz⟩
      exact ⟨_, hz⟩

/-- **Tarski–Seidenberg theorem**, images: the image of a semialgebraic subset of `ℝ^ι` under a
polynomial map `ℝ^ι → ℝ^κ`, `ι` and `κ` finite, is semialgebraic. -/
theorem image_polynomialMap {ι : Type u} [Finite ι] {κ : Type v} [Finite κ]
    (F : κ → MvPolynomial ι ℝ) {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic ((fun x : ι → ℝ ↦ fun k ↦ eval x (F k)) '' S) := by
  let G : Set (κ ⊕ ι → ℝ) := (fun w ↦ w ∘ Sum.inr) ⁻¹' S ∩
    ⋂ k, {w | eval w (X (Sum.inl k)) = eval w (rename Sum.inr (F k))}
  have hG : IsSemialgebraic G := (hS.preimage_comp Sum.inr).inter
    (IsSemialgebraic.iInter fun k ↦ IsSemialgebraic.eq _ _)
  convert hG.exists_sumElim using 1
  ext y
  simp only [G, mem_image, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, eval_X,
    eval_rename]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, fun k ↦ rfl⟩
  · rintro ⟨x, hx, hk⟩
    exact ⟨x, hx, funext fun k ↦ (hk k).symm⟩

end IsSemialgebraic
