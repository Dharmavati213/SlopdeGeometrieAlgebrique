/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.TarskiSeidenberg

/-!
# First-order definitions of semialgebraic sets

The Tarski–Seidenberg theorem in the form used for definitions by first-order formulas: a set
`{x | φ x}` is semialgebraic as soon as `φ` is a first-order formula built from polynomial sign
conditions with `∧`, `∨`, `¬`, `→`, `↔`, `∃ t : ℝ`, `∀ t : ℝ` (and `∃`, `∀` over `ℝ^κ`, `κ` finite).
The combinators `IsSemialgebraic.ofPred_and`, `ofPred_or`, `ofPred_not`, `ofPred_imp`, `ofPred_iff`,
`ofPred_exists`, `ofPred_forall`, `ofPred_exists_pi`, `ofPred_forall_pi` reduce such a goal to the
subformulas, a quantified variable becoming the new coordinate `none` (or `Sum.inr k`) of
`ℝ^(Option ι)` (or `ℝ^(ι ⊕ κ)`); the atoms are `IsSemialgebraic.ofPred_lt`, `ofPred_le`,
`ofPred_eq`, `ofPred_ne`, whose sides are *polynomial functions* `IsPolynomialFun f` (proved by
`fun_prop`). For instance
```
example : IsSemialgebraic {x : Unit → ℝ | ∃ t, 0 < t ∧ ∀ s, s ^ 2 ≤ x () * t} :=
  ofPred_exists (ofPred_and (ofPred_lt (by fun_prop) (by fun_prop))
    (ofPred_forall (ofPred_le (by fun_prop) (by fun_prop))))
```
Unification finds the subformulas, so only the atoms need to be spelled out.

We also record the variants quantifying a coordinate `n` of `ℝ^ι` *in place*
(`IsSemialgebraic.exists_update`, `IsSemialgebraic.forall_update`).

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Proposition 2.2.4][BCR]
* [L. van den Dries, *Tame topology and o-minimal structures*, Chapter 1][vdD]
-/

open Set hiding ofPred_and ofPred_or ofPred_exists ofPred_forall
open MvPolynomial

/-! ### Polynomial functions -/

section PolynomialFun

variable {ι : Type*}

/-- `f : ℝ^ι → ℝ` is a *polynomial function*: `f x = p(x)` for a real polynomial `p`. -/
@[fun_prop]
def IsPolynomialFun (f : (ι → ℝ) → ℝ) : Prop := ∃ p : MvPolynomial ι ℝ, ∀ x, f x = eval x p

namespace IsPolynomialFun

@[fun_prop] lemma const (c : ℝ) : IsPolynomialFun fun _ : ι → ℝ ↦ c := ⟨C c, fun _ ↦ by simp⟩

@[fun_prop] lemma apply (i : ι) : IsPolynomialFun fun x : ι → ℝ ↦ x i := ⟨X i, fun _ ↦ by simp⟩

@[fun_prop] lemma eval (p : MvPolynomial ι ℝ) : IsPolynomialFun fun x ↦ eval x p :=
  ⟨p, fun _ ↦ rfl⟩

@[fun_prop] lemma add {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun fun x ↦ f x + g x := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x ↦ by simp [hp, hq]⟩

@[fun_prop] lemma sub {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun fun x ↦ f x - g x := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun x ↦ by simp [hp, hq]⟩

@[fun_prop] lemma mul {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsPolynomialFun fun x ↦ f x * g x := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x ↦ by simp [hp, hq]⟩

@[fun_prop] lemma neg {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) :
    IsPolynomialFun fun x ↦ -f x := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x ↦ by simp [hp]⟩

@[fun_prop] lemma pow {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (n : ℕ) :
    IsPolynomialFun fun x ↦ f x ^ n := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun x ↦ by simp [hp]⟩

@[fun_prop] lemma sum {α : Type*} (s : Finset α) {f : α → (ι → ℝ) → ℝ}
    (hf : ∀ a, IsPolynomialFun (f a)) : IsPolynomialFun fun x ↦ ∑ a ∈ s, f a x := by
  choose p hp using hf
  exact ⟨∑ a ∈ s, p a, fun x ↦ by simp [hp]⟩

/-- Substitution of polynomial functions into a polynomial. -/
lemma eval_comp {κ : Type*} {g : (ι → ℝ) → κ → ℝ} (hg : ∀ k, IsPolynomialFun fun x ↦ g x k)
    (p : MvPolynomial κ ℝ) : IsPolynomialFun fun x ↦ MvPolynomial.eval (g x) p := by
  choose q hq using hg
  refine ⟨bind₁ q p, fun x ↦ ?_⟩
  have h1 : MvPolynomial.eval x (bind₁ q p) =
      MvPolynomial.eval (fun k ↦ MvPolynomial.eval x (q k)) p :=
    eval₂Hom_bind₁ _ _ _ _
  have h2 : g x = fun k ↦ MvPolynomial.eval x (q k) := funext fun k ↦ hq k x
  change MvPolynomial.eval (g x) p = _
  rw [h1, h2]

/-- Precomposition with a map of index sets. -/
lemma comp {κ : Type*} {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (e : ι → κ) :
    IsPolynomialFun fun x : κ → ℝ ↦ f (x ∘ e) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨rename e p, fun x ↦ by simp [hp, eval_rename]⟩

lemma continuous {f : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  simpa only [← funext hp] using p.continuous_eval

end IsPolynomialFun

end PolynomialFun

/-! ### First-order combinators -/

namespace IsSemialgebraic

section Combinators

variable {ι : Type*}

lemma ofPred_lt {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x < g x} := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  simpa only [hp, hq] using IsSemialgebraic.lt p q

lemma ofPred_le {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x ≤ g x} := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  simpa only [hp, hq] using IsSemialgebraic.le p q

lemma ofPred_eq {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x = g x} := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  simpa only [hp, hq] using IsSemialgebraic.eq p q

lemma ofPred_ne {f g : (ι → ℝ) → ℝ} (hf : IsPolynomialFun f) (hg : IsPolynomialFun g) :
    IsSemialgebraic {x | f x ≠ g x} := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  simpa only [hp, hq] using IsSemialgebraic.ne p q

/-- Substitution of polynomial functions: `{x | F x ∈ S}` is semialgebraic if `S` is and the
coordinates of `F` are polynomial functions. -/
lemma ofPred_mem {κ : Type*} {S : Set (κ → ℝ)} (hS : IsSemialgebraic S)
    {F : (ι → ℝ) → κ → ℝ} (hF : ∀ k, IsPolynomialFun fun x ↦ F x k) :
    IsSemialgebraic {x | F x ∈ S} := by
  choose p hp using hF
  convert hS.preimage_polynomialMap p using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage]
  congr! 1
  funext k
  exact hp k x

lemma ofPred_const (p : Prop) : IsSemialgebraic {_x : ι → ℝ | p} := by
  by_cases hp : p
  · simpa [hp] using IsSemialgebraic.univ
  · simpa [hp] using IsSemialgebraic.empty

lemma ofPred_and {P Q : (ι → ℝ) → Prop} (hP : IsSemialgebraic {x | P x})
    (hQ : IsSemialgebraic {x | Q x}) : IsSemialgebraic {x | P x ∧ Q x} :=
  hP.inter hQ

lemma ofPred_or {P Q : (ι → ℝ) → Prop} (hP : IsSemialgebraic {x | P x})
    (hQ : IsSemialgebraic {x | Q x}) : IsSemialgebraic {x | P x ∨ Q x} :=
  hP.union hQ

lemma ofPred_not {P : (ι → ℝ) → Prop} (hP : IsSemialgebraic {x | P x}) :
    IsSemialgebraic {x | ¬ P x} :=
  hP.compl

lemma ofPred_imp {P Q : (ι → ℝ) → Prop} (hP : IsSemialgebraic {x | P x})
    (hQ : IsSemialgebraic {x | Q x}) : IsSemialgebraic {x | P x → Q x} := by
  simpa only [imp_iff_not_or] using hP.ofPred_not.ofPred_or hQ

lemma ofPred_iff {P Q : (ι → ℝ) → Prop} (hP : IsSemialgebraic {x | P x})
    (hQ : IsSemialgebraic {x | Q x}) : IsSemialgebraic {x | P x ↔ Q x} := by
  simpa only [iff_iff_implies_and_implies] using (hP.ofPred_imp hQ).ofPred_and (hQ.ofPred_imp hP)

/-- Existential quantification over `ℝ`: the bound variable becomes the coordinate `none`. -/
lemma ofPred_exists {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {w : Option ι → ℝ | P (fun i ↦ w (some i)) (w none)}) :
    IsSemialgebraic {x | ∃ t, P x t} :=
  h.exists_real

/-- Universal quantification over `ℝ`: the bound variable becomes the coordinate `none`. -/
lemma ofPred_forall {P : (ι → ℝ) → ℝ → Prop}
    (h : IsSemialgebraic {w : Option ι → ℝ | P (fun i ↦ w (some i)) (w none)}) :
    IsSemialgebraic {x | ∀ t, P x t} :=
  h.forall_real

/-- A finite conjunction. -/
lemma ofPred_forall_finite {α : Type*} [Finite α] {P : α → (ι → ℝ) → Prop}
    (h : ∀ a, IsSemialgebraic {x | P a x}) : IsSemialgebraic {x | ∀ a, P a x} := by
  convert IsSemialgebraic.iInter h using 1
  ext x
  simp

/-- A finite disjunction. -/
lemma ofPred_exists_finite {α : Type*} [Finite α] {P : α → (ι → ℝ) → Prop}
    (h : ∀ a, IsSemialgebraic {x | P a x}) : IsSemialgebraic {x | ∃ a, P a x} := by
  convert IsSemialgebraic.iUnion h using 1
  ext x
  simp

/-- Existential quantification over `ℝ^κ`, `κ` finite: the bound variables become the
coordinates `Sum.inr k`. -/
lemma ofPred_exists_pi {κ : Type*} [Finite κ] {P : (ι → ℝ) → (κ → ℝ) → Prop}
    (h : IsSemialgebraic {w : ι ⊕ κ → ℝ | P (fun i ↦ w (.inl i)) (fun k ↦ w (.inr k))}) :
    IsSemialgebraic {x | ∃ y, P x y} :=
  h.exists_sumElim

/-- Universal quantification over `ℝ^κ`, `κ` finite. -/
lemma ofPred_forall_pi {κ : Type*} [Finite κ] {P : (ι → ℝ) → (κ → ℝ) → Prop}
    (h : IsSemialgebraic {w : ι ⊕ κ → ℝ | P (fun i ↦ w (.inl i)) (fun k ↦ w (.inr k))}) :
    IsSemialgebraic {x | ∀ y, P x y} := by
  have := (ofPred_not h).exists_sumElim
  rw [← compl_iff]
  convert this using 1
  ext x
  simp

end Combinators

/-! ### Quantifying a coordinate in place -/

variable {ι : Type*} [DecidableEq ι]

/-- Quantifying a coordinate existentially: `{x | ∃ t, x[n ↦ t] ∈ S}` is semialgebraic. -/
theorem exists_update {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) (n : ι) :
    IsSemialgebraic {x : ι → ℝ | ∃ t : ℝ, Function.update x n t ∈ S} := by
  -- `ι ≃ Option {i // i ≠ n}`
  let e : ι → Option {i // i ≠ n} := fun i ↦ if h : i = n then none else some ⟨i, h⟩
  have key (x : ι → ℝ) (t : ℝ) :
      (fun o ↦ Option.elim o t (x ∘ Subtype.val)) ∘ e = Function.update x n t := by
    funext i
    by_cases h : i = n
    · subst h
      simp [e]
    · simp [e, h]
  convert (hS.preimage_comp e).exists_real.preimage_comp Subtype.val using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, key]

/-- Quantifying a coordinate universally: `{x | ∀ t, x[n ↦ t] ∈ S}` is semialgebraic. -/
theorem forall_update {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) (n : ι) :
    IsSemialgebraic {x : ι → ℝ | ∀ t : ℝ, Function.update x n t ∈ S} := by
  rw [← compl_iff]
  convert hS.compl.exists_update n using 1
  ext x
  simp

/-- Membership after substituting a coordinate: `{x | x[n ↦ p(x)] ∈ S}` is semialgebraic for a
polynomial `p`. -/
theorem preimage_update {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) (n : ι)
    (p : MvPolynomial ι ℝ) :
    IsSemialgebraic {x : ι → ℝ | Function.update x n (eval x p) ∈ S} := by
  convert hS.preimage_polynomialMap (fun i ↦ if i = n then p else X i) using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage]
  congr! 1
  funext i
  by_cases h : i = n
  · subst h
    simp
  · simp [h]

end IsSemialgebraic
