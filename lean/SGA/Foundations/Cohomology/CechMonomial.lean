/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech
import Mathlib.Data.Finsupp.Basic

/-!
# Čech complexes graded by monomials

This file contains the combinatorial part of the computation of the cohomology of projective
space by Čech cochains (Stacks Project, Tag 01XT; Hartshorne III.5.1; EGA III 2.1.12).

Let `U : ι → Opens X` be a family of opens and `P` a presheaf of abelian groups. Suppose the
groups of sections `P(U_x)` over the finite intersections embed compatibly (`Φ`) into a fixed
group `M →₀ A` of "Laurent polynomials", and that the image of `P(U_x)` is the set of those
elements whose monomials lie in `S x`. If there is a choice `κ : M → ι` such that the monomial
`μ` is allowed on `U_x` as soon as it is allowed on `U_{κ μ} ∩ U_x`, then the Čech complex is
exact in positive degrees: on the `μ`-component, the cone construction `c ↦ c_{κ μ, -}` is a
contracting homotopy.

## Main results

* `TopCat.Presheaf.cechComplex_exactAt_of_embedding`: exactness of the Čech complex is reduced to
  exactness of the corresponding complex of "constant" cochains `(Fin (n + 1) → ι) → L`.
* `TopCat.Presheaf.exists_cechDConst_eq_of_support`: exactness of the complex of cochains with
  values in `M →₀ A` subject to support conditions, by the monomial-wise cone construction.
-/

universe w v u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Presheaf

section Const

variable {ι : Type w} {L : Type*} [AddCommGroup L]

/-- The Čech differential on cochains with values in a fixed abelian group:
`(d c)_{x₀ … x_{n+1}} = ∑ᵢ (-1)ⁱ c_{x₀ … x̂ᵢ … x_{n+1}}`. -/
def cechDConst (n : ℕ) (c : (Fin (n + 1) → ι) → L) : (Fin (n + 2) → ι) → L :=
  fun x ↦ ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • c (x ∘ Fin.succAbove i)

/-- The cone identity for the constant Čech differential. -/
lemma cechDConst_cons (k : ι) {n : ℕ} (c : (Fin (n + 2) → ι) → L) (x : Fin (n + 2) → ι) :
    cechDConst (n + 1) c (Fin.cons k x) =
      c x - ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • c (Fin.cons k (x ∘ Fin.succAbove j)) := by
  rw [cechDConst, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib,
    cons_comp_succAbove_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    cons_comp_succAbove_succ]

lemma cechDConst_sub (n : ℕ) (b e : (Fin (n + 1) → ι) → L) :
    cechDConst n (b - e) = cechDConst n b - cechDConst n e := by
  funext x
  simp [cechDConst, Finset.sum_sub_distrib, smul_sub]

lemma cechDConst_add (n : ℕ) (b e : (Fin (n + 1) → ι) → L) :
    cechDConst n (b + e) = cechDConst n b + cechDConst n e := by
  funext x
  simp [cechDConst, Finset.sum_add_distrib, smul_add]

/-- The constant Čech differential commutes with additive maps. -/
lemma cechDConst_map {L' : Type*} [AddCommGroup L'] (f : L →+ L') (n : ℕ)
    (c : (Fin (n + 1) → ι) → L) :
    cechDConst n (fun x ↦ f (c x)) = fun x ↦ f (cechDConst n c x) := by
  funext x
  simp [cechDConst, map_sum, map_zsmul]

/-- The constant Čech differential squares to zero. -/
lemma cechDConst_cechDConst {G : Type v} [AddCommGroup G] (n : ℕ) (c : (Fin (n + 1) → ι) → G) :
    cechDConst (n + 1) (cechDConst n c) = 0 := by
  let P : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of PUnit.{1}) :=
    (Functor.const _).obj (AddCommGrpCat.of G)
  let U : ι → Opens (TopCat.of PUnit.{1}) := fun _ ↦ ⊤
  have h (m : ℕ) (c : CechCochain U P m) : cechD U P m c = cechDConst m c := by
    funext x
    rw [cechD_apply, cechDConst]
    rfl
  have := cechD_cechD U P n c
  rwa [h, h] at this

end Const

section Embedding

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X) (P : TopCat.Presheaf AddCommGrpCat.{v} X)
  {L : Type*} [AddCommGroup L]
  (Φ : ∀ {m : ℕ} (x : Fin (m + 1) → ι), P.obj (op (cechOpen U x)) →+ L)

/-- If the maps `Φ` commute with restrictions, they transform the Čech differential into the
constant one. -/
lemma cechD_embedding
    (hΦ : ∀ {m m' : ℕ} (x : Fin (m + 1) → ι) (y : Fin (m' + 1) → ι)
      (h : cechOpen U x ≤ cechOpen U y) (s : P.obj (op (cechOpen U y))),
      Φ x (P.map (homOfLE h).op s) = Φ y s)
    {n : ℕ} (c : CechCochain U P n) (x : Fin (n + 2) → ι) :
    Φ x (cechD U P n c x) = cechDConst n (fun y ↦ Φ y (c y)) x := by
  rw [cechD_apply, map_sum, cechDConst]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, hΦ]

/-- Let `Φ` be a compatible family of embeddings of the groups of sections of `P` over the
finite intersections of the `U i` into a fixed group `L`. If the complex of `L`-valued cochains
`x ↦ c x ∈ Φ(P(U_x))` is exact in degree `p + 1`, so is the Čech complex of `P`. -/
theorem cechComplex_exactAt_of_embedding
    (hΦ : ∀ {m m' : ℕ} (x : Fin (m + 1) → ι) (y : Fin (m' + 1) → ι)
      (h : cechOpen U x ≤ cechOpen U y) (s : P.obj (op (cechOpen U y))),
      Φ x (P.map (homOfLE h).op s) = Φ y s)
    (hinj : ∀ {m : ℕ} (x : Fin (m + 1) → ι), Function.Injective (Φ x)) (p : ℕ)
    (hexact : ∀ c : (Fin (p + 2) → ι) → L, (∀ x, c x ∈ Set.range (Φ x)) →
      cechDConst (p + 1) c = 0 →
      ∃ b : (Fin (p + 1) → ι) → L, (∀ y, b y ∈ Set.range (Φ y)) ∧ cechDConst p b = c) :
    (cechComplex U P).ExactAt (p + 1) := by
  rw [cechComplex_exactAt_succ_iff]
  intro c hc
  obtain ⟨b', hb', hdb'⟩ := hexact (fun x ↦ Φ x (c x)) (fun x ↦ ⟨c x, rfl⟩) (funext fun x ↦ by
    rw [← cechD_embedding U P Φ hΦ, hc]
    exact map_zero _)
  choose b hb using hb'
  refine ⟨b, funext fun x ↦ hinj x ?_⟩
  rw [cechD_embedding U P Φ hΦ]
  simp only [hb, hdb']

end Embedding

section Monomial

variable {ι : Type w} {M A : Type*} [AddCommGroup A]

/-- The cone construction on monomials: the `μ`-coefficient of `coneMonomial κ c y` is the
`μ`-coefficient of `c (κ μ, y)`. -/
noncomputable def coneMonomial [Fintype ι] [DecidableEq ι] (κ : M → ι) {n : ℕ}
    (c : (Fin (n + 2) → ι) → (M →₀ A)) (y : Fin (n + 1) → ι) : M →₀ A :=
  ∑ k : ι, (c (Fin.cons k y)).filter fun μ ↦ κ μ = k

lemma coneMonomial_apply [Fintype ι] [DecidableEq ι] (κ : M → ι) {n : ℕ}
    (c : (Fin (n + 2) → ι) → (M →₀ A)) (y : Fin (n + 1) → ι) (μ : M) :
    coneMonomial κ c y μ = c (Fin.cons (κ μ) y) μ := by
  rw [coneMonomial, Finsupp.finsetSum_apply]
  simp only [Finsupp.filter_apply]
  rw [Finset.sum_ite_eq Finset.univ (κ μ) (fun k ↦ c (Fin.cons k y) μ)]
  simp

/-- **Monomial-wise exactness of Čech complexes** (the combinatorial core of Stacks Tag 01XT).
Let `S x ⊆ M` be sets of allowed monomials, indexed by tuples `x`, and `κ : M → ι` such that a
monomial `μ` allowed for `(κ μ, y)` is allowed for `y`. Then every cocycle of degree `p + 1` of
the complex of `(M →₀ A)`-valued cochains with `supp (c x) ⊆ S x` is a coboundary of such a
cochain. -/
theorem exists_cechDConst_eq_of_support [Finite ι]
    (S : ∀ {m : ℕ}, (Fin (m + 1) → ι) → Set M) (κ : M → ι)
    (hκ : ∀ {m : ℕ} (y : Fin (m + 1) → ι) (μ : M), μ ∈ S (Fin.cons (κ μ) y) → μ ∈ S y)
    {p : ℕ} (c : (Fin (p + 2) → ι) → (M →₀ A)) (hc : ∀ x, ↑(c x).support ⊆ S x)
    (hdc : cechDConst (p + 1) c = 0) :
    ∃ b : (Fin (p + 1) → ι) → (M →₀ A), (∀ y, ↑(b y).support ⊆ S y) ∧ cechDConst p b = c := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨coneMonomial κ c, fun y μ hμ ↦ ?_, funext fun x ↦ Finsupp.ext fun μ ↦ ?_⟩
  · rw [Finset.mem_coe, Finsupp.mem_support_iff, coneMonomial_apply] at hμ
    exact hκ y μ (hc _ (Finsupp.mem_support_iff.mpr hμ))
  · have h := congrArg (fun f ↦ f μ) (congrFun hdc (Fin.cons (κ μ) x))
    simp only [cechDConst_cons, Pi.zero_apply, Finsupp.coe_zero, Finsupp.coe_sub,
      Pi.sub_apply, sub_eq_zero] at h
    rw [h, cechDConst, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finsupp.smul_apply, Finsupp.smul_apply, coneMonomial_apply]

end Monomial

section Surjective

variable {G : Type v} [AddCommGroup G]

/-- Exactness of the complex of cochains supported on surjective tuples, above the top degree:
for a finite `ι` with `#ι ≤ p + 1`, every cocycle of degree `p + 1` supported on surjective tuples
`Fin (p + 2) → ι` is the coboundary of a cochain supported on surjective tuples. (This complex
computes the relative cohomology of a simplex modulo its boundary; it is the part of the Čech
complex of `𝒪(d)` on projective space coming from the monomials with all exponents negative.) -/
theorem exists_cechDConst_eq_of_surjective : ∀ (n : ℕ) {ι : Type w} [Fintype ι],
    Fintype.card ι = n → ∀ {p : ℕ}, n ≤ p + 1 → ∀ (c : (Fin (p + 2) → ι) → G),
    (∀ x, ¬ Function.Surjective x → c x = 0) → cechDConst (p + 1) c = 0 →
    ∃ b : (Fin (p + 1) → ι) → G, (∀ y, ¬ Function.Surjective y → b y = 0) ∧
      cechDConst p b = c := by
  intro n
  induction n with
  | zero =>
    intro ι _ hcard p _ c _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    exact ⟨0, fun _ _ ↦ rfl, funext fun x ↦ isEmptyElim (x 0)⟩
  | succ n ih =>
    intro ι _ hcard p hp c hc hdc
    classical
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨k⟩ := this
    -- the cone on `k`
    set b₁ : (Fin (p + 1) → ι) → G := fun y ↦ c (Fin.cons k y) with hb₁
    have hdb₁ : cechDConst p b₁ = c := by
      funext x
      have h := congrFun hdc (Fin.cons k x)
      rw [cechDConst_cons, Pi.zero_apply, sub_eq_zero] at h
      rw [h]
      rfl
    have hb₁s (y : Fin (p + 1) → ι) (hk : k ∈ Set.range y) (hy : ¬ Function.Surjective y) :
        b₁ y = 0 := by
      refine hc _ fun hs ↦ hy fun i ↦ ?_
      obtain ⟨a, ha⟩ := hs i
      induction a using Fin.cases with
      | zero => simpa [← ha] using hk
      | succ a => exact ⟨a, by simpa using ha⟩
    cases p with
    | zero =>
      -- `ι` has a single element, and every tuple is surjective
      refine ⟨b₁, fun y hy ↦ absurd (fun i ↦ ⟨0, ?_⟩) hy, hdb₁⟩
      have : Fintype.card ι ≤ 1 := by omega
      exact Fintype.card_le_one_iff.mp this _ _
    | succ p =>
      -- restrict the cone to the tuples avoiding `k`
      let ι' := {i : ι // i ≠ k}
      have hcard' : Fintype.card ι' = n := by
        simp [ι', Fintype.card_subtype_compl, hcard]
      have hs' (y' : Fin (p + 2) → ι') (hy' : ¬ Function.Surjective y') :
          b₁ (Subtype.val ∘ y') = 0 := by
        refine hc _ fun hs ↦ hy' fun i ↦ ?_
        obtain ⟨a, ha⟩ := hs i.1
        induction a using Fin.cases with
        | zero => exact absurd (by simpa using ha.symm) i.2
        | succ a => exact ⟨a, Subtype.ext (by simpa using ha)⟩
      have hd' : cechDConst (p + 1) (fun y' : Fin (p + 2) → ι' ↦ b₁ (Subtype.val ∘ y')) = 0 := by
        funext y'
        rw [Pi.zero_apply]
        change cechDConst (p + 1) b₁ (Subtype.val ∘ y') = 0
        rw [hdb₁]
        refine hc _ fun hs ↦ ?_
        obtain ⟨a, ha⟩ := hs k
        exact (y' a).2 ha
      obtain ⟨e', he's, hde'⟩ := ih hcard' (p := p) (by omega) _ hs' hd'
      · classical
        let e : (Fin (p + 1) → ι) → G := fun y ↦
          if h : ∀ j, y j ≠ k then e' (fun j ↦ ⟨y j, h j⟩) else 0
        refine ⟨b₁ - cechDConst p e, fun y hy ↦ ?_, ?_⟩
        · by_cases hk : k ∈ Set.range y
          · rw [Pi.sub_apply, hb₁s y hk hy, zero_sub, neg_eq_zero, cechDConst,
              Finset.sum_eq_zero]
            intro i _
            by_cases h : ∀ j, (y ∘ Fin.succAbove i) j ≠ k
            · rw [show e (y ∘ Fin.succAbove i) = e' _ from dite_eq_left h, he's, smul_zero]
              intro hs
              refine hy fun l ↦ ?_
              by_cases hl : l = k
              · rw [hl]
                exact hk
              · obtain ⟨a, ha⟩ := hs ⟨l, hl⟩
                exact ⟨_, congrArg Subtype.val ha⟩
            · rw [show e (y ∘ Fin.succAbove i) = 0 from dite_eq_right h, smul_zero]
          · have hy' : ∀ j, y j ≠ k := fun j hj ↦ hk ⟨j, hj⟩
            have := congrFun hde' (fun j ↦ ⟨y j, hy' j⟩)
            rw [Pi.sub_apply, sub_eq_zero]
            refine this.symm.trans ?_
            rw [cechDConst, cechDConst]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [show e (y ∘ Fin.succAbove i) = e' _ from dite_eq_left fun j ↦ hy' _]
            rfl
        · rw [cechDConst_sub, cechDConst_cechDConst, sub_zero]
          exact hdb₁

end Surjective

end TopCat.Presheaf
