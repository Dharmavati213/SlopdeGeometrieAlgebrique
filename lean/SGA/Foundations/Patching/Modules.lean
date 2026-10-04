/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination
import SGA.Foundations.Patching.Factorization

/-!
# Patching of free modules over rings with the factorization property

Let `R` be a commutative ring and `A₁, A₂ ⊆ R` subrings. They have the *factorization property*
in size `ι` (`Subring.HasGLFactorization`) if every invertible `ι × ι` matrix over `R` is a
product `B₁ B₂` of an invertible matrix over `A₁` and one over `A₂`. In patching over fields
(Harbater–Hartmann, *Patching over fields*, Israel J. Math. 176 (2010), §2) `R` is the product
of the fields `F_℘` of the branches, `A₁` is the field `F_U` and `A₂` is the product of the
fields `F_P` of the points; with a single branch, all three are fields.

Main result, `Subring.exists_basis_span_eq` (patching of free modules): let `W` be a free
`R`-module with bases `b₁`, `b₂`, and let `Vᵢ = span_{Aᵢ} bᵢ` be the corresponding `Aᵢ`-forms of
`W`. There is a basis `b` of `W` with `span_{A₁} b = V₁` and `span_{A₂} b = V₂`, and then
`V₁ ∩ V₂ = span_{A₁ ∩ A₂} b`. So `V₁ ∩ V₂` is a free `(A₁ ∩ A₂)`-module, with a basis that is an
`R`-basis of `W` and an `Aᵢ`-basis of `Vᵢ`: the solution of the patching problem induces the
given data `Vᵢ` after base change to `Aᵢ`. The coordinate form is
`Subring.exists_basis_forall_repr_mem_iff`; over fields, `Subfield.span_inter_eq_top` is a
basis-free consequence.

The factorization property comes from the simultaneous factorization of matrices over complete
rings (`Matrix.exists_eq_map_mul_map`) and a density condition
(`Subring.hasGLFactorization_of_isAdicComplete`).
-/

open Matrix

namespace Module.Basis

variable {ι R W : Type*} [Fintype ι] [CommRing R] [AddCommGroup W] [Module R W]

omit [Fintype ι] in
/-- An element lies in the `A`-span of a basis iff its coordinates lie in `A`. -/
lemma mem_span_subring_iff [Finite ι] (b : Basis ι R W) (A : Subring R) {v : W} :
    v ∈ Submodule.span A (Set.range b) ↔ ∀ i, b.repr v i ∈ A := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [b.repr_self, Finsupp.single_apply]
      split_ifs
      · exact A.one_mem
      · exact A.zero_mem
    | zero => exact fun i ↦ by rw [map_zero, Finsupp.zero_apply]; exact A.zero_mem
    | add x y _ _ hx hy =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact A.add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      rw [Subring.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact A.mul_mem a.2 (hx i)
  · intro hv
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have : b.repr v i • b i = (⟨b.repr v i, hv i⟩ : A) • b i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- If `b' j = ∑ i, B i j • b i` for a matrix `B` over `A`, an element with coordinates in `A` for
`b'` has coordinates in `A` for `b`. -/
lemma repr_mem_of_eq_sum {b b' : Basis ι R W} {A : Subring R} (B : Matrix ι ι A)
    (h : ∀ j, b' j = ∑ i, (B i j : R) • b i) {v : W} (hv : ∀ j, b'.repr v j ∈ A) (i : ι) :
    b.repr v i ∈ A := by
  have hcol : ∀ j, b.repr (b' j) i = B i j := fun j ↦ by
    rw [h j]
    exact congrFun (b.repr_sum_self fun i ↦ (B i j : R)) i
  have hrepr : b.repr v i = ∑ j, b'.repr v j * B i j := by
    conv_lhs => rw [← b'.sum_repr v]
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, Finsupp.smul_apply, hcol, smul_eq_mul]
  rw [hrepr]
  exact A.sum_mem fun j _ ↦ A.mul_mem (hv j) (B i j).2

/-- If `b' j = ∑ i, B i j • b i` for a matrix `B` that is invertible over the subring `A`, an
element has coordinates in `A` for `b` iff it has coordinates in `A` for `b'`. -/
lemma forall_repr_mem_iff_of_eq_sum [DecidableEq ι] {b b' : Basis ι R W} {A : Subring R}
    {B : Matrix ι ι A} (hB : IsUnit B) (h : ∀ j, b' j = ∑ i, (B i j : R) • b i) (v : W) :
    (∀ i, b.repr v i ∈ A) ↔ ∀ i, b'.repr v i ∈ A := by
  refine ⟨fun hv ↦ repr_mem_of_eq_sum B⁻¹ (fun j ↦ ?_) hv, fun hv ↦ repr_mem_of_eq_sum B h hv⟩
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hB)
  have hcoe : ∀ l, (((B * B⁻¹) l j : A) : R) = ∑ i, (B l i : R) * (B⁻¹ i j : R) := fun l ↦ by
    rw [Matrix.mul_apply]
    push_cast
    rfl
  calc b j = ∑ l, (((B * B⁻¹) l j : A) : R) • b l := by
        rw [hBB, Finset.sum_eq_single j (fun l _ hl ↦ by rw [Matrix.one_apply_ne hl]; simp)
          (by simp), Matrix.one_apply_eq]
        simp
    _ = ∑ i, (B⁻¹ i j : R) • b' i := by
        simp_rw [hcoe, h, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
        rw [mul_comm]

end Module.Basis

namespace Subring

variable {R : Type*} [CommRing R]

/-- Two subrings `A₁, A₂` of `R` have the factorization property in size `ι` if
`GL_ι(R) = GL_ι(A₁) · GL_ι(A₂)`. -/
def HasGLFactorization (A₁ A₂ : Subring R) (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ M : Matrix ι ι R, IsUnit M → ∃ (B₁ : Matrix ι ι A₁) (B₂ : Matrix ι ι A₂),
    IsUnit B₁ ∧ IsUnit B₂ ∧ M = B₁.map ((↑) : A₁ → R) * B₂.map ((↑) : A₂ → R)

/-- A square matrix over a subring `A` whose image is invertible is invertible, if `A` contains
the inverses of its elements that are units of `R`. -/
lemma isUnit_of_isUnit_map {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Subring R}
    (hA : ∀ a : A, IsUnit (a : R) → IsUnit a) {Z : Matrix ι ι A}
    (hZ : IsUnit (Z.map ((↑) : A → R))) : IsUnit Z := by
  rw [isUnit_iff_isUnit_det] at hZ ⊢
  refine hA _ ?_
  change IsUnit (A.subtype Z.det)
  rw [RingHom.map_det]
  exact hZ

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module R W]
  {A₁ A₂ : Subring R}

/-- **Patching of free modules**, in coordinates: if `A₁, A₂` have the factorization property in
size `ι`, then for bases `b₁, b₂` of `W` there is a basis `b` whose coordinates lie in `A₁` exactly
when those for `b₁` do, and in `A₂` exactly when those for `b₂` do. -/
theorem exists_basis_forall_repr_mem_iff (h : A₁.HasGLFactorization A₂ ι)
    (b₁ b₂ : Module.Basis ι R W) :
    ∃ b : Module.Basis ι R W, ∀ v : W,
      ((∀ i, b.repr v i ∈ A₁) ↔ ∀ i, b₁.repr v i ∈ A₁) ∧
      ((∀ i, b.repr v i ∈ A₂) ↔ ∀ i, b₂.repr v i ∈ A₂) := by
  have hM : IsUnit (b₁.toMatrix b₂) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (b₁.toMatrix_mul_toMatrix_flip b₂))
  obtain ⟨B₁, B₂, hB₁, hB₂, hfac⟩ := h _ hM
  have hM₁ : IsUnit (B₁.map ((↑) : A₁ → R)) := hB₁.map A₁.subtype.mapMatrix
  let e : W ≃ₗ[R] W := LinearMap.GeneralLinearGroup.generalLinearEquiv R W
    (hM₁.map (Matrix.toLinAlgEquiv b₁)).unit
  let b := b₁.map e
  have hb : ∀ j, b j = ∑ i, (B₁ i j : R) • b₁ i := fun j ↦ by
    change Matrix.toLinAlgEquiv b₁ (B₁.map ((↑) : A₁ → R)) (b₁ j) = _
    rw [Matrix.toLinAlgEquiv_self]
    rfl
  have hb₂ : ∀ j, b₂ j = ∑ l, (B₂ l j : R) • b l := fun j ↦ by
    conv_lhs => rw [← b₁.sum_repr (b₂ j)]
    have hc : ∀ i, b₁.repr (b₂ j) i = ∑ l, (B₁ i l : R) * (B₂ l j : R) := fun i ↦ by
      rw [← Module.Basis.toMatrix_apply, hfac, Matrix.mul_apply]
      rfl
    simp_rw [hc, hb, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_comm]
  exact ⟨b, fun v ↦ ⟨(Module.Basis.forall_repr_mem_iff_of_eq_sum hB₁ hb v).symm,
    Module.Basis.forall_repr_mem_iff_of_eq_sum hB₂ hb₂ v⟩⟩

/-- **Patching of free modules** (Harbater–Hartmann): if `A₁, A₂` have the factorization property in
size `ι`, then for bases `b₁, b₂` of `W` there is a basis `b` of `W` with
`span_{A₁} b = span_{A₁} b₁` and `span_{A₂} b = span_{A₂} b₂`; the intersection of these two spans
is `span_{A₁ ∩ A₂} b`, a free `(A₁ ∩ A₂)`-module whose base changes to `A₁` and `A₂` are the given
ones. -/
theorem exists_basis_span_eq (h : A₁.HasGLFactorization A₂ ι) (b₁ b₂ : Module.Basis ι R W) :
    ∃ b : Module.Basis ι R W,
      Submodule.span A₁ (Set.range b) = Submodule.span A₁ (Set.range b₁) ∧
      Submodule.span A₂ (Set.range b) = Submodule.span A₂ (Set.range b₂) ∧
      (Submodule.span A₁ (Set.range b₁) : Set W) ∩ Submodule.span A₂ (Set.range b₂) =
        Submodule.span ↥(A₁ ⊓ A₂) (Set.range b) := by
  obtain ⟨b, hb⟩ := exists_basis_forall_repr_mem_iff h b₁ b₂
  refine ⟨b, ?_, ?_, ?_⟩
  · ext v
    rw [b.mem_span_subring_iff, b₁.mem_span_subring_iff, (hb v).1]
  · ext v
    rw [b.mem_span_subring_iff, b₂.mem_span_subring_iff, (hb v).2]
  · ext v
    rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe, SetLike.mem_coe,
      b₁.mem_span_subring_iff, b₂.mem_span_subring_iff, b.mem_span_subring_iff, ← (hb v).1,
      ← (hb v).2, ← forall_and]
    exact forall_congr' fun i ↦ Subring.mem_inf.symm

/-- **The factorization property from complete rings** (Harbater–Hartmann): let `R₀ → R` be a
ring map, and `f₁ : R₁ → R₀`, `f₂ : R₂ → R₀` as in the simultaneous factorization
`Matrix.exists_eq_map_mul_map` (complete for `t₁`, `t₂`; `R₀ = f₁(R₁) + f₂(R₂) + t R₀`). Let
`A₁, A₂ ⊆ R` be subrings containing the images of `R₁`, `R₂` and the inverses of their elements
that are units of `R`. If every element of `R` becomes integral after multiplication by a power of
`t`, and `A₂` is `t`-adically dense in `R` relative to `R₀`, then `A₁` and `A₂` have the
factorization property. -/
theorem hasGLFactorization_of_isAdicComplete {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁]
    [CommRing R₂] (i₀ : R₀ →+* R) {f₁ : R₁ →+* R₀} {f₂ : R₂ →+* R₀} {t₁ : R₁} {t₂ : R₂}
    {t : R₀} [IsAdicComplete (Ideal.span {t₁}) R₁] [IsAdicComplete (Ideal.span {t₂}) R₂]
    [IsHausdorff (Ideal.span {t}) R₀] (h₁ : f₁ t₁ = t) (h₂ : f₂ t₂ = t)
    (hdecomp : ∀ r : R₀, ∃ a b c, r = f₁ a + f₂ b + t * c)
    (hA₁ : ∀ r, i₀ (f₁ r) ∈ A₁) (hA₂ : ∀ r, i₀ (f₂ r) ∈ A₂)
    (hunit₁ : ∀ a : A₁, IsUnit (a : R) → IsUnit a) (hunit₂ : ∀ a : A₂, IsUnit (a : R) → IsUnit a)
    (hbound : ∀ z : R, ∃ (a : ℕ) (r : R₀), z * i₀ t ^ a = i₀ r)
    (hdense : ∀ (z : R) (N : ℕ), ∃ z' ∈ A₂, ∃ r : R₀, z - z' = i₀ t ^ N * i₀ r) :
    A₁.HasGLFactorization A₂ ι := by
  intro M hM
  -- a common power of `t` clears the denominators of `M`
  choose a r hr using hbound
  let A : ℕ := Finset.univ.sup fun ij : ι × ι ↦ a (M ij.1 ij.2)
  have hMA : ∀ i j, ∃ m : R₀, M i j * i₀ t ^ A = i₀ m := by
    intro i j
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.le_sup (f := fun ij : ι × ι ↦ a (M ij.1 ij.2)) (Finset.mem_univ (i, j)))
    refine ⟨r (M i j) * t ^ d, ?_⟩
    rw [show A = a (M i j) + d from hd, pow_add, ← mul_assoc, hr, map_mul, map_pow]
  choose M' hM' using hMA
  -- approximate `M⁻¹` by a matrix `C` over `A₂`, to order `t^{A+1}`
  choose z' hz'A hz'r hz' using hdense
  let C : Matrix ι ι R := Matrix.of fun i j ↦ z' (M⁻¹ i j) (A + 1)
  let N : Matrix ι ι R₀ := Matrix.of fun i j ↦ hz'r (M⁻¹ i j) (A + 1)
  have hCN : C = M⁻¹ - i₀ t ^ (A + 1) • N.map i₀ := by
    ext i j
    simp only [C, N, of_apply, Matrix.sub_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
    linear_combination (-1 : R) * hz' (M⁻¹ i j) (A + 1)
  have hτM : i₀ t ^ A • M = (Matrix.of M').map i₀ := by
    ext i j
    simp [← hM', mul_comm]
  have hMC : M * C = (1 + t • (Matrix.of M' * -N)).map i₀ := by
    rw [hCN, Matrix.mul_sub, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hM),
      Matrix.mul_smul, pow_succ', mul_smul, ← Matrix.smul_mul (i₀ t ^ A) M, hτM]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, map_apply, Matrix.add_apply, mul_apply,
      smul_eq_mul, map_add, map_mul, map_sum, map_neg, Matrix.neg_apply, Finset.mul_sum,
      Matrix.one_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  -- factor `M C` over `R₁` and `R₂`
  obtain ⟨B₁, B₂, hB₁, hB₂, hfac⟩ :=
    Matrix.exists_eq_map_mul_map_of_isUnit h₁ h₂ hdecomp (1 + t • (Matrix.of M' * -N)) ⟨_, rfl⟩
  let X : Matrix ι ι A₁ := Matrix.of fun i j ↦ ⟨i₀ (f₁ (B₁ i j)), hA₁ _⟩
  let Y : Matrix ι ι A₂ := Matrix.of fun i j ↦ ⟨i₀ (f₂ (B₂ i j)), hA₂ _⟩
  let Ĉ : Matrix ι ι A₂ := Matrix.of fun i j ↦ ⟨C i j, hz'A _ _⟩
  have hX : X.map ((↑) : A₁ → R) = (B₁.map f₁).map i₀ := rfl
  have hY : Y.map ((↑) : A₂ → R) = (B₂.map f₂).map i₀ := rfl
  have hĈ : Ĉ.map ((↑) : A₂ → R) = C := rfl
  have hMXY : M * C = X.map (↑) * Y.map (↑) := by
    rw [hMC, hfac, hX, hY, Matrix.map_mul]
  have hXu : IsUnit (X.map ((↑) : A₁ → R)) := by
    rw [hX]
    exact (hB₁.map f₁.mapMatrix).map i₀.mapMatrix
  have hYu : IsUnit (Y.map ((↑) : A₂ → R)) := by
    rw [hY]
    exact (hB₂.map f₂.mapMatrix).map i₀.mapMatrix
  have hCu : IsUnit C := by
    have : C = M⁻¹ * (X.map (↑) * Y.map (↑)) := by
      rw [← hMXY, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM),
        Matrix.one_mul]
    rw [this]
    exact ((isUnit_nonsing_inv_iff).mpr hM).mul (hXu.mul hYu)
  have hĈu : IsUnit Ĉ := isUnit_of_isUnit_map hunit₂ (hĈ ▸ hCu)
  refine ⟨X, Y * Ĉ⁻¹, isUnit_of_isUnit_map hunit₁ hXu,
    (isUnit_of_isUnit_map hunit₂ hYu).mul ((isUnit_nonsing_inv_iff).mpr hĈu), ?_⟩
  have hinv : C * (Ĉ⁻¹).map ((↑) : A₂ → R) = 1 := by
    rw [← hĈ]
    change A₂.subtype.mapMatrix Ĉ * A₂.subtype.mapMatrix Ĉ⁻¹ = 1
    rw [← map_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hĈu), map_one]
  calc M = M * C * (Ĉ⁻¹).map ((↑) : A₂ → R) := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = X.map (↑) * (Y * Ĉ⁻¹).map (↑) := by
      rw [hMXY, Matrix.mul_assoc]
      congr 1
      exact (Matrix.map_mul (f := A₂.subtype)).symm

end Subring

namespace Subfield

variable {F₀ : Type*} [Field F₀]

/-- A subfield contains the inverses of its non-zero elements. -/
lemma isUnit_of_isUnit_coe (F : Subfield F₀) (a : F.toSubring) (ha : IsUnit (a : F₀)) :
    IsUnit a := by
  refine ⟨⟨a, ⟨(a : F₀)⁻¹, F.inv_mem a.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · exact mul_inv_cancel₀ ha.ne_zero
  · exact inv_mul_cancel₀ ha.ne_zero

/-- A spanning set of a finite-dimensional vector space contains a basis indexed by any type of
the right cardinality. -/
lemma exists_basis_mem_of_span_eq_top {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {ι : Type*} [Fintype ι] (hι : Fintype.card ι = Module.finrank K W)
    {S : Set W} (hS : Submodule.span K S = ⊤) : ∃ b : Module.Basis ι K W, ∀ i, b i ∈ S := by
  obtain ⟨s, hsS, hspan, hli⟩ := exists_linearIndependent K S
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Fintype s := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card s = Fintype.card ι := by
    rw [hι, Module.finrank_eq_card_basis B]
  refine ⟨B.reindex (Fintype.equivOfCardEq hcard), fun i ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact hsS (Subtype.mem _)

/-- **Patching of vector spaces**, basis-free form: let `W` be a finite-dimensional
`F₀`-vector space, `V₁` an `F₁`-subspace and `V₂` an `F₂`-subspace, both spanning `W` over `F₀`.
If `F₁, F₂` have the factorization property in size `dim W`, then `V₁ ∩ V₂` spans `W` over `F₀`.
(The patching data need not be split: `W` is arbitrary, e.g. a non-split Galois algebra over
`F₀`.) -/
theorem span_inter_eq_top {W : Type*} [AddCommGroup W] [Module F₀ W] [FiniteDimensional F₀ W]
    {F₁ F₂ : Subfield F₀}
    (h : F₁.toSubring.HasGLFactorization F₂.toSubring (Fin (Module.finrank F₀ W)))
    (V₁ : Submodule F₁ W) (V₂ : Submodule F₂ W) (h₁ : Submodule.span F₀ (V₁ : Set W) = ⊤)
    (h₂ : Submodule.span F₀ (V₂ : Set W) = ⊤) :
    Submodule.span F₀ ((V₁ : Set W) ∩ V₂) = ⊤ := by
  obtain ⟨b₁, hb₁⟩ := exists_basis_mem_of_span_eq_top (ι := Fin (Module.finrank F₀ W))
    (Fintype.card_fin _) h₁
  obtain ⟨b₂, hb₂⟩ := exists_basis_mem_of_span_eq_top (ι := Fin (Module.finrank F₀ W))
    (Fintype.card_fin _) h₂
  obtain ⟨b, hb⟩ := Subring.exists_basis_forall_repr_mem_iff h b₁ b₂
  -- an element whose coordinates for `bᵢ` lie in `Fᵢ` lies in `Vᵢ`
  have hmem : ∀ {F : Subfield F₀} (V : Submodule F W)
      (b' : Module.Basis (Fin (Module.finrank F₀ W)) F₀ W),
      (∀ i, b' i ∈ V) → ∀ v : W, (∀ i, b'.repr v i ∈ F) → v ∈ V := by
    intro F V b' hb' v hv
    rw [← b'.sum_repr v]
    refine V.sum_mem fun i _ ↦ ?_
    have : b'.repr v i • b' i = (⟨b'.repr v i, hv i⟩ : F) • b' i := rfl
    rw [this]
    exact V.smul_mem _ (hb' i)
  have hcoord : ∀ (j i : Fin (Module.finrank F₀ W)) (F : Subfield F₀), b.repr (b j) i ∈ F :=
    fun j i F ↦ by
      rw [b.repr_self, Finsupp.single_apply]
      split_ifs
      · exact F.one_mem
      · exact F.zero_mem
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨hmem V₁ b₁ hb₁ _ ?_, hmem V₂ b₂ hb₂ _ ?_⟩
  · exact (hb (b j)).1.mp fun i ↦ hcoord j i F₁
  · exact (hb (b j)).2.mp fun i ↦ hcoord j i F₂

end Subfield
