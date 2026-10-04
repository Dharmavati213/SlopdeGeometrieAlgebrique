/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Degree counting for Artin–Schreier maps (the core of Serre's theorem on `p`-group kernels)

Serre's theorem (C. R. Acad. Sci. Paris 311 (1990)), used in Raynaud's proof of XIII.2.13,
says that embedding problems with `p`-group kernel for `π₁(𝔸¹_k)` have proper solutions. Its
key input is that `H¹(π₁, V)` is infinite for every non-zero `𝔽_p[π₁]`-module `V`: in terms of
the Galois algebra `B` of `V`, the cokernel of `℘ = F - 1` on the invariants
`M = (B ⊗ V)^H` is infinite. Following Serre, we prove it by counting degrees:

* `deg b w`: the degree of `w` in a free `k[T]`-module `W` with basis `b`;
* `exists_finrank_degFiltration_eq`: for a non-zero `k[T]`-submodule `M`, the `k`-dimension of
  `M_{≤ E} = {m ∈ M | deg m ≤ E}` is eventually `c + s E` with `s ≥ 1` (the leading
  coefficients stabilize);
* `exists_mem_forall_ne_add_sub`: if `F` is an injective `p`-semilinear map multiplying degrees by
  `p` up to bounded errors and `F M ⊆ M`, then `M` is not a finite union of translates of
  `℘(M)`, because `℘(M) ∩ M_{≤ D}` lies in a subspace of dimension about `s D (2p - 1)/p² < s D`
  and a vector space over an infinite field is not a finite union of proper subspaces.
-/
namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

open Polynomial Module

section Degree

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k[X] W]
  {I : Type*} [Fintype I] (b : Basis I k[X] W)

/-- The degree of `w` with respect to the `k[T]`-basis `b`: the largest degree of a coordinate. -/
noncomputable def deg (w : W) : ℕ := Finset.univ.sup fun i ↦ (b.repr w i).natDegree

lemma natDegree_repr_le_deg (w : W) (i : I) : (b.repr w i).natDegree ≤ deg b w :=
  Finset.le_sup (f := fun i ↦ (b.repr w i).natDegree) (Finset.mem_univ i)

lemma deg_le_iff {w : W} {E : ℕ} : deg b w ≤ E ↔ ∀ i, (b.repr w i).natDegree ≤ E := by
  simp [deg, Finset.sup_le_iff]

lemma deg_zero : deg b (0 : W) = 0 := by
  simp [deg]

lemma deg_add_le (w w' : W) : deg b (w + w') ≤ max (deg b w) (deg b w') := by
  rw [deg_le_iff]
  intro i
  rw [map_add, Finsupp.add_apply]
  exact (natDegree_add_le _ _).trans
    (max_le_max (natDegree_repr_le_deg b w i) (natDegree_repr_le_deg b w' i))

lemma deg_neg (w : W) : deg b (-w) = deg b w := by
  simp [deg]

lemma deg_sub_le (w w' : W) : deg b (w - w') ≤ max (deg b w) (deg b w') := by
  rw [sub_eq_add_neg, ← deg_neg b w']
  exact deg_add_le b _ _

lemma deg_smul_le (c : k[X]) (w : W) : deg b (c • w) ≤ c.natDegree + deg b w := by
  rw [deg_le_iff]
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_repr_le_deg b w i) _)

lemma exists_natDegree_repr_eq [Nonempty I] (w : W) : ∃ i, (b.repr w i).natDegree = deg b w := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i ↦ (b.repr w i).natDegree)
  exact ⟨i, hi.symm⟩

lemma le_deg_sub [Nonempty I] {w w' : W} (h : deg b w' < deg b w) : deg b w ≤ deg b (w - w') := by
  obtain ⟨i, hi⟩ := exists_natDegree_repr_eq b w
  have hlt : (b.repr w' i).natDegree < (b.repr w i).natDegree :=
    (natDegree_repr_le_deg b w' i).trans_lt (hi ▸ h)
  calc deg b w = (b.repr w i).natDegree := hi.symm
    _ = (b.repr (w - w') i).natDegree := by
        rw [map_sub, Finsupp.sub_apply, natDegree_sub_eq_left_of_natDegree_lt hlt]
    _ ≤ deg b (w - w') := natDegree_repr_le_deg b _ i

variable [Module k W] [IsScalarTower k k[X] W]

lemma smul_eq_C_smul (c : k) (w : W) : c • w = (C c : k[X]) • w := by
  rw [← algebraMap_smul (A := k[X]) c w, algebraMap_eq]

lemma deg_smul_k_le (c : k) (w : W) : deg b (c • w) ≤ deg b w := by
  rw [smul_eq_C_smul]
  exact (deg_smul_le b _ w).trans (by rw [natDegree_C, zero_add])

/-- The `k`-subspace of elements of degree `≤ E`. -/
def degLE (E : ℕ) : Submodule k W where
  carrier := {w | deg b w ≤ E}
  add_mem' {w w'} hw hw' := (deg_add_le b w w').trans (max_le hw hw')
  zero_mem' := by simp [deg_zero]
  smul_mem' c w hw := (deg_smul_k_le b c w).trans hw

lemma mem_degLE {E : ℕ} {w : W} : w ∈ degLE b E ↔ deg b w ≤ E := Iff.rfl

end Degree

section Levels

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k[X] W] [Module k W]
  [IsScalarTower k k[X] W] {I : Type*} [Fintype I] (b : Basis I k[X] W)

/-- The `E`-th coefficients of the coordinates, a `k`-linear map `W → kᴵ`. -/
noncomputable def coeffMap (E : ℕ) : W →ₗ[k] (I → k) where
  toFun w i := (b.repr w i).coeff E
  map_add' w w' := by
    ext i
    simp
  map_smul' c w := by
    ext i
    simp [smul_eq_C_smul (k := k), coeff_C_mul]

omit [Fintype I] in
lemma coeffMap_apply (E : ℕ) (w : W) (i : I) : coeffMap b E w i = (b.repr w i).coeff E := rfl

instance finiteDimensional_degLE (E : ℕ) : FiniteDimensional k (degLE b E) := by
  let f : degLE b E →ₗ[k] (Fin (E + 1) → I → k) :=
    LinearMap.pi fun j ↦ (coeffMap b j).comp (degLE b E).subtype
  refine Module.Finite.of_injective f fun w w' h ↦ ?_
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  set v := w - w'
  have hv : deg b (v : W) ≤ E := v.2
  apply Subtype.ext
  change (v : W) = 0
  apply b.repr.injective
  ext i j
  rw [map_zero, Finsupp.zero_apply, coeff_zero]
  by_cases hj : j ≤ E
  · have := congrFun (congrFun h ⟨j, Nat.lt_succ_of_le hj⟩) i
    exact this
  · exact coeff_eq_zero_of_natDegree_lt
      (((natDegree_repr_le_deg b _ i).trans hv).trans_lt (not_le.mp hj))

variable (M : Submodule k[X] W)

/-- The elements of `M` of degree `≤ E`, a finite-dimensional `k`-subspace. -/
noncomputable def degFiltration (E : ℕ) : Submodule k W := M.restrictScalars k ⊓ degLE b E

lemma mem_degFiltration {E : ℕ} {w : W} : w ∈ degFiltration b M E ↔ w ∈ M ∧ deg b w ≤ E := Iff.rfl

instance finiteDimensional_degFiltration (E : ℕ) : FiniteDimensional k (degFiltration b M E) :=
  Submodule.finiteDimensional_of_le inf_le_right

lemma degFiltration_mono {E E' : ℕ} (h : E ≤ E') : degFiltration b M E ≤ degFiltration b M E' :=
  fun _ hw ↦ ⟨hw.1, hw.2.trans h⟩

/-- The leading coefficients in degree `E` of the elements of `M` of degree `≤ E`. -/
noncomputable def leadingCoeffs (E : ℕ) : Submodule k (I → k) :=
  (degFiltration b M E).map (coeffMap b E)

lemma leadingCoeffs_le_leadingCoeffs_succ (E : ℕ) :
    leadingCoeffs b M E ≤ leadingCoeffs b M (E + 1) := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨(X : k[X]) • w, ⟨M.smul_mem _ hw.1, ?_⟩, ?_⟩
  · exact (deg_smul_le b X w).trans (by rw [natDegree_X, add_comm]; exact Nat.succ_le_succ hw.2)
  · ext i
    simp [coeffMap_apply, coeff_X_mul]

lemma leadingCoeffs_mono : Monotone (leadingCoeffs b M) :=
  monotone_nat_of_le_succ (leadingCoeffs_le_leadingCoeffs_succ b M)

lemma finrank_degFiltration_succ (E : ℕ) :
    finrank k (degFiltration b M (E + 1)) =
      finrank k (degFiltration b M E) + finrank k (leadingCoeffs b M (E + 1)) := by
  let f : degFiltration b M (E + 1) →ₗ[k] (I → k) :=
    (coeffMap b (E + 1)).comp (degFiltration b M (E + 1)).subtype
  have hrange : LinearMap.range f = leadingCoeffs b M (E + 1) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker :
      LinearMap.ker f = (degFiltration b M E).comap (degFiltration b M (E + 1)).subtype := by
    ext ⟨w, hw⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, f,
      LinearMap.comp_apply]
    constructor
    · intro h
      refine ⟨hw.1, (deg_le_iff b).mpr fun i ↦ ?_⟩
      have hi : (b.repr w i).natDegree ≤ E + 1 := (natDegree_repr_le_deg b w i).trans hw.2
      have hc : (b.repr w i).coeff (E + 1) = 0 := congrFun h i
      rcases Nat.lt_or_ge (b.repr w i).natDegree (E + 1) with hlt | hge
      · exact Nat.le_of_lt_succ hlt
      · have heq : (b.repr w i).natDegree = E + 1 := le_antisymm hi hge
        have : b.repr w i = 0 := by
          by_contra hne
          rw [← heq, coeff_natDegree, leadingCoeff_eq_zero] at hc
          exact hne hc
        rw [this, natDegree_zero]
        exact Nat.zero_le _
    · intro h
      ext i
      exact coeff_eq_zero_of_natDegree_lt
        (((natDegree_repr_le_deg b w i).trans h.2).trans_lt (Nat.lt_succ_self E))
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker,
    (Submodule.comapSubtypeEquivOfLe (degFiltration_mono b M (Nat.le_succ E))).finrank_eq]
    at this
  omega

lemma exists_leadingCoeffs_ne_bot (hM : M ≠ ⊥) : ∃ d, leadingCoeffs b M d ≠ ⊥ := by
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  have hrepr : b.repr m ≠ 0 := fun h ↦ hm0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨i₀, hi₀⟩ : ∃ i, b.repr m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hrepr (Finsupp.ext h)
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hi⟩ : ∃ i, (b.repr m i).coeff (deg b m) ≠ 0 := by
    rcases Nat.eq_zero_or_pos (deg b m) with h0 | hpos
    · refine ⟨i₀, ?_⟩
      have hle : (b.repr m i₀).natDegree = 0 :=
        Nat.le_zero.mp ((natDegree_repr_le_deg b m i₀).trans h0.le)
      rw [h0, ← hle, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hi₀
    · obtain ⟨i, hi⟩ := exists_natDegree_repr_eq b m
      refine ⟨i, ?_⟩
      have hne : b.repr m i ≠ 0 := fun h ↦ by
        rw [h, natDegree_zero] at hi
        omega
      rw [← hi, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hne
  refine ⟨deg b m, fun h ↦ hi ?_⟩
  have hmem : coeffMap b (deg b m) m ∈ leadingCoeffs b M (deg b m) :=
    ⟨m, (mem_degFiltration b M).mpr ⟨hm, le_rfl⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  exact congrFun hmem i

/-- The dimensions of the levels of a nonzero `M` grow linearly: `dim_k M_{≤ E} = c + s E`
for large `E`, with slope `s ≥ 1`. -/
lemma exists_finrank_degFiltration_eq (hM : M ≠ ⊥) : ∃ s E₀, 1 ≤ s ∧ ∀ E, E₀ ≤ E →
    finrank k (degFiltration b M E) = finrank k (degFiltration b M E₀) + s * (E - E₀) := by
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    (⟨leadingCoeffs b M, leadingCoeffs_mono b M⟩ : ℕ →o Submodule k (I → k))
  obtain ⟨d, hd⟩ := exists_leadingCoeffs_ne_bot b M hM
  refine ⟨finrank k (leadingCoeffs b M (max n d)), max n d, ?_, fun E hE ↦ ?_⟩
  · refine Nat.one_le_iff_ne_zero.mpr fun h ↦ hd ?_
    rw [Submodule.finrank_eq_zero] at h
    exact eq_bot_iff.mpr (h ▸ leadingCoeffs_mono b M (le_max_right n d))
  · induction E, hE using Nat.le_induction with
    | base => simp
    | succ E hE ih =>
      have hlead : leadingCoeffs b M (E + 1) = leadingCoeffs b M (max n d) :=
        (hn (E + 1) (by omega)).symm.trans (hn (max n d) (le_max_left n d))
      rw [finrank_degFiltration_succ, ih, hlead, show E + 1 - max n d = (E - max n d) + 1 by omega]
      ring

end Levels

section Frobenius

variable {k : Type*} [Field k] {p : ℕ} {W : Type*} [AddCommGroup W] [Module k W]
  (F : W →+ W) (hF : ∀ (c : k) (w : W), F (c • w) = c ^ p • F w)

include hF in
/-- A `p`-semilinear map sends a finite-dimensional subspace into the span of the images of a
basis, so the span of its image has dimension at most that of the subspace. -/
lemma span_image_le (X : Submodule k W) [FiniteDimensional k X] :
    Submodule.span k (F '' X) ≤
      Submodule.span k (Set.range fun i ↦ F (Module.finBasis k X i : W)) := by
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  have hsum := congrArg Subtype.val ((Module.finBasis k X).sum_repr ⟨w, hw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [hF]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

include hF in
lemma finiteDimensional_span_image (X : Submodule k W) [FiniteDimensional k X] :
    FiniteDimensional k (Submodule.span k (F '' X)) :=
  have := FiniteDimensional.span_of_finite k
    (Set.finite_range fun i ↦ F (Module.finBasis k X i : W))
  Submodule.finiteDimensional_of_le (span_image_le F hF X)

include hF in
lemma finrank_span_image_le (X : Submodule k W) [FiniteDimensional k X] :
    finrank k (Submodule.span k (F '' X)) ≤ finrank k X := by
  have := FiniteDimensional.span_of_finite k
    (Set.finite_range fun i ↦ F (Module.finBasis k X i : W))
  have := Submodule.finrank_mono (span_image_le F hF X)
  refine this.trans ((finrank_range_le_card (R := k) _).trans ?_)
  rw [Fintype.card_fin]

variable [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

include hF in
lemma linearIndependent_comp {ι : Type*} [Finite ι] (hFinj : Function.Injective F)
    {v : ι → W} (hv : LinearIndependent k v) : LinearIndependent k (F ∘ v) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg i
  set r := fun i ↦ (frobeniusEquiv k p).symm (g i)
  have hr : ∀ i, r i ^ p = g i := fun i ↦ frobeniusEquiv_symm_pow_p k p (g i)
  have h0 : F (∑ i, r i • v i) = 0 := by
    rw [map_sum]
    simp only [hF, hr]
    exact hg
  have := hv r (hFinj (h0.trans F.map_zero.symm)) i
  rw [← hr i, this, zero_pow hp.out.ne_zero]

include hF in
lemma finrank_le_finrank_span_image (hFinj : Function.Injective F)
    (Y : Submodule k W) [FiniteDimensional k Y] :
    finrank k Y ≤ finrank k (Submodule.span k (F '' Y)) := by
  have := finiteDimensional_span_image F hF Y
  let e := Module.finBasis k Y
  have hv : LinearIndependent k fun i ↦ (e i : W) :=
    e.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
  have hFv := linearIndependent_comp F hF hFinj hv
  have hle : Submodule.span k (Set.range (F ∘ fun i ↦ (e i : W))) ≤
      Submodule.span k (F '' Y) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨e i, (e i).2, rfl⟩)
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hFv, Fintype.card_fin] at this
  exact this

end Frobenius

section Counting

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]
  [Infinite k] {W : Type*} [AddCommGroup W] [Module k[X] W] [Module k W]
  [IsScalarTower k k[X] W] {I : Type*} [Fintype I] (b : Basis I k[X] W)
  (F : W →+ W) (hF : ∀ (c : k) (w : W), F (c • w) = c ^ p • F w)
  (hFinj : Function.Injective F) (c₀ c₂ : ℕ) (hlow : ∀ w, p * deg b w ≤ deg b (F w) + c₀)
  (hup : ∀ w, deg b (F w) ≤ p * deg b w + c₂)

omit [CharP k p] [PerfectRing k p] [Infinite k] [Module k W] [IsScalarTower k k[X] W] in
include hlow in
/-- If `F x - x` has degree `≤ E`, then `x` has degree `≤ max c₀ ((E + c₀) / p)`. -/
lemma deg_le_of_deg_sub_le {x : W} {E : ℕ} (h : deg b (F x - x) ≤ E) :
    deg b x ≤ max c₀ ((E + c₀) / p) := by
  rcases le_or_gt (deg b x) c₀ with hx | hx
  · exact le_max_of_le_left hx
  · have hp2 := hp.out.two_le
    have hFx : deg b x < deg b (F x) := by
      have := hlow x
      nlinarith
    have : Nonempty I := by
      by_contra hI
      rw [not_nonempty_iff] at hI
      have : deg b x = 0 := by simp [deg]
      omega
    have h1 := (le_deg_sub b hFx).trans h
    refine le_max_of_le_right ((Nat.le_div_iff_mul_le hp.out.pos).mpr ?_)
    have := hlow x
    nlinarith

include hF hFinj hlow hup in
/-- Serre's degree count: let `W` be a free `k[T]`-module of finite rank (`k` infinite and
perfect of characteristic `p`) with an injective `p`-semilinear map `F` that multiplies degrees
by `p` up to bounded errors, and `M ≠ 0` a `k[T]`-submodule stable under `F`. Then `M` is not
covered by finitely many translates `f + ℘(M)` of the image of `℘ = F - 1`: the cokernel of `℘`
on `M` is infinite. -/
theorem exists_mem_forall_ne_add_sub (M : Submodule k[X] W) (hM : M ≠ ⊥)
    (hFM : ∀ m ∈ M, F m ∈ M) (S₀ : Finset W) :
    ∃ m ∈ M, ∀ f ∈ S₀, ∀ x ∈ M, m ≠ f + (F x - x) := by
  classical
  obtain ⟨s, E₀, hs, hlin⟩ := exists_finrank_degFiltration_eq b M hM
  set c₃ := S₀.sup (deg b)
  set L := E₀ + 2 * c₀ + c₃ + 2 with hL
  set D' := p * L + c₂ + c₀ with hD'
  set D := p * (p * L + c₂) with hD
  have hp2 := hp.out.two_le
  have hpL : 2 * L ≤ p * L := Nat.mul_le_mul_right L hp2
  have hLD' : L ≤ D' := by omega
  have hD'D : D' ≤ D := by
    have : 2 * (p * L + c₂) ≤ p * (p * L + c₂) := Nat.mul_le_mul_right _ hp2
    omega
  have hE₀L : E₀ ≤ L := by omega
  have hc₃L : c₃ ≤ L := by omega
  have key : 2 * D' + 2 ≤ D + L := by
    have h1 : 2 * (p * L) + 2 * c₂ ≤ p * (p * L) + p * c₂ := by
      have : (p - 1) * (p - 1) * L + (p - 2) * c₂ + 2 * (p * L) + 2 * c₂ =
          p * (p * L) + p * c₂ + L := by
        zify [show 1 ≤ p by omega, show 2 ≤ p from hp2]
        ring
      have h0 : L ≤ (p - 1) * (p - 1) * L := by
        have : 1 ≤ (p - 1) * (p - 1) := Nat.one_le_iff_ne_zero.mpr (by
          have : p - 1 ≠ 0 := by omega
          positivity)
        nlinarith
      omega
    have : D = p * (p * L) + p * c₂ := by rw [hD]; ring
    omega
  -- the dimension count
  have hfD := hlin D (by omega)
  have hfD' := hlin D' (by omega)
  have hfL := hlin L hE₀L
  set Xs := degFiltration b M D'
  set Ys := degFiltration b M L
  set Sp := Submodule.span k (F '' Xs)
  set S := Sp ⊔ Xs
  have : FiniteDimensional k Sp := finiteDimensional_span_image F hF Xs
  have hSpX : finrank k Sp ≤ finrank k Xs := finrank_span_image_le F hF Xs
  have hFY : F '' Ys ⊆ Sp ⊓ Xs := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨Submodule.subset_span ⟨y, degFiltration_mono b M hLD' hy, rfl⟩, hFM y hy.1, ?_⟩
    exact (hup y).trans (by have := Nat.mul_le_mul_left p hy.2; omega)
  have hY : finrank k Ys ≤ finrank k ↥(Sp ⊓ Xs) := by
    have := finiteDimensional_span_image F hF Ys
    calc finrank k Ys ≤ finrank k (Submodule.span k (F '' Ys)) :=
          finrank_le_finrank_span_image F hF hFinj Ys
      _ ≤ finrank k ↥(Sp ⊓ Xs) := Submodule.finrank_mono (Submodule.span_le.mpr hFY)
  have hS : finrank k S + 2 ≤ finrank k (degFiltration b M D) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Sp Xs
    have h2 : s * (D - E₀) + s * (L - E₀) ≥ 2 * (s * (D' - E₀)) + 2 := by
      have e1 : D - E₀ = (D - D') + (D' - E₀) := by omega
      have e2 : D - D' + (L - E₀) ≥ (D' - E₀) + 2 := by omega
      rw [e1]
      nlinarith
    change finrank k ↥(Sp ⊔ Xs) + 2 ≤ _
    omega
  -- the covering argument
  by_contra hcon
  push Not at hcon
  let P : S₀ → Submodule k (degFiltration b M D) := fun f ↦
    ((k ∙ (f : W)) ⊔ S).comap (degFiltration b M D).subtype
  have hP : ∀ f, P f ≠ ⊤ := by
    intro f hf
    have hle : degFiltration b M D ≤ (k ∙ (f : W)) ⊔ S := fun w hw ↦ by
      have : (⟨w, hw⟩ : degFiltration b M D) ∈ P f := hf ▸ Submodule.mem_top
      exact this
    have := Submodule.finrank_mono hle
    have := Submodule.finrank_add_le_finrank_add_finrank (k ∙ (f : W)) S
    have : finrank k (k ∙ (f : W)) ≤ 1 := by
      simpa using finrank_span_le_card (R := k) ({(f : W)} : Set W)
    omega
  obtain ⟨y, hy⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  obtain ⟨f, hf, x, hx, hyx⟩ := hcon y y.2.1
  apply hy ⟨f, hf⟩
  have hdeg : deg b (F x - x) ≤ D := by
    have : F x - x = y - f := by rw [hyx]; abel
    rw [this]
    exact (deg_sub_le b _ _).trans (max_le y.2.2 ((Finset.le_sup hf).trans (by omega)))
  have hxD' : deg b x ≤ D' := by
    refine (deg_le_of_deg_sub_le b F c₀ hlow hdeg).trans (max_le (by omega) ?_)
    refine Nat.div_le_of_le_mul ?_
    have : c₀ ≤ p * c₀ := Nat.le_mul_of_pos_left c₀ hp.out.pos
    rw [hD', hD]
    nlinarith
  have hxX : x ∈ Xs := ⟨hx, hxD'⟩
  change (y : W) ∈ (k ∙ (f : W)) ⊔ S
  rw [hyx]
  exact add_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    (Submodule.mem_sup_right (sub_mem (Submodule.mem_sup_left (Submodule.subset_span
      ⟨x, hxX, rfl⟩)) (Submodule.mem_sup_right hxX)))

end Counting

end SerrePKernel

end SGA.SGA1.ExposeXIII
