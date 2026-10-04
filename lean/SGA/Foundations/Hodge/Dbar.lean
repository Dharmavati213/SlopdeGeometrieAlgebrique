/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.FormType

/-!
# The operators `∂` and `∂̄` on complex-valued forms over a complex normed space

Let `E` be a complex normed space and `ω : E → E [⋀^Fin n]→L[ℝ] ℂ` a complex-valued differential
form on `E` (viewed as a real normed space). mathlib's exterior derivative is
`dω(x; v₀, …, vₙ) = Σᵢ (-1)ⁱ Dω(x)(vᵢ)(v₀, …, v̂ᵢ, …, vₙ)` (`extDeriv`). Splitting the real
derivative `Dω(x)` into its complex linear and complex antilinear parts,

  `D'L = ½ (L - i L ∘ i)`, `D''L = ½ (L + i L ∘ i)` (`Hodge.partCLM (-1)`, `Hodge.partCLM 1`),

gives the operators `∂ω` (`Hodge.delDeriv`) and `∂̄ω` (`Hodge.dbarDeriv`), defined by the same
formula with `D'`, resp. `D''`, in place of `D`. In coordinates `∂̄ (f dz_I ∧ dz̄_J) =
Σⱼ ∂f/∂z̄ⱼ dz̄ⱼ ∧ dz_I ∧ dz̄_J`, i.e. these are the usual `∂` and `∂̄`, for forms of every type.

Main results:
* `Hodge.extDeriv_eq_delDeriv_add_dbarDeriv`: `d = ∂ + ∂̄`;
* `Hodge.dbarDeriv_dbarDeriv`, `Hodge.delDeriv_delDeriv`, `Hodge.delDeriv_dbarDeriv_add`:
  `∂̄² = 0`, `∂² = 0`, `∂∂̄ + ∂̄∂ = 0` for `C²` forms (all from the symmetry of second
  derivatives, `Hodge.partDeriv_partDeriv_add_partDeriv_partDeriv`);
* `Hodge.isOfType_dbarDeriv`, `Hodge.isOfType_delDeriv`: `∂̄` maps forms of type `(p, q)` to type
  `(p, q + 1)`, `∂` to type `(p + 1, q)`;
* `Hodge.partDeriv_pullbackForm`: `∂` and `∂̄` commute with pullback along holomorphic maps;
* `Hodge.dbarDeriv_conjForm`: `∂̄ ω̄ = conj (∂ ω)`.

Reference: D. Huybrechts, *Complex geometry*, §1.3; R. O. Wells, *Differential analysis on complex
manifolds*, Ch. II.3.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap Filter Topology

namespace Hodge

section Parts

variable {E V W F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

variable (E) in
/-- Multiplication by `i` on a complex normed space, as a real continuous linear map. -/
def mulI : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp]
lemma mulI_apply (v : E) : mulI E v = Complex.I • v :=
  rfl

variable (E V) in
/-- `partCLM E V ε L = ½ (L + ε i (L ∘ i))` for a real linear map `L : E → V` between complex
spaces. For `ε = 1` this is the complex antilinear part of `L`, for `ε = -1` its complex linear
part (`Hodge.partCLM_one_apply_smul`, `Hodge.partCLM_neg_one_apply_smul`). -/
def partCLM (ε : ℂ) : (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.id ℝ (E →L[ℝ] V) +
    (ε * Complex.I) • ContinuousLinearMap.precomp V (mulI E))

lemma partCLM_apply (ε : ℂ) (L : E →L[ℝ] V) (v : E) :
    partCLM E V ε L v = (2⁻¹ : ℂ) • (L v + (ε * Complex.I) • L (Complex.I • v)) := by
  simp [partCLM]

lemma partCLM_smul (ε c : ℂ) (L : E →L[ℝ] V) : partCLM E V ε (c • L) = c • partCLM E V ε L := by
  ext v
  simp only [partCLM_apply, FunLike.coe_smul, Pi.smul_apply]
  module

/-- `partCLM ε L (i v) = -ε i · partCLM ε L v` when `ε² = 1`. -/
lemma partCLM_apply_I_smul {ε : ℂ} (hε : ε ^ 2 = 1) (L : E →L[ℝ] V) (v : E) :
    partCLM E V ε L (Complex.I • v) = (-(ε * Complex.I)) • partCLM E V ε L v := by
  rw [partCLM_apply, partCLM_apply, smul_smul Complex.I Complex.I v, Complex.I_mul_I, neg_one_smul,
    map_neg]
  have h1 : (ε * Complex.I) * (ε * Complex.I) = -1 := by
    linear_combination (Complex.I ^ 2) * hε + Complex.I_sq
  linear_combination (norm := module) ((2⁻¹ : ℂ) * h1) • L (Complex.I • v)

/-- A real linear map is the sum of its complex linear and complex antilinear parts. -/
lemma partCLM_one_add_partCLM_neg_one (L : E →L[ℝ] V) :
    partCLM E V 1 L + partCLM E V (-1) L = L := by
  ext v
  rw [_root_.add_apply, partCLM_apply, partCLM_apply]
  module

/-- `partCLM` commutes with precomposition by a complex linear map. -/
lemma partCLM_comp (ε : ℂ) (L : E →L[ℝ] V) (g : F →L[ℂ] E) :
    partCLM F V ε (L.comp (g.restrictScalars ℝ)) =
      (partCLM E V ε L).comp (g.restrictScalars ℝ) := by
  ext v
  simp [partCLM_apply, map_smul]

/-- `partCLM` commutes with postcomposition by a complex linear map. -/
lemma partCLM_postcomp (ε : ℂ) (A : V →L[ℝ] W) (hA : ∀ (c : ℂ) (x : V), A (c • x) = c • A x)
    (L : E →L[ℝ] V) : partCLM E W ε (A.comp L) = A.comp (partCLM E V ε L) := by
  ext v
  simp [partCLM_apply, hA]

/-- `c • x = Re c • x + Im c • (i • x)` (real scalars on the right). -/
lemma complex_smul_eq_re_smul_add_im_smul (c : ℂ) (x : V) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]

/-- A real linear map commuting with `i` commutes with every complex scalar. -/
lemma map_complex_smul_of_map_I_smul (A : V →L[ℝ] W)
    (hA : ∀ x : V, A (Complex.I • x) = Complex.I • A x) (c : ℂ) (x : V) :
    A (c • x) = c • A x := by
  rw [complex_smul_eq_re_smul_add_im_smul c x, complex_smul_eq_re_smul_add_im_smul c (A x),
    map_add, map_smul, map_smul, hA]

/-- The antilinear part is antilinear: `D''L (c v) = c̄ · D''L v`. -/
lemma partCLM_one_apply_smul (L : E →L[ℝ] V) (c : ℂ) (v : E) :
    partCLM E V 1 L (c • v) = conj c • partCLM E V 1 L v := by
  rw [complex_smul_eq_re_smul_add_im_smul c v, map_add, map_smul, map_smul,
    partCLM_apply_I_smul (by norm_num), one_mul, ← Complex.coe_smul, ← Complex.coe_smul,
    smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

/-- The linear part is linear: `D'L (c v) = c · D'L v`. -/
lemma partCLM_neg_one_apply_smul (L : E →L[ℝ] V) (c : ℂ) (v : E) :
    partCLM E V (-1) L (c • v) = c • partCLM E V (-1) L v := by
  rw [complex_smul_eq_re_smul_add_im_smul c v, map_add, map_smul, map_smul,
    partCLM_apply_I_smul (by norm_num), neg_one_mul, neg_neg, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

end Parts

section Deriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {n p q : ℕ}

/-- The derivative `Σᵢ (-1)ⁱ (partCLM ε (Dη x)) (vᵢ) (v̂ᵢ)` of a complex-valued form. For `ε = 1`
it is `∂̄` (`Hodge.dbarDeriv`), for `ε = -1` it is `∂` (`Hodge.delDeriv`). -/
def partDeriv (ε : ℂ) (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  alternatizeUncurryFin (partCLM E _ ε (fderiv ℝ η x))

/-- The operator `∂̄` on complex-valued forms on a complex normed space. -/
def dbarDeriv (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  partDeriv 1 η x

/-- The operator `∂` on complex-valued forms on a complex normed space. -/
def delDeriv (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  partDeriv (-1) η x

lemma dbarDeriv_def (η : E → E [⋀^Fin n]→L[ℝ] ℂ) : dbarDeriv η = partDeriv 1 η :=
  rfl

lemma delDeriv_def (η : E → E [⋀^Fin n]→L[ℝ] ℂ) : delDeriv η = partDeriv (-1) η :=
  rfl

/-- `d = ∂ + ∂̄`. -/
theorem extDeriv_eq_delDeriv_add_dbarDeriv (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) :
    extDeriv η x = delDeriv η x + dbarDeriv η x := by
  rw [delDeriv, dbarDeriv, partDeriv, partDeriv, ← alternatizeUncurryFin_add]
  exact congrArg alternatizeUncurryFin
    ((add_comm _ _).trans (partCLM_one_add_partCLM_neg_one (fderiv ℝ η x))).symm

lemma partDeriv_apply (ε : ℂ) (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) (v : Fin (n + 1) → E) :
    partDeriv ε η x v =
      ∑ i : Fin (n + 1), (-1) ^ i.val • partCLM E _ ε (fderiv ℝ η x) (v i) (i.removeNth v) :=
  alternatizeUncurryFin_apply _ _

lemma partDeriv_eq_comp (ε : ℂ) (η : E → E [⋀^Fin n]→L[ℝ] ℂ) :
    partDeriv ε η = fun x ↦
      (alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ ε) (fderiv ℝ η x) := by
  ext1 x
  simp [partDeriv, alternatizeUncurryFinCLM_apply]

/-- `alternatizeUncurryFin` commutes with complex scalars. -/
lemma alternatizeUncurryFinCLM_complex_smul (c : ℂ) (f : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ) :
    alternatizeUncurryFinCLM ℝ E ℂ (c • f) = c • alternatizeUncurryFinCLM ℝ E ℂ f := by
  simp [alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_smul]

/-- The scalar identity behind `Hodge.partDeriv_partDeriv_add_partDeriv_partDeriv`, stated in an
abstract complex vector space so that the kernel checks it quickly. -/
private lemma sym_aux {V : Type*} [AddCommGroup V] [Module ℂ V] (ε δ : ℂ) (a b c d : V) :
    (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • (a + (ε * Complex.I) • b) +
        (δ * Complex.I) • (2⁻¹ : ℂ) • (c + (ε * Complex.I) • d)) +
      (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • (a + (δ * Complex.I) • b) +
        (ε * Complex.I) • (2⁻¹ : ℂ) • (c + (δ * Complex.I) • d)) =
    (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • (a + (ε * Complex.I) • c) +
        (δ * Complex.I) • (2⁻¹ : ℂ) • (b + (ε * Complex.I) • d)) +
      (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • (a + (δ * Complex.I) • c) +
        (ε * Complex.I) • (2⁻¹ : ℂ) • (b + (δ * Complex.I) • d)) := by
  module

/-- **Second derivatives**: `P_ε P_δ η + P_δ P_ε η = 0` for `C²` forms. With `ε, δ ∈ {1, -1}` this
gives `∂̄² = 0`, `∂² = 0` and `∂∂̄ + ∂̄∂ = 0`. -/
theorem partDeriv_partDeriv_add_partDeriv_partDeriv (ε δ : ℂ) {η : E → E [⋀^Fin n]→L[ℝ] ℂ}
    {x : E} (hη : ContDiffAt ℝ 2 η x) :
    partDeriv ε (partDeriv δ η) x + partDeriv δ (partDeriv ε η) x = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ η) x :=
    (hη.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  set H := fderiv ℝ (fderiv ℝ η) x with hH
  have hsymm : ∀ v w, H v w = H w v := fun v w ↦
    (hη.isSymmSndFDerivAt (by simp)) v w
  -- the derivative of `partDeriv δ η` at `x`
  have key (δ : ℂ) : fderiv ℝ (partDeriv δ η) x =
      (alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ δ) ∘L H := by
    rw [partDeriv_eq_comp]
    exact ((alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ δ).hasFDerivAt.comp x
      hd.hasFDerivAt).fderiv
  have hG (δ : ℂ) : ∀ (c : ℂ) (y : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ),
      (alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ δ) (c • y) =
        c • (alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ δ) y := by
    intro c y
    simp only [ContinuousLinearMap.comp_apply, partCLM_smul, alternatizeUncurryFinCLM_complex_smul]
  have step (ε δ : ℂ) : partDeriv ε (partDeriv δ η) x =
      alternatizeUncurryFin (alternatizeUncurryFinCLM ℝ E ℂ ∘L
        (partCLM E _ δ ∘L partCLM E _ ε H)) := by
    rw [partDeriv, key, partCLM_postcomp ε _ (hG δ), ContinuousLinearMap.comp_assoc]
  rw [step, step, ← alternatizeUncurryFin_add, ← ContinuousLinearMap.comp_add]
  apply alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
  intro v w
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, partCLM_apply, _root_.smul_apply]
  rw [hsymm w v, hsymm (Complex.I • w) v, hsymm w (Complex.I • v),
    hsymm (Complex.I • w) (Complex.I • v)]
  exact sym_aux ε δ _ _ _ _

private lemma eq_zero_of_add_self {V : Type*} [AddCommGroup V] [Module ℂ V] {a : V}
    (h : a + a = 0) : a = 0 := by
  rw [← two_smul ℂ a] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-- `∂̄² = 0`. -/
theorem dbarDeriv_dbarDeriv {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hη : ContDiffAt ℝ 2 η x) :
    dbarDeriv (dbarDeriv η) x = 0 :=
  eq_zero_of_add_self (partDeriv_partDeriv_add_partDeriv_partDeriv 1 1 hη)

/-- `∂² = 0`. -/
theorem delDeriv_delDeriv {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hη : ContDiffAt ℝ 2 η x) :
    delDeriv (delDeriv η) x = 0 :=
  eq_zero_of_add_self (partDeriv_partDeriv_add_partDeriv_partDeriv (-1) (-1) hη)

/-- `∂∂̄ + ∂̄∂ = 0`. -/
theorem delDeriv_dbarDeriv_add {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hη : ContDiffAt ℝ 2 η x) :
    delDeriv (dbarDeriv η) x + dbarDeriv (delDeriv η) x = 0 :=
  partDeriv_partDeriv_add_partDeriv_partDeriv (-1) 1 hη

/-- If `η` takes values of type `(p, q)` near `x`, so does every directional derivative of `η`
at `x`. -/
lemma isOfType_fderiv_apply {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (h : ∀ᶠ y in 𝓝 x, IsOfType p q (η y)) (u : E) : IsOfType p q (fderiv ℝ η x u) := by
  intro c v
  by_cases hd : DifferentiableAt ℝ η x
  · let φ : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousAlternatingMap.apply ℝ E ℂ (c • v) -
        (c ^ p * conj c ^ q) • ContinuousAlternatingMap.apply ℝ E ℂ v
    have h0 : (φ ∘ η) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [h] with y hy
      simp [φ, hy c v]
    have h1 : fderiv ℝ (φ ∘ η) x = φ.comp (fderiv ℝ η x) :=
      (φ.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
    have h2 : φ (fderiv ℝ η x u) = 0 := by
      rw [← ContinuousLinearMap.comp_apply, ← h1, h0.fderiv_eq]
      simp
    simpa [φ, sub_eq_zero] using h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- If `L : E → Alt` takes values of type `(p, q)`, so does `partCLM ε L`. -/
lemma isOfType_partCLM_apply (ε : ℂ) (L : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ)
    (hL : ∀ u, IsOfType p q (L u)) (u : E) : IsOfType p q (partCLM E _ ε L u) := by
  rw [partCLM_apply]
  exact ((hL u).add ((hL _).smul _)).smul _

/-- `∂̄` maps forms of type `(p, q)` to forms of type `(p, q + 1)`. -/
theorem isOfType_dbarDeriv {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (h : ∀ᶠ y in 𝓝 x, IsOfType p q (η y)) : IsOfType p (q + 1) (dbarDeriv η x) := by
  intro c v
  have hP := isOfType_partCLM_apply 1 (fderiv ℝ η x) (isOfType_fderiv_apply h)
  rw [dbarDeriv, partDeriv_apply, partDeriv_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hv : (c • v) i = c • v i := rfl
  have hr : i.removeNth (c • v) = c • i.removeNth v := rfl
  rw [hv, hr, partCLM_one_apply_smul, ContinuousAlternatingMap.smul_apply, hP, smul_eq_mul]
  simp only [zsmul_eq_mul]
  ring

/-- `∂` maps forms of type `(p, q)` to forms of type `(p + 1, q)`. -/
theorem isOfType_delDeriv {η : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (h : ∀ᶠ y in 𝓝 x, IsOfType p q (η y)) : IsOfType (p + 1) q (delDeriv η x) := by
  intro c v
  have hP := isOfType_partCLM_apply (-1) (fderiv ℝ η x) (isOfType_fderiv_apply h)
  rw [delDeriv, partDeriv_apply, partDeriv_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hv : (c • v) i = c • v i := rfl
  have hr : i.removeNth (c • v) = c • i.removeNth v := rfl
  rw [hv, hr, partCLM_neg_one_apply_smul, ContinuousAlternatingMap.smul_apply, hP, smul_eq_mul]
  simp only [zsmul_eq_mul]
  ring

end Deriv

section Pullback

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {n : ℕ}

/-- For `f` complex `C²` at `x`, the real second derivative of `f` at `x` is complex linear in its
first argument. -/
lemma fderiv_fderiv_complex_smul {f : E → F} {x : E} (hf : ContDiffAt ℂ 2 f x) (c : ℂ) (v : E) :
    fderiv ℝ (fderiv ℝ f) x (c • v) = c • fderiv ℝ (fderiv ℝ f) x v := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have h1 : fderiv ℝ f =ᶠ[𝓝 x] fun y ↦ (fderiv ℂ f y).restrictScalars ℝ := by
    filter_upwards [hev] with y hy
    exact hy.fderiv_restrictScalars ℝ
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let R := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℂ
  have h2 : HasFDerivAt (fun y ↦ R (fderiv ℂ f y))
      ((R ∘L fderiv ℂ (fderiv ℂ f) x).restrictScalars ℝ) x :=
    (R.hasFDerivAt.comp x hd.hasFDerivAt).restrictScalars ℝ
  rw [h1.fderiv_eq]
  change fderiv ℝ (fun y ↦ R (fderiv ℂ f y)) x (c • v) = c • fderiv ℝ (fun y ↦ R (fderiv ℂ f y)) x v
  rw [h2.fderiv]
  simp

/-- The pullback `f^* η` of a form along `f`, `(f^* η)(y) = η (f y) ∘ (Df(y), …, Df(y))`. -/
def pullbackForm (f : E → F) (η : F → F [⋀^Fin n]→L[ℝ] ℂ) (y : E) : E [⋀^Fin n]→L[ℝ] ℂ :=
  (η (f y)).compContinuousLinearMap (fderiv ℝ f y)

lemma compContinuousLinearMap_complex_smul (g : E →L[ℝ] F) (c : ℂ) (α : F [⋀^Fin n]→L[ℝ] ℂ) :
    (c • α).compContinuousLinearMap g = c • α.compContinuousLinearMap g := by
  ext v
  simp

/-- **Naturality**: `∂` and `∂̄` (and `partDeriv ε` for any `ε`) commute with pullback along maps
that are complex `C²` (in particular holomorphic). -/
theorem partDeriv_pullbackForm (ε : ℂ) {η : F → F [⋀^Fin n]→L[ℝ] ℂ} {f : E → F} {x : E}
    (hη : DifferentiableAt ℝ η (f x)) (hf : ContDiffAt ℂ 2 f x) :
    partDeriv ε (pullbackForm f η) x =
      (partDeriv ε η (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  have hfR : ContDiffAt ℝ 2 f x := hf.restrict_scalars ℝ
  have hdf : DifferentiableAt ℝ f x := hfR.differentiableAt (by norm_num)
  have hd2f : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfR.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDf : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ :=
    (hf.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ
  set h := fderiv ℝ (fderiv ℝ f) x with hh
  have hsymm : ∀ v w, h v w = h w v := fun v w ↦ hfR.isSymmSndFDerivAt (by simp) v w
  have hsymmI : ∀ v w, (h ∘L mulI E) v w = (h ∘L mulI E) w v := by
    intro v w
    simp only [ContinuousLinearMap.comp_apply, mulI_apply, hh, fderiv_fderiv_complex_smul hf,
      _root_.smul_apply]
    rw [← hh, hsymm v w]
  set A := (η (f x)).fderivCompContinuousLinearMap (fderiv ℝ f x)
  have h2 : alternatizeUncurryFin (partCLM E _ ε (A ∘L h)) = 0 := by
    have : partCLM E _ ε (A ∘L h) =
        (2⁻¹ : ℂ) • (A ∘L h + (ε * Complex.I) • (A ∘L (h ∘L mulI E))) := by
      ext v
      simp [partCLM_apply]
    rw [this, alternatizeUncurryFin_smul, alternatizeUncurryFin_add, alternatizeUncurryFin_smul,
      alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero _ _ hsymm,
      alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero _ _ hsymmI]
    simp
  have hC : ∀ (c : ℂ) (α : F [⋀^Fin n]→L[ℝ] ℂ),
      compContinuousLinearMapCLM (fderiv ℝ f x) (c • α) =
        c • compContinuousLinearMapCLM (fderiv ℝ f x) α := fun c α ↦
    compContinuousLinearMap_complex_smul _ c α
  have hpb : pullbackForm f η = fun y ↦ ((η ∘ f) y).compContinuousLinearMap (fderiv ℝ f y) := rfl
  rw [partDeriv, hpb,
    fderiv_continuousAlternatingMapCompContinuousLinearMap (hη.comp x hdf) hd2f, map_add,
    alternatizeUncurryFin_add, ← hh, Function.comp_apply, h2, add_zero, fderiv_comp x hη hdf,
    partCLM_postcomp ε _ hC, hDf, partCLM_comp]
  ext v
  simp +unfoldPartialApp [alternatizeUncurryFin_apply, partDeriv, Fin.removeNth, Function.comp_def]

end Pullback

section Conj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

variable (E n) in
/-- Complex conjugation of forms, as a real continuous linear equivalence (an involution). -/
def conjFormCLE : (E [⋀^Fin n]→L[ℝ] ℂ) ≃L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toLinearMap := (conjFormCLM E n).toLinearMap
  invFun := conjFormCLM E n
  left_inv α := by simp
  right_inv α := by simp
  continuous_toFun := (conjFormCLM E n).continuous
  continuous_invFun := (conjFormCLM E n).continuous

@[simp]
lemma conjFormCLE_apply (α : E [⋀^Fin n]→L[ℝ] ℂ) : conjFormCLE E n α = conjForm α := by
  simp [conjFormCLE]

/-- `∂̄ η̄ = conj (∂ η)`. -/
theorem dbarDeriv_conjForm (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) :
    dbarDeriv (fun y ↦ conjForm (η y)) x = conjForm (delDeriv η x) := by
  have : (fun y ↦ conjForm (η y)) = conjFormCLE E n ∘ η := by
    ext1 y
    simp
  rw [dbarDeriv, delDeriv, partDeriv, partDeriv, this, ContinuousLinearEquiv.comp_fderiv]
  ext v
  simp only [alternatizeUncurryFin_apply, partCLM_apply, conjForm_apply, _root_.map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Complex.conj_I, map_ofNat]

/-- `∂ η̄ = conj (∂̄ η)`. -/
theorem delDeriv_conjForm (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) :
    delDeriv (fun y ↦ conjForm (η y)) x = conjForm (dbarDeriv η x) := by
  have h := dbarDeriv_conjForm (fun y ↦ conjForm (η y)) x
  simp only [conjForm_conjForm] at h
  exact ((congrArg conjForm h).trans (conjForm_conjForm _)).symm

end Conj

end Hodge
