/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Monic

/-!
# Simple roots depend continuously on the coefficients

This is the analytic input of XII.3.1 (iii) and XII.3.3 a): the implicit function theorem shows
that a simple root of a monic polynomial over a complete nontrivially normed field (for instance
`ℂ`) is locally a continuous function of the coefficients.
-/

noncomputable section

namespace SGA.SGA1.ExposeXII

open Topology Set Filter Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

section Implicit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The implicit function theorem for one scalar equation `F (c, x) = 0` in one scalar unknown
`x`, in the form: near a point where `∂F/∂x ≠ 0`, the solutions are the graph of a continuous
function. -/
theorem exists_continuousOn_implicit {F : E × 𝕜 → 𝕜} {F' : E × 𝕜 →L[𝕜] 𝕜} {u : E × 𝕜}
    (hF : HasStrictFDerivAt F F' u) (hu : F u = 0) (h : F' (0, 1) ≠ 0) :
    ∃ U V : Set _, IsOpen U ∧ IsOpen V ∧ u.1 ∈ U ∧ u.2 ∈ V ∧ ∃ r : E → 𝕜,
      ContinuousOn r U ∧ MapsTo r U V ∧ ∀ c ∈ U, ∀ x ∈ V, F (c, x) = 0 ↔ r c = x := by
  set a := F' (0, 1)
  have hsplit (v : E × 𝕜) : F' v = F' (v.1, 0) + v.2 * a := by
    have : v = (v.1, 0) + v.2 • ((0 : E), (1 : 𝕜)) := by ext <;> simp
    conv_lhs => rw [this, map_add, map_smul, smul_eq_mul]
  let Φ' : E × 𝕜 →L[𝕜] E × 𝕜 := (ContinuousLinearMap.fst 𝕜 E 𝕜).prod F'
  let Ψ' : E × 𝕜 →L[𝕜] E × 𝕜 := (ContinuousLinearMap.fst 𝕜 E 𝕜).prod
    (a⁻¹ • (ContinuousLinearMap.snd 𝕜 E 𝕜 -
      F'.comp ((ContinuousLinearMap.inl 𝕜 E 𝕜).comp (ContinuousLinearMap.fst 𝕜 E 𝕜))))
  have h₁ : ∀ v, Ψ' (Φ' v) = v := fun v ↦ by
    ext
    · simp [Φ', Ψ']
    · simp only [Φ', Ψ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        FunLike.coe_smul, FunLike.coe_sub, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hsplit v]
      field_simp
      ring
  have h₂ : ∀ w, Φ' (Ψ' w) = w := fun w ↦ by
    ext
    · simp [Φ', Ψ']
    · simp only [Φ', Ψ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        FunLike.coe_smul, FunLike.coe_sub, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hsplit]
      field_simp
      ring
  let Φe : (E × 𝕜) ≃L[𝕜] E × 𝕜 := ContinuousLinearEquiv.equivOfInverse Φ' Ψ' h₁ h₂
  let Φ : E × 𝕜 → E × 𝕜 := fun v ↦ (v.1, F v)
  have hΦ : HasStrictFDerivAt Φ (Φe : E × 𝕜 →L[𝕜] E × 𝕜) u :=
    hasStrictFDerivAt_fst.prodMk hF
  set e := hΦ.toOpenPartialHomeomorph Φ
  have he : ⇑e = Φ := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hΦ
  have huS : u ∈ e.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hΦ
  have huT : Φ u ∈ e.target := HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hΦ
  obtain ⟨U₀, V, hU₀, hV, hu₀, hv, hUV⟩ :=
    isOpen_prod_iff.mp e.open_source u.1 u.2 (by simpa using huS)
  let W := {c : E | (c, (0 : 𝕜)) ∈ e.target}
  have hcont0 : Continuous fun c : E ↦ (c, (0 : 𝕜)) := continuous_id.prodMk continuous_const
  have hW : IsOpen W := e.open_target.preimage hcont0
  let r : E → 𝕜 := fun c ↦ (e.symm (c, 0)).2
  have hr : ContinuousOn r W :=
    continuous_snd.comp_continuousOn (e.continuousOn_symm.comp hcont0.continuousOn fun _ h ↦ h)
  -- on `W`, the point `e.symm (c, 0)` is `(c, r c)` and solves the equation
  have hW' : ∀ c ∈ W, e.symm (c, 0) = (c, r c) ∧ F (c, r c) = 0 := fun c hc ↦ by
    have := e.right_inv hc
    rw [he] at this
    simp only [Φ, Prod.ext_iff] at this
    have h1 : (e.symm (c, 0)).1 = c := this.1
    refine ⟨Prod.ext h1 rfl, ?_⟩
    rw [← this.2]
    congr 1
    exact Prod.ext h1.symm rfl
  have hu0 : Φ u = (u.1, 0) := by simp [Φ, hu]
  refine ⟨U₀ ∩ (W ∩ r ⁻¹' V), V, hU₀.inter (hr.isOpen_inter_preimage hW hV), hV, ?_, hv,
    r, hr.mono fun c hc ↦ hc.2.1, fun c hc ↦ hc.2.2, ?_⟩
  · have hmem : u.1 ∈ W := by simpa [W, hu0] using huT
    have hru : r u.1 = u.2 := by
      simp only [r]
      rw [← hu0, ← he, e.left_inv huS]
    exact ⟨hu₀, hmem, by simpa [hru] using hv⟩
  · rintro c ⟨hcU, hcW, -⟩ x hx
    constructor
    · intro hFx
      have hS : (c, x) ∈ e.source := hUV ⟨hcU, hx⟩
      have : e (c, x) = (c, 0) := by rw [he]; simp [Φ, hFx]
      have := e.left_inv hS
      rw [‹e (c, x) = (c, 0)›] at this
      simp [r, this]
    · rintro rfl
      exact (hW' c hcW).2

end Implicit

/-- Simple roots of a continuous family of monic polynomials of fixed degree depend locally
continuously on the parameter, and are locally the only roots. -/
theorem exists_continuousOn_simpleRoot {T : Type*} [TopologicalSpace T] {d : ℕ} (P : T → 𝕜[X])
    (hmonic : ∀ τ, (P τ).Monic) (hdeg : ∀ τ, (P τ).natDegree = d)
    (hcont : ∀ i, Continuous fun τ ↦ (P τ).coeff i) {τ₀ : T} {x₀ : 𝕜}
    (hroot : (P τ₀).IsRoot x₀) (hsimple : (P τ₀).derivative.eval x₀ ≠ 0) :
    ∃ U V : Set _, IsOpen U ∧ IsOpen V ∧ τ₀ ∈ U ∧ x₀ ∈ V ∧ ∃ r : T → 𝕜,
      ContinuousOn r U ∧ MapsTo r U V ∧ ∀ τ ∈ U, ∀ x ∈ V, (P τ).IsRoot x ↔ r τ = x := by
  -- the universal monic polynomial of degree `d`
  let F : (Fin d → 𝕜) × 𝕜 → 𝕜 := fun v ↦ v.2 ^ d + ∑ i : Fin d, v.1 i * v.2 ^ (i : ℕ)
  let c : T → Fin d → 𝕜 := fun τ i ↦ (P τ).coeff i
  have hc : Continuous c := continuous_pi fun i ↦ hcont i
  have hF (τ : T) (x : 𝕜) : (P τ).eval x = F (c τ, x) := by
    conv_lhs => rw [(hmonic τ).as_sum, hdeg τ]
    simp [F, c, eval_finsetSum, Fin.sum_univ_eq_sum_range (fun i ↦ (P τ).coeff i * x ^ i) d]
  let u : (Fin d → 𝕜) × 𝕜 := (c τ₀, x₀)
  -- `F` is strictly differentiable at `u`
  obtain ⟨F', hF'⟩ : ∃ F', HasStrictFDerivAt F F' u := by
    have h₁ : ∀ i : Fin d, ∃ G : (Fin d → 𝕜) × 𝕜 →L[𝕜] 𝕜,
        HasStrictFDerivAt (fun v : (Fin d → 𝕜) × 𝕜 ↦ v.1 i * v.2 ^ (i : ℕ)) G u := by
      intro i
      let L : (Fin d → 𝕜) × 𝕜 →L[𝕜] 𝕜 :=
        (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin d ↦ 𝕜) i).comp
          (ContinuousLinearMap.fst 𝕜 _ 𝕜)
      exact ⟨_, L.hasStrictFDerivAt.mul (hasStrictFDerivAt_snd.pow _)⟩
    choose G hG using h₁
    exact ⟨_, (hasStrictFDerivAt_snd.pow d).add
      (HasStrictFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hG i)⟩
  -- its partial derivative in `x` is the derivative of the polynomial
  have hpartial : F' (0, 1) = (P τ₀).derivative.eval x₀ := by
    have h₁ : HasFDerivAt (fun x : 𝕜 ↦ ((c τ₀, x) : (Fin d → 𝕜) × 𝕜))
        ((0 : 𝕜 →L[𝕜] (Fin d → 𝕜)).prod (ContinuousLinearMap.id 𝕜 𝕜)) x₀ :=
      (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
    have h₂ := (hF'.hasFDerivAt.comp x₀ h₁).hasDerivAt
    have h₃ : (fun x ↦ F (c τ₀, x)) = fun x ↦ (P τ₀).eval x := funext fun x ↦ (hF τ₀ x).symm
    rw [Function.comp_def, h₃] at h₂
    simpa using h₂.unique ((P τ₀).hasDerivAt x₀)
  obtain ⟨U, V, hU, hV, hcU, hxV, r, hr, hrUV, hrF⟩ :=
    exists_continuousOn_implicit hF' (by simpa [u, ← hF] using hroot) (hpartial ▸ hsimple)
  refine ⟨c ⁻¹' U, V, hU.preimage hc, hV, hcU, hxV, r ∘ c,
    hr.comp hc.continuousOn fun _ h ↦ h, fun τ hτ ↦ hrUV hτ, fun τ hτ x hx ↦ ?_⟩
  rw [IsRoot.def, hF]
  exact hrF _ hτ x hx

end SGA.SGA1.ExposeXII
