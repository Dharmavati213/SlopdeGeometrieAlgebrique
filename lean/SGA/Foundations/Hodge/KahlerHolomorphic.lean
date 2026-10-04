/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.KahlerPositivity

/-!
# Holomorphic forms on compact Kähler manifolds: closedness, and `h^{q,0} ≤ h^{0,q}`

Let `M` be a compact Hausdorff complex manifold (modelled on a finite-dimensional complex normed
space `E`, `n = dim_ℂ E`) with a Kähler form `κ`.

* `Hodge.integralForm_wedge_conj_wedgePow_eq_zero`: **positivity on `M`**. If `θ` is a smooth
  form of type `(p, 0)`, `p + m = n`, and `∫_M θ ∧ θ̄ ∧ κᵐ = 0`, then `θ = 0`. The integral is
  `Hodge.integralForm`, evaluated on the real frame `Hodge.stdFrame` of the basis
  `Module.finBasis ℂ E`; it comes from the pointwise positivity
  `Hodge.IsPositiveForm.wedge_conj_wedgePow_pos`.
* `Hodge.IsKahlerForm.delForm_eq_zero_of_dbarForm_eq_zero`: **holomorphic forms are closed**:
  a smooth `(q, 0)`-form `η` with `∂̄η = 0` has `∂η = 0`, hence `dη = 0`. Proof: `ψ = ∂η` is a
  holomorphic `(q + 1, 0)`-form and `ψ ∧ ψ̄ ∧ κᵐ = ∂(η ∧ ψ̄ ∧ κᵐ)`, whose integral vanishes by
  Stokes.
* `Hodge.IsKahlerForm.eq_zero_of_conjForm_eq_dbarForm`: if `η` is holomorphic of type `(q, 0)`,
  `q ≥ 1`, and `η̄ = ∂̄β` for some smooth `β`, then `η = 0`: `η ∧ η̄ ∧ κᵐ = ± ∂̄(η ∧ β ∧ κᵐ)`.
* `Hodge.conjDolbeault`: the map `η ↦ [η̄]` from holomorphic `q`-forms to `H^{0,q}_∂̄(M)`,
  additive and conjugate linear (`Hodge.conjDolbeault_smul`), for `M` compact Kähler;
  `Hodge.conjDolbeault_injective`.
* `Hodge.finrank_holomorphicForms_le_finrank_dolbeaultCohomology`: **`h^{q,0} ≤ h^{0,q}`**: if
  `H^{0,q}_∂̄(M)` is finite-dimensional, so is the space of holomorphic `q`-forms, and its
  dimension is at most that of `H^{0,q}_∂̄(M)`.

This is the elementary half of Hodge symmetry `h^{0,q} = h^{q,0}`
(`Hodge.CompactKahlerHodgeSymmetryStatement`); the other half needs harmonic theory.

Reference: D. Huybrechts, *Complex geometry*, Prop. 3.1.12 and Cor. 3.2.12 (we follow the direct
argument by Stokes' theorem, avoiding harmonic forms); C. Voisin, *Hodge theory and complex
algebraic geometry I*, §6.1.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap MeasureTheory
open scoped Manifold ContDiff ComplexOrder

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] {a a' b k k' k'' : ℕ}

lemma domDomCongr_finCongr_wedge (h : a = a') (α : E [⋀^Fin a]→L[ℝ] 𝕜)
    (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α.domDomCongr (finCongr h) ⋏ β = (α ⋏ β).domDomCongr (finCongr (congrArg (· + b) h)) := by
  subst h
  simp

lemma domDomCongr_finCongr_domDomCongr_finCongr (h : k = k') (h' : k' = k'')
    (α : E [⋀^Fin k]→L[ℝ] 𝕜) :
    (α.domDomCongr (finCongr h)).domDomCongr (finCongr h') =
      α.domDomCongr (finCongr (h.trans h')) := by
  subst h h'
  simp

lemma zsmul_wedge (z : ℤ) (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (z • α) ⋏ β = z • (α ⋏ β) :=
  map_zsmul ((wedgeL E 𝕜 a b).flip β) z α

end ContinuousAlternatingMap

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-! ### Auxiliary facts on forms -/

/-- `∂`, `∂̄` of the zero form. -/
lemma partForm_zero (ε : ℂ) {k : ℕ} : partForm ε (0 : M → E [⋀^Fin k]→L[ℝ] ℂ) = 0 := by
  ext1 x
  rw [partForm, localRep_zero, partDeriv, show (0 : E → E [⋀^Fin k]→L[ℝ] ℂ) = fun _ ↦ 0 from rfl,
    fderiv_const_apply, _root_.map_zero, ← alternatizeUncurryFinCLM_apply, _root_.map_zero]
  rfl

/-- A form of type `(p, 0)` with `p > dim_ℂ E` vanishes. -/
lemma IsOfType.eq_zero_of_finrank_lt [FiniteDimensional ℂ E] {p : ℕ}
    {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ) (hp : Module.finrank ℂ E < p) : θ = 0 := by
  rw [hθ.eq_sum_detForm (Module.finBasis ℂ E)]
  refine Finset.sum_eq_zero fun J _ ↦ absurd (Set.powersetCard.card_eq J) ?_
  have := Finset.card_le_univ (J : Finset (Fin (Module.finrank ℂ E)))
  rw [Fintype.card_fin] at this
  omega

/-! ### Integrals -/

section Integral

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) {k k' : ℕ}

omit [FiniteDimensional ℂ E] [BorelSpace E] in
lemma integralForm_const_smul (P : ChartPartition E M) (b : Fin k → E) (c : ℂ)
    (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) :
    integralForm μ P b (fun z ↦ c • ρ z) = c * integralForm μ P b ρ := by
  unfold integralForm chartIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_const_mul]
  have h : (fun z ↦ P.fn i z • c • ρ z) = c • fun z ↦ P.fn i z • ρ z := by
    ext1 z
    exact smul_comm _ _ _
  rw [h, localRep_smul]
  rfl

omit [FiniteDimensional ℂ E] [BorelSpace E] in
lemma integralForm_domDomCongr (P : ChartPartition E M) (e : Fin k ≃ Fin k') (b : Fin k' → E)
    (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) :
    integralForm μ P b (fun z ↦ (ρ z).domDomCongr e) = integralForm μ P (fun i ↦ b (e i)) ρ := by
  unfold integralForm chartIntegral
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rfl

variable (E) in
/-- The real frame `(w₀, …, w_{n-1}, i w₀, …, i w_{n-1})` of the basis `w = Module.finBasis ℂ E`,
indexed by `Fin k` for any `k = n + n`. -/
def stdFrame (h : k = Module.finrank ℂ E + Module.finrank ℂ E) : Fin k → E :=
  fun i ↦ basisFrame (Module.finBasis ℂ E) (finCongr h i)

omit [MeasurableSpace E] [BorelSpace E] in
lemma stdFrame_finCongr (h : k = Module.finrank ℂ E + Module.finrank ℂ E) (h' : k' = k) :
    (fun i ↦ stdFrame E h (finCongr h' i)) = stdFrame E (h'.trans h) :=
  rfl

variable [CompactSpace M] [T2Space M] [μ.IsAddHaarMeasure]

omit [T2Space M] in
/-- **Positivity on a compact Kähler manifold.** If `θ` is a smooth form of type `(p, 0)`,
`p + m = n`, and `∫_M θ ∧ θ̄ ∧ κᵐ = 0`, then `θ = 0`. -/
theorem integralForm_wedge_conj_wedgePow_eq_zero {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsKahlerForm κ) {p m : ℕ} (hpm : p + m = Module.finrank ℂ E)
    (h : (p + p) + 2 * m = Module.finrank ℂ E + Module.finrank ℂ E) (P : ChartPartition E M)
    {θ : M → E [⋀^Fin p]→L[ℝ] ℂ} (hθs : IsSmoothForm θ) (hθ : ∀ x, IsOfType p 0 (θ x))
    (h0 : integralForm μ P (stdFrame E h)
      (fun z ↦ (θ z ⋏ conjForm (θ z)) ⋏ wedgePow (κ z) m) = 0) : θ = 0 := by
  have hk : Module.finrank ℝ E = (p + p) + 2 * m := by
    rw [finrank_real_of_complex]
    omega
  by_contra hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  set c : ℂ := (-1) ^ (Module.finrank ℂ E).choose 2 * Complex.I ^ (p ^ 2)
  have hs : IsSmoothForm fun z ↦ c • ((θ z ⋏ conjForm (θ z)) ⋏ wedgePow (κ z) m) :=
    ((hθs.wedge hθs.conjForm).wedge (hκ.isSmoothForm.wedgePow m)).smul c
  have hpos := integralForm_pos μ hk (stdFrame E h) P hs
    (fun z ↦ (hκ.isPositiveForm z).wedge_conj_wedgePow_nonneg hpm (hθ z) _ h)
    ((hκ.isPositiveForm z₀).wedge_conj_wedgePow_pos hpm (hθ z₀) hz₀ _ h)
  rw [integralForm_const_smul, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

end Integral

/-! ### Holomorphic forms are closed -/

section Closed

variable [FiniteDimensional ℂ E] [CompactSpace M] [T2Space M]

/-- **Holomorphic forms on a compact Kähler manifold are closed**: a smooth form `η` of type
`(q, 0)` with `∂̄η = 0` satisfies `∂η = 0`. -/
theorem IsKahlerForm.delForm_eq_zero_of_dbarForm_eq_zero {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsKahlerForm κ) {q : ℕ} {η : M → E [⋀^Fin q]→L[ℝ] ℂ} (hηs : IsSmoothForm η)
    (hη : ∀ x, IsOfType q 0 (η x)) (hdb : dbarForm η = 0) : delForm η = 0 := by
  set ψ := delForm η
  have hψs : IsSmoothForm ψ := hηs.delForm
  have hψ : ∀ x, IsOfType (q + 1) 0 (ψ x) := isOfType_delForm hη
  have hψdb : dbarForm ψ = 0 := by
    have h := delForm_dbarForm_add hηs
    rw [hdb] at h
    rw [show delForm (0 : M → E [⋀^Fin (q + 1)]→L[ℝ] ℂ) = 0 from partForm_zero (-1),
      zero_add] at h
    exact h
  by_cases hqn : q + 1 ≤ Module.finrank ℂ E
  swap
  · ext1 x
    exact (hψ x).eq_zero_of_finrank_lt (by omega)
  obtain ⟨m, hm⟩ : ∃ m, (q + 1) + m = Module.finrank ℂ E := ⟨_, Nat.add_sub_of_le hqn⟩
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨P⟩ := ChartPartition.nonempty (E := E) (M := M)
  -- `τ = η ∧ ψ̄ ∧ κᵐ`, with `∂τ = ψ ∧ ψ̄ ∧ κᵐ`
  set ψc : M → E [⋀^Fin (q + 1)]→L[ℝ] ℂ := fun x ↦ conjForm (ψ x)
  have hψcs : IsSmoothForm ψc := hψs.conjForm
  have hψcd : delForm ψc = 0 := by
    ext1 x
    rw [delForm_conjForm, hψdb]
    simp [conjForm_zero]
  have hκm : partForm (-1) (fun x ↦ wedgePow (κ x) m) = 0 := hκ.delForm_wedgePow m
  have H : ((q + 1) + (q + 1)) + 2 * m = ((q + (q + 1)) + 2 * m) + 1 := by omega
  have hτ : partForm (-1) (fun x ↦ (η x ⋏ ψc x) ⋏ wedgePow (κ x) m) =
      fun x ↦ ((ψ x ⋏ ψc x) ⋏ wedgePow (κ x) m).domDomCongr (finCongr H) := by
    ext1 x
    rw [partForm_wedge (hηs.wedge hψcs) (hκ.isSmoothForm.wedgePow m), hκm,
      partForm_wedge hηs hψcs, show partForm (-1) ψc = delForm ψc from rfl, hψcd]
    simp only [Pi.zero_apply, wedge_zero_right, smul_zero, add_zero,
      domDomCongr_finCongr_wedge, domDomCongr_finCongr_domDomCongr_finCongr]
    rfl
  have hk : Module.finrank ℝ E = ((q + (q + 1)) + 2 * m) + 1 := by
    rw [finrank_real_of_complex]
    omega
  have hS := integralForm_partForm_eq_zero (Measure.addHaar : Measure E) hk
    (stdFrame E (by omega : ((q + (q + 1)) + 2 * m) + 1 = _)) P
    ((hηs.wedge hψcs).wedge (hκ.isSmoothForm.wedgePow m)) (-1)
  rw [hτ, integralForm_domDomCongr, stdFrame_finCongr] at hS
  exact integralForm_wedge_conj_wedgePow_eq_zero (Measure.addHaar : Measure E) hκ hm _ P hψs hψ hS

/-- On a compact Kähler manifold, a smooth form `η` of type `(r + 1, 0)` with `∂̄η = 0` whose
conjugate is `∂̄`-exact, `η̄ = ∂̄β` with `β` smooth, vanishes. -/
theorem IsKahlerForm.eq_zero_of_conjForm_eq_dbarForm {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ}
    (hκ : IsKahlerForm κ) {r : ℕ} {η : M → E [⋀^Fin (r + 1)]→L[ℝ] ℂ} (hηs : IsSmoothForm η)
    (hη : ∀ x, IsOfType (r + 1) 0 (η x)) (hdb : dbarForm η = 0)
    {β : M → E [⋀^Fin r]→L[ℝ] ℂ} (hβs : IsSmoothForm β)
    (hβ : ∀ x, conjForm (η x) = dbarForm β x) : η = 0 := by
  by_cases hqn : r + 1 ≤ Module.finrank ℂ E
  swap
  · ext1 x
    exact (hη x).eq_zero_of_finrank_lt (by omega)
  obtain ⟨m, hm⟩ : ∃ m, (r + 1) + m = Module.finrank ℂ E := ⟨_, Nat.add_sub_of_le hqn⟩
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨P⟩ := ChartPartition.nonempty (E := E) (M := M)
  have hκm : partForm 1 (fun x ↦ wedgePow (κ x) m) = 0 := hκ.dbarForm_wedgePow m
  have H : ((r + 1) + (r + 1)) + 2 * m = (((r + 1) + r) + 2 * m) + 1 := by omega
  -- `∂̄ (η ∧ β ∧ κᵐ) = (-1)^(r+1) η ∧ η̄ ∧ κᵐ`
  have hτ : partForm 1 (fun x ↦ (η x ⋏ β x) ⋏ wedgePow (κ x) m) =
      fun x ↦ ((-1 : ℂ) ^ (r + 1)) •
        ((η x ⋏ conjForm (η x)) ⋏ wedgePow (κ x) m).domDomCongr (finCongr H) := by
    ext1 x
    rw [partForm_wedge (hηs.wedge hβs) (hκ.isSmoothForm.wedgePow m), hκm,
      partForm_wedge hηs hβs, show partForm 1 η = dbarForm η from rfl, hdb,
      show partForm 1 β x = dbarForm β x from rfl, ← hβ x]
    simp only [Pi.zero_apply, wedge_zero_right, wedge_zero_left, smul_zero, add_zero, zero_add,
      domDomCongr_zero, zsmul_wedge]
    rw [← Int.cast_smul_eq_zsmul ℂ, domDomCongr_smul]
    push_cast
    rfl
  have hk : Module.finrank ℝ E = (((r + 1) + r) + 2 * m) + 1 := by
    rw [finrank_real_of_complex]
    omega
  have hS := integralForm_partForm_eq_zero (Measure.addHaar : Measure E) hk
    (stdFrame E (by omega : (((r + 1) + r) + 2 * m) + 1 = _)) P
    ((hηs.wedge hβs).wedge (hκ.isSmoothForm.wedgePow m)) 1
  rw [hτ, integralForm_const_smul, integralForm_domDomCongr, stdFrame_finCongr] at hS
  have hS' := (mul_eq_zero.1 hS).resolve_left (pow_ne_zero _ (by norm_num))
  exact integralForm_wedge_conj_wedgePow_eq_zero (Measure.addHaar : Measure E) hκ hm _ P hηs hη hS'

end Closed

/-! ### The map `η ↦ [η̄]` into Dolbeault cohomology -/

section Dolbeault

variable (E M)

/-- The conjugate `η̄` of a `(q, 0)`-form `η`, a `(0, q)`-form, with its degree written `0 + q` as
in `Hodge.smoothForms E M 0 q`. -/
def conjZeroForm {q : ℕ} (η : M → E [⋀^Fin (q + 0)]→L[ℝ] ℂ) : M → E [⋀^Fin (0 + q)]→L[ℝ] ℂ :=
  fun x ↦ (conjForm (η x)).domDomCongr (finCongr (by omega))

variable {E M}

lemma conjZeroForm_mem_smoothForms {q : ℕ} {η : M → E [⋀^Fin (q + 0)]→L[ℝ] ℂ}
    (hη : η ∈ smoothForms E M q 0) : conjZeroForm E M η ∈ smoothForms E M 0 q :=
  ⟨hη.1.conjForm.domDomCongr _, fun x ↦ ((hη.2 x).conjForm).domDomCongr _⟩

lemma dbarForm_conjZeroForm {q : ℕ} {η : M → E [⋀^Fin (q + 0)]→L[ℝ] ℂ} (hdel : delForm η = 0) :
    dbarForm (conjZeroForm E M η) = 0 := by
  ext1 x
  have h : dbarForm (conjZeroForm E M η) x = (dbarForm (fun x ↦ conjForm (η x)) x).domDomCongr
      (finCongr (by omega)) :=
    partForm_domDomCongr_finCongr (η := fun x ↦ conjForm (η x)) _ 1 x
  rw [h, dbarForm_conjForm, hdel]
  simp [conjForm_zero]

variable [FiniteDimensional ℂ E] [CompactSpace M] [T2Space M]

/-- On a compact Kähler manifold, every holomorphic form is `∂`-closed. -/
lemma delForm_holomorphicForms (hK : IsKahlerManifold E M) {q : ℕ}
    (η : holomorphicForms E M q) : delForm (η : smoothForms E M q 0).1 = 0 := by
  obtain ⟨κ, hκ⟩ := hK
  have h := η.2
  change dbarLinear E M q 0 η.1 = 0 at h
  exact hκ.delForm_eq_zero_of_dbarForm_eq_zero η.1.2.1 η.1.2.2 (congrArg Subtype.val h)

variable (E M) in
/-- **The map `η ↦ [η̄]`** from holomorphic `q`-forms to `H^{0,q}_∂̄(M)`, on a compact Kähler
manifold (where holomorphic forms are `∂`-closed, so that `η̄` is `∂̄`-closed). It is additive
and conjugate linear (`Hodge.conjDolbeault_smul`). -/
def conjDolbeault (hK : IsKahlerManifold E M) (q : ℕ) :
    holomorphicForms E M q →+ dolbeaultCohomology E M 0 q where
  toFun η := Submodule.Quotient.mk ⟨⟨conjZeroForm E M (η : smoothForms E M q 0).1,
    conjZeroForm_mem_smoothForms η.1.2⟩,
    Subtype.ext (dbarForm_conjZeroForm (delForm_holomorphicForms hK η))⟩
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero]
    congr 1
    ext x v
    simp [conjZeroForm, conjForm_zero]
  map_add' η₁ η₂ := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    ext x v
    simp [conjZeroForm, conjForm_add]

lemma conjDolbeault_smul (hK : IsKahlerManifold E M) {q : ℕ} (c : ℂ) (η : holomorphicForms E M q) :
    conjDolbeault E M hK q (c • η) = conj c • conjDolbeault E M hK q η := by
  change Submodule.Quotient.mk _ = conj c • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  ext x v
  simp [conjZeroForm, conjForm_smul]

/-- **`η ↦ [η̄]` is injective** on a compact Kähler manifold. -/
theorem conjDolbeault_injective (hK : IsKahlerManifold E M) (q : ℕ) :
    Function.Injective (conjDolbeault E M hK q) := by
  rw [injective_iff_map_eq_zero]
  intro η hη
  change Submodule.Quotient.mk _ = 0 at hη
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hη
  obtain ⟨κ, hκ⟩ := id hK
  have hconj : ∀ x, conjZeroForm E M (η : smoothForms E M q 0).1 x =
      (conjForm ((η : smoothForms E M q 0).1 x)).domDomCongr (finCongr (by omega)) := fun x ↦ rfl
  -- reduce to `η.1.1 = 0`
  suffices h : (η : smoothForms E M q 0).1 = 0 by
    ext1
    ext1
    exact h
  cases q with
  | zero =>
    change _ ∈ (⊥ : Submodule ℂ (smoothForms E M 0 0)) at hη
    rw [Submodule.mem_bot] at hη
    ext1 x
    have hx := congrFun (congrArg Subtype.val hη) x
    simp only [Submodule.coe_subtype, ZeroMemClass.coe_zero, Pi.zero_apply] at hx
    rw [hconj] at hx
    have hx' : conjForm ((η : smoothForms E M 0 0).1 x) = 0 := by
      simpa using hx
    rw [Pi.zero_apply, ← conjForm_conjForm ((η : smoothForms E M 0 0).1 x), hx', conjForm_zero]
  | succ r =>
    change _ ∈ LinearMap.range (dbarLinear E M 0 r) at hη
    obtain ⟨β, hβ⟩ := hη
    have hβ' : ∀ x, dbarForm β.1 x = conjZeroForm E M (η : smoothForms E M (r + 1) 0).1 x :=
      fun x ↦ congrFun (congrArg Subtype.val hβ) x
    set β' : M → E [⋀^Fin r]→L[ℝ] ℂ := fun x ↦ (β.1 x).domDomCongr (finCongr (Nat.zero_add r))
    have hβ's : IsSmoothForm β' := β.2.1.domDomCongr _
    have hdb : dbarForm (η : smoothForms E M (r + 1) 0).1 = 0 :=
      congrArg Subtype.val (show dbarLinear E M (r + 1) 0 η.1 = 0 from η.2)
    refine hκ.eq_zero_of_conjForm_eq_dbarForm η.1.2.1 η.1.2.2 hdb hβ's fun x ↦ ?_
    rw [show dbarForm β' x = partForm 1 (fun x ↦ (β.1 x).domDomCongr
      (finCongr (Nat.zero_add r))) x from rfl, partForm_domDomCongr_finCongr,
      show partForm 1 β.1 x = dbarForm β.1 x from rfl, hβ', hconj,
      domDomCongr_finCongr_domDomCongr_finCongr]
    simp

/-- **`h^{q,0} ≤ h^{0,q}` on a compact Kähler manifold**: if `H^{0,q}_∂̄(M)` is finite-dimensional,
then so is the space of holomorphic `q`-forms, and `dim H⁰(M, Ωᵍ) ≤ dim H^{0,q}_∂̄(M)`. -/
theorem finrank_holomorphicForms_le_finrank_dolbeaultCohomology (hK : IsKahlerManifold E M)
    (q : ℕ) [FiniteDimensional ℂ (dolbeaultCohomology E M 0 q)] :
    FiniteDimensional ℂ (holomorphicForms E M q) ∧
      Module.finrank ℂ (holomorphicForms E M q) ≤
        Module.finrank ℂ (dolbeaultCohomology E M 0 q) := by
  have hr := rank_le_of_surjective_injective (starRingEnd ℂ) (conjDolbeault E M hK q)
    (fun z ↦ ⟨conj z, Complex.conj_conj z⟩) (conjDolbeault_injective hK q)
    (fun c η ↦ conjDolbeault_smul hK c η)
  have hfin : Module.rank ℂ (dolbeaultCohomology E M 0 q) < Cardinal.aleph0 :=
    Module.rank_lt_aleph0_iff.2 inferInstance
  refine ⟨Module.rank_lt_aleph0_iff.1 (hr.trans_lt hfin), ?_⟩
  exact Module.finrank_le_finrank_of_rank_le_rank (by simpa using hr) hfin

end Dolbeault

end Hodge
