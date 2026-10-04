/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.RootsOfUnity.Complex
import SGA.Foundations.Topology.FiniteCovering
import SGA.Foundations.Topology.LocallyContractible

/-!
# Punctured discs and `ℂ ∖ {0}`: fundamental group and finite coverings

Let `B ⊆ ℂ ∖ {0}` be such that `exp⁻¹(B)` is simply connected: for example `ℂ ∖ {0}`
(`isSimplyConnected_exp_preimage_compl_zero`), a punctured disc
(`isSimplyConnected_exp_preimage_ball_diff_zero`), or an annulus. Then:

* `Complex.isAddQuotientCoveringMap_expRestrict`: `exp : exp⁻¹(B) → B` is a quotient covering map
  by `2πiℤ` (a universal covering);
* `Complex.fundamentalGroupMulEquivInt`: `π₁(B, b) ≅ ℤ`, the generator being the loop around `0`
  (`Complex.generatorLoop`);
* `Complex.isCoveringMap_powRestrict`: the Kummer map `w ↦ wⁿ`, `{w | wⁿ ∈ B} → B`, is a finite
  covering, on whose fibres the loop around `0` acts by `exp (2πi / n)`
  (`Complex.monodromy_generatorLoop_powRestrict`);
* `Complex.not_forall_pow_eq_of_continuous`: for `n ≥ 2` there is no continuous `n`-th root of `z`
  on `B`;
* `Complex.exists_homeomorph_powRestrict`: every finite covering `p : E → B` with `E` nonempty and
  transitive monodromy (e.g. `E` path-connected) is a Kummer covering: `E ≃ₜ {w | wⁿ ∈ B}` over
  `B` for some `n ≠ 0`. This is the local model of a finite étale covering near a normal-crossings
  divisor in the proof of SGA 1 XII.5.1, step 2 c), and of XII.5.4, in the case of one variable
  and one branch (`n = p = 1` in SGA's notation: a punctured disc). The total space is taken in
  `Type` because the classification of finite coverings
  (`TopCat.FiniteCovering.equivalenceAction`) is stated for coverings in the universe of the base.

The form with a connected total space `E` in place of transitive monodromy is
`Complex.exists_homeomorph_powRestrict_of_connectedSpace`
(`Foundations/Topology/PuncturedDiscConnected.lean`). The higher-dimensional local model
`(Δ*)ᵖ × Δ^q` (fundamental group `ℤᵖ`, coverings dominated by multi-Kummer coverings) is in
`Foundations/Topology/PuncturedDiscProduct.lean`.

General tools proved on the way: `IsQuotientCoveringMap.restrictPreimage` (a quotient covering map
restricts over any subset of the base) and `MulAction.exists_equiv_smul_of_forall_smul_eq_iff`
(transitive `G`-sets with points of equal stabilizers are isomorphic).

The fundamental group of the circle is in mathlib, as
`Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv`.

## References

* [A. Hatcher, *Algebraic Topology*, §1.1 and §1.3][hatcher02]
* [O. Forster, *Lectures on Riemann Surfaces*, Theorem 5.10][forster1981]
-/

open Set Topology

/-- Two pretransitive `G`-sets `A` and `B` are isomorphic (by a `G`-equivariant bijection) as soon
as some points `a ∈ A` and `b ∈ B` have the same stabilizer. -/
theorem MulAction.exists_equiv_smul_of_forall_smul_eq_iff {G A B : Type*} [Group G]
    [MulAction G A] [MulAction G B] [IsPretransitive G A] [IsPretransitive G B] {a : A} {b : B}
    (h : ∀ g : G, g • a = a ↔ g • b = b) :
    ∃ Φ : A ≃ B, ∀ (g : G) (x : A), Φ (g • x) = g • Φ x := by
  have key (g g' : G) : g • a = g' • a ↔ g • b = g' • b :=
    calc g • a = g' • a ↔ (g'⁻¹ * g) • a = a := by rw [mul_smul, inv_smul_eq_iff]
      _ ↔ (g'⁻¹ * g) • b = b := h _
      _ ↔ g • b = g' • b := by rw [mul_smul, inv_smul_eq_iff]
  choose χ hχ using fun x : A ↦ exists_smul_eq G a x
  choose ψ hψ using fun y : B ↦ exists_smul_eq G b y
  refine ⟨{ toFun x := χ x • b, invFun y := ψ y • a, left_inv x := ?_, right_inv y := ?_ },
    fun g x ↦ ?_⟩
  · change ψ (χ x • b) • a = x
    rw [(key (ψ (χ x • b)) (χ x)).mpr (hψ _), hχ]
  · change χ (ψ y • a) • b = y
    rw [(key (χ (ψ y • a)) (ψ y)).mp (hχ _), hψ]
  · change χ (g • x) • b = g • χ x • b
    rw [smul_smul, (key (χ (g • x)) (g * χ x)).mp (by rw [hχ, mul_smul, hχ])]

/-- The monodromy of a covering map fixes the points of a continuous section. -/
theorem IsCoveringMap.monodromy_section {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {F : X → E} (hF : Continuous F) (hpF : ∀ x, p (F x) = x)
    {x : X} (γ : FundamentalGroup X x) : hp.monodromy γ ⟨F x, hpF x⟩ = ⟨F x, hpF x⟩ := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
  exact hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk (γ.map hF))
    (congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t ↦ hpF (γ t))))

namespace IsQuotientCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
  {G : Type*} [Group G] [MulAction G E]

/-- The preimage of a set under a quotient covering map by `G`, as a sub-`G`-set. -/
@[to_additive /-- The preimage of a set under a quotient covering map by `G`, as a
sub-`G`-set. -/]
def subMulActionPreimage (hf : IsQuotientCoveringMap f G) (U : Set X) : SubMulAction G E where
  carrier := f ⁻¹' U
  smul_mem' g e he := by rwa [mem_preimage, hf.map_smul]

/-- A quotient covering map by `G` restricts to a quotient covering map by `G` over any subset
of the base. -/
@[to_additive /-- A quotient covering map by `G` restricts to a quotient covering map by `G`
over any subset of the base. -/]
theorem restrictPreimage (hf : IsQuotientCoveringMap f G) (U : Set X) :
    IsQuotientCoveringMap (fun e : hf.subMulActionPreimage U ↦ (⟨f e, e.2⟩ : U)) G := by
  have := hf.toContinuousConstSMul
  have hc := hf.isCancelSMul
  refine (isQuotientCoveringMap_iff_isCoveringMap_and _ _).mpr
    ⟨hf.isCoveringMap.restrictPreimage U, fun u ↦ ?_, ⟨fun g ↦ ?_⟩, ⟨fun g h e he ↦ ?_⟩,
      fun {e₁ e₂} ↦ ?_⟩
  · obtain ⟨e, he⟩ := hf.surjective u
    exact ⟨⟨e, show f e ∈ U from he ▸ u.2⟩, Subtype.ext he⟩
  · exact ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _
  · exact hc.right_cancel g h e (congrArg Subtype.val he)
  · rw [Subtype.ext_iff, hf.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg Subtype.val hg⟩

end IsQuotientCoveringMap

namespace Complex

open Real in
/-- `exp⁻¹(B)`, as a sub-`2πiℤ`-set of `ℂ`. -/
noncomputable def expPreimage (B : Set ℂ) :
    SubAddAction (AddSubgroup.zmultiples (2 * π * I)) ℂ :=
  isAddQuotientCoveringMap_exp.subAddActionPreimage {z | (z : ℂ) ∈ B}

variable {B : Set ℂ}

@[simp] lemma mem_expPreimage {w : ℂ} : w ∈ expPreimage B ↔ exp w ∈ B := Iff.rfl

/-- The restriction of `exp` to `exp⁻¹(B) → B`. -/
noncomputable def expRestrict (B : Set ℂ) (w : expPreimage B) : B := ⟨exp w, w.2⟩

@[fun_prop] lemma continuous_expRestrict : Continuous (expRestrict B) :=
  (continuous_exp.comp continuous_subtype_val).subtype_mk _

/-- `{z ≠ 0 | z ∈ B} ≃ₜ B` for `0 ∉ B`. -/
private def neZeroHomeomorph (hB0 : (0 : ℂ) ∉ B) :
    {z : {z : ℂ // z ≠ 0} // (z : ℂ) ∈ B} ≃ₜ B where
  toFun z := ⟨z.1.1, z.2⟩
  invFun b := ⟨⟨b.1, fun h ↦ hB0 (h ▸ b.2)⟩, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

open Real in
/-- For `0 ∉ B`, `exp : exp⁻¹(B) → B` is a quotient covering map by `2πiℤ`. -/
theorem isAddQuotientCoveringMap_expRestrict (hB0 : (0 : ℂ) ∉ B) :
    IsAddQuotientCoveringMap (expRestrict B) (AddSubgroup.zmultiples (2 * π * I)) :=
  (isAddQuotientCoveringMap_exp.restrictPreimage {z | (z : ℂ) ∈ B}).homeomorph_comp
    (neZeroHomeomorph hB0)

section Loop

open Real

variable (hB0 : (0 : ℂ) ∉ B)

include hB0 in
lemma exp_log_coe (b : B) : exp (log b) = b := exp_log fun h ↦ hB0 (h ▸ b.2)

/-- The point `log b` of `exp⁻¹(B)` over `b`. -/
noncomputable def logLift (b : B) : expPreimage B :=
  ⟨log b, by simp [exp_log_coe hB0 b]⟩

/-- The point `log b + 2πi` of `exp⁻¹(B)` over `b`. -/
noncomputable def logLiftAdd (b : B) : expPreimage B :=
  ⟨log b + 2 * π * I, by simp [exp_add, exp_log_coe hB0 b]⟩

@[simp] lemma coe_logLift (b : B) : (logLift hB0 b : ℂ) = log b := rfl

@[simp] lemma coe_logLiftAdd (b : B) : (logLiftAdd hB0 b : ℂ) = log b + 2 * π * I := rfl

lemma expRestrict_logLift (b : B) : expRestrict B (logLift hB0 b) = b :=
  Subtype.ext (exp_log_coe hB0 b)

lemma expRestrict_logLiftAdd (b : B) : expRestrict B (logLiftAdd hB0 b) = b :=
  Subtype.ext (by simp [expRestrict, logLiftAdd, exp_add, exp_log_coe hB0 b])

variable [PathConnectedSpace (expPreimage B)]

/-- The loop around `0` at `b ∈ B`: the image under `exp` of a path in `exp⁻¹(B)` from `log b`
to `log b + 2πi`. If `exp⁻¹(B)` is simply connected, it generates `π₁(B, b)`
(`mem_zpowers_generatorLoop`). -/
noncomputable def generatorLoop (b : B) : FundamentalGroup B b :=
  Path.Homotopic.Quotient.mk
    (((PathConnectedSpace.somePath (logLift hB0 b) (logLiftAdd hB0 b)).map
      continuous_expRestrict).cast (expRestrict_logLift hB0 b).symm
      (expRestrict_logLiftAdd hB0 b).symm)

/-- The monodromy of `generatorLoop` on the covering `exp : exp⁻¹(B) → B` sends `log b` to
`log b + 2πi`. -/
lemma monodromy_generatorLoop (b : B) :
    (isAddQuotientCoveringMap_expRestrict hB0).isCoveringMap.monodromy (generatorLoop hB0 b)
      ⟨logLift hB0 b, expRestrict_logLift hB0 b⟩ =
      ⟨logLiftAdd hB0 b, expRestrict_logLiftAdd hB0 b⟩ :=
  (isAddQuotientCoveringMap_expRestrict hB0).isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)) rfl

variable [SimplyConnectedSpace (expPreimage B)]

/-- Under `π₁(B, b) ≅ (2πiℤ)ᵐᵒᵖ` given by the universal covering `exp⁻¹(B) → B`, the loop around
`0` goes to `2πi`. -/
private lemma fundamentalGroupEquiv_generatorLoop (b : B) :
    (isAddQuotientCoveringMap_expRestrict hB0).fundamentalGroupEquiv
      ⟨logLift hB0 b, expRestrict_logLift hB0 b⟩ (generatorLoop hB0 b) =
      MulOpposite.op (Multiplicative.ofAdd
        (⟨2 * π * I, AddSubgroup.mem_zmultiples _⟩ : AddSubgroup.zmultiples (2 * π * I))) := by
  refine ((isAddQuotientCoveringMap_expRestrict hB0).fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
    ?_
  rw [monodromy_generatorLoop]
  apply Subtype.ext
  change (2 * π * I : ℂ) + log b = log b + 2 * π * I
  ring

/-- If `exp⁻¹(B)` is simply connected, `π₁(B, b)` is generated by the loop around `0`. -/
theorem mem_zpowers_generatorLoop (b : B) (γ : FundamentalGroup B b) :
    γ ∈ Subgroup.zpowers (generatorLoop hB0 b) := by
  let φ := (isAddQuotientCoveringMap_expRestrict hB0).fundamentalGroupEquiv
    ⟨logLift hB0 b, expRestrict_logLift hB0 b⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (Multiplicative.toAdd (φ γ).unop).2
  have hγ : φ γ = φ (generatorLoop hB0 b ^ k) := by
    rw [map_zpow, fundamentalGroupEquiv_generatorLoop, ← MulOpposite.op_zpow, ← ofAdd_zsmul]
    apply MulOpposite.unop_injective
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hk.symm
  exact ⟨k, (φ.injective hγ).symm⟩

/-- `π₁(B, b) ≅ ℤ` for `B ⊆ ℂ ∖ {0}` with `exp⁻¹(B)` simply connected; `1` goes to the loop
around `0`. -/
noncomputable def fundamentalGroupMulEquivInt (b : B) :
    Multiplicative ℤ ≃* FundamentalGroup B b :=
  MulEquiv.ofBijective (zpowersHom _ (generatorLoop hB0 b)) ⟨by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 := congrArg ((isAddQuotientCoveringMap_expRestrict hB0).fundamentalGroupEquiv
      ⟨logLift hB0 b, expRestrict_logLift hB0 b⟩) hk
    rw [zpowersHom_apply, map_zpow, fundamentalGroupEquiv_generatorLoop, map_one,
      ← MulOpposite.op_zpow, ← ofAdd_zsmul] at h1
    have h2 : (Multiplicative.toAdd k) • (2 * π * I : ℂ) = 0 :=
      congrArg Subtype.val (Multiplicative.ofAdd.injective (MulOpposite.op_injective h1))
    rw [smul_eq_zero] at h2
    exact h2.resolve_right two_pi_I_ne_zero,
    fun γ ↦ by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_generatorLoop hB0 b γ)
      exact ⟨Multiplicative.ofAdd k, hk⟩⟩

@[simp] lemma fundamentalGroupMulEquivInt_apply (b : B) (k : Multiplicative ℤ) :
    fundamentalGroupMulEquivInt hB0 b k = generatorLoop hB0 b ^ (Multiplicative.toAdd k) :=
  rfl

end Loop

section Kummer

open Real

variable (B) (n : ℕ)

/-- The Kummer covering `w ↦ wⁿ` of `B`, with total space `{w | wⁿ ∈ B}`. -/
def powRestrict (w : {w : ℂ // w ^ n ∈ B}) : B := ⟨w.1 ^ n, w.2⟩

@[fun_prop] lemma continuous_powRestrict : Continuous (powRestrict B n) :=
  (continuous_subtype_val.pow n).subtype_mk _

variable {B} {n}

/-- For `0 ∉ B` and `n ≠ 0`, the Kummer map `w ↦ wⁿ` is a covering map of `B`. -/
theorem isCoveringMap_powRestrict (hB0 : (0 : ℂ) ∉ B) (hn : n ≠ 0) :
    IsCoveringMap (powRestrict B n) :=
  ((isCoveringMapOn_npow n (by exact_mod_cast hn)).mono fun z hz ↦ by
    rintro rfl
    exact hB0 hz).isCoveringMap_restrictPreimage

/-- The fibres of the Kummer covering are finite. -/
theorem finite_powRestrict_preimage (hn : n ≠ 0) (b : B) :
    (powRestrict B n ⁻¹' {b}).Finite := by
  refine (((Polynomial.nthRoots n (b : ℂ)).toFinset.finite_toSet).preimage
    Subtype.val_injective.injOn).subset fun w hw ↦ ?_
  have hw : w.1 ^ n = b := congrArg Subtype.val hw
  simp [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn), hw]

variable (hB0 : (0 : ℂ) ∉ B)

include hB0 in
private lemma pow_mul_exp_eq {b : B} {w : ℂ} (hw : w ^ n = b) (hn : n ≠ 0) (s : ℂ) :
    (w * exp ((s - log b) / n)) ^ n = exp s := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [mul_pow, ← exp_nat_mul, mul_div_cancel₀ _ hn', exp_sub, exp_log_coe hB0 b, hw,
    mul_div_cancel₀ _ (fun h ↦ hB0 (h ▸ b.2))]

variable [PathConnectedSpace (expPreimage B)]

/-- The monodromy of the loop around `0` on the Kummer covering of degree `n` is multiplication by
`exp (2πi / n)`. -/
theorem monodromy_generatorLoop_powRestrict (hn : n ≠ 0) (b : B)
    (w : powRestrict B n ⁻¹' {b}) :
    ((isCoveringMap_powRestrict hB0 hn).monodromy (generatorLoop hB0 b) w : ℂ) =
      exp (2 * π * I / n) * w := by
  have hwb : (w : ℂ) ^ n = b := congrArg Subtype.val w.2
  let δ := PathConnectedSpace.somePath (logLift hB0 b) (logLiftAdd hB0 b)
  have hmem : (exp (2 * π * I / n) * w) ^ n ∈ B := by
    rw [mul_pow, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), exp_two_pi_mul_I,
      one_mul, hwb]
    exact b.2
  let Γ : Path (w : {w : ℂ // w ^ n ∈ B}) ⟨exp (2 * π * I / n) * w, hmem⟩ :=
    { toFun t := ⟨w * exp (((δ t : ℂ) - log b) / n), by
        rw [pow_mul_exp_eq hB0 hwb hn]; exact (δ t).2⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp [δ]
      target' := by ext; simp [δ, mul_comm] }
  have hey : powRestrict B n ⟨exp (2 * π * I / n) * w, hmem⟩ = b := by
    ext
    simp only [powRestrict]
    rw [mul_pow, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn),
      exp_two_pi_mul_I, one_mul, hwb]
  have := (isCoveringMap_powRestrict hB0 hn).monodromy_eq_of_map_eq
    (ey := ⟨_, hey⟩) (γ := generatorLoop hB0 b) (Path.Homotopic.Quotient.mk Γ)
    (congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t ↦ Subtype.ext
      (pow_mul_exp_eq hB0 hwb hn _))))
  rw [this]

end Kummer

section Examples

open Real

/-- `exp⁻¹(ℂ ∖ {0}) = ℂ` is simply connected. -/
lemma isSimplyConnected_exp_preimage_compl_zero : IsSimplyConnected (exp ⁻¹' {0}ᶜ) := by
  have : exp ⁻¹' {0}ᶜ = univ := eq_univ_of_forall fun w ↦ exp_ne_zero w
  rw [this]
  have := (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace univ_nonempty
  exact SimplyConnectedSpace.ofContractible _

/-- For `r > 0`, `exp⁻¹(D(0, r) ∖ {0})` (a half-plane) is simply connected. -/
lemma isSimplyConnected_exp_preimage_ball_diff_zero {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (exp ⁻¹' (Metric.ball (0 : ℂ) r \ {0})) := by
  have : exp ⁻¹' (Metric.ball (0 : ℂ) r \ {0}) = {w : ℂ | w.re < Real.log r} := by
    ext w
    simp [norm_exp, Real.lt_log_iff_exp_lt hr, exp_ne_zero]
  rw [this]
  have hc : Convex ℝ {w : ℂ | w.re < Real.log r} :=
    convex_halfSpace_lt (f := Complex.re) ⟨fun _ _ ↦ rfl, fun _ _ ↦ by simp⟩ _
  have := hc.contractibleSpace ⟨Real.log r - 1, by simp⟩
  exact SimplyConnectedSpace.ofContractible _

end Examples

section Classification

open Real CategoryTheory

/-- For `B ⊆ ℂ ∖ {0}` with `exp⁻¹(B)` simply connected (e.g. a punctured disc) and `n ≥ 2`, there
is no continuous `n`-th root of `z` on `B`. -/
theorem not_forall_pow_eq_of_continuous (hB0 : (0 : ℂ) ∉ B)
    (hS : IsSimplyConnected (exp ⁻¹' B)) {n : ℕ} (hn : 2 ≤ n) {f : B → ℂ} (hf : Continuous f) :
    ¬ ∀ z : B, f z ^ n = z := by
  intro hpow
  have : SimplyConnectedSpace (expPreimage B) := hS.simplyConnectedSpace
  have hn0 : n ≠ 0 := by omega
  obtain ⟨w, hw⟩ := hS.nonempty
  let b : B := ⟨exp w, hw⟩
  let F : B → {w : ℂ // w ^ n ∈ B} := fun z ↦ ⟨f z, by rw [hpow]; exact z.2⟩
  have hF : Continuous F := hf.subtype_mk _
  have hpF : ∀ z, powRestrict B n (F z) = z := fun z ↦ Subtype.ext (hpow z)
  have h₁ := (isCoveringMap_powRestrict hB0 hn0).monodromy_section hF hpF (generatorLoop hB0 b)
  have h₂ := monodromy_generatorLoop_powRestrict hB0 hn0 b ⟨F b, hpF b⟩
  rw [h₁] at h₂
  have hfb : f b ≠ 0 := fun h ↦ hB0 (by simpa [h, zero_pow hn0, ← hpow b] using b.2)
  have hζ : exp (2 * π * I / n) = 1 := by
    have : f b = exp (2 * π * I / n) * f b := h₂
    exact (mul_eq_right₀ hfb).mp this.symm
  exact (isPrimitiveRoot_exp n hn0).ne_one (by omega) hζ

/-- **Connected finite coverings of `B ⊆ ℂ ∖ {0}` are Kummer coverings.** Let `B ⊆ ℂ ∖ {0}` be
open with `exp⁻¹(B)` simply connected (e.g. a punctured disc, `ℂ ∖ {0}`, an annulus). Let
`p : E → B` be a covering map with finite fibres, `E` nonempty, on which the monodromy acts
transitively on every fibre (e.g. `E` path-connected). Then for some `n ≠ 0` there is a
homeomorphism `φ : E ≃ₜ {w | wⁿ ∈ B}` with `p = φⁿ`. -/
theorem exists_homeomorph_powRestrict (hBo : IsOpen B) (hB0 : (0 : ℂ) ∉ B)
    (hS : IsSimplyConnected (exp ⁻¹' B)) {E : Type} [TopologicalSpace E] [Nonempty E]
    {p : E → B} (hp : IsCoveringMap p) (hfin : ∀ b, (p ⁻¹' {b}).Finite)
    (htrans : ∀ (b : B) (e₁ e₂ : p ⁻¹' {b}),
      ∃ γ : FundamentalGroup B b, hp.monodromy γ e₁ = e₂) :
    ∃ (n : ℕ) (_ : n ≠ 0) (φ : E ≃ₜ {w : ℂ // w ^ n ∈ B}),
      ∀ x, powRestrict B n (φ x) = p x := by
  classical
  have : SimplyConnectedSpace (expPreimage B) := hS.simplyConnectedSpace
  have : PathConnectedSpace B :=
    (isAddQuotientCoveringMap_expRestrict hB0).surjective.pathConnectedSpace
      continuous_expRestrict
  have : StronglyLocallyContractibleSpace B := hBo.stronglyLocallyContractibleSpace
  obtain ⟨e₀⟩ := ‹Nonempty E›
  set b₀ := p e₀
  have hF : Finite (p ⁻¹' {b₀}) := (hfin b₀).to_subtype
  set n := Nat.card (p ⁻¹' {b₀}) with hn_def
  have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨e₀, rfl⟩⟩, hF⟩
  have hK := isCoveringMap_powRestrict hB0 hn
  set ℓ := generatorLoop hB0 b₀
  let _ : MulAction (FundamentalGroup B b₀) (p ⁻¹' {b₀}) := hp.fundamentalGroupMulAction b₀
  let _ : MulAction (FundamentalGroup B b₀) (powRestrict B n ⁻¹' {b₀}) :=
    hK.fundamentalGroupMulAction b₀
  have hgen := mem_zpowers_generatorLoop hB0 b₀
  -- the fibre of `E`
  let e₀' : p ⁻¹' {b₀} := ⟨e₀, rfl⟩
  have htE : MulAction.IsPretransitive (FundamentalGroup B b₀) (p ⁻¹' {b₀}) := ⟨htrans b₀⟩
  have hperE : Function.minimalPeriod (ℓ • ·) e₀' = n := by
    have horb : MulAction.orbit (Subgroup.zpowers ℓ) e₀' = univ := by
      refine eq_univ_of_forall fun e ↦ ?_
      obtain ⟨γ, hγ⟩ := htrans b₀ e₀' e
      exact ⟨⟨γ, hgen γ⟩, hγ⟩
    rw [← Nat.card_zmod (Function.minimalPeriod _ _),
      ← Nat.card_congr (MulAction.orbitZPowersEquiv ℓ e₀'), horb, Nat.card_univ]
  -- the fibre of the Kummer covering
  let ζ := exp (2 * π * I / n)
  have hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_exp n hn
  have hiter (i : ℕ) (w : powRestrict B n ⁻¹' {b₀}) :
      (((ℓ • ·)^[i] w : powRestrict B n ⁻¹' {b₀}) : ℂ) = ζ ^ i * w := by
    induction i generalizing w with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      change ((hK.monodromy ℓ ((ℓ • ·)^[i] w) : {w : ℂ // w ^ n ∈ B}) : ℂ) = _
      rw [monodromy_generatorLoop_powRestrict hB0 hn, ih, pow_succ]
      ring
  have hwb (w : powRestrict B n ⁻¹' {b₀}) : (w : ℂ) ^ n = b₀ := congrArg Subtype.val w.2
  have hb₀ : (b₀ : ℂ) ≠ 0 := fun h ↦ hB0 (h ▸ b₀.2)
  have hroot : exp (log b₀ / n) ^ n = b₀ := by
    rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), exp_log hb₀]
  let w₀ : powRestrict B n ⁻¹' {b₀} :=
    ⟨⟨exp (log b₀ / n), by rw [hroot]; exact b₀.2⟩, Subtype.ext hroot⟩
  have hw0 (w : powRestrict B n ⁻¹' {b₀}) : (w : ℂ) ≠ 0 := by
    intro h
    have := hwb w
    rw [h, zero_pow hn] at this
    exact hb₀ this.symm
  have htK :
      MulAction.IsPretransitive (FundamentalGroup B b₀) (powRestrict B n ⁻¹' {b₀}) := by
    refine ⟨fun w w' ↦ ?_⟩
    have : NeZero n := ⟨hn⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (w' : ℂ) / w)
      (by rw [div_pow, hwb, hwb, div_self hb₀])
    refine ⟨ℓ ^ i, Subtype.ext (Subtype.ext ?_)⟩
    rw [← smul_iterate_apply, hiter, hi, div_mul_cancel₀ _ (hw0 w)]
  have hperK : Function.minimalPeriod (ℓ • ·) w₀ = n := by
    refine Nat.dvd_antisymm ?_ ?_
    · refine Function.IsPeriodicPt.minimalPeriod_dvd (Subtype.ext (Subtype.ext ?_))
      rw [hiter, hζ.pow_eq_one, one_mul]
    · have h := Function.isPeriodicPt_minimalPeriod (ℓ • ·) w₀
      have h' := congrArg (fun w : powRestrict B n ⁻¹' {b₀} ↦ (w : ℂ)) h
      simp only [hiter] at h'
      exact (hζ.pow_eq_one_iff_dvd _).mp
        (mul_eq_right₀ (hw0 w₀) |>.mp h')
  have hstab (γ : FundamentalGroup B b₀) : γ • e₀' = e₀' ↔ γ • w₀ = w₀ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen γ)
    rw [MulAction.zpow_smul_eq_iff_minimalPeriod_dvd,
      MulAction.zpow_smul_eq_iff_minimalPeriod_dvd, hperE, hperK]
  obtain ⟨Φ, hΦ⟩ := MulAction.exists_equiv_smul_of_forall_smul_eq_iff hstab
  -- the two finite coverings and the isomorphism between them
  let X := TopCat.of B
  let EC : TopCat.FiniteCovering X :=
    ⟨Over.mk (TopCat.ofHom ⟨p, hp.continuous⟩), hp, hfin⟩
  let KC : TopCat.FiniteCovering X :=
    ⟨Over.mk (TopCat.ofHom ⟨powRestrict B n, continuous_powRestrict B n⟩), hK,
      finite_powRestrict_preimage hn⟩
  let Φ' : (TopCat.FiniteCovering.fiber b₀).obj EC ≃ (TopCat.FiniteCovering.fiber b₀).obj KC :=
    Φ
  let i : (TopCat.FiniteCovering.monodromyAction b₀).obj EC ≅
      (TopCat.FiniteCovering.monodromyAction b₀).obj KC :=
    Action.mkIso (FintypeCat.equivEquivIso Φ') fun γ ↦ by
      ext x
      exact hΦ γ x
  have : PathConnectedSpace X := ‹PathConnectedSpace B›
  have : LocallyPathConnectedSpace X := (inferInstance : LocallyPathConnectedSpace B)
  have : SemilocallySimplyConnectedSpace X :=
    (inferInstance : SemilocallySimplyConnectedSpace B)
  -- `clear_value` keeps the elaborator from unfolding `preimageIso` below
  let j : EC ≅ KC :=
    (TopCat.FiniteCovering.equivalenceAction (X := X) b₀).fullyFaithfulFunctor.preimageIso i
  clear_value j
  let φ : E ≃ₜ {w : ℂ // w ^ n ∈ B} :=
    TopCat.homeoOfIso ((ObjectProperty.ι _ ⋙ Over.forget X).mapIso j)
  refine ⟨n, hn, φ, fun x ↦ ?_⟩
  exact ConcreteCategory.congr_hom (Over.w j.hom.hom) x

end Classification

end Complex
