/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurves
import SGA.SGA1.ExposeXII.EntirePolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Normed.Module.Connected

/-!
# SGA 1, Exposé XII, 5.1 for curves: symmetric functions on finite coverings of `ℂ ∖ S`

Let `S ⊂ ℂ` be finite and `p : E → ℂ ∖ S` a finite covering. For `F : E → ℂ`, the *fibrewise
characteristic polynomial* `P_F(z) = ∏_{p(e) = z} (T - F(e))` (`PuncturedPlane.fiberCharpoly`) has
`F` as a root over every point. If `F` is holomorphic on `E` (along continuous local sections of
`p`, `PuncturedPlane.IsHolomorphic`) and of moderate growth at the punctures and at infinity
(`PuncturedPlane.IsModerate`), the coefficients of `P_F` are rational functions of `z` with poles
in `S` (`PuncturedPlane.exists_coeff_fiberCharpoly_mul_eq_eval`): they are holomorphic on
`ℂ ∖ S` (symmetric functions of `F` along local sections), and of polynomial growth after
multiplication by a power of `∏_{a ∈ S} (z - a)`, hence polynomials by Riemann's removable
singularity theorem and Liouville's theorem (`exists_polynomial_of_differentiableOn`).

This is the step "the symmetric functions of `F` are regular functions on `ℂ ∖ S`" of the
algebraic half of this project's proof of XII.5.1 for curves (not SGA's route, which goes through
resolution of singularities and GAGA or the Grauert–Remmert theorem, see
`SGA.SGA1.ExposeXII.RiemannCurves`). The two predicates are the clauses of
`SeparatingFunctionStatement` and `FiberSeparatingFunctionStatement`.

The file also states `FiberSeparatingFunctionStatement`, the analytic heart in the form the
algebraic half uses: a separating function for *every* fibre (it implies
`SeparatingFunctionStatement`, and follows from `CompactRiemannSurfaceMeromorphicStatement` in
the same way). It is proved: `fiberSeparatingFunction` (`SGA.SGA1.ExposeXII.GAGAFiberSeparating`).
-/

noncomputable section

open Polynomial Topology Set Filter

namespace SGA.SGA1.ExposeXII

namespace PuncturedPlane

variable {S : Finset ℂ} {E : Type*} [TopologicalSpace E] (p : E → {z : ℂ // z ∉ S})

/-- `F : E → ℂ` is holomorphic on a covering `p : E → ℂ ∖ S`: `F ∘ s` is holomorphic for every
continuous local section `s` of `p` over an open `U ⊆ ℂ ∖ S` (the holomorphy clause of
`SeparatingFunctionStatement`). -/
def IsHolomorphic (F : E → ℂ) : Prop :=
  ∀ (U : Set ℂ) (_ : IsOpen U) (_ : ∀ z ∈ U, z ∉ S) (s : U → E), Continuous s →
    (∀ z : U, (p (s z) : ℂ) = z) →
      DifferentiableOn ℂ (Function.extend (fun z : U ↦ (z : ℂ)) (F ∘ s) 0) U

/-- `F : E → ℂ` has moderate growth at the punctures `S` and at infinity:
`‖F e‖ * ∏_{a ∈ S} ‖p e - a‖ ^ N ≤ C * (1 + ‖p e‖) ^ (N * (|S| + 1))` (the growth clause of
`SeparatingFunctionStatement`). -/
def IsModerate (F : E → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ e, ‖F e‖ * ∏ a ∈ S, ‖(p e : ℂ) - a‖ ^ N ≤
    C * (1 + ‖(p e : ℂ)‖) ^ (N * (S.card + 1))

variable {p} (hfin : ∀ z, (p ⁻¹' {z}).Finite)

/-- The fibrewise characteristic polynomial `∏_{p(e) = z} (T - F(e))` of `F : E → ℂ`. -/
def fiberCharpoly (F : E → ℂ) (z : {z : ℂ // z ∉ S}) : ℂ[X] :=
  ∏ e ∈ (hfin z).toFinset, (X - C (F e))

variable (F : E → ℂ)

omit [TopologicalSpace E] in
lemma monic_fiberCharpoly (z : {z : ℂ // z ∉ S}) : (fiberCharpoly hfin F z).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

omit [TopologicalSpace E] in
lemma natDegree_fiberCharpoly (z : {z : ℂ // z ∉ S}) :
    (fiberCharpoly hfin F z).natDegree = (hfin z).toFinset.card := by
  rw [fiberCharpoly, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp

omit [TopologicalSpace E] in
lemma eval_fiberCharpoly_self (e : E) : (fiberCharpoly hfin F (p e)).eval (F e) = 0 := by
  rw [fiberCharpoly, eval_prod]
  exact Finset.prod_eq_zero (i := e) (by simp) (by simp)

omit [TopologicalSpace E] in
lemma roots_fiberCharpoly (z : {z : ℂ // z ∉ S}) :
    (fiberCharpoly hfin F z).roots = (hfin z).toFinset.val.map F := by
  rw [fiberCharpoly, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C
    ((hfin z).toFinset.val.map F), Multiset.map_map]
  rfl

/-- Every coefficient of `∏_{i ∈ s} (T - g_i(z))` is holomorphic where the `g_i` are. -/
lemma differentiableOn_coeff_prod {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) {U : Set ℂ}
    (hg : ∀ i ∈ s, DifferentiableOn ℂ (g i) U) (k : ℕ) :
    DifferentiableOn ℂ (fun z ↦ (∏ i ∈ s, (X - C (g i z))).coeff k) U := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  | insert a s has ih =>
    have hs : ∀ i ∈ s, DifferentiableOn ℂ (g i) U := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    have ha : DifferentiableOn ℂ (g a) U := hg a (Finset.mem_insert_self a s)
    simp_rw [Finset.prod_insert has]
    rcases k with _ | k
    · simp_rw [mul_comm (X - C _), mul_sub, coeff_sub, mul_comm _ X, coeff_X_mul_zero, zero_sub,
        coeff_mul_C]
      exact ((ih hs 0).mul ha).neg
    · simp_rw [mul_comm (X - C _), coeff_mul_X_sub_C]
      exact (ih hs k).sub ((ih hs (k + 1)).mul ha)

variable {F}

/-- Near every point `z₀` of `ℂ ∖ S`, the fibrewise characteristic polynomial of any `G` is
`∏_i (T - G(s_i(z)))` for continuous local sections `s_i` of `p`, indexed by the fibre over
`z₀`. -/
lemma exists_fiberCharpoly_eq_prod (hp : IsCoveringMap p) (z₀ : {z : ℂ // z ∉ S}) :
    ∃ (U : Set ℂ), IsOpen U ∧ (z₀ : ℂ) ∈ U ∧ (∀ z ∈ U, z ∉ S) ∧
      ∃ s : (hfin z₀).toFinset → U → E, (∀ i, Continuous (s i)) ∧
        (∀ i z, (p (s i z) : ℂ) = z) ∧
        ∀ (G : E → ℂ) (z : U) (hz : (z : ℂ) ∉ S),
          fiberCharpoly hfin G ⟨z, hz⟩ = ∏ i ∈ (hfin z₀).toFinset.attach, (X - C (G (s i z))) := by
  obtain ⟨_, V, hz₀V, hV, -, H, hH⟩ := hp z₀
  let U : Set ℂ := {z | ∃ h : z ∉ S, (⟨z, h⟩ : {z : ℂ // z ∉ S}) ∈ V}
  have hUV : U = Subtype.val '' V := by
    ext z
    constructor
    · rintro ⟨h, hz⟩
      exact ⟨_, hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, hv⟩
  have hSo : IsOpen ((↑S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hUo : IsOpen U := by
    rw [hUV]
    exact hSo.isOpenMap_subtype_val V hV
  let v : U → V := fun z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  have hv : Continuous v :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  let idx : (hfin z₀).toFinset → p ⁻¹' {z₀} := fun i ↦ ⟨i.1, (hfin z₀).mem_toFinset.mp i.2⟩
  let s : (hfin z₀).toFinset → U → E := fun i z ↦ (H.symm (v z, idx i)).1
  have hs : ∀ i, Continuous (s i) := fun i ↦
    continuous_subtype_val.comp (H.symm.continuous.comp (hv.prodMk continuous_const))
  have hps : ∀ i z, p (s i z) = (v z).1 := fun i z ↦ by
    rw [← hH, Homeomorph.apply_symm_apply]
  refine ⟨U, hUo, ⟨z₀.2, hz₀V⟩, fun z hz ↦ hz.1, s, hs, fun i z ↦ by rw [hps], ?_⟩
  intro G z hz
  rw [fiberCharpoly]
  have hmem (e : E) (he : e ∈ (hfin ⟨z, hz⟩).toFinset) : e ∈ p ⁻¹' V := by
    have : p e = ⟨z, hz⟩ := (hfin _).mem_toFinset.mp he
    change p e ∈ V
    rw [this]
    exact z.2.2
  have hleft (e : E) (he : e ∈ (hfin ⟨z, hz⟩).toFinset) :
      s ⟨(H ⟨e, hmem e he⟩).2.1, (hfin z₀).mem_toFinset.mpr (H ⟨e, hmem e he⟩).2.2⟩ z = e := by
    have h1 : v z = (H ⟨e, hmem e he⟩).1 :=
      Subtype.ext (by rw [hH]; exact ((hfin _).mem_toFinset.mp he).symm)
    change (H.symm (v z, idx _)).1 = e
    have h2 : idx ⟨(H ⟨e, hmem e he⟩).2.1, (hfin z₀).mem_toFinset.mpr (H ⟨e, hmem e he⟩).2.2⟩ =
        (H ⟨e, hmem e he⟩).2 := rfl
    rw [h1, h2, Prod.mk.eta, Homeomorph.symm_apply_apply]
  refine Finset.prod_bij' (fun e he ↦ ⟨(H ⟨e, hmem e he⟩).2.1,
      (hfin z₀).mem_toFinset.mpr (H ⟨e, hmem e he⟩).2.2⟩)
    (fun i _ ↦ s i z) (fun _ _ ↦ Finset.mem_attach _ _) ?_ hleft ?_ ?_
  · intro i _
    refine (hfin _).mem_toFinset.mpr (Subtype.ext ?_)
    rw [hps]
  · intro i _
    refine Subtype.ext ?_
    change (H ⟨(H.symm (v z, idx i)).1, _⟩).2.1 = i.1
    simp [idx]
  · intro e he
    rw [hleft e he]

variable (F) in
/-- The `k`-th coefficient of the fibrewise characteristic polynomial of `F`, as a function on
`ℂ` (`0` on `S`). -/
def coeffFun (k : ℕ) (z : ℂ) : ℂ :=
  if hz : z ∉ S then (fiberCharpoly hfin F ⟨z, hz⟩).coeff k else 0

omit [TopologicalSpace E] in
lemma coeffFun_of_notMem (k : ℕ) {z : ℂ} (hz : z ∉ S) :
    coeffFun hfin F k z = (fiberCharpoly hfin F ⟨z, hz⟩).coeff k := by
  simp [coeffFun, hz]

/-- The coefficients of the fibrewise characteristic polynomial of a holomorphic `F` are
holomorphic on `ℂ ∖ S` (symmetric functions of `F` along local sections). -/
theorem differentiableOn_coeffFun (hp : IsCoveringMap p) (hF : IsHolomorphic p F) (k : ℕ) :
    DifferentiableOn ℂ (coeffFun hfin F k) (↑S)ᶜ := by
  intro z₀ hz₀
  obtain ⟨U, hU, hz₀U, hUS, s, hs, hps, heq⟩ := exists_fiberCharpoly_eq_prod hfin hp ⟨z₀, hz₀⟩
  let g : (hfin ⟨z₀, hz₀⟩).toFinset → ℂ → ℂ :=
    fun i ↦ Function.extend (fun z : U ↦ (z : ℂ)) (F ∘ s i) 0
  have hg : ∀ i ∈ (hfin ⟨z₀, hz₀⟩).toFinset.attach, DifferentiableOn ℂ (g i) U :=
    fun i _ ↦ hF U hU hUS (s i) (hs i) (hps i)
  have hd := differentiableOn_coeff_prod _ g hg k
  have heq' : coeffFun hfin F k =ᶠ[𝓝 z₀]
      fun z ↦ (∏ i ∈ (hfin ⟨z₀, hz₀⟩).toFinset.attach, (X - C (g i z))).coeff k := by
    filter_upwards [hU.mem_nhds hz₀U] with z hz
    rw [coeffFun_of_notMem hfin k (hUS z hz), heq F ⟨z, hz⟩ (hUS z hz)]
    have hgz : ∀ i, g i z = F (s i ⟨z, hz⟩) := fun i ↦
      Subtype.val_injective.extend_apply (F ∘ s i) 0 (⟨z, hz⟩ : U)
    simp only [hgz]
  exact (((hd z₀ hz₀U).differentiableAt (hU.mem_nhds hz₀U)).congr_of_eventuallyEq
    heq').differentiableWithinAt

omit [TopologicalSpace E] in
lemma preconnectedSpace_compl : PreconnectedSpace {z : ℂ // z ∉ S} := by
  have h : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact isPreconnected_iff_preconnectedSpace.mp
    (S.finite_toSet.countable.isPathConnected_compl_of_one_lt_rank h).isConnected.isPreconnected

/-- The fibres of a finite covering of `ℂ ∖ S` all have the same cardinality (`ℂ ∖ S` is
connected). -/
theorem card_fiber_eq (hp : IsCoveringMap p) (z z' : {z : ℂ // z ∉ S}) :
    (hfin z).toFinset.card = (hfin z').toFinset.card := by
  have := preconnectedSpace_compl (S := S)
  have hlc : IsLocallyConstant fun z ↦ (hfin z).toFinset.card := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z₀
    obtain ⟨U, hU, hz₀U, hUS, s, -, -, heq⟩ := exists_fiberCharpoly_eq_prod hfin hp z₀
    refine ⟨{z | (z : ℂ) ∈ U}, hU.preimage continuous_subtype_val, hz₀U, fun z hz ↦ ?_⟩
    have h1 := heq (fun _ ↦ 0) ⟨z, hz⟩ z.2
    rw [← natDegree_fiberCharpoly hfin (fun _ ↦ (0 : ℂ)) z, h1,
      natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
    simp
  exact hlc.apply_eq_of_preconnectedSpace z z'

/-- The coefficients of the fibrewise characteristic polynomial of a holomorphic `F` of moderate
growth are rational functions with poles in `S`: `c_k(z) ∏_{a ∈ S} (z - a)ᴹ` is a polynomial. -/
theorem exists_coeff_fiberCharpoly_mul_eq_eval (hp : IsCoveringMap p) (hF : IsHolomorphic p F)
    (hb : IsModerate p F) (k : ℕ) : ∃ (q : ℂ[X]) (M : ℕ), ∀ z : {z : ℂ // z ∉ S},
      (fiberCharpoly hfin F z).coeff k * ∏ a ∈ S, ((z : ℂ) - a) ^ M = q.eval (z : ℂ) := by
  obtain ⟨z₁, hz₁⟩ := S.exists_notMem
  let d := (hfin ⟨z₁, hz₁⟩).toFinset.card
  obtain ⟨C₀, N, hCN⟩ := hb
  let K₀ : ℝ := ∏ a ∈ S, (1 + ‖a‖) ^ N
  let G : ℂ → ℂ := fun z ↦ coeffFun hfin F k z * ∏ a ∈ S, (z - a) ^ (N * d)
  have hG : DifferentiableOn ℂ G (↑S)ᶜ :=
    (differentiableOn_coeffFun hfin hp hF k).mul (by fun_prop)
  have hbound : ∀ z ∉ S, ‖G z‖ ≤
      (max C₀ K₀ ^ d * d.choose (d / 2)) * (1 + ‖z‖) ^ (N * (S.card + 1) * d) := by
    intro z hz
    let w : {z : ℂ // z ∉ S} := ⟨z, hz⟩
    let P : ℝ := ∏ a ∈ S, ‖z - a‖ ^ N
    let Q : ℝ := (1 + ‖z‖) ^ (N * (S.card + 1))
    have hP : 0 < P := Finset.prod_pos fun a ha ↦ pow_pos (norm_pos_iff.mpr
      (sub_ne_zero.mpr fun h ↦ hz (by rwa [h]))) _
    have hQ : 1 ≤ Q := one_le_pow₀ (by linarith [norm_nonneg z])
    have hPK : P ≤ K₀ * Q := by
      have h1 : P ≤ ∏ a ∈ S, ((1 + ‖a‖) ^ N * (1 + ‖z‖) ^ N) :=
        Finset.prod_le_prod (fun a _ ↦ by positivity) fun a _ ↦ by
          rw [← mul_pow]
          gcongr
          calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ (1 + ‖a‖) * (1 + ‖z‖) := by nlinarith [norm_nonneg z, norm_nonneg a]
      rw [Finset.prod_mul_distrib, Finset.prod_const] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by nlinarith)
    have hd : (fiberCharpoly hfin F w).natDegree = d := by
      rw [natDegree_fiberCharpoly, card_fiber_eq hfin hp w]
    have hroots : ∀ r ∈ (map (RingHom.id ℂ) (fiberCharpoly hfin F w)).roots, ‖r‖ ≤ C₀ * Q / P := by
      intro r hr
      rw [Polynomial.map_id, roots_fiberCharpoly, Multiset.mem_map] at hr
      obtain ⟨e, he, rfl⟩ := hr
      have hpe : p e = w := (hfin w).mem_toFinset.mp he
      rw [le_div_iff₀ hP]
      have := hCN e
      rw [hpe] at this
      exact this
    have hcoeff := coeff_bdd_of_roots_le (RingHom.id ℂ) (monic_fiberCharpoly hfin F w)
      (IsAlgClosed.splits _) hd.le hroots k
    rw [Polynomial.map_id] at hcoeff
    have hGz : ‖G z‖ = ‖(fiberCharpoly hfin F w).coeff k‖ * P ^ d := by
      simp only [G, coeffFun_of_notMem hfin k hz, norm_mul, norm_prod, norm_pow, P]
      rw [← Finset.prod_pow]
      simp_rw [← pow_mul]
      rfl
    rw [hGz]
    calc ‖(fiberCharpoly hfin F w).coeff k‖ * P ^ d
        ≤ max (C₀ * Q / P) 1 ^ d * d.choose (d / 2) * P ^ d := by gcongr
      _ = (max (C₀ * Q / P) 1 * P) ^ d * d.choose (d / 2) := by ring
      _ = max (C₀ * Q) P ^ d * d.choose (d / 2) := by
          rw [max_mul_of_nonneg _ _ hP.le, div_mul_cancel₀ _ hP.ne', one_mul]
      _ ≤ (max C₀ K₀ * Q) ^ d * d.choose (d / 2) := by
          gcongr
          refine max_le ?_ (hPK.trans ?_)
          · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
          · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
      _ = (max C₀ K₀ ^ d * d.choose (d / 2)) * (1 + ‖z‖) ^ (N * (S.card + 1) * d) := by
          rw [mul_pow, pow_mul]
          ring
  obtain ⟨q, -, hq⟩ := exists_polynomial_of_differentiableOn S hG hbound
  refine ⟨q, N * d, fun z ↦ ?_⟩
  rw [← hq z z.2]
  simp only [G, coeffFun_of_notMem hfin k z.2]

end PuncturedPlane

/-- The analytic heart of the Riemann existence theorem for curves, in the language of coverings,
*fibre by fibre*: let `S ⊂ ℂ` be finite and `p : E → ℂ ∖ S` a connected finite
covering. Then for every `z ∈ ℂ ∖ S` there is `F : E → ℂ`, continuous, holomorphic on `E`
(`PuncturedPlane.IsHolomorphic`) and of moderate growth at the punctures and at infinity
(`PuncturedPlane.IsModerate`), which is injective on the fibre over `z`.

This is the form the algebraic half of the proof uses: over the open set where `F` separates the
fibres, `E` is the covering defined by the equation `P_F(z, T) = 0`, `P_F` the fibrewise
characteristic polynomial of `F` (`PuncturedPlane.exists_coeff_fiberCharpoly_mul_eq_eval`), and
these open sets cover `ℂ ∖ S`. It implies `SeparatingFunctionStatement`
(`separatingFunctionStatement_of_fiberSeparatingFunctionStatement`). Classically it follows from
`CompactRiemannSurfaceMeromorphicStatement` as `SeparatingFunctionStatement` does: in the compact
Riemann surface `Ē` obtained by filling in the punctures of `E`, let `e₁, …, eₙ` be the fibre over
`z` and `fₖ` a meromorphic function with a single pole, of order `mₖ`, at `eₖ`; then
`gₖ = (t - z)^{mₖ} fₖ` is holomorphic on `E`, vanishes at the `eⱼ`, `j ≠ k`, and not at `eₖ`, so
`F = ∑ₖ k gₖ / gₖ(eₖ)` takes the value `k` at `eₖ`. Proved this way: `fiberSeparatingFunction`
(`SGA.SGA1.ExposeXII.GAGAFiberSeparating`), from the compactification of `E`
(`fiberSeparatingFunctionStatement_of_compactification`,
`SGA.SGA1.ExposeXII.RiemannCurvesCompactification`). -/
def FiberSeparatingFunctionStatement : Prop :=
  ∀ (S : Finset ℂ) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
    (p : E → {z : ℂ // z ∉ S}), IsCoveringMap p → (∀ z, (p ⁻¹' {z}).Finite) →
    ∀ z, ∃ F : E → ℂ, Continuous F ∧ PuncturedPlane.IsHolomorphic p F ∧
      PuncturedPlane.IsModerate p F ∧ Set.InjOn F (p ⁻¹' {z})

/-- Separating every fibre implies separating one fibre. -/
theorem separatingFunctionStatement_of_fiberSeparatingFunctionStatement
    (H : FiberSeparatingFunctionStatement) : SeparatingFunctionStatement := by
  intro S E _ _ p hp hfin
  obtain ⟨z₁, hz₁⟩ := S.exists_notMem
  obtain ⟨F, hF, hhol, hmod, hinj⟩ := H S E p hp hfin ⟨z₁, hz₁⟩
  exact ⟨F, hF, hhol, hmod, ⟨z₁, hz₁⟩, hinj⟩

end SGA.SGA1.ExposeXII
