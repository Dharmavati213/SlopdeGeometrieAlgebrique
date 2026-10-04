/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherPolyFamily

/-!
# The roots of a continuous family of separable polynomials form a covering

Let `C` be a topological space and `P : C → ℂ[X]` a family of monic separable polynomials of
degree `n` with continuous coefficients. The space of roots
`RiemannHigher.RootSpace P = {(c, y) | P_c(y) = 0}` is a covering of `C` with `n`-element fibres
(`RiemannHigher.isCoveringMap_rootSpace`): near every `c₀` the roots are `n` continuous, pairwise
distinct functions of `c` (`exists_continuousOn_roots`), and these trivialize the root space.

This is the topological model of the covering `Spec R[Y]/(P)` of `Spec R` in the induction step of
XII.5.1 in higher dimension (`SGA.SGA1.ExposeXII.RiemannHigher`).
-/
noncomputable section

open Polynomial Topology Set Filter

namespace SGA.SGA1.ExposeXII.RiemannHigher

variable {C : Type*} [TopologicalSpace C] {n : ℕ} (P : C → ℂ[X])

/-- The space of roots `{(c, y) | P_c(y) = 0}` of a family of polynomials. -/
abbrev RootSpace : Type _ := {y : C × ℂ // (P y.1).eval y.2 = 0}

/-- The projection of the root space to the parameter space. -/
abbrev rootProj (y : RootSpace P) : C := y.1.1

variable {P}

/-- The roots of a continuous family of monic separable polynomials of degree `n` form a covering
of the parameter space. -/
theorem isCoveringMap_rootSpace (hmonic : ∀ c, (P c).Monic) (hdeg : ∀ c, (P c).natDegree = n)
    (hcont : ∀ i, Continuous fun c ↦ (P c).coeff i) (hsep : ∀ c, (P c).Separable) :
    IsCoveringMap (rootProj P) := by
  classical
  intro c₀
  obtain ⟨W, s, ρ, hW, hs, hρ, hsep', hiff⟩ := exists_continuousOn_roots hmonic hdeg hcont hsep c₀
  -- a neighbourhood on which the roots stay `ρ / 2`-close to those at `c₀`
  have hcl : ∀ᶠ c in 𝓝 c₀, c ∈ W ∧ ∀ i, ‖s c i - s c₀ i‖ < ρ / 2 := by
    refine (show ∀ᶠ c in 𝓝 c₀, c ∈ W from hW).and ?_
    have hsc : ContinuousAt s c₀ := hs.continuousAt hW
    refine eventually_all.mpr fun i ↦ ?_
    have : ContinuousAt (fun c ↦ ‖s c i - s c₀ i‖) c₀ :=
      ((continuous_apply i).continuousAt.comp hsc |>.sub continuousAt_const).norm
    exact this.eventually (gt_mem_nhds (by simpa using half_pos hρ))
  obtain ⟨U, hUsub, hUo, hc₀U⟩ := mem_nhds_iff.mp hcl
  have hUW (c : C) (hc : c ∈ U) : c ∈ W := (hUsub hc).1
  have hUρ (c : C) (hc : c ∈ U) (i : Fin n) : ‖s c i - s c₀ i‖ < ρ / 2 := (hUsub hc).2 i
  -- the roots over `U` are the `s c i`
  have hroot (c : C) (hc : c ∈ U) (y : ℂ) : (P c).eval y = 0 ↔ ∃ i, y = s c i := by
    have := hiff c (hUW c hc) y
    constructor
    · intro h
      by_contra hne
      exact this.mpr (fun i hi ↦ hne ⟨i, hi⟩) h
    · rintro ⟨i, rfl⟩
      by_contra h
      exact this.mp h i rfl
  -- the index of a root near `c₀`
  have huniq (c : C) (hc : c ∈ U) (i j : Fin n) (y : ℂ) (hi : ‖y - s c₀ i‖ < ρ / 2)
      (hj : ‖y - s c₀ j‖ < ρ / 2) : i = j := by
    by_contra hij
    have := hsep' i j hij
    have : ‖s c₀ i - s c₀ j‖ < ρ := by
      calc ‖s c₀ i - s c₀ j‖ = ‖(y - s c₀ j) - (y - s c₀ i)‖ := by ring_nf
        _ ≤ ‖y - s c₀ j‖ + ‖y - s c₀ i‖ := norm_sub_le _ _
        _ < ρ / 2 + ρ / 2 := add_lt_add hj hi
        _ = ρ := add_halves ρ
    linarith
  have hex (y : {y : RootSpace P // rootProj P y ∈ U}) :
      ∃ i, ‖y.1.1.2 - s c₀ i‖ < ρ / 2 := by
    obtain ⟨i, hi⟩ := (hroot _ y.2 _).mp y.1.2
    exact ⟨i, by rw [hi]; exact hUρ _ y.2 i⟩
  let idx (y : {y : RootSpace P // rootProj P y ∈ U}) : Fin n := (hex y).choose
  have hidx (y : {y : RootSpace P // rootProj P y ∈ U}) : y.1.1.2 = s y.1.1.1 (idx y) := by
    obtain ⟨i, hi⟩ := (hroot _ y.2 _).mp y.1.2
    have : idx y = i := huniq _ y.2 _ _ _ (hex y).choose_spec (by rw [hi]; exact hUρ _ y.2 i)
    rw [this, hi]
  have hcontidx : Continuous idx := by
    refine continuous_def.mpr fun t _ ↦ ?_
    have : idx ⁻¹' t = ⋃ i ∈ t, {y | ‖y.1.1.2 - s c₀ i‖ < ρ / 2} := by
      ext y
      simp only [mem_preimage, mem_iUnion, exists_prop]
      constructor
      · intro hy
        exact ⟨idx y, hy, (hex y).choose_spec⟩
      · rintro ⟨i, hi, hy⟩
        have : idx y = i := huniq _ y.2 _ _ _ (hex y).choose_spec hy
        rw [this]
        exact hi
    rw [this]
    refine isOpen_biUnion fun i _ ↦ ?_
    exact isOpen_lt (by fun_prop) continuous_const
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Fin n)
    ⟨inferInstance, U, hc₀U, hUo, hUo.preimage (by fun_prop),
    { toFun y := (⟨rootProj P y.1, y.2⟩, idx y)
      invFun ci := ⟨⟨(ci.1.1, s ci.1.1 ci.2), (hroot _ ci.1.2 _).mpr ⟨ci.2, rfl⟩⟩, ci.1.2⟩
      left_inv y := by
        refine Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
        exact (hidx y).symm
      right_inv ci := by
        refine Prod.ext rfl ?_
        refine huniq _ ci.1.2 _ _ (s ci.1.1 ci.2) ?_ (hUρ _ ci.1.2 ci.2)
        have := (hex ⟨⟨(ci.1.1, s ci.1.1 ci.2), (hroot _ ci.1.2 _).mpr ⟨ci.2, rfl⟩⟩, ci.1.2⟩).choose_spec
        exact this
      continuous_toFun := by
        refine Continuous.prodMk (by fun_prop) hcontidx
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _) _
        have hsU : Continuous fun c : U ↦ s c := hs.mono (fun c hc ↦ hUW c hc) |>.domRestrict
        exact continuous_prod_of_discrete_right.mpr fun i ↦ (continuous_apply i).comp hsU },
      fun _ ↦ rfl⟩

omit [TopologicalSpace C] in
/-- The fibres of the root space are finite. -/
theorem finite_rootProj_preimage (hne : ∀ c, P c ≠ 0) (c : C) :
    (rootProj P ⁻¹' {c}).Finite := by
  refine Set.Finite.of_finite_image (f := fun y : RootSpace P ↦ y.1.2) ?_ ?_
  · refine (Polynomial.finite_setOfPred_isRoot (hne c)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hy
    change IsRoot (P c) y.1.2
    rw [← hy]
    exact y.2
  · intro y hy y' hy' h
    exact Subtype.ext (Prod.ext (hy.trans hy'.symm) h)

end SGA.SGA1.ExposeXII.RiemannHigher
