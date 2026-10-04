/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultFormSheaf
import SGA.Foundations.Analytic.Osgood

/-!
# The Dolbeault resolution of `𝒪` on `ℂ^σ`

A smooth function on an open subset of `ℂ^σ` with `∂f/∂z̄ⱼ = 0` for all `j` is holomorphic in each
variable (Cauchy–Riemann), hence analytic by Osgood's lemma
(`AnalyticGeometry.analyticAt_of_dbarPartial_eq_zero'`). So

  `0 → 𝒪 → 𝒞^{0,0} → Z¹ → 0`

is a short exact sequence of abelian sheaves (`AnalyticGeometry.holomorphicSeq_shortExact`), where
`𝒪 = holomorphicAbSheaf σ` is the sheaf of analytic functions. With the sequences
`0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0` (`dolbeaultSeq_shortExact`) this is the Dolbeault resolution of
`𝒪` by fine sheaves, and the cohomology of `𝒪` on an open set `V` vanishes in positive degrees as
soon as `∂̄` is globally exact on `V` in every positive degree
(`AnalyticGeometry.H'_holomorphicAbSheaf_subsingleton_of_dbarExact`; Dolbeault's theorem,
Hörmander, *An introduction to complex analysis in several variables*, 7.4).
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter Set
open scoped ContDiff

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [LinearOrder σ]

omit [LinearOrder σ] in
/-- **Smooth `∂̄`-closed functions are analytic** (Cauchy–Riemann in each variable and Osgood's
lemma). -/
theorem analyticAt_of_dbarPartial_eq_zero' [DecidableEq σ] {U : Set (σ → ℂ)} (hU : IsOpen U)
    {f : (σ → ℂ) → ℂ} (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hdf : ∀ y ∈ U, ∀ j, dbarPartial j f y = 0) {x : σ → ℂ} (hx : x ∈ U) :
    AnalyticAt ℂ f x := by
  refine analyticAt_of_continuousOn_of_separately hU
    (fun y hy ↦ (hf y hy).continuousAt.continuousWithinAt) (fun z hz j ↦ ?_) hx
  have hd : DifferentiableAt ℝ (fun t ↦ f (Function.update z j t)) (z j) := by
    have h1 : DifferentiableAt ℝ f (Function.update z j (z j)) := by
      rw [Function.update_eq_self]
      exact hf z hz
    exact h1.comp (z j) (hasFDerivAt_update z (z j)).differentiableAt
  have h0 := hdf z hz j
  rw [dbarPartial_eq_dbar_update (hf z hz) j] at h0
  exact (dbar_eq_zero_iff hd).mp h0

variable (σ) in
/-- `𝒪 ⟶ 𝒞^{0,0}`: a holomorphic function as a smooth `(0,0)`-form. -/
def holomorphicToForm : holomorphicAbSheaf σ ⟶ formSheaf σ 0 :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ⟨fun x _ ↦ (f : analyticSections ℂ U.unop).1 x, by
            have h := isSmoothOn_restrict (g := fun y (_ : {I : Finset σ // I.card = 0}) ↦
              extendByZero (f : analyticSections ℂ U.unop).1 y) U.unop.2 fun y hy ↦
                contDiffAt_pi.mpr fun _ ↦ (((f : analyticSections ℂ U.unop).2 ⟨y, hy⟩).contDiffAt
                  (n := ∞)).restrict_scalars ℝ
            have heq : (fun (x : U.unop) (_ : {I : Finset σ // I.card = 0}) ↦
                extendByZero (f : analyticSections ℂ U.unop).1 x) =
                fun x _ ↦ (f : analyticSections ℂ U.unop).1 x := by
              funext x I
              simp
            change IsSmoothOn _
            rw [← heq]
            exact h⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

omit [LinearOrder σ] in
lemma formCoeffs_holomorphicToForm {U : (Opens (TopCat.of (σ → ℂ)))ᵒᵖ}
    (f : (holomorphicAbSheaf σ).obj.obj U) (I : Finset σ) (y : σ → ℂ) :
    formCoeffs ((holomorphicToForm σ).hom.app U f).1 I y =
      if I.card = 0 then extendByZero (f : analyticSections ℂ U.unop).1 y else 0 := by
  by_cases hI : I.card = 0
  · rw [formCoeffs_of_card _ hI, ite_eq_left hI]
    by_cases hy : y ∈ (U.unop : Set (σ → ℂ))
    · rw [extendByZero_of_mem _ hy, extendByZero_of_mem _ hy]
      rfl
    · rw [extendByZero_of_notMem _ hy, extendByZero_of_notMem _ hy]
      rfl
  · rw [formCoeffs_of_card_ne _ hI, ite_eq_right hI]
    rfl

/-- `∂̄` kills holomorphic functions: `𝒪 ⟶ 𝒞^{0,0} ⟶ Z¹` is zero. -/
lemma holomorphicToForm_comp_dbarFormHom : holomorphicToForm σ ≫ dbarFormHom σ 0 = 0 := by
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  ext f
  refine Subtype.ext (funext fun x ↦ funext fun J ↦ ?_)
  change dbarForm (formCoeffs ((holomorphicToForm σ).hom.app U f).1) J.1 x = 0
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hfun : formCoeffs ((holomorphicToForm σ).hom.app U f).1 (J.1.erase j) =
      fun y ↦ if (J.1.erase j).card = 0 then extendByZero (f : analyticSections ℂ U.unop).1 y
        else 0 := funext fun y ↦ formCoeffs_holomorphicToForm f _ y
  rw [hfun]
  by_cases hc : (J.1.erase j).card = 0
  · simp only [ite_eq_left hc]
    rw [dbarPartial_eq_zero_of_differentiableAt j
      (((f : analyticSections ℂ U.unop).2 x).differentiableAt), mul_zero]
  · simp only [ite_eq_right hc]
    rw [show (fun _ : σ → ℂ ↦ (0 : ℂ)) = 0 from rfl, dbarPartial_zero, mul_zero]

variable (σ) in
/-- The sequence `0 → 𝒪 → 𝒞^{0,0} → Z¹ → 0`. -/
def holomorphicSeq :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
      AddCommGrpCat.{0}) :=
  ShortComplex.mk (holomorphicToForm σ) (dbarFormHom σ 0) holomorphicToForm_comp_dbarFormHom

/-- **The Dolbeault resolution of `𝒪`, first step**: `0 → 𝒪 → 𝒞^{0,0} → Z¹ → 0` is a short exact
sequence of abelian sheaves on `ℂ^σ`. -/
theorem holomorphicSeq_shortExact : (holomorphicSeq σ).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_sections (fun U f g h ↦ ?_) (fun U φ hφ ↦ ?_)
    (isLocallySurjective_dbarFormHom 0)
  · refine Subtype.ext (funext fun x ↦ ?_)
    have := congrFun (congrFun (congrArg Subtype.val h) x) ⟨∅, Finset.card_empty⟩
    exact this
  · -- a smooth `∂̄`-closed function is analytic
    set h : (σ → ℂ) → ℂ := formCoeffs φ.1 ∅ with hhdef
    have hsm : ∀ y ∈ (U.unop : Set (σ → ℂ)), DifferentiableAt ℝ h y := fun y hy ↦
      (φ.2.isSmoothFormAt hy).differentiableAt ∅
    have hdb : ∀ y ∈ (U.unop : Set (σ → ℂ)), ∀ j, dbarPartial j h y = 0 := by
      intro y hy j
      have h0 := congrFun (congrFun (congrArg Subtype.val hφ) ⟨y, hy⟩)
        ⟨{j}, Finset.card_singleton j⟩
      change dbarForm (formCoeffs φ.1) {j} y = 0 at h0
      rw [dbarForm, Finset.sum_singleton, Finset.erase_singleton] at h0
      exact (mul_eq_zero.mp h0).resolve_left (koszulSign_ne_zero _ _)
    have han : ∀ y ∈ (U.unop : Set (σ → ℂ)), AnalyticAt ℂ h y := fun y hy ↦
      analyticAt_of_dbarPartial_eq_zero' U.unop.2 hsm hdb hy
    refine ⟨(⟨fun x ↦ h x, isAnalyticOn_restrict U.unop.2 han⟩ : analyticSections ℂ U.unop), ?_⟩
    refine Subtype.ext (funext fun x ↦ funext fun I ↦ ?_)
    have hI : I = ⟨∅, Finset.card_empty⟩ := Subtype.ext (Finset.card_eq_zero.mp I.2)
    subst hI
    change h x = φ.1 x ⟨∅, Finset.card_empty⟩
    rw [hhdef, formCoeffs_of_card _ Finset.card_empty, extendByZero_of_mem _ x.2]
    rfl

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
  AddCommGrpCat.{0})]

/-- **Dolbeault's theorem, vanishing form**: if on an open set `V ⊆ ℂ^σ` every smooth
`∂̄`-closed `(0, q + 1)`-form is `∂̄` of a smooth `(0, q)`-form on `V` (for all `q`), then
`Hⁿ(V, 𝒪) = 0` for all `n > 0`. -/
theorem H'_holomorphicAbSheaf_subsingleton_of_dbarExact (V : Opens (TopCat.of (σ → ℂ)))
    (hV : ∀ q, DbarExactOn (V : Set (σ → ℂ)) q) (n : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (n + 1) V) := by
  cases n with
  | zero =>
    refine TopCat.Sheaf.subsingleton_H'_one_of_shortExact holomorphicSeq_shortExact V
      (H'_smoothSheaf_subsingleton 0 V) fun g ↦ ?_
    obtain ⟨u, hu, hdu⟩ := hV 0 g.1 g.2
    exact ⟨⟨u, hu⟩, Subtype.ext hdu⟩
  | succ n =>
    exact TopCat.Sheaf.subsingleton_H'_succ_succ_of_shortExact holomorphicSeq_shortExact V n
      (H'_closedFormSheaf_subsingleton V hV n 1) (H'_smoothSheaf_subsingleton (n + 1) V)

end AnalyticGeometry
