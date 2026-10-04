/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultSheaf
import SGA.Foundations.Analytic.Statements
import SGA.Foundations.Analytic.DolbeaultDisc

/-!
# The Dolbeault sequence `0 → 𝒪 → 𝒞^∞ → 𝒞^∞ → 0` in one variable

On `ℂ^σ` the Wirtinger derivative in the `j`-th coordinate, `∂f/∂z̄ⱼ = (∂f/∂xⱼ + i ∂f/∂yⱼ)/2`, is
`AnalyticGeometry.dbarPartial j f`. It is local, sends smooth functions to smooth functions and
kills holomorphic functions, so it gives morphisms of abelian sheaves
`AnalyticGeometry.holomorphicToSmooth σ : 𝒪 ⟶ 𝒞^∞` and
`AnalyticGeometry.dbarPartialHom σ j : 𝒞^∞ ⟶ 𝒞^∞` on `ℂ^σ`.

In one variable (`σ` with a unique element) the sequence `0 → 𝒪 → 𝒞^∞ → 𝒞^∞ → 0` (the Dolbeault
resolution of `𝒪`) is a short exact sequence of abelian sheaves
(`AnalyticGeometry.dolbeaultShortComplex_shortExact`): a smooth function with `∂f/∂z̄ = 0` is
holomorphic, hence analytic (Cauchy–Riemann, `dbar_eq_zero_iff`, and
`DifferentiableOn.analyticAt`), and `∂/∂z̄` is locally onto by Dolbeault's lemma
(`exists_contDiff_dbar_eq_on_ball`). Since `𝒞^∞` is acyclic
(`AnalyticGeometry.H'_smoothSheaf_subsingleton`), `Hⁿ(V, 𝒪) = 0` for `n > 0` on every open
`V ⊆ ℂ` on which `∂/∂z̄` is onto (`AnalyticGeometry.H'_holomorphicAbSheaf_subsingleton_of_dbar`),
in particular on discs (`AnalyticGeometry.H'_polydiscProduct_one_zero_zero_subsingleton`: the
case `c = 1`, `a = b = 0` of `AnalyticGeometry.PolydiscProductVanishingStatement`).

References: Hörmander, *An introduction to complex analysis in several variables*, 1.4.4 and 7.4;
Forster, *Lectures on Riemann surfaces*, 13.2 and 15.

Several variables need the Dolbeault–Grothendieck lemma with parameters and are not treated here.
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter Set Metric
open scoped ContDiff

namespace AnalyticGeometry

section Partial

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The Wirtinger derivative `∂f/∂z̄ⱼ = (∂f/∂xⱼ + i ∂f/∂yⱼ) / 2` of `f : ℂ^σ → ℂ` at `z`, computed
from the real derivative. -/
def dbarPartial (j : σ) (f : (σ → ℂ) → ℂ) (z : σ → ℂ) : ℂ :=
  dbarCLM ((fderiv ℝ f z).comp (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) j))

omit [Fintype σ] in
lemma dbarPartial_congr {j : σ} {f g : (σ → ℂ) → ℂ} {z : σ → ℂ} (h : f =ᶠ[𝓝 z] g) :
    dbarPartial j f z = dbarPartial j g z := by
  simp only [dbarPartial, h.fderiv_eq]

omit [Fintype σ] in
lemma dbarPartial_add [Finite σ] {j : σ} {f g : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (f + g) z = dbarPartial j f z + dbarPartial j g z := by
  have := Fintype.ofFinite σ
  simp only [dbarPartial, fderiv_add hf hg, ContinuousLinearMap.add_comp, map_add]

omit [Fintype σ] in
lemma dbarPartial_sub [Finite σ] {j : σ} {f g : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (f - g) z = dbarPartial j f z - dbarPartial j g z := by
  have := Fintype.ofFinite σ
  simp only [dbarPartial, fderiv_sub hf hg, ContinuousLinearMap.sub_comp, map_sub]

omit [Fintype σ] in
lemma dbarPartial_neg [Finite σ] {j : σ} {f : (σ → ℂ) → ℂ} {z : σ → ℂ} :
    dbarPartial j (-f) z = -dbarPartial j f z := by
  have := Fintype.ofFinite σ
  simp only [dbarPartial, fderiv_neg, ContinuousLinearMap.neg_comp, map_neg]

omit [Fintype σ] in
lemma dbarPartial_zero (j : σ) (z : σ → ℂ) : dbarPartial j 0 z = 0 := by
  simp [dbarPartial, Pi.zero_def]

/-- `∂f/∂z̄ⱼ` is smooth where `f` is. -/
lemma contDiffAt_dbarPartial (j : σ) {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (dbarPartial j f) z := by
  let Φ : ((σ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ := dbarCLM.comp
    ((ContinuousLinearMap.compL ℝ ℂ (σ → ℂ) ℂ).flip
      (ContinuousLinearMap.single ℝ (fun _ : σ ↦ ℂ) j))
  have : dbarPartial j f = fun z ↦ Φ (fderiv ℝ f z) := rfl
  rw [this]
  exact Φ.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

omit [Fintype σ] in
/-- A holomorphic function has `∂f/∂z̄ⱼ = 0`. -/
lemma dbarPartial_eq_zero_of_differentiableAt [Finite σ] (j : σ) {f : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℂ f z) : dbarPartial j f z = 0 := by
  have := Fintype.ofFinite σ
  rw [dbarPartial, hf.fderiv_restrictScalars ℝ, dbarCLM_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.single_apply]
  have : (Pi.single j Complex.I : σ → ℂ) = Complex.I • Pi.single j (1 : ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, (fderiv ℂ f z).map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

omit [Fintype σ] in
/-- In one variable, `∂f/∂z̄` is the Wirtinger derivative of `f` read in the coordinate. -/
lemma dbarPartial_eq_dbar [Unique σ] (f : (σ → ℂ) → ℂ) (z : σ → ℂ) :
    dbarPartial default f z =
      dbar (f ∘ (ContinuousLinearEquiv.funUnique σ ℂ ℂ).symm) (z default) := by
  set e : (σ → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique σ ℝ ℂ
  have he : ⇑(ContinuousLinearEquiv.funUnique σ ℂ ℂ).symm = ⇑e.symm := rfl
  have hz : e.symm (z default) = z := by
    funext i
    rw [Unique.eq_default i]
    rfl
  rw [he, dbar_eq_dbarCLM, e.symm.comp_right_fderiv, hz, dbarPartial]
  congr 2
  ext t i
  rw [Unique.eq_default i]
  simp [e]

end Partial

/-! ### The sheaf morphisms `𝒪 ⟶ 𝒞^∞` and `∂/∂z̄ⱼ : 𝒞^∞ ⟶ 𝒞^∞` -/

section Sheaves

variable (σ : Type) [Fintype σ]

variable {σ} in
/-- An analytic function on a subset of `ℂ^σ` is smooth. -/
lemma IsAnalyticOn.isSmoothOn {U : Set (σ → ℂ)} {f : U → ℂ} (hf : IsAnalyticOn ℂ f) :
    IsSmoothOn f :=
  fun x ↦ ((hf x).contDiffAt (n := ∞)).restrict_scalars ℝ

/-- The inclusion `𝒪 ⟶ 𝒞^∞` of holomorphic functions into smooth functions on `ℂ^σ`, as a
morphism of abelian sheaves. -/
def holomorphicToSmooth : holomorphicAbSheaf σ ⟶ smoothSheaf (σ → ℂ) ℂ :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ⟨(f : analyticSections ℂ U.unop).1,
            (f : analyticSections ℂ U.unop).2.isSmoothOn⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

variable {σ}

@[simp] lemma holomorphicToSmooth_app_apply {U : (Opens (TopCat.of (σ → ℂ)))ᵒᵖ}
    (f : (holomorphicAbSheaf σ).obj.obj U) (x : U.unop) :
    ((holomorphicToSmooth σ).hom.app U f).1 x = (f : analyticSections ℂ U.unop).1 x := rfl

lemma holomorphicToSmooth_app_injective (U : (Opens (TopCat.of (σ → ℂ)))ᵒᵖ) :
    Function.Injective ((holomorphicToSmooth σ).hom.app U) := fun _ _ h ↦
  Subtype.ext (congrArg Subtype.val h :)

variable [DecidableEq σ]

/-- `∂/∂z̄ⱼ` of a smooth function on an open set, as a smooth function. -/
def dbarPartialSmooth (j : σ) {U : Opens (σ → ℂ)} (f : smoothSections (σ → ℂ) ℂ U) :
    smoothSections (σ → ℂ) ℂ U :=
  ⟨fun x ↦ dbarPartial j (extendByZero f.1) x,
    isSmoothOn_restrict U.2 fun x hx ↦ contDiffAt_dbarPartial j (by
      simpa using f.2 ⟨x, hx⟩)⟩

lemma dbarPartialSmooth_apply (j : σ) {U : Opens (σ → ℂ)} (f : smoothSections (σ → ℂ) ℂ U)
    (x : U) : (dbarPartialSmooth j f).1 x = dbarPartial j (extendByZero f.1) x := rfl

variable (σ) in
/-- `∂/∂z̄ⱼ : 𝒞^∞ ⟶ 𝒞^∞` on `ℂ^σ`, as a morphism of abelian sheaves. -/
def dbarPartialHom (j : σ) : smoothSheaf (σ → ℂ) ℂ ⟶ smoothSheaf (σ → ℂ) ℂ :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ dbarPartialSmooth j f
          map_zero' := by
            refine Subtype.ext (funext fun x ↦ ?_)
            change dbarPartial j (extendByZero (0 : U.unop → ℂ)) x = 0
            rw [extendByZero_zero, dbarPartial_zero]
          map_add' := fun f g ↦ by
            refine Subtype.ext (funext fun x ↦ ?_)
            change dbarPartial j (extendByZero (f.1 + g.1)) x =
              dbarPartial j (extendByZero f.1) x + dbarPartial j (extendByZero g.1) x
            rw [extendByZero_add]
            exact dbarPartial_add ((f.2 x).differentiableAt (by simp))
              ((g.2 x).differentiableAt (by simp)) }
      naturality := fun U V i ↦ by
        ext f
        refine Subtype.ext (funext fun x ↦ ?_)
        change dbarPartial j (extendByZero fun y : V.unop ↦ f.1 ⟨y, leOfHom i.unop y.2⟩) x =
          dbarPartial j (extendByZero f.1) x
        exact dbarPartial_congr
          (extendByZero_eventuallyEq V.unop.2 (leOfHom i.unop) _ _ (fun _ ↦ rfl) x.2) }

@[simp] lemma dbarPartialHom_app_apply (j : σ) {U : (Opens (TopCat.of (σ → ℂ)))ᵒᵖ}
    (f : (smoothSheaf (σ → ℂ) ℂ).obj.obj U) (x : U.unop) :
    ((dbarPartialHom σ j).hom.app U f).1 x = dbarPartial j (extendByZero f.1) x := rfl

/-- `∂/∂z̄ⱼ` kills holomorphic functions: `𝒪 ⟶ 𝒞^∞ ⟶ 𝒞^∞` is zero. -/
lemma holomorphicToSmooth_comp_dbarPartialHom (j : σ) :
    holomorphicToSmooth σ ≫ dbarPartialHom σ j = 0 := by
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  ext f
  refine Subtype.ext (funext fun x ↦ ?_)
  change dbarPartial j (extendByZero (f : analyticSections ℂ U.unop).1) x = 0
  exact dbarPartial_eq_zero_of_differentiableAt j
    (((f : analyticSections ℂ U.unop).2 x).differentiableAt)

end Sheaves

/-! ### One variable: the Dolbeault short exact sequence -/

section OneVariable

variable {σ : Type} [Fintype σ] [DecidableEq σ] [Unique σ]

/-- The Dolbeault complex `𝒪 ⟶ 𝒞^∞ ⟶ 𝒞^∞` on `ℂ^σ`, `σ` with a unique element. -/
def dolbeaultShortComplex (σ : Type) [Fintype σ] [DecidableEq σ] [Unique σ] :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
      AddCommGrpCat.{0}) :=
  ShortComplex.mk (holomorphicToSmooth σ) (dbarPartialHom σ default)
    (holomorphicToSmooth_comp_dbarPartialHom default)

/-- In one variable, a function smooth near `x` with `∂f/∂z̄ = 0` near `x` is analytic at `x`. -/
lemma analyticAt_of_dbarPartial_eq_zero {f : (σ → ℂ) → ℂ} {U : Set (σ → ℂ)} (hU : IsOpen U)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y) (hdf : ∀ y ∈ U, dbarPartial default f y = 0)
    {x : σ → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  set e := ContinuousLinearEquiv.funUnique σ ℂ ℂ
  set eR := ContinuousLinearEquiv.funUnique σ ℝ ℂ
  have heR : ⇑eR.symm = ⇑e.symm := rfl
  set g : ℂ → ℂ := f ∘ e.symm
  have hfg : f = g ∘ e := by
    funext y
    simp [g]
  have hW : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ g (e.symm ⁻¹' U) := fun t ht ↦ by
    have hd : DifferentiableAt ℝ g t :=
      (hf _ ht).comp t (heR ▸ eR.symm.differentiableAt)
    have h0 : dbar g t = 0 := by
      have := hdf _ ht
      rwa [dbarPartial_eq_dbar, show e.symm t default = t from rfl] at this
    exact ((dbar_eq_zero_iff hd).mp h0).differentiableWithinAt
  have hex : e x ∈ e.symm ⁻¹' U := by simpa using hx
  rw [hfg]
  exact (hg.analyticAt (hW.mem_nhds hex)).comp_of_eq (e.analyticAt x) rfl

/-- **Local solvability of `∂u/∂z̄ = w` in one variable**: `∂/∂z̄ : 𝒞^∞ ⟶ 𝒞^∞` is locally
surjective (Dolbeault's lemma on a small disc, `exists_contDiff_dbar_eq_on_ball`). -/
lemma isLocallySurjective_dbarPartialHom :
    TopCat.Presheaf.IsLocallySurjective (dbarPartialHom σ default).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  set e := ContinuousLinearEquiv.funUnique σ ℂ ℂ
  set eR := ContinuousLinearEquiv.funUnique σ ℝ ℂ
  have heR : ⇑eR.symm = ⇑e.symm := rfl
  have heR' : ⇑eR = ⇑e := rfl
  -- a disc around `e x` whose points come from `U`
  obtain ⟨R, hR, hRU⟩ : ∃ R > 0, ∀ s ∈ ball (e x) R, e.symm s ∈ (U : Set (σ → ℂ)) := by
    have : e.symm ⁻¹' (U : Set (σ → ℂ)) ∈ 𝓝 (e x) :=
      e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using U.2.mem_nhds hx)
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp this
    exact ⟨R, hR, fun y hy ↦ hRU hy⟩
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (extendByZero t.1 ∘ e.symm) (ball (e x) R) := fun s hs ↦ by
    have hs' : e.symm s ∈ (U : Set (σ → ℂ)) := hRU s hs
    have := (t.2 ⟨_, hs'⟩).comp s (heR ▸ eR.symm.contDiff.contDiffAt)
    exact this.contDiffWithinAt
  obtain ⟨u, hu, hdu⟩ := exists_contDiff_dbar_eq_on_ball (n := ⊤) le_top (half_pos hR)
    (half_lt_self hR) hw
  let V : Opens (σ → ℂ) := ⟨e ⁻¹' ball (e x) (R / 2), isOpen_ball.preimage e.continuous⟩
  have hVU : V ≤ U := fun y hy ↦ by
    have := hRU (e y) (ball_subset_ball (half_lt_self hR).le hy)
    simpa using this
  have hxV : x ∈ V := by
    change e x ∈ ball (e x) (R / 2)
    simpa using half_pos hR
  refine ⟨V, hVU, ⟨⟨fun y ↦ u (e y), isSmoothOn_restrict V.2 fun y _ ↦
    (hu.comp (heR' ▸ eR.contDiff)).contDiffAt⟩, ?_⟩, hxV⟩
  refine Subtype.ext (funext fun y ↦ ?_)
  change dbarPartial default (extendByZero fun y : V ↦ u (e y)) y = t.1 ⟨y, hVU y.2⟩
  have hev : (extendByZero fun y : V ↦ u (e y)) =ᶠ[𝓝 (y : σ → ℂ)] u ∘ e := by
    filter_upwards [V.2.mem_nhds y.2] with z hz
    rw [extendByZero_of_mem _ hz]
    rfl
  rw [dbarPartial_congr hev, dbarPartial_eq_dbar]
  have hcomp : (u ∘ e) ∘ e.symm = u := by
    funext s
    simp
  rw [hcomp, show (y : σ → ℂ) default = e y from rfl, hdu _ y.2, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, extendByZero_of_mem _ (hVU y.2)]

/-- **The Dolbeault resolution of `𝒪` in one variable**: `0 → 𝒪 → 𝒞^∞ → 𝒞^∞ → 0` is a short
exact sequence of abelian sheaves on `ℂ^σ`, `σ` with a unique element. -/
theorem dolbeaultShortComplex_shortExact : (dolbeaultShortComplex σ).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_sections holomorphicToSmooth_app_injective
    (fun U b hb ↦ ?_) isLocallySurjective_dbarPartialHom
  have hb' : ∀ y ∈ (U.unop : Set (σ → ℂ)), dbarPartial default (extendByZero b.1) y = 0 :=
    fun y hy ↦ congrArg (fun s : smoothSections (σ → ℂ) ℂ U.unop ↦ s.1 ⟨y, hy⟩) hb
  have han : ∀ y ∈ (U.unop : Set (σ → ℂ)), AnalyticAt ℂ (extendByZero b.1) y := fun y hy ↦
    analyticAt_of_dbarPartial_eq_zero U.unop.2
      (fun z hz ↦ (b.2 ⟨z, hz⟩).differentiableAt (by simp)) hb' hy
  refine ⟨(⟨b.1, fun y ↦ han y y.2⟩ : analyticSections ℂ U.unop), ?_⟩
  rfl

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
  AddCommGrpCat.{0})]

/-- **Theorem B for `𝒪` in one variable, from `∂̄`**: if `∂u/∂z̄ = w` is solvable with `u` smooth
on an open `V ⊆ ℂ` for every smooth `w` on `V`, then `Hⁿ(V, 𝒪) = 0` for all `n > 0`. -/
theorem H'_holomorphicAbSheaf_subsingleton_of_dbar (V : Opens (TopCat.of (σ → ℂ)))
    (hV : ∀ w : smoothSections (σ → ℂ) ℂ V, ∃ u : smoothSections (σ → ℂ) ℂ V,
      dbarPartialSmooth default u = w) (q : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (q + 1) V) := by
  have hS := dolbeaultShortComplex_shortExact (σ := σ)
  cases q with
  | zero =>
    exact TopCat.Sheaf.subsingleton_H'_one_of_shortExact hS V
      (H'_smoothSheaf_subsingleton 0 V) hV
  | succ q =>
    exact TopCat.Sheaf.subsingleton_H'_succ_succ_of_shortExact hS V q
      (H'_smoothSheaf_subsingleton q V) (H'_smoothSheaf_subsingleton (q + 1) V)

omit [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
  AddCommGrpCat.{0})] in
/-- In one variable, if `∂u/∂z̄ = w` is solvable on the open set `D = {s : ℂ | (s, …, s) ∈ V}` for
every smooth `w` on `D`, the hypothesis of `H'_holomorphicAbSheaf_subsingleton_of_dbar` holds on
`V`. -/
lemma exists_dbarPartialSmooth_eq_of_dbar {V : Opens (σ → ℂ)}
    (h : ∀ w : ℂ → ℂ, ContDiffOn ℝ ∞ w
        ((ContinuousLinearEquiv.funUnique σ ℂ ℂ).symm ⁻¹' (V : Set (σ → ℂ))) →
      ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u
          ((ContinuousLinearEquiv.funUnique σ ℂ ℂ).symm ⁻¹' (V : Set (σ → ℂ))) ∧
        ∀ z ∈ (ContinuousLinearEquiv.funUnique σ ℂ ℂ).symm ⁻¹' (V : Set (σ → ℂ)),
          dbar u z = w z)
    (w : smoothSections (σ → ℂ) ℂ V) : ∃ u : smoothSections (σ → ℂ) ℂ V,
      dbarPartialSmooth default u = w := by
  set e := ContinuousLinearEquiv.funUnique σ ℂ ℂ
  set eR := ContinuousLinearEquiv.funUnique σ ℝ ℂ
  have heR : ⇑eR.symm = ⇑e.symm := rfl
  have heR' : ⇑eR = ⇑e := rfl
  set D := e.symm ⁻¹' (V : Set (σ → ℂ))
  have hD : IsOpen D := V.2.preimage e.symm.continuous
  have hW : ContDiffOn ℝ ∞ (extendByZero w.1 ∘ e.symm) D := fun s hs ↦
    ((w.2 ⟨_, hs⟩).comp s (heR ▸ eR.symm.contDiff.contDiffAt)).contDiffWithinAt
  obtain ⟨u, hu, hdu⟩ := h _ hW
  have heD : ∀ y : V, e y ∈ D := fun y ↦ by
    change e.symm (e y) ∈ (V : Set (σ → ℂ))
    simp
  refine ⟨⟨fun y ↦ u (e y), isSmoothOn_restrict V.2 fun y hy ↦
    ((hu.contDiffAt (hD.mem_nhds (heD ⟨y, hy⟩))).comp y
      (heR' ▸ eR.contDiff.contDiffAt))⟩, Subtype.ext (funext fun y ↦ ?_)⟩
  change dbarPartial default (extendByZero fun y : V ↦ u (e y)) y = w.1 y
  have hev : (extendByZero fun y : V ↦ u (e y)) =ᶠ[𝓝 (y : σ → ℂ)] u ∘ e := by
    filter_upwards [V.2.mem_nhds y.2] with z hz
    rw [extendByZero_of_mem _ hz]
    rfl
  have hcomp : (u ∘ e) ∘ e.symm = u := by
    funext s
    simp
  rw [dbarPartial_congr hev, dbarPartial_eq_dbar, hcomp, show (y : σ → ℂ) default = e y from rfl,
    hdu _ (heD y), Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply,
    extendByZero_coe]

end OneVariable

/-! ### Discs -/

section Disc

/-- `Fin 1 ⊕ Fin 0 ⊕ Fin 0` has a unique element (a local instance, used in this section only). -/
@[instance_reducible]
private def uniqueFinOneSum : Unique (Fin 1 ⊕ Fin 0 ⊕ Fin 0) where
  default := Sum.inl 0
  uniq := by
    rintro (i | i | i)
    · rw [Subsingleton.elim i 0]
    · exact i.elim0
    · exact i.elim0

attribute [local instance] uniqueFinOneSum

/-- **Theorem B for `𝒪` on a disc**: `Hⁿ(Δ, 𝒪) = 0` for `n > 0` and every open disc `Δ ⊆ ℂ`
centred at `0` (of any radius `r 0`; for `r 0 ≤ 0` the disc is empty). This is the case
`c = 1`, `a = b = 0` of `AnalyticGeometry.PolydiscProductVanishingStatement`. -/
theorem H'_polydiscProduct_one_zero_zero_subsingleton (r : Fin 1 → ℝ) (q : ℕ) :
    Subsingleton ((holomorphicAbSheaf (Fin 1 ⊕ Fin 0 ⊕ Fin 0)).H' (q + 1)
      (polydiscProduct 1 0 0 r)) := by
  refine H'_holomorphicAbSheaf_subsingleton_of_dbar _ (fun w ↦ ?_) q
  refine exists_dbarPartialSmooth_eq_of_dbar (fun w hw ↦ ?_) w
  have hD : (ContinuousLinearEquiv.funUnique (Fin 1 ⊕ Fin 0 ⊕ Fin 0) ℂ ℂ).symm ⁻¹'
      (polydiscProduct 1 0 0 r : Set (Fin 1 ⊕ Fin 0 ⊕ Fin 0 → ℂ)) = ball 0 (r 0) := by
    ext s
    simp [polydiscProduct, Fin.forall_fin_one]
  rw [hD] at hw ⊢
  rcases lt_or_ge 0 (r 0) with h0 | h0
  · exact exists_contDiffOn_dbar_eq_ball h0 hw
  · rw [ball_eq_empty.mpr h0]
    exact ⟨w, contDiffOn_empty, fun z hz ↦ hz.elim⟩

end Disc

end AnalyticGeometry
