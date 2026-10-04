/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherTransport

/-!
# Pointed charts of a family and coverings of its total space

Let `π : P → B` be continuous with a continuous section `σ`. A *pointed chart* at `b₀`
(`RiemannHigher.PointedChart`) is a neighbourhood `N` of `b₀` which contracts to a point `c`,
with a trivialization `Θ : π⁻¹(N) ≅ N × F` over `N` (`F` path-connected) sending `σ` to a constant
`x₀`. For a covering `p : E → P`:

* `PointedChart.chart`: over `N`, `E` is the product of `N` with the slice `S` of `E` over
  `{c} × F` (`sliceHomeomorph`), and `S → F` is a covering (`PointedChart.isCoveringMap_sliceProj`);
* `PointedChart.fibreChart`: for `b ∈ N`, the part of `E` over `π⁻¹(b)` is homeomorphic to `S`,
  compatibly with the projections to `F`;
* `eq_of_forall_proj_eq_x₀`: two maps of coverings of a path-connected space which agree on one
  fibre are equal.

These are the tools for rigidifying fibrewise isomorphisms of coverings by frames over `σ`
(`SGA.SGA1.ExposeXII.RiemannHigherFrames`), in the induction step of XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`). General topology; reference: Hatcher, *Algebraic topology*,
§1.3.
-/
noncomputable section

open Topology unitInterval Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

section Unique

variable {S₁ S₂ F : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂] [TopologicalSpace F]
  [PathConnectedSpace F] {q₁ : S₁ → F} {q₂ : S₂ → F}

/-- Two maps of coverings of a path-connected space which agree on the fibre over one point are
equal (lift a path to that point and use the uniqueness of lifts). -/
theorem eq_of_forall_proj_eq_x₀ (hq₁ : IsCoveringMap q₁) (hq₂ : IsCoveringMap q₂)
    {f g : S₁ → S₂} (hf : Continuous f) (hg : Continuous g) (hqf : ∀ s, q₂ (f s) = q₁ s)
    (hqg : ∀ s, q₂ (g s) = q₁ s) (x₀ : F) (h : ∀ s, q₁ s = x₀ → f s = g s) : f = g := by
  funext s
  let γ := PathConnectedSpace.somePath (q₁ s) x₀
  obtain ⟨Γ, hΓ, hΓ0⟩ := hq₁.exists_path_lifts γ.toContinuousMap s γ.source
  have hΓ1 : q₁ (Γ 1) = x₀ := by
    have := congr_fun hΓ 1
    simp only [Function.comp_apply] at this
    rw [this]
    exact γ.target
  have key := hq₂.eq_of_comp_eq (A := I) (g₁ := f ∘ Γ) (g₂ := g ∘ Γ) (hf.comp Γ.continuous)
    (hg.comp Γ.continuous) (funext fun t ↦ by simp only [Function.comp_apply, hqf, hqg]) 1
    (h _ hΓ1)
  have := congr_fun key 0
  simpa only [Function.comp_apply, hΓ0] using this

end Unique

section Chart

variable {B P : Type*} [TopologicalSpace B] [TopologicalSpace P] (π : P → B) (sec : B → P)
  (hsec : ∀ b, π (sec b) = b)

/-- A *pointed chart* of `π : P → B` with section `σ` at `b₀`: an open neighbourhood `N` of `b₀`
with a contraction `h` of `N` to a point `c`, and a trivialization `Θ : π⁻¹(N) ≅ N × F` over `N`
sending the section `σ` to the constant `x₀`, with `F` path-connected. -/
structure PointedChart (b₀ : B) where
  /-- The neighbourhood of `b₀`. -/
  N : Set B
  mem_nhds_N : N ∈ 𝓝 b₀
  /-- The centre of the contraction of `N`. -/
  c : N
  /-- A contraction of `N` to `c`. -/
  h : C(I × N, N)
  h_zero : ∀ n, h (0, n) = c
  h_one : ∀ n, h (1, n) = n
  /-- The fibre of the trivialization. -/
  F : Type
  [topF : TopologicalSpace F]
  [pathConnected : PathConnectedSpace F]
  /-- The image of the section. -/
  x₀ : F
  /-- The trivialization of `π` over `N`. -/
  Θ : {x : P // π x ∈ N} ≃ₜ N × F
  fst_Θ : ∀ x, ((Θ x).1 : B) = π x
  Θ_sec : ∀ n : N, Θ ⟨sec n, by rw [hsec]; exact n.2⟩ = (n, x₀)

attribute [instance] PointedChart.topF PointedChart.pathConnected

variable {π sec hsec} {b₀ : B} (K : PointedChart π sec hsec b₀)
variable {E : Type*} [TopologicalSpace E] {p : E → P}

namespace PointedChart

lemma mem_N : b₀ ∈ K.N := mem_of_mem_nhds K.mem_nhds_N

lemma mem_interior_N : b₀ ∈ interior K.N := mem_interior_iff_mem_nhds.mpr K.mem_nhds_N

/-- The covering `E` over `π⁻¹(N)`, seen over `N × F` through the chart. -/
def restrict (p : E → P) : {e : E // π (p e) ∈ K.N} → K.N × K.F := fun e ↦ K.Θ ⟨p e, e.2⟩

lemma isCoveringMap_restrict (hp : IsCoveringMap p) : IsCoveringMap (K.restrict p) :=
  (hp.restrictPreimage {x | π x ∈ K.N}).homeomorph_comp K.Θ

/-- The slice of `E` over `{c} × F`. -/
abbrev Slice (p : E → P) : Type _ := SliceSpace (K.restrict p) K.c

/-- The projection of the slice to `F`. -/
def sliceProj (p : E → P) (z : K.Slice p) : K.F := (K.restrict p z.1).2

lemma isCoveringMap_sliceProj (hp : IsCoveringMap p) : IsCoveringMap (K.sliceProj p) := by
  let t : Set (K.N × K.F) := {y | y.1 = K.c}
  let e : t ≃ₜ K.F :=
    { toFun y := y.1.2
      invFun x := ⟨(K.c, x), rfl⟩
      left_inv y := Subtype.ext (Prod.ext y.2.symm rfl)
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ((K.isCoveringMap_restrict hp).restrictPreimage t).homeomorph_comp e

/-- The product structure of `E` over `π⁻¹(N)`: `N × S ≅ E|_{π⁻¹(N)}`. -/
def chart (hp : IsCoveringMap p) : K.N × K.Slice p ≃ₜ {e : E // π (p e) ∈ K.N} :=
  sliceHomeomorph (K.isCoveringMap_restrict hp) K.h K.h_zero K.h_one

lemma restrict_chart (hp : IsCoveringMap p) (x : K.N × K.Slice p) :
    K.restrict p (K.chart hp x) = (x.1, K.sliceProj p x.2) :=
  proj_sliceHomeomorph (K.isCoveringMap_restrict hp) K.h K.h_zero K.h_one x

lemma proj_chart (hp : IsCoveringMap p) (x : K.N × K.Slice p) :
    π (p (K.chart hp x).1) = x.1 := by
  have := congrArg (fun y ↦ (y.1 : B)) (K.restrict_chart hp x)
  simp only at this
  rw [← this]
  exact (K.fst_Θ ⟨p (K.chart hp x).1, (K.chart hp x).2⟩).symm

lemma fst_chart_symm (hp : IsCoveringMap p) (e : {e : E // π (p e) ∈ K.N}) :
    (((K.chart hp).symm e).1 : B) = π (p e.1) := by
  conv_rhs => rw [← (K.chart hp).apply_symm_apply e]
  exact (K.proj_chart hp _).symm

lemma sliceProj_chart_symm (hp : IsCoveringMap p) (e : {e : E // π (p e) ∈ K.N}) :
    K.sliceProj p ((K.chart hp).symm e).2 = (K.Θ ⟨p e.1, e.2⟩).2 := by
  have := K.restrict_chart hp ((K.chart hp).symm e)
  rw [Homeomorph.apply_symm_apply] at this
  exact (congrArg Prod.snd this).symm

/-- For `b ∈ N`, the part of `E` over `π⁻¹(b)` is homeomorphic to the slice. -/
def fibreChart (hp : IsCoveringMap p) {b : B} (hb : b ∈ K.N) :
    FibreSpace p π b ≃ₜ K.Slice p where
  toFun e := ((K.chart hp).symm ⟨e.1, by rw [e.2]; exact hb⟩).2
  invFun z := ⟨(K.chart hp (⟨b, hb⟩, z)).1, K.proj_chart hp _⟩
  left_inv e := by
    have h₁ : ((K.chart hp).symm ⟨e.1, by rw [e.2]; exact hb⟩).1 = ⟨b, hb⟩ :=
      Subtype.ext ((K.fst_chart_symm hp _).trans e.2)
    refine Subtype.ext ?_
    change (K.chart hp (⟨b, hb⟩, ((K.chart hp).symm ⟨e.1, _⟩).2)).1 = e.1
    rw [← h₁, Prod.mk.eta, Homeomorph.apply_symm_apply]
  right_inv z := by
    change ((K.chart hp).symm ⟨(K.chart hp (⟨b, hb⟩, z)).1, _⟩).2 = z
    rw [Subtype.coe_eta, Homeomorph.symm_apply_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma sliceProj_fibreChart (hp : IsCoveringMap p) {b : B} (hb : b ∈ K.N)
    (e : FibreSpace p π b) :
    K.sliceProj p (K.fibreChart hp hb e) = (K.Θ ⟨p e.1, by rw [e.2]; exact hb⟩).2 :=
  K.sliceProj_chart_symm hp _

/-- A point of `E` over `sec b` goes to the fibre of the slice over `x₀`. -/
lemma sliceProj_fibreChart_of_eq_sec (hp : IsCoveringMap p) {b : B} (hb : b ∈ K.N)
    (e : FibreSpace p π b) (he : p e.1 = sec b) : K.sliceProj p (K.fibreChart hp hb e) = K.x₀ := by
  rw [K.sliceProj_fibreChart hp hb]
  have : (⟨p e.1, by rw [e.2]; exact hb⟩ : {x : P // π x ∈ K.N}) =
      ⟨sec (⟨b, hb⟩ : K.N), by rw [hsec]; exact hb⟩ := Subtype.ext he
  rw [this, K.Θ_sec]

/-- Conversely, a point of the slice over `x₀` comes from a point of `E` over `sec b`. -/
lemma eq_sec_of_sliceProj_fibreChart (hp : IsCoveringMap p) {b : B} (hb : b ∈ K.N)
    (e : FibreSpace p π b) (he : K.sliceProj p (K.fibreChart hp hb e) = K.x₀) : p e.1 = sec b := by
  rw [K.sliceProj_fibreChart hp hb] at he
  have h₁ : K.Θ ⟨p e.1, by rw [e.2]; exact hb⟩ =
      K.Θ ⟨sec (⟨b, hb⟩ : K.N), by rw [hsec]; exact hb⟩ := by
    rw [K.Θ_sec]
    exact Prod.ext (Subtype.ext ((K.fst_Θ _).trans e.2)) he
  exact congrArg Subtype.val (K.Θ.injective h₁)

end PointedChart

end Chart

end SGA.SGA1.ExposeXII.RiemannHigher
