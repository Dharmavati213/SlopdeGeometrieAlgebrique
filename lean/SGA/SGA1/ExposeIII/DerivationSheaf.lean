/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.ExtensionCharts
import SGA.SGA1.ExposeIII.LocalizationHom

/-!
# SGA 1, Exposé III, §5.2: the sheaf `𝒢 = ℋom(g₀^* Ω_{X/T}, 𝒥)` and differences of extensions

Let `f : X → T` with `T` affine, `i : T₀ → T` a surjective closed immersion whose ideal `𝒥` has
square zero, and `g₀ : T₀ → X` a section of `f` over `T₀`. SGA 1 III.5.2 observes that two
extensions of `g₀` over an open `U` differ by a section over `U` of
`𝒢 = ℋom_{𝒪_{T₀}}(g₀^* Ω_{X/T}, 𝒥)`, and that `𝒢` acts simply transitively on the extensions
over `U`.

We describe `𝒢(U)` on affine charts (`ExtensionChart`): a section is a compatible family of
derivations `Γ(X, V) → J(W) = ker(Γ(T, W) → Γ(T₀, i⁻¹ W))` for the charts `(V, W)` with
`W ⊆ U` (`ChartDerivation`). These form a presheaf of `Γ(T, ⊤)`-modules on `T`
(`derivationPresheaf`), and:

* `ChartDerivation.diff`: the difference of two extensions, with `diff_add_diff`,
  `diff_eq_zero_iff` (III.5.2, the action is free);
* `Extension.ofChartDer`: an extension `g` over an affine `W` modified by a derivation on a chart
  `(V, W)`, with `diff_ofChartDer` (III.5.2, the action is transitive);
* `ChartDerivation.ext_of_apply_eq`: a section of `𝒢` over `U` is determined by its value on one
  chart `(V, U)`: this uses that `Γ(X, V) → Γ(X, D(s))` is a localization;
* `isLocalizedModule_res`: on affine opens `W' = W ∩ D(r)`, the restriction `𝒢(W) → 𝒢(W')` is
  a localization at `r`, i.e. `𝒢` is quasi-coherent. This uses that `Ω_{Γ(X, V)/Γ(T, ⊤)}` is
  finitely presented (`f` smooth) and that `J` is quasi-coherent.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace SGA.SGA1.ExposeIII

variable {X T T₀ : Scheme.{u}} (f : X ⟶ T) (i : T₀ ⟶ T) (g₀ : T₀ ⟶ X)

/-- The ideal `J(W) = ker(Γ(T, W) → Γ(T₀, i⁻¹ W))` of `i` on an open `W`. -/
def idealOn (W : T.Opens) : Ideal Γ(T, W) := RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom

/-- The ideal of `i` has square zero on affine opens. -/
def IsSqZeroOn : Prop :=
  ∀ W : T.Opens, IsAffineOpen W → ∀ x ∈ idealOn i W, ∀ y ∈ idealOn i W, x * y = 0

variable {i g₀}

lemma ExtensionChart.mem_idealOn_iff (c : ExtensionChart i g₀) (x : Γ(T, c.W)) :
    x ∈ idealOn i c.W ↔ c.ρ x = 0 :=
  Iff.rfl

lemma map_resTop {W W' : T.Opens} (h : W' ≤ W) (r : Γ(T, ⊤)) :
    T.presheaf.map (homOfLE h).op (resTop W r) = resTop W' r := by
  rw [resTop, resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A derivation on a chart `(V, W)`: an additive map `Γ(X, V) → J(W)` vanishing on `Γ(T, ⊤)`
and satisfying the Leibniz rule with respect to lifts of `g₀`. -/
structure IsChartDer (c : ExtensionChart i g₀) (d : Γ(X, c.V) → Γ(T, c.W)) : Prop where
  map_add (a b : Γ(X, c.V)) : d (a + b) = d a + d b
  mem (a : Γ(X, c.V)) : d a ∈ idealOn i c.W
  map_α (r : Γ(T, ⊤)) : d (c.α f r) = 0
  leibniz (a b : Γ(X, c.V)) (a' b' : Γ(T, c.W)) : c.ρ a' = c.γ a → c.ρ b' = c.γ b →
    d (a * b) = a' * d b + b' * d a

variable (i g₀) in
/-- The families of chart derivations over the charts `(V, W)` with `W ⊆ U`. -/
abbrev ChartFamily (U : T.Opens) : Type u :=
  ∀ c : {c : ExtensionChart i g₀ // c.W ≤ U}, Γ(X, c.1.V) → Γ(T, c.1.W)

/-- III.5.2: the condition for a family of chart derivations to be a section of
`ℋom(g₀^* Ω_{X/T}, 𝒥)`: each member is a derivation, and they are compatible with restriction. -/
structure IsChartDerivation {U : T.Opens} (δ : ChartFamily i g₀ U) : Prop where
  isChartDer (c : ExtensionChart i g₀) (hc : c.W ≤ U) : IsChartDer f c (δ ⟨c, hc⟩)
  map_res (c c' : ExtensionChart i g₀) (hc : c.W ≤ U) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    δ ⟨c', hc'⟩ (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (δ ⟨c, hc⟩ a)

variable (i g₀) in
/-- III.5.2: the group `𝒢(U)` of sections over `U` of `ℋom(g₀^* Ω_{X/T}, 𝒥)`, described as
compatible families of derivations on the affine charts inside `U`. -/
def chartDerivations (U : T.Opens) : AddSubgroup (ChartFamily i g₀ U) where
  carrier := {δ | IsChartDerivation f δ}
  add_mem' {δ δ'} hδ hδ' :=
    { isChartDer c hc :=
        { map_add a b := by
            simp only [Pi.add_apply, (hδ.isChartDer c hc).map_add, (hδ'.isChartDer c hc).map_add]
            abel
          mem a := add_mem ((hδ.isChartDer c hc).mem a) ((hδ'.isChartDer c hc).mem a)
          map_α r := by
            simp [(hδ.isChartDer c hc).map_α, (hδ'.isChartDer c hc).map_α]
          leibniz a b a' b' ha hb := by
            simp only [Pi.add_apply, (hδ.isChartDer c hc).leibniz a b a' b' ha hb,
              (hδ'.isChartDer c hc).leibniz a b a' b' ha hb]
            ring }
      map_res c c' hc hc' hV hW a := by
        simp only [Pi.add_apply, map_add, hδ.map_res c c' hc hc' hV hW,
          hδ'.map_res c c' hc hc' hV hW] }
  zero_mem' :=
    { isChartDer c hc :=
        { map_add a b := by simp
          mem a := zero_mem _
          map_α r := rfl
          leibniz a b a' b' _ _ := by simp }
      map_res c c' hc hc' hV hW a := by simp }
  neg_mem' {δ} hδ :=
    { isChartDer c hc :=
        { map_add a b := by
            simp only [Pi.neg_apply, (hδ.isChartDer c hc).map_add]
            abel
          mem a := neg_mem ((hδ.isChartDer c hc).mem a)
          map_α r := by simp [(hδ.isChartDer c hc).map_α]
          leibniz a b a' b' ha hb := by
            simp only [Pi.neg_apply, (hδ.isChartDer c hc).leibniz a b a' b' ha hb]
            ring }
      map_res c c' hc hc' hV hW a := by
        simp only [Pi.neg_apply, map_neg, hδ.map_res c c' hc hc' hV hW] }

variable (i g₀) in
/-- III.5.2: sections over `U` of `𝒢 = ℋom(g₀^* Ω_{X/T}, 𝒥)`. -/
abbrev ChartDerivation (U : T.Opens) : Type u := chartDerivations f i g₀ U

namespace ChartDerivation

variable {f} {U : T.Opens}

/-- The value of a section of `𝒢` on a chart `(V, W)` with `W ⊆ U`. -/
def app (δ : ChartDerivation f i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    Γ(X, c.V) → Γ(T, c.W) :=
  δ.1 ⟨c, hc⟩

lemma isChartDerivation (δ : ChartDerivation f i g₀ U) : IsChartDerivation f δ.1 := δ.2

lemma isChartDer (δ : ChartDerivation f i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    IsChartDer f c (δ.app c hc) :=
  δ.2.isChartDer c hc

lemma map_res (δ : ChartDerivation f i g₀ U) (c c' : ExtensionChart i g₀) (hc : c.W ≤ U)
    (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V) (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    δ.app c' hc' (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (δ.app c hc a) :=
  δ.2.map_res c c' hc hc' hV hW a

@[ext]
lemma ext {δ δ' : ChartDerivation f i g₀ U}
    (h : ∀ c hc a, δ.app c hc a = δ'.app c hc a) : δ = δ' :=
  Subtype.ext (funext fun c ↦ funext fun a ↦ h c.1 c.2 a)

/-- Evaluation of sections of `𝒢` on a chart at an element, as an additive map. -/
def appAddHom (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V)) :
    ChartDerivation f i g₀ U →+ Γ(T, c.W) where
  toFun δ := δ.app c hc a
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma appAddHom_apply (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V))
    (δ : ChartDerivation f i g₀ U) : appAddHom c hc a δ = δ.app c hc a := rfl

@[simp] lemma add_app (δ δ' : ChartDerivation f i g₀ U) (c hc a) :
    (δ + δ').app c hc a = δ.app c hc a + δ'.app c hc a := rfl

@[simp] lemma neg_app (δ : ChartDerivation f i g₀ U) (c hc a) :
    (-δ).app c hc a = -δ.app c hc a := rfl

@[simp] lemma sub_app (δ δ' : ChartDerivation f i g₀ U) (c hc a) :
    (δ - δ').app c hc a = δ.app c hc a - δ'.app c hc a := rfl

@[simp] lemma zero_app (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a) :
    (0 : ChartDerivation f i g₀ U).app c hc a = 0 := rfl

/-- `Γ(T, ⊤)` acts on `𝒢(U)` through the restrictions `Γ(T, ⊤) → Γ(T, W)`. -/
instance : SMul Γ(T, ⊤) (ChartDerivation f i g₀ U) where
  smul r δ := ⟨fun c a ↦ resTop c.1.W r * δ.app c.1 c.2 a,
    { isChartDer c hc :=
        { map_add a b := by rw [(δ.isChartDer c hc).map_add, mul_add]
          mem a := Ideal.mul_mem_left _ _ ((δ.isChartDer c hc).mem a)
          map_α r := by rw [(δ.isChartDer c hc).map_α, mul_zero]
          leibniz a b a' b' ha hb := by
            rw [(δ.isChartDer c hc).leibniz a b a' b' ha hb]
            ring }
      map_res c c' hc hc' hV hW a := by
        rw [δ.map_res c c' hc hc' hV hW, map_mul, map_resTop] }⟩

@[simp] lemma smul_app (r : Γ(T, ⊤)) (δ : ChartDerivation f i g₀ U) (c hc a) :
    (r • δ).app c hc a = resTop c.W r * δ.app c hc a := rfl

instance : Module Γ(T, ⊤) (ChartDerivation f i g₀ U) where
  one_smul δ := ext fun c hc a ↦ by simp
  mul_smul r s δ := ext fun c hc a ↦ by simp [mul_assoc]
  smul_zero r := ext fun c hc a ↦ by simp
  smul_add r δ δ' := ext fun c hc a ↦ by simp [mul_add]
  add_smul r s δ := ext fun c hc a ↦ by simp [add_mul]
  zero_smul δ := ext fun c hc a ↦ by simp

/-- Restriction of sections of `𝒢` to a smaller open. -/
def res {U U' : T.Opens} (h : U' ≤ U) :
    ChartDerivation f i g₀ U →ₗ[Γ(T, ⊤)] ChartDerivation f i g₀ U' where
  toFun δ := ⟨fun c ↦ δ.app c.1 (c.2.trans h),
    { isChartDer c hc := δ.isChartDer c (hc.trans h)
      map_res c c' hc hc' := δ.map_res c c' (hc.trans h) (hc'.trans h) }⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma res_app {U U' : T.Opens} (h : U' ≤ U) (δ : ChartDerivation f i g₀ U) (c hc a) :
    (res h δ).app c hc a = δ.app c (hc.trans h) a := rfl

end ChartDerivation

variable (i g₀)

/-- III.5.2: the presheaf of abelian groups `𝒢 = ℋom(g₀^* Ω_{X/T}, 𝒥)` on `T`. -/
def derivationPresheaf : TopCat.Presheaf AddCommGrpCat.{u} T where
  obj U := AddCommGrpCat.of (ChartDerivation f i g₀ U.unop)
  map h := AddCommGrpCat.ofHom (ChartDerivation.res h.unop.le).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance (U : T.Opens) : Module Γ(T, ⊤) ((derivationPresheaf f i g₀).obj (op U)) :=
  inferInstanceAs (Module Γ(T, ⊤) (ChartDerivation f i g₀ U))

variable {f i g₀} in
/-- Evaluation of sections of `𝒢` on a chart at an element, on the presheaf `𝒢`. -/
def derivationPresheafEval {V : T.Opens} (c : ExtensionChart i g₀) (hc : c.W ≤ V)
    (a : Γ(X, c.V)) : (derivationPresheaf f i g₀).obj (op V) →+ Γ(T, c.W) :=
  ChartDerivation.appAddHom c hc a

lemma derivationPresheaf_map_smul ⦃U U' : T.Opens⦄ (h : U' ≤ U) (r : Γ(T, ⊤))
    (δ : (derivationPresheaf f i g₀).obj (op U)) :
    (derivationPresheaf f i g₀).map (homOfLE h).op (r • δ) =
      r • (derivationPresheaf f i g₀).map (homOfLE h).op δ :=
  rfl

variable {f i g₀}

section Diff

lemma Extension.ρ_chartMap_apply [Surjective i] [IsClosedImmersion i] {U : T.Opens}
    (g : Extension f (𝟙 T) i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V)) : c.ρ (g.chartMap c hc a) = c.γ a := by
  rw [← ConcreteCategory.comp_apply, Extension.chartMap_ρ]

lemma Extension.chartMap_α_apply [IsAffine T] [Surjective i] {U : T.Opens}
    (g : Extension f (𝟙 T) i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) (r : Γ(T, ⊤)) :
    g.chartMap c hc (c.α f r) = resTop c.W r := by
  rw [← ConcreteCategory.comp_apply, Extension.α_chartMap]

lemma Extension.chartMap_map_apply [Surjective i] {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U)
    (c c' : ExtensionChart i g₀) (hc : c.W ≤ U) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    g.chartMap c' hc' (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (g.chartMap c hc a) := by
  rw [← ConcreteCategory.comp_apply, Extension.map_chartMap g c c' hc hc' hV hW,
    ConcreteCategory.comp_apply]

lemma mul_eq_zero_of_mem (hsq : IsSqZeroOn i) (c : ExtensionChart i g₀) {x y : Γ(T, c.W)}
    (hx : c.ρ x = 0)
    (hy : c.ρ y = 0) : x * y = 0 :=
  hsq c.W c.hW x hx y hy

variable [IsAffine T] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

/-- III.5.2: the difference `g' - g ∈ 𝒢(U)` of two extensions over `U`. -/
noncomputable def ChartDerivation.diff {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U) :
    ChartDerivation f i g₀ U :=
  ⟨fun c a ↦ g'.chartMap c.1 c.2 a - g.chartMap c.1 c.2 a,
    { isChartDer c hc :=
        { map_add a b := by simp only [map_add]; abel
          mem a := by
            rw [ExtensionChart.mem_idealOn_iff, map_sub, g.ρ_chartMap_apply,
              g'.ρ_chartMap_apply, sub_self]
          map_α r := by rw [g.chartMap_α_apply, g'.chartMap_α_apply, sub_self]
          leibniz a b a' b' ha hb := by
            have h₁ : (a' - g'.chartMap c hc a) * (g'.chartMap c hc b - g.chartMap c hc b) = 0 :=
              mul_eq_zero_of_mem hsq c (by rw [map_sub, ha, g'.ρ_chartMap_apply, sub_self])
                (by rw [map_sub, g.ρ_chartMap_apply, g'.ρ_chartMap_apply, sub_self])
            have h₂ : (b' - g.chartMap c hc b) * (g'.chartMap c hc a - g.chartMap c hc a) = 0 :=
              mul_eq_zero_of_mem hsq c (by rw [map_sub, hb, g.ρ_chartMap_apply, sub_self])
                (by rw [map_sub, g.ρ_chartMap_apply, g'.ρ_chartMap_apply, sub_self])
            simp only [map_mul]
            linear_combination -h₁ - h₂ }
      map_res c c' hc hc' hV hW a := by
        rw [g.chartMap_map_apply c c' hc hc' hV hW, g'.chartMap_map_apply c c' hc hc' hV hW,
          map_sub] }⟩

namespace ChartDerivation

@[simp] lemma diff_app {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U) (c hc a) :
    (diff hsq g g').app c hc a = g'.chartMap c hc a - g.chartMap c hc a := rfl

lemma diff_add_diff {U : T.Opens} (g g' g'' : Extension f (𝟙 T) i g₀ U) :
    diff hsq g g' + diff hsq g' g'' = diff hsq g g'' :=
  ext fun c hc a ↦ by simp only [add_app, diff_app]; abel

lemma diff_self {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U) : diff hsq g g = 0 :=
  ext fun c hc a ↦ by simp

lemma neg_diff {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U) :
    -diff hsq g g' = diff hsq g' g :=
  ext fun c hc a ↦ by simp

lemma res_diff {U U' : T.Opens} (h : U' ≤ U) (g g' : Extension f (𝟙 T) i g₀ U) :
    res h (diff hsq g g') = diff hsq (g.restrict h) (g'.restrict h) :=
  ext fun c hc a ↦ by simp [Extension.chartMap_restrict]

/-- III.5.2: two extensions with difference zero are equal. -/
lemma diff_eq_zero_iff {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U) :
    diff hsq g g' = 0 ↔ g = g' := by
  refine ⟨fun h ↦ Extension.ext_of_chartMap fun c hc ↦ ?_, fun h ↦ h ▸ diff_self hsq g⟩
  ext a
  have := congrArg (fun δ : ChartDerivation f i g₀ U ↦ δ.app c hc a) h
  simp only [diff_app, zero_app, sub_eq_zero] at this
  exact this.symm

end ChartDerivation

end Diff

section Local

/-- A section of the structure sheaf which vanishes near every point is zero. -/
lemma eq_zero_of_locally_zero {Y : Scheme.{u}} {W : Y.Opens} (s : Γ(Y, W))
    (h : ∀ x ∈ W, ∃ (W' : Y.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      Y.presheaf.map (homOfLE hW').op s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext Y.sheaf W s 0 fun x hx ↦ by
    obtain ⟨W', hW', hxW', h⟩ := h x hx
    change Y.presheaf.germ W x hx s = Y.presheaf.germ W x hx 0
    rw [map_zero, ← Y.presheaf.germ_res_apply (homOfLE hW') x hxW', h, map_zero]

variable [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

include hsq in
/-- A section of `𝒢` over `U` is determined by its value on a single chart `(V, U)`: the value
on any other chart is determined on smaller charts `(D(s), W)`, `s ∈ Γ(X, V)`, where it extends
the value on `(V, U)` along the localization `Γ(X, V) → Γ(X, D(s))`. -/
theorem ChartDerivation.eq_zero_of_app_eq_zero {U : T.Opens} (δ : ChartDerivation f i g₀ U)
    (c₀ : ExtensionChart i g₀) (hc₀ : c₀.W ≤ U) (hU : U ≤ c₀.W)
    (h : ∀ a, δ.app c₀ hc₀ a = 0) : δ = 0 := by
  ext c hc a
  rw [zero_app]
  refine eq_zero_of_locally_zero _ fun x hx ↦ ?_
  obtain ⟨w, hw⟩ := i.surjective x
  have hwc : g₀ w ∈ c.V := c.le (show i w ∈ c.W from hw ▸ hx)
  have hwc₀ : g₀ w ∈ c₀.V := c₀.le (show i w ∈ c₀.W from hw ▸ hU (hc hx))
  obtain ⟨s, hsV, hws⟩ := c₀.hV.exists_basicOpen_le ⟨g₀ w, hwc⟩ hwc₀
  obtain ⟨W, hW, hxW, hWc, hWs⟩ := exists_isAffineOpen_preimage_le (i := i) (g₀ := g₀)
    (V := X.basicOpen s) hx fun w' hw' ↦ by
      rwa [i.isClosedEmbedding.injective (hw'.trans hw.symm)]
  let c' : ExtensionChart i g₀ := ⟨X.basicOpen s, W, c₀.hV.basicOpen s, hW, hWs⟩
  have hc' : c'.W ≤ U := hWc.trans hc
  refine ⟨W, hWc, hxW, ?_⟩
  rw [← δ.map_res c c' hc hc' hsV hWc]
  have := c₀.hV.isLocalization_basicOpen s
  refine eq_zero_of_isLocalization_away (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom s
    (IsLocalization.Away.algebraMap_isUnit s) (fun y ↦ ?_) c'.ρ.hom c'.ρ_surjective c'.γ.hom
    (fun x y hx hy ↦ hsq W hW x hx y hy) (δ.app c' hc') (δ.isChartDer c' hc').mem
    (δ.isChartDer c' hc').leibniz (fun a ↦ ?_) _
  · obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers s) y
    exact ⟨a, n, by rw [← map_pow]; exact h⟩
  · rw [δ.map_res c₀ c' hc₀ hc' (X.basicOpen_le s) (hWc.trans (hc.trans hU)), h, map_zero]

include hsq in
/-- Sections of `𝒢` over `U` agreeing on one chart `(V, U)` are equal. -/
theorem ChartDerivation.ext_of_app_eq {U : T.Opens} {δ δ' : ChartDerivation f i g₀ U}
    (c₀ : ExtensionChart i g₀) (hc₀ : c₀.W ≤ U) (hU : U ≤ c₀.W)
    (h : ∀ a, δ.app c₀ hc₀ a = δ'.app c₀ hc₀ a) : δ = δ' :=
  sub_eq_zero.mp (eq_zero_of_app_eq_zero hsq _ c₀ hc₀ hU fun a ↦ by
    rw [sub_app, h, sub_self])

end Local

section Modify

lemma IsChartDer.map_zero {c : ExtensionChart i g₀} {d : Γ(X, c.V) → Γ(T, c.W)}
    (hd : IsChartDer f c d) : d 0 = 0 := by
  have := hd.map_add 0 0
  rw [add_zero, left_eq_add] at this
  exact this

lemma IsChartDer.map_one {c : ExtensionChart i g₀} {d : Γ(X, c.V) → Γ(T, c.W)}
    (hd : IsChartDer f c d) : d 1 = 0 := by
  have := hd.leibniz 1 1 1 1 (by simp) (by simp)
  rw [mul_one, one_mul, left_eq_add] at this
  exact this

/-- The ring map `φ + d : Γ(X, V) → Γ(T, W)` for a lift `φ` of `g₀` and a derivation `d` on the
chart `(V, W)`. -/
def addChartMap (hsq : IsSqZeroOn i) (c : ExtensionChart i g₀) (φ : Γ(X, c.V) ⟶ Γ(T, c.W))
    (hφ : ∀ a, c.ρ (φ a) = c.γ a) (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsChartDer f c d) :
    Γ(X, c.V) ⟶ Γ(T, c.W) :=
  CommRingCat.ofHom
    { toFun a := φ a + d a
      map_one' := by rw [map_one, hd.map_one, add_zero]
      map_mul' a b := by
        have h₀ := mul_eq_zero_of_mem hsq c (hd.mem a) (hd.mem b)
        rw [map_mul, hd.leibniz a b (φ a) (φ b) (hφ a) (hφ b)]
        linear_combination -h₀
      map_zero' := by rw [map_zero, hd.map_zero, add_zero]
      map_add' a b := by rw [map_add, hd.map_add]; abel }

lemma addChartMap_apply (hsq : IsSqZeroOn i) (c : ExtensionChart i g₀)
    (φ : Γ(X, c.V) ⟶ Γ(T, c.W)) (hφ : ∀ a, c.ρ (φ a) = c.γ a) (d : Γ(X, c.V) → Γ(T, c.W))
    (hd : IsChartDer f c d) (a : Γ(X, c.V)) : addChartMap hsq c φ hφ d hd a = φ a + d a :=
  rfl

variable [IsAffine T] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

/-- III.5.2: the extension `g + d` over an affine `W`, for a derivation `d` on a chart `(V, W)`. -/
def Extension.ofChartDer {c : ExtensionChart i g₀} (g : Extension f (𝟙 T) i g₀ c.W)
    (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsChartDer f c d) : Extension f (𝟙 T) i g₀ c.W :=
  Extension.ofChartMap c
    (addChartMap hsq c (g.chartMap c le_rfl) (g.ρ_chartMap_apply c le_rfl) d hd)
    (by ext r; simp [addChartMap_apply, g.chartMap_α_apply, hd.map_α])
    (by
      ext a
      change c.ρ (g.chartMap c le_rfl a + d a) = c.γ a
      have h₀ : c.ρ (d a) = 0 := (c.mem_idealOn_iff _).mp (hd.mem a)
      rw [map_add, g.ρ_chartMap_apply, h₀, add_zero])

lemma Extension.chartMap_ofChartDer {c : ExtensionChart i g₀}
    (g : Extension f (𝟙 T) i g₀ c.W) (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsChartDer f c d)
    (a : Γ(X, c.V)) :
    (g.ofChartDer hsq d hd).chartMap c le_rfl a = g.chartMap c le_rfl a + d a := by
  rw [Extension.ofChartDer, Extension.chartMap_ofChartMap, addChartMap_apply]

/-- III.5.2: `𝒢(W)` acts transitively on the extensions over `W`: `(g + δ) - g = δ`. -/
lemma ChartDerivation.diff_ofChartDer {c : ExtensionChart i g₀}
    (g : Extension f (𝟙 T) i g₀ c.W) (δ : ChartDerivation f i g₀ c.W) :
    diff hsq g (g.ofChartDer hsq (δ.app c le_rfl) (δ.isChartDer c le_rfl)) = δ :=
  ext_of_app_eq hsq c le_rfl le_rfl fun a ↦ by
    rw [diff_app, Extension.chartMap_ofChartDer, add_sub_cancel_left]

end Modify

section Localization

variable [IsAffine T] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

/-- The chart `(V, W')` obtained by shrinking `W` to `W' ⊆ W`. -/
abbrev ExtensionChart.shrink (c : ExtensionChart i g₀) {W' : T.Opens} (hW' : IsAffineOpen W')
    (h : W' ≤ c.W) : ExtensionChart i g₀ :=
  ⟨c.V, W', c.hV, hW', (i.preimage_mono h).trans c.le⟩

lemma map_homOfLE_rfl_apply {Y : Scheme.{u}} {V : Y.Opens} (a : Γ(Y, V)) :
    Y.presheaf.map (homOfLE (le_refl V)).op a = a := by
  rw [show homOfLE (le_refl V) = 𝟙 V from rfl, op_id, Y.presheaf.map_id]
  rfl

variable (c : ExtensionChart i g₀) [Algebra Γ(T, ⊤) Γ(X, c.V)] [Algebra Γ(X, c.V) Γ(T, c.W)]
  [Algebra Γ(T, ⊤) Γ(T, c.W)] [IsScalarTower Γ(T, ⊤) Γ(X, c.V) Γ(T, c.W)]
  (hα : ∀ r, algebraMap Γ(T, ⊤) Γ(X, c.V) r = c.α f r)
  (hφ : ∀ a, c.ρ (algebraMap Γ(X, c.V) Γ(T, c.W) a) = c.γ a)
  (hR : ∀ r, algebraMap Γ(T, ⊤) Γ(T, c.W) r = resTop c.W r)

omit [IsAffine T] [Surjective i] [IsClosedImmersion i] in
include hα hφ hR in
lemma ExtensionChart.ρ_resTop (r : Γ(T, ⊤)) : c.ρ (resTop c.W r) = c.γ (c.α f r) := by
  rw [← hR, IsScalarTower.algebraMap_apply Γ(T, ⊤) Γ(X, c.V) Γ(T, c.W), hφ, hα]

/-- The value of a section of `𝒢` over `W` on the chart `(V, W)`, as a derivation
`Γ(X, V) → J(W)`; here `Γ(X, V)` acts on `J(W)` through a lift `Γ(X, V) → Γ(T, W)` of `g₀`. -/
def ChartDerivation.ev :
    ChartDerivation f i g₀ c.W →ₗ[Γ(T, ⊤)] Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i c.W) where
  toFun δ :=
    { toFun a := ⟨δ.app c le_rfl a, (δ.isChartDer c le_rfl).mem a⟩
      map_add' a b := Subtype.ext ((δ.isChartDer c le_rfl).map_add a b)
      map_smul' r a := Subtype.ext (by
        change δ.app c le_rfl (r • a) = r • δ.app c le_rfl a
        rw [Algebra.smul_def, Algebra.smul_def, hα, (δ.isChartDer c le_rfl).leibniz _ _
          (resTop c.W r) (algebraMap _ Γ(T, c.W) a) (c.ρ_resTop hα hφ hR r) (hφ a),
          (δ.isChartDer c le_rfl).map_α, mul_zero, add_zero, hR])
      map_one_eq_zero' := Subtype.ext (δ.isChartDer c le_rfl).map_one
      leibniz' a b := Subtype.ext (by
        change δ.app c le_rfl (a * b) = a • δ.app c le_rfl b + b • δ.app c le_rfl a
        rw [Algebra.smul_def, Algebra.smul_def]
        exact (δ.isChartDer c le_rfl).leibniz a b _ _ (hφ a) (hφ b)) }
  map_add' _ _ := rfl
  map_smul' r δ := by
    ext a
    change resTop c.W r * δ.app c le_rfl a = r • δ.app c le_rfl a
    rw [Algebra.smul_def, hR]

omit [IsAffine T] [Surjective i] [IsClosedImmersion i] in
lemma ChartDerivation.ev_apply (δ : ChartDerivation f i g₀ c.W) (a : Γ(X, c.V)) :
    (ev c hα hφ hR δ a : Γ(T, c.W)) = δ.app c le_rfl a :=
  rfl

omit [IsAffine T] in
include hsq in
lemma ChartDerivation.ev_injective : Function.Injective (ev c hα hφ hR) := fun _ _ h ↦
  ext_of_app_eq hsq c le_rfl le_rfl fun a ↦ congrArg Subtype.val (congrArg (· a) h)

include hsq in
lemma ChartDerivation.ev_surjective (g : Extension f (𝟙 T) i g₀ c.W) :
    Function.Surjective (ev c hα hφ hR) := by
  intro D
  let d : Γ(X, c.V) → Γ(T, c.W) := fun a ↦ D a
  have hd : IsChartDer f c d :=
    { map_add a b := by simp [d]
      mem a := (D a).2
      map_α r := by simp only [d, ← hα, Derivation.map_algebraMap, ZeroMemClass.coe_zero]
      leibniz a b a' b' ha hb := by
        have h₁ := mul_eq_zero_of_mem hsq c
          (x := a' - algebraMap _ Γ(T, c.W) a) (y := d b) (by rw [map_sub, ha, hφ, sub_self])
          ((c.mem_idealOn_iff _).mp (D b).2)
        have h₂ := mul_eq_zero_of_mem hsq c
          (x := b' - algebraMap _ Γ(T, c.W) b) (y := d a) (by rw [map_sub, hb, hφ, sub_self])
          ((c.mem_idealOn_iff _).mp (D a).2)
        have : d (a * b) = algebraMap _ Γ(T, c.W) a * d b + algebraMap _ Γ(T, c.W) b * d a := by
          simp only [d, Derivation.leibniz, Submodule.coe_add, Submodule.coe_smul_of_tower,
            Algebra.smul_def]
        rw [this]
        linear_combination -h₁ - h₂ }
  refine ⟨diff hsq g (g.ofChartDer hsq d hd), ?_⟩
  ext a
  rw [ev_apply, diff_app, Extension.chartMap_ofChartDer, add_sub_cancel_left]


omit [IsAffine T] [Surjective i] [IsClosedImmersion i] in
lemma appLE_res_apply {W W' : T.Opens} (h : W' ≤ W) (x : Γ(T, W)) :
    i.appLE W' (i ⁻¹ᵁ W') le_rfl (T.presheaf.map (homOfLE h).op x) =
      T₀.presheaf.map (homOfLE (i.preimage_mono h)).op (i.appLE W (i ⁻¹ᵁ W) le_rfl x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

omit [IsAffine T] in
include hsq in
/-- III.5.2: the sheaf `𝒢 = ℋom(g₀^* Ω_{X/T}, 𝒥)` is quasi-coherent: if `W` carries an
extension of `g₀` and a chart `(V, W)`, and `W' ⊆ W` is the locus where `r ∈ Γ(T, ⊤)` is
invertible (i.e. `Γ(T, W) → Γ(T, W')` and `Γ(T₀, i⁻¹ W) → Γ(T₀, i⁻¹ W')` are localizations away
from `r`), then `𝒢(W) → 𝒢(W')` is the localization away from `r`. -/
theorem ChartDerivation.isLocalizedModule_res [IsAffine T] [Smooth f] (c : ExtensionChart i g₀)
    (g : Extension f (𝟙 T) i g₀ c.W) {W' : T.Opens} (hW' : IsAffineOpen W') (h : W' ≤ c.W)
    (r : Γ(T, ⊤))
    (hB : @IsLocalization.Away _ _ (resTop c.W r) Γ(T, W') _
      (T.presheaf.map (homOfLE h).op).hom.toAlgebra)
    (hC : @IsLocalization.Away _ _ (c.ρ (resTop c.W r)) Γ(T₀, i ⁻¹ᵁ W') _
      (T₀.presheaf.map (homOfLE (i.preimage_mono h)).op).hom.toAlgebra)
    (L : ChartDerivation f i g₀ c.W →ₗ[Γ(T, ⊤)] ChartDerivation f i g₀ W')
    (hL : ∀ δ, L δ = res h δ) :
    IsLocalizedModule (Submonoid.powers r) L := by
  let g' : Extension f (𝟙 T) i g₀ (c.shrink hW' h).W := g.restrict h
  let _ : Algebra Γ(T, ⊤) Γ(X, c.V) := (c.α f).hom.toAlgebra
  let _ : Algebra Γ(X, c.V) Γ(T, c.W) := (g.chartMap c le_rfl).hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) Γ(T, c.W) := (resTop c.W).hom.toAlgebra
  let _ : Algebra Γ(X, c.V) Γ(T, W') := (g'.chartMap (c.shrink hW' h) le_rfl).hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) Γ(T, W') := (resTop W').hom.toAlgebra
  let _ : Algebra Γ(T, c.W) Γ(T, W') := (T.presheaf.map (homOfLE h).op).hom.toAlgebra
  let _ : Algebra Γ(T₀, i ⁻¹ᵁ c.W) Γ(T₀, i ⁻¹ᵁ W') :=
    (T₀.presheaf.map (homOfLE (i.preimage_mono h)).op).hom.toAlgebra
  have hφ' (a : Γ(X, c.V)) : g'.chartMap (c.shrink hW' h) le_rfl a =
      T.presheaf.map (homOfLE h).op (g.chartMap c le_rfl a) := by
    rw [Extension.chartMap_restrict, ← g.chartMap_map_apply c (c.shrink hW' h) le_rfl h le_rfl h,
      map_homOfLE_rfl_apply]
  have _ : IsScalarTower Γ(T, ⊤) Γ(X, c.V) Γ(T, c.W) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (g.chartMap_α_apply c le_rfl r).symm
  have _ : IsScalarTower Γ(T, ⊤) Γ(X, c.V) Γ(T, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (g'.chartMap_α_apply (c.shrink hW' h) le_rfl r).symm
  have _ : IsScalarTower Γ(T, ⊤) Γ(T, c.W) Γ(T, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (map_resTop h r).symm
  have _ : IsScalarTower Γ(X, c.V) Γ(T, c.W) Γ(T, W') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ hφ' a
  have _ : Algebra.Smooth Γ(T, ⊤) Γ(X, c.V) :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top T⟩ ⟨c.V, c.hV⟩ _
  have hα (r : Γ(T, ⊤)) : algebraMap Γ(T, ⊤) Γ(X, c.V) r = c.α f r := rfl
  let e := ev c hα (g.ρ_chartMap_apply c le_rfl) (fun _ ↦ rfl)
  let e' := ev (c.shrink hW' h) hα (g'.ρ_chartMap_apply (c.shrink hW' h) le_rfl) (fun _ ↦ rfl)
  have he : Function.Bijective e := ⟨ev_injective hsq c _ _ _, ev_surjective hsq c _ _ _ g⟩
  have he' : Function.Bijective e' :=
    ⟨ev_injective hsq _ _ _ _, ev_surjective hsq (c.shrink hW' h) _ _ _ g'⟩
  -- the restriction `J(W) → J(W')`
  let resJ : idealOn i c.W →ₗ[Γ(X, c.V)] idealOn i W' :=
    { toFun m := ⟨algebraMap Γ(T, c.W) Γ(T, W') m, by
        change i.appLE W' (i ⁻¹ᵁ W') le_rfl (T.presheaf.map (homOfLE h).op m) = 0
        rw [appLE_res_apply, (RingHom.mem_ker.mp m.2), map_zero]⟩
      map_add' m m' := Subtype.ext (map_add _ _ _)
      map_smul' a m := Subtype.ext (by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul, RingHom.id_apply]
        rw [← IsScalarTower.algebraMap_apply]) }
  have hker : IsLocalizedModule (Submonoid.powers r) (resJ.restrictScalars Γ(T, ⊤)) :=
    isLocalizedModule_ker c.ρ.hom (c.shrink hW' h).ρ.hom (fun x ↦ appLE_res_apply h x) r _
      fun _ ↦ rfl
  have hA : IsLocalizedModule (Submonoid.powers (algebraMap Γ(T, ⊤) Γ(X, c.V) r)) resJ := by
    have := IsLocalizedModule.of_restrictScalars (Submonoid.powers r) resJ
    rwa [Algebra.algebraMapSubmonoid_powers] at this
  have hD : IsLocalizedModule (Submonoid.powers (algebraMap Γ(T, ⊤) Γ(X, c.V) r))
      (resJ.compDer : Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i c.W) →ₗ[Γ(X, c.V)]
        Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i W')) :=
    isLocalizedModule_compDer _ resJ
  have hDR : IsLocalizedModule (Submonoid.powers r)
      ((resJ.compDer : Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i c.W) →ₗ[Γ(X, c.V)]
        Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i W')).restrictScalars Γ(T, ⊤)) :=
    IsLocalizedModule.restrictScalars_powers r _
  have hcomm : e' ∘ₗ L = (resJ.compDer : Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i c.W) →ₗ[Γ(X, c.V)]
      Derivation Γ(T, ⊤) Γ(X, c.V) (idealOn i W')).restrictScalars Γ(T, ⊤) ∘ₗ e := by
    ext δ a
    change (L δ).app (c.shrink hW' h) le_rfl a = T.presheaf.map (homOfLE h).op (δ.app c le_rfl a)
    rw [hL, res_app, ← δ.map_res c (c.shrink hW' h) le_rfl h le_rfl h, map_homOfLE_rfl_apply]
  have h₁ := (IsLocalizedModule.comp_iff_of_bijective_right (S := Submonoid.powers r) e he).mpr
    hDR
  rw [← hcomm] at h₁
  exact (IsLocalizedModule.comp_iff_of_bijective_left (S := Submonoid.powers r) e' he').mp h₁

end Localization

end SGA.SGA1.ExposeIII

end
