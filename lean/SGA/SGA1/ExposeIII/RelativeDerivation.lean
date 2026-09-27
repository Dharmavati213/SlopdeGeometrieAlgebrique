/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.DerivationSheaf

/-!
# SGA 1, Exposé III, §5.2 over an affine base: the sheaf `𝒢` for a non-affine thickening

Let `f : X → S` be a morphism to an affine scheme, `p : T → S`, `i : T₀ → T` a surjective closed
immersion whose ideal has square zero on affine opens, and `g₀ : T₀ → X` an `S`-morphism. As in
`DerivationSheaf.lean`, sections over an open `U ⊆ T` of `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)` are described
as compatible families of derivations `Γ(X, V) → J(W)` on the affine charts `(V, W)` with
`W ⊆ U` (`RelChartDerivation`), now `Γ(S, ⊤)`-linear. Here `T` need not be affine: the base
condition only involves `S`.

* `RelChartDerivation.diff`: the difference `g' - g ∈ 𝒢(U)` of two extensions (III.5.2), with
  `diff_add_diff`, `diff_eq_zero_iff`;
* `Extension.ofRelChartDer`, `RelChartDerivation.diff_ofRelChartDer`: `𝒢(W)` acts transitively on
  the extensions over an affine chart `W` (III.5.2);
* `RelChartDerivation.ext_of_app_eq`: a section over `U` is determined by its value on one chart
  `(V, U)`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace SGA.SGA1.ExposeIII

variable {X T T₀ S : Scheme.{u}} (f : X ⟶ S) {i : T₀ ⟶ T} {g₀ : T₀ ⟶ X}

/-- A derivation on a chart `(V, W)` relative to `f : X → S`: an additive map `Γ(X, V) → J(W)`
vanishing on `Γ(S, ⊤)` and satisfying the Leibniz rule with respect to lifts of `g₀`. -/
structure IsRelChartDer (c : ExtensionChart i g₀) (d : Γ(X, c.V) → Γ(T, c.W)) : Prop where
  map_add (a b : Γ(X, c.V)) : d (a + b) = d a + d b
  mem (a : Γ(X, c.V)) : d a ∈ idealOn i c.W
  map_α (r : Γ(S, ⊤)) : d (c.α f r) = 0
  leibniz (a b : Γ(X, c.V)) (a' b' : Γ(T, c.W)) : c.ρ a' = c.γ a → c.ρ b' = c.γ b →
    d (a * b) = a' * d b + b' * d a

/-- The condition for a family of chart derivations to be a section of `𝒢` over `U`. -/
structure IsRelChartDerivation {U : T.Opens} (δ : ChartFamily i g₀ U) : Prop where
  isChartDer (c : ExtensionChart i g₀) (hc : c.W ≤ U) : IsRelChartDer f c (δ ⟨c, hc⟩)
  map_res (c c' : ExtensionChart i g₀) (hc : c.W ≤ U) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    δ ⟨c', hc'⟩ (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (δ ⟨c, hc⟩ a)

variable (i g₀) in
/-- III.5.2: the group `𝒢(U)`, for `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)`. -/
def relChartDerivations (U : T.Opens) : AddSubgroup (ChartFamily i g₀ U) where
  carrier := {δ | IsRelChartDerivation f δ}
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
/-- III.5.2: sections over `U` of `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)`. -/
abbrev RelChartDerivation (U : T.Opens) : Type u := relChartDerivations f i g₀ U

namespace RelChartDerivation

variable {f} {U : T.Opens}

/-- The value of a section of `𝒢` on a chart `(V, W)` with `W ⊆ U`. -/
def app (δ : RelChartDerivation f i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    Γ(X, c.V) → Γ(T, c.W) :=
  δ.1 ⟨c, hc⟩

lemma isChartDer (δ : RelChartDerivation f i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    IsRelChartDer f c (δ.app c hc) :=
  δ.2.isChartDer c hc

lemma map_res (δ : RelChartDerivation f i g₀ U) (c c' : ExtensionChart i g₀) (hc : c.W ≤ U)
    (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V) (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    δ.app c' hc' (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (δ.app c hc a) :=
  δ.2.map_res c c' hc hc' hV hW a

@[ext]
lemma ext {δ δ' : RelChartDerivation f i g₀ U}
    (h : ∀ c hc a, δ.app c hc a = δ'.app c hc a) : δ = δ' :=
  Subtype.ext (funext fun c ↦ funext fun a ↦ h c.1 c.2 a)

/-- Evaluation of sections of `𝒢` on a chart at an element, as an additive map. -/
def appAddHom (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V)) :
    RelChartDerivation f i g₀ U →+ Γ(T, c.W) where
  toFun δ := δ.app c hc a
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma appAddHom_apply (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V))
    (δ : RelChartDerivation f i g₀ U) : appAddHom c hc a δ = δ.app c hc a := rfl

@[simp] lemma add_app (δ δ' : RelChartDerivation f i g₀ U) (c hc a) :
    (δ + δ').app c hc a = δ.app c hc a + δ'.app c hc a := rfl

@[simp] lemma neg_app (δ : RelChartDerivation f i g₀ U) (c hc a) :
    (-δ).app c hc a = -δ.app c hc a := rfl

@[simp] lemma sub_app (δ δ' : RelChartDerivation f i g₀ U) (c hc a) :
    (δ - δ').app c hc a = δ.app c hc a - δ'.app c hc a := rfl

@[simp] lemma zero_app (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a) :
    (0 : RelChartDerivation f i g₀ U).app c hc a = 0 := rfl

/-- Restriction of sections of `𝒢` to a smaller open. -/
def res {U U' : T.Opens} (h : U' ≤ U) :
    RelChartDerivation f i g₀ U →+ RelChartDerivation f i g₀ U' where
  toFun δ := ⟨fun c ↦ δ.app c.1 (c.2.trans h),
    { isChartDer c hc := δ.isChartDer c (hc.trans h)
      map_res c c' hc hc' := δ.map_res c c' (hc.trans h) (hc'.trans h) }⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma res_app {U U' : T.Opens} (h : U' ≤ U) (δ : RelChartDerivation f i g₀ U) (c hc a) :
    (res h δ).app c hc a = δ.app c (hc.trans h) a := rfl

end RelChartDerivation

variable (i g₀)

/-- III.5.2: the presheaf of abelian groups `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)` on `T`. -/
def relDerivationPresheaf : TopCat.Presheaf AddCommGrpCat.{u} T where
  obj U := AddCommGrpCat.of (RelChartDerivation f i g₀ U.unop)
  map h := AddCommGrpCat.ofHom (RelChartDerivation.res h.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {f i g₀}

/-- Evaluation of sections of `𝒢` on a chart at an element, on the presheaf `𝒢`. -/
def relDerivationPresheafEval {V : T.Opens} (c : ExtensionChart i g₀) (hc : c.W ≤ V)
    (a : Γ(X, c.V)) : (relDerivationPresheaf f i g₀).obj (op V) →+ Γ(T, c.W) :=
  RelChartDerivation.appAddHom c hc a

section Diff

variable {p : T ⟶ S}

lemma Extension.ρ_chartMap_apply' [Surjective i] [IsClosedImmersion i] {U : T.Opens}
    (g : Extension f p i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V)) :
    c.ρ (g.chartMap c hc a) = c.γ a := by
  rw [← ConcreteCategory.comp_apply, Extension.chartMap_ρ]

lemma Extension.chartMap_α_apply' [IsAffine S] [Surjective i] {U : T.Opens}
    (g : Extension f p i g₀ U) (c : ExtensionChart i g₀) (hc : c.W ≤ U) (r : Γ(S, ⊤)) :
    g.chartMap c hc (c.α f r) = p.appLE ⊤ c.W (le_top.trans_eq p.preimage_top.symm) r := by
  rw [← ConcreteCategory.comp_apply, Extension.α_chartMap_eq_appLE]

lemma Extension.chartMap_map_apply' [Surjective i] {U : T.Opens} (g : Extension f p i g₀ U)
    (c c' : ExtensionChart i g₀) (hc : c.W ≤ U) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    g.chartMap c' hc' (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (g.chartMap c hc a) := by
  rw [← ConcreteCategory.comp_apply, Extension.map_chartMap g c c' hc hc' hV hW,
    ConcreteCategory.comp_apply]

variable [IsAffine S] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

/-- III.5.2: the difference `g' - g ∈ 𝒢(U)` of two extensions over `U`. -/
def RelChartDerivation.diff {U : T.Opens} (g g' : Extension f p i g₀ U) :
    RelChartDerivation f i g₀ U :=
  ⟨fun c a ↦ g'.chartMap c.1 c.2 a - g.chartMap c.1 c.2 a,
    { isChartDer c hc :=
        { map_add a b := by simp only [map_add]; abel
          mem a := by
            rw [ExtensionChart.mem_idealOn_iff, map_sub, g.ρ_chartMap_apply',
              g'.ρ_chartMap_apply', sub_self]
          map_α r := by rw [g.chartMap_α_apply', g'.chartMap_α_apply', sub_self]
          leibniz a b a' b' ha hb := by
            have h₁ : (a' - g'.chartMap c hc a) * (g'.chartMap c hc b - g.chartMap c hc b) = 0 :=
              mul_eq_zero_of_mem hsq c (by rw [map_sub, ha, g'.ρ_chartMap_apply', sub_self])
                (by rw [map_sub, g.ρ_chartMap_apply', g'.ρ_chartMap_apply', sub_self])
            have h₂ : (b' - g.chartMap c hc b) * (g'.chartMap c hc a - g.chartMap c hc a) = 0 :=
              mul_eq_zero_of_mem hsq c (by rw [map_sub, hb, g.ρ_chartMap_apply', sub_self])
                (by rw [map_sub, g.ρ_chartMap_apply', g'.ρ_chartMap_apply', sub_self])
            simp only [map_mul]
            linear_combination -h₁ - h₂ }
      map_res c c' hc hc' hV hW a := by
        rw [g.chartMap_map_apply' c c' hc hc' hV hW, g'.chartMap_map_apply' c c' hc hc' hV hW,
          map_sub] }⟩

namespace RelChartDerivation

@[simp] lemma diff_app {U : T.Opens} (g g' : Extension f p i g₀ U) (c hc a) :
    (diff hsq g g').app c hc a = g'.chartMap c hc a - g.chartMap c hc a := rfl

lemma diff_add_diff {U : T.Opens} (g g' g'' : Extension f p i g₀ U) :
    diff hsq g g' + diff hsq g' g'' = diff hsq g g'' :=
  ext fun c hc a ↦ by simp only [add_app, diff_app]; abel

lemma diff_self {U : T.Opens} (g : Extension f p i g₀ U) : diff hsq g g = 0 :=
  ext fun c hc a ↦ by simp

lemma neg_diff {U : T.Opens} (g g' : Extension f p i g₀ U) :
    -diff hsq g g' = diff hsq g' g :=
  ext fun c hc a ↦ by simp

lemma res_diff {U U' : T.Opens} (h : U' ≤ U) (g g' : Extension f p i g₀ U) :
    res h (diff hsq g g') = diff hsq (g.restrict h) (g'.restrict h) :=
  ext fun c hc a ↦ by simp [Extension.chartMap_restrict]

/-- III.5.2: two extensions with difference zero are equal. -/
lemma diff_eq_zero_iff {U : T.Opens} (g g' : Extension f p i g₀ U) :
    diff hsq g g' = 0 ↔ g = g' := by
  refine ⟨fun h ↦ Extension.ext_of_chartMap fun c hc ↦ ?_, fun h ↦ h ▸ diff_self hsq g⟩
  ext a
  have := congrArg (fun δ : RelChartDerivation f i g₀ U ↦ δ.app c hc a) h
  simp only [diff_app, zero_app, sub_eq_zero] at this
  exact this.symm

end RelChartDerivation

end Diff

section Local

variable [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

include hsq in
/-- A section of `𝒢` over `U` is determined by its value on a single chart `(V, U)`. -/
theorem RelChartDerivation.eq_zero_of_app_eq_zero {U : T.Opens}
    (δ : RelChartDerivation f i g₀ U) (c₀ : ExtensionChart i g₀) (hc₀ : c₀.W ≤ U)
    (hU : U ≤ c₀.W) (h : ∀ a, δ.app c₀ hc₀ a = 0) : δ = 0 := by
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
theorem RelChartDerivation.ext_of_app_eq {U : T.Opens} {δ δ' : RelChartDerivation f i g₀ U}
    (c₀ : ExtensionChart i g₀) (hc₀ : c₀.W ≤ U) (hU : U ≤ c₀.W)
    (h : ∀ a, δ.app c₀ hc₀ a = δ'.app c₀ hc₀ a) : δ = δ' :=
  sub_eq_zero.mp (eq_zero_of_app_eq_zero hsq _ c₀ hc₀ hU fun a ↦ by
    rw [sub_app, h, sub_self])

end Local

section Modify

lemma IsRelChartDer.map_zero {c : ExtensionChart i g₀} {d : Γ(X, c.V) → Γ(T, c.W)}
    (hd : IsRelChartDer f c d) : d 0 = 0 := by
  have := hd.map_add 0 0
  rw [add_zero, left_eq_add] at this
  exact this

lemma IsRelChartDer.map_one {c : ExtensionChart i g₀} {d : Γ(X, c.V) → Γ(T, c.W)}
    (hd : IsRelChartDer f c d) : d 1 = 0 := by
  have := hd.leibniz 1 1 1 1 (by simp) (by simp)
  rw [mul_one, one_mul, left_eq_add] at this
  exact this

/-- The ring map `φ + d : Γ(X, V) → Γ(T, W)` for a lift `φ` of `g₀` and a derivation `d` on the
chart `(V, W)`. -/
def addRelChartMap (hsq : IsSqZeroOn i) (c : ExtensionChart i g₀) (φ : Γ(X, c.V) ⟶ Γ(T, c.W))
    (hφ : ∀ a, c.ρ (φ a) = c.γ a) (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsRelChartDer f c d) :
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

lemma addRelChartMap_apply (hsq : IsSqZeroOn i) (c : ExtensionChart i g₀)
    (φ : Γ(X, c.V) ⟶ Γ(T, c.W)) (hφ : ∀ a, c.ρ (φ a) = c.γ a) (d : Γ(X, c.V) → Γ(T, c.W))
    (hd : IsRelChartDer f c d) (a : Γ(X, c.V)) :
    addRelChartMap hsq c φ hφ d hd a = φ a + d a :=
  rfl

variable {p : T ⟶ S} [IsAffine S] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

/-- III.5.2: the extension `g + d` over an affine `W`, for a derivation `d` on a chart `(V, W)`. -/
def Extension.ofRelChartDer {c : ExtensionChart i g₀} (g : Extension f p i g₀ c.W)
    (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsRelChartDer f c d) : Extension f p i g₀ c.W :=
  Extension.ofChartMapS c
    (addRelChartMap hsq c (g.chartMap c le_rfl) (g.ρ_chartMap_apply' c le_rfl) d hd)
    (by ext r; simp [addRelChartMap_apply, g.chartMap_α_apply', hd.map_α])
    (by
      ext a
      change c.ρ (g.chartMap c le_rfl a + d a) = c.γ a
      have h₀ : c.ρ (d a) = 0 := (c.mem_idealOn_iff _).mp (hd.mem a)
      rw [map_add, g.ρ_chartMap_apply', h₀, add_zero])

lemma Extension.chartMap_ofRelChartDer {c : ExtensionChart i g₀}
    (g : Extension f p i g₀ c.W) (d : Γ(X, c.V) → Γ(T, c.W)) (hd : IsRelChartDer f c d)
    (a : Γ(X, c.V)) :
    (g.ofRelChartDer hsq d hd).chartMap c le_rfl a = g.chartMap c le_rfl a + d a := by
  rw [Extension.ofRelChartDer, Extension.chartMap_ofChartMapS, addRelChartMap_apply]

/-- III.5.2: `𝒢(W)` acts transitively on the extensions over `W`: `(g + δ) - g = δ`. -/
lemma RelChartDerivation.diff_ofRelChartDer {c : ExtensionChart i g₀}
    (g : Extension f p i g₀ c.W) (δ : RelChartDerivation f i g₀ c.W) :
    diff hsq g (g.ofRelChartDer hsq (δ.app c le_rfl) (δ.isChartDer c le_rfl)) = δ :=
  ext_of_app_eq hsq c le_rfl le_rfl fun a ↦ by
    rw [diff_app, Extension.chartMap_ofRelChartDer, add_sub_cancel_left]

end Modify

end SGA.SGA1.ExposeIII
