/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.ExtensionSheaf

/-!
# SGA 1, Exposé III, §5: extensions on affine charts

Let `f : X → T`, let `i : T₀ → T` be a surjective closed immersion and `g₀ : T₀ → X` a
`T`-morphism (a section of `f` over `T₀`). An extension of `g₀` over an open `U ⊆ T` is a
morphism `U → X` over `T` restricting to `g₀` (`Extension f p i g₀ U`).

This file describes extensions on affine charts, which is how SGA 1 III.5.1–5.2 computes with
them: a *chart* is a pair of affine opens `V ⊆ X`, `W ⊆ T` with `g₀(i⁻¹ W) ⊆ V`
(`ExtensionChart`), and an extension `g` over `U ⊇ W` induces a ring map
`Γ(X, V) → Γ(T, W)` (`Extension.chartMap`), which lifts `Γ(X, V) → Γ(T₀, i⁻¹ W)` and is a
`Γ(T, ⊤)`-algebra map. Conversely such ring maps over a chart with `W = U` give extensions
(`Extension.ofChartMap`), and extensions are determined by their chart maps
(`Extension.ext_of_chartMap`).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SGA.SGA1.ExposeIII

variable {X T T₀ S : Scheme.{u}} (f : X ⟶ S) (i : T₀ ⟶ T) (g₀ : T₀ ⟶ X)

/-- A chart for the extension problem of `g₀` along `i`: affine opens `V ⊆ X` and `W ⊆ T` with
`g₀(i⁻¹ W) ⊆ V`. -/
structure ExtensionChart where
  /-- The affine open of `X`. -/
  V : X.Opens
  /-- The affine open of `T`. -/
  W : T.Opens
  hV : IsAffineOpen V
  hW : IsAffineOpen W
  le : i ⁻¹ᵁ W ≤ g₀ ⁻¹ᵁ V

namespace ExtensionChart

variable {i g₀} (c : ExtensionChart i g₀)

/-- The restriction `Γ(T, W) → Γ(T₀, i⁻¹ W)`. -/
noncomputable def ρ : Γ(T, c.W) ⟶ Γ(T₀, i ⁻¹ᵁ c.W) := i.appLE c.W (i ⁻¹ᵁ c.W) le_rfl

/-- The map `Γ(X, V) → Γ(T₀, i⁻¹ W)` induced by `g₀`. -/
noncomputable def γ : Γ(X, c.V) ⟶ Γ(T₀, i ⁻¹ᵁ c.W) := g₀.appLE c.V (i ⁻¹ᵁ c.W) c.le

/-- The structure map `Γ(S, ⊤) → Γ(X, V)`. -/
noncomputable def α : Γ(S, ⊤) ⟶ Γ(X, c.V) := f.appLE ⊤ c.V (by simp)

@[reassoc]
lemma SpecMap_α_fromSpec [IsAffine S] :
    Spec.map (c.α f) ≫ (isAffineOpen_top S).fromSpec = c.hV.fromSpec ≫ f :=
  IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top S) c.hV _

lemma ρ_surjective [IsClosedImmersion i] : Function.Surjective c.ρ := by
  have := i.app_surjective c.W c.hW
  rwa [Scheme.Hom.app_eq_appLE] at this

end ExtensionChart

/-- The restriction map `Γ(T, ⊤) → Γ(T, W)`. -/
noncomputable def resTop (W : T.Opens) : Γ(T, ⊤) ⟶ Γ(T, W) := T.presheaf.map (homOfLE le_top).op

section Opens

variable {i g₀}

/-- Given `x ∈ U` and an open `V ⊆ X` containing `g₀(i⁻¹ x)`, there is an affine open `W ∋ x`
inside `U` with `g₀(i⁻¹ W) ⊆ V`. -/
lemma exists_isAffineOpen_preimage_le [IsClosedImmersion i] {U : T.Opens} {V : X.Opens} {x : T}
    (hxU : x ∈ U) (hxV : ∀ w, i w = x → g₀ w ∈ V) :
    ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ i ⁻¹ᵁ W ≤ g₀ ⁻¹ᵁ V := by
  have hcl : IsClosed (i '' (g₀ ⁻¹ᵁ V : Set T₀)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ (g₀ ⁻¹ᵁ V).2.isClosed_compl
  have hxO : x ∈ (U : Set T) ∩ (i '' (g₀ ⁻¹ᵁ V : Set T₀)ᶜ)ᶜ :=
    ⟨hxU, fun ⟨w, hw, hwx⟩ ↦ hw (hxV w hwx)⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open hxO
    (U.2.inter hcl.isOpen_compl)
  refine ⟨W, hW, hxW, fun y hy ↦ (hWO hy).1, fun w hw ↦ ?_⟩
  by_contra h
  exact (hWO hw).2 ⟨w, h, rfl⟩

/-- Variant of `exists_isAffineOpen_preimage_le` over an affine `T`, with `W` a basic open. -/
lemma exists_basicOpen_preimage_le [IsAffine T] [IsClosedImmersion i] {U : T.Opens} {V : X.Opens}
    {x : T} (hxU : x ∈ U) (hxV : ∀ w, i w = x → g₀ w ∈ V) :
    ∃ r : Γ(T, ⊤), x ∈ T.basicOpen r ∧ T.basicOpen r ≤ U ∧ i ⁻¹ᵁ T.basicOpen r ≤ g₀ ⁻¹ᵁ V := by
  obtain ⟨W, -, hxW, hWU, hW⟩ := exists_isAffineOpen_preimage_le hxU hxV
  obtain ⟨r, hrW, hxr⟩ := (isAffineOpen_top T).exists_basicOpen_le ⟨x, hxW⟩ trivial
  exact ⟨r, hxr, hrW.trans hWU, (i.preimage_mono hrW).trans hW⟩

end Opens

namespace Extension

variable {f i g₀} {p : T ⟶ S}

/-- The open immersion `Spec Γ(T, W) → U` for an affine open `W ⊆ U`. -/
noncomputable def specLift (U : T.Opens) {W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ U) :
    Spec Γ(T, W) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι hW.fromSpec (by rw [hW.range_fromSpec, Scheme.Opens.range_ι]; exact h)

@[reassoc (attr := simp)]
lemma specLift_ι (U : T.Opens) {W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ U) :
    specLift U hW h ≫ U.ι = hW.fromSpec :=
  IsOpenImmersion.lift_fac _ _ _

instance (U : T.Opens) {W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ U) :
    IsOpenImmersion (specLift U hW h) :=
  have : IsOpenImmersion (specLift U hW h ≫ U.ι) := by rw [specLift_ι]; infer_instance
  IsOpenImmersion.of_comp _ U.ι

@[reassoc]
lemma SpecMap_map_specLift (U : T.Opens) {W W' : T.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (h : W ≤ U) (h' : W' ≤ W) :
    Spec.map (T.presheaf.map (homOfLE h').op) ≫ specLift U hW h = specLift U hW' (h'.trans h) := by
  rw [← cancel_mono U.ι, Category.assoc, specLift_ι, specLift_ι, IsAffineOpen.map_fromSpec]

lemma specLift_homOfLE {U U' : T.Opens} (h : U' ≤ U) {W : T.Opens} (hW : IsAffineOpen W)
    (hW' : W ≤ U') : specLift U' hW hW' ≫ T.homOfLE h = specLift U hW (hW'.trans h) := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, specLift_ι, specLift_ι]

/-- An extension of `g₀` agrees pointwise with `g₀`. -/
lemma apply_eq {U : T.Opens} (g : Extension f p i g₀ U) (x : U.toScheme) (w : T₀)
    (hw : i w = x.1) : g.hom x = g₀ w := by
  have hwU : w ∈ i ⁻¹ᵁ U := by
    change i w ∈ U
    rw [hw]; exact x.2
  let w' : (i ⁻¹ᵁ U).toScheme := ⟨w, hwU⟩
  have hx : (i ∣_ U) w' = x := by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact hw
  rw [← hx, ← Scheme.Hom.comp_apply, g.hom_extends, Scheme.Hom.comp_apply]
  rfl

variable [Surjective i]

lemma range_specLift_comp_subset {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    Set.range (specLift U c.hW hc ≫ g.hom) ⊆ Set.range c.hV.fromSpec := by
  rintro _ ⟨z, rfl⟩
  rw [c.hV.range_fromSpec]
  obtain ⟨w, hw⟩ := i.surjective (specLift U c.hW hc z).1
  have hwW : w ∈ i ⁻¹ᵁ c.W := by
    have h₁ : U.ι (specLift U c.hW hc z) = c.hW.fromSpec z := by
      rw [← Scheme.Hom.comp_apply, specLift_ι]
    have h₂ := Set.mem_range_self (f := c.hW.fromSpec) z
    rw [c.hW.range_fromSpec, ← h₁] at h₂
    change i w ∈ c.W
    rw [hw]
    exact h₂
  rw [Scheme.Hom.comp_apply, apply_eq g _ w hw]
  exact c.le hwW

/-- The ring map `Γ(X, V) → Γ(T, W)` induced by an extension `g` over `U ⊇ W` on a chart
`(V, W)`. -/
noncomputable def chartMap {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) : Γ(X, c.V) ⟶ Γ(T, c.W) :=
  Spec.preimage (IsOpenImmersion.lift c.hV.fromSpec _ (range_specLift_comp_subset g c hc))

@[reassoc]
lemma SpecMap_chartMap {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    Spec.map (g.chartMap c hc) ≫ c.hV.fromSpec = specLift U c.hW hc ≫ g.hom := by
  rw [chartMap, Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma chartMap_eq_iff {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) (φ : Γ(X, c.V) ⟶ Γ(T, c.W)) :
    g.chartMap c hc = φ ↔ Spec.map φ ≫ c.hV.fromSpec = specLift U c.hW hc ≫ g.hom := by
  refine ⟨fun h ↦ h ▸ SpecMap_chartMap g c hc, fun h ↦ Spec.map_injective ?_⟩
  rw [← cancel_mono c.hV.fromSpec, h, SpecMap_chartMap]

/-- The chart map of an extension lifts the map induced by `g₀`. -/
@[reassoc (attr := simp)]
lemma chartMap_ρ [IsClosedImmersion i] {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) : g.chartMap c hc ≫ c.ρ = c.γ := by
  have hW₀ : IsAffineOpen (i ⁻¹ᵁ c.W) := c.hW.preimage i
  apply Spec.map_injective
  rw [← cancel_mono c.hV.fromSpec, ExtensionChart.γ,
    IsAffineOpen.SpecMap_appLE_fromSpec g₀ c.hV hW₀, Spec.map_comp, Category.assoc,
    SpecMap_chartMap]
  -- `Spec Γ(T₀, i⁻¹ W) → Spec Γ(T, W) → U` factors through `i⁻¹ U`
  have hle : i ⁻¹ᵁ c.W ≤ i ⁻¹ᵁ U := i.preimage_mono hc
  have key : Spec.map c.ρ ≫ specLift U c.hW hc =
      specLift (i ⁻¹ᵁ U) hW₀ hle ≫ (i ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, specLift_ι, ExtensionChart.ρ,
      IsAffineOpen.SpecMap_appLE_fromSpec i c.hW hW₀, Category.assoc, morphismRestrict_ι,
      specLift_ι_assoc]
  rw [reassoc_of% key, g.hom_extends, specLift_ι_assoc]

/-- The chart map of an extension is a `Γ(S, ⊤)`-algebra map. -/
@[reassoc]
lemma α_chartMap_eq_appLE [IsAffine S] {U : T.Opens} (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    c.α f ≫ g.chartMap c hc = p.appLE ⊤ c.W (le_top.trans_eq p.preimage_top.symm) := by
  apply Spec.map_injective
  rw [← cancel_mono (isAffineOpen_top S).fromSpec, Spec.map_comp, Category.assoc,
    ExtensionChart.SpecMap_α_fromSpec, SpecMap_chartMap_assoc, g.hom_comp, specLift_ι_assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top S) c.hW]

lemma id_appLE_top_eq_resTop (W : T.Opens) :
    Scheme.Hom.appLE (𝟙 T) ⊤ W (le_top.trans_eq (Scheme.Hom.preimage_top (𝟙 T)).symm) = resTop W :=
  rfl

/-- The chart map of an extension is a `Γ(T, ⊤)`-algebra map. -/
@[reassoc (attr := simp)]
lemma α_chartMap [IsAffine T] {f' : X ⟶ T} {U : T.Opens} (g : Extension f' (𝟙 T) i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U) : c.α f' ≫ g.chartMap c hc = resTop c.W := by
  rw [α_chartMap_eq_appLE, id_appLE_top_eq_resTop]

/-- Chart maps do not depend on the open on which the extension is considered. -/
lemma chartMap_restrict {U U' : T.Opens} (h : U' ≤ U) (g : Extension f p i g₀ U)
    (c : ExtensionChart i g₀) (hc : c.W ≤ U') :
    (g.restrict h).chartMap c hc = g.chartMap c (hc.trans h) := by
  rw [chartMap_eq_iff, SpecMap_chartMap, Extension.restrict_hom, ← Category.assoc,
    specLift_homOfLE]

/-- Naturality of chart maps with respect to smaller charts. -/
@[reassoc]
lemma map_chartMap {U : T.Opens} (g : Extension f p i g₀ U)
    (c c' : ExtensionChart i g₀) (hc : c.W ≤ U) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) :
    X.presheaf.map (homOfLE hV).op ≫ g.chartMap c' hc' =
      g.chartMap c hc ≫ T.presheaf.map (homOfLE hW).op := by
  apply Spec.map_injective
  rw [← cancel_mono c.hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc,
    IsAffineOpen.map_fromSpec c.hV c'.hV, SpecMap_chartMap, Category.assoc, SpecMap_chartMap,
    SpecMap_map_specLift_assoc]

variable [IsClosedImmersion i]

/-- Extensions are determined by their chart maps. -/
lemma ext_of_chartMap {U : T.Opens} {g g' : Extension f p i g₀ U}
    (h : ∀ (c : ExtensionChart i g₀) (hc : c.W ≤ U), g.chartMap c hc = g'.chartMap c hc) :
    g = g' := by
  refine Extension.ext (Scheme.hom_ext_of_forall _ _ fun x ↦ ?_)
  obtain ⟨w, hw⟩ := i.surjective x.1
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g₀ w)) isOpen_univ
  obtain ⟨W, hW, hxW, hWU, hWV⟩ := exists_isAffineOpen_preimage_le (i := i) (g₀ := g₀)
    (V := V) x.2 fun w' hw' ↦ by
      rwa [i.isClosedEmbedding.injective (hw'.trans hw.symm)]
  let c : ExtensionChart i g₀ := ⟨V, W, hV, hW, hWV⟩
  have hc := h c hWU
  rw [chartMap_eq_iff, SpecMap_chartMap] at hc
  refine ⟨U.ι ⁻¹ᵁ W, hxW, ?_⟩
  have hrange : Set.range (U.ι ⁻¹ᵁ W).ι ⊆ Set.range (specLift U hW hWU) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ : ((U.ι ⁻¹ᵁ W).ι y).1 ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]; exact y.2
    refine ⟨z, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, specLift_ι, hz]
    rfl
  rw [← IsOpenImmersion.lift_fac _ _ hrange, Category.assoc, Category.assoc, hc]

omit [Surjective i] [IsClosedImmersion i] in
/-- The extension defined by a ring map on a chart with `W = U`, over an affine base `S`. -/
noncomputable def ofChartMapS [IsAffine S] (c : ExtensionChart i g₀) (ψ : Γ(X, c.V) ⟶ Γ(T, c.W))
    (h₁ : c.α f ≫ ψ = p.appLE ⊤ c.W (le_top.trans_eq p.preimage_top.symm))
    (h₂ : ψ ≫ c.ρ = c.γ) :
    Extension f p i g₀ c.W := by
  refine ⟨c.hW.isoSpec.hom ≫ Spec.map ψ ≫ c.hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← ExtensionChart.SpecMap_α_fromSpec,
      ← Spec.map_comp_assoc, h₁, IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top S) c.hW,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  · have hW₀ : IsAffineOpen (i ⁻¹ᵁ c.W) := c.hW.preimage i
    have hL : (i ∣_ c.W) ≫ c.hW.isoSpec.hom = hW₀.isoSpec.hom ≫ Spec.map c.ρ := by
      rw [← cancel_mono c.hW.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
        morphismRestrict_ι, Category.assoc, ExtensionChart.ρ,
        IsAffineOpen.SpecMap_appLE_fromSpec i c.hW hW₀ le_rfl,
        IsAffineOpen.isoSpec_hom_fromSpec_assoc]
    rw [← Category.assoc, hL, Category.assoc, ← Spec.map_comp_assoc, h₂, ExtensionChart.γ,
      IsAffineOpen.SpecMap_appLE_fromSpec g₀ c.hV hW₀ c.le,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc]

lemma chartMap_ofChartMapS [IsAffine S] (c : ExtensionChart i g₀) (ψ : Γ(X, c.V) ⟶ Γ(T, c.W))
    (h₁ : c.α f ≫ ψ = p.appLE ⊤ c.W (le_top.trans_eq p.preimage_top.symm))
    (h₂ : ψ ≫ c.ρ = c.γ) :
    (ofChartMapS c ψ h₁ h₂).chartMap c le_rfl = ψ := by
  rw [chartMap_eq_iff]
  change _ = _ ≫ c.hW.isoSpec.hom ≫ Spec.map ψ ≫ c.hV.fromSpec
  have : specLift c.W c.hW le_rfl = c.hW.isoSpec.inv := by
    rw [← cancel_mono c.W.ι, specLift_ι, IsAffineOpen.isoSpec_inv_ι]
  rw [this, Iso.inv_hom_id_assoc]

/-- The extension defined by a ring map on a chart with `W = U`. -/
noncomputable def ofChartMap [IsAffine T] {f' : X ⟶ T} (c : ExtensionChart i g₀)
    (ψ : Γ(X, c.V) ⟶ Γ(T, c.W)) (h₁ : c.α f' ≫ ψ = resTop c.W) (h₂ : ψ ≫ c.ρ = c.γ) :
    Extension f' (𝟙 T) i g₀ c.W :=
  ofChartMapS c ψ (h₁.trans (id_appLE_top_eq_resTop c.W).symm) h₂

lemma chartMap_ofChartMap [IsAffine T] {f' : X ⟶ T} (c : ExtensionChart i g₀)
    (ψ : Γ(X, c.V) ⟶ Γ(T, c.W)) (h₁ : c.α f' ≫ ψ = resTop c.W) (h₂ : ψ ≫ c.ρ = c.γ) :
    (ofChartMap c ψ h₁ h₂).chartMap c le_rfl = ψ :=
  chartMap_ofChartMapS c ψ _ h₂

end Extension

end SGA.SGA1.ExposeIII
