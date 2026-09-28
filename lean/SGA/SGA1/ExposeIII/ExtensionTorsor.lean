/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.GlobalExtension
import SGA.Foundations.Etale.Torsor

/-!
# SGA 1, Exposé III, 5.1–5.2: the torsor of extensions

Let `f : X → T` be a morphism with `T` affine, `i : T₀ → T` a surjective closed immersion whose
ideal `𝒥` has square zero, and `g₀ : T₀ → X` a section of `f` over `T₀`. SGA 1 III.5.1 states
that the sheaf `𝒫(g₀)` of extensions of `g₀` is formally principal homogeneous under
`𝒢 = ℋom(g₀^* Ω_{X/T}, 𝒥)`, and III.5.2 that it is a torsor when `f` is smooth.

* `ChartDerivation.eq_of_res_eq`, `ChartDerivation.exists_res_eq`: `𝒢` is a sheaf;
* `Extension.exists_diff_eq`, `Extension.vadd`: the action of `𝒢(U)` on the extensions over
  any open `U`, and `Extension.diff_vadd`, `Extension.vadd_diff`: it is simply transitive
  (III.5.1);
* `extensionTorsor`: when `f` is smooth, the extensions form a torsor under `𝒢` in the sense of
  `CategoryTheory.Torsor` (III.5.2); its class in `H¹(T, 𝒢)` vanishes if and only if `g₀` extends
  to `T` (`extensionTorsor_class_eq_trivialClass_iff`), and it does vanish since `T` is affine
  (`extensionTorsor_class_eq_trivialClass`, III.5.5).

`T` is assumed affine, and `𝒢` consists of `Γ(T, ⊤)`-linear derivations; the general situation
of SGA (a morphism `X → S` and an `S`-morphism `g₀ : Y₀ → X`) reduces to this one by base change
to `Y` (`exists_extension_of_isSqZeroOn`) and localization on `Y`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace SGA.SGA1.ExposeIII

variable {X T T₀ : Scheme.{u}} {f : X ⟶ T} {i : T₀ ⟶ T} {g₀ : T₀ ⟶ X}

section Sheaf

variable [Surjective i] [IsClosedImmersion i]

omit [Surjective i] [IsClosedImmersion i] in
/-- Two composites of restriction maps with the same source and target agree. -/
lemma presheaf_map_map_apply' {Y : Scheme.{u}} {A B C : Y.Opens} (f : A ⟶ B) (g : B ⟶ C)
    (h : A ⟶ C) (x : Γ(Y, C)) :
    Y.presheaf.map f.op (Y.presheaf.map g.op x) = Y.presheaf.map h.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (f ≫ g) h]

omit [Surjective i] [IsClosedImmersion i] in
/-- Two sections of the structure sheaf which agree near every point are equal. -/
lemma eq_of_locally_zero' {Y : Scheme.{u}} {W : Y.Opens} (s t : Γ(Y, W))
    (h : ∀ x ∈ W, ∃ (W' : Y.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      Y.presheaf.map (homOfLE hW').op s = Y.presheaf.map (homOfLE hW').op t) : s = t := by
  rw [← sub_eq_zero]
  refine eq_zero_of_locally_zero _ fun x hx ↦ ?_
  obtain ⟨W', hW', hx', h'⟩ := h x hx
  exact ⟨W', hW', hx', by rw [map_sub, h', sub_self]⟩

/-- Every point of `W` lies in an affine open inside `W ⊓ V`, given that it lies in `V`. -/
lemma exists_isAffineOpen_le_inf {Y : Scheme.{u}} {W V : Y.Opens} {x : Y} (hxW : x ∈ W)
    (hxV : x ∈ V) : ∃ W' : Y.Opens, IsAffineOpen W' ∧ x ∈ W' ∧ W' ≤ W ∧ W' ≤ V := by
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'O⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W ⊓ V : Y.Opens) from ⟨hxW, hxV⟩) (W ⊓ V).2
  exact ⟨W', hW', hxW', fun y hy ↦ (hW'O hy).1, fun y hy ↦ (hW'O hy).2⟩

omit [Surjective i] [IsClosedImmersion i] in
/-- III.5.2: `𝒢` is separated: sections over `U` agreeing on the members of an open cover of
`U` are equal. -/
theorem ChartDerivation.eq_of_res_eq {ι : Type*} {U : T.Opens} (V : ι → T.Opens)
    (hV : ∀ j, V j ≤ U) (hcov : U ≤ ⨆ j, V j) {δ δ' : ChartDerivation f i g₀ U}
    (h : ∀ j, res (hV j) δ = res (hV j) δ') : δ = δ' := by
  ext c hc a
  rw [← sub_eq_zero]
  refine eq_zero_of_locally_zero _ fun x hx ↦ ?_
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov (hc hx))
  obtain ⟨W, hW, hxW, hWc, hWV⟩ := exists_isAffineOpen_le_inf hx hj
  refine ⟨W, hWc, hxW, ?_⟩
  have h₁ := δ.map_res c (c.shrink hW hWc) hc (hWc.trans hc) le_rfl hWc a
  have h₂ := δ'.map_res c (c.shrink hW hWc) hc (hWc.trans hc) le_rfl hWc a
  have h₃ := congrArg (fun δ ↦ ChartDerivation.app δ (c.shrink hW hWc) hWV
    (X.presheaf.map (homOfLE (le_refl c.V)).op a)) (h j)
  simp only [res_app] at h₃
  rw [map_sub, ← h₁, ← h₂]
  exact sub_eq_zero.mpr h₃


section Glue

variable {ι : Type u} {U : T.Opens} (V : ι → T.Opens) (δ : ∀ j, ChartDerivation f i g₀ (V j))
  (hδ : ∀ j k, ChartDerivation.res (inf_le_left : V j ⊓ V k ≤ V j) (δ j) =
    ChartDerivation.res inf_le_right (δ k))

/-- (Implementation) The affine opens `W ⊆ c.W` contained in some `V j`, indexed with such a `j`. -/
def GlueIndex (c : ExtensionChart i g₀) : Type u :=
  {p : ι × T.Opens // IsAffineOpen p.2 ∧ p.2 ≤ c.W ∧ p.2 ≤ V p.1}

variable {V}

omit [Surjective i] [IsClosedImmersion i] in
lemma iSup_glueIndex (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U) :
    c.W ≤ ⨆ p : GlueIndex V c, p.1.2 := by
  intro x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov (hc hx))
  obtain ⟨W, hW, hxW, hWc, hWV⟩ := exists_isAffineOpen_le_inf hx hj
  exact Opens.mem_iSup.mpr ⟨⟨(j, W), hW, hWc, hWV⟩, hxW⟩

/-- (Implementation) The local values of the glued section on a chart. -/
def glueLocal (c : ExtensionChart i g₀) (a : Γ(X, c.V)) (p : GlueIndex V c) : Γ(T, p.1.2) :=
  (δ p.1.1).app (c.shrink p.2.1 p.2.2.1) p.2.2.2 a

include hδ in
omit [Surjective i] [IsClosedImmersion i] in
lemma glueLocal_res (c : ExtensionChart i g₀) (a : Γ(X, c.V)) (p : GlueIndex V c)
    {W : T.Opens} (hW : IsAffineOpen W) (hWp : W ≤ p.1.2) (j : ι) (hWj : W ≤ V j) :
    T.presheaf.map (homOfLE hWp).op (glueLocal δ c a p) =
      (δ j).app (c.shrink hW (hWp.trans p.2.2.1)) hWj a := by
  rw [glueLocal, ← (δ p.1.1).map_res (c.shrink p.2.1 p.2.2.1) (c.shrink hW (hWp.trans p.2.2.1))
    p.2.2.2 (hWp.trans p.2.2.2) le_rfl hWp, map_homOfLE_rfl_apply]
  have := congrArg (fun δ' ↦ ChartDerivation.app δ' (c.shrink hW (hWp.trans p.2.2.1))
    (le_inf (hWp.trans p.2.2.2) hWj) a) (hδ p.1.1 j)
  simpa using this

include hδ in
omit [Surjective i] [IsClosedImmersion i] in
lemma glueLocal_compatible (c : ExtensionChart i g₀) (a : Γ(X, c.V)) :
    TopCat.Presheaf.IsCompatible T.presheaf (fun p : GlueIndex V c ↦ p.1.2)
      (glueLocal δ c a) := by
  intro p q
  refine eq_of_locally_zero' _ _ fun x hx ↦ ?_
  obtain ⟨W, hW, hxW, hWp, hWq⟩ := exists_isAffineOpen_le_inf hx.1 hx.2
  refine ⟨W, le_inf hWp hWq, hxW, ?_⟩
  rw [presheaf_map_map_apply' _ _ (homOfLE hWp), presheaf_map_map_apply' _ _ (homOfLE hWq)]
  exact (glueLocal_res δ hδ c a p hW hWp p.1.1 (hWp.trans p.2.2.2)).trans
    (glueLocal_res δ hδ c a q hW hWq p.1.1 (hWp.trans p.2.2.2)).symm


omit [Surjective i] [IsClosedImmersion i] in
lemma ExtensionChart.shrink_γ (c : ExtensionChart i g₀) {W : T.Opens} (hW : IsAffineOpen W)
    (h : W ≤ c.W) (a : Γ(X, c.V)) :
    (c.shrink hW h).γ a = T₀.presheaf.map (homOfLE (i.preimage_mono h)).op (c.γ a) := by
  rw [ExtensionChart.γ, ExtensionChart.γ, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

omit [Surjective i] [IsClosedImmersion i] in
lemma ExtensionChart.shrink_ρ (c : ExtensionChart i g₀) {W : T.Opens} (hW : IsAffineOpen W)
    (h : W ≤ c.W) (x : Γ(T, c.W)) :
    (c.shrink hW h).ρ (T.presheaf.map (homOfLE h).op x) =
      T₀.presheaf.map (homOfLE (i.preimage_mono h)).op (c.ρ x) :=
  appLE_res_apply h x

include hδ in
omit [Surjective i] [IsClosedImmersion i] in
lemma exists_glueVal (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U)
    (a : Γ(X, c.V)) : ∃! t : Γ(T, c.W), ∀ p : GlueIndex V c,
      T.presheaf.map (homOfLE p.2.2.1).op t = glueLocal δ c a p :=
  TopCat.Sheaf.existsUnique_gluing' T.sheaf (fun p : GlueIndex V c ↦ p.1.2) c.W
    (fun p ↦ homOfLE p.2.2.1) (iSup_glueIndex hcov c hc) (glueLocal δ c a)
    (glueLocal_compatible δ hδ c a)

/-- (Implementation) The glued value on a chart. -/
def glueVal (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U) (a : Γ(X, c.V)) :
    Γ(T, c.W) :=
  (exists_glueVal δ hδ hcov c hc a).exists.choose

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_spec (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U)
    (a : Γ(X, c.V)) (p : GlueIndex V c) :
    T.presheaf.map (homOfLE p.2.2.1).op (glueVal δ hδ hcov c hc a) = glueLocal δ c a p :=
  (exists_glueVal δ hδ hcov c hc a).exists.choose_spec p

omit [Surjective i] [IsClosedImmersion i] in
lemma glue_ext (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U)
    {t t' : Γ(T, c.W)} (h : ∀ p : GlueIndex V c,
      T.presheaf.map (homOfLE p.2.2.1).op t = T.presheaf.map (homOfLE p.2.2.1).op t') :
    t = t' :=
  TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun p : GlueIndex V c ↦ p.1.2) c.W
    (fun p ↦ homOfLE p.2.2.1) (iSup_glueIndex hcov c hc) t t' h

section

variable (hcov : U ≤ ⨆ j, V j) (c : ExtensionChart i g₀) (hc : c.W ≤ U)

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_add (a b : Γ(X, c.V)) :
    glueVal δ hδ hcov c hc (a + b) = glueVal δ hδ hcov c hc a + glueVal δ hδ hcov c hc b :=
  glue_ext hcov c hc fun p ↦ by
    rw [map_add, glueVal_spec, glueVal_spec, glueVal_spec, glueLocal, glueLocal, glueLocal,
      ((δ p.1.1).isChartDer _ _).map_add]

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_mem (a : Γ(X, c.V)) : glueVal δ hδ hcov c hc a ∈ idealOn i c.W := by
  refine eq_zero_of_locally_zero _ fun y hy ↦ ?_
  obtain ⟨p, hp⟩ := Opens.mem_iSup.mp (iSup_glueIndex hcov c hc hy)
  refine ⟨i ⁻¹ᵁ p.1.2, i.preimage_mono p.2.2.1, hp, ?_⟩
  rw [← appLE_res_apply p.2.2.1, glueVal_spec]
  exact ((δ p.1.1).isChartDer (c.shrink p.2.1 p.2.2.1) p.2.2.2).mem a

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_α (r : Γ(T, ⊤)) : glueVal δ hδ hcov c hc (c.α f r) = 0 :=
  glue_ext hcov c hc fun p ↦ by
    rw [glueVal_spec, glueLocal, map_zero]
    exact ((δ p.1.1).isChartDer (c.shrink p.2.1 p.2.2.1) p.2.2.2).map_α r

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_leibniz (a b : Γ(X, c.V)) (a' b' : Γ(T, c.W)) (ha : c.ρ a' = c.γ a)
    (hb : c.ρ b' = c.γ b) :
    glueVal δ hδ hcov c hc (a * b) =
      a' * glueVal δ hδ hcov c hc b + b' * glueVal δ hδ hcov c hc a :=
  glue_ext hcov c hc fun p ↦ by
    rw [map_add, map_mul, map_mul, glueVal_spec, glueVal_spec, glueVal_spec, glueLocal,
      glueLocal, glueLocal]
    refine ((δ p.1.1).isChartDer (c.shrink p.2.1 p.2.2.1) p.2.2.2).leibniz a b _ _ ?_ ?_
    · rw [ExtensionChart.shrink_ρ, ExtensionChart.shrink_γ, ha]
    · rw [ExtensionChart.shrink_ρ, ExtensionChart.shrink_γ, hb]

omit [Surjective i] [IsClosedImmersion i] in
lemma glueVal_map_res (c' : ExtensionChart i g₀) (hc' : c'.W ≤ U) (hV : c'.V ≤ c.V)
    (hW : c'.W ≤ c.W) (a : Γ(X, c.V)) :
    glueVal δ hδ hcov c' hc' (X.presheaf.map (homOfLE hV).op a) =
      T.presheaf.map (homOfLE hW).op (glueVal δ hδ hcov c hc a) :=
  glue_ext hcov c' hc' fun p ↦ by
    let q : GlueIndex V c := ⟨p.1, p.2.1, p.2.2.1.trans hW, p.2.2.2⟩
    have h₂ := glueVal_spec δ hδ hcov c hc a q
    rw [presheaf_map_map_apply' _ _ (homOfLE q.2.2.1), h₂, glueVal_spec]
    change (δ p.1.1).app (c'.shrink p.2.1 p.2.2.1) p.2.2.2 (X.presheaf.map (homOfLE hV).op a) =
      (δ p.1.1).app (c.shrink p.2.1 (p.2.2.1.trans hW)) p.2.2.2 a
    rw [(δ p.1.1).map_res (c.shrink p.2.1 (p.2.2.1.trans hW)) (c'.shrink p.2.1 p.2.2.1) p.2.2.2
      p.2.2.2 hV le_rfl, map_homOfLE_rfl_apply]

end

/-- (Implementation) The glued section of `𝒢`. -/
def glueDerivation (hcov : U ≤ ⨆ j, V j) : ChartDerivation f i g₀ U :=
  ⟨fun c a ↦ glueVal δ hδ hcov c.1 c.2 a,
    { isChartDer c hc :=
        { map_add := glueVal_add δ hδ hcov c hc
          mem := glueVal_mem δ hδ hcov c hc
          map_α := glueVal_α δ hδ hcov c hc
          leibniz := glueVal_leibniz δ hδ hcov c hc }
      map_res c c' hc hc' hV hW := glueVal_map_res δ hδ hcov c hc c' hc' hV hW }⟩

omit [Surjective i] [IsClosedImmersion i] in
lemma res_glueDerivation (hcov : U ≤ ⨆ j, V j) (hV : ∀ j, V j ≤ U) (j : ι) :
    ChartDerivation.res (hV j) (glueDerivation δ hδ hcov) = δ j := by
  ext c hc a
  have := glueVal_spec δ hδ hcov c (hc.trans (hV j)) a ⟨(j, c.W), c.hW, le_rfl, hc⟩
  rw [map_homOfLE_rfl_apply] at this
  exact this

end Glue

variable {ι : Type u} {U : T.Opens} in
omit [Surjective i] [IsClosedImmersion i] in
/-- III.5.2: `𝒢` is a sheaf: compatible sections over the members of an open cover glue. -/
theorem ChartDerivation.exists_res_eq (V : ι → T.Opens) (hV : ∀ j, V j ≤ U)
    (hcov : U ≤ ⨆ j, V j) (δ : ∀ j, ChartDerivation f i g₀ (V j))
    (hδ : ∀ j k, res (inf_le_left : V j ⊓ V k ≤ V j) (δ j) = res inf_le_right (δ k)) :
    ∃ δ' : ChartDerivation f i g₀ U, ∀ j, res (hV j) δ' = δ j :=
  ⟨glueDerivation δ hδ hcov, res_glueDerivation δ hδ hcov hV⟩

end Sheaf

section Action

variable [IsAffine T] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)

omit [IsAffine T] in
/-- The affine opens carrying a chart cover every open. -/
lemma le_iSup_chart (U : T.Opens) :
    U ≤ ⨆ c : {c : ExtensionChart i g₀ // c.W ≤ U}, c.1.W := by
  intro x hx
  obtain ⟨w, hw⟩ := i.surjective x
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g₀ w)) isOpen_univ
  obtain ⟨W, hW, hxW, hWU, hWV⟩ := exists_isAffineOpen_preimage_le (i := i) (g₀ := g₀)
    (V := V) hx fun w' hw' ↦ by rwa [i.isClosedEmbedding.injective (hw'.trans hw.symm)]
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, W, hV, hW, hWV⟩, hWU⟩, hxW⟩

include hsq in
/-- III.5.1: `𝒢(U)` acts transitively on the extensions over `U`: for every extension `g` and
every `δ ∈ 𝒢(U)` there is an extension `g'` with `g' - g = δ`. The extension is constructed on
the charts inside `U` and glued (III.5.1, the extensions form a sheaf). -/
theorem Extension.exists_diff_eq {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U)
    (δ : ChartDerivation f i g₀ U) : ∃ g', ChartDerivation.diff hsq g g' = δ := by
  let ι := {c : ExtensionChart i g₀ // c.W ≤ U}
  let V : ι → T.Opens := fun c ↦ c.1.W
  have hV (c : ι) : V c ≤ U := c.2
  let gc (c : ι) : Extension f (𝟙 T) i g₀ (V c) :=
    (g.restrict c.2).ofChartDer hsq ((ChartDerivation.res c.2 δ).app c.1 le_rfl)
      ((ChartDerivation.res c.2 δ).isChartDer c.1 le_rfl)
  have hgc (c : ι) : ChartDerivation.diff hsq (g.restrict c.2) (gc c) =
      ChartDerivation.res c.2 δ :=
    ChartDerivation.diff_ofChartDer hsq (c := c.1) _ _
  have hgc' (c : ι) (c'' : ExtensionChart i g₀) (h : c''.W ≤ V c) (a : Γ(X, c''.V)) :
      (gc c).chartMap c'' h a = g.chartMap c'' (h.trans (hV c)) a +
        δ.app c'' (h.trans (hV c)) a := by
    have := congrArg (fun δ' ↦ ChartDerivation.app δ' c'' h a) (hgc c)
    simp only [ChartDerivation.diff_app, ChartDerivation.res_app,
      Extension.chartMap_restrict] at this
    rw [← this]
    ring
  have hcompat (c c' : ι) :
      (gc c).restrict (inf_le_left : V c ⊓ V c' ≤ V c) = (gc c').restrict inf_le_right := by
    rw [← ChartDerivation.diff_eq_zero_iff hsq]
    ext c'' hc'' a
    simp only [ChartDerivation.diff_app, ChartDerivation.zero_app, Extension.chartMap_restrict,
      hgc']
    ring
  obtain ⟨s, hs, -⟩ := (isSheaf_extensionPresheaf f (𝟙 T) i g₀).isSheafUniqueGluing_types
    (U := V) gc hcompat
  let s' : Extension f (𝟙 T) i g₀ (⨆ c, V c) := s
  have hs' (c : ι) : s'.restrict (le_iSup V c) = gc c := hs c
  refine ⟨s'.restrict (le_iSup_chart U), ChartDerivation.eq_of_res_eq V hV (le_iSup_chart U)
    fun c ↦ ?_⟩
  rw [ChartDerivation.res_diff, Extension.restrict_restrict, ← hgc c, ← hs' c]

/-- III.5.1: the action of `𝒢(U)` on the extensions over `U`: `g + δ` is the extension whose
difference with `g` is `δ`. -/
def Extension.vadd {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U)
    (δ : ChartDerivation f i g₀ U) : Extension f (𝟙 T) i g₀ U :=
  (g.exists_diff_eq hsq δ).choose

lemma Extension.diff_vadd {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U)
    (δ : ChartDerivation f i g₀ U) : ChartDerivation.diff hsq g (g.vadd hsq δ) = δ :=
  (g.exists_diff_eq hsq δ).choose_spec

/-- III.5.1: the action is simply transitive: `g + (g' - g) = g'`. -/
lemma Extension.vadd_diff {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U) :
    g.vadd hsq (ChartDerivation.diff hsq g g') = g' := by
  rw [← ChartDerivation.diff_eq_zero_iff hsq,
    ← ChartDerivation.diff_add_diff hsq _ g, ← ChartDerivation.neg_diff, diff_vadd]
  exact neg_add_cancel _

lemma Extension.vadd_eq_iff {U : T.Opens} (g g' : Extension f (𝟙 T) i g₀ U)
    (δ : ChartDerivation f i g₀ U) : g.vadd hsq δ = g' ↔ ChartDerivation.diff hsq g g' = δ :=
  ⟨fun h ↦ h ▸ g.diff_vadd hsq δ, fun h ↦ h ▸ g.vadd_diff hsq g'⟩

lemma Extension.vadd_zero {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U) : g.vadd hsq 0 = g := by
  rw [vadd_eq_iff, ChartDerivation.diff_self]

lemma Extension.vadd_add {U : T.Opens} (g : Extension f (𝟙 T) i g₀ U)
    (δ δ' : ChartDerivation f i g₀ U) : g.vadd hsq (δ + δ') = (g.vadd hsq δ).vadd hsq δ' := by
  rw [vadd_eq_iff, ← ChartDerivation.diff_add_diff hsq _ (g.vadd hsq δ), diff_vadd, diff_vadd]

lemma Extension.restrict_vadd {U U' : T.Opens} (h : U' ≤ U) (g : Extension f (𝟙 T) i g₀ U)
    (δ : ChartDerivation f i g₀ U) :
    (g.vadd hsq δ).restrict h = (g.restrict h).vadd hsq (ChartDerivation.res h δ) := by
  rw [eq_comm, vadd_eq_iff, ← ChartDerivation.res_diff, diff_vadd]

end Action

section Torsor

variable (f i g₀)

/-- The presheaf of groups `𝒢`, written multiplicatively. -/
def derivationGroupPresheaf : (Opens T)ᵒᵖ ⥤ GrpCat.{u} where
  obj U := GrpCat.of (Multiplicative (ChartDerivation f i g₀ U.unop))
  map h := GrpCat.ofHom
    (AddMonoidHom.toMultiplicative (ChartDerivation.res h.unop.le).toAddMonoidHom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- III.5.2: `𝒢` is a sheaf. -/
theorem isSheaf_derivationGroupPresheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology T)
      (derivationGroupPresheaf f i g₀ ⋙ CategoryTheory.forget GrpCat) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  change TopCat.Presheaf.IsSheaf _
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι V sf hsf
  let δ : ∀ j, ChartDerivation f i g₀ (V j) := fun j ↦ Multiplicative.toAdd (sf j)
  have hδ : ∀ j k, ChartDerivation.res (inf_le_left : V j ⊓ V k ≤ V j) (δ j) =
      ChartDerivation.res inf_le_right (δ k) := hsf
  obtain ⟨δ', hδ'⟩ := ChartDerivation.exists_res_eq V (le_iSup V) le_rfl δ hδ
  refine ⟨Multiplicative.ofAdd δ', hδ', fun δ'' hδ'' ↦ ?_⟩
  exact ChartDerivation.eq_of_res_eq (δ := Multiplicative.toAdd δ'') V (le_iSup V) le_rfl
    fun j ↦ (hδ'' j).trans (hδ' j).symm

variable [IsAffine T] [Smooth f] [Surjective i] [IsClosedImmersion i] (hsq : IsSqZeroOn i)
  (hg₀ : g₀ ≫ f = i)

include hg₀ in
/-- III.3.1: extensions exist on every chart. -/
lemma nonempty_extension_chart (c : ExtensionChart i g₀) :
    Nonempty (Extension f (𝟙 T) i g₀ c.W) := by
  obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_affineOpens f (𝟙 T) i i.surjective g₀
    (by rw [Category.comp_id, hg₀]) (isAffineOpen_top T) c.hV c.hW (by simp) (by simp) c.le
  exact ⟨⟨g, hg₁, hg₂⟩⟩

include hg₀ in
/-- III.5.2: the sheaf of extensions of `g₀` is a torsor under `𝒢` when `f` is smooth. -/
def extensionTorsor :
    CategoryTheory.Torsor (Opens.grothendieckTopology T) (derivationGroupPresheaf f i g₀) where
  obj := extensionPresheaf f (𝟙 T) i g₀
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).mp (isSheaf_extensionPresheaf f (𝟙 T) i g₀)
  smul _ δ g := Extension.vadd hsq g (Multiplicative.toAdd δ)
  one_smul _ g := Extension.vadd_zero hsq g
  mul_smul U δ δ' g := by
    let d : ChartDerivation f i g₀ U.unop := Multiplicative.toAdd δ
    let d' : ChartDerivation f i g₀ U.unop := Multiplicative.toAdd δ'
    change Extension.vadd hsq g (d + d') = Extension.vadd hsq (Extension.vadd hsq g d') d
    rw [add_comm]
    exact Extension.vadd_add hsq g d' d
  map_smul h δ g := Extension.restrict_vadd hsq h.unop.le g (Multiplicative.toAdd δ)
  existsUnique_smul _ g g' := ⟨Multiplicative.ofAdd (ChartDerivation.diff hsq g g'),
    Extension.vadd_diff hsq g g', fun δ hδ ↦ congrArg Multiplicative.ofAdd
      ((Extension.vadd_eq_iff hsq g g' _).mp hδ).symm⟩
  locallyNonempty U := by
    refine ⟨(extensionPresheaf f (𝟙 T) i g₀).nonemptySieve' U, fun x hx ↦ ?_,
      fun _ _ hV ↦ hV⟩
    obtain ⟨⟨c, hc⟩, hxc⟩ := Opens.mem_iSup.mp (le_iSup_chart (i := i) (g₀ := g₀) U hx)
    exact ⟨c.W, homOfLE hc, nonempty_extension_chart f i g₀ hg₀ c, hxc⟩

omit [IsAffine T] [Smooth f] [Surjective i] [IsClosedImmersion i] in
lemma nonempty_extension_top_iff :
    Nonempty (Extension f (𝟙 T) i g₀ ⊤) ↔ ∃ s : T ⟶ X, s ≫ f = 𝟙 T ∧ i ≫ s = g₀ := by
  refine ⟨fun ⟨g⟩ ↦ ⟨g.toHom, by simp, by simp⟩,
    fun ⟨s, hs₁, hs₂⟩ ↦ ⟨⟨(⊤ : T.Opens).ι ≫ s, ?_, ?_⟩⟩⟩
  · rw [Category.assoc, hs₁]
  · rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hs₂]

/-- III.5.2: the class of the torsor of extensions in `H¹(T, 𝒢)` vanishes if and only if `g₀`
extends to a section of `f` over `T`. -/
theorem extensionTorsor_class_eq_trivialClass_iff :
    (extensionTorsor f i g₀ hsq hg₀).class =
        H1.trivialClass _ _ (isSheaf_derivationGroupPresheaf f i g₀) ↔
      ∃ s : T ⟶ X, s ≫ f = 𝟙 T ∧ i ≫ s = g₀ := by
  rw [Torsor.class_eq_trivialClass_iff_of_isTerminal Limits.isTerminalTop]
  exact nonempty_extension_top_iff f i g₀

/-- III.5.5, torsor form: since `T` is affine, the class of the torsor of extensions vanishes. -/
theorem extensionTorsor_class_eq_trivialClass :
    (extensionTorsor f i g₀ hsq hg₀).class =
      H1.trivialClass _ _ (isSheaf_derivationGroupPresheaf f i g₀) :=
  (extensionTorsor_class_eq_trivialClass_iff f i g₀ hsq hg₀).mpr
    (exists_section_of_isSqZeroOn f i g₀ hsq hg₀)

end Torsor

end SGA.SGA1.ExposeIII
