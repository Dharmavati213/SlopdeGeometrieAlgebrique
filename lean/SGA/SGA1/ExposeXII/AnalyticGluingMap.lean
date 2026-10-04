/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.AnalyticGluing

/-!
# SGA 1, Exposé XII, 1.2: the morphism `f^an` for separated schemes

For a morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type, the morphism
`f^an : X^an → Y^an` (`analyticMap f`) with `f^an ≫ φ_Y = φ_X ≫ f` (`analyticMap_toScheme`).

`X^an` is glued from the charts of all affine opens of `X`, which need not map into an affine open
of `Y`. We therefore first glue `X^an` from the charts of the affine opens `U` with `f(U)` inside
some affine open `V` of `Y` (`smallFamily f`); this gives `X^an` again (`isIso_gluedToAnalytic`),
and on such a chart `f^an` is `U^an → V^an ⊆ Y^an` (`chartHom`, `ι_analyticMap`).

Functoriality: `analyticMap_id`, `analyticMap_comp`. Not proved: the uniqueness of `f^an` (SGA
deduces it from the universal property of `Y^an`, which is proved only for affine `Y` on local
models).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AnalyticGeometry Topology

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

open AffineAnalytification LocallyRingedSpaceComparison SchemePoints

attribute [local instance] sectionsAlgebra finitePresentation_sections

section Small

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- The affine opens of `X` mapped by `f` into an affine open of `Y`. -/
def smallFamily : Set X.affineOpens := {U | ∃ V : Y.affineOpens, (U : X.Opens) ≤ f ⁻¹ᵁ V}

lemma smallFamily_basis (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)) :
    ∃ W ∈ smallFamily f, W ≤ U ∧ x ∈ (W : X.Opens) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((U : X.Opens) ⊓ f ⁻¹ᵁ V : X.Opens) from ⟨hx, hxV⟩)
    ((U : X.Opens) ⊓ f ⁻¹ᵁ V).2
  exact ⟨⟨W, hW⟩, ⟨⟨V, hV⟩, fun y hy ↦ (hWU hy).2⟩, fun y hy ↦ (hWU hy).1, hxW⟩

/-- A chosen affine open of `Y` containing `f(U)`, for `U` in the small family. -/
def target (U : smallFamily f) : Y.affineOpens := U.2.choose

lemma le_target (U : smallFamily f) : (U.1 : X.Opens) ≤ f ⁻¹ᵁ (target f U) := U.2.choose_spec

end Small

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y)
  [f.IsOver (Spec (.of ℂ))]

/-- For affine opens `U ⊆ f⁻¹(V)`, the morphism `U^an → V^an` induced by `f` (XII.1.2). -/
def chartHom {U : X.affineOpens} {V : Y.affineOpens} (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    chart X U ⟶ chart Y V :=
  affineAnalytificationMap (appLEAlgHom (K := ℂ) f e)

@[reassoc]
lemma chartHom_chartToScheme {U : X.affineOpens} {V : Y.affineOpens}
    (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    chartHom f e ≫ chartToScheme V = chartToScheme U ≫ f.toLRSHom := by
  rw [chartHom, chartToScheme, chartToScheme, ← Category.assoc,
    affineAnalytificationMap_comp_affineToSpec, Category.assoc, Category.assoc]
  congr 1
  have := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen V) (isAffineOpen U) e
  exact congrArg Scheme.Hom.toLRSHom this

@[reassoc]
lemma chartMap_chartHom {U U' : X.affineOpens} {V : Y.affineOpens} (h : U' ≤ U)
    (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    chartMap h ≫ chartHom f e = chartHom f ((show (U' : X.Opens) ≤ U from h).trans e) := by
  rw [chartMap, chartHom, chartHom, ← affineAnalytificationMap_comp]
  congr 1
  ext a
  change X.presheaf.map (homOfLE _).op (f.appLE V U e a) = f.appLE V U' _ a
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

@[reassoc]
lemma chartHom_chartMap {U : X.affineOpens} {V V' : Y.affineOpens} (h : V ≤ V')
    (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    chartHom f e ≫ chartMap h =
      chartHom f (e.trans (f.preimage_mono (show (V : Y.Opens) ≤ V' from h))) := by
  rw [chartMap, chartHom, chartHom, ← affineAnalytificationMap_comp]
  congr 1
  ext a
  change f.appLE V U e (Y.presheaf.map (homOfLE _).op a) = f.appLE V' U _ a
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

variable [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]

/-- `f^an` on the chart of a member `U` of the small family: `U^an → V^an → Y^an`. -/
def smallChartMap (U : smallFamily f) : chart X U.1 ⟶ analyticSpace Y :=
  chartHom f (le_target f U) ≫ ι (target f U)

omit [IsSeparated (X ↘ Spec (CommRingCat.of ℂ))] in
lemma chartHom_ι_eq {U : X.affineOpens} {V V' : Y.affineOpens} (e : (U : X.Opens) ≤ f ⁻¹ᵁ V)
    (e' : (U : X.Opens) ≤ f ⁻¹ᵁ V') : chartHom f e ≫ ι V = chartHom f e' ≫ ι V' := by
  have e₃ : (U : X.Opens) ≤ f ⁻¹ᵁ (inter V V') := by
    intro x hx
    exact ⟨e hx, e' hx⟩
  calc chartHom f e ≫ ι V = chartHom f e₃ ≫ chartMap (inter_le_left V V') ≫ ι V := by
        rw [chartHom_chartMap_assoc]
    _ = chartHom f e₃ ≫ chartMap (inter_le_right V V') ≫ ι V' := by
        rw [chartMap_ι, chartMap_ι]
    _ = chartHom f e' ≫ ι V' := by rw [chartHom_chartMap_assoc]

lemma smallChartMap_glue_condition (i j : smallFamily f) :
    chartMap (inter_le_left i.1 j.1) ≫ smallChartMap f i =
      (chartMap (inter_le_inter_comm i.1 j.1) ≫ chartMap (inter_le_left j.1 i.1)) ≫
        smallChartMap f j := by
  rw [smallChartMap, smallChartMap, chartMap_chartHom_assoc, Category.assoc, chartMap_comp_assoc,
    chartMap_chartHom_assoc]
  exact chartHom_ι_eq f _ _

/-- `f^an` on the analytic space glued from the small family. -/
def smallAnalyticMap : gluedSpace (smallFamily f) ⟶ analyticSpace Y :=
  Multicoequalizer.desc _ _ (fun U ↦ smallChartMap f U) fun ⟨i, j⟩ ↦
    smallChartMap_glue_condition f i j

@[reassoc (attr := simp)]
lemma gluedι_smallAnalyticMap (U : smallFamily f) :
    gluedι (smallFamily f) U ≫ smallAnalyticMap f = smallChartMap f U :=
  Multicoequalizer.π_desc (glueData X (smallFamily f)).toGlueData.diagram _ _ _ U

instance : IsIso (gluedToAnalytic (smallFamily f)) :=
  isIso_gluedToAnalytic _ (smallFamily_basis f)

/-- XII.1.2: the morphism `f^an : X^an → Y^an` induced by a `ℂ`-morphism `f : X → Y` of separated
`ℂ`-schemes locally of finite type, with `f^an ≫ φ_Y = φ_X ≫ f` (`analyticMap_toScheme`).

In SGA, `f^an` is the unique morphism making this square commute (from the universal property of
`Y^an`); that uniqueness is not proved here. Functoriality is: `analyticMap_id`,
`analyticMap_comp`. On the chart of an affine open `U ⊆ f⁻¹(V)`, `f^an` is the analytification of
`Γ(Y, V) → Γ(X, U)` (`ι_analyticMap`). -/
def analyticMap : analyticSpace X ⟶ analyticSpace Y :=
  inv (gluedToAnalytic (smallFamily f)) ≫ smallAnalyticMap f

lemma gluedι_smallAnalyticMap_toScheme (U : smallFamily f) :
    gluedι (smallFamily f) U ≫ smallAnalyticMap f ≫ toScheme Y =
      gluedι (smallFamily f) U ≫ gluedToScheme (smallFamily f) ≫ f.toLRSHom := by
  rw [gluedι_smallAnalyticMap_assoc, gluedι_gluedToScheme_assoc, smallChartMap, Category.assoc,
    ι_toScheme, chartHom_chartToScheme]

/-- XII.1.2: the square formed by `f^an`, `f` and the canonical morphisms `φ` commutes. -/
@[reassoc]
theorem analyticMap_toScheme :
    analyticMap f ≫ toScheme Y = toScheme X ≫ f.toLRSHom := by
  rw [analyticMap, Category.assoc, IsIso.inv_comp_eq, gluedToAnalytic_toScheme_assoc]
  exact Multicoequalizer.hom_ext _ _ _ fun U ↦ gluedι_smallAnalyticMap_toScheme f U

/-- On the chart of an affine open `U ⊆ f⁻¹(V)`, `f^an` is `U^an → V^an ⊆ Y^an`. -/
@[reassoc]
theorem ι_analyticMap {U : X.affineOpens} {V : Y.affineOpens} (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    ι U ≫ analyticMap f = chartHom f e ≫ ι V := by
  let U' : smallFamily f := ⟨U, V, e⟩
  rw [← gluedι_gluedToAnalytic (smallFamily f) U', analyticMap, Category.assoc,
    IsIso.hom_inv_id_assoc, gluedι_smallAnalyticMap, smallChartMap]
  exact chartHom_ι_eq f _ _

omit [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (Y ↘ Spec (.of ℂ))] in
private lemma gluedι_gluedToAnalytic_comp_eq (S : Set X.affineOpens) [IsIso (gluedToAnalytic S)]
    (U : S) {Z : LocallyRingedSpace.{0}} {g₁ g₂ : analyticSpace X ⟶ Z}
    (h : ι U.1 ≫ g₁ = ι U.1 ≫ g₂) :
    gluedι S U ≫ gluedToAnalytic S ≫ g₁ = gluedι S U ≫ gluedToAnalytic S ≫ g₂ := by
  rw [gluedι_gluedToAnalytic_assoc, gluedι_gluedToAnalytic_assoc]
  exact h

omit [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (Y ↘ Spec (.of ℂ))] in
/-- Two morphisms out of `X^an` that agree on the charts of a family `S` of affine opens which
contains a neighbourhood basis inside every affine open are equal. -/
theorem hom_ext_of_basis (S : Set X.affineOpens)
    (hS : ∀ (U : X.affineOpens) (x : X), x ∈ (U : X.Opens) → ∃ W ∈ S, W ≤ U ∧ x ∈ (W : X.Opens))
    {Z : LocallyRingedSpace.{0}} {g₁ g₂ : analyticSpace X ⟶ Z}
    (h : ∀ U ∈ S, ι U ≫ g₁ = ι U ≫ g₂) : g₁ = g₂ := by
  have := isIso_gluedToAnalytic S hS
  rw [← cancel_epi (gluedToAnalytic S)]
  exact Multicoequalizer.hom_ext _ _ _ fun U ↦ gluedι_gluedToAnalytic_comp_eq S U (h U.1 U.2)

omit [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (Y ↘ Spec (.of ℂ))] in
/-- XII.1.2, functoriality: `(𝟙 X)^an = 𝟙`. -/
theorem analyticMap_id : analyticMap (𝟙 X) = 𝟙 (analyticSpace X) := by
  refine hom_ext_of_basis Set.univ (fun U x hx ↦ ⟨U, trivial, le_rfl, hx⟩) fun U _ ↦ ?_
  have e : (U : X.Opens) ≤ (𝟙 X) ⁻¹ᵁ U := fun x hx ↦ hx
  rw [ι_analyticMap (𝟙 X) e, Category.comp_id]
  have : chartHom (𝟙 X) e = 𝟙 _ := by
    rw [chartHom, ← affineAnalytificationMap_id]
    congr 1
    ext a
    change Scheme.Hom.appLE (𝟙 X) U U e a = a
    have h : X.presheaf.map (𝟙 (Opposite.op (U : X.Opens))) a = a := by
      rw [X.presheaf.map_id]
      rfl
    exact h
  rw [this, Category.id_comp]

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]
  [IsSeparated (Z ↘ Spec (.of ℂ))] (g : Y ⟶ Z) [g.IsOver (Spec (.of ℂ))]

omit [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  [IsSeparated (Z ↘ Spec (.of ℂ))] in
@[reassoc]
lemma chartHom_comp {U : X.affineOpens} {V : Y.affineOpens} {W : Z.affineOpens}
    (e : (U : X.Opens) ≤ f ⁻¹ᵁ V) (e' : (V : Y.Opens) ≤ g ⁻¹ᵁ W) :
    chartHom f e ≫ chartHom g e' =
      chartHom (f ≫ g) (e.trans (f.preimage_mono e')) := by
  rw [chartHom, chartHom, chartHom, ← affineAnalytificationMap_comp]
  congr 1
  ext a
  change f.appLE V U e (g.appLE W V e' a) = (f ≫ g).appLE W U _ a
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- XII.1.2, functoriality: `(f ≫ g)^an = f^an ≫ g^an`. -/
theorem analyticMap_comp : analyticMap (f ≫ g) = analyticMap f ≫ analyticMap g := by
  let S : Set X.affineOpens := {U | ∃ (V : Y.affineOpens) (W : Z.affineOpens),
    (U : X.Opens) ≤ f ⁻¹ᵁ V ∧ (V : Y.Opens) ≤ g ⁻¹ᵁ W}
  have hS (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)) :
      ∃ W ∈ S, W ≤ U ∧ x ∈ (W : X.Opens) := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ (g ⁻¹ᵁ W : Y.Opens) from hxW) (g ⁻¹ᵁ W).2
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((U : X.Opens) ⊓ f ⁻¹ᵁ V : X.Opens) from ⟨hx, hxV⟩)
      ((U : X.Opens) ⊓ f ⁻¹ᵁ V).2
    exact ⟨⟨U', hU'⟩, ⟨⟨V, hV⟩, ⟨W, hW⟩, fun y hy ↦ (hU'U hy).2, fun y hy ↦ hVW hy⟩,
      fun y hy ↦ (hU'U hy).1, hxU'⟩
  refine hom_ext_of_basis S hS fun U ⟨V, W, e, e'⟩ ↦ ?_
  rw [ι_analyticMap_assoc f e, ι_analyticMap g e', chartHom_comp_assoc f g e e',
    ι_analyticMap (f ≫ g)]

end AnalyticGluing

end SGA.SGA1.ExposeXII
