/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.AnalyticGluingMap
import SGA.Foundations.Analytic.Modules
import SGA.Foundations.Analytic.Morphisms
import SGA.Foundations.Cohomology.Statements

/-!
# SGA 1, Exposé XII, §4: GAGA (statements)

SGA 1 XII §4 compares a proper `ℂ`-scheme `X` with its analytic space `X^an`:

* XII.4.1: for `f : X → Y` and an `𝒪_X`-module `F`, the canonical morphisms
  `θ_p : (Rᵖf_* F)^an → Rᵖf^an_* F^an` are constructed;
* XII.4.2: they are isomorphisms for `f` proper and `F` coherent;
* XII.4.3: for `X` proper and `F` coherent, `Hᵖ(X, F) → Hᵖ(X^an, F^an)` is an isomorphism;
* XII.4.4: for `X` proper, `F ↦ F^an` is an equivalence between coherent `𝒪_X`-modules and coherent
  analytic sheaves on `X^an`;
* XII.4.5: `X ↦ X^an` is fully faithful on proper `ℂ`-schemes;
* XII.4.6: for `X` proper, `X' ↦ X'^an` is an equivalence between finite (resp. finite étale)
  `X`-schemes and finite (resp. finite étale) analytic spaces over `X^an`.

Stated here, on `X^an = AnalyticGluing.analyticSpace X` (defined for separated `X`; proper schemes
are separated):

* `CohomologyComparisonStatement` (XII.4.3), with the canonical map
  `LocallyRingedSpace.Modules.pullbackCohomologyMap (toScheme X) F p` and
  `F^an = (Modules.pullback φ).obj F` (`analytification`);
* `CoherentEquivalenceStatement` (XII.4.4);
* `AnalyticFullyFaithfulStatement` (XII.4.5);
* `FiniteAnalyticEquivalenceStatement` (XII.4.6, both the finite and the finite étale case).

Not stated: XII.4.1 and XII.4.2 (the relative case). They need the higher direct images
`Rᵖf_*` as `𝒪_Y`-modules on both sides, their analytification, and the Leray edge maps of 4.1;
none of these exists here (the repository works with `Hᵖ` over opens or over an affine base).
XII.4.3 is the case `Y = Spec ℂ` of XII.4.2.

**Dependencies of the proofs** (SGA's route, through Serre's GAGA for `ℙⁿ`):
* XII.4.3 for projective `X`: `Hᵖ(ℙⁿ, 𝒪(d))` analytically, from Theorem B for `𝒪` on the standard
  affine opens `ℂᵃ × (ℂ*)ᵇ` of `ℙⁿ` (`AnalyticGeometry.PolydiscProductVanishingStatement`) and
  Leray; for proper `X`, Chow's lemma and the relative projective case over the singular base
  `X^an`, whose stalks need Theorem B on polydisc products `Δ × ℂᵃ × (ℂ*)ᵇ` (the polydisc factor
  of the same statement); dévissage (EGA III 3.1.2);
* XII.4.4, full faithfulness: XII.4.3 applied to `ℋom(F, G)`; essential surjectivity: Serre's
  theorem 3 (GAGA no. 12), i.e. Theorems A and B for coherent analytic sheaves on `ℙⁿ`, which
  need the Cartan–Serre finiteness theorem and Oka's coherence theorem
  (`AnalyticGeometry.OkaCoherenceStatement`), then Chow and noetherian induction with the `Ext`
  comparison (EGA 0_III 12.3.5);
* XII.4.5 from XII.4.4: graphs are closed analytic subspaces of `X^an × Y^an`, which correspond to
  coherent ideals; this needs fibre products of analytic spaces and `(X ×_ℂ Y)^an ≅ X^an × Y^an`;
* XII.4.6 from XII.4.4: finite analytic spaces over `X^an` correspond to coherent
  `𝒪_{X^an}`-algebras (Cartan, exp. 19 §5, th. 2); the étale case also uses XII.3.1 (iii) with
  "étale" as local isomorphism.

`ℂ`-linearity: a morphism of analytic spaces is `ℂ`-linear if it commutes with the structure
morphisms to `Spec ℂ` (`IsCLinear`; for local models this is `LocalModelData.IsKLinear`, by
`LocalModelData.isKLinear_iff_comp_toSpecField`). This is needed: a point has the non-trivial
ring automorphisms of `ℂ` as endomorphisms.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AnalyticGeometry

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]

variable (X) in
/-- The `ℂ`-structure of `X^an`: the morphism `X^an → X → Spec ℂ`. -/
def structureMorphism : analyticSpace X ⟶ specField ℂ :=
  toScheme X ≫ (X ↘ Spec (.of ℂ)).toLRSHom

/-- A morphism `g : X^an → Y^an` is `ℂ`-linear: it is compatible with the structure morphisms
`X^an → X → Spec ℂ` and `Y^an → Y → Spec ℂ`. On local models this is
`LocalModelData.IsKLinear` (`LocalModelData.isKLinear_iff_comp_toSpecField`). -/
def IsCLinear (g : analyticSpace X ⟶ analyticSpace Y) : Prop :=
  g ≫ toScheme Y ≫ (Y ↘ Spec (.of ℂ)).toLRSHom = toScheme X ≫ (X ↘ Spec (.of ℂ)).toLRSHom

lemma isCLinear_iff (g : analyticSpace X ⟶ analyticSpace Y) :
    IsCLinear g ↔ g ≫ structureMorphism Y = structureMorphism X :=
  Iff.rfl

/-- The morphism `f^an` induced by a `ℂ`-morphism `f` is `ℂ`-linear. -/
lemma isCLinear_analyticMap (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] :
    IsCLinear (analyticMap f) := by
  rw [IsCLinear, analyticMap_toScheme_assoc, ← Scheme.Hom.comp_toLRSHom,
    CategoryTheory.comp_over]

/-- The map `f ↦ f^an` from `ℂ`-morphisms `X → Y` to `ℂ`-linear morphisms `X^an → Y^an`. -/
def analyticMapCLinear (f : {f : X ⟶ Y // f ≫ (Y ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)}) :
    {g : analyticSpace X ⟶ analyticSpace Y // IsCLinear g} :=
  have : f.1.IsOver (Spec (.of ℂ)) := ⟨f.2⟩
  ⟨analyticMap f.1, isCLinear_analyticMap f.1⟩

/-- `f^an` only depends on `f`. -/
lemma analyticMap_congr {f g : X ⟶ Y} [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))]
    (h : f = g) : analyticMap f = analyticMap g := by
  subst h
  rfl

variable (X) in
/-- XII.1.3: the analytic sheaf `F^an = φ^* F` on `X^an` attached to an `𝒪_X`-module `F`. -/
def analytification : X.Modules ⥤ (analyticSpace X).Modules :=
  LocallyRingedSpace.Modules.pullback (toScheme X)

end AnalyticGluing

open AnalyticGluing LocallyRingedSpace.Modules

/-- XII.4.3 (statement only): for a proper `ℂ`-scheme `X` and a coherent `𝒪_X`-module `F`, the
canonical map `Hᵖ(X, F) → Hᵖ(X^an, F^an)` is bijective for every `p`. The map is
`pullbackCohomologyMap φ F p` (apply the exact functor `φ⁻¹` to `Ext`, then `φ⁻¹F → φ^*F`); `Hᵖ`
is the cohomology of the underlying abelian sheaf (`CategoryTheory.Sheaf.H`, isomorphic to the
`Scheme.Modules.H` of `SGA.Foundations.Cohomology` by `CategoryTheory.Sheaf.H'.addEquivH`). Stated
in universe `0`. -/
def CohomologyComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))] (F : X.Modules)
    [F.IsCoherent] (p : ℕ),
    Function.Bijective (pullbackCohomologyMap (X := analyticSpace X)
      (Y := X.toLocallyRingedSpace) (toScheme X) F p)

/-- XII.4.4 (statement only): for a proper `ℂ`-scheme `X`, `F ↦ F^an` is an equivalence between
coherent `𝒪_X`-modules and coherent `𝒪_{X^an}`-modules: it sends coherent modules to coherent ones,
it is fully faithful on coherent modules, and every coherent `𝒪_{X^an}`-module is isomorphic to
some `F^an`. A coherent analytic sheaf is taken to be an `𝒪_{X^an}`-module of finite presentation
(`SheafOfModules.IsFinitePresentation`); this agrees with SGA's "coherent" (finite type with
relation sheaves of finite type) because `𝒪_{X^an}` is coherent, by Oka's theorem
(`AnalyticGeometry.OkaCoherenceStatement`), which is not proved. Stated in universe `0`. -/
def CoherentEquivalenceStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))],
    (∀ F : X.Modules, F.IsCoherent →
      SheafOfModules.IsFinitePresentation.{0} ((analytification X).obj F)) ∧
    (∀ F G : X.Modules, F.IsCoherent → G.IsCoherent →
      Function.Bijective ((analytification X).map : (F ⟶ G) → _)) ∧
    ∀ 𝓕 : (analyticSpace X).Modules, SheafOfModules.IsFinitePresentation.{0} 𝓕 →
      ∃ F : X.Modules, F.IsCoherent ∧ Nonempty ((analytification X).obj F ≅ 𝓕)

/-- XII.4.5 (statement only): for proper `ℂ`-schemes `X` and `Y`, the map `f ↦ f^an` from
`ℂ`-morphisms `X → Y` to `ℂ`-linear morphisms of analytic spaces `X^an → Y^an` is bijective
(`X ↦ X^an` is fully faithful on proper `ℂ`-schemes). Stated in universe `0`. -/
def AnalyticFullyFaithfulStatement : Prop :=
  ∀ (X Y : Scheme.{0}) [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] [IsProper (Y ↘ Spec (.of ℂ))],
    Function.Bijective (analyticMapCLinear (X := X) (Y := Y))

namespace AnalyticGluing

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))]
  {X' X'' : Scheme.{0}} [X'.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X' ↘ Spec (.of ℂ))]
  [IsSeparated (X' ↘ Spec (.of ℂ))] [X''.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (X'' ↘ Spec (.of ℂ))] [IsSeparated (X'' ↘ Spec (.of ℂ))]
  (f' : X' ⟶ X) [f'.IsOver (Spec (.of ℂ))] (f'' : X'' ⟶ X) [f''.IsOver (Spec (.of ℂ))]

/-- XII.4.6: the map `g ↦ g^an` from `X`-morphisms `X' → X''` to `X^an`-morphisms
`X'^an → X''^an`. -/
def analyticMapOver (g : {g : X' ⟶ X'' // g ≫ f'' = f'}) :
    {h : analyticSpace X' ⟶ analyticSpace X'' // h ≫ analyticMap f'' = analyticMap f'} :=
  have : g.1.IsOver (Spec (.of ℂ)) :=
    ⟨by rw [← CategoryTheory.comp_over f'' (Spec (.of ℂ)), ← Category.assoc, g.2,
      CategoryTheory.comp_over]⟩
  ⟨analyticMap g.1, by rw [← analyticMap_comp, analyticMap_congr g.2]⟩

end AnalyticGluing

/-- XII.4.6 (statement only): for a proper `ℂ`-scheme `X`, `X' ↦ X'^an` is an equivalence between
finite (resp. finite étale) `X`-schemes and finite (resp. finite étale) analytic spaces over `X^an`.
Stated, for each of the two cases, as: `f'^an : X'^an → X^an` is finite (resp. finite and a local
isomorphism) for `f' : X' → X` finite (resp. finite étale); `g ↦ g^an` is bijective on
`X`-morphisms; and every `ℂ`-analytic space `Y` with a finite (resp. finite, locally
isomorphic) morphism `p : Y → X^an` is isomorphic over `X^an` to some `X'^an`.

Conventions: a finite morphism of analytic spaces is a proper map with finite fibres
(`AnalyticGeometry.IsFiniteMap`; Cartan, exp. 19 §5), an étale one is a local isomorphism
(`AnalyticGeometry.IsLocalIsomorphism`), and `Y` is a `ℂ`-analytic space for the structure
`Y → X^an → Spec ℂ` (`AnalyticGeometry.IsAnalyticSpaceOver`). An `X`-scheme `X'` is given with a
`ℂ`-structure for which `X' → X` is a `ℂ`-morphism (any finite `X`-scheme is one, via
`X' → X → Spec ℂ`), separated and locally of finite type over `ℂ` (automatic for finite `X'`);
these are hypotheses only because `X'^an` is defined here for such schemes. Stated in
universe `0`. -/
def FiniteAnalyticEquivalenceStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))] (etale : Bool),
    let P : ∀ {X' : Scheme.{0}}, (X' ⟶ X) → Prop := fun f ↦
      IsFinite f ∧ (etale → Etale f)
    let Q : ∀ {Y : LocallyRingedSpace.{0}}, (Y ⟶ analyticSpace X) → Prop := fun p ↦
      IsFiniteMap p ∧ (etale → IsLocalIsomorphism p)
    (∀ (X' : Scheme.{0}) [X'.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X' ↘ Spec (.of ℂ))]
      [IsSeparated (X' ↘ Spec (.of ℂ))] (f' : X' ⟶ X) [f'.IsOver (Spec (.of ℂ))],
      P f' → Q (analyticMap f')) ∧
    (∀ (X' X'' : Scheme.{0}) [X'.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X' ↘ Spec (.of ℂ))]
      [IsSeparated (X' ↘ Spec (.of ℂ))] [X''.Over (Spec (.of ℂ))]
      [LocallyOfFiniteType (X'' ↘ Spec (.of ℂ))] [IsSeparated (X'' ↘ Spec (.of ℂ))]
      (f' : X' ⟶ X) [f'.IsOver (Spec (.of ℂ))] (f'' : X'' ⟶ X) [f''.IsOver (Spec (.of ℂ))],
      P f' → P f'' → Function.Bijective (analyticMapOver f' f'')) ∧
    ∀ (Y : LocallyRingedSpace.{0}) (p : Y ⟶ analyticSpace X),
      IsAnalyticSpaceOver ℂ Y (p ≫ structureMorphism X) → Q p →
        ∃ (X' : Scheme.{0}) (_ : X'.Over (Spec (.of ℂ)))
          (_ : LocallyOfFiniteType (X' ↘ Spec (.of ℂ))) (_ : IsSeparated (X' ↘ Spec (.of ℂ)))
          (f' : X' ⟶ X) (_ : f'.IsOver (Spec (.of ℂ))) (e : Y ≅ analyticSpace X'),
          P f' ∧ e.hom ≫ analyticMap f' = p

end SGA.SGA1.ExposeXII
