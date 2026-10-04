/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properties of morphisms over a limit descend to a finite stage: statements

The interface statement of EGA IV 8.10.5 (registry row A40 of
`notes/topics/out-of-scope-plan.md`): let `c.pt = lim E i` be the limit of a cofiltered diagram of
quasi-compact and quasi-separated schemes with affine transition maps, `X_j` a scheme of finite
presentation over some `E j`, and `X = X_j ×_{E j} c.pt`. If `X ⟶ c.pt` has a property `P`, then
`X_j ×_{E j} E k ⟶ E k` has `P` for some `k ⟶ j`. EGA IV 8.10.5 proves this for (among others)
isomorphisms, open and closed immersions, separated, surjective, affine, finite, proper
(8.10.5 (xii), through Chow's lemma) and quasi-finite morphisms; EGA IV 17.7.8 for étale and smooth
morphisms; EGA IV 11.2.6 for flat morphisms.

* `AlgebraicGeometry.Scheme.LimitDescendsStatement P`: the statement for the property `P`.
* `AlgebraicGeometry.Scheme.ProperLimitStatement`: the case `P = IsProper` (EGA IV 8.10.5 (xii),
  Stacks 081F). Stacks' proof uses Chow's lemma (Stacks 0200, 0203); the repository's Chow lemma
  is `exists_isHProjective_isIso_morphismRestrict`.

Proved instances (EGA IV 8.10.5): surjective (`Scheme.limitDescends_surjective`,
`SGA.Foundations.Limits.PropertiesLimitSurjective`), isomorphisms and closed immersions
(`Scheme.limitDescends_isIso`, `Scheme.limitDescends_isClosedImmersion`,
`SGA.Foundations.Limits.PropertiesLimitClosedImmersion`), separated
(`Scheme.limitDescends_isSeparated`, `SGA.Foundations.Limits.PropertiesLimitSeparated`), proper
(`Scheme.properLimitStatement`, `SGA.Foundations.Limits.PropertiesLimitProper`, by Chow's lemma
and noetherian approximation), étale and smooth (EGA IV 17.7.8: `Scheme.limitDescends_etale`,
`Scheme.limitDescends_smooth`, `SGA.Foundations.Limits.PropertiesLimitEtale`), affine, finite,
monomorphisms and open immersions (`Scheme.limitDescends_isAffineHom`,
`Scheme.limitDescends_isFinite`, `Scheme.limitDescends_mono`,
`Scheme.limitDescends_isOpenImmersion`, `SGA.Foundations.Limits.PropertiesLimitFinite`). Not done:
immersions, quasi-finite and flat morphisms (EGA IV 11.2.6).

## References

* [EGA IV₃, 8.10.5][EGA4]; [EGA IV₄, 17.7.8][EGA4]; [EGA IV₃, 11.2.6][EGA4]
* [Stacks Project, Limits of schemes, Section 32.8 (descending properties of morphisms)][stacks]
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- EGA IV 8.10.5 for a property `P` of morphisms, statement: let `c.pt = lim E i` be the limit of
a cofiltered diagram `E : I ⥤ Scheme` (`I : Type u`) of quasi-compact and quasi-separated schemes
with affine transition maps, `qⱼ : X_j ⟶ E j` of finite presentation (locally of finite
presentation, quasi-compact, quasi-separated), and `X ⟶ c.pt` its base change along
`c.π.app j`. If `X ⟶ c.pt` has `P`, then the base change `X_j ×_{E j} E k ⟶ E k` has `P` for
some `g : k ⟶ j`. -/
def Scheme.LimitDescendsStatement (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃I : Type u⦄ [Category.{u} I] [IsCofiltered I] (E : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
    [∀ i, QuasiSeparatedSpace (E.obj i)] (c : Cone E) (_ : IsLimit c) ⦃j : I⦄
    ⦃X Xj : Scheme.{u}⦄ (qj : Xj ⟶ E.obj j) [LocallyOfFinitePresentation qj] [QuasiCompact qj]
    [QuasiSeparated qj] (e : X ⟶ Xj) (q : X ⟶ c.pt), IsPullback e q qj (c.π.app j) → P q →
      ∃ (k : I) (g : k ⟶ j), P (pullback.snd qj (E.map g))

/-- EGA IV 8.10.5 (xii) (Stacks 081F), statement: properness of a morphism of finite presentation
over the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes with affine
transition maps descends to a finite stage. -/
def Scheme.ProperLimitStatement : Prop :=
  Scheme.LimitDescendsStatement.{u} @IsProper

end AlgebraicGeometry
