/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import SGA.SGA1.ExposeXII.RiemannExistence
import SGA.SGA1.ExposeXII.RiemannCurves
import SGA.Foundations.Topology.FiniteCoveringBaseChange

/-!
# SGA 1, Exposé XII, 5.1 in higher dimension: statements

XII.5.1 (`RiemannExistenceStatement`) for affine `X = Spec A` of any dimension is being reduced,
along the following route, to the curve case (`CurveRiemannExistenceStatement`), the extension of
coverings across divisors of smooth varieties of dimension `≥ 2`, and the local irreducibility
of normal varieties. The route is this project's, not SGA's: SGA uses Hironaka's resolution,
Serre's extension of coherent analytic sheaves across codimension `2` on a normal space, and GAGA
(XII.5.1 2) a)–c)).

1. *Hypersurface complements* `𝔸^d ∖ V(f)`, by induction on `d`
   (`HypersurfaceComplementRiemannExistenceStatement`), through the family of punctured lines
   `{(w, x) | f(w, x) ≠ 0}` over a dense open of `𝔸^{d-1}`, whose fibres are `ℂ` minus finitely
   many points.
2. *Extension across a divisor* (`DivisorExtensionStatement`): on a smooth `X`, a covering of
   `X(ℂ)` which is algebraic over a dense basic open subset is algebraic. In dimension `≤ 1` it
   follows from the curve case (`CurveDivisorExtensionStatement`); dimension `≥ 2` is
   `HigherDivisorExtensionStatement`.
3. *Smooth `X`* (`SmoothRiemannExistenceStatement`), from 1 and 2 by Noether normalization.
4. *Normal `X`*, from 3 and the local irreducibility of normal complex varieties
   (`TopologicallyUnibranchStatement`), applied to the normalization of `X` in a covering of its
   smooth locus.
5. *All `X`*, by descent along the normalization (`RiemannExistenceFiniteDescentStatement`).

SGA 4 XI's route through Artin's elementary fibrations is not used: it needs the injectivity of
`π₁` of a fibre into `π₁` of the total space of an elementary fibration, which is the third part
of XIII.4.4 (`ExposeXIII.NormalCrossingsShortExactSequenceStatement`), out of scope here.

All statements are for `A : Type` (`ℂ : Type`); `riemannExistence_iff_zero` moves the general
statement to any universe.
-/

noncomputable section

open CategoryTheory Topology

namespace SGA.SGA1.ExposeXII

namespace RiemannHigher

/-- The continuous map `B(ℂ) → A(ℂ)` induced by a `ℂ`-algebra map `φ : A → B`, as a morphism of
`TopCat`. -/
abbrev pointsHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) : TopCat.of (Points ℂ B) ⟶ TopCat.of (Points ℂ A) :=
  TopCat.ofHom ⟨Points.map φ, Points.continuous_map φ⟩

/-- The restriction of a finite covering `E` of `X(ℂ)`, `X = Spec A`, to the basic open
`D(g)(ℂ) = {φ | φ g ≠ 0}`, as a finite covering of `A_g(ℂ)` (the pullback along the open
embedding `A_g(ℂ) → A(ℂ)`, `Points.isOpenEmbedding_map_of_isLocalizationAway`). -/
abbrev restrictAway {A : Type} [CommRing A] [Algebra ℂ A] (g : A)
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) :
    TopCat.FiniteCovering (TopCat.of (Points ℂ (Localization.Away g))) :=
  (TopCat.FiniteCovering.baseChange
    (pointsHom (IsScalarTower.toAlgHom ℂ A (Localization.Away g)))).obj E

end RiemannHigher

open RiemannHigher

/-- XII.5.1 for smooth affine `X` (statement only): for `A` of finite type and smooth over `ℂ`,
the functor `Ψ : S ↦ S(ℂ)` from finite étale `A`-algebras to finite coverings of `X(ℂ)`,
`X = Spec A`, is an equivalence. This is `RiemannExistenceStatement.{0}` restricted to smooth
`A` (`smoothRiemannExistence_of_riemannExistence`). -/
def SmoothRiemannExistenceStatement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A],
    (pointsFunctor ℂ A).IsEquivalence

/-- XII.5.1 for complements of hypersurfaces in `𝔸^d` (statement only): for every nonzero
`f ∈ ℂ[x₁, …, x_d]`, the functor `Ψ` is an equivalence for `X = 𝔸^d ∖ V(f) = Spec ℂ[x][1/f]`.
For `d = 1` this is XII.5.1 for `ℂ` minus a finite set (`PuncturedPlane.riemannExistence_coordRing`,
up to the identification of `ℂ[x][1/f]` with `ℂ[t][1/∏_{a ∈ S} (t - a)]`, `S` the roots of `f`). -/
def HypersurfaceComplementRiemannExistenceStatement (d : ℕ) : Prop :=
  ∀ f : MvPolynomial (Fin d) ℂ, f ≠ 0 → (pointsFunctor ℂ (Localization.Away f)).IsEquivalence

/-- Extension of the Riemann existence theorem across a divisor (statement only): let `A` be of
finite type and smooth over `ℂ`, `g ∈ A` a nonzerodivisor (so that `D(g)` is dense in
`X = Spec A`), and `E` a finite covering of `X(ℂ)`. If the restriction of `E` to
`D(g)(ℂ) = {φ | φ g ≠ 0}` is isomorphic to `S(ℂ)` for a finite étale `A_g`-algebra `S`, then `E`
is isomorphic to `T(ℂ)` for a finite étale `A`-algebra `T`. Classically: the normalization of `X`
in `S` is étale over the generic points of `V(g)`, because `E` is a covering over them, and then
everywhere by Zariski–Nagata purity (X.3.3). In dimension `1`, `V(g)` is a finite set of points
and this is the extension of XII.5.1 across finitely many points of a smooth curve. -/
def DivisorExtensionStatement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A]
    (g : A), g ∈ nonZeroDivisors A → ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)),
      (pointsFunctor ℂ (Localization.Away g)).essImage (restrictAway g E) →
        (pointsFunctor ℂ A).essImage E

/-- `DivisorExtensionStatement` in Krull dimension at most `1` (statement only): there `V(g)` is a
finite set of points of a smooth curve. It follows from XII.5.1 for curves
(`curveDivisorExtension_of_curveRiemannExistence`). -/
def CurveDivisorExtensionStatement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A],
    ringKrullDim A ≤ 1 → ∀ (g : A), g ∈ nonZeroDivisors A →
      ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)),
        (pointsFunctor ℂ (Localization.Away g)).essImage (restrictAway g E) →
          (pointsFunctor ℂ A).essImage E

/-- `DivisorExtensionStatement` in Krull dimension at least `2` (statement only). This is the part
of step 2 of the route that is not a consequence of the curve case. -/
def HigherDivisorExtensionStatement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A],
    2 ≤ ringKrullDim A → ∀ (g : A), g ∈ nonZeroDivisors A →
      ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)),
        (pointsFunctor ℂ (Localization.Away g)).essImage (restrictAway g E) →
          (pointsFunctor ℂ A).essImage E

/-- The extension across divisors in dimension `≤ 1` follows from XII.5.1 for curves, which makes
every covering algebraic. -/
theorem curveDivisorExtension_of_curveRiemannExistence (H : CurveRiemannExistenceStatement) :
    CurveDivisorExtensionStatement := fun A _ _ _ _ hA _ _ E _ ↦
  have := H A hA
  Functor.EssSurj.mem_essImage _ E

/-- `DivisorExtensionStatement` is the conjunction of its parts in dimension `≤ 1` and `≥ 2`. -/
theorem divisorExtension_iff :
    DivisorExtensionStatement ↔ CurveDivisorExtensionStatement ∧ HigherDivisorExtensionStatement :=
  ⟨fun h ↦ ⟨fun A _ _ _ _ _ ↦ h A, fun A _ _ _ _ _ ↦ h A⟩, fun ⟨h₁, h₂⟩ A _ _ _ _ ↦ by
    rcases le_or_gt (ringKrullDim A) 1 with hA | hA
    · exact h₁ A hA
    · refine h₂ A ?_
      rcases hd : ringKrullDim A with _ | n
      · rw [hd] at hA
        exact absurd hA (not_lt.mpr bot_le)
      · rw [hd] at hA
        change ((1 : ℕ∞) : WithBot ℕ∞) < (n : WithBot ℕ∞) at hA
        change ((2 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)
        exact WithBot.coe_le_coe.mpr (Order.add_one_le_of_lt (WithBot.coe_lt_coe.mp hA))⟩

/-- The extension across divisors from XII.5.1 for curves and the extension in dimension `≥ 2`. -/
theorem divisorExtension_of_curveRiemannExistence (H : CurveRiemannExistenceStatement)
    (H₂ : HigherDivisorExtensionStatement) : DivisorExtensionStatement :=
  divisorExtension_iff.mpr ⟨curveDivisorExtension_of_curveRiemannExistence H, H₂⟩

/-- Extension of coverings across divisors on normal varieties (statement only): let `A` be a
normal domain of finite type over `ℂ`, `g ∈ A` nonzero, and `E` a finite covering of `X(ℂ)`,
`X = Spec A`. If the restriction of `E` to `D(g)(ℂ)` is `S(ℂ)` for a finite étale `A_g`-algebra
`S`, then `E` is `T(ℂ)` for a finite étale `A`-algebra `T`. Expected route: `T` is the
normalization of `A` in `S`, finite over `A`; `T(ℂ) ≅ E` over `X(ℂ)` by the topological extension
lemma, using the local irreducibility of the normal varieties `X` and `Spec T`
(`TopologicallyUnibranchStatement`); and `T` is étale over `A` because every fibre of
`T(ℂ) → X(ℂ)` has `[Frac T : Frac A]` points (discriminant of the trace form, `A` being
integrally closed). Together with `GenericRiemannExistenceStatement` it gives XII.5.1 for normal
domains, hence for all `X` by normalization
(`isEquivalence_pointsFunctor_of_forall_normalization`). -/
def NormalDivisorExtensionStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (g : A), g ≠ 0 → ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)),
      (pointsFunctor ℂ (Localization.Away g)).essImage (restrictAway g E) →
        (pointsFunctor ℂ A).essImage E

/-- Normal complex varieties are locally irreducible (statement only): let `A` be a normal domain
of finite type over `ℂ`, `g ∈ A` nonzero and `x ∈ X(ℂ)`, `X = Spec A`. Then `x` has arbitrarily
small open neighbourhoods `V` in `X(ℂ)` such that `V ∖ V(g)(ℂ) = {φ ∈ V | φ g ≠ 0}` is connected.
This is the topological form of Zariski's main theorem (the analytic germ of a normal variety is
irreducible, and the complement of a proper analytic subset of an irreducible germ is locally
connected); SGA uses instead, in XII.5.1 2) b), Serre's theorem that coherent analytic sheaves of
algebras on a normal space extend across codimension `2`. It is the input of the reduction of
XII.5.1 for normal `X` to smooth `X`. -/
def TopologicallyUnibranchStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (g : A), g ≠ 0 → ∀ (x : Points ℂ A), ∀ U ∈ 𝓝 x,
      ∃ V : Set (Points ℂ A), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsPreconnected (V ∩ {φ | φ g ≠ 0})

/-- Descent of the Riemann existence theorem along a finite surjective morphism, per covering
(statement only): let `φ : A → B` be an injective finite map of `ℂ`-algebras of finite type (so
that `Spec B → Spec A` is finite and surjective, e.g. the normalization of a reduced `A`), and
`E` a finite covering of `A(ℂ)`. If the pullback of `E` to `B(ℂ)` is isomorphic to `S(ℂ)` for a
finite étale `B`-algebra `S`, then `E` is isomorphic to `T(ℂ)` for a finite étale `A`-algebra `T`.
This is the reduction to normal `X` in XII.5.1 2) a): `Spec B → Spec A` is an effective descent
morphism for étale coverings (IX.4.7), the descent datum comes from the full faithfulness of `Ψ`
(step 1)), and `B(ℂ) → A(ℂ)` is a descent morphism for coverings, being proper and surjective. -/
def RiemannExistenceFiniteDescentStatement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ A]
    [Algebra.FiniteType ℂ B] (φ : A →ₐ[ℂ] B), φ.toRingHom.Finite → Function.Injective φ →
    ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)),
      (pointsFunctor ℂ B).essImage ((TopCat.FiniteCovering.baseChange (pointsHom φ)).obj E) →
        (pointsFunctor ℂ A).essImage E

/-- XII.5.1 for all affine `X` implies it for smooth affine `X`. -/
theorem smoothRiemannExistence_of_riemannExistence (H : RiemannExistenceStatement.{0}) :
    SmoothRiemannExistenceStatement := fun A _ _ _ _ ↦ H A

/-- XII.5.1 for all affine `X` implies it for hypersurface complements. -/
theorem hypersurfaceComplementRiemannExistence_of_riemannExistence
    (H : RiemannExistenceStatement.{0}) (d : ℕ) :
    HypersurfaceComplementRiemannExistenceStatement d := fun f _ ↦ H (Localization.Away f)

/-- XII.5.1 for smooth affine `X` implies it for hypersurface complements (which are smooth). -/
theorem hypersurfaceComplementRiemannExistence_of_smooth (H : SmoothRiemannExistenceStatement)
    (d : ℕ) : HypersurfaceComplementRiemannExistenceStatement d := fun f _ ↦
  have : Algebra.Smooth ℂ (MvPolynomial (Fin d) ℂ) := {}
  have : Algebra.Smooth (MvPolynomial (Fin d) ℂ) (Localization.Away f) :=
    .of_isLocalization_Away f
  have : Algebra.Smooth ℂ (Localization.Away f) :=
    .comp ℂ (MvPolynomial (Fin d) ℂ) (Localization.Away f)
  have : Algebra.FiniteType ℂ (Localization.Away f) := inferInstance
  H (Localization.Away f)

end SGA.SGA1.ExposeXII
