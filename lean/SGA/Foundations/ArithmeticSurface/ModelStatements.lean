/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.ArithmeticSurface.Model
import SGA.Foundations.Etale.Picard
import SGA.Foundations.Semistable.Components
import SGA.Foundations.Semistable.NumericalType

/-!
# Regular models of curves: statements used by the semistable reduction theorem

Interface statements (registry row A21, work stream `semistable`) for the geometry of a regular
proper model `X` of a smooth proper geometrically connected curve `C` over the fraction field `K`
of a discrete valuation ring `R` with algebraically closed residue field `k` (Stacks, Situation
0C5Y), in the form used by the proof of the semistable reduction theorem in Stacks, Sections
0CEG and 0CEI. Notation: `X_k` is the closed fibre (`AlgebraicGeometry.closedFibre`), `Cᵢ` its
irreducible components, `mᵢ` their multiplicities, `(Cᵢ · Cⱼ)` the intersection matrix,
`gᵢ = h¹(Cᵢ, 𝒪)`, `(X_k)_red` the reduced closed fibre, all as defined in
`SGA.Foundations.Semistable.Components`.

* `AlgebraicGeometry.MinimalModelStatement` (Stacks, Tags 0C2W and 0CA6): `C` has a regular proper
  model without component `Cᵢ` with `gᵢ = 0` and `(Cᵢ · Cᵢ) = -1` (a minimal model);
* `AlgebraicGeometry.NumericalTypeOfModelStatement` (Stacks, Tags 0CA4 and 0CA3): the data
  `(mᵢ, (Cᵢ · Cⱼ), gᵢ)` form a numerical type (weights `1`) of genus `g(C)`;
* `AlgebraicGeometry.RationalPointModelStatement` (Stacks, Tag 0CE8 (1), (2)): if `C(K) ≠ ∅`, then
  `X_k` has a closed point at which it is regular, lying on a single component `Cᵢ`, with `mᵢ = 1`;
* `AlgebraicGeometry.PicTorsionModelStatement` (Stacks, Tags 0CAD and 0CAE): for a prime `ℓ`
  invertible in `k` and prime to `gcd(mᵢ)`,
  `|Pic(C)[ℓ]| ≤ |Coker(Cᵢ · Cⱼ)[ℓ]| · |Pic((X_k)_red)[ℓ]|`;
* `AlgebraicGeometry.GenusReducedFibreUpperStatement` (Stacks, Tags 0CE9 and 0CE8 (3)): for a
  minimal model and `C(K) ≠ ∅`, `h¹((X_k)_red) ≤ g(C)`, with strict inequality if some `mᵢ ≠ 1`;
* `AlgebraicGeometry.GenusReducedFibreLowerStatement` (Stacks, Tag 0CEA): if `X_k` has a regular
  closed point, `g_top + g_geom((X_k)_red) ≤ h¹((X_k)_red)`;
* `AlgebraicGeometry.ClosedFibreDimensionStatement` (Stacks, Tag 0D4J): the local rings of `X_k`
  have dimension `≤ 1`.

The last step of the argument ("the closed fibre is a semistable curve once all `mᵢ = 1` and
`(X_k)_red` has only multicross singularities") is stated in SGA 1 terms, in
`SGA.SGA1.ExposeXIII.SemistableReductionAssembly`, where these statements are assembled.

## Deviations

* The residue field `k` is algebraically closed (the case of
  `SGA.SGA1.ExposeXIII.SemistableReductionStatement`), so that all weights `[H⁰(Cᵢ, 𝒪) : k]` are
  `1` (`AlgebraicGeometry.NumericalType`). Stacks allows any residue field.
* Minimal models are defined in Stacks by the absence of exceptional curves of the first kind;
  `MinimalModelStatement` uses the equivalent numerical condition of Tag 0CA6 ("the numerical type
  is minimal"), as exceptional curves are not defined here.
* The intersection matrix is `AlgebraicGeometry.Scheme.intersectionMatrix`, which agrees with
  Stacks' `(Cᵢ · Cⱼ)` by Tags 0C64 and 0C66 (see the deviation in
  `SGA.Foundations.Semistable.Components`); that the diagonal division there is exact is part of
  `NumericalTypeOfModelStatement`.
* Tags 0CAD/0CAE give an exact sequence `0 → Pic(X)[ℓ] → Pic(C)[ℓ] → Pic(T)[ℓ]` and an injection
  `Pic(X)[ℓ] → Pic((X_k)_red)[ℓ]`; `PicTorsionModelStatement` only records the resulting bound on
  cardinalities.
* Tag 0CE9 states that `H¹(X_k, 𝒪) → H¹((X_k)_red, 𝒪)` is surjective with a nontrivial kernel when
  `X_k` is not reduced, under `gcd(mᵢ) = 1` and `H⁰((X_k)_red, 𝒪) = k`; with Tag 0CE8 (3)
  (`h¹(X_k) = g(C)` and these hypotheses when `C(K) ≠ ∅`) and the fact that `X_k` has no embedded
  points (so that `X_k` is reduced when all `mᵢ = 1`), this gives
  `GenusReducedFibreUpperStatement`.
* Tag 0CEA assumes a `k`-rational smooth point of `X_k`; for `k` algebraically closed this is a
  closed point at which `X_k` is regular.
* Tag 0D4J (the dimension of the fibres of a proper flat morphism is locally constant) gives
  `dim X_k = dim C = 1`; `ClosedFibreDimensionStatement` records the consequence for local rings.

## References

* [Stacks Project, Chapter 55 (Semistable Reduction), Sections 0C5Y, 0CA2, 0CA9, 0CEG, 0CEI](https://stacks.math.columbia.edu/tag/0C5Y)
* [M. Artin, G. Winters, *Degenerate fibres and stable reduction of curves*, Topology 10 (1971)]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Stacks, Tags 0C2W and 0CA6 (statement): let `R` be a discrete valuation ring with fraction field
`K` and algebraically closed residue field, and `C` a smooth proper geometrically connected curve
over `K`. Then `C` has a minimal model: a regular proper model `X` such that no irreducible
component `Cᵢ` of `X_k` has `h¹(Cᵢ, 𝒪) = 0` and `(Cᵢ · Cᵢ) = -1` (no exceptional curve of the first
kind, by Tag 0CA6). -/
def MinimalModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f],
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (.of R)), IsRegularProperModel g f ∧
      ∀ [Fintype (irreducibleComponents (closedFibre g))]
        (Z : irreducibleComponents (closedFibre g)),
        ¬ (Scheme.componentGenus (closedFibreHom g) Z = 0 ∧
          Scheme.intersectionMatrix (closedFibreHom g) Z Z = -1)

/-- Stacks, Tags 0CA4 and 0CA3 (statement): for a regular proper model `X` of a smooth proper
geometrically connected curve `C` over the fraction field of a discrete valuation ring with
algebraically closed residue field, the multiplicities `mᵢ`, the intersection matrix
`((Cᵢ · Cⱼ))` and the genera `gᵢ = h¹(Cᵢ, 𝒪)` of the components of `X_k` form a numerical type
(with weights `1`) whose genus is the genus `h¹(C, 𝒪_C)` of `C` (the genus formula). -/
def NumericalTypeOfModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    ∀ [Fintype (irreducibleComponents (closedFibre g))],
      ∃ T : NumericalType (irreducibleComponents (closedFibre g)),
        (∀ Z, T.m Z = Scheme.componentMultiplicity Z) ∧
        T.a = Scheme.intersectionMatrix (closedFibreHom g) ∧
        (∀ Z, T.g Z = Scheme.componentGenus (closedFibreHom g) Z) ∧
        T.genus = f.genus

/-- Stacks, Tag 0CE8 (1), (2) (statement): for a regular proper model `X` of a smooth proper
geometrically connected curve `C` with a `K`-rational point, over a discrete valuation ring with
algebraically closed residue field, the closed fibre `X_k` has a closed point `x` at which it is
regular (a smooth `k`-rational point); `x` lies on a unique irreducible component `Cᵢ`, and
`mᵢ = 1`. -/
def RationalPointModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    (∃ s : Spec (.of K) ⟶ C, s ≫ f = 𝟙 _) →
    ∃ (x : closedFibre g) (Z : irreducibleComponents (closedFibre g)),
      IsClosed ({x} : Set (closedFibre g)) ∧ x ∈ Z.1 ∧
      (∀ W : irreducibleComponents (closedFibre g), x ∈ W.1 → W = Z) ∧
      IsRegularLocalRing ((closedFibre g).presheaf.stalk x) ∧
      Scheme.componentMultiplicity Z = 1

/-- Stacks, Tags 0CAD and 0CAE (statement, as a bound on cardinalities): for a regular proper model
`X` of a smooth proper geometrically connected curve `C` over the fraction field of a discrete
valuation ring with algebraically closed residue field `k`, and a prime `ℓ` invertible in `k` and
not dividing all the multiplicities `mᵢ`,
`|Pic(C)[ℓ]| ≤ |Pic(T)[ℓ]| · |Pic((X_k)_red)[ℓ]|`, where `Pic(T) = Coker((Cᵢ · Cⱼ))` is the Picard
group of the numerical type of `X` (weights `1`). -/
def PicTorsionModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    ∀ [Fintype (irreducibleComponents (closedFibre g))] (ℓ : ℕ) [Fact ℓ.Prime],
      (ℓ : IsLocalRing.ResidueField R) ≠ 0 →
      (∃ Z : irreducibleComponents (closedFibre g), ¬ ℓ ∣ Scheme.componentMultiplicity Z) →
      Nat.card (powMonoidHom ℓ : C.Pic →* C.Pic).ker ≤
        Nat.card (Submodule.torsionBy ℤ ((irreducibleComponents (closedFibre g) → ℤ) ⧸
            LinearMap.range (Scheme.intersectionMatrix (closedFibreHom g)).mulVecLin) (ℓ : ℤ)) *
          Nat.card (powMonoidHom ℓ : (closedFibre g).reduction.Pic →* _).ker

/-- Stacks, Tags 0CE9 and 0CE8 (3) (statement): for a minimal model `X` (no component with
`gᵢ = 0` and `(Cᵢ · Cᵢ) = -1`) of a smooth proper geometrically connected curve `C` with a
`K`-rational point, over a discrete valuation ring with algebraically closed residue field,
`h¹((X_k)_red, 𝒪) ≤ g(C)`, and the inequality is strict if some multiplicity `mᵢ` is not `1`. -/
def GenusReducedFibreUpperStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    (∃ s : Spec (.of K) ⟶ C, s ≫ f = 𝟙 _) →
    ∀ [Fintype (irreducibleComponents (closedFibre g))],
      (∀ Z : irreducibleComponents (closedFibre g),
        ¬ (Scheme.componentGenus (closedFibreHom g) Z = 0 ∧
          Scheme.intersectionMatrix (closedFibreHom g) Z Z = -1)) →
      ((closedFibre g).reductionι ≫ closedFibreHom g).genus ≤ f.genus ∧
      ((∃ Z : irreducibleComponents (closedFibre g), Scheme.componentMultiplicity Z ≠ 1) →
        ((closedFibre g).reductionι ≫ closedFibreHom g).genus < f.genus)

/-- Stacks, Tag 0CEA (statement): for a regular proper model `X` of a smooth proper geometrically
connected curve over the fraction field of a discrete valuation ring with algebraically closed
residue field `k`, if `X_k` has a closed point at which it is regular, then
`g_top + g_geom((X_k)_red/k) ≤ h¹((X_k)_red, 𝒪)`, where `g_top = 1 - n + e` is the topological
genus of the numerical type of `X` (`Matrix.topGenus` of the intersection matrix). -/
def GenusReducedFibreLowerStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    (∃ x : closedFibre g, IsClosed ({x} : Set (closedFibre g)) ∧
      IsRegularLocalRing ((closedFibre g).presheaf.stalk x)) →
    ∀ [Fintype (irreducibleComponents (closedFibre g))]
      [Fintype (irreducibleComponents (closedFibre g).reduction)]
      [QuasiSeparatedSpace (closedFibre g).reduction],
      (Scheme.intersectionMatrix (closedFibreHom g)).topGenus +
          Scheme.geometricGenus ((closedFibre g).reductionι ≫ closedFibreHom g) ≤
        ((closedFibre g).reductionι ≫ closedFibreHom g).genus

/-- Stacks, Tag 0D4J (consequence, statement): for a proper flat model `X` of a smooth proper
geometrically connected curve `C` over the fraction field of a discrete valuation ring, the closed
fibre has dimension `dim C = 1`; in particular every local ring of `X_k` has Krull dimension
`≤ 1`. -/
def ClosedFibreDimensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)) [IsProper g] [Flat g],
    (∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅ C,
      e.hom ≫ f = pullback.snd _ _) →
    ∀ x : closedFibre g, ringKrullDim ((closedFibre g).presheaf.stalk x) ≤ 1

end AlgebraicGeometry
