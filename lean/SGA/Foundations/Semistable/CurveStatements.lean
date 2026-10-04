/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import SGA.Foundations.Etale.Picard
import SGA.Foundations.Semistable.Components

/-!
# Curves over a field: statements used by the semistable reduction theorem

Interface statements (registry rows A21 and A61, work stream `semistable`) for the facts about
curves over a field that enter the proof of the semistable reduction theorem in Stacks, Sections
0CDK, 0CEG and 0CEI:

* `AlgebraicGeometry.PicTorsionReducedCurveStatement` (Stacks, Tag 0C20): for a proper reduced
  scheme `Y` of dimension `≤ 1` over an algebraically closed field and a prime `ℓ` invertible in
  `k`, `dim_{𝔽_ℓ} Pic(Y)[ℓ] ≤ h¹(Y, 𝒪_Y) + g_geom(Y)`, with equality if and only if every
  singular closed point of `Y` is a multicross singularity;
* `AlgebraicGeometry.TorsionBecomesVisibleStatement` (Stacks, Tag 0CDU): a smooth proper curve
  of genus `g ≥ 1` over a field `K` acquires a rational point and `Pic[n] ≅ (ℤ/n)^{2g}` over a
  finite separable extension, for a prime `n` invertible in `K`;
* `AlgebraicGeometry.GenusBaseChangeStatement` (Stacks, Tag 02KH applied to `H¹(𝒪)`): the genus
  `h¹(C, 𝒪_C)` does not change under extension of the base field;
* `AlgebraicGeometry.GenusZeroSmoothModelStatement` (Stacks, Section 0CDK): a smooth proper
  geometrically connected curve of genus `0` becomes `ℙ¹` over a finite separable extension
  `K'`, hence has a smooth proper model over every discrete valuation ring with fraction field
  `K'`.

`Pic Y` is `H¹(Y_Zar, 𝒪_Y^×)` (`AlgebraicGeometry.Scheme.Pic`) and `Pic(Y)[ℓ]` is the kernel of
`L ↦ L^ℓ`; the genus is `Scheme.Hom.genus = h¹(𝒪)`; `g_geom` and multicross points are defined in
`SGA.Foundations.Semistable.Components`.

## Deviations

* Stacks, Tag 0C20 is stated for `Y` connected of dimension `1`. Here `Y` need not be connected and
  may have components of dimension `0`: `Pic`, `h¹` and `g_geom` are additive over connected
  components, and a reduced point `Spec k` contributes nothing and is a regular point, so the
  statement follows from Tag 0C20 applied to the connected components of dimension `1`.
  "Dimension `≤ 1`" is spelled out as "every local ring has Krull dimension `≤ 1`".
* In Tag 0CDU the prime `n` is only asked to be invertible in `K`; the statement here is the same.
  The degree bound of Tag 0CDU for `g ≥ 2` is not included.

## References

* [Stacks Project, Tags 0C20, 0CDU, 02KH, Section 0CDK](https://stacks.math.columbia.edu/tag/0C20)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Stacks, Tag 0C20 (statement, in the generality explained in the module docstring): let `k` be
an algebraically closed field, `Y` a proper reduced scheme over `k` all of whose local rings have
dimension `≤ 1`, and `ℓ` a prime invertible in `k`. Then
`|Pic(Y)[ℓ]| ≤ ℓ^{h¹(Y, 𝒪_Y) + g_geom(Y)}`, with equality if and only if every closed point of `Y`
is a regular point or a multicross singularity. -/
def PicTorsionReducedCurveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u}) (p : Y ⟶ Spec (.of k)) [IsProper p]
    [IsReduced Y] [Fintype (irreducibleComponents Y)] [QuasiSeparatedSpace Y],
    (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      Nat.card (powMonoidHom ℓ : Y.Pic →* Y.Pic).ker ≤ ℓ ^ (p.genus + Scheme.geometricGenus p) ∧
      (Nat.card (powMonoidHom ℓ : Y.Pic →* Y.Pic).ker = ℓ ^ (p.genus + Scheme.geometricGenus p) ↔
        ∀ y : Y, IsClosed ({y} : Set Y) →
          IsRegularLocalRing (Y.presheaf.stalk y) ∨ Scheme.IsMulticrossPoint k y)

/-- Stacks, Tag 0CDU (statement): let `C` be a smooth proper geometrically connected curve of genus
`g = h¹(C, 𝒪_C) ≥ 1` over a field `K`, and `n` a prime invertible in `K`. There is a finite
separable extension `K'/K` such that `C_{K'}` has a `K'`-rational point and
`Pic(C_{K'})[n] ≅ (ℤ/n)^{2g}`. -/
def TorsionBecomesVisibleStatement : Prop :=
  ∀ (K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f], 1 ≤ f.genus →
    ∀ (n : ℕ) [Fact n.Prime], (n : K) ≠ 0 →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
        (_ : Algebra.IsSeparable K K'),
        (∃ s : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
          s ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty ((powMonoidHom n : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap K K')))).Pic →* _).ker ≃* Multiplicative (Fin (2 * f.genus) → ZMod n))

/-- The genus is invariant under extension of the base field (statement; Stacks, Tag 02KH, flat
base change, applied to `H¹(C, 𝒪_C)`): for a proper scheme `C` over a field `K` and a field
extension `K'/K`, `h¹(C_{K'}, 𝒪) = h¹(C, 𝒪)`. -/
def GenusBaseChangeStatement : Prop :=
  ∀ (K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    (K' : Type u) [Field K'] [Algebra K K'],
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K')))).genus = f.genus

/-- Stacks, Section 0CDK (semistable reduction in genus `0`, statement): let `C` be a smooth proper
geometrically connected curve of genus `0` over a field `K`. There is a finite separable extension
`K'/K` (of degree `≤ 2`, not recorded here) with `C_{K'} ≅ ℙ¹_{K'}`; hence for every discrete
valuation ring `R'` with fraction field `K'`, `C_{K'}` has a proper smooth model `ℙ¹_{R'}`. -/
def GenusZeroSmoothModelStatement : Prop :=
  ∀ (K : Type u) [Field K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f], f.genus = 0 →
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R' K']
        [IsFractionRing R' K'],
        ∃ (𝒳 : Scheme.{u}) (g : 𝒳 ⟶ Spec (.of R')), IsProper g ∧
          SmoothOfRelativeDimension 1 g ∧
          ∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) ≅
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
            e.hom ≫ pullback.snd _ _ = pullback.snd _ _

end AlgebraicGeometry
