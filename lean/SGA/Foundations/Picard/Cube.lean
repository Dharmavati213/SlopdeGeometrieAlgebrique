/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.Picard.Basic

/-!
# The theorem of the cube (statement)

The theorem of the cube (Mumford, *Abelian varieties*, §6; Milne, *Abelian varieties*, Theorem
5.1): let `X`, `Y` be complete varieties and `Z` a variety over an algebraically closed field
`k`, with `k`-points `x₀`, `y₀`, `z₀`. A line bundle on `X × Y × Z` whose restrictions to
`{x₀} × Y × Z`, `X × {y₀} × Z` and `X × Y × {z₀}` are trivial is trivial.

`AlgebraicGeometry.TheoremOfTheCubeStatement` records this for `X`, `Y` proper and geometrically
integral and `Z` smooth and connected over `k`, the products being taken in `Over (Spec k)`. The
smoothness of `Z` is stronger than Mumford's hypothesis (any variety); it is what the proof we
plan uses (the local rings of `Z` are factorial) and it holds in the application to abelian
varieties (`SGA.SGA1.ExposeXI.AbelianVarietyCube`).

## References

* [D. Mumford, *Abelian varieties*, §6, §10][mumford1970]
* [J. S. Milne, *Abelian varieties*, Theorem 5.1][milne1986]
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The theorem of the cube (Mumford, *Abelian varieties*, §6), for `Z` smooth: let `k` be an
algebraically closed field, `X`, `Y` proper and geometrically integral `k`-schemes, `Z` a
connected smooth `k`-scheme, and `x₀`, `y₀`, `z₀` rational points. A class `c` in
`Pic ((X ×ₖ Y) ×ₖ Z)` whose inverse images along the three inclusions
`Y ×ₖ Z → {x₀} × Y × Z`, `X ×ₖ Z → X × {y₀} × Z` and `X ×ₖ Y → X × Y × {z₀}` are trivial is
trivial. Mumford allows any variety `Z`; here `Z` is smooth. -/
def TheoremOfTheCubeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X Y Z : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    [Smooth Z.hom] [ConnectedSpace Z.left]
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Z) (c : ((X ⊗ Y) ⊗ Z).left.Pic),
    Scheme.Pic.pullback (lift (lift (toUnit (Y ⊗ Z) ≫ x₀) (fst Y Z)) (snd Y Z)).left c = 1 →
    Scheme.Pic.pullback (lift (lift (fst X Z) (toUnit (X ⊗ Z) ≫ y₀)) (snd X Z)).left c = 1 →
    Scheme.Pic.pullback (lift (𝟙 (X ⊗ Y)) (toUnit (X ⊗ Y) ≫ z₀)).left c = 1 →
    c = 1

/-- The openness step in the proof of the theorem of the cube (the infinitesimal and formal part
of Mumford, *Abelian varieties*, §6; Grothendieck's proof of the rigidity of rigidified line
bundles on `X ×ₖ Y`): let `k` be algebraically closed, `X`, `Y` proper and geometrically integral
over `k` with `k`-points `x₀`, `y₀`, and `W` locally of finite type over `k` with a `k`-point
`w₀`. If a class `c ∈ Pic ((X ×ₖ Y) ×ₖ W)` is trivial on `{x₀} × Y × W`, on `X × {y₀} × W` and on
the fibre `X × Y × {w₀}`, then it is trivial over `X × Y × U` for some open neighbourhood `U` of
`w₀`.

The planned proof: on the thickenings `X × Y × Spec 𝒪_{W,w₀}/𝔪ⁿ⁺¹` the obstruction to lifting a
trivialization lies in `H¹(X × Y, 𝒪) ⊗ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` and restricts to zero on both axes, hence vanishes
by the Künneth formula `H¹(X × Y, 𝒪) = H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)`; the theorem on formal functions
then gives a section near `w₀`. -/
def CubeOpennessStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X Y W : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType W.hom]
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (w₀ : 𝟙_ (Over (Spec (.of k))) ⟶ W) (c : ((X ⊗ Y) ⊗ W).left.Pic),
    Scheme.Pic.pullback (lift (lift (toUnit (Y ⊗ W) ≫ x₀) (fst Y W)) (snd Y W)).left c = 1 →
    Scheme.Pic.pullback (lift (lift (fst X W) (toUnit (X ⊗ W) ≫ y₀)) (snd X W)).left c = 1 →
    Scheme.Pic.pullback (lift (𝟙 (X ⊗ Y)) (toUnit (X ⊗ Y) ≫ w₀)).left c = 1 →
    ∃ U : W.left.Opens, Set.range w₀.left ⊆ U ∧
      Scheme.Pic.pullback ((snd (X ⊗ Y) W).left ⁻¹ᵁ U).ι c = 1

end AlgebraicGeometry
