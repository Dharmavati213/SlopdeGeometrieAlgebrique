/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurvesCompactification
import SGA.Foundations.Analytic.RiemannSurfaceCompactification

/-!
# SGA 1, Exposé XII, 5.1 for `ℂ ∖ S`: the compactification, and the unconditional results

`PuncturedPlaneCompactificationStatement` (xii51,
`SGA.SGA1.ExposeXII.RiemannCurvesCompactification`) asks for a finite covering `p : E → ℂ ∖ S`
(`S` finite) to be an open subset of a compact Riemann surface on which `p` is the chart at the
points of `E`. It holds
(`puncturedPlaneCompactification`): fill in one point for each end of `E`, with the Kummer chart
there (`AnalyticGeometry.PuncturedPlaneCovering.Fill`,
`SGA.Foundations.Analytic.RiemannSurfaceCompactification`; the connectedness of `E` is not used).

With xii51's derivations from it, this makes the following unconditional (this project's route,
not SGA's, which goes through GAGA and the Grauert–Remmert extension theorem):

* `fiberSeparatingFunction : FiberSeparatingFunctionStatement`, the analytic input of the
  algebraic half (functions holomorphic on `E`, of moderate growth, separating any fibre);
* `PuncturedPlane.riemannExistence_coordRing`: **XII.5.1 for `ℂ ∖ S`**, i.e. for
  `Spec ℂ[t][1/∏_{a ∈ S} (t - a)]`;
* `PuncturedPlane.riemannExistence_finiteEtale`: XII.5.1 for every finite étale
  `ℂ[t][1/∏(t - a)]`-algebra;
* `PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`: the étale fundamental
  group of `ℙ¹_ℂ` minus `|S| + 1` points is the profinite completion of the free group on `S`
  (XII.5.2, and XIII.2.12 in genus `0` over `ℂ`).
-/

open AnalyticGeometry

namespace SGA.SGA1.ExposeXII

/-- **Filling in the punctures of a finite covering of `ℂ ∖ S`**: `E` is an open subset of a
compact Riemann surface `Ē` (`PuncturedPlaneCovering.Fill`) in which `p` is the chart at the
points of `E`. The connectedness of `E` is not used. -/
theorem puncturedPlaneCompactification : PuncturedPlaneCompactificationStatement := by
  intro S E _ _ p hp hfin
  let C : PuncturedPlaneCovering S := ⟨E, p, hp, hfin⟩
  refine ⟨C.Fill, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    PuncturedPlaneCovering.Fill.ofE (C := C), C.isOpenEmbedding_ofE,
    fun e => ⟨fun x hx => ?_, fun e' _ => C.eChart_apply_ofE e e'⟩⟩
  obtain ⟨y, -, rfl⟩ := (C.mem_eChart_source_iff e x).mp hx
  exact ⟨y, rfl⟩

/-- The analytic input of XII.5.1 for curves, in covering form, holds: every fibre of a finite
covering of `ℂ ∖ S` is separated by a holomorphic function of moderate growth. -/
theorem fiberSeparatingFunction : FiberSeparatingFunctionStatement :=
  fiberSeparatingFunctionStatement_of_compactification puncturedPlaneCompactification

namespace PuncturedPlane

/-- **XII.5.1 for `ℂ ∖ S`** (`S ⊂ ℂ` finite; this project's route, not SGA's): for
`A = ℂ[t][1/∏_{a ∈ S} (t - a)]`, the functor `Ψ` from finite étale `A`-algebras to finite coverings
of `(Spec A)(ℂ) = ℂ ∖ S` is an equivalence of categories. -/
theorem riemannExistence_coordRing (S : Finset ℂ) :
    (pointsFunctor ℂ (coordRing S)).IsEquivalence :=
  isEquivalence_pointsFunctor_coordRing_of_compactification puncturedPlaneCompactification S

/-- XII.5.1 for the finite étale coverings of `ℂ ∖ S` (e.g. smooth affine curves minus finitely
many points, when they are finite étale over some `ℂ ∖ S`; this project's route). -/
theorem riemannExistence_finiteEtale (S : Finset ℂ)
    (B : CommAlgCat.FiniteEtale.{0} (coordRing S)) :
    letI := algebraOfFiniteEtale ℂ (coordRing S) B
    (pointsFunctor ℂ B).IsEquivalence :=
  isEquivalence_pointsFunctor_finiteEtale_of_compactification puncturedPlaneCompactification S B

/-- XII.5.2 for `ℂ ∖ S` (and XIII.2.12 in genus `0` over `ℂ`; this project's route): the étale
fundamental group of `ℙ¹_ℂ` minus `|S| + 1` points is the profinite completion of the free group
on `S`. -/
theorem etaleFundamentalGroup_mulEquiv_completion_freeGroup (S : Finset ℂ)
    (x : SchemePoints ℂ (AlgebraicGeometry.Spec (.of (coordRing S)))) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup S))) :=
  nonempty_etaleFundamentalGroup_continuousMulEquiv_completion_freeGroup_of_compactification
    puncturedPlaneCompactification S x

end PuncturedPlane

end SGA.SGA1.ExposeXII
