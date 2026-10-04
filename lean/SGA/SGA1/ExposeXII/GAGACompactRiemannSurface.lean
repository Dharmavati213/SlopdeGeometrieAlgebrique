/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurves
import SGA.Foundations.Analytic.RiemannSurfaceMeromorphic

/-!
# SGA 1, Exposé XII, 5.1 for curves: the analytic heart

The analytic input of the Riemann existence theorem for curves,
`CompactRiemannSurfaceMeromorphicStatement`, holds: on a compact Riemann surface, every point is
the only pole of some meromorphic function (Forster, *Lectures on Riemann surfaces*, 14.13). The
proof, in `SGA.Foundations.Analytic` (`AnalyticGeometry.exists_meromorphic_single_pole`), follows
Forster 14.9 with sup norms instead of `L²` norms:

* Dolbeault's lemma for compactly supported data (`AnalyticGeometry.dbar_cauchyTransform`);
* L. Schwartz's theorem on compact perturbations of surjections
  (`ContinuousLinearMap.cofg_range_sub_of_surjective`);
* Montel's theorem for bounded holomorphic functions on a Riemann surface
  (`AnalyticGeometry.boundedHolomorphic.isCompactOperator_restrict`);
* finiteness of the bounded holomorphic Čech cohomology of a disc cover
  (`AnalyticGeometry.DiscChart.cofg_range_cechδ`), and the Mittag-Leffler argument.

SGA itself deduces XII.5.1 from GAGA (XII.4.4) and the Grauert–Remmert extension theorem; this
is the curve case, by the classical route.
-/

namespace SGA.SGA1.ExposeXII

/-- The analytic heart of XII.5.1 for curves (Forster 14.13): on a compact Riemann surface, for
every point `y` there is a meromorphic function whose only pole is at `y`. The connectedness
hypothesis of the statement is not used. -/
theorem compactRiemannSurfaceMeromorphic : CompactRiemannSurfaceMeromorphicStatement := by
  intro M _ _ _ _ _ _ y
  exact AnalyticGeometry.exists_meromorphic_single_pole y

end SGA.SGA1.ExposeXII
