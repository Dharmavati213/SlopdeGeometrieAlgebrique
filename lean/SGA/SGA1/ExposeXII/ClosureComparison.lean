/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.Nullstellensatz
import SGA.SGA1.ExposeXII.Nullstellensatz
import SGA.SGA1.ExposeXII.SchemeLimits
import SGA.SGA1.ExposeXII.Proper

/-!
# SGA 1, Exposé XII, 2.2–2.3 without hypotheses

`Nullstellensatz.lean` derives XII.2.2 (`SchemePoints.ClosureComparisonStatement`) from
Rückert's Nullstellensatz, recorded there as
`AffineAnalytification.RueckertNullstellensatzStatement`.
The Nullstellensatz is proved in `SGA.Foundations.Analytic.Nullstellensatz`
(`AnalyticGeometry.LocalModelData.isNilpotent_classOf_of_eventually_eq_zero`). This file
combines the two and restates the consequences of XII.2.2 unconditionally: XII.2.2, XII.2.3,
XII.3.1 (viii), XII.3.2 (ii) and the closedness part of the converse of XII.3.2 (v).
-/

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry CategoryTheory Topology

/-- Rückert's Nullstellensatz, the analytic input of XII.2.2. -/
theorem AffineAnalytification.rueckertNullstellensatz :
    AffineAnalytification.RueckertNullstellensatzStatement :=
  fun _ _ g x G hG h ↦
    (AnalyticGeometry.polynomialModel g).isNilpotent_classOf_of_eventually_eq_zero x G hG h

namespace SchemePoints

/-- XII.2.2: for `X` locally of finite type over `ℂ` and `T ⊆ X` locally constructible, the
closure of `T(ℂ)` in `X(ℂ)` is the set of `ℂ`-points of the Zariski closure of `T`. -/
theorem closureComparison : ClosureComparisonStatement :=
  closureComparisonStatement_of_rueckert AffineAnalytification.rueckertNullstellensatz

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- XII.2.2, pointwise form. -/
theorem closure_preimage_pt_eq {T : Set X} (hT : IsLocallyConstructible T) :
    closure (pt ⁻¹' T : Set (SchemePoints ℂ X)) = pt ⁻¹' closure T :=
  closureComparison X T hT

/-- XII.2.3: a locally constructible `T ⊆ X` is closed if and only if `T(ℂ)` is closed. -/
theorem isClosed_iff {T : Set X} (hT : IsLocallyConstructible T) :
    IsClosed T ↔ IsClosed (pt ⁻¹' T : Set (SchemePoints ℂ X)) :=
  isClosed_iff_of_closureComparison closureComparison hT

/-- XII.2.3: a locally constructible `T ⊆ X` is open if and only if `T(ℂ)` is open. -/
theorem isOpen_iff {T : Set X} (hT : IsLocallyConstructible T) :
    IsOpen T ↔ IsOpen (pt ⁻¹' T : Set (SchemePoints ℂ X)) :=
  isOpen_iff_of_closureComparison closureComparison hT

/-- XII.2.3: a locally constructible `T ⊆ X` is dense if and only if `T(ℂ)` is dense. -/
theorem dense_iff {T : Set X} (hT : IsLocallyConstructible T) :
    Dense T ↔ Dense (pt ⁻¹' T : Set (SchemePoints ℂ X)) :=
  dense_iff_of_closureComparison closureComparison hT

/-- XII.3.2 (ii): a quasi-compact `f : Y → X` of `ℂ`-schemes locally of finite type is dominant if
and only if `Y(ℂ) → X(ℂ)` has dense image. -/
theorem denseRange_map_iff' {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : Y ⟶ X) [f.IsOver (Spec (.of ℂ))]
    [QuasiCompact f] : DenseRange (map (K := ℂ) f) ↔ DenseRange f :=
  denseRange_map_iff closureComparison f

/-- XII.3.1 (viii) for `X → Spec ℂ`: `X` is separated if and only if `X(ℂ)` is Hausdorff. -/
theorem isSeparated_iff_t2Space' (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    IsSeparated (X ↘ Spec (.of ℂ)) ↔ T2Space (SchemePoints ℂ X) :=
  isSeparated_iff_t2Space closureComparison X

/-- XII.3.1 (viii): a morphism of `ℂ`-schemes locally of finite type is separated if and only if
`X(ℂ) → Y(ℂ)` is a separated map. -/
theorem isSeparated_iff_isSeparatedMap' {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] :
    IsSeparated f ↔ IsSeparatedMap (map (K := ℂ) f) :=
  isSeparated_iff_isSeparatedMap closureComparison f

/-- XII.3.2 (v), part of the converse: a quasi-compact `f` with `X(ℂ) → Y(ℂ)` proper is a closed
map. -/
theorem isClosedMap_of_isProperMap_map' {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    [QuasiCompact f] (hf : IsProperMap (map (K := ℂ) f)) : IsClosedMap f :=
  isClosedMap_of_isProperMap_map closureComparison f hf

end SchemePoints

end SGA.SGA1.ExposeXII
