/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.AnalyticGluingMap
import SGA.SGA1.ExposeXII.MorphismComparisonScheme

/-!
# SGA 1, Exposé XII, 3.1 (i)–(iii) for separated schemes

Let `f : X → Y` be a morphism of separated `ℂ`-schemes locally of finite type and
`f^an : X^an → Y^an` the induced morphism of analytic spaces (`AnalyticGluing.analyticMap`). Then
`f` is flat (resp. unramified, resp. étale) iff `f^an` is:

* XII.3.1 (i): `AnalyticGluing.flat_iff_forall_flat_stalkMap_analyticMap`;
* XII.3.1 (ii): `AnalyticGluing.formallyUnramified_iff_forall_map_maximalIdeal_analyticMap`, with
  "`f^an` unramified at `x`" meaning `𝔪_{f^an(x)} 𝒪_{X^an,x} = 𝔪_{X^an,x}` (SGA's "net"; the
  residue fields of `X^an` are `ℂ`). Since `f` is locally of finite type, formally unramified is
  unramified;
* XII.3.1 (iii): `AnalyticGluing.etale_iff_forall_analyticMap`.

The proof is SGA's: `f^an` is flat (resp. unramified) at `x` iff `f` is at the closed point
`φ(x)` (comparison of local rings, `MorphismComparison.lean`), the corresponding loci of `f` are
open, and `X` is a Jacobson scheme (`MorphismComparisonScheme.lean`).

(iv) smooth is `AnalyticGluing.smooth_iff_forall_analyticMap` (`MorphismComparisonSmooth.lean`);
(vii) in one direction is `AnalyticGluing.injective_analyticMap_of_injective`
(`MorphismComparisonPoints.lean`); (ix) is `AnalyticGluing.isIso_iff_isIso_analyticMap`
(`MorphismComparisonIso.lean`) and (xi) is
`AnalyticGluing.isOpenImmersion_iff_isOpenImmersion_analyticMap`
(`MorphismComparisonOpenImmersion.lean`), both for quasi-compact `f`. Not covered: (v), (vi) (they
need the converse directions of XII.2.1 (vi), (vii)), the converse of (vii), (viii) and (x) (they
need fibre products of analytic spaces). Separatedness is assumed because the
analytic space `X^an` is built here for separated `X` only (every `X` in SGA's applications of
GAGA is proper, hence separated).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

open LocallyRingedSpaceComparison

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

omit [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] in
lemma locallyOfFiniteType_of_isOver : LocallyOfFiniteType f := by
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of ℂ))) := by
    rw [CategoryTheory.comp_over]
    infer_instance
  exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of ℂ))

/-- XII.3.1 (i): a morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type is flat
iff `f^an : X^an → Y^an` is flat at every point. -/
theorem flat_iff_forall_flat_stalkMap_analyticMap :
    Flat f ↔ ∀ x, ((analyticMap f).stalkMap x).hom.Flat := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  have := locallyOfFiniteType_of_isOver f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  exact flat_iff_forall_flat_stalkMap_of_comparison (analyticMap_toScheme f)
    isComparison_toScheme isComparison_toScheme range_toScheme_base.symm.subset

/-- XII.3.1 (ii): a morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type is
unramified iff `f^an` is unramified at every point `x`, i.e. `𝔪_{f^an(x)} 𝒪_{X^an,x} = 𝔪_x`. -/
theorem formallyUnramified_iff_forall_map_maximalIdeal_analyticMap :
    FormallyUnramified f ↔ ∀ x, (maximalIdeal _).map ((analyticMap f).stalkMap x).hom =
      maximalIdeal _ := by
  have := locallyOfFiniteType_of_isOver f
  exact formallyUnramified_iff_forall_map_maximalIdeal_of_comparison (X ↘ Spec (.of ℂ))
    (Y ↘ Spec (.of ℂ)) (CategoryTheory.comp_over f _) (analyticMap_toScheme f) isComparison_toScheme
    isComparison_toScheme range_toScheme_base range_toScheme_base.subset

/-- XII.3.1 (iii): a morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type is étale
iff `f^an` is flat and unramified at every point.

"`f^an` étale" is taken here to mean "flat and unramified at every point", which is how SGA proves
(iii) ("(i), (ii), hence also (iii)"). XII.3.1 (xi) and XII.4.6 use étale analytic morphisms as
local isomorphisms; the equivalence of the two notions (an inverse function theorem for singular
local models) is not proved. -/
theorem etale_iff_forall_analyticMap :
    Etale f ↔ ∀ x, ((analyticMap f).stalkMap x).hom.Flat ∧
      (maximalIdeal _).map ((analyticMap f).stalkMap x).hom = maximalIdeal _ := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  have := locallyOfFiniteType_of_isOver f
  exact etale_iff_forall_of_comparison (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
    (CategoryTheory.comp_over f _) (analyticMap_toScheme f) isComparison_toScheme
    isComparison_toScheme range_toScheme_base range_toScheme_base.subset

end AnalyticGluing

end SGA.SGA1.ExposeXII
