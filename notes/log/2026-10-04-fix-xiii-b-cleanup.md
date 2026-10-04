---
author: fix-xiii-b
date: 2026-10-04
area: SGA1 X, SGA1 XI, SGA1 XIII, Foundations/Cohomology, sga1-oos-coord, xiii43, xiii212, xiii213, xiii46
kind: experience
---

# Wave-1 cleanup of the XIII streams (xiii43, xiii212, xiii213, xiii46)

Cleanup after wave 1, run by the coordinator. Every module listed below, its direct importers and
the barrels `SGA.SGA1.ExposeX`, `ExposeXI`, `ExposeXIII` and `SGA.Foundations` build.

## Reviewer blockers fixed

- **XIII.5.5 ring.** `ExposeXIII.relativeAbhyankarRing` (`ExposeXIII/RelativeAbhyankar.lean`) is
  now an abbrev for `KummerAlgebra n (fun i : I ↦ toStrictLocalizationTop ξ (f i))`
  (`ExposeXIII/KummerCoverings.lean`). It is definitionally the old ring, checked by `rfl` in a
  scratch file, so `RelativeAbhyankarStatement` is unchanged. Registry row A9 updated.
- **"Coverings of degree prime to p are tame" is false without "Galois".** In characteristic 2 a
  degree-3 subcover of an `S₃`-covering of `𝔸¹` has degree prime to `p` but is not tame. Fixed the
  docstrings of `tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement` and of its
  primed version, and the XIII.2.12 item in `topics/hard-parts.md`.
  `GaloisCoveringsTameStatement` said "statement only"; it now points to
  `galoisCoveringsTameStatement`.
- **Registry row A32** now lists the `Subring.*` patching API (`Subring.HasGLFactorization`,
  `exists_basis_forall_repr_mem_iff`, `exists_basis_span_eq`, `hasGLFactorization_of_isAdicComplete`)
  and puts `Subfield.span_inter_eq_top` in `Modules.lean`. I checked every name with grep.

## Stale docstrings

- `ProperSmoothHomotopyExactSequenceStatement` (open in general) now names the proved cases:
  `properSmoothHomotopyExactSequence_of_field`, `isProLShortExact_of_isRegularLocalRing` and
  `properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`.
- `TameRamificationAtMaximalPointsStatement` and the `NormalCrossings` module docstring: XIII.5.5
  is stated as `RelativeAbhyankarStatement` (not proved).
- `ExposeXIII/ArtinSchreier.lean`: the π₁ identification is `affineLineArtinSchreier`. On
  Abhyankar's conjecture:
  - the necessary condition is `sylowSup_eq_top_of_affineLine`;
  - `p`-groups: `abhyankarAffineLine_of_isPGroup`;
  - `S₃` and `A₄`: `exists_surjective_of_mulEquiv_perm_fin_three` and `…_alternatingGroup_fin_four`;
  - Serre's theorem: `SerrePKernel.affineLinePExtension`;
  - Raynaud's reduction: `SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`.
- `SchemeFundamentalGroup.lean`: the same pointers for `AbhyankarAffineLineStatement`.
  `KunnethCharZeroStatement` now points to `surjective_map_prod_of_isAlgClosed` and to the
  resolution-free reductions to `AffineLineOpenInvarianceStatement`
  (`bijective_map_prod_of_isNormalScheme_of_isNormalScheme`, `…_of_smooth`).

## Dedups

- `infinite_continuousMonoidHom_aut_fiberFunctor` moved from `AffineLinePGroups.lean` to
  `AffineLineFundamentalGroup.lean`, with the same full name. `not_isTopologicallyFG_aut_fiberFunctor`
  is now a three-line corollary of it.
- `ExposeXIII.TameRamification` now has `galoisClosure_eq_fieldRange`, `finrank_galoisClosure`,
  `isTameExtension_of_isGalois` (any local `R`, from xiii212's `TameGaloisAlgebra` copy) and
  `ramificationIdx_dvd_finrank` (DVR). Deleted:
  - the `TameGaloisAlgebra` copies;
  - `ExposeXI.MultiplicativeGroupCovering.{isTameExtension_of_isGalois, ramificationIdx_dvd_finrank}`.

  `ExposeX.isTamelyRamifiedAt_and_dvd_of_isGalois` is now derived from these lemmas with
  `isTameExtension_iff_isTamelyRamifiedOver`.
- `isPushout_app_of_isPullback` moved to `Foundations/Cohomology/FlatBaseChange.lean` as
  `AlgebraicGeometry.CohomologyAux.isPushout_app_of_isPullback`. `isPushout_app_pullback_snd` is
  now its corollary, and the two callers in `TameLiftingExtension.lean` are updated.
- `ExposeX/ProperOverField.lean` now imports `Foundations/Fields/GeometricallyConnected.lean`, and
  its lemmas are one-line corollaries:
  - `trivialIdempotents_tensor_of_isAlgClosed` of `trivialIdempotents_tensorProduct_of_isAlgClosed`;
  - `connectedSpace_pullback_of_isAlgClosed` of `geometricallyConnected_of_isAlgClosed`.

  xiii46's general X.1.8 surjectivity (`ExposeXIII.surjective_map_pullback_fst_of_isAlgClosed`,
  `KunnethSurjective.lean`) moved here as `ExposeX.surjective_map_pullback_fst_of_isAlgClosed`. The
  proper version `ExposeX.surjective_map_pullback_of_isAlgClosed` is its corollary, and the Kunneth
  callers are updated. I moved it down rather than importing `KunnethSurjective`, because that
  module pulls ExposeXI into ExposeX.
- `MultiplicativeGroup.lean` uses `fundamentalGroupSpecContinuousMulEquiv`.

## Left for the coordinator (files not mine)

- Registry rows A11, A16 and A20 name the old locations:
  - A11: `surjective_map_pullback_fst_of_isAlgClosed` is now `ExposeX.…` in `ProperOverField.lean`;
  - A16: `isTameExtension_of_isGalois` and `finrank_galoisClosure` are now in the `ExposeXIII`
    namespace, in `TameRamification.lean`. Its title "(`p'`-covers are tame)" should say Galois,
    and "(proof todo)" is stale;
  - A20: `infinite_continuousMonoidHom_aut_fiberFunctor` is now in `AffineLineFundamentalGroup.lean`.
- `topics/strategy.md` (≈ l. 557) names `ExposeX.isPushout_app_of_isPullback`, which is now
  `CohomologyAux.isPushout_app_of_isPullback`.
- `docs/formalization.md`: XIII.2.3 b) is proved for *Galois* coverings of degree prime to `p`.
- `AffineLinePrimeToP.lean` cannot use `fundamentalGroupSpecContinuousMulEquiv`: it is upstream of
  `AffineLinePGroups` (via `SchemeFundamentalGroup`), and `FundamentalGroup` is only defined in
  `SchemeFundamentalGroup`.
