/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.Stacks
import SGA.SGA1.ExposeXIII.EtaleBaseChange
import SGA.SGA1.ExposeXIII.EtaleRestriction
import SGA.SGA1.ExposeXIII.LocallyConstantSheaves
import SGA.SGA1.ExposeXIII.CohomologicalProperness
import SGA.SGA1.ExposeXIII.ExactDiagrams
import SGA.SGA1.ExposeXIII.TameRamification
import SGA.SGA1.ExposeXIII.NormalCrossings
import SGA.SGA1.ExposeXIII.ProLQuotient
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeXIII.ProperHomotopySequence
import SGA.SGA1.ExposeXIII.Coinvariants
import SGA.SGA1.ExposeXIII.ArtinSchreier
import SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP
import SGA.SGA1.ExposeXIII.RegularLocalRing
import SGA.SGA1.ExposeXIII.RootAdjunction
import SGA.SGA1.ExposeXIII.KummerCoverings
import SGA.SGA1.ExposeXIII.AbhyankarBasic
import SGA.SGA1.ExposeXIII.AbhyankarSmooth
import SGA.SGA1.ExposeXIII.AbhyankarPurity
import SGA.SGA1.ExposeXIII.AbhyankarDescent
import SGA.SGA1.ExposeXIII.Abhyankar
import SGA.SGA1.ExposeXIII.DirectImageFiniteness
import SGA.SGA1.ExposeXIII.AbhyankarAffineLine
import SGA.SGA1.ExposeXIII.AbhyankarAffineLineExamples
import SGA.SGA1.ExposeXIII.AffineLinePGroups
import SGA.SGA1.ExposeXIII.CurveFundamentalGroup
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupPresentation
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupProjectiveLine
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupTame
import SGA.SGA1.ExposeXIII.Desingularization
import SGA.SGA1.ExposeXIII.DesingularizationCurves
import SGA.SGA1.ExposeXIII.DesingularizationCurvesStrong
import SGA.SGA1.ExposeXIII.KunnethCurve
import SGA.SGA1.ExposeXIII.KunnethCurveOpen
import SGA.SGA1.ExposeXIII.KunnethField
import SGA.SGA1.ExposeXIII.KunnethFiniteEtale
import SGA.SGA1.ExposeXIII.KunnethInvariance
import SGA.SGA1.ExposeXIII.KunnethMain
import SGA.SGA1.ExposeXIII.KunnethNormal
import SGA.SGA1.ExposeXIII.KunnethNormalProduct
import SGA.SGA1.ExposeXIII.KunnethSurjective
import SGA.SGA1.ExposeXIII.KunnethTower
import SGA.SGA1.ExposeXIII.LocalAcyclicity
import SGA.SGA1.ExposeXIII.LocalAcyclicityField
import SGA.SGA1.ExposeXIII.LocalAcyclicityFieldAspherical
import SGA.SGA1.ExposeXIII.LocalAcyclicityFieldStalks
import SGA.SGA1.ExposeXIII.LocalAcyclicitySmoothBaseChange
import SGA.SGA1.ExposeXIII.MultiplicativeGroup
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertia
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaChart
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaKummer
import SGA.SGA1.ExposeXIII.ProLShortExact
import SGA.SGA1.ExposeXIII.ProperBaseChange
import SGA.SGA1.ExposeXIII.ProperBaseChangeClosure
import SGA.SGA1.ExposeXIII.ProperBaseChangeField
import SGA.SGA1.ExposeXIII.ProperBaseChangeHenselian
import SGA.SGA1.ExposeXIII.ProperBaseChangeNoetherian
import SGA.SGA1.ExposeXIII.ProperBaseChangeRepresentable
import SGA.SGA1.ExposeXIII.ProperSmoothTame
import SGA.SGA1.ExposeXIII.RelativeAbhyankar
import SGA.SGA1.ExposeXIII.SerrePKernel
import SGA.SGA1.ExposeXIII.SerrePKernelCounting
import SGA.SGA1.ExposeXIII.SerrePKernelFrobenius
import SGA.SGA1.ExposeXIII.SerrePKernelLift
import SGA.SGA1.ExposeXIII.SerrePKernelProper
import SGA.SGA1.ExposeXIII.SerrePKernelVector

/-!
# SGA 1, Exposé XIII — Cohomological properness of sheaves of sets and of non-commutative groups

English translation: `translation/SGA1/ExposeXIII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §0–§1, stacks, étale sheaves and cohomological properness: `Stacks`, `EtaleBaseChange`,
  `EtaleRestriction`, `LocallyConstantSheaves`, `CohomologicalProperness`, `ExactDiagrams`.
  XIII 1.4 in dimension `≤ -1` holds for every universally closed `f`, for sheaves of sets and of
  groups (`isCohomologicallyProperLENegOne_of_universallyClosed`,
  `isCohomologicallyProperLENegOneGroup_of_universallyClosed`), and with it 1.8 (sheaves of sets)
  and 1.9 in dimension `≤ -1`; 1.9 in dimension `≤ 0` holds for `f` finite
  (`isCohomologicallyProperLEZero_pushforward_iff_of_isFinite`) and for `f` integral given SGA 4
  VIII 5.6 (`IntegralBaseChangeStatement`, `isCohomologicallyProperLEZero_pushforward_iff`).
  XIII 1.4 for sheaves of sets holds over a locally noetherian base, for every sheaf, from Gabber's
  theorem (`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`,
  `ProperBaseChangeNoetherian`, which also gives 1.8 in dimension `≤ 0` over such a base), and
  by a more elementary argument for sheaves represented by separated étale schemes
  (`ProperBaseChangeRepresentable`, `ProperBaseChangeField`, `ProperBaseChangeHenselian`);
  cohomological properness in dimension `≤ 0` passes to subsheaves for `f` universally closed,
  and to finite limits (`ProperBaseChangeClosure`). `ProperBaseChange` states proper base change
  in degree `≤ 1` for étale coverings over a henselian local base (SGA 4 XII 5.5, which contains
  IX.1.10; `HenselianEtaleCoveringsOfClosedFibreStatement`); faithfulness is proved over every
  local base and fullness over a noetherian henselian base (`ProperBaseChangeHenselian`).
* §2, tame ramification and divisors with normal crossings: `TameRamification`,
  `NormalCrossings`, `ProLQuotient`; XIII.2.3 b) for Galois coverings of degree prime to `p` of
  `X` minus finitely many points, `X` a proper smooth connected curve over a separably closed
  field, the case used in 2.12 (`galoisCoveringsTameStatement`, `primeToPCoveringsTameStatement`,
  `CurveFundamentalGroupTame`).
* XIII.2.12, the tame fundamental group of a curve minus `n` points: the statement and its
  "in other words" form (`CurveFundamentalGroup`, `CurveFundamentalGroupPresentation`), and the
  proof that the first implies the second (`CurveFundamentalGroupTame`). The cases
  `(g, n) = (0, 0)`, `(0, 1)` and `(0, 2)` on `ℙ¹`, for `k` algebraically closed and the points
  `∞`, resp. `0, ∞`, with the inertia conditions, are proved in the "in other words" form without
  Riemann's existence theorem (`tameCurvePrimeToPConclusion_projectiveLine_zero`, `_one`,
  `_two`): `π₁^{p'}(𝔸¹_k) = 1` (`AffineLinePrimeToP`), `π₁^{p'}(𝔾_m)` is the prime-to-`p`
  completion of `ℤ` (`MultiplicativeGroup`), inertia (`MultiplicativeGroupInertia`,
  `MultiplicativeGroupInertiaChart`, `MultiplicativeGroupInertiaKummer`), and `ℙ¹`
  (`CurveFundamentalGroupProjectiveLine`).
* Remark 2.13, the affine line in characteristic `p`: the Artin–Schreier description of
  `Hom(π₁(𝔸¹_k), ℤ/p)` and the fact that `π₁(𝔸¹_k)` is not topologically finitely generated
  (`ArtinSchreier`, `AffineLineFundamentalGroup`). Abhyankar's conjecture for the affine line
  (statement and necessary condition in `SchemeFundamentalGroup`): `p`-groups and central
  `p`-extensions (`AffineLinePGroups`; `exists_surjective_fundamentalGroup_affineLine_of_isPGroup`),
  `S₃` for `p = 2` and `A₄` for `p = 3` (`AbhyankarAffineLineExamples`), Serre's theorem on
  extensions by `p`-groups (`SerrePKernel.affineLinePExtension`; `SerrePKernel`,
  `SerrePKernelCounting`, `SerrePKernelFrobenius`, `SerrePKernelLift`, `SerrePKernelProper`,
  `SerrePKernelVector`), and with it the reduction of the conjecture to Raynaud's cases A
  (patching) and B, which are stated (`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`,
  `AbhyankarAffineLine`).
* §3, generic cohomological properness and local acyclicity: `LocalAcyclicity` states 3.1 1),
  3.3, 3.4, 3.5 and their inputs SGA 4 XV 2.1 and 4.1, and proves 3.3 and 3.4 for étale `f`, and
  for smooth `f` given SGA 4 XV 2.1 (`exists_isUniversallyLocallyOneAspherical_of_etale`,
  `exists_isUniversallyLocallyOneAspherical_of_smooth`); 3.2 1) is proved for every field
  (`fieldCohomologicalPropernessStatement`; `LocalAcyclicityField`, `LocalAcyclicityFieldStalks`);
  local `1`-asphericity over a field in the non-universal form
  (`LocalAcyclicityFieldAspherical`); smooth base change in degree `0`, given SGA 4 XV 2.1
  (`LocalAcyclicitySmoothBaseChange`). The desingularization hypotheses of §3 and of 4.6
  (`Desingularization`) are proved in dimension `≤ 1` over a perfect field
  (`DesingularizationCurves`, `DesingularizationCurvesStrong`).
* §4, homotopy exact sequences: `SchemeFundamentalGroup`, `HomotopySequence`,
  `ProperHomotopySequence` (4.4 first part, 4.5, 4.6 for `π₁^L` and `X` proper), `Coinvariants`
  (4.7–4.8). The conclusion of 4.3, hence the second part of 4.4 without the section, over a
  field, at the closed point of a complete regular local base, and over a complete discrete
  valuation ring with separably closed residue field (`ProLShortExact`, `ProperSmoothTame`). The
  Künneth formula 4.6: the surjectivity half in every characteristic, for `k` algebraically closed
  and `X`, `Y` connected (`surjective_map_prod_of_isAlgClosed`, `KunnethSurjective`); in
  characteristic `0`, for `k` algebraically closed and without resolution of singularities,
  `π₁(X ×ₖ 𝔸¹) ≅ π₁(X)` for `X` connected, normal and locally of finite type
  (`bijective_map_prod_affineLine_of_isNormalScheme`), and 4.6 for `X`, `Y` connected, normal and
  locally of finite type (`Y` quasi-compact and quasi-separated) given the case of the open subsets
  of `𝔸¹` (`AffineLineOpenInvarianceStatement`;
  `bijective_map_prod_of_isNormalScheme_of_isNormalScheme`) (`KunnethField`, `KunnethNormal`,
  `KunnethMain`, `KunnethInvariance`, `KunnethCurve`, `KunnethFiniteEtale`, `KunnethCurveOpen`,
  `KunnethTower`, `KunnethNormalProduct`).
* Appendix I, Abhyankar's lemma: `RegularLocalRing`, `RootAdjunction`, `KummerCoverings`,
  `AbhyankarBasic`, `AbhyankarSmooth`, `AbhyankarPurity`, `AbhyankarDescent`, `Abhyankar`; the
  relative lemma 5.5 is stated, existence part only (`RelativeAbhyankar`).
* Appendix II, finiteness of direct images of stacks: `DirectImageFiniteness`.

Open, stated as `…Statement`: 1.4 for sheaves of sets over an arbitrary base
(`ProperBaseChangeStatement`); SGA 4 VIII 5.6 (`IntegralBaseChangeStatement`); SGA 4 XII 5.5
(`HenselianEtaleCoveringsOfClosedFibreStatement`: essential surjectivity, and fullness over a
non-noetherian base); 2.3 a) and 2.4 1) (`TameRamificationAtMaximalPointsStatement`,
`TameBaseChangeStatement`); 2.12 (`TameCurveFundamentalGroupStatement`); 2.13
(`AbhyankarAffineLineStatement`, through `AffineLinePatchingStatement` and
`AffineLineCaseBStatement`; Raynaud's proof of case B uses `SemistableReductionStatement`); §3
(`GenericCohomologicalPropernessStatement`, `GenericCohomologicalPropernessConstructibleStatement`,
`GenericLocalAsphericityStatement`, `FieldLocalAsphericityStatement`,
`GenericSpecializationStatement`, and SGA 4 XV 2.1 and 4.1, `LocalAsphericitySmoothStatement`,
`LocalAcyclicityFlatReducedStatement`); 4.4, second and third parts
(`ProperSmoothHomotopyExactSequenceStatement`, `ProperSmoothHomotopyExactSequenceRegularStatement`,
`NormalCrossingsHomotopyExactSequenceStatement`, `NormalCrossingsShortExactSequenceStatement`);
4.6 in characteristic `0` (`KunnethCharZeroStatement`, `InvarianceCharZeroStatement`,
`AffineLineOpenInvarianceStatement`); 5.2 and 5.5, existence parts
(`AbsoluteAbhyankarStatement`, `RelativeAbhyankarStatement`). Not formalized: stacks of torsors
and their inverse images; 1.4 for sheaves of groups in dimension `≤ 0`
(`IsCohomologicallyProperLEZeroGroup` is defined; no theorem proves it for proper `f`); 1.8 for
sheaves of groups, in any dimension;
cohomological properness in dimension `≤ 1` for sheaves of groups and 1-constructible stacks,
hence 3.1 2), 3.2 2), 4.3 as stated and 6.1–6.3; 2.3 b) beyond the Galois coverings of curves
above; 5.6–5.7. `docs/formalization.md` and `lean/SGA/Foundations/README.md` discuss what the
in-scope and the out-of-scope items still need.
-/
