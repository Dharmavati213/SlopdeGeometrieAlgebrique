# Foundations

Prerequisites of the SGA 1 formalization that mathlib does not have, written as if for mathlib:
mathlib namespaces and naming, no SGA numbers in names, module docstrings citing EGA, SGA 4 or the
Stacks Project. The barrel is `SGA.Foundations` (`SGA/Foundations.lean`); its docstring lists the
areas covered.

## Out of scope

Some results of SGA 1 rest on theories that the seminar quotes from elsewhere: Hodge theory,
resolution of singularities, complex analytic geometry beyond the local theory, the étale
cohomology of SGA 4, and Raynaud's proof of Abhyankar's conjecture. These results are recorded as
faithful `Prop`-valued `…Statement` definitions, and every consequence SGA draws from them is
proved from the statement. The working plan is in
[`notes/topics/out-of-scope-plan.md`](../../../notes/topics/out-of-scope-plan.md).

Some routes avoid the theory SGA quotes:

- X.2.9 in characteristic 0 (for `#k ≤ 𝔠`, in universe 0) is proved without Riemann existence.
- XII.5.2 is reduced to XII.5.1 without triangulation.
- XIII.4.6 in characteristic 0 is proved for `X` and `Y` normal, `Y` quasi-compact and
  quasi-separated, without resolution of singularities, through the case of the open subsets of
  the affine line (`AffineLineOpenInvarianceStatement`, proved).

Of the statements in the Lean entries below, only XIII.3.2 1)
(`FieldCohomologicalPropernessStatement`) and `AffineLineOpenInvarianceStatement` (an input of
XIII.4.6) are proved in full. The Proved entries list partial and
conditional results with their hypotheses. Every open `…Statement` not in a Lean entry
(`RelativeAbhyankarStatement`, for example) is in-scope work, not out of scope;
[`docs/formalization.md`](../../../docs/formalization.md) lists them.

Items are in the order of the exposés. Files are under `SGA/SGA1/` unless the path starts with
`Foundations/`.

### X.2.9, X.2.12

- **SGA.** `π₁` of a proper connected variety over an algebraically closed field is topologically
  finitely generated.
- **Lean.** `TopologicallyFiniteStatement` (`ExposeX/Semicontinuity.lean`).
- **Proved.**
  - For `k` algebraically closed of characteristic 0 with `#k ≤ 𝔠`, in universe 0, without
    Riemann existence: X.2.9 (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`) and
    X.2.12 (`finite_principalH1_of_mk_le_continuum`), both in
    `ExposeX/TopologicallyFiniteCharZero.lean`.
  - In every characteristic, X.2.9 follows from the curve case (X.2.6 for normal integral proper
    curves): `topologicallyFiniteStatement_of_curve`, and from the case of plane curves,
    `topologicallyFiniteStatement_of_planeCurve` (`ExposeX/TopologicallyFiniteBertini.lean`);
    also `topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`.
  - X.2.10 in an existence form, in every characteristic and without projectivity
    (`exists_hyperplane_section`).
  - From Exposé IX: IX.5.2 for `S` noetherian and connected and `g` proper surjective, in place
    of an effective descent morphism
    (`ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_isProper_of_surjective`).
  - From Exposé IX: a consequence of IX.5.4, under hypotheses replacing SGA's
    (`ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_pinching`).
- **Missing.** The curve case in characteristic `p` (SGA lifts the curve by III.7.4); X.2.10 in
  SGA's form; `#k > 𝔠`; universes above 0.

### XI.1.4

- **SGA.** (Serre) A smooth proper (SGA: projective) unirational variety over an algebraically
  closed field of characteristic 0 is simply connected.
- **Lean.** `SerreUnirationalSimplyConnectedStatement` (`ExposeXI/Geometry.lean`). In
  `ExposeXI/SerreUnirational.lean`: `HodgeSymmetryZeroStatement` (`h^{0,q} = h^{q,0}`) and
  `UnirationalStructureSheafVanishingStatement` (step 2: `H^q(X, 𝒪) = 0` for `q > 0`).
- **Proved.**
  - XI.1.4 from Hodge symmetry (`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`),
    through step 2 (`unirationalStructureSheafVanishing_of_hodgeSymmetryZero`) and steps 3–4
    (`serreUnirationalSimplyConnectedStatement_of_vanishing`).
  - Step 1, `H⁰(X, Ω^q) = 0` for `q > 0`, in characteristic 0
    (`regularForms_eq_bot_of_isUnirational`).
  - Steps 3–4 in every characteristic, without Riemann–Roch: finite étale coverings of unirational
    varieties are unirational (`isUnirational_of_isFinite_of_etale`), and `χ(𝒪)` is
    multiplicative in finite étale coverings (`eulerCharFiniteEtaleStatement`,
    `Foundations/Cohomology/`).
  - In every characteristic, `#π₁` divides the separable degree of a unirational parametrization
    (`natCard_etaleFundamentalGroup_dvd_finSepDegree`).
  - In every characteristic, unirational curves are simply connected
    (`isSimplyConnected_of_isUnirational_of_trdeg_eq_one`).
- **Missing.** `HodgeSymmetryZeroStatement` for `q ≥ 1` (`q = 0` is
  `finrankH_unit_zero_eq_finrank_regularForms_zero`), which is analytic Hodge theory.

### XI.2.1

- **SGA.** `π₁(A) ≅ lim_n K_n` for an abelian variety `A`.
- **Lean.** `AbelianVarietyFundamentalGroupStatement` and `MulNIsogenyStatement`
  (`ExposeXI/TateModule.lean`); `AbelianVarietyPrimaryComponentStatement`
  (`ExposeXI/TateModulePrimary.lean`).
- **Proved** (none of it uses the theorem of the cube).
  - The key step `SerreLangStatement` (`serreLangStatement`, `ExposeXI/SerreLang.lean`).
  - XI.2.1 in characteristic 0 (`exists_tateModule_equiv_of_charZero`).
  - The `ℓ`-primary clause of XI.2.1 for every prime `ℓ ≠ char k`
    (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`).
  - All of XI.2.1 from SGA's cited "`n_A` is an isogeny"
    (`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`).
  - `n_A` is an isogeny for `n` invertible in `k` (`mulNIsogeny_of_ne_zero`).
- **Missing.** In characteristic `p`, the `p`-primary clause, to which XI.2.1 is equivalent there
  (`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`). It follows from `p_A`
  finite and surjective (`exists_tateModule_equiv_of_charP`), the open case `n = p` of
  `MulNIsogenyStatement`, whose proof needs the theorem of the cube and an ample line bundle.

### XII.3.1, XII.4

- **SGA.** XII.3.1 for `f^an`: a morphism `f` of `ℂ`-schemes locally of finite type is (i) flat,
  (ii) unramified, (iii) étale, (iv) smooth, (v) normal, (vi) reduced, (vii) injective,
  (viii) separated, (ix) an isomorphism, (x) a monomorphism, (xi) an open immersion if and only
  if `f^an` is. XII.4: GAGA.
- **Lean.** `CohomologyComparisonStatement`, `CoherentEquivalenceStatement`,
  `AnalyticFullyFaithfulStatement`, `FiniteAnalyticEquivalenceStatement` (XII.4.3–4.6,
  `ExposeXII/GAGA.lean`). XII.4.1–4.2 are not stated.
- **Proved.**
  - For separated `X` in `Scheme.{0}`, `X^an` glued from affine charts
    (`AnalyticGluing.analyticSpace`).
  - XII.3.1 for `f^an`, `X` and `Y` separated (all in `AnalyticGluing`):
    - (i) `flat_iff_forall_flat_stalkMap_analyticMap`;
    - (ii) `formallyUnramified_iff_forall_map_maximalIdeal_analyticMap`;
    - (iii) `etale_iff_forall_analyticMap`, with "`f^an` étale" read as flat and unramified;
    - (iv) `smooth_iff_forall_analyticMap`, with "`f^an` smooth" read as flat with regular
      fibres;
    - (vii) in one direction (`injective_analyticMap_of_injective`);
    - (ix) and (xi) for quasi-compact `f` (`isIso_iff_isIso_analyticMap`,
      `isOpenImmersion_iff_isOpenImmersion_analyticMap`).
  - Towards Theorem B: Cousin I on a disc
    (`AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`,
    `Foundations/Analytic/Cousin.lean`) and Dolbeault's lemma on a disc
    (`AnalyticGeometry.exists_contDiffOn_dbar_eq_ball`).
  - Theorem B for `𝒪` on `Δ(r) × ℂᵃ × (ℂ*)ᵇ`, `Δ(r)` a polydisc:
    `AnalyticGeometry.polydiscProductVanishing : PolydiscProductVanishingStatement`
    (`Foundations/Analytic/TheoremB.lean`).
  - Oka's coherence theorem, germ form:
    `AnalyticGeometry.okaCoherence : OkaCoherenceStatement` (`Foundations/Analytic/Oka.lean`).
  - The analytic heart of Riemann existence for curves: on a compact Riemann surface, every point
    is the only pole of some meromorphic function (`compactRiemannSurfaceMeromorphic`,
    `ExposeXII/GAGACompactRiemannSurface.lean`).
- **Missing.**
  - Cartan–Serre finiteness (`CartanSerreFinitenessStatement`) and Theorems A and B for coherent
    analytic sheaves (`CoherentTheoremABStatement`), both in
    `Foundations/Analytic/CoherentStatements.lean`.
  - XII.4.1–4.2, which need `Rᵖf_*` on both sides.
  - XII.3.1 (v), (vi), (viii), (x) and the converse of (vii) for `f^an`; (iii) with "étale"
    meaning local isomorphism.

### XII.5.1

- **SGA.** The Riemann existence theorem: for `X` locally of finite type over `ℂ`, the functor
  `Ψ : X' ↦ X'^an` is an equivalence from finite étale coverings of `X` to finite étale coverings
  of `X^an`.
- **Lean.** `RiemannExistenceStatement`, `SchemeRiemannExistenceStatement`
  (`ExposeXII/RiemannExistence.lean`); `CurveRiemannExistenceStatement` (affine curves,
  `ExposeXII/RiemannCurves.lean`).
- **Proved.**
  - `Ψ : Y ↦ Y(ℂ)` is fully faithful (`schemePointsFunctorFullyFaithful`).
  - For connected `X`, the easy half of XII.5.2, `π̂₁(X(ℂ)) ↠ π₁(X)`
    (`surjective_autWhiskerLeft_schemePointsFunctor`).
  - The scheme and affine forms are equivalent (`schemeRiemannExistence_iff`).
  - XII.5.1 when `X(ℂ)` is simply connected
    (`isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`).
  - XII.5.1 for `𝔾_m` (`riemannExistence_laurentPolynomial`).
  - XII.5.1 for `ℂ ∖ S` with `S` finite, and for its finite étale coverings
    (`PuncturedPlane.riemannExistence_coordRing`, `PuncturedPlane.riemannExistence_finiteEtale`,
    `ExposeXII/GAGAFiberSeparating.lean`). Hence `π₁` of `ℙ¹_ℂ` minus `n + 1` points is
    isomorphic to the profinite completion of a free group on `n` generators, as an abstract
    isomorphism (`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`).
  - XII.5.1 for `A` of finite type over `ℂ` with `ringKrullDim A ≤ 1` (`curveRiemannExistence`),
    and for a scheme locally of finite type over `ℂ` with `topologicalKrullDim ≤ 1`
    (`schemeCurveRiemannExistence`), both in `ExposeXII/RiemannCurvesExistence.lean`.
- **Missing.** Higher dimension.

### XII.5.2

- **SGA.** `π₁(X)` is the profinite completion of `π₁(X(ℂ))`.
- **Lean.** `SchemeFundamentalGroupComparisonStatement`, `LocallyContractibleStatement`
  (`ExposeXII/FundamentalGroup.lean`); `FundamentalGroupComparisonStatement` (affine form,
  `ExposeXII/RiemannExistence.lean`).
- **Proved.**
  - For every connected `X` locally of finite type over `ℂ`, conditional only on XII.5.1:
    `schemeFundamentalGroupComparison_of_riemannExistence` (`ExposeXII/LocalTopologySLSC.lean`;
    the isomorphism is stated as `Nonempty`).
  - SGA uses only that `X(ℂ)` is locally path-connected and semilocally simply connected. Both are
    proved without triangulation:
    - locally path-connected, through Noether normalization and branched coverings:
      `locallyPathConnectedStatement` (`ExposeXII/LocalTopologyLPC.lean`; the branched coverings
      are in `ExposeXII/BranchedCover.lean`);
    - semilocally simply connected, through semialgebraic geometry:
      `semilocallySimplyConnectedStatement` (`Foundations/Semialgebraic/`: Tarski–Seidenberg, the
      Łojasiewicz inequality, a gradient retraction).
  - The affine form follows from the affine XII.5.1 alone
    (`fundamentalGroupComparison_of_riemannExistence`, `ExposeXII/StatementCorollaries.lean`).
    Its topological input `CoveringFundamentalGroupStatement` is proved
    (`coveringFundamentalGroupStatement`).
  - `LocallyContractibleStatement` holds for `X` smooth
    (`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`) and for `dim X ≤ 1`
    (`SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one`).
- **Missing.** XII.5.1. The stronger `LocallyContractibleStatement` (a basis of contractible
  neighbourhoods) is open for singular `X` of dimension `≥ 2`; it is not needed.

### XIII 1.4

- **SGA.** Proper base change, for sheaves of sets, and in degree 1 for étale coverings over a
  henselian base.
- **Lean.** `ProperBaseChangeStatement` (`ExposeXIII/CohomologicalProperness.lean`);
  `HenselianEtaleCoveringsOfClosedFibreStatement` (SGA 4 XII 5.5,
  `ExposeXIII/ProperBaseChange.lean`).
- **Proved.**
  - Dimension `≤ -1` for every universally closed `f`, for sheaves of sets and of groups
    (`isCohomologicallyProperLENegOne_of_universallyClosed`,
    `isCohomologicallyProperLENegOneGroup_of_universallyClosed`). This makes the following
    unconditional in dimension `≤ -1`:
    - XIII 1.8, for sheaves of sets (`IsCohomologicallyProperLENegOne.comp_of_universallyClosed`);
    - XIII 1.9, for sheaves of sets and of groups
      (`isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom`,
      `isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom`).
  - XIII 1.4 for every sheaf of sets over a locally noetherian base
    (`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`,
    `ExposeXIII/ProperBaseChangeNoetherian.lean`), through:
    - Gabber's theorem over a noetherian henselian base (`properHenselianSectionsStatement`,
      `Foundations/Etale/GabberHenselian.lean`);
    - SGA 4 VII 5.7 / VIII 5.2 in degree 0 (`Scheme.exists_toLimitSections_eq`,
      `Scheme.pushforwardStalkStrictLocalizationStatement`,
      `Foundations/Limits/EtaleSectionsGluing.lean`).
  - For étale coverings of `X` proper over `Spec A`, restriction to the closed fibre is faithful
    for every local `A` (`faithful_pullback_closedFibre_of_isLocalRing`) and full for `A`
    henselian and noetherian (`full_pullback_closedFibre_of_henselianLocalRing`), both in
    `ExposeXIII/ProperBaseChangeHenselian.lean`.
- **Missing.**
  - For sheaves of sets, an arbitrary base (EGA IV 8 spreading out and constructible sheaves, or
    Gabber over a non-noetherian base).
  - For étale coverings, essential surjectivity, and fullness for non-noetherian `A`.
  - For sheaves of groups, 1.4 in dimension `≤ 0` is not stated, and dimension `≤ 1` is not
    defined.

### XIII.2.12

- **SGA.** XIII.2.12 for general `g`, `n`: the tame fundamental group of a curve.
- **Lean.** `TameCurveFundamentalGroupStatement`, `TameCurvePrimeToPStatement`
  (`ExposeXIII/CurveFundamentalGroupPresentation.lean`).
- **Proved.**
  - On `ℙ¹`, for `k` algebraically closed (SGA: separably closed), the "in other words" form
    `TameCurvePrimeToPConclusion` (not the form of `TameCurveFundamentalGroupStatement`) at fixed
    points, all in `ExposeXIII/CurveFundamentalGroupProjectiveLine.lean`:
    - `(g, n) = (0, 0)` (`tameCurvePrimeToPConclusion_projectiveLine_zero`);
    - `(0, 1)` at `∞` (`tameCurvePrimeToPConclusion_projectiveLine_one`);
    - `(0, 2)` at `0, ∞`, with inertia (`tameCurvePrimeToPConclusion_projectiveLine_two`).
  - `π₁^{p'}(𝔾_m)` is the prime-to-`p` completion of `ℤ`, for `k` algebraically closed, without
    the inertia condition (`multiplicativeGroupPrimeToPStatement`).
  - Genus 0 over `ℂ`, without inertia data, in universe 0:
    `PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup` (see XII.5.1).
  - On a proper smooth connected curve over a separably closed `k`, minus finitely many points,
    Galois coverings of degree prime to `p` are tame (`galoisCoveringsTameStatement`), hence
    `primeToPCoveringsTameStatement`.
- **Missing.**
  - General `g`, `n`: in characteristic 0, Riemann existence plus surface topology; in
    characteristic `p`, also lifting (III.7.4) and tame specialization.
  - Arbitrary points of `ℙ¹` (SGA moves them to `0, ∞` by `PGL₂(k)`).

### XIII.2.13

- **SGA.** Abhyankar's conjecture for the affine line.
- **Lean.** `AbhyankarAffineLineStatement` (`ExposeXIII/SchemeFundamentalGroup.lean`). Raynaud's
  cases `AffineLinePatchingStatement` and `AffineLineCaseBStatement`, and the input
  `SemistableReductionStatement` (`ExposeXIII/AbhyankarAffineLine.lean`).
- **Proved.**
  - Every finite `p`-group is a quotient of `π₁(𝔸¹_k)`, for every `k` of characteristic `p`
    (`exists_surjective_fundamentalGroup_affineLine_of_isPGroup`).
  - For `k` algebraically closed: `S₃` for `p = 2` and `A₄` for `p = 3`
    (`exists_surjective_of_mulEquiv_perm_fin_three`,
    `exists_surjective_of_mulEquiv_alternatingGroup_fin_four`), and every extension of a realized
    group by a `p`-group (Serre, `SerrePKernel.affineLinePExtension`).
  - `AbhyankarAffineLineStatement` follows from Raynaud's cases A and B
    (`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`). Field patching over `k⟦t⟧` is in
    `Foundations/Patching/`.
  - The necessity half (`sylowSup_eq_top_of_affineLine`) and the other assertions of XIII.2.13
    (`not_isTopologicallyFG_fundamentalGroup_affineLine`, `affineLineArtinSchreier`).
- **Missing.**
  - Case A: `AffineLinePatchingStatement` (formal or rigid patching).
  - Case B: `AffineLineCaseBStatement`, which needs XIII.2.12 in characteristic 0 from Riemann
    existence, semistable reduction (`SemistableReductionStatement`), and a degeneration step that
    is not stated.

### XIII §3 (3.1–3.5)

- **SGA.** Generically on the base, morphisms of finite presentation are cohomologically proper
  (3.1, 3.2) and universally locally `1`-aspherical (3.3, 3.4); the specialization maps of
  prime-to-`p` fundamental groups are generically bijective (3.5).
- **Lean.** All in `ExposeXIII/LocalAcyclicity.lean`:
  - `GenericCohomologicalPropernessStatement` (3.1 1) a));
  - `GenericCohomologicalPropernessConstructibleStatement` (3.1 1) b));
  - `FieldCohomologicalPropernessStatement` (3.2 1), proved);
  - `GenericLocalAsphericityStatement` (3.3), `FieldLocalAsphericityStatement` (3.4) and
    `GenericSpecializationStatement` (3.5), all three with SGA's desingularization hypotheses;
  - the inputs `LocalAsphericitySmoothStatement` (SGA 4 XV 2.1) and
    `LocalAcyclicityFlatReducedStatement` (SGA 4 XV 4.1).
- **Proved.**
  - 3.2 1), for every field and every base change (`fieldCohomologicalPropernessStatement`,
    `ExposeXIII/LocalAcyclicityFieldStalks.lean`).
  - 3.3 and 3.4 for étale `f` (`exists_isUniversallyLocallyOneAspherical_of_etale`), and for
    smooth `f` given SGA 4 XV 2.1 (`exists_isUniversallyLocallyOneAspherical_of_smooth`).
  - Over a field, every morphism is locally (not universally) `1`-aspherical
    (`isLocallyOneAspherical_of_field`).
  - The desingularization hypotheses in dimension `≤ 1` over a perfect field
    (`desingularizableUpTo_one`, `stronglyDesingularizableUpTo_one`). So 3.3 and 3.4 for relative
    curves follow from the statements without them.
- **Missing.**
  - SGA 4 XV 2.1 and 4.1 (local acyclicity); proper base change in degree 1.
  - 3.1 2), 3.1.1–3.1.3 and 3.2 2) are not stated: they need cohomological properness in dimension
    `≤ 1` for sheaves of groups and 1-constructibility of stacks, neither of which is defined.

### XIII.4.3, XIII.4.4

- **SGA.** XIII.4.3, and the second and third parts of XIII.4.4: the homotopy exact sequence for
  `f` proper and smooth with a section, and for the complement of a divisor with normal
  crossings.
- **Lean.** `ProperSmoothHomotopyExactSequenceStatement`,
  `NormalCrossingsHomotopyExactSequenceStatement`, `NormalCrossingsShortExactSequenceStatement`
  (`ExposeXIII/ProperHomotopySequence.lean`); `ProperSmoothHomotopyExactSequenceRegularStatement`
  (regular base, `ExposeXIII/ProperSmoothTame.lean`).
- **Proved.**
  - X.3.8 over every locally noetherian base (`tameSpecializationStatement`,
    `ExposeX/TameLiftingGeneral.lean`), from EGA II 7.1.7 and its core
    `TameLiftingDVRStatement` (`tameLiftingDVRStatement`, `ExposeX/TameLiftingProof.lean`).
    Over a complete DVR with separably closed residue field:
    - X.3.8 (`exists_tameSpecialization_of_isDiscreteValuationRing`);
    - X.3.9 (`exists_primeToQuotientEquiv_of_isDiscreteValuationRing`), bijective in residue
      characteristic 0 (`exists_bijective_specialization_of_isDiscreteValuationRing`);
    - the second part of XIII.4.4 without the section
      (`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`).
  - The second part of XIII.4.4 without the section, over a field
    (`properSmoothHomotopyExactSequence_of_field`, `ExposeXIII/ProLShortExact.lean`).
  - These two bases, `Spec k` with `k` a field and `Spec R` with `R` a complete DVR with separably
    closed residue field, are the only cases of
    `ProperSmoothHomotopyExactSequenceRegularStatement` that are proved.
  - Over a complete regular local base, the second part of XIII.4.4 without the section, at the
    closed point only (`isProLShortExact_of_isRegularLocalRing`).
  - X.2.1 for `X` integral and normal
    (`isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`).
- **Missing.**
  - A general base `S` (finiteness for bases that are not geometrically unibranch).
  - The third part, which needs XIII.2.9 and XIII.5.5; SGA proves them with SGA 2 XIV. XIII.5.5
    is stated, existence part only, as `RelativeAbhyankarStatement`
    (`ExposeXIII/RelativeAbhyankar.lean`), the input of
    `TameRamificationAtMaximalPointsStatement` and `TameBaseChangeStatement`.

### XIII.4.6

- **SGA.** The Künneth formula for `π₁`, in characteristic 0.
- **Lean.** `KunnethCharZeroStatement` (`ExposeXIII/SchemeFundamentalGroup.lean`); its case
  `Y = Spec k'`, `InvarianceCharZeroStatement` (`ExposeXIII/KunnethField.lean`);
  `AffineLineOpenInvarianceStatement` (`ExposeXIII/KunnethCurveOpen.lean`), proved as
  `affineLineOpenInvarianceStatement` (`ExposeXIII/KunnethCurveInvariance.lean`).
- **Proved.**
  - The surjectivity half in every characteristic, for `k` algebraically closed and `X`, `Y`
    connected (`surjective_map_prod_of_isAlgClosed`).
  - For `k` algebraically closed of characteristic 0, without resolution of singularities:
    - `π₁(X ×ₖ 𝔸¹) ≅ π₁(X)` for `X` connected, normal, locally of finite type
      (`bijective_map_prod_affineLine_of_isNormalScheme`);
    - XIII.4.6 for `X` connected, normal, locally of finite type and `Y` connected, normal (or
      smooth), quasi-compact, quasi-separated, locally of finite type
      (`bijective_map_prod_of_isNormalScheme_of_isNormalScheme`,
      `bijective_map_prod_of_isNormalScheme_of_smooth`, `ExposeXIII/KunnethTower.lean`; they take
      `AffineLineOpenInvarianceStatement` as a hypothesis, discharged by
      `affineLineOpenInvarianceStatement`, through Kummer coverings, Abhyankar's lemma in
      characteristic 0 and purity).
  - For `X` proper and reduced, `Y` locally noetherian, at a rational point: the `π₁^L` form
    (`bijective_proLMap_prod_of_isProper`) and X.1.7 (`ExposeX.bijective_map_prod`).
- **Missing.** Descent to non-normal `X`, `Y`; the reduction to quasi-compact quasi-separated `X`
  with arbitrary `Y`.

## Other results

Further modules of this directory, by subdirectory. They are imported from `SGA.Foundations` and,
where the statement lives in an exposé, from that exposé's barrel. Declarations named here are
theorems, except the open statements, which are `…Statement` definitions. Paths are relative to
this directory.

- **`Analytic/`.** Runge approximation on compact boxes, the Hartogs extension in dimension `≥ 2`,
  and Dolbeault's lemma on products of open sets in `ℂ`. Oka's coherence theorem, Theorem B on
  `Δ(r) × ℂᵃ × (ℂ*)ᵇ`, and the open `CartanSerreFinitenessStatement` and
  `CoherentTheoremABStatement` are listed under [XII.3.1, XII.4](#xii31-xii4).
- **`CommAlg/`.**
  - EGA II 7.1.7: `IsLocalRing.dominatingDVRStatement` (`CommAlg/DominatingDVRGeneral.lean`).
  - EGA 0_III 10.3.1: `IsLocalRing.flatResidueExtensionStatement`
    (`CommAlg/FlatResidueExtensionGeneral.lean`).
  - Krull–Akizuki for a ring between `A` and a finite extension of `Frac A`:
    `isNoetherianRing_of_finiteDimensional` and `krullDimLE_one_of_finiteDimensional`
    (`CommAlg/KrullAkizukiFinite.lean`).
- **`Limits/`.**
  - EGA IV 8.8.2: `Scheme.spreadingOutStatement` (`Limits/SpreadingOutGluing.lean`).
  - EGA IV 8.10.5 for proper morphisms: `Scheme.properLimitStatement`
    (`Limits/PropertiesLimitProper.lean`).
  - Spreading out to a subfield: `Scheme.spreadingOutSubfieldStatement`
    (`Limits/SpreadingOutSubfield.lean`).
- **`Hodge/`.** The language of `(p, q)`-forms, `∂` and `∂̄`. Open:
  `Hodge.CompactKahlerHodgeSymmetryStatement` and `Hodge.DolbeaultIsomorphismStatement`. Hodge
  symmetry is not proved, so XI.1.4 is proved only from it (see [XI.1.4](#xi14)).
- **`Projective/`.**
  - A smooth proper curve over a field is finite and flat over `ℙ¹`:
    `AlgebraicGeometry.smoothProperCurveFiniteFlatStatement`. `Projective/CurveProjective.lean`
    states it; the proof is in `SGA.SGA1.ExposeIII.CurveLiftCurve`.
  - `Projective/Bertini*` and `Projective/PlaneModel*`: the hyperplane and plane-model steps used
    for X.2.9.
- **`Semistable/`, `Blowup/`.** The numerical types and blow-ups used toward semistable
  reduction. `SemistableReductionStatement` is open (see [XIII.2.13](#xiii213)).
- **`Topology/`.** `Topology/Surface*` is the topology of compact surfaces (presentations,
  Schreier transversals). `BranchedCoveringPresentationStatement`
  (`Topology/SurfaceBranchedCovering.lean`) is open.
