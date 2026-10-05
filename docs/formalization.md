# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1 and SGA 2. It uses
mathlib's definitions and results where they exist and adds what mathlib lacks.

## SGA 1 — *Revêtements étales et groupe fondamental*

Entry points: the barrels `SGA.SGA1.ExposeI` … `SGA.SGA1.ExposeXIII` (there is no Exposé VII)
and `SGA.Foundations`, all imported by `lean/SGA.lean`. Each barrel's module docstring lists its
files and what they prove. The SGA 1 conventions, which follow mathlib naming and differ from
those of the SGA 2 files, are in [`lean/SGA/SGA1/CONVENTIONS.md`](../lean/SGA/SGA1/CONVENTIONS.md).
In short:

- The docstring of a declaration for a numbered item starts with the number
  (`/-- IX.4.12: … -/`) and states how the declaration differs from SGA, if it does (extra
  hypotheses, special cases, one direction).
- A numbered statement that is not proved is recorded as a faithful `Prop`-valued `…Statement`
  definition, and the consequences SGA draws from it are proved with it as a hypothesis.
- There is no `sorry`, `admit`, `native_decide` or custom axiom. From `lean/`,
  `lake env lean CheckSGA1Axioms.lean` checks every declaration of `SGA.SGA1.*` and
  `SGA.Foundations.*` and allows only `propext`, `Classical.choice` and `Quot.sound`.
- Prerequisites that mathlib does not have are in `lean/SGA/Foundations/`, with mathlib
  namespaces and naming and references to EGA, SGA 4 and the Stacks Project. The results that
  are out of scope, and why, are listed in
  [`lean/SGA/Foundations/README.md`](../lean/SGA/Foundations/README.md) (below, "the Foundations
  README").

### Coverage by exposé

The longer subsections group the numbered items, each group in SGA order: proved; partial
(proved only in the cases stated in the item); conditional (proved from an open `…Statement`);
stated, not proved; out of scope, with what is proved (what is missing is in the Foundations
README); not formalized or not stated. What is missing for the in-scope open `…Statement`s is in
[Open statements](#open-statements).

#### I — Étale morphisms

Every numbered statement is proved, with these qualifications:

- I.3.1 is stated with global diagonals.
- I.3.6 (iv) and I.4.7 are proved for base change along one projection only.
- I.10.7–I.10.12 go through EGA IV 15.5.1 and the strict henselization (module
  `GeometricPoints`). I.10.11 adds SGA's standing locally noetherian hypothesis.
- Not stated: I.7.9–I.7.10 (lemmas of the proof of I.7.6), and the scheme forms of
  I.10.3–I.10.6.

#### II — Smooth morphisms

Every recorded statement is proved. II.2.5 (Hironaka's criterion) and the sufficiency half of
II.2.6 need multiplicity theory and are not stated.

#### III — Infinitesimal lifting

**Proved:**

- III.2.1, without completeness.
- III.3.1–III.3.2, at scheme level.
- III.4.
- III.5.1–III.5.4, in Čech form over an affine base.
- III.5.8, for affine formal schemes.
- III.6.7 and III.6.10, when `X₀` is the union of two affine opens.
- III.6.8.
- III.7.4: `smoothProperCurveLiftStatement` proves `SmoothProperCurveLiftStatement`
  (`ExposeIII/CurveLiftCurve.lean`), through a finite flat map to `ℙ¹`
  (`smoothProperCurveFiniteFlatStatement`).

**Not formalized:** III.5.8 for non-affine formal schemes, III.5.9, III.6.3 in general, III.6.9,
III.7.1–III.7.3.

#### IV — Flat morphisms

Every numbered statement is proved.

#### V — The fundamental group: generalities

Every numbered statement is proved, with these restrictions: V.2.2 in ring form (`B`
noetherian); V.5.9 and V.5.11 for small Galois categories; V.8.2 for `Spec R`; V.9 for finitely
many connected components. The second assertion of V.6.12 is false and is not formalized.

#### VI — Fibered categories and descent

Every numbered statement is proved, on mathlib's fibered categories.

#### VIII — Faithfully flat descent

Every numbered statement is proved: VIII.6.4 over a noetherian base, as in SGA, the rest over an
arbitrary base. Ampleness and quasi-projectivity (VIII.5.8, VIII.7.7–VIII.7.8) use
`SGA.Foundations.Projective`.

#### IX — Descent of étale morphisms

**Proved:**

- IX.1.2–IX.1.9, over any base.
- IX.2, over any base.
- IX.2.6, in both directions, with `g` quasi-compact; SGA's finite-type hypothesis is not used.
  The sufficiency half, `UniversallySubmersiveValuativeCriterionStatement`, is proved as
  `universallySubmersiveValuativeCriterion` (`ExposeIX/SubmersiveValuative.lean`), from EGA II
  7.1.7 (`dominatingDVRStatement`) and Krull–Akizuki (`KrullAkizukiFinite.lean`).
- IX.3, over any base.
- IX.4.1–IX.4.11, over any base.
- IX.4.6, in SGA's form: `isEffectiveIffStrictlyLocal` proves
  `IsEffectiveIffStrictlyLocalStatement` (`ExposeIX/StrictlyLocalDescentGeneral.lean`), from
  EGA 0_III 10.3.1 (`flatResidueExtensionStatement`).
- IX.4.9 (`EffectiveDescentOfUniversallyOpenStatement`), unconditionally: its input, the
  existence of quasi-sections (EGA IV 14.5.4, `QuasiSectionStatement`), is proved as
  `quasiSectionStatement` (`ExposeIX/QuasiSection.lean`).
- IX.4.12, over an arbitrary base: `effectiveDescentOfProperStatement` proves
  `EffectiveDescentOfProperStatement` (`ExposeIX/EffectiveDescentGeneral.lean`), from EGA IV
  8.8.2 and 8.10.5 for proper morphisms (`spreadingOutStatement`, `properLimitStatement`).
- IX.6.2, IX.6.4 and IX.6.7.
- IX.6.8 and IX.6.11, over an arbitrary base: `properDescentStatement` and
  `geometricFibresStatement` prove `ProperDescentStatement` and `GeometricFibresStatement`
  (`ExposeIX/ProperDescentGeneral.lean`).
- IX.6.9.

**Partial:**

- IX.1.10 (= X.2.1; `EtaleCoveringsOfClosedFibreStatement`, `CompleteLocalBaseStatement`):
  - for `X` projective over `A` (`isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion`);
  - for `X` integral and normal, as X.2.1
    (`ExposeX.isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`);
  - full faithfulness for every proper `X` (`ExposeIX.full_pullback_closedFibre`,
    `ExposeIX.faithful_pullback_closedFibre`); fullness also over a noetherian henselian local
    base (`ExposeXIII.full_pullback_closedFibre_of_henselianLocalRing`) and faithfulness over any
    local base (`ExposeXIII.faithful_pullback_closedFibre_of_isLocalRing`).
- IX.5.2, for a descent morphism `g` with `S'` and `S''` connected, only in the abstract form of
  Galois categories (`DescentDiagram.DiagonalPoint.exists_finite_topologicalClosure_eq_top`).
- IX.5.2 for schemes, without IX.5.1 and with `S'` and `S''` possibly disconnected, when `S` is
  noetherian and connected and `g` is proper and surjective instead of an effective descent
  morphism (`isTopologicallyFG_etaleFundamentalGroup_of_isProper_of_surjective`).
- IX.5.4 (pinching): only the consequence "`π₁(S')` is topologically finitely generated if
  `π₁(S)` is", under hypotheses that replace SGA's: `g` proper and surjective, `S` locally
  noetherian, `S'` connected, everything over a separably closed field `k`, the points of
  `S' ×_S S'` off the diagonal finitely many and closed, `S' ×_S S' ×_S S'` with finitely many
  connected components, all of these carrying `k`-points
  (`isTopologicallyFG_etaleFundamentalGroup_of_pinching`). These hypotheses hold for a finite
  surjective morphism onto a scheme of finite type over an algebraically closed field that is an
  isomorphism off finitely many closed points
  (`isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict`), for example
  the normalization of a curve
  (`isTopologicallyFG_etaleFundamentalGroup_normalization_of_isTopologicallyFG`).
- IX.5.6, for proper coverings.
- IX.5.8, in its group-theoretic form only.
- IX.6.1 (`ExactSequenceStatement`), with the closed fibre also quasi-separated.

**Stated, not proved:** IX.6.5 (`LocalProperDescentStatement`).

**Not formalized:** IX.5.1 when `S'` or `S''` is not connected; IX.5.3; IX.5.4 apart from the
consequence above; IX.5.5 and IX.5.7 (profinite presentations); IX.6.3; IX.6.6, except for an
étale covering over `Spec 𝒪̂_{S,s}`, a step of the proof of IX.6.7
(`exists_isActAt_fromSpecCompletedStalk`); IX.6.10; IX.6.12.

#### X — Specialization of the fundamental group

**Proved:**

- X.1.1–X.1.5. X.1.2 goes through EGA III 7.8.10, in `SGA.Foundations.Cohomology`.
- X.1.8–X.1.10.
- X.3.1–X.3.4 (Zariski–Nagata purity, in every dimension).
- X.3.6.
- The core of X.3.8, the case to which SGA reduces it in X.3.7: `TameLiftingDVRStatement`,
  proved as `tameLiftingDVRStatement`. Hence, for `f` proper and smooth with geometrically
  connected fibres over the spectrum `Y` of a complete discrete valuation ring with separably
  closed residue field, `y₀` closed and `y₁` generic: X.3.8
  (`exists_tameSpecialization_of_isDiscreteValuationRing`) and X.3.9
  (`exists_primeToQuotientEquiv_of_isDiscreteValuationRing`; an isomorphism in residue
  characteristic 0, `exists_bijective_specialization_of_isDiscreteValuationRing`).
- X.3.8 over every locally noetherian base `Y`, as in SGA, for any specialization `y₁ ⤳ y₀`, in
  the existence form (a homomorphism with SGA's properties exists): `tameSpecializationStatement`
  proves `TameSpecializationStatement` (`ExposeX/TameLiftingGeneral.lean`). The reduction to the
  case above is `tameSpecializationStatement_of_exists_isDiscreteValuationRing`, with EGA II 7.1.7
  in the form `IsLocalRing.exists_isDiscreteValuationRing_dominating`
  (`SGA.Foundations.CommAlg.DominatingDVR`).
- X.3.9 over the same bases, from X.3.8 (`exists_primeToQuotientEquiv_of_tameSpecialization`; an
  isomorphism when `κ(y₀)` has characteristic 0, `exists_bijective_of_tameSpecialization`).

**Partial:**

- X.1.7, for a rational base point and `X` reduced (`bijective_map_prod`).
- X.2.1–X.2.4, for `X` projective over the base. For X.2.4 (`SpecializationSurjectiveStatement`)
  this is `exists_continuous_surjective_specialization_of_isClosedImmersion`.
- X.2.1, also for `X` integral and normal
  (`isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`).
- X.2.2–X.2.3, also over a complete local base.

**Conditional:**

- X.2.1–X.2.4 for `X` proper, from IX.1.10; for X.2.4 this is
  `specializationSurjectiveStatement_of_etaleCoveringsOfClosedFibreStatement`.

**Out of scope**, with what is proved:

- X.2.9 and X.2.12, for every proper connected `X` over an algebraically closed field `k` of
  characteristic 0 with `#k ≤ 𝔠`, in universe 0, without the Riemann existence theorem
  (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`,
  `finite_principalH1_of_mk_le_continuum`).
- X.2.9 in every characteristic follows from the curve case, X.2.6 for normal integral proper
  curves (`topologicallyFiniteStatement_of_curve`), and from the case of plane curves
  (`topologicallyFiniteStatement_of_planeCurve`). The curve case in characteristic `p` is open.
  `topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite` is the reduction to normal
  proper curves and to X.2.10 in an existence form.
- X.2.10, the hyperplane step, in existence form, in every characteristic, for `X` normal,
  integral and proper over an algebraically closed `k`, of dimension `≥ 2`; SGA asks for `X`
  projective, which is not needed (`exists_hyperplane_section`,
  `ExposeX/TopologicallyFiniteBertini.lean`).
- X.2.12 follows from X.2.9 (`finite_principalH1_of_topologicallyFiniteStatement`).

**Not stated:** X.1.6, X.2.5–X.2.8, X.2.10–X.2.11 in SGA's form (the existence form used for
X.2.9 is above), X.2.13–X.2.14, X.3.5, X.3.7, X.3.10–X.3.11.

#### XI — Examples and complements

**Proved:**

- XI.1.1: `ℙʳ` is simply connected, for all `r`.
- XI.1.2 and XI.1.3, in SGA's form (proper normal `X`), from purity X.3.3 and XI.1.1
  (`rationalSimplyConnectedStatement`, `unirationalFiniteFundamentalGroupStatement`).
- XI.2: `π₁` of a proper connected reduced group scheme over an algebraically closed field is
  commutative (`mul_comm_of_monObj`).
- XI.2, before XI.2.1: for an abelian variety `A` over an algebraically closed field, a connected
  étale covering `A' → A` with a marked point over the origin has a unique group law with the
  marked point as origin making it a homomorphism (`existsUnique_grpObj_coveringOver`), and is
  then an isogeny (`isFinite_coveringHom`, `surjective_coveringHom`).
- XI.2.1, key step (Serre–Lang): every connected étale covering of an abelian variety is
  dominated by multiplication by some `n` (`serreLangStatement`), without abelian-variety
  theory.
- XI.4–XI.6: torsors, non-abelian `H¹`, `H¹(S, G) ≅ H¹(π₁, G(s̄))` for finite étale `G`, Kummer
  and Artin–Schreier theory, `Pic`.

**Partial:**

- XI.2, SGA's "every isogeny is a quotient of some `n_A`": for the coverings above, when the
  `n_A` are surjective (`exists_surjective_isMonHom_comp_eq_mulN`), in particular in
  characteristic 0 (`exists_surjective_isMonHom_comp_eq_mulN_of_charZero`).

**Out of scope**, with what is proved:

- XI.1.4 (Serre) is reduced to Hodge symmetry `h^{0,q} = h^{q,0}`
  (`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`); `HodgeSymmetryZeroStatement`
  is open.
- Toward XI.1.4, in every characteristic, for `X` proper and normal over an algebraically closed
  field: unirational curves are simply connected
  (`isSimplyConnected_of_isUnirational_of_trdeg_eq_one`), and `#π₁` divides the separable degree
  of a unirational parametrization (`natCard_etaleFundamentalGroup_dvd_finSepDegree`).
- XI.2.1 (`π₁(A) ≅ lim_n K_n`, the Tate module):
  - in characteristic 0 (`exists_tateModule_equiv_of_charZero`);
  - its `ℓ`-primary clause, for every prime `ℓ ≠ char k`
    (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`);
  - all of it from SGA's cited "`n_A` is an isogeny"
    (`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`, from `MulNIsogenyStatement`).

  In characteristic `p`, XI.2.1 is open and equivalent to its `p`-primary clause
  (`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`).

**Not formalized:** the disconnected principal coverings in XI.2 (`Ext(A, G) ≅ H¹(A, G)`); the
identification of `H¹(S_Zar, GL_n(𝒪_S))` with locally free Modules of rank `n`.

#### XII — Algebraic geometry and analytic geometry

**Proved:**

- XII.1–XII.2.1: affine analytification and local rings.
- XII.2.3, through Rückert's Nullstellensatz (proved in `SGA.Foundations.Analytic`), as is XII.2.2
  in the forms below.
- XII.2.4 and XII.2.6 (connectedness), without GAGA.

**Partial:**

- XII.1.1–XII.1.2, for separated `X` only: the analytic space `X^an` glued from affine charts,
  `φ : X^an → X` and `f^an` (`AnalyticGluing.analyticSpace`, `AnalyticGluing.analyticMap`), with
  underlying space `X(ℂ)` (`AnalyticGluing.pointsHomeomorph`). SGA's universal property of
  `X^an` is proved only for affine `X`.
- XII.2.2: for schemes, `SchemePoints.closureComparison` (for `X : Scheme.{0}`); the affine form,
  `Points.ClosureComparisonStatement`, for `A : Type` only
  (`Points.closureComparisonStatement_zero`).

**§3, on the spaces of points `X(ℂ)`:**

- XII.3.1 (viii) and XII.3.2 (i), (ii), in both directions.
- XII.3.1 (vii), (xi) and XII.3.2 (v), (vi), in one direction (some only for affine schemes),
  with part of the converse of (v).
- XII.3.3 a): étale morphisms give local homeomorphisms.

**§3, for `f^an`**, with `X` and `Y` separated (all in `AnalyticGluing`):

- XII.3.1 (i) (`flat_iff_forall_flat_stalkMap_analyticMap`).
- XII.3.1 (ii) (`formallyUnramified_iff_forall_map_maximalIdeal_analyticMap`).
- XII.3.1 (iii), with "`f^an` étale" read as flat and unramified at every point, not shown to be
  a local isomorphism (`etale_iff_forall_analyticMap`).
- XII.3.1 (iv), with "`f^an` smooth" read as flat with regular fibres
  (`smooth_iff_forall_analyticMap`).
- XII.3.1 (vii), the direct implication (`injective_analyticMap_of_injective`).
- XII.3.1 (ix) and (xi), for `f` quasi-compact (`isIso_iff_isIso_analyticMap`,
  `isOpenImmersion_iff_isOpenImmersion_analyticMap`); the direct implications need no
  quasi-compactness.
- XII.3.2 (i), (ii), for `f` quasi-compact, which SGA's hypothesis that `f` be of finite type
  includes (`surjective_analyticMap_iff`, `denseRange_analyticMap_iff`).
- XII.3.2 (v), the direct implication, topological part (`isProperMap_analyticMap`).
- XII.3.2 (vi), the direct implication, with "finite" read as `AnalyticGeometry.IsFiniteMap`, a
  proper map with finite fibres (`isFiniteMap_analyticMap`).

**Out of scope**, with what is proved:

- The rest of XII.3.1 for `f^an`.
- §4 (GAGA): XII.4.3–XII.4.6 are stated (`ExposeXII/GAGA.lean`), not proved; XII.4.1–XII.4.2 are
  not stated.
- XII.5.1 (Riemann existence) is proved:
  - when `X(ℂ)` is simply connected
    (`isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`);
  - for schemes locally of finite type over `ℂ` of dimension `≤ 1` (`curveRiemannExistence`,
    `schemeCurveRiemannExistence`);
  - for `𝔾_m` (`riemannExistence_laurentPolynomial`);
  - for `ℂ` minus a finite set and its finite étale coverings
    (`PuncturedPlane.riemannExistence_coordRing`, `PuncturedPlane.riemannExistence_finiteEtale`),
    by this project's route, not SGA's: a meromorphic function with a single pole on a compact
    Riemann surface (`AnalyticGeometry.exists_meromorphic_single_pole`).

  For every `X`, `Ψ` is fully faithful (`schemePointsFunctorFullyFaithful`), and the scheme and
  affine forms of XII.5.1 are equivalent (`schemeRiemannExistence_iff`).
- XII.5.2 follows from XII.5.1 alone, for every connected `X`
  (`schemeFundamentalGroupComparison_of_riemannExistence`, with the isomorphism stated as
  `Nonempty`; affine form `fundamentalGroupComparison_of_riemannExistence`), because `X(ℂ)` is
  locally path-connected and semilocally simply connected (`locallyPathConnectedStatement`,
  `semilocallySimplyConnectedStatement`, without triangulation). The surjection
  `π̂₁(X(ℂ)) ↠ π₁(X)` needs no XII.5.1 (`surjective_autWhiskerLeft_schemePointsFunctor`).
- For `ℙ¹_ℂ` minus `n + 1 ≥ 1` points, `π₁` is isomorphic to the profinite completion of a free
  group on `n` generators (`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`;
  an abstract isomorphism, with no generators identified with loops or inertia).

**Not formalized:** XII.1.3.1 (only the functor `F ↦ F^an` is defined,
`AnalyticGluing.analytification`); XII.2.5; `X^an` for non-separated `X`; the uniqueness of
`f^an`; fibre products of analytic spaces (XII.1.2 is compared on points only); XII.3.2 (iii),
(iv) and the converses of (v), (vi) for `f^an`; XII.5.3–XII.5.5 (normal analytic spaces).

#### XIII — Cohomological properness

**Defined:** in §1, 1.1–1.2, 1.5 a) and c), 1.6 and 1.13 1). For sheaves of groups, 1.3.1 (ii)
is the definition, since stacks of torsors and their inverse images are not available.

**Proved:**

- SGA 4 VIII 5.2 (degree 0), 5.5 and 5.8.
- 2.0–2.0.3 and 2.1.1 (locally constant sheaves).
- 3.2 1), for every field (`fieldCohomologicalPropernessStatement`).
- 4.0.
- 4.4, first part, at all geometric points.
- 4.5.
- 5.1, 5.3 and 5.4.

**Partial:**

- SGA 4 VIII 5.6 (`IntegralBaseChangeStatement`, used in 1.9): for finite morphisms
  (`isCohomologicallyProperLEZero_of_isFinite`), and in dimension `≤ -1` for every integral `f`
  (`isCohomologicallyProperLENegOne_of_universallyClosed`). The limit theorems it uses are proved
  in degree 0: SGA 4 VII 5.7, surjectivity (`Scheme.exists_toLimitSections_eq`), and VIII 5.2
  (`Scheme.pushforwardStalkStrictLocalizationStatement`).
- 1.4 in dimension `≤ -1`, for every universally closed `f`, for sheaves of sets
  (`isCohomologicallyProperLENegOne_of_universallyClosed`) and of groups
  (`isCohomologicallyProperLENegOneGroup_of_universallyClosed`); hence 1.8 for sheaves of sets
  and 1.9, in dimension `≤ -1`.
- 1.7 for sheaves of groups, in dimension `≤ -1`
  (`IsCohomologicallyProperLENegOneGroup.pushforward`).
- 1.9 for sheaves of sets in dimension `≤ 0`, for finite morphisms
  (`isCohomologicallyProperLEZero_pushforward_iff_of_isFinite`).
- 2.3 b), for Galois coverings of degree prime to `p` of an open `U` with finite complement in a
  proper smooth connected curve over a separably closed field (`galoisCoveringsTameStatement`).
- 4.7–4.8: the group theory, without closures.
- 5.2 (`AbsoluteAbhyankarStatement`), except in mixed characteristic over a ring that is not
  strictly henselian: the existence of the extension for every regular local ring, and the
  statement in equal characteristic and in dimension 1.

**Conditional:**

- 1.9 for sheaves of sets in dimension `≤ 0`, for integral morphisms, given
  `IntegralBaseChangeStatement` (`isCohomologicallyProperLEZero_pushforward_iff`).

**Stated, not proved:**

- 2.3 a) and 2.4 1), for sheaves of sets (`TameRamificationAtMaximalPointsStatement`,
  `TameBaseChangeStatement`).
- 5.5, existence part (`RelativeAbhyankarStatement`).

**Out of scope**, with what is proved:

- 1.4 for sheaves of sets over an arbitrary base. Over a locally noetherian base it is proved
  (`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`, through Gabber's theorem),
  hence 1.8 for sheaves of sets in dimension `≤ 0` over such a base
  (`IsCohomologicallyProperLEZero.comp_of_isProper_of_isLocallyNoetherian`).
- 2.12: its "in other words" form on `ℙ¹` over an algebraically closed `k`, with the inertia
  conditions, for `(g, n) = (0, 0)`, `(0, 1)` at the point `∞` and `(0, 2)` at the points
  `0, ∞`, without Riemann existence (`tameCurvePrimeToPConclusion_projectiveLine_zero`,
  `tameCurvePrimeToPConclusion_projectiveLine_one`,
  `tameCurvePrimeToPConclusion_projectiveLine_two`). 2.12 implies that form
  (`tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement'`).
- 2.13:
  - the Artin–Schreier description of `Hom(π₁(𝔸¹_k), ℤ/p)` (`affineLineArtinSchreier`);
  - `π₁(𝔸¹_k)` is not topologically finitely generated
    (`not_isTopologicallyFG_fundamentalGroup_affineLine`);
  - the necessary condition of Abhyankar's conjecture (`sylowSup_eq_top_of_affineLine`);
  - for the sufficiency: `p`-groups (`exists_surjective_fundamentalGroup_affineLine_of_isPGroup`),
    `S₃` for `p = 2` and `A₄` for `p = 3` (`exists_surjective_of_mulEquiv_perm_fin_three`,
    `exists_surjective_of_mulEquiv_alternatingGroup_fin_four`), and Serre's theorem on `p`-group
    kernels (`SerrePKernel.affineLinePExtension`), with which the conjecture is reduced to
    Raynaud's cases A and B (`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`).
- §3, apart from 3.2 1). 3.1 1), 3.3, 3.4 and 3.5 are stated.
  - 3.3 and 3.4 for étale `f` (`exists_isUniversallyLocallyOneAspherical_of_etale`), and for
    smooth `f` given SGA 4 XV 2.1 (`exists_isUniversallyLocallyOneAspherical_of_smooth`).
  - Over a field, every morphism is locally, not universally, `1`-aspherical
    (`isLocallyOneAspherical_of_field`).
  - The desingularization hypotheses hold for integral schemes of dimension `≤ 1` of finite type
    over a perfect field (`desingularizableUpTo_one`, `stronglyDesingularizableUpTo_one`).
- 4.4, second and third parts. The second part, without the section, is proved over a field
  (`properSmoothHomotopyExactSequence_of_field`), at the closed point of a complete regular local
  base (`isProLShortExact_of_isRegularLocalRing`), and over a complete discrete valuation ring
  with separably closed residue field
  (`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`).
- 4.6:
  - for `π₁^L`, with `X` proper and reduced (`bijective_proLMap_prod_of_isProper`);
  - with `k` algebraically closed (SGA: separably closed) and `X`, `Y` connected, the
    surjectivity half, in every characteristic (`surjective_map_prod_of_isAlgClosed`);
  - with `k` algebraically closed (SGA: separably closed), in characteristic 0 and without
    resolution of singularities, `π₁(X ×ₖ 𝔸¹) ≅ π₁(X)` for `X` connected, normal and locally of
    finite type (`bijective_map_prod_affineLine_of_isNormalScheme`);
  - for `k` algebraically closed of characteristic 0, without resolution of singularities, 4.6
    for `X` connected, normal, locally of finite type and `Y` connected, normal (or smooth),
    quasi-compact, quasi-separated, locally of finite type
    (`bijective_map_prod_of_isNormalScheme_of_isNormalScheme`,
    `bijective_map_prod_of_isNormalScheme_of_smooth`, with `affineLineOpenInvarianceStatement`,
    `ExposeXIII/KunnethCurveInvariance.lean`).

**Not formalized:**

- For sheaves of groups: 1.8; 1.4 in dimension `≤ 0` (neither proved nor stated); 1.7 and 1.9 in
  dimension `≤ 0`; dimension `≤ 1`; 2.4 1).
- The equivalences of 1.3.1, 1.5 b), 1.13 2)–3) and 1.10–1.17 apart from 1.13 1) (see the module
  docstring of `ExposeXIII/CohomologicalProperness.lean`).
- 2.3 b) beyond the Galois coverings of curves above.
- The items of §2 on sheaves of groups and stacks (2.1.3–2.1.6, 2.2, 2.5–2.9), 2.4 2) and 2.11.
- 3.1.1–3.1.3, 3.1 2) and 3.2 2).
- 4.3 as stated (its hypotheses are not defined).
- The uniqueness in 5.5, and 5.6–5.7.
- Appendix II (6.1–6.3).

### Open statements

The in-scope `…Statement` definitions that are not proved, or proved only in the cases
indicated. The out-of-scope ones are in the Foundations README. Numbered items that are neither
proved nor stated have no `…Statement`; the exposé subsections list them as not formalized or not
stated.

| Statement | Item | Proved | Missing |
| --- | --- | --- | --- |
| `GrothendieckExistenceStatement` (Foundations) | EGA III 5.1.4 | Full faithfulness for proper `X`; essential surjectivity for finite étale coverings of projective `X`, and its Chow/Stein descent step | Essential surjectivity for proper `X` (gluing along the conductor, noetherian induction) |
| `EtaleCoveringsOfClosedFibreStatement`, `CompleteLocalBaseStatement` | IX.1.10 = X.2.1 | `X` projective over `A`; `X` integral and normal; full faithfulness for every proper `X` (see IX) | Essential surjectivity for proper `X` that is neither projective nor integral and normal (the existence theorem for proper morphisms) |
| `ExactSequenceStatement` | IX.6.1 | Closed fibre quasi-compact and quasi-separated | A fibre that is not quasi-separated: nothing is known (the Stacks Project also assumes quasi-separatedness) |
| `LocalProperDescentStatement` | IX.6.5 | — | Stein factorization and its compatibility with completion |
| `SpecializationSurjectiveStatement` | X.2.4 | `X` projective over `Y`; every proper `X`, given IX.1.10 (see X) | IX.1.10 for proper `X` |
| `Points.ClosureComparisonStatement` | XII.2.2, affine form | `A : Type`; the scheme form for `X : Scheme.{0}` (see XII) | Universes above 0 |
| `IntegralBaseChangeStatement` | SGA 4 VIII 5.6 (used in XIII 1.9) | Finite morphisms; dimension `≤ -1` for every integral `f`; the limit theorems it uses, in degree 0 (see XIII) | Gabber's theorem for `B` integral over a strictly henselian local ring `A`: restriction of sections from `Spec B` to `Spec (B/𝔪_A B)` is bijective |
| `TameRamificationAtMaximalPointsStatement`, `TameBaseChangeStatement` | XIII.2.3 a), XIII.2.4 1) (sheaves of sets) | — | The relative Abhyankar lemma XIII.5.5 (`RelativeAbhyankarStatement`) |
| `AbsoluteAbhyankarStatement` | XIII.5.2 | Existence of the extension for every regular local ring; the statement in equal characteristic and in dimension 1 | The exponents are prime to `p` in mixed characteristic over a ring that is not strictly henselian |
| `RelativeAbhyankarStatement` | XIII.5.5, existence part (the uniqueness is not stated) | — | SGA 2 XIV 1.20 (étale depth), to reduce to the maximal points of `Y'₁`, where X.3.6 applies; the descent showing that the `nᵢ` are prime to `p` |

### Corrections to SGA 1

The exposé READMEs under `translation/SGA1/` record, in a table "Found during the Lean
formalization", the points where SGA 1 is wrong or needs an extra hypothesis, with the Lean
declaration that proves or records the corrected form. They concern I.9.8, I.10.7 and I.10.9,
V.6.8, V.6.11, V.6.12, the remarks after VI.6.1, VI.9, X.1.10, and the proof of XIII.1.3.1
(recorded in the definition `IsCohomologicallyProperLEZeroGroup`). The same READMEs list misprints
found by the translators (for example IX.2.5, `S'' → S`).

### Foundations

`SGA.Foundations` (`lean/SGA/Foundations/`, about 600 files) contains what SGA 1 needs and
mathlib lacks. The module docstring of `SGA/Foundations.lean` lists the areas:

- EGA II: quasi-affine, ample and quasi-projective morphisms, relative `Proj`, norms and Chow's
  lemma.
- Commutative algebra: regular local rings, Auslander–Buchsbaum, factoriality and Zariski–Nagata
  purity; dimension theory; E. Noether's finiteness of integral closure
  (`Algebra.FiniteType.finite_integralClosure`) and the finite normalization of an integral scheme
  of finite type over a perfect field (`isFinite_fromNormalization_fromSpecStalk_genericPoint`).
- Smooth morphisms: generic smoothness over a perfect field; smooth morphisms are geometrically
  reduced.
- Henselization, strict henselization, strict localization and étale stalks (EGA IV 18).
- Limits of schemes and of finite étale coverings: EGA IV 8 and 15.5.1.
- Cohomology: Čech and derived cohomology of quasi-coherent sheaves, and the EGA III theorems
  (Serre vanishing, finiteness, formal functions, Zariski connectedness, Stein factorization, flat
  base change, Grothendieck existence).
- Euler characteristic (`Cohomology/EulerCharacteristic*`): `hᵖ` and `χ` of coherent modules on
  proper schemes over a field; `χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)` for `X` proper over a field and
  `Y → X` finite étale of degree `d`, in every characteristic, by dévissage and without
  Riemann–Roch (`eulerCharFiniteEtaleStatement`); on an integral noetherian scheme, an additive
  function of coherent modules that vanishes on modules supported in proper closed subsets is
  determined by the generic rank (`exists_additive_eq_mul_unitModule`).
- Formal schemes.
- Étale sheaves, torsors and non-abelian `H¹`.
- Gabber's theorem and proper base change in degree 0 (`Etale/Gabber*`, `Limits/EtaleSections*`,
  `EtaleStalkProper*`):
  - Gabber's theorem for proper schemes over a noetherian henselian local ring (Stacks 0A3S,
    `properHenselianSectionsStatement`);
  - SGA 4 VII 5.7 (surjectivity) in degree 0, for inverse images over a cofiltered limit of
    quasi-compact quasi-separated schemes with affine transition maps
    (`Scheme.exists_toLimitSections_eq`), and VIII 5.2 in degree 0
    (`Scheme.pushforwardStalkStrictLocalizationStatement`);
  - the base change morphism of a universally closed morphism is injective on stalks
    (`injective_sheafFiber_etaleBaseChangeMap_of_universallyClosed`);
  - an étale morphism with finite fibres and one geometric point in each fibre is an isomorphism
    (`isIso_of_forall_geometricFiberCard_eq_one`);
  - for a proper scheme over a noetherian henselian local ring, every clopen subset of the closed
    fibre is the trace of a clopen subset
    (`exists_isClopen_preimage_closedFibre_of_henselianLocalRing`).
- Local acyclicity (`Etale/LocalAcyclicity*`): locally acyclic morphisms through Milnor fibres
  (SGA 4 XV 1.11), the base change form of Stacks 0A3H and 0EZX, base change morphisms on stalks
  through strict localizations; a connected scheme integral over a strictly henselian local ring
  is simply connected (`isIso_of_isFinite_of_etale_of_isIntegralHom`).
- Pro-objects; the profinite completion of a finitely generated group is topologically finitely
  generated (`ProfiniteGrp.ProfiniteCompletion.exists_finset_dense_closure`).
- Embeddings into `ℂ` of fields of characteristic 0 with `#k ≤ 𝔠`
  (`Complex.nonempty_ringHom_of_mk_le_continuum`).
- Group schemes (`GroupScheme/`): multiplication by `n` acts as `n` on the cotangent space at the
  origin of a monoid scheme over a field, so it is injective on the local ring there when the
  scheme is locally noetherian and `n` is invertible
  (`AlgebraicGeometry.GroupScheme.injective_stalkEnd_pow`); points with values in local rings.
- Topology (`Topology/`):
  - topological coverings;
  - `π₁` of a compact, R₁, path-connected, locally path-connected and semilocally simply
    connected space is finitely generated (`FundamentalGroup.fg_of_compactSpace`);
  - van Kampen for any open cover (groupoid and group forms, and a presentation);
  - `π₁` of finite products, and products of covering maps;
  - connected finite coverings of punctured discs are Kummer coverings
    (`Complex.exists_homeomorph_powRestrict_of_connectedSpace`), and those of `(Δ*)ᵖ × Δ^q` are
    quotients of multi-Kummer coverings (`Complex.exists_subgroup_continuousMap_multiPowRestrict`);
  - `π₁(C ∖ S)` is free on loops around the points of `S`, for `C ⊆ ℂ` open and convex and `S`
    finite (`Complex.exists_freeGroupBasis_fundamentalGroup_diff`);
  - path lifting for proper maps with finite fibres that are coverings over a subset
    (`IsCoveringMapOn.exists_path_lift`, `Topology/CoveringMapOn.lean`);
  - monodromy is transitive on path-connected finite coverings
    (`TopCat.FiniteCovering.exists_monodromy_eq`).
- Semialgebraic geometry (`Semialgebraic/`): Tarski–Seidenberg, the monotonicity theorem,
  semialgebraic choice for compact fibres, a Kurdyka–Łojasiewicz inequality and a
  gradient-descent retraction, so that real algebraic sets are locally contractible, locally
  path-connected and semilocally simply connected
  (`MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero`,
  `MvPolynomial.semilocallySimplyConnectedSpace_setOf_eval_eq_zero`).
- Analytic geometry and Riemann surfaces (`Analytic/`):
  - convergent power series, Rückert's Nullstellensatz and analytification;
  - sheaves of modules on locally ringed spaces with pullback, pushforward and the maps
    `Hⁿ(Y, M) → Hⁿ(X, f^*M)`;
  - finite and étale morphisms of analytic spaces; the localizations used to glue `X^an`;
  - Oka's coherence theorem, germ form (`AnalyticGeometry.okaCoherence`), and Theorem B for `𝒪`
    on `Δ × ℂᵃ × (ℂ*)ᵇ` (`AnalyticGeometry.polydiscProductVanishing`), both stated in
    `Analytic/Statements.lean`;
  - Dolbeault's lemma and the first Cousin problem on a disc
    (`AnalyticGeometry.exists_contDiffOn_dbar_eq_ball`,
    `AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`);
  - L. Schwartz's theorem on compact perturbations; Montel's theorem;
  - on a compact Riemann surface, every point is the only pole of some meromorphic function
    (`AnalyticGeometry.exists_meromorphic_single_pole`, Forster 14.13);
  - the compact Riemann surface obtained by filling in the punctures of a finite covering of
    `ℂ ∖ S`.
- Field patching (`Patching/`): Cartan factorization and patching of free modules and of Galois
  algebras, on `ℙ¹` over `k⟦t⟧` and on a double cover of that configuration modelled on
  Harbater–Stevenson's node (the identification with their nodal model is not formalized).

### Mathlib correspondences

SGA works with locally noetherian schemes after no. I.2 and defines étale as flat + unramified of
finite type. Mathlib's `Etale` is formally étale of finite presentation. On a locally noetherian
base these agree (`etale_of_flat_unramified_locallyNoetherian`). Universally injective is SGA's
radicial.

| SGA 1 I | Mathlib |
| --- | --- |
| I.1 `Ω¹_{X/Y}` | `Ω[S⁄R]`, `FormallyUnramified` |
| I.2 quasi-finite | `Algebra.QuasiFinite`, `LocallyQuasiFinite`, `QuasiFiniteAt` |
| I.3 net / unramified | `FormallyUnramified`, `Algebra.Unramified` |
| I.3.1 residue / `mS = n` | `FormallyUnramified.iff_map_maximalIdeal_eq` |
| I.3.4 graph | `pullback_lift_diagonal_isPullback` |
| I.4 étale | `Etale`, `Algebra.Etale` |
| I.4.9 covering | `IsFinite` + `Etale`, `CommAlgCat.FiniteEtale` |
| I.5.1 étale + radicial | `IsOpenImmersion.of_flat_of_mono` |
| I.5.5 uniqueness | `FormallyUnramified.hom_ext` |
| I.7 standard étale | `StandardEtalePair`, `IsStandardEtale` |
| I.7.6–I.7.8 | `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, `IsEtaleAt.exists_isStandardEtale` |
| I.9.5 integral closure | `TensorProduct.toIntegralClosure_bijective_of_smooth` |
| I.10 normalization | `Scheme.Hom.toNormalization` |

| SGA 1 V, VI | Mathlib |
| --- | --- |
| V.4–V.5 Galois categories | `PreGaloisCategory`, `GaloisCategory`, `FiberFunctor` |
| VI.2 category over another | `BasedCategory`, `BasedFunctor`, `BasedNatTrans` |
| VI.4 fiber-category | `CategoryTheory.Functor.Fiber`, `HasFibers` |
| VI.5.1 cartesian morphism | `Functor.IsCartesian` |
| strongly cartesian | `Functor.IsStronglyCartesian` (Stacks 02XK) |
| VI.6.1 prefibered / fibered | `Functor.IsPreFibered`, `Functor.IsFibered` |
| VI.8 cloven / Grothendieck construction | `∫ᶜ`, `Pseudofunctor.CoGrothendieck.forget` |
| VI.9 split (1-functor) | `Functor.toPseudofunctor'` then `∫ᶜ` |
| VI.10 cocartesian | `Functor.IsCocartesian` |
| descent data, (pre)stack | `Pseudofunctor.DescentData`, `IsPrestack`, `IsStack` |

## SGA 2, Exposé I — Local cohomological invariants

Entry point: `lean/SGA/SGA2/ExposeI.lean`. Source: `translation/SGA2/ExposeI/`. Files below are in
`lean/SGA/SGA2/ExposeI/` unless prefixed `ExposeIII/`.

Coefficients are abelian sheaves on a topological space `X`. A closed support is `Z : Closeds X`; a
locally closed one is a witness `W : LocallyClosedIn X` (an open `V` and a closed subset of `V`);
support objects, section functors and their derived functors do not depend on the witness (I.2.2,
I.2.4). SGA's `H_Z^n` is `derivedGammaZSections`, the right derived functors of `Γ_Z`; the Ext model of
I.2.3 bis is `H_Z Z F n := Ext(ℤ_{Z,X}, F, n)` (`H_locallyClosed` for a witness), and
`derivedGammaZSectionsIsoH_Z` identifies the two. SGA's `ℋ_Z^n` is `derivedUnderlineGammaZ`, the derived
functors of `Γ̲_Z = ker(F → j_* j^* F)` (`underlineGammaZ`); I.2.11 compares it with the model
`sheafH_Z_n` (kernel, cokernel, `R^{n-1} j_*`). Mathlib supplies flasque sheaves, pushforward and
pullback, `Ext`, `Functor.rightDerived`, spectral objects and algebraic local cohomology.

### Proved

`F_U` is the restriction of `F` to an open `U`; `Z′` is closed in a locally closed `Z`, `Z″ = Z ∖ Z′`.

| SGA 2 I | Lean | Content |
| --- | --- | --- |
| I.1 (2), (8) | `gammaZ`, `gammaZSections` (`GammaZ.lean`); `underlineGammaZ` (`UnderlineGammaZ.lean`); `underlineGammaZSectionsEquiv`, `underlineGammaZPresheafFunctorIso` (`SupportedSheafSections.lean`) | closed `Z`; `Γ(U, Γ̲_Z F) = Γ_{Z∩U}(F_U)`, natural in `F` and `U`; `Γ̲_Z` additive, left exact |
| I.1 (3)–(4) | `LocallyClosedIn`, `LocallyClosedIn.gamma`, `gammaZSections_restrict_addEquiv` (`LocallyClosed.lean`); `LocallyClosedIn.ofClosed` (`ClosedAsLocallyClosed.lean`) | locally closed `Z`, independent of the open; closed `Z` as a witness |
| I.1 (6), (9) | `zZX_closed`, `underlineGamma_locallyClosed` (`ExtensionByZero.lean`) | closed `i_! = i_*`, open `i^! = i^*`; closed `ℤ_{Z,X}`; `Γ̲_Z` on the open of a witness |
| I.1.3–I.1.4 | `iBang_open`, `openExtensionByZeroAdjunction`, `restrictToOpen_injective` (`OpenExtensionByZero.lean`); `closedSupportAdjunction`, `locallyClosedSupportAdjunction`, `closedSupportPushforwardIso`, `closedSupportPullbackIso` (`ClosedSupportAdjunction.lean`) | `i_! ⊣ i^!` for open, closed, locally closed `Z`; `i_!` exact (closed: fully faithful); `i^!` preserves injectives; `i_* i^! ≅ Γ̲_Z` with counit the inclusion; `i^! ≅ i^* Γ̲_Z` |
| I.1 (13) | `LocallyClosedComposition.lean` | nested locally closed immersions: `(ij)_! = i_! j_!`, `(ij)^! = j^! i^!`, via a homeomorphism of support spaces, compatible with units and counits |
| I.1 (17) | `locallyClosedSingleExtensionSequence_shortExact`, `locallyClosedSingleExtensionSequenceFunctorIso` (`OpenExtensionCounit.lean`, `OpenClosedExtensionSequence.lean`, `LocallyClosedExtensionEndpoints.lean`) | short exact for every `G` on `Z`, natural in `G`; arrows the open counit (monic) and the closed unit (its cokernel); the ends are extensions along single witnesses for `Z″`, `Z′` |
| I.1.6, I.2.3 bis, inputs | `abelianSheafHom` (`InternalHom.lean`); `internalHomSectionsRestrictEquiv` (`TopologicalInternalHom.lean`); `internalSheafExtSheafificationIso` (`SheafExtLocalComparison.lean`); `abelianSheafHomPrecomp`, `internalSheafExtPrecomp` (`InternalHomPrecomposition.lean`, `InternalHomBifunctor.lean`); `localExtRestriction`, `internalExtPresheafSectionsEquiv_restrict` (`SheafExtRestriction.lean`); `localExtδ`, `restrictToOpen_map_shortExact` (`SheafExtConnecting.lean`) | `ℋom`, left exact, and sheaf Ext; `Γ(U, ℋom(F, G)) = Hom(F_U, G_U)`; sheaf Ext is sheafified local Ext, naturally; first-variable maps; restriction and connecting maps of local Ext |
| I.1.6 | `closedSupportHomEquiv` (`ClosedSupportHom.lean`); `closedSupportInternalHomFunctorIso` (`ClosedSupportInternalHom.lean`); `locallyClosedSupportInternalHomFunctorIso` (`InternalHomIntersection.lean`, `LocallyClosedSupportInternalHom.lean`); `openSupportHomEquiv` (`OpenSupportCohomology.lean`) | `Γ_Z = Hom(ℤ_{Z,X}, −)`, `Γ̲_Z = ℋom(ℤ_{Z,X}, −)`, natural; locally closed `Z`: the `ℋom` form, natural also in the open (`Hom` form: I.2.1); open `U`: `Hom(ℤ_{U,X}, F) = F(U)` |
| — | `closedSupportRestrictionIso` (`ClosedSupportRestriction.lean`) | `ℤ_{Z,X}` restricted to an open `U` is `ℤ_{Z∩U,U}`, compatibly with its integer presentation |
| I.1.7 | `ringedSpaceSupportHomEquiv` (`RingedSpaceSupportHom.lean`) | Modules, closed `Z`: `Hom(𝒪_X, Γ̲_Z F) = Γ_Z(F)` |
| I.1.8 | `exact_gammaZ_of_le`, `I_1_8_package` (`ExactSequences.lean`, `Flasque.lean`); `locallyClosedNestedGammaSequence_exact_and_mono`, `locallyClosedNestedGammaSequence_shortExact` (`LocallyClosedNestedGamma.lean`) | left exact, short exact for flasque `F`: closed `Z′ ⊆ Z` (first two names); locally closed `Z`, naturally (last two) |
| I.1.9 | `locallyClosedNestedSheafSequence_exact`, `locallyClosedNestedSheafInclusion_mono`, `locallyClosedNestedSheafSequence_shortExact` (`NestedSupportedPresheafSequence.lean`, `NestedSupportedSheafSequence.lean`, `LocallyClosedNestedSheafSequence.lean`) | the same for `Γ̲`; the maps are inclusion and restriction of sections |
| I.1.10 | `constantSupportSequence_shortExact` (`ConstantSupportSequence.lean`, `ConstantSupportSequenceCompatibility.lean`); `locallyClosedNestedObjectSequence_shortExact`, `nestedClosedSubspaceObjectSequence_shortExact` (`NestedSupportObjects.lean`, `NestedSupportLocallyClosed.lean`, `NestedSupportSubspace.lean`) | `0 → ℤ_{X∖Z,X} → ℤ_X → ℤ_{Z,X} → 0`, first map from the adjunction; `0 → ℤ_{Z″,X} → ℤ_{Z,X} → ℤ_{Z′,X} → 0` for any closed `Z′` of the subspace `Z` |
| | `nestedSupportObjectRestriction_internalHom`, `nestedSupportObjectInclusion_internalHom`, `nestedSupportInternalHomSequenceIso` (`NestedSupportInternalHom.lean`) | `Z` open ∩ closed: `ℋom(−, F)` of that sequence is the I.1.9 sequence, as short complexes; `Hom(−, F)`: I.2.8 |
| I.2.1, I.2.3 bis | `H_Z` (`DerivedFunctors.lean`); `derivedGammaZSections` (`DerivedSupportedSections.lean`); `derivedGammaZSectionsIsoH_Z` (`SupportedCohomologyComparison.lean`) | closed `Z`: the two `H_Z^n` agree naturally in every degree; `Γ_Z` left exact, `R^0 Γ_Z = Γ_Z` naturally |
| | `zZX_locallyClosed`, `H_locallyClosed`, `derivedGammaLocallyClosedIsoExt`, `locallyClosedSupportExtEquiv` (`LocallyClosedCohomology.lean`) | locally closed `Z`: the same, `ℤ_{Z,X}` a composite extension by zero; equal to closed-support cohomology on the witness's open |
| | `localCohomology` (`LocalCohomology.lean`); `ModuleCat.exists_isRegular_tfae` | algebraic `H_J^i(M)` (mathlib); Rees depth criterion for Exposé III |
| I.2.2 | `I_2_2_degree_zero`, `I_2_2_excision_degree_zero`; `supportedExcisionEquiv`, `closedSupportExcisionIso` (`SupportedExcision.lean`) | closed `Z ⊆ V`: `H_Z(X, F) = H_Z(V, F_V)` in every degree, natural; `j_! ℤ_{Z,V} ≅ ℤ_{Z,X}` |
| | `locallyClosedSupportIsoOfSameSet`, `derivedGammaLocallyClosedIndependenceIso`, `locallyClosedCohomologyEquivOfSameSet` (`LocallyClosedIndependence.lean`) | locally closed `Z`: `ℤ_{Z,X}`, `R^n Γ_Z` and Ext independent of the witness, natural |
| I.2.3 | `openSupportExtEquiv` | open `U`: `Ext^n(ℤ_{U,X}, F) = H^n(U, F_U)`, natural, compatible with connecting maps |
| I.2.3 bis (21 bis) | `closedSupportInternalSheafExtIso`, `closedSupportInternalSheafExtIsoModel`, `locallyClosedSupportInternalSheafExtIso` | `ℋ_Z^n` is sheaf Ext from `ℤ_{Z,X}`, closed and locally closed `Z`; also `sheafH_Z_n` |
| I.2.4 | `supportedCohomologySheafificationIso`, `supportedCohomologyPresheafSectionsEquiv` (`DerivedSupportedSheaves.lean`); `sheafH_Z_nSheafificationIso`; `underlineGammaLocallyClosedFunctor`, `locallyClosedCohomologySheafificationIso`, `derivedUnderlineGammaLocallyClosedIndependenceIso` (`LocallyClosedSupportedSheaves.lean`, `OpenSupportedSections.lean`) | `ℋ_Z^n` is the sheafification of `U ↦ H^n_{Z∩U}(U, F_U)`, natural, also for `sheafH_Z_n`; locally closed `Z`: ambient `Γ̲_Z`, its derived functors, the same formula, witness independence |
| I.2.5 | `derivedUnderlineGammaOfOpenIso` (`OpenDerivedSupportedSheaves.lean`) | open `U`: `ℋ_U^n = R^n i_*(F_U)`, natural; exactness of `i_*` not assumed |

**I.2.6**, for closed `Z` and an injective resolution `I` of `F`:

- `supportedTruncationSpectralSequence` (`LocalToGlobalSpectralObject.lean`,
  `LocalToGlobalSpectralSequence.lean`): canonical truncations of `Γ̲_Z I` under derived Hom from
  `ℤ_X`; all pages, differentials and next-page isomorphisms. Inputs: `Γ̲_Z` preserves injectives
  (`SupportedSheafInjective.lean`); `Γ(X, Γ̲_Z I)` computes `H_Z` (`LocalToGlobalResolution.lean`).
- `supportedTruncationSpectralSequenceE2Equiv` (`LocalToGlobalE2.lean`): `E₂^{p,q} ≅ H^p(X, ℋ_Z^q F)`;
  the pages live in `AddCommGrpCat.{u+1}` and the isomorphism crosses universes.
  `supportedLocalToGlobalAbelianSpectralObject_isFirstQuadrant` (`LocalToGlobalFirstQuadrant.lean`):
  every `E_r`, `r ≥ 2`, vanishes outside the first quadrant.
- `supportedSpectralObjectTotalEquivH_Z` (`LocalToGlobalTotalCohomology.lean`): the total groups are
  `H_Z`, by K-injectivity. `supportedCohomologyFiniteFiltration`,
  `supportedLocalToGlobalStablePageIsoGraded` (`LocalToGlobalConvergence.lean`): a finite image
  filtration of `H^n_Z` from 0 to the whole group, with graded pieces `E_r^{n−q,q}` for `r ≥ n + 2`.
- Functoriality in `F`
  (`LocalToGlobal{SpectralFunctoriality,PageMaps,E2Naturality,TotalNaturality,ConvergenceNaturality}.lean`):
  `supportedAbelianSpectralObjectMap` preserves connecting maps; `supportedTruncationSpectralSequenceMap`,
  `_d`, `_next` commute with differentials and next-page isomorphisms and are determined by the first
  page (`spectralSequence_hom_ext_firstPage`); the E₂, total (with `H_Z_map`), stable-page and
  filtration comparisons are natural (`supportedTruncationSpectralSequenceE2Equiv_naturality`,
  `supportedSpectralObjectTotalEquivH_Z_naturality`,
  `supportedLocalToGlobalStablePageIsoGraded_coefficient_naturality`,
  `H_Z_map_mem_supportedCohomologyFiltration`).
- `supportedTruncationSpectralSequenceFunctor` (`LocalToGlobalCoefficientFunctor.lean`) is a functor:
  these maps, and the total, filtration and graded maps, do not depend on the lift to resolutions;
  a change of resolution gives natural isomorphisms with the cocycle identity; the filtration on
  `H_Z` does not depend on the resolution (`supportedCohomologyFiltrationOnH_Z_independent`).
- Locally closed `Z`: all of the above for the ambient functor, with cohomology on `X` and abutment
  `H_locallyClosed`, as `locallyClosedTruncationSpectralSequence` and companions
  (`LocallyClosedLocalToGlobal{Resolution,SpectralSequence,Convergence,Maps,CoefficientFunctor,E2Naturality,TotalNaturality,ConvergenceNaturality}.lean`).
  Open `Z` is the witness `LocallyClosedIn.ofOpen`.
- `grothendieckSpectralSequenceOfSupportedSheaf` (`OpenInclusionLeray.lean`) names this sequence as
  the Grothendieck spectral sequence of `Γ(X, −) ∘ Γ̲_Z` (by definition, not a comparison);
  `openInclusionLerayE2Equiv`: for open `U`, `E₂^{p,q} ≅ H^p(X, R^q i_*(F_U))`;
  `locallyClosedTruncationSpectralSequenceE2WitnessEquiv` (`LocallyClosedWitnessChangeSpectral.lean`):
  the E₂ terms for two witnesses of one set agree.

| SGA 2 I | Lean | Content |
| --- | --- | --- |
| I.2.7 | `derivedSupportedSheafRestrictionIso` (`SupportedSheafRestriction.lean`); `SupportedSheafBoundary.lean`; `derivedUnderlineGammaZ_stalkSupport_subset_frontier` and its `sheafH_Z_n` and sheaf-Ext versions (`SupportedSheafStalkBoundary.lean`) | closed `Z`: `ℋ_Z^n` commutes with restriction to opens, is 0 on `X ∖ Z`, and on the interior of `Z` for `n > 0`; stalk support in `Z`, in `∂Z` for `n > 0`; also for sheaf Ext and `sheafH_Z_n` |
| | `derivedUnderlineGammaLocallyClosed_stalkSupport_subset_closure`, `_subset_frontier` (`LocallyClosedSheafBoundary.lean`) | locally closed `Z`: 0 off `Z̄`, and on the interior of `Z` for `n > 0`; stalk support in `Z̄`, in `∂Z` for `n > 0` |
| I.2.7 (23 bis) | `closedPushforwardCohomologyEquiv`, `derivedSupportedSheafClosedCohomologyEquiv` (`ClosedSupportCohomology.lean`); `derivedLocallyClosedSupportCohomologyEquiv`, `_naturality` (`LocallyClosedSupportCohomology.lean`) | closed pushforward preserves cohomology; `ℋ_Z^q F = i_* i^* ℋ_Z^q F` and `H^p(X, ℋ_Z^q F) = H^p(Z̄, i^* ℋ_Z^q F)` for `i : Z̄ → X`, natural, closed and locally closed `Z` |
| I.2.8 | `locallyClosedNestedCohomologySequence_exact`, `nestedClosedSubspaceCohomologySequence_exact` (`NestedSupportCohomology.lean`, `NestedSupportLocallyClosed.lean`, `NestedSupportSubspace.lean`); `ext_contravariant_exact` (`ExactSequences.lean`, generic, for a given short exact sequence) | Ext sequence of I.1.10, exact in every degree, natural, boundary the extension class; degree 0 for `Z` open ∩ closed: inclusion and restriction of sections |
| I.2.9 | `relativeCohomologySequence_exact`, `relativeBoundaryEquiv` (`RelativeCohomologySequence.lean`); `relativeRestriction_zero_sections`, `relativeSupportMap_zero_sections` (`RelativeCohomologySections.lean`); `ExposeIII/OrdinaryCohomologyRestriction.lean` | `H_Z → H(X) → H(X ∖ Z) → H_Z[1]` exact, injective at the start; degree 0: inclusion and restriction of sections; middle map ordinary restriction; `H^n(X ∖ Z) ≅ H^{n+1}_Z` if `H^n(X) = H^{n+1}(X) = 0` |
| I.2.10 | `locallyClosedNestedDerivedSheafSequence_exact`, `nestedClosedSubspaceDerivedSheafSequence_exact` (`LocallyClosedNestedSheafCohomology.lean`) | exact in every degree, natural; derived maps of the I.1.9 arrows, boundary from an injective resolution; first map monic; degree 0 gives I.1.9 |
| I.2.11 | `sheafH_Z_n` (`DerivedFunctors.lean`); `derivedUnderlineGammaZIsoModel` (`SupportedSheafModel.lean`, `DerivedSupportedSheafOne.lean`, `SupportedSheafDimensionShift.lean`) | `ℋ_A^0`, `ℋ_A^1` are kernel and cokernel of `F → f_*(F_{X∖A})`, `ℋ_A^i = R^{i−1} f_*(F_{X∖A})` for `i ≥ 2`, natural |
| I.2.12, inputs | `isFlasque_of_injective` (`InjectiveFlasque.lean`); `H_pos_subsingleton_of_isFlasque`, `H_pos_restrict_subsingleton_of_isFlasque` (`FlasqueCohomology.lean`); `gammaZSectionsFunctor_map_shortExact` (`SupportedSectionExactness.lean`); `DerivedFunctors.lean` | injectives are flasque; flasque sheaves are acyclic on every open; `Γ_Z` on every open is exact on sequences with flasque kernel; `H^n_Z` (`n > 0`) vanishes on injectives |
| I.2.12 | `derivedGammaZSections_isZero_of_isFlasque` (`FlasqueResolution.lean`); `H_Z_pos_subsingleton_of_isFlasque`, `H_Z_pos_restrict_subsingleton_of_isFlasque`; `LocallyClosedCohomology.lean`; `derivedUnderlineGammaZ_isZero_of_isFlasque`, `sheafH_Z_n_isZero_of_isFlasque`, `derivedUnderlineGammaLocallyClosed_isZero_of_isFlasque` | flasque `F`, `n > 0`: `H^n_Z = 0` in both forms (closed `Z` also on every open) and `ℋ^n_Z = 0`, closed and locally closed `Z` |
| | `isFlasque_iff_H_Z_one_subsingleton`, `isFlasque_iff_H_Z_pos_subsingleton` (`FlasqueVanishingCriterion.lean`) | `F` flasque iff `H^1_Z(X, F) = 0` for all closed `Z`, iff all positive `H_Z` vanish |
| I.2.13 | `I_2_13_degree_zero_mono_iff`, `I_2_13_degree_zero_one_iso_criterion`, `I_2_14_unit_sections_injective` (`ExactSequences.lean`) | `ℋ^0_Z = 0` iff `F → j_* j^* F` is mono (then injective on sections); `ℋ^0_Z = ℋ^1_Z = 0` iff it is an isomorphism |
| | `derivedSupported_vanishes_iff_intersectionRestriction` (`ExposeIII/CohomologyRestrictionCriterion.lean`) | every `N`: `ℋ^i_Z F = 0` for `i ≤ N` iff, on every open `V`, `H^i(V, F) → H^i(V ∩ U, F)` is bijective for `i < N`, injective for `i = N` |
| | `ExposeIII/RestrictionRedundancy.lean`; `derivedSupported_vanishes_iff_intersectionRestriction_bijective` (`ExposeIII/HigherRestrictionRedundancy.lean`) | `N > 0`: b) follows from a); `N = 1` directly, all `N` by complement-adapted injective effacement and dimension shifting |
| I.2.14 | `supported_vanishing_iff_relativeRestriction` (`RelativeCohomologySequence.lean`); `supported_vanishing_iff_ordinaryRestriction` (`ExposeIII/CohomologyRestrictionCriterion.lean`) | `H^i_Z(X, F) = 0` for `i ≤ n` iff `H^i(X) → H^i(X ∖ Z)` is bijective for `i < n`, injective for `i = n` (relative-sequence, resp. ordinary maps) |

Generic lemmas: `ExtRightDerived*`, `RightDerived*`, `SpectralObject*`, `SpectralSequence*`,
`HomComplex*`, `DerivedTruncation*`, `HomologicalSpectralObject`, `RepresentedFunctorSequence`.

### Open

- **I.1.1–I.1.2** in SGA's form: `i^!(F)` as the unique subsheaf of `i^*(F)`, and `i_!(G)` as the
  subsheaf of `i_*(G)` of sections with support closed in `U`. The functors are constructed directly
  (I.1.3–I.1.4); these characterizations are not stated.
- **I.1.5** `ℋom(i_!G, F) = i_*ℋom(G, i^!F)` for arbitrary `G`; only `G = ℤ_Z` (I.1.6) is proved.
- **I.1.7** For Modules only I.1.6 exists (`ringedSpaceSupportHomEquiv`; Exposé VI's
  `moduleLocallyClosedSupport`); the module `i_! ⊣ i^!` of I.1.3 and I.1.5 are not constructed.
- **I.2.6, comparisons.** For open `Z`, only the E₂ terms are compared with the Leray spectral
  sequence of `Z → X`; no Leray spectral sequence is constructed. For two witnesses of one locally
  closed set, only the E₂ terms are identified.
- **I.2.10 and I.2.8.** The sheaf sequence is not shown to be the sheafification of the group
  sequence; the connecting maps are not compared.
- **Remark after I.2.14**, (30)–(32): the normal orientation sheaf `𝒯_{Y,X}` and the Gysin map are
  not formalized.

## SGA 2, Exposé II — Application to quasi-coherent sheaves on preschemes

Entry point: `lean/SGA/SGA2/ExposeII.lean`; files are in `lean/SGA/SGA2/ExposeII/` unless a path is
given. English: `translation/SGA2/ExposeII/en-body.tex`.

Lean works on `X = Spec R`. For an `R`-module `M`, `affineTildeAbSheaf M` is the associated sheaf `M~`
as an abelian sheaf (`affineTildeSheaf M` keeps the module values), `affineSupportClosed I` is `V(I)`,
and `H_Z`, `H`, `derivedUnderlineGammaZ Z i` (the sheaves `ℋ_Z^i`) are as in Exposé I. SGA's
`lim Ext^i(A/I^n, M)` is mathlib's `localCohomology I i`; `H^i((f), M)` is `stableKoszulCohomology fs M i`,
the colimit over `n` of the cohomology of `Hom(K(f^n), M)`, where `koszulComplex` is the iterated
homotopy cofiber of multiplication by each `f_α`. "Any `R`" means no noetherian hypothesis.

### Proved

| SGA 2 II | Lean | Content |
| --- | --- | --- |
| II.1–II.3 | `II_1_open`, `II_3_restriction`, `II_3_affineChart` (`QuasiCoherentSupported.lean`) | `ℋ_U^n(F) ≅ R^n j_*(j^*F)` for open `U`; `ℋ_Z^n` commutes with restriction to opens; `H_Z` on an affine open of a scheme is `H_Z` on its `Spec` chart |
| II.3, closed `Z`, degree 0 | `schemeModuleGammaZ_isQuasicoherent` (`ExposeVI/QuasiCoherentSupportedModules.lean`) | On a locally noetherian scheme, the sections of a quasi-coherent module supported in `Z` form a quasi-coherent module |
| II.4 | `affineTildeAb_H_pos_subsingleton`, `affineTildeAb_globalSectionsEquiv` (`AffineCohomologyVanishing.lean`), `affineTildeAb_shortExact` (`AffineExactness.lean`) | `H^{n+1}(X, M~) = 0` for `R` noetherian and any `M`; for any `R`, `M ↦ M~` is exact and `Γ(X, M~) ≅ M` |
| II.(4.2)–(4.3) | `affineRelativeLowDegree_exact`, `affineSupportedCohomologyEquivOpen` (`AffineRelativeSequence.lean`) | `R` noetherian, any closed `Z` and `M`: `0 → H_Z^0 → H^0(X) → H^0(X−Z) → H_Z^1 → 0` is exact and `H_Z^{n+2} ≅ H^{n+1}(X−Z)` |
| II.(4.2), degree 0 | `localizationFamilyMap_ker` (`LocalizationKernel.lean`); `powerTorsionEquivAffineSupportedSections`, `powerTorsionEquivGammaZ` (`AffineSupport.lean`) | `ker(M → ∏ M_{f_α})` (finite family) is the torsion `powerTorsion I M`, `I = (f_α)`; for `I` finitely generated, torsion is the module of sections of `M~` supported in `V(I)`, and Exposé I's `gammaZ` |
| II.5 | `II_5`, `II_5_addEquiv` (`KoszulSupportedComparison.lean`); `II_5_zero`, `stableKoszulCohomologyZeroIsoGammaZ` (`AffineComparisonZero.lean`) | `H^n((f), M) ≅ H^n_{V(f)}(M~)` naturally in `M`, for any finite list: every `n` for `R` noetherian, `n = 0` for any `R`. The two factors of `II_5` commute with connecting maps (`localCohomologyToStableKoszul_δ`, `affineLocalCohomologyNatIso_δ`) |
| II.5, one element | `stableKoszulSingletonOneIsoRestrictionCokernel`, `stableKoszulSingleton_isZero_above_one` (`LocalizationCokernelColimit.lean`, `PrincipalCechComparison.lean`) | Any `R`: `H^1((f), M) ≅ coker(Γ(X, M~) → Γ(D(f), M~))`, and `H^i((f), M) = 0` for `i > 1` |
| II.6–II.7 | `II_6_a_affine`, `II_6_b_affine`, `II_7_affine_ordinary_vanishing` (`AffineExtColimitComparison.lean`) | Aliases of `affineLocalCohomologyNatIso`, its components, and `affineTildeAb_H_pos_subsingleton`; `II_2_affine_global` and `GeneralSchemeComparison.lean` hold further aliases |
| II.(7.3) | `affineLocalCohomologyNatIso`, `affineLocalCohomologyAddEquiv`, `affineLocalCohomologyNatIso_δ` (`ConnectingSequenceExtension.lean`, `AffineCohomologyComparison.lean`) | `R` noetherian, any `I`: `localCohomology I n ≅ H^n_{V(I)}(−~)` in every degree, naturally in all modules, compatibly with connecting maps |
| II.(7.3), degree 0 | `localCohomologyZeroIsoAffineSupportedFunctor`, `localCohomologyZeroIsoGammaZ` (`AffineComparisonZero.lean`) | Any `R`, `I` finitely generated: `localCohomology I 0` is the module of supported sections of `M~` (naturally in `M`), and `gammaZ` |
| II.(7.3)–(7.4) | `generatorPowerIdeal_cofinal`, `generatorPowersLocalCohomologyIso` (`FiniteGenerators.lean`, `FiniteGeneratorColimits.lean`) | The ideals `(f^n)` and `I^n` are cofinal; their `Ext` colimits are naturally isomorphic in each degree |
| II.(7.3)–(7.6) | `localCohomologyIsoOfFinal_δ`, `localCohomologyToStableKoszul_δ` (`LocalCohomologyReindexing.lean`, `KoszulLocalCohomologySequence.lean`) | Any `R`: reindexing and `localCohomology (f) i → H^i((f), −)` commute with connecting maps |
| II.(7.5) | `powerTorsion`, `quotientHomEquivTorsionBySet`, `powerTorsion_eq_of_radical_eq` (`Torsion.lean`); `localCohomologyZeroIsoPowerTorsion` (`LocalCohomologyZero.lean`) | Torsion is the union of the annihilators of the `I^n`; `Hom(R/I, M) ≅ {m : Im = 0}` by evaluation at `1`; torsion depends only on the radical (finitely generated ideals); `localCohomology I 0` is torsion |
| II.(7.5), colimits | `quotientHomColimitIso`, `generatorHomColimitIso` (`TorsionColimit.lean`, `GeneratorHomColimit.lean`) | `colim Hom(R/I^n, −)` and `colim Hom(R/(f^n), −)` are naturally the torsion functor |
| II.(7.5), Koszul | `koszulHomologyZeroIsoQuotient`, `koszulCohomologyZeroIsoAnnihilator`, `stableKoszulCohomologyZeroIsoPowerTorsion` (`KoszulDegreeZero.lean`, `KoszulCohomologyZero.lean`) | Any `R`: `H_0(f, R) ≅ R/(f)`; `H^0(f, M)` is the annihilator of `(f)`; `H^0((f), M)` is torsion |
| II.(7.6) | `koszulExtComparison`, `stableKoszulExtComparison`, `stableKoszulExtComparison_zero_isIso` (`KoszulAugmentation.lean`, `ProjectiveComplexLift.lean`, `KoszulExtComparison.lean`, `KoszulExtComparisonZero.lean`) | Lift the augmentation `K(f) → R/(f)` (projective terms) to a projective resolution, unique up to homotopy; dualize, take cohomology and colimits. The map is natural in `M`, independent of the lift, and an isomorphism in degree 0 |
| II.(7.6), connecting maps | `stableKoszulExtComparisonConnectingHom` (`KoszulCoefficientSequence.lean`, `ExtCoefficientSequence.lean`, `ExtColimitSequence.lean`, `KoszulComparisonIsomorphism.lean`) | Connecting maps of finite and stable Koszul cohomology and of `Ext` colimits, with exactness; (7.6) commutes with them |
| II.8 | `II_8`, `stableKoszulExtComparisonIso` (`CohomologicalComparison.lean`, `KoszulComparisonIsomorphism.lean`); `localCohomologyIsoStableKoszul` (`KoszulLocalCohomology.lean`) | `R` noetherian: (7.6) is an isomorphism in every degree, natural in `M` (dimension shifting, `ConnectingSequence.Hom.isIso_of_degree_zero`, with II.9 and II.11); hence `localCohomology (f) i ≅ H^i((f), −)` |
| II.8, regular sequences | `koszulProjectiveResolution`, `koszulExtComparisonIsoOfIsRegular` (`KoszulRegularResolution.lean`) | `R` noetherian local, `f` regular (mathlib's `IsRegular`): `K(f)` is a projective resolution of `R/(f)`, and the finite-stage comparison is a natural isomorphism in every degree |
| II.9 | `II_9_b_iff_c`, `II_9_a_implies_b` (`EssentiallyZero.lean`, `InjectiveDetection.lean`, `InjectiveHomology.lean`, `InjectiveLocalCohomology.lean`, `KoszulCohomology.lean`); `II_9_a_iff_b`, `II_9_a_iff_c` (`KoszulComparisonIsomorphism.lean`) | Any `R`. In each degree `i`: (b) `H^i((f), E) = 0` for injective `E` iff (c) `(H_i(f^n, R))_n` is essentially zero; for `i > 0`, any isomorphism `localCohomology I i ≅ H^i((f), −)` gives (b). (a) (7.6) is an isomorphism in every degree iff (b) for all `i > 0` iff (c) for all `i > 0`; (b) ⇒ (a) is proved only in this all-degree form. Inputs: `Hom` colimits of essentially zero systems vanish, injectives detect essential vanishing, and `Hom(H_i(K), E) ≅ H^i(Hom(K, E))` for injective `E` |
| II.10 | `affineTildeSheaf_isFlasque_of_injective`, `affineTildeAbSheaf_isFlasque_of_injective`, `powerTorsion_injective_of_injective` (`InjectiveLocalization.lean`, `InjectiveTorsion.lean`, `FiniteFractionCover.lean`, `InjectiveFlasque.lean`) | `R` noetherian, `E` injective: `E → E_f` is surjective, torsion in `E` is injective (Artin–Rees, Baer's criterion), and `E~` is flasque |
| II.10, Koszul side | `II_10_koszul_vanishing_of_injective`, `II_10_flasque_implies_koszul` (`TopologicalNoetherianFlasque.lean`) | `R` noetherian, `E` injective, `i > 0`: `H^i_{V(f)}(E~) = 0`; if every such `E~` is flasque, `H^i((f), E) = 0` (by II.5) |
| II.11 | `II_11`, `scalarCofiberHomologyShortComplex_shortExact` (`KoszulComplex.lean`, `KoszulCofiber.lean`, `KoszulProZero.lean`) | Any `R`, noetherian `N`, `i > 0`: `(H_i(f^n, N))_n` is essentially zero. Induction on the list via `0 → H_{i+1}(K)/a → H_{i+1}(Cone a) → Ann(a, H_i(K)) → 0`; Koszul terms are noetherian for noetherian `N` |
| II.11, steps | `Principal.lean`, `PrincipalSystem.lean`, `PrincipalKoszul.lean`, `VariableAnnihilators.lean`, `EssentiallyZero.lean` | One element: the annihilators of `f^n` in a noetherian module stabilize and the transitions vanish uniformly, also with coefficients varying in `n`, so their `Hom` colimits vanish; principal Koszul homology is `M/fM`, `Ann(f)`, then `0`. Essentially zero systems are closed under subobjects, quotients and extensions |
| Examples | `Examples.lean`, `ExamplesII5.lean` | `f = 0` over `ℤ`: `H_1 ≠ 0` in an essentially zero system, zero transition from exponent 2 to 1; empty families; II.5 and II.6 b) for `(2) ⊂ ℤ` |

### Open

- **II.1–II.3**: quasi-coherence of `ℋ_Z^i(F)`, except for closed `Z` in degree 0 on a locally
  noetherian scheme. It needs quasi-coherence of higher direct images of quasi-coherent modules under
  quasi-compact open immersions, which mathlib does not have.
- **II.4**: (4.1) `ℋ_Y^i(F) ≅ (H_Y^i(X, F))~`; vanishing, (4.2) and (4.3) over a non-noetherian ring.
  The degeneration of the spectral sequence I.2.6 in SGA's proof is not stated:
  `II_7_affine_ordinary_vanishing` is only the vanishing of `H^{p+1}(X, M~)`.
- **II.5** in positive degrees over a non-noetherian ring.
- **II.6–II.7**: II.6 a) (the sheaf map `lim 𝓔xt^i(𝒪/I^n, F) → ℋ_Y^i(F)` on a locally noetherian
  scheme), II.6 b) on a non-affine noetherian scheme, and Lemma II.7. The affine results concern
  global sections.
- **II.10** when `Spec A` is a noetherian space and `A` is not a noetherian ring.

## SGA 2, Exposé III — Cohomological invariants and depth

Entry point: `lean/SGA/SGA2/ExposeIII.lean`; files are in `lean/SGA/SGA2/ExposeIII/`.
English: `translation/SGA2/ExposeIII/`.

Module statements (§§1–2, as in SGA, and the affine rows of §3) assume a noetherian ring and finite
modules unless a row says otherwise.
`depth I M : ℕ∞` (III.2.3) is the supremum of the `n` with `Ext^i(N, M) = 0` (`Abelian.Ext`) for `i < n`
and every finite `N` killed by a power of `I`; `localDepth M p` is the depth of `M_p` over `R_p`. SGA's
regular sequences may have zero last quotient: they are mathlib's `IsWeaklyRegular`. §3 uses Exposé I's
notation, with closed supports `Z`. A coherent module is `M : X.Modules` with `M.IsFinitePresentation` on
a locally noetherian scheme (mathlib has no `IsCoherent`); `moduleStalkDepth M x` and
`structureStalkDepth X x` are the depths of `M_x` and `𝒪_{X,x}`.

### Proved

| SGA 2 III | Lean | Content |
| --- | --- | --- |
| III.1 | `sgaAssociatedPrimeSpectrum`, `sgaAssociatedPrimeSpectrum_eq` (`AssociatedPrimes.lean`, also for III.1.1–III.2.1) | Primes that are the annihilator of a nonzero element, over any ring; over a noetherian ring, mathlib's associated primes (radical-annihilator convention) |
| III.1.1–III.1.3 | `associatedPrimes_finite`, `exists_nonzero_smul_eq_zero_iff`, `radical_annihilator_eq_sInf_minimal_associatedPrimes`; `mem_support_iff_exists_associatedPrime`, `mem_support_iff_annihilator_le`, `mem_support_iff_radical_annihilator_le`; `associatedPrimeSpectrum_linearMap` | 1.1: finitely many; their union is the zero divisors; `√ann M` is the intersection of the minimal ones. 1.2: `p ∈ Supp M` iff `p` contains an associated prime, `ann M`, or `√ann M`. 1.3: `Ass Hom(N, M) = Supp N ∩ Ass M` |
| III.2.1 | `lemma_2_1` | The five conditions, including the localization criterion, for finite `N` with `Supp N = V(I)` |
| III.2.2 | `III_2_2_a`, `III_2_2_b` (`RegularExt.lean`) | (a) Any ring and modules: a regular sequence of length `l` in `I` gives `Ext^i(N, M) = 0` for `i < l` if a power of `I` kills `N`. (b) The converse for `Supp N = V(I)`. No `IM ≠ M` hypothesis, unlike mathlib's Rees theorem |
| III.2.3–III.2.4 | `depth`, `le_depth_iff`, `le_depth_iff_exists_regular`, `le_depth_iff_exists_test_module` (`Depth.lean`) | The definition (any ring); `n ≤ depth_I M` iff some regular sequence of length `n` lies in `I`, iff `Ext^i(N, M) = 0` for `i < n` for one finite `N` with `Supp N = V(I)` |
| III.2.5 | `III_2_5` (`Depth.lean`) | `depth_I M = depth_I(M/fM) + 1` for `f ∈ I` regular on `M`, including infinite depth |
| III.2.6 | `III_2_6`, `exists_regular_extension`, `exists_regular_extension_of_depth_top` (`MaximalRegular.lean`); `exists_infinite_regular_extension` (`InfiniteRegular.lean`); `no_maximalRegularSequence_top` (`Examples.lean`) | Depth `n < ∞`: a regular sequence in `I` extends to a maximal one, of length `n`, and to any length `≤ n`. Depth `∞`: it extends by one element, and to an infinite sequence with regular finite prefixes; for `I = R` no maximal one exists. SGA omits the finite-depth hypothesis; the translation keeps SGA's wording |
| III.2.7 | `III_2_7` (`DepthSupport.lean`) | `depth_I M < ∞` iff `Supp M ∩ V(I) ≠ ∅` |
| III.2.8 | `depth_eq_extDepth`, `depth_maximalIdeal_eq_extDepth` (`Depth.lean`) | Depth is the first `i` with `Ext^i(N, M) ≠ 0`, for any finite `N` with `Supp N = V(I)`; in a local ring, `N` the residue field |
| III.2.9–III.2.10 | `III_2_9`, `III_2_10` (`DepthLocalization.lean`) | `depth_I M = inf_{p ∈ V(I)} localDepth M p`; in a semilocal ring, depth along the Jacobson radical is the infimum over maximal ideals |
| III.2.11 | `III_2_11_flat`, `III_2_11_faithfullyFlat` (`DepthBaseChange.lean`) | `R → S` flat, `S` any ring: `depth_I M ≤ depth_{IS}(S ⊗ M)`; equality for `S` faithfully flat and noetherian |
| III.§3, algebra | `le_depth_iff_localCohomology_vanishes`, `depth_eq_iInf_localCohomology` (`DepthLocalCohomology.lean`) | `n ≤ depth_I M` iff `localCohomology I i M = 0` for `i < n`; depth is the first nonzero degree, or `∞`. The `Ext` of `depth` and that of `localCohomology` are linked by a vanishing equivalence |
| III.§3, affine | `le_depth_iff_affine_H_Z_vanishes`, `depth_eq_iInf_affine_H_Z`, `affine_H_Z_vanishes_iff_localDepth`, `affine_H_Z_vanishes_iff_testModule_ext`, `affine_H_Z_vanishes_iff_quotient_ext` (`AffineDepth.lean`) | `n ≤ depth_I M` iff `H^i_{V(I)}(M~) = 0` for `i < n`, iff `localDepth M p ≥ n` on `V(I)`, iff `Ext^i` from a test module, or from `R/I`, vanishes for `i < n` |
| Affine stalks | `affineStalkRingEquiv`, `affineModuleStalkSemilinearEquiv`, `localDepth_eq_actual_stalk_depth` (`AffineStalkDepth.lean`) | `R_p ≅ 𝒪_{X,p}` and `M_p ≅ (M~)_p` compatibly with scalars; `localDepth M p` is the depth of the stalk |
| III.3.1 (i) ⇔ (iii) | `derivedSupported_vanishes_iff_local_H_Z` (`SupportedSheafVanishing.lean`) | Any space and abelian sheaf: `ℋ_Z^i(F) = 0` for `i < n` iff `H^i_{Z∩U}(U, F) = 0` for `i < n` on every open `U`; proof by I.2.6 and sheafification |
| III.3.1 (i) ⇔ (ii) | `derivedSupported_vanishes_iff_intersectionRestriction`, `relativeRestriction_eq_ordinary` (`OrdinaryCohomologyRestriction.lean`, `OpenIntersectionCohomology.lean`, `CohomologyRestrictionCriterion.lean`) | `ℋ_Z^i(F) = 0` for `i ≤ n` iff, on every open `V`, `H^i(V, F) → H^i(V ∩ (X−Z), F)` (`ordinaryCohomologyRestrictionToIntersection`) is bijective for `i < n` and injective for `i = n`; the map of the sequence I.2.9 is this restriction in every degree, and `V ∩ (X−Z)` as an open of `V` is identified with the open of `X` |
| III.3.2, I.2.13 | `derivedSupported_vanishes_two_iff_intersectionRestriction_zero`, `intersectionRestriction_one_injective_of_zero_bijective` (`RestrictionRedundancy.lean`); `derivedSupported_vanishes_iff_intersectionRestriction_bijective`, `intersectionRestriction_highest_injective_of_lower_bijective` (`ComplementInjectiveEffacement.lean`, `RestrictionCoefficientShift.lean`, `HigherRestrictionRedundancy.lean`) | Any abelian sheaf, `n ≥ 0`: `ℋ_Z^i(F) = 0` for `i < n + 2` iff restriction is bijective for `i ≤ n` on every open; injectivity in degree `n + 1` follows. Proof: embed `F` in the direct image of an injective sheaf on `X−Z`, then shift dimension |
| III.3.3 (i), (iii), (iv) | `coherent_depth_iff_derivedSupported_vanishes`, `coherent_depth_iff_local_H_Z_vanishes` (`HomeomorphismSupportedCohomology.lean`, `AffineChartSupportedCohomology.lean`, `CoherentDepth.lean`) | Coherent `M`, every `n`: `moduleStalkDepth M x ≥ n` on `Z` iff `ℋ_Z^i(M) = 0` for `i < n` iff `H^i_{Z∩U}(U, M) = 0` for `i < n` on every open `U`, by transport to affine charts |
| III.3.3 (ii) | `coherent_depth_iff_intersectionRestriction` (`CohomologyRestrictionCriterion.lean`), `coherent_depth_iff_intersectionRestriction_bijective` (`HigherRestrictionRedundancy.lean`) | Coherent `M`: depth `≥ n + 1` on `Z` iff restriction is bijective for `i < n` and injective for `i = n`; depth `≥ n + 2` iff bijective for `i ≤ n` |
| III.3.3 (v), (vi) | `III_3_3_v`, `III_3_3_vi`, `III_3_3_vi_quotient` (`SheafExtDepth.lean`) | Restatements of III.2.4 with module `Ext_R`: all finite `N` killed by a power of `I`; one finite `N` with `Supp N = V(I)`; `N = R/I` |
| III.3.4 | `example_3_4` (`AffineHartogs.lean`) | `R` noetherian local: `depth M ≥ n + 1` iff `H^i(X, M~) → H^i(X − {m}, M~)` is bijective for `i < n` and injective for `i = n`, iff `Ext^i(k, M) = 0` for `i ≤ n`, iff `H^i_m(M~) = 0` for `i ≤ n` |
| III.3.5, affine | `one_le_depth_iff_affineRestriction_injective`, `two_le_depth_iff_affineRestriction_bijective`, `affineRestriction_bijective_of_localDepth` (`AffineHartogs.lean`) | `Γ(X, M~) → Γ(X − V(I), M~)` is injective iff `depth_I M ≥ 1`, bijective iff `depth_I M ≥ 2`; bijective if `localDepth M p ≥ 2` on `V(I)` |
| III.3.5 | `structureStalkDepth_two_le_iff_restriction_bijective`, `structureGlobalHartogsRingEquiv` (`SchemeHartogs.lean`, `SheafHartogsGluing.lean`, `SchemeHartogsCriterion.lean`); `coherent_hartogs_iff`, `coherentHartogsEquiv` (`SchemeModuleStalks.lean`, `AffineQuasicoherentHartogs.lean`, `CoherentAffineCharts.lean`, `CoherentHartogs.lean`) | Locally noetherian `X`: `structureStalkDepth X x ≥ 2` on `Z` iff `𝒪(V) → 𝒪(V − Z)` is bijective for every open `V`; the same for coherent `M` with `moduleStalkDepth`, finite affine coefficient modules coming from `IsFinitePresentation` |
| III.3.6 | `affine_connected_iff_of_localDepth`, `affineConnectedComponents_bijective_of_localDepth`, `affineConnectedComponentsEquiv` (`AffineClopens.lean`, `AffineHartogs.lean`, `AffineConnectedComponents.lean`); `schemeConnectedComponents_bijective_of_stalkDepth`, `schemeConnectedComponentsEquiv` (`SchemeClopens.lean`, `SchemeConnectedComponents.lean`) | Locally noetherian `X`, `structureStalkDepth X x ≥ 2` on `Z`: `π₀(X − Z) → π₀(X)` is bijective, with no quasi-compactness hypothesis; proof through idempotent sections of clopens. Affine form with `localDepth R p ≥ 2` on `V(I)`, including "`X` connected iff `X − V(I)` connected" |
| III.3.7 | `III_3_7_complement`, `III_3_7_of_minDim` (`ConnectednessInCodimension.lean`); `III_3_7`, `III_3_7_list`, `III_3_7_codimension_list` (`ComponentChains.lean`) | Locally noetherian `X` with `dim 𝒪_{X,x} ≥ d ⇒ depth 𝒪_{X,x} ≥ 2`: removing a closed set of local dimension `≥ d` preserves `π₀`; on connected `X`, components are joined by finite chains with `codim(X_i ∩ X_{i+1}) ≤ d − 1`, codimension being the infimum of `dim 𝒪_{X,x}` |
| III.3.8 | `ClosedAntifilter` (`AntifilterConnectedness.lean`); `exists_irreducibleComponents_connected_chain`, `III_3_8_ii_implies_i`, `III_3_8_i_implies_ii`, `III_3_8`, `III_3_8_list` (`LocallyNoetherianComponents.lean`, `AntifilterEquivalence.lean`) | Locally noetherian space, antifilter `Ff` containing each closed set locally in `Ff`: complements of members are connected iff any two components are joined by a chain with `X_i ∩ X_{i+1} ∉ Ff`. Connected means `IsPreconnected`. Components are locally finite (finitely many on a noetherian space) with closed unions; on a connected noetherian space they are joined by chains of meeting components |
| III.3.9 | `III_3_9` (`Catenary.lean`, `EquidimensionalityCriterion.lean`) | `R` noetherian local, `dim R_p ≥ 2 ⇒ depth R_p ≥ 2`, chain condition (`SatisfiesChainCondition`): `dim R/p = dim R` for every minimal prime `p`; the chain condition gives equal dimensions to adjacent components |
| III.3.10 | `III_3_10_depth_lt_two` (`ConnectednessInCodimension.lean`) | If `π₀(X − Z) → π₀(X)` is not bijective, some point of `Z` has depth `< 2` |
| III.3.12 | `III_3_12_koszul`, `III_3_12_structure`, `III_3_12` (`HigherVanishingOnStructure.lean`) | `R` noetherian, `Y = V(f_1, …, f_m)`: `H^i_Y(M~) = 0` for `i > m` and every `M` (by II.5); `III_3_12` is the resulting equivalence with the case `M = R` |
| III.3.13 | `III_3_13_principal`, `III_3_13_exists_non_principal`, `III_3_13_relative` (`ExamplesIII313.lean`) | `H^i_{V(f)}(𝒪) = 0` for `i > 1`; a noetherian domain that is not a UFD has a non-principal prime of height 1; `H_Y^{n+2}(𝒪) ≅ H^{n+1}(X − Y, 𝒪)` on a noetherian affine |
| Examples | `depth_top`, `depth_bot`, `depth_int_two` (`Examples.lean`); `ExamplesIII.lean` | Depth `∞` along `R` (lists of `1` are regular), `0` along `0` on a nonzero finite module, `1` for `ℤ` along `(2)`; III.3.3 (vi), III.3.12, III.3.13 over `ℤ` |

### Open

- **III.3.3 (v)–(vi)** with sheaf `𝓔xt^i_𝒪(G, F)` for coherent `G` supported on `Y`, on a locally
  noetherian scheme.
- **III.3.10**: the ring `k[X_1, …, X_5]/(𝔭 ∩ 𝔮)` and the remark on set-theoretic complete
  intersections.
- **III.3.12** for a closed `Y` not cut out by `m` equations, and for `ℋ_Y^i` on a scheme. Both sides of
  `III_3_12` hold when `Y = V(f_1, …, f_m)`.
- **III.3.13** on a normal 2-dimensional noetherian local ring: the complement of a curve is affine, and
  some curve is not cut out by one equation.

## SGA 2, Exposé IV — Dualizing modules and functors

Entry point: `lean/SGA/SGA2/ExposeIV.lean`. English: `translation/SGA2/ExposeIV/`.
Files below are in `lean/SGA/SGA2/ExposeIV/` unless prefixed with another exposé's directory.

`R` is commutative and noetherian unless a row says otherwise. SGA's `T : 𝒞_Y° → Ab` is an
additive functor `(SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat` (`𝒞_Y`: finite modules supported in
`V(J)`); `T(M)` is an `R`-module through homotheties, and left exact means `PreservesFiniteLimits`.
Dualizing modules over a local ring follow the supported-module convention
`SupportedDualizingModule H`: `H` is supported at `𝔪` and `Hom(-, H)` satisfies IV.3.1(i) on
`𝒞_𝔪`; IV.4.1's condition alone does not see a summand `N` of `H` with `Γ_𝔪(N) = 0`. Locally
Artinian means finitely generated submodules are Artinian. `Â = AdicCompletion 𝔪 R`, and
`Î = I ⊗ Â` (IV.4.6 footnote), not the adic completion of `I`.

### Proved

| SGA 2 IV | Lean | Content |
| --- | --- | --- |
| IV.1, opening | `additiveFunctorModule`, `additiveFunctorModuleLift` (`AdditiveFunctorModules.lean`) | `T(M)` is an `R`-module via `T` of homotheties; each `T(f)` is linear; forgetting the action gives back `T`. |
| IV.1.1 | `additiveFiniteModuleEvaluation_isIso_iff`, `additiveFiniteModuleRepresentationIso` (`FiniteModuleEvaluation.lean`, `FiniteFreeEvaluation.lean`, `FiniteModuleRepresentation.lean`) | `φ_T : T → Hom(-, T(R))` is an isomorphism iff `T` is left exact; `T(R)` need not be finite. Proof: coordinates on finite free modules, then finite free covers. |
| IV.1, after 1.1 | `finiteModuleFunctorEquivalence` (`FiniteModuleFunctorEquivalence.lean`) | `H ↦ Hom(-, H)`: all modules `≌` additive left-exact functors on finite modules. |
| IV.1.2 | `additiveModuleEvaluation_isIso_iff_preorderLimits`, `additiveModule_representable_iff_preorderLimits` (`FiniteSubmoduleColimit.lean`, `ModuleEvaluation.lean`, `ModuleRepresentation.lean`, `PreorderLimitRepresentation.lean`) | `T` on all modules is represented by `T(R)` iff it preserves limits over preordered sets in `R`'s universe, filtered or not. Every module is the filtered colimit of its finite submodules; products and pullbacks are preorder limits. |
| IV.1.3, setting | `SupportedFGModuleCat`, `supportedQuotientStage`, `supportedQuotientStage_covers`, `supportedFunctorDiagram` (`SupportedFiniteModules.lean`, `SupportedQuotientStages.lean`, `SupportedFunctorDiagram.lean`) | `𝒞_Y` is abelian, the union of the exact full subcategories of finite `R/Jⁿ`-modules. `T(R/Jⁿ)` is a diagram of `R`-modules killed by `Jⁿ`, with injective transitions if `T` is left exact. |
| IV.1.3 | `additiveSupportedFunctorEvaluation_isIso_iff`, `additiveSupportedFunctorRepresentationIso` (`SupportedStageEvaluation.lean`, `SupportedStageRepresentation.lean`, `SupportedFunctorColimit.lean`, `SupportedFunctorEvaluation.lean`, `SupportedFunctorRepresentation.lean`) | `H = colim T(R/Jⁿ)` (`supportedFunctorColimit`) is supported in `V(J)`. `φ_T : T → Hom(-, H)` is independent of `n` and natural, and is an isomorphism iff `T` is left exact; then maps from finite modules to `H` factor through one stage. |
| IV.1.3, end | `supportedModuleFunctorEquivalence` (`SupportedRestrictedHom.lean`, `SupportedFunctorEquivalence.lean`) | Restricted Hom: modules supported in `V(J)` `≌` additive left-exact functors on `𝒞_Y`. |
| IV.1.4 | `supportedDeltaFunctor_vanishing_tfae`, `IntegerCohomologicalSequence` (`IntegerCohomologicalSequence.lean`, `SupportedFunctorVanishing.lean`, `SupportedDeltaVanishing.lean`); `subsingleton_linearMap_iff_of_support_eq_zeroLocus` (`SupportedHomDetection.lean`) | (i)–(iii) are equivalent for bounded-below exact `∂`-functors `(Tⁱ)_{i∈ℤ}` on `𝒞_Y`; `Tⁿ⁻¹ = 0` makes `Tⁿ` left exact. A finite module with support `V(J)` detects vanishing of any module supported in `V(J)`, finite or not. |
| IV.2.1 | `finiteSupportedHomExact_iff_injective` (`InjectivityCriterion.lean`); `powerTorsion_eq_top_iff_support_subset_zeroLocus`, `finiteSupportedHomExact_iff_injective_of_support` (`SupportedModuleTorsion.lean`); `supportedFunctorExact_iff_injective_colimit`, `supportedFunctor_preservesHomology_iff_injective_colimit` (`SupportedFunctorExactness.lean`) | Supported in `V(J)` is the same as `J`-power torsion. For such `H`, `Hom(-, H)` is exact on `𝒞_Y` iff `H` is injective (Artin–Rees and Baer). A left-exact `T` is exact (equivalently `PreservesHomology`) iff `colim T(R/Jⁿ)` is injective. |
| IV.2.2 | `powerTorsion_injective` (`InjectivityCriterion.lean`, from `ExposeII/InjectiveTorsion.lean`) | `H⁰_J(K)` is injective for injective `K`. |
| IV.3.1, Hom form | `moduleBidualEvaluation_isIso_of_artinian_support`, `moduleHomDual_finite_of_artinian_support`, `moduleHomDual_length_of_artinian_support` (`ModuleBidual.lean`, `ModuleBidualFiniteLength.lean`, `ModuleBidualSimpleTests.lean`, `SupportedArtinianDuality.lean`) | `R/J` Artinian, so objects of `𝒞_Y` have finite length. If `H` is injective and `Hom(k, H) ≅ k` for the residue fields at maximal ideals containing `J`, then on `𝒞_Y` canonical evaluation is invertible and `Hom(M, H)` is finite of length `long M`; `H` need not be finite. |
| IV.3.1 | `supportedFunctor_duality_tfae`, `supportedFunctorBidualEvaluationNatTrans`, `supportedFunctorValueIsoOfRepresentation` (`SupportedFunctorDual.lean`, `SupportedFunctorBidualNaturality.lean`, `SupportedFunctorDualityConditions.lean`, `SupportedFunctorDuality.lean`, `ModuleBidualConverse.lean`) | `R/J` Artinian: (i)–(iv) are equivalent for every additive `T`, with left exactness and finite values part of (i). `M → T(T(M))` is natural; representations of `T` respect the `R`-actions. |
| IV.3.2 | `supportedFunctor_exact_and_length_iff_length`, `supportedFunctor_duality_iff_length` (`HomDualLengthExactness.lean`, `SupportedFunctorLengthExactness.lean`) | `R/J` Artinian, `T` left exact: (iv)′ implies (i)–(iv). |
| IV.4.1 | `SupportedDualizingModule`, `supportedDualizingModule_iff_support_functorDuality` (`LocalInjectiveEnvelopes.lean`) | `H` is dualizing iff it is supported at `𝔪` and `Hom(-, H)` satisfies IV.3.1(i). |
| IV.4.2, existence | `nonlocalDualizingFunctor`, `nonlocalDualizingEvaluationIso`, `nonlocalDualizingAntiEquivalence`, `nonlocalDualizingAnnihilator_length` (`NonlocalDualizingFunctor.lean`, `ResidueSumInjectiveEnvelope.lean`, `FiniteLengthHomDuality.lean`, `FiniteLengthModuleCategory.lean`) | Any commutative `R`. For `E` the injective envelope of `⊕_𝔪 R/𝔪`, `Hom(-, E)` is an exact `R`-linear anti-equivalence of finite-length modules with canonical `id ≅ T∘T`. Each `𝔪`-annihilator of `E` is `R/𝔪`, of length 1. |
| IV.4.2, local Artinianness | `allResidueFieldEnvelope_locallyArtinian` (`NonlocalDualizingLocallyArtinian.lean`) | `E` is locally Artinian (essential extensions keep associated primes). |
| IV.4.2, local case | `localFiniteLengthEquivalence` (`LocalFiniteLengthCategory.lean`) | Local `R`: finite-length modules are `𝒞_𝔪` (identity on modules and maps). |
| IV.4.2, representation | `quotient_annihilator_isFiniteLength`, `cofiniteRingQuotientDiagram` (`CofiniteIdeals.lean`); `additiveCofiniteFunctorEvaluation_isIso_iff`, `additiveCofiniteFunctorRepresentationIso` (`CofiniteFunctorRepresentation.lean` and imports) | Any commutative `R`. Ideals `𝔞` with `R/𝔞` of finite length form a filtered system containing the annihilators of finite-length modules. An additive `T` on finite-length modules is represented by `colim_𝔞 T(R/𝔞)` iff it is left exact. |
| IV.4.2, equivalence | `locallyArtinianRestrictedHomFullyFaithful`, `locallyArtinianIsoOfFiniteLengthHom` (`FiniteLengthRestrictedHom.lean`); `locallyArtinianFiniteLengthFunctorEquivalence` (`CofiniteFunctorEquivalence.lean`); `finiteLengthHomExact_iff_injective`, `cofiniteFunctorExact_iff_injective_colimit` (`NonlocalInjectivityCriterion.lean`, `CofiniteFunctorExactness.lean`) | `R` not necessarily local. Restricted Hom: locally Artinian modules `≌` additive left-exact functors on finite-length modules. A locally Artinian `H` is injective iff `Hom(-, H)` is exact there; so `T` is exact iff `colim_𝔞 T(R/𝔞)` is injective. |
| IV.4.2, any dualizing functor | `nonlocalInvolutiveRepresentationIso`, `nonlocalInvolutiveCoefficient_injective`, `nonlocalInvolutiveAnnihilator_length` (`NonlocalDualizingRepresentation.lean`) | `F` an additive `R`-linear contravariant endofunctor of finite-length modules with some natural isomorphism `id ≅ F∘F`, not necessarily canonical evaluation: `F ≅ Hom(-, D)` with `D = colim_𝔞 F(R/𝔞)` injective and locally Artinian, and each `𝔪`-annihilator of `D` (the `𝔪`-primary socle) is `R/𝔪`. |
| IV.4.3 | `finite_local_coinduction_supported_duality`, `SupportedDualizingModule.finite_coinduction` (`CoinductionHomDuality.lean`, `FiniteCoinductionDuality.lean`, `FiniteCoinductionSupport.lean`, `SupportedDualizingTransfers.lean`) | `B` finite over `A`, both noetherian local, `A → B` not assumed local: `Hom_A(B, I)` is dualizing for `B`. |
| IV.4.4 | `quotientCoinductionAnnihilatorIso`, `quotientAnnihilator_supported_duality`, `SupportedDualizingModule.quotient_annihilator` (`QuotientAnnihilatorDuality.lean`, `SupportedDualizingTransfers.lean`) | `A/𝔞` local: the annihilator of `𝔞` in `I`, which is `Hom_A(A/𝔞, I)` by evaluation at 1, is dualizing for `A/𝔞`. |
| IV.4.5 | `localArtinianTensorCompletionEquiv`, `moduleLocallyArtinian_iff_support_maximalIdeal` (`AdicTensorNilpotent.lean`, `LocalArtinianSupport.lean`, `AdicTensorSupported.lean`) | Local `R`: `x ↦ x ⊗ 1 : M → M ⊗ Â` is bijective for every locally Artinian (equivalently, `𝔪`-supported) `M`, finite or not. |
| IV.4.5, equivalences | `supportedCompletionEquivalence`, `localArtinianCompletionEquivalence`, `finiteSupportedCompletionEquivalence`, `completion_submodule_smul_mem`, `completion_restrictScalars_finite` (`SupportedScalarChange.lean`, `SupportedCompletionEquivalence.lean`, `LocalArtinianFiniteIdeal.lean`, `LocalCompletionEquivalence.lean`, `FiniteSupportedCompletionEquivalence.lean`, `CompletionSubmodules.lean`) | `⊗ Â` and restriction (unit `x ↦ 1 ⊗ x`, counit multiplication) are inverse equivalences on modules supported in `V(J)` (`J`-adic `Â`), on locally Artinian modules and on finite supported modules. `R`-submodules are `Â`-submodules. No noetherian hypothesis on `Â`. |
| IV.4.6 | `completion_supportedDualizingModule_iff`, `SupportedDualizingModule.completion`, `SupportedDualizingModule.completionAddEquiv` (`CompletionHomDuality.lean`, `CompletionDualizingTransfer.lean`, `SupportedDualityTransport.lean`) | Restriction and `⊗ Â` preserve dualizing modules, matching Hom modules and canonical evaluations; `x ↦ 1 ⊗ x` identifies the groups underlying `I` and `Î`. |
| IV.4.7 | `nonempty_moduleInjectiveEnvelope`, `ModuleInjectiveEnvelope.exists_iso` (`EssentialModuleExtensions.lean`); `supportedDualizingModule_iff_injective_essential_residue`, `exists_supportedDualizingModule`, `SupportedDualizingModule.nonempty_iso` (`LocalInjectiveEnvelopes.lean`) | Injective envelopes exist (two Zorn arguments) and are unique up to isomorphism over the base. (c) Dualizing iff injective essential extension of `k` (support derived via IV.2.2); (a) and (b) follow. |
| IV.4.9 | `SupportedDualizingModule.locallyArtinian` (`LocalInjectiveEnvelopes.lean`); `supportedFunctorColimit_locallyArtinian`, `supportedFunctorColimit_annihilator_isFiniteLength`, `supportedFunctorAnnihilatorFiltrationIsColimit` (`SupportedLocallyArtinian.lean`, `SupportedFunctorAnnihilatorStages.lean`, `AnnihilatorFiltrationColimit.lean`) | Dualizing modules are locally Artinian. With `R/J` Artinian, `colim T(R/Jⁿ)` is locally Artinian. For left-exact `T` the stage maps identify `T(R/Jⁿ)` with its `Jⁿ`-annihilators, of which it is the colimit; they have finite length if `T` satisfies IV.3.1(i). |
| IV.5, anti-equivalence | `supportedFunctorAntiEquivalence` (`SupportedFunctorAntiEquivalence.lean`) | `T` satisfying IV.3.1(i) is an anti-equivalence of `𝒞_Y`, with counit the inverse of canonical evaluation. |
| IV.5, orthogonality | `supportedHomOrthogonalOrderIso`, `supportedFunctorOrthogonalOrderIso`, `mem_supportedFunctorOrthogonalOrderIso` (`SupportedHomOrthogonality.lean`); `supportedFunctorOrthogonal_length_eq_colength`, `supportedFunctorOrthogonal_colength_eq_length` (`HomOrthogonalLength.lean`) | Same `T`. Orthogonality through `φ_T` is an order-reversing bijection between submodules of `M` and of `T(M)`; `long N = colong N′` and `colong N = long N′`, infinite lengths included. |
| IV.5, monogenic modules | `supportedFunctor_monogenic_iff_socle_length_le_one`, `localSocle_eq_sSup_simple` (`LocalMonogenicCriterion.lean`, `LocalSocleDuality.lean`) | Same `T`, local `R`: `M` has one generator (zero included) iff the socle of `T(M)` has length ≤ 1. The socle, the `𝔪`-annihilator, is the sum of the simple submodules. |
| IV.5, Artinian ring | `artinianLocalHomIdealOrderIso`, `mem_artinianLocalHomIdealOrderIso` (`ArtinianLocalIdealDuality.lean`) | Artinian local `R`, `H` injective with `Hom(k, H) ≅ k`: `𝔞 ↦` annihilator of `𝔞` in `H` reverses order and is a bijection from ideals to submodules (every module is supported at `𝔪` here). |
| IV.5, `DA ≃ DÂ` | `matlisCompleteCompletionEquivalence` (`MatlisCompleteCompletion.lean`) | Adic completion and restriction: `DA(R) ≌ DA(Â)`, with unit the completion map. |
| IV.5.1, categories | `MatlisArtinianModuleCat`, `MatlisCompleteModuleCat`, `matlisCompleteFiniteEquivalence` (`MatlisCategories.lean`) | `I` is a dualizing module. `CA`: locally Artinian with finite socle. `DA`: `𝔪`-adically complete with every `M/𝔪ⁿ⁺¹M` of finite length; for complete `R`, the finite modules. |
| IV.5.1, complete `R` | `matlisCompleteAntiEquivalence`, `matlisCompleteCategoryAntiEquivalence` (`MatlisCompleteDuality.lean`) | `Hom(-, I)` both ways: `CA(R)ᵒᵖ ≌ FGModuleCat R` and `≌ DA(R)`, with unit and counit built from the two canonical evaluations. |
| IV.5.1, proof | `finiteBidualCompletionIso`, `finiteBidualCompletionIso_evaluation` (`MatlisBidualCompletion.lean`); `homDualCompletionIso_hom`, `SupportedDualizingModule.supported_dual_isAdicComplete`, `matlisHomToComplete` (`MatlisDualComplete.lean`, `MatlisFiniteDual.lean`); `homIdealAnnihilatorQuotientIso` (`HomAnnihilatorQuotient.lean`); `supportedAnnihilatorFiltrationIsColimit` (`SupportedAnnihilatorColimit.lean`) | For finite `M`, `Hom(Hom(M, I), I)` is the adic completion, evaluation being the completion map. For `X` in `CA`, `Hom(X, I)` is in `DA`. Restriction of `Hom(X, I)` to the `𝔞`-annihilator (`I` injective, `𝔞` finitely generated) is onto with kernel `𝔞·Hom(X, I)`. Supported modules are colimits of their power annihilators. |
| IV.5.1, inputs | `maximalIdealAnnihilator_isFiniteLength_of_finite_socle` (`FiniteSocleAnnihilators.lean`); `finite_of_isHausdorff_of_finite_reduction` (`CompleteFiniteModules.lean`); `SupportedDualizingModule.exists_hom_apply_ne_zero`, `SupportedDualizingModule.isIso_of_moduleHomDual_map`, `SupportedDualizingModule.moduleBidualEvaluation_isIso_of_dual` (`SupportedHomCogenerator.lean`); `EssentialIn.localSocle_le`, `EssentialModuleMap.localSocleMap_surjective`, `EssentialModuleMap.localSocle_finite`, `localSocle_finite_of_injective` (`EssentialSocles.lean`) | Finite socle gives finite-length `𝔪ⁿ`-annihilators. Topological Nakayama: over complete `R`, Hausdorff `M` with `M/𝔪M` finite is finite. A dualizing `I` cogenerates all modules; `Hom(-, I)` reflects isomorphisms and reflexivity. Essential embeddings are bijective on socles; finite socle passes to submodules. |
| IV.5.1, completed ring | `matlisArtinianCompletionEquivalence`, `completionSocleRestrictionEquiv` (`MatlisArtinianCompletion.lean`); `adicCompletion_isNoetherianRing` (`NoetherianCompletion.lean`); `matlisCompletedRingAntiEquivalence` (`MatlisCompletedRingDuality.lean`); `matlisCompletedRingHomIso` (`MatlisCompletedHomComparison.lean`) | `⊗ Â` and restriction give `CA(R) ≌ CA(Â)`, with equal socles. Adic completions of noetherian rings are noetherian (any ideal). `CA(R)ᵒᵖ ≌ FGModuleCat Â` by scalar change and `Hom_Â(-, Î)`; after restriction its forward functor is naturally `Hom_R(-, I)`. |
| IV.5.1 | `matlisAntiEquivalence` (`MatlisDuality.lean`); `matlisDualityForwardCompletionIso`, `matlisDualityInverseCompletionIso` (`MatlisDualityTransport.lean`) | Noetherian local `R`, not necessarily complete: `CA(R)ᵒᵖ ≌ DA(R)` with forward functor `Hom_R(-, I)` (definitionally) and inverse completion, `Hom_Â(-, Î)`, restriction; the unit is not identified with canonical evaluation. Transported to `Â`, both functors are naturally `Hom_Â(-, Î)`. |
| IV.5.1, finite length | `matlisFiniteLengthIntersectionEquivalence`, `finiteLength_matlisHomToComplete` (`MatlisFiniteLengthIntersection.lean`) | Finite modules in `CA` are the finite-length modules; both Hom functors and their evaluations restrict to the finite-length duality. |
| IV.5.1, `CA` | `matlisArtinianModuleProperty_iff_isArtinian` (`HomArtinianCriterion.lean`, `CompletionArtinian.lean`, `MatlisArtinianModules.lean`) | `CA` is the category of Artinian modules (orthogonals embed submodule lattices; `R`- and `Â`-submodules of supported modules agree). |
| IV.5.2 | `macaulayFunctor_duality`, `macaulayModule_supportedDualizing`, `macaulayFunctorRepresentationIso`, `coefficientField_finrank_eq_residueDegree_mul_length` (`CoefficientFieldDuality.lean`, `MacaulayDualizingFunctor.lean`, `MacaulayDualizingModule.lean`) | `A` noetherian local, `K → A` a field, `[k : K]` finite (`A` need not be finite over `K`): `dim_K M = [k : K]·long M`, and `Hom_K(-, K)` is dualizing, represented by the dualizing module `A' = colim Hom_K(A/𝔪ⁿ, K)` (`macaulayModule`). |
| IV.5.2, topological dual | `continuous_linearForm_adic_iff`, `macaulayModuleIsoContinuousDual` (`MacaulayContinuousDual.lean`) | A `K`-linear form on `A` is `𝔪`-adically continuous iff it kills some `𝔪ⁿ`; `A'` is the continuous dual. `A` need not be complete. |
| IV.5.3, parameters | `regularLocal_isDomain` (`ExposeIII/RegularLocalDomain.lean`); `regularLocal_exists_regular_parameters`, `regularLocal_isRegular_of_minimal_generating_list` (`ExposeIII/RegularLocalRegularSequence.lean`); `koszulProjectiveResolution`, `koszulExtComparisonIsoOfIsRegular` (`ExposeII/KoszulRegularResolution.lean`) | Regular local rings are domains; minimal generating lists of `𝔪` are regular sequences of length `dim R`. Over a noetherian local ring the Koszul complex of a regular sequence is a projective resolution, and the finite-stage Ext comparison is an isomorphism in every degree, natural in the coefficient. |
| IV.5.3, `Extⁱ(k, R)` | `koszulTopCohomologyIsoQuotient` (`ExposeII/KoszulTopCohomology.lean`); `regularLocal_topResidueModuleExtIso` (`RegularLocalTopExt.lean`); `regularLocal_residueField_projectiveDimension`, `regularLocal_moduleExt_ring_isZero_of_finiteLength` (`RegularLocalExtVanishing.lean`) | Top Hom–Koszul cohomology is the coefficient quotient (any ring and list). `Extⁿ(k, R) ≅ k` as `R`-modules, depending on the ordered parameters; `pd k = n`; `Extⁱ(M, R) = 0` for `i ≠ n` and `M` of finite length. |
| IV.5.3, depth | `regularLocal_depth_eq`, `regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator` (`RegularLocalDepth.lean`) | `depth R = n`; `Extⁱ(M, R) = 0` for `i < n` whenever a power of `𝔪` kills `M`. |
| IV.5.3, global dimension | `finite_hasProjectiveDimensionLE_of_residueField`, `regularLocal_finite_hasProjectiveDimensionLE` (`ExposeV/FiniteProjectiveDimension.lean`); `injective_of_cyclic_ext_one`, `hasInjectiveDimensionLE_of_cyclic_ext`, `hasProjectiveDimensionLE_of_cyclic_bound`, `moduleGlobalDimension_eq_residueField`, `regularLocal_moduleGlobalDimension_eq`, `regularLocal_ext_subsingleton_of_gt`, `regularLocal_moduleExt_isZero_of_gt` (`ExposeV/GlobalProjectiveDimension.lean`) | Noetherian local `R`: global dimension `= pd k`, possibly infinite (induction on support dimension; Baer and injective dimension shifting, valid over any ring). Regular `R`: it is `n`, and `Extⁱ(M, N) = 0` for `i > n` and all `M`, `N`. |
| IV.5.3, Ext models | `moduleExtAddEquivAbelianExt` (`ModuleExtDerivedComparison.lean`); `moduleExtLinearIsoAbelianExt` (`ModuleExtDerivedLinear.lean`); `moduleExtLinearIsoAbelianExt_naturality_first`, `moduleExtLinearIsoAbelianExt_naturality_coefficient` (`ModuleExtDerivedNaturality.lean`, `ModuleExtDerivedCoefficientNaturality.lean`) | Any ring: mathlib's module-valued `Ext` and the derived-category `Abelian.Ext` are `R`-linearly isomorphic, naturally in both variables. The IV.5.3 results hold for both. |
| IV.5.4 | `regularLocalTopExtFunctor_exact`, `regularLocalTopExtRepresentationIso`, `regularLocalTopExtModule_injective` (`RegularLocalExtFunctor.lean`); `regularLocalTopExtFunctor_duality`, `regularLocalTopExtModule_dualizing` (`RegularLocalExtDuality.lean`) | `n = dim R`: `Extⁿ(-, R)` is exact and dualizing on `𝒞_𝔪`, represented by the injective dualizing module `I = colim Extⁿ(R/𝔪ʳ, R)`. |
| IV.5.4, `I ≅ Hⁿ_𝔪(R)` | `regularLocalTopExtModuleIsoLocalCohomology`, `regularLocal_localCohomology_dualizing`, `regularLocalTopExtLocalCohomologyRepresentationIso` (`SupportedExtDiagram.lean`, `RegularLocalCohomologyComparison.lean`, `RegularLocalCohomologyDuality.lean`) | `I ≅ Hⁿ_𝔪(R)` (mathlib's `localCohomology`), compatibly with the stage maps; `Hⁿ_𝔪(R)` is dualizing and represents `Extⁿ(-, R)`. |
| IV.5.4, footnote | `regularLocalTopExtModuleIsoSupportedCohomology` (`RegularLocalCohomologyComparison.lean`) | As an abelian group, `I` is `H_Z` (the Ext model of I.2.3 bis) of the structure sheaf of `Spec R`, `Z` the closed point. Module structures are not compared. |
| IV.5.5, first sentence | `regularLocal_localCohomology_nonempty_iso_macaulay` (`RegularMacaulayComparison.lean`) | `R` regular local, `K → R` a field, `[k : K]` finite, `R` not necessarily complete: `Hⁿ_𝔪(R) ≅ A'`, noncanonically. |
| IV.5.5, Koszul colimit | `koszulTopCohomologyRing_transition_add_apply`, `koszulTopCohomologyRing_transition_monomial` (`ExposeII/KoszulTopTransition.lean`); `koszulTopQuotientDiagram`, `koszulTopQuotientColimitIsoLocalCohomology` (`ExposeII/KoszulTopQuotientColimit.lean`) | Any ring: the top Koszul transition `I_r → I_{r+s}` is multiplication by `(x₁⋯xₙ)ˢ`, so `e^r_a ↦ e^{r+s}_{a+s}`. Noetherian ring, any list, any `M`: `colim_r M/(x₁ʳ, …, xₙʳ)M ≅ Hⁿ_{(x)}(M)`, compatibly with stage maps. |
| IV.5.5, power series | `powerSeriesPowerQuotientBasis_apply_prod`, `powerSeriesPowerQuotient_finrank` (`PowerSeriesPowerQuotientBasis.lean`); `powerSeriesPowerQuotientResidue_mul_complement`, `powerSeriesPowerQuotientResidueEquiv` (`PowerSeriesResiduePairing.lean`) | `A = K[[x₁, …, x_d]]` (`MvPowerSeries (Fin d) K`): the `e^r_a` with `0 ≤ aᵢ < r` are a `K`-basis of `I_r`, so `dim I_r = r^d` (`d = 0`, `r = 0` included); for `r ≥ 1`, `(f, g) ↦ ρ_r(fg)` is a perfect pairing. |
| IV.5.5, `v` and `ρ` | `powerSeriesLocalCohomologyIsoMacaulay`, `powerSeriesLocalCohomologyIsoContinuousDual_stage_apply` (`PowerSeriesCoordinateIdeals.lean`, `PowerSeriesResidueContinuous.lean`, `PowerSeriesResidueColimit.lean`, `PowerSeriesLocalCohomologyResidue.lean`); `powerSeriesLocalCohomologyResidue_basis`, `powerSeriesLocalCohomologyResidue_smul`, `powerSeriesLocalCohomologyResidue_nondegenerate`, `powerSeriesTopLocalCohomology_supportedDualizing` (`AdicContinuousDualEvaluation.lean`, `PowerSeriesResidueDuality.lean`) | Same `A`; the coordinates generate `𝔪`. The `ρ_r` glue to an `A`-linear isomorphism `v : H^d_𝔪(A) → A'` sending `f ∈ I_r` to `a ↦` (coefficient of `(x₁⋯x_d)^{r-1}` in `fa`), constructed as a colimit map, not from uniqueness. The `K`-linear residue form `ρ` has `ρ(e^r_a) = 1` if every `aᵢ = r - 1` and `0` otherwise, `v(x)(a) = ρ(ax)`, and `(a, x) ↦ ρ(ax)` is nondegenerate. `H^d_𝔪(A)` is dualizing through `v`. |

### Open

- **IV.4.8:** the reduction of the computation of dualizing modules to regular local rings,
  which needs Cohen's structure theorem (a complete noetherian local ring is a quotient of a
  regular local ring). `adicCompletion_isNoetherianRing` presents `Â` as a quotient of a power
  series ring over `R`, not over a field.
- **IV.5.5,** for a complete regular local ring `A` of equal characteristic: a coefficient field
  `K`; the isomorphism `A ≅ K[[T₁, …, Tₙ]]` given by a system of parameters, hence `v` for such
  `A` (`v` is proved for `K[[x₁, …, x_d]]` with its coordinates); the completed differentials
  `Ωⁿ(A/K)`, their basis `dx₁ ∧ … ∧ dxₙ` and `u : Hⁿ_𝔪(Ωⁿ) → Hⁿ_𝔪(A)`; independence of
  `w = vu` from the parameters and its compatibility with change of base field. The
  correspondence between `A`-linear maps `M → A'` and `K`-linear forms on `M` continuous on
  finitely generated submodules is proved only as `v(x)(a) = ρ(ax)` for `M = H^d_𝔪(K[[x₁, …, x_d]])`.

## SGA 2, Exposé V — Local duality and structure of the `Hⁱ(M)`

Entry point: `lean/SGA/SGA2/ExposeV.lean`; files below are in `lean/SGA/SGA2/ExposeV/` unless prefixed.

`Hⁱ_J(M)` is mathlib's `localCohomology J i`, the colimit of `Extⁱ(R/Jᵏ, M)`, indexed by `ℕ`; SGA's
vanishing for `i < 0` is therefore a convention, and negative shifts in V.3.5–V.3.6 impose no
condition. `D` is `moduleHomDual D` for a `SupportedDualizingModule D` (Exposé IV). SGA's differential
`d(h) = h∘d₁ + (-1)^(s+1) d₂∘h` is `sourceHomComplex`; names starting `source` use it, the others use
mathlib's `HomComplex` ("standard"). V.3.2 uses module sheaves on ringed spaces and the module-valued
derived functors `derivedModuleGammaZSections` of `Γ_Z`.

### Proved

**§1.** `(1.3)`–`(1.5)`, `(6)`, `(8)`–`(9)`, `(12)` are displayed formulas of §1.

| SGA 2 V | Lean | Content |
| --- | --- | --- |
| V.1.1–V.1.2 | `sourceHomδ_v`, `sourceHomδ_comp`, `sourceHomComplexIso`, `sourceHomSign_smul_comp`, `sourceHomLeftHomologyData`, `sourceHomologyComp_mk`, `sourceHomologyAddEquiv_comp` (`SourceHomComplex*.lean`) | `d² = 0`; Leibniz, cocycle and homotopy formulas; cohomology is unscaled cocycles modulo coboundaries; isomorphic to the standard complex (signs below) |
| V.1.1, exact sequences | `homComplexContravariantSequence_shortExact`, `homComplexContravariant_exact₁`–`₃`, `sourceHomContravariantSequence_shortExact`, `sourceHomContravariant_exact₁`–`₃`, `sourceHomContravariantδ_naturality`, `homComplexCovariantSequence_shortExact`, `homComplexCovariant_exact₁`–`₃`, `sourceHomCovariantSequence_shortExact`, `sourceHomCovariantδ_naturality` | natural long exact sequences in every integer degree, both differentials: in the first variable into a degreewise-injective complex, no splitting assumed; in the second from any complex, when the first coefficient is degreewise injective |
| V.1.1, boundaries | `connectingConeCocycle_postcomp`, `homCocycle_connecting_eq_derived`, `sourceHomCocycle_connecting_eq_derived`, `homComplexContravariantδ_mk`, `homComplexContravariantδ_compare`, `sourceHomContravariantδ_compare`, `homComplexCovariantδ_compare`, `sourceHomCovariantδ_compare` | lift-and-differentiate is the derived connecting morphism, through a mapping-cone cocycle; first variable into a degreewise-injective K-injective target, second with K-injective end coefficients |
| `(1.3)` | `homComplexPrecomp_quasiIso`, `sourceInjectiveHomAugmentation_f`, `injectiveHomologyExtAddEquiv`, `sourceInjectiveHomologyExtAddEquiv`, `injectiveHomologyExtAddEquiv_precomp`, `injectiveHomologyExtAddEquiv_postcomp`, with `source` and `_modelChange` variants (`InjectiveHomComplexExt.lean`, `InjectiveHomExtNaturality.lean`, `InjectiveHomModuleExtModelChange.lean`) | the Hom complex of two injective resolutions computes `Ext` through the augmentation (precomposing with a quasi-isomorphism preserves cohomology into a K-injective target); natural in both variables and independent of the resolutions, also for module-valued `Ext` |
| `(1.4)` | `homClassComp_mk`, `homClassComp_assoc`, `homologyComp`, `sourceHomologyComp`, `homologyComp_naturality_first`, `homologyComp_naturality_middle`, `homologyComp_naturality_last`, `sourceHomologyComp_naturality_first`, `sourceHomologyComp_naturality_middle`, `sourceHomologyComp_naturality_last` | composition of representatives is a biadditive, associative pairing on cohomology, natural in all three complexes in every degree |
| `(1.4)`, `(12)` | `homologyComp_connecting`, `sourceHomologyComp_connecting` | the pairing intertwines the two Hom boundaries (signs below); the defect `(12)` is the coboundary of a composite of lifts; only degreewise injectivity is needed |
| `(1.5)` | `injectiveHomologyExtAddEquiv_comp`, `sourceInjectiveHomologyExtAddEquiv_comp`, `extPairing_sequence_connecting`, `moduleExtPairing_naturality_middle` | `(1.3)` carries the product to Yoneda composition, which commutes with both `Ext` connecting maps; the module-valued pairing is natural in all three variables |
| `(6)` | `InjectiveResolutionSequence.ofShortExact`, `nonempty_injectiveResolutionSequence`, `injective_splitRow`, `InjectiveHorseshoe.rowResolution`, `InjectiveHorseshoe.compare`, `InjectiveHorseshoe.compare_augmentation`, `compareHomotopy`, `sequenceCompare_augmentation`, `InjectiveHorseshoe.homotopyFunctor`, `homotopyFunctor_map_eq`, `InjectiveRowResolution.change_trans`, `InjectiveRowResolution.change_naturality` (`InjectiveHorseshoe*.lean`) | with enough injectives, a short exact sequence has a degreewise split, augmented short exact sequence of injective resolutions, which resolves the short complex; maps lift compatibly with all arrows and augmentations, uniquely up to homotopy; changes of resolution are natural and satisfy the cocycle law |
| `(6)`, given resolutions | `injectiveResolutionNatHom`, `InjectiveResolutionSequence.rowResolution`, `InjectiveResolutionSequence.compare`, `InjectiveResolutionSequence.compare_augmentation`, `rowCompareHomotopy`, `InjectiveResolutionSequence.change_trans`, `InjectiveResolutionSequence.change_naturality` | the same for any given augmented resolution sequence |
| `(8)`–`(9)` | `InjectiveResolutionSequence.extClass_augmentation`, `injectiveHomologyExtAddEquiv_contravariantδ`, `injectiveHomologyExtAddEquiv_covariantδ`, `injectiveHomologyModuleExtAddEquiv_contravariantδ`, `sourceInjectiveHomologyModuleExtAddEquiv_covariantδ` and their opposite-convention variants; `InjectiveHorseshoe.covariantδ_compare_naturality`, `InjectiveHorseshoe.contravariantδ_compare_naturality`, `InjectiveResolutionSequence.covariantδ_compare_naturality`, `InjectiveResolutionSequence.contravariantδ_compare_naturality` with `source` variants | the connecting arrow of a resolution sequence is the extension class; `(1.3)` carries Hom boundaries to `Ext` boundaries in every degree, including zero and for module-valued `Ext`; both boundaries commute with comparison maps, no compatible map of resolutions assumed |
| `Ext` boundaries | `projectiveExtCocycle_comp_extClass`, `projectiveExtMk_comp_extClass`, `exists_projectiveExtBoundaryFormula`, `moduleCohomologyMk_δ`, `moduleExtLinearEquivAbelianExt_isoExt_inv_mk`, `moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ`, `extColimitYonedaBoundary_eq_signed_extColimitδ`, `localCohomologyYonedaBoundary_eq_signed_localCohomologyδ` | Yoneda composition with an extension class is signed lift-and-differentiate on projective-resolution representatives; every class has such lifts, giving a cocycle; module representatives map to their `extMk` classes; the same on `colim Ext` and `Hⁿ_J`; every degree, including zero |

**§2 and formula (22).** `R` is regular local of dimension `r` unless stated.

| SGA 2 V | Lean | Content |
| --- | --- | --- |
| V.2, (13)–(14) | `localDualityMap`, `localDualityMap_stage`, `localDualityNatTrans`, `localDualityMap_identity_evaluation`, `localDualityMap_ring_top_isIso` (`LocalDualityMap.lean`) | over any commutative ring, the quotient-`Ext` stages give a natural map `Hⁱ_J(M) → Hom(Ext^j(M,P), Hⁿ_J(P))`, `i + j = n`; for `M = P`, `j = 0`, evaluation at the identity class retracts it, and for `M = P = R` it is an isomorphism, every ideal and `n` |
| V.2.1 | `regularLocal_localCohomology_isZero_of_gt`, `regularLocal_localCohomology_ring_isZero_of_ne`, `regularLocal_topLocalCohomology_not_isZero`, `regularLocal_localDualityMap_top_isIso`, `regularLocal_localDualityTopNatIso`, `regularLocal_localDualityMap_isIso`, `regularLocal_localDualityNatIso` (`LocalDuality.lean`) | `Hⁱ(N) = 0` for `i > r`, every `N`; `Hⁱ(R) ≠ 0` iff `i = r`; the map is a natural isomorphism on finite modules for all `i + j = r` (degree `r` by right exactness and finite free covers, then descending induction) |
| (22) | `regularLocal_localCohomologyDualCompletionIso`, `regularLocal_localCohomologyDualCompletionIso_transpose`, `regularLocal_localDualityTransposeMap_isIso`, `regularLocal_localCohomologyDualIsoExt`, `regularLocal_localDualityTransposeNatIso` | `D(Hⁱ(M))` is the completion of `Ext^{r-i}(M,R)`, the transpose being the completion map; for complete `R` the transpose `Ext^{r-i}(M,R) → D(Hⁱ(M))` is a natural isomorphism on finite modules |
| (a)–(c) after (22) | `regularLocal_supportDim_le_iff_localized_vanishing`, `regularLocal_supportDim_le_iff_codimension_ge` | equivalent for any module, including zero, when `i + j = r`; codimension via structure-stalk dimensions |
| V.3.1(ii), `Ext` | `regularLocal_ext_localized_subsingleton_of_lt`, `regularLocal_ext_supportCodimension_ge`, `regularLocal_ext_supportDim_le` | `Ext^j(M,N)_p = 0` if `dim R_p < j`, so support codimension `≥ j` (empty support allowed) and support dimension `≤ r − j`; `M` finite, `N` arbitrary |

**V.3.1.** `R` is noetherian local, neither regular nor complete unless stated; `M` is finite of
dimension `n`; `D` is any supported dualizing module.

| SGA 2 V | Lean | Content |
| --- | --- | --- |
| (i) | `exists_localParameters`, `exists_localParameters_modulo`, `exists_moduleParameters`, `koszulTransition_comp_eq_zero_of_annihilating_prefix`, `stableKoszulCohomology_isZero_of_annihilating_prefix`, `localRing_localCohomology_isZero_of_gt_moduleDim` | `Hⁱ(M) = 0` for `i > n`: there are `n` parameters modulo `Ann M`, and after annihilating elements the Hom–Koszul transitions vanish above degree `n` |
| (i), any module | `localRing_localCohomology_isZero_of_gt` | `Hⁱ(N) = 0` for `i > dim R`, every `N` |
| (ii), Artinian | `FiniteResidueExt.injectiveEnvelope`, `FiniteResidueExt.cokernel_injectiveEnvelope`, `FiniteResidueExt.localCohomology_isArtinian`, `localRing_localCohomology_isArtinian`, `localRing_localCohomology_socle_finite`, `localRing_localCohomology_annihilator_isFiniteLength`, `localRing_localCohomology_dual_completeProperty`; regular case `regularLocal_localCohomology_isArtinian`, `regularLocal_localCohomology_socle_finite`, `regularLocal_localCohomology_annihilator_isFiniteLength`, `regularLocal_localCohomology_dual_completeProperty_of_dualizing` | `Hⁱ(N)` is Artinian if all residue `Ext` of `N` are finite, so for `N` finite (dimension shifting through injective envelopes); finite socle; annihilators of `mᵏ` of finite length; `D(Hⁱ(M))` lies in IV's complete category |
| (ii), finiteness | `localRing_completedLocalCohomologyDual_finite`, `localRing_localCohomology_dual_finite`, `regularLocal_completedLocalCohomologyDual_finite_of_dualizing` | the completion of `D(Hⁱ(M))` is finite over `R̂`; `D(Hⁱ(M))` is finite if `R` is complete |
| (ii), dimension | `localRing_completedLocalCohomologyDual_supportDim_le`, `completeLocal_localCohomology_dual_supportDim_le`, `powerTorsion_quotient_eq_bot`, `exists_regular_on_powerTorsion_quotient`, `localCohomology_powerTorsion_mkQ_isIso`, `localCohomology_linear` | the completed dual of `Hⁱ(M)` has dimension `≤ i` over `R̂`, and so has `D(Hⁱ(M))` if `R` is complete; induction through a regular element on `M` modulo its `m`-power torsion, whose projection is an isomorphism on `Hⁱ`, `i > 0`; scalars on `M` act as scalars on `Hⁱ(M)` |
| (iii) | `localRing_topLocalCohomology_nontrivial`, `localRing_completedTopLocalCohomologyDual_supportDim_eq`, `completeLocal_topLocalCohomology_nontrivial`, `completeLocal_topLocalCohomology_dual_supportDim_eq` | `Hⁿ(M) ≠ 0`; its completed dual has dimension `n` over `R̂`; for complete `R` (or `dim R = 0`), `dim D(Hⁿ(M)) = n` |
| (iii), `Ass` | `supportedLocalCohomologyFunctor_preservesFiniteColimits`, `supportedTopLocalCohomologyDual_isZero_iff`, `localRing_topLocalCohomologyDual_associatedPrimeSpectrum` | `Hⁿ` is right exact on finite modules supported in dimension `≤ n`, and `D(Hⁿ(M')) = 0` iff `Supp M'` misses the generic points of the top-dimensional components; so `Ass D(Hⁿ(M)) = {p ∈ Ass M : dim R/p = n}`, without completeness (by V.3.3, III.1.3, `additiveFunctorModuleLiftIsoOfLinear`) |

**V.3.2.** `f : X → Y` is any morphism of ringed spaces, `Z ⊆ Y` closed, `X' = f⁻¹(Z)`, `f̄ : Γ(Y,𝒪_Y) → Γ(X,𝒪_X)`; no flatness.

| SGA 2 V | Lean | Content |
| --- | --- | --- |
| inputs | `moduleGammaZSectionsFunctor`, `moduleGammaZSectionsForgetIso`, `moduleToSheaf_map_shortExact`, `moduleIsFlasque_of_injective`, `derivedModuleGammaZSections_isZero_of_isFlasque`, `derivedModuleGammaZSections_isZero_pushforward_injective` | `Γ_Z(U, −)` is `𝒪(U)`-linear and forgets to Exposé I's functor; forgetting scalars is exact; injective module sheaves are flasque; higher `Γ_Z` vanishes on flasque sheaves and on `f_*` of injectives |
| (16)–(17) | `ringedModulePushforwardSupportedGlobalIso`, `ringedModuleSupportedGlobalRightDerivedIso`, `gammaZSections_quasiIso_of_boundedBelow_flasque`, `derivedModuleGammaZSectionsForgetIso`, `derivedModuleGammaZSectionsIsoH_Z`, `moduleUnderlyingComplexGlobalScalarRingHom`, `moduleUnderlyingDerivedGlobalScalarRingHom` | `Γ_Z ∘ f_*` and its derived functors are `Γ_{X'}`-cohomology with scalars restricted along `f̄`; forgetting scalars gives Exposé I's `derivedGammaZSections` and the Ext model `H_Z` of I.2.3 bis, naturally; the global ring acts on the underlying complexes and derived objects, compatibly with cochain maps |
| (15), E₂ | `ringedModulePushforwardAdditiveSpectralSequence`, `ringedModulePushforwardAdditiveSpectralSequenceE2Equiv`, `ringedModulePushforwardE2ModuleAddEquiv`, `spectralObjectModuleLift`, `ringedModulePushforwardModuleSpectralSequence`, `ringedModulePushforwardModuleSpectralSequenceForgetIso`, `ringedModulePushforwardModuleE2LinearEquiv`, `ringedModulePushforwardModuleE2LinearEquiv_toAddEquiv` | pages and differentials are `Γ(Y,𝒪_Y)`-linear and forget to the additive spectral sequence; `E₂^{p,q} ≅ H^p_Z(Y, R^q f_* F)` linearly; no commutativity assumed |
| abutment | `ringedModulePushforwardModuleSpectralObject_isFirstQuadrant`, `ringedModulePushforwardSpectralFiniteFiltration`, `ringedModulePushforwardModuleStablePageIsoGraded`, `flasqueGammaComplexDerivedHomEquiv`, `ringedModulePushforwardSpectralAbutmentLinearEquiv`, `ringedModulePushforwardSourceFiniteFiltration` | first quadrant; for `r ≥ n + 2`, `E_r` in total degree `n` is the graded of a finite exhaustive filtration of `Hⁿ_{X'}(X, F)_{[f̄]}` |
| functoriality | `ringedModulePushforwardModuleSpectralSequenceFunctor`, `ringedModulePushforwardModuleSpectralSequenceCoefficientMap_E2`, `ringedModulePushforwardSpectralTotalCoefficientMap_abutment`, `ringedModulePushforwardModuleSpectralSequenceCoefficientMap_add`, `ringedModulePushforwardModuleSpectralSequencePageFunctor_additive`, `ringedModulePushforwardModuleSpectralSequenceResolutionIso_naturality`, `ringedModulePushforwardModuleStablePageIsoGraded_naturality`, `ringedModulePushforwardSourceFiniteFiltration_map_le`, `ringedModulePushforwardSourceFiniteFiltration_eq` | additive and functorial in `F`, independent of lifts, compatible with the E₂ and abutment identifications; changes of resolution are natural with the cocycle law; coefficient maps preserve the filtration, which does not depend on the resolution |

**V.3.3–V.3.6.**

| SGA 2 V | Lean | Content |
| --- | --- | --- |
| V.3.3 | `supportedFunctorColimit_associatedPrimeSpectrum_eq`, `supportedFunctorColimit_associatedPrimeSpectrum_eq_of_components`, `supportedFunctorColimit_associatedPrimes_of_irreducibleComponents` | if left-exact `T` vanishes exactly on modules whose support contains none of the chosen irreducible components of `V(J)`, the associated primes of IV's representing module `supportedFunctorColimit` are the generic points of those components, which are constructed, not supplied |
| V.3.4 | `homeomorphismCohomologyFunctorIso`, `affineChartCohomologyEquiv`, `affineOpen_H_pos_subsingleton` (`ExposeIII/`), `localCohomology_isZero_of_affineComplement`, `localRing_ringKrullDim_le_one_of_affinePuncturedSpectrum`, `irreducibleComponent_codimension_le_one_of_affineComplement` | `R` noetherian: quasi-coherent modules are acyclic on affine opens, so `Spec R ∖ V(J)` affine gives `Hⁱ_J = 0` for `i ≥ 2`; a noetherian local ring with affine punctured spectrum has dimension `≤ 1`, by V.3.1(iii); every irreducible component of a closed set with affine complement has codimension (infimum of stalk dimensions) `≤ 1` |
| (19)–(21) | `koszulSystemBaseChangeIso`, `koszulHomComplexSystemScalarChangeIso`, `localCohomologyScalarChangeIso` (`ExposeII/`), `localRing_localCohomologyScalarChangeIso`, `localRing_localCohomology_length_eq_of_surjective`, `localRing_localCohomology_finiteLength_iff_of_surjective`, `surjectiveHomDualScalarChangeIso`, `surjectiveLocalCohomologyDualIso`, `restrictScalarsAnnihilatorQuotientEquiv`, `restrictScalars_finite_iff_of_surjective`, `restrictScalars_supportDim_of_surjective` | along any map of noetherian rings, Koszul systems and `Hⁱ` commute with change of rings, any coefficients, no flatness; for a surjection of local rings `B → A`: (19) `Hⁱ_{m_B}(M_{[f]}) ≅ Hⁱ_{m_A}(M)_{[f]}`, same length; (20) coinduction is dualizing and `D_A(M)_{[f]} ≅ D_B(M_{[f]})` naturally, also for duals of `Hⁱ`, once the dualizing modules are identified; (21) `B/Ann M_{[f]} ≅ A/Ann M`, so finiteness and dimension of `M` agree |
| V.3.5, duality and `Ext` | `SupportedDualizingModule.moduleHomDual_finiteLength_iff`, `SupportedDualizingModule.moduleHomDual_length` (`ExposeIV/MatlisFiniteLengthDetection.lean`), `finiteProjectiveResolution`, `localizedLinearYonedaObjIso`, `moduleExtLocalizationIso`, `moduleExtLocalizationRingIso`, `regularLocal_localCohomology_length_eq_ext`, `regularLocal_localCohomology_finiteLength_iff_ext_atPrime` | `D` detects finite length and preserves length on all modules, no completeness, and the bidual map is invertible when the dual has finite length; `Ext_R(M,N)_p ≅ Ext_{R_p}(M_p,N_p)`, `R_p`-linearly, for `M` finite and any `N` (also `N = R`); for regular `R`, `Hⁱ(M)` has the length of `Ext^{r-i}(M,R)` and finite length iff that `Ext` vanishes at every nonmaximal prime |
| V.3.5, localization | `localizedPrimeQuotientResidueFieldIso`, `localizedPrimeQuotientResidueFieldIso_hom_mk`, `regularLocal_atPrime_moduleGlobalDimension_le`, `isRegularLocalRing_of_residueField_bound`, `isRegularLocalRing_iff_residueField_projectiveDimension_ne_top`, `regularLocal_atPrime_isRegularLocalRing`, `regularLocal_isRegularRing`, `regularLocal_atPrime_moduleGlobalDimension_eq_ringKrullDim`, `regularLocal_top_associated_mem_ext_support`, `regularLocal_atPrime_dimension_add_quotient` | `(R/p)_p = κ(p)` and `gldim R_p ≤ dim R`; a noetherian local ring is regular iff its residue field has finite projective dimension; so each `R_p` of a regular local `R` is regular, of global dimension `dim R_p`, and `dim R_p + dim R/p = dim R` without assuming catenarity |
| V.3.5, quotients | `localRingHom_surjective`, `localizedRestrictScalarsIso`, `localizedRestrictScalarsIso_hom_mk`, `ringKrullDim_quotient_comap_of_surjective`, `localCohomologyAtPrimeScalarChangeIso`, `puncturedLocalCohomologyVanishing_iff_of_surjective`, `localCohomologyFiniteLengthCriterion_iff_of_surjective` | both conditions of V.3.5 are invariant under a surjection of local rings; primes outside the image contribute nothing |
| V.3.6, depth | `puncturedLocalCohomologyVanishing_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_criterion`, `puncturedDepthBound_iff_of_surjective` | any noetherian local ring: shifted vanishing through degree `n` is the depth bound (infinite depth allowed), so V.3.5 implies V.3.6; the bound is quotient-invariant |
| V.3.5–V.3.6 | `regularLocal_localCohomology_finiteLength_iff_punctured`, `localCohomology_finiteLength_iff_punctured_of_surjective`, `regularLocal_localCohomology_finiteLength_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_surjective` (`LocalCohomologyFiniteLengthCriterion.lean`) | `M` finite over a quotient of a regular local ring: `Hⁱ(M)` has finite length iff `H^{i − dim R/p}_p(M_p) = 0` at each nonmaximal prime `p`; finite length for all `i ≤ n` iff `depth M_p > n − dim R/p` there (the zero module has infinite depth) |

### Sign conventions

| Comparison | standard | SGA's differential |
| --- | --- | --- |
| complex isomorphism `sourceHomComplexIso`, degree `n` | — | `(-1)^(n(n+1)/2)` |
| product versus Yoneda composition | `1` | `(-1)^(ij)` |
| pairing versus the two Hom boundaries, `(12)` | `(-1)^(j+1)` | `(-1)^(i+1)` |
| first-variable Hom boundary versus derived connecting arrow | `(-1)^(n+1)` | `1` |
| second-variable Hom boundary versus derived connecting arrow | `1` | `(-1)^(n+1)` |
| `(1.3)`: Hom boundary versus `Ext` boundary, first / second variable | `(-1)^(n+1)` / `1` | same |

For SGA's differential the derived-arrow rows use the unscaled quotient equivalence and the `(1.3)`
row the scaled augmentation. The Yoneda coefficient boundary is `(-1)^(n+1)` times lift-and-differentiate
on unsigned projective representatives, in every degree, also on `colim Ext` and `Hⁿ_J`. SGA's unsigned
augmentation and pairing formulas, which are incompatible, are not asserted; Lean proves the signed forms above.

### Not formalized

Cohen's structure theorem, used in SGA's proof of V.3.1. Every part of V.3.1 is proved without it.

## SGA 2, Exposé VI — The functors `Ext^•_Z(X; F, G)` and `ℰxt^•_Z(F, G)`

Entry point: `lean/SGA/SGA2/ExposeVI.lean`; files below are in `lean/SGA/SGA2/ExposeVI/` unless prefixed.

Module sheaves are mathlib's `SheafOfModules R` over any ring sheaf; locally closed supports are
`ExposeI.LocallyClosedIn X`. `ℋom(F, G)` is `moduleSheafHomAb F G`, the abelian sheaf of local
module-linear maps (`moduleSheafHom` is the module-valued version over a commutative ring sheaf).
`Ext_Z(X; F, G)` and `ℰxt_Z(F, G)` are right derived functors in the category of module sheaves, valued
in abelian groups and sheaves (`moduleSupportedExtFunctor`, `moduleLocallyClosedSupportedExtFunctor`,
`moduleLocallyClosedSheafExtFunctor`).

### Proved

| SGA 2 VI | Lean | Content |
| --- | --- | --- |
| VI.1.1, `ℋom` | `moduleLocalHomOverEquiv`, `moduleSheafHomAbFunctor`, `moduleSheafHomAbGlobalEquiv` (`ModuleInternalHom.lean`, `ModuleInternalHomFunctor.lean`, `ModuleGlobalHom.lean`) | the local-linear part of the additive internal Hom is a sheaf, since linearity is local; sections over `U` are module maps over `U`; additive and left exact in `G`, contravariant in `F`; global sections are `Hom(F, G)` |
| VI.1.1, `Γ̲_Z` | `moduleGammaZSheafFunctor` (`ModuleSupportedSheaf.lean`) | closed `Z`: a left exact module sheaf whose underlying sheaf is Exposé I's kernel sheaf |
| VI.1.1, `Ext` | `ModuleSupportedExt.lean`, `ModuleSheafExtLinear.lean`, `ModuleLocallyClosedSheafExtLinear.lean` | `Ext_Z` and `ℰxt_Z` for closed and locally closed `Z`, with degree-zero comparisons and positive-degree vanishing on injectives; over a commutative ring sheaf, `ℰxt` and `ℰxt_Z` are module sheaves and `Ext_Z` a `Γ(X,𝒪_X)`-module, forgetting naturally to the additive versions |
| VI.1.2 | `moduleExtPresheafEvalIso`, `moduleLocallySupportedExtPresheafEvalIso`, `moduleLocallySupportedExtSheafificationIso` (`ModuleOpenRestriction*.lean`) | the value on `U` is `Ext` among module sheaves on `U`, ordinary or locally supported, and these presheaves sheafify to `ℰxt_Z`; restriction to an open, and between nested opens, is exact and preserves injectives |
| VI.1.3 | `VI_1_3` (`ModuleOpenRestrictionLocallyClosed.lean`) | excision in every degree for locally closed `Z` in an open `V`, natural in `G` |
| VI.1.4.1–2 | `VI_1_4_1` (`SupportObjectHom.lean`), `VI_1_4_2` (`TensorSupportHom.lean`), `LocallyClosedTensorSupportHom.lean` | commutative structure sheaf: `Γ_Z(ℋom(F,G)) ≅ Hom(𝒪_{X,Z}, ℋom(F,G)) ≅ Hom(𝒪_{X,Z} ⊗ F, G)`, sheafified tensor; closed `Z`, then every locally closed `Z`, natural in both variables |
| VI.1.4, `θ` | `moduleLocallyClosedSupportedExtTensorIso`, `moduleLocallyClosedSupportedExtTensorIso_precomp` (`TensorSupportExtNaturality.lean`) | `Extⁱ(𝒪_{X,Z} ⊗ F, G) ≅ Extⁱ_Z(X; F, G)` in every degree, locally closed `Z`, natural in `F` and `G` |
| VI.1.4.3 | `VI_1_4_3`, `moduleSupportedHomFunctorIso`, `moduleSupportedHomEquiv_precomp`, `moduleSupportedInternalHomFunctorIso`, `moduleSupportedExtViaSupportedSheafIso`, `moduleLocallyClosedSupportedHomFunctorIso` (`ModuleSupportedHom.lean`, `ModuleLocallyClosedSupportedHom.lean`) | `Γ_Z(ℋom(F,G)) ≅ Hom(F, Γ̲_Z(G))` through the factorization and inclusion maps, natural in both variables, with a sheaf form compatible with restriction; derived in every degree (a comparison of composites, not VI.1.6.3); also for locally closed `Z` |
| I.1.7, used in VI.1.4 | `ringedSpaceSupportHomEquiv` (`ExposeI/RingedSpaceSupportHom.lean`) | `Hom(𝒪_X, Γ̲_Z(F))` is the sections of `F` supported in closed `Z` |
| VI.1.5 | `ModuleOpenSubpresheaf.lean`, `ModuleHomInjectiveFlasque.lean`, `ModuleSupportedSheafInjective.lean`, `ModuleLocallyClosedSupportedSheafInjective.lean` | for injective `G`, local linear maps extend globally, so `ℋom(F, G)` is flasque with no positive closed or locally closed supported cohomology (forgetting scalars need not preserve injectives); `Γ̲_Z` preserves injectives (closed `Z` by a mono-preserving left adjoint; locally closed `Z` through closed support, restriction and direct image) |
| VI.1.6 | `VI_1_6_1_locallyClosed_spectralFunctor`, `VI_1_6_2_spectralFunctor`, `VI_1_6_3_locallyClosed_spectralFunctor` (`SpectralFunctors.lean`) | locally closed `Z`: spectral functors in `G` with E₂ terms `H^p_Z(X, ℰxt^q(F,G))`, `H^p(X, ℰxt^q_Z(F,G))`, `Ext^p(F, ℋ^q_Z(G))`, abutment `Ext_Z(X; F, G)`, and a finite filtration whose graded pieces are the stable pages |
| VI.1.6.3, naturality | `ModuleLocallyClosedSupportSpectralSequence.lean`, `ModuleLocallyClosedSupportSpectralNaturality.lean`, `ModuleEndofunctorSpectralAbutmentNaturality.lean` | the E₂ and abutment identifications are natural in `G` |
| VI.1.7 | `moduleNestedSupportObjectSequence_shortExact`, `moduleNestedTensorSupportSequence_shortExact` (`ModuleSupportObjectSequence.lean`, `TensorSupportObjectSequence.lean`, `SheafTensorFunctor.lean`, `ExposeI/RepresentedFunctorSequence.lean`) | (VI.1.7.1) and (VI.1.7.2) are short exact with SGA's maps: `Z` locally closed, `Z' ⊆ Z` closed, any `F` |
| VI.1.8 | `VI_1_8_exact`, `VI_1_8_sheaf_exact` (`SupportExactSequences.lean`, `LocallyClosedExtSequences.lean`, `LocallyClosedSheafExtSequences.lean`, `ExtSequenceFirstVariable.lean`) | the long exact sequences of `Ext` and of `ℰxt`, same hypotheses; degree-zero maps are inclusion and restriction of supported Hom; natural in `F` and `G` |
| VI.1.9 | `moduleRelativeExtRestriction_zero_standard`, `moduleRelativeExtRestriction_eq_functor` (`ModuleRelativeExtSequence.lean`, `ModuleRelativeExtCompatibility.lean`, `ExposeI/ExtRightDerivedMap.lean`) | exact `… → Extⁱ_Y(F,G) → Extⁱ(F,G) → Extⁱ(F_U,G_U) → Ext^{i+1}_Y(F,G) → …`, `U = X ∖ Y`; the restriction is `Hom` restriction in degree zero and the map of the exact restriction functor in every degree |
| VI.2.1, `ℋom` | `affineInternalHomIso` (`AffineInternalHom.lean`, `AffineInternalHomNaturality.lean`), `SchemeInternalHomRestriction.lean`, `coherent_internalHom_isQuasicoherent` (`CoherentInternalHom.lean`) | `ℋom(M~, N~) ≅ Hom_R(M,N)~` for finitely presented `M`, any commutative ring, natural in both; `ℋom` commutes with open restriction and is quasi-coherent for coherent `F`, quasi-coherent `G`, `X` locally noetherian |
| VI.2.1, degree 0, closed `Z` | `schemeModuleGammaZ_isQuasicoherent`, `coherent_closedSupportedHom_isQuasicoherent`, `coherent_closedSheafExtZero_isQuasicoherent` (`QuasiCoherentSupportedModules.lean`) | `X` locally noetherian: `Γ̲_Z` preserves quasi-coherence, so `Γ̲_Z ℋom(F,G)` and `ℰxt⁰_Z(F,G)` are quasi-coherent for coherent `F`, quasi-coherent `G` |
| VI.2.3, degree 0 | `adicQuotientHomTorsionIsColimit`, `adicQuotientHomColimitIsoPowerTorsion`, `adicQuotientHomColimitIsoPowerTorsion_ι`, `adicQuotientHomTorsionCocone_apply`, `VI_2_3_zero` (`AffineHomColimit.lean`) | `colim Hom_R(M/IⁿM, N)` is the `I`-power torsion of `Hom_R(M,N)` through the quotient maps; any commutative ring and modules; uses Exposé IV's quotient–annihilator identifications |
| VI.2.3, `F = 𝒪_X` | `VI_2_3_structure`, `VI_2_3_sheaf` (`AffineExtComparison.lean`) | `R` noetherian: `colimₙ Extⁱ(R/Iⁿ, N) ≅ Hⁱ_{V(I)}(Spec R, Ñ)` in every degree, natural in `N` (from II.6) |

### Open

- VI.1.2–VI.1.3: compatibility with the higher `Ext` restrictions between nested opens and with
  coefficient connecting maps.
- VI.1.4: compatibility of `θ` with the connecting maps in `F` and in `G`.
- VI.2.1: `ℰxtⁱ_Z(F, G)` for `i > 0`, and for `i = 0` when `Z` is not closed.
- VI.2.3 (a), (b) for general coherent `F`: `colim Ext(M/IⁿM, N) → Ext_Y(X; F, G)`.

## SGA 2, Exposé VII — Vanishing criteria; coherence of `ℰxtⁱ_Y(F, G)`

Entry point: `lean/SGA/SGA2/ExposeVII.lean`.

### Proved

- **VII.1.3, `X` locally noetherian**: `VII_1_3_locallyNoetherian` (`ExposeVII/HomDetection.lean`). If
  `P` is coherent, `H` quasi-coherent, `ℋom(P, H) = 0` and `Supp H ⊆ Supp P` (stalk supports,
  `schemeModuleSupport`), then `H = 0`.

### Open

- VII.1.3 without local noetherianity; VII.1.1–VII.1.2, VII.1.4–VII.1.7 and VII.2.1–VII.2.3.

## Axiom verification

Two scripts in `lean/`, run from that directory, collect the axioms each audited declaration depends on,
transitively, and fail on any axiom other than `propext`, `Classical.choice` and `Quot.sound` (so on
`sorryAx`, added mathematical axioms and native evaluation) or if they find no declarations. They check
axioms, not coverage of SGA.

- `lake env lean CheckSGA1Axioms.lean`: every declaration defined in a module under `SGA.SGA1` or
  `SGA.Foundations`, selected by module because the foundation files use mathlib namespaces.
- `lake env lean CheckSGA2Axioms.lean`: every declaration named in the `SGA.SGA2` namespace, including
  private ones, selected by name.
