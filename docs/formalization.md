# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1 and SGA 2.
Mathlib already has the language of the exposés; we import it and add
the statements that are still missing.

## SGA 1 — *Revêtements étales et groupe fondamental*

Entry points: the barrels `SGA.SGA1.ExposeI` … `SGA.SGA1.ExposeXIII` (there is no Exposé VII)
and `SGA.Foundations`, all imported by `lean/SGA.lean`. Each barrel's module docstring lists its
files and what they prove. The conventions for SGA 1 are in
[`lean/SGA/SGA1/CONVENTIONS.md`](../lean/SGA/SGA1/CONVENTIONS.md); they differ from the SGA 2
files and follow mathlib naming.

- Every declaration for a numbered item starts its docstring with the number
  (`/-- IX.4.12: … -/`) and says how it differs from SGA when it does (extra hypotheses, special
  cases, one direction).
- A numbered statement that is not proved is recorded as a faithful `Prop`-valued
  `…Statement` definition, and the consequences SGA draws from it are proved with it as a
  hypothesis.
- There is no `sorry`, `admit`, `native_decide` or custom axiom: from `lean/`,
  `lake env lean CheckSGA1Axioms.lean` checks every declaration of `SGA.SGA1.*` and
  `SGA.Foundations.*` and allows only `propext`, `Classical.choice` and `Quot.sound`.
- Prerequisites that mathlib does not have live in `lean/SGA/Foundations/` (mathlib namespaces
  and naming, references to EGA, SGA 4 and the Stacks Project). The results that are out of
  scope, and why, are listed in [`lean/SGA/Foundations/README.md`](../lean/SGA/Foundations/README.md).

### Coverage by exposé

| Exposé | State |
| --- | --- |
| I — Étale morphisms | Every numbered statement is proved. I.10.7–I.10.12 go through EGA IV 15.5.1 and the strict henselization (`GeometricPoints`); I.10.11 adds SGA's standing locally noetherian hypothesis. I.3.6 (iv) and I.4.7 are proved for base change along one projection only; I.3.1 is stated with global diagonals; I.7.9–I.7.10 (lemmas of the proof of I.7.6) and scheme forms of I.10.3–I.10.6 are not stated. |
| II — Smooth morphisms | Every recorded statement is proved. II.2.5 (Hironaka's criterion) and the sufficiency half of II.2.6 need multiplicity theory and are not stated. |
| III — Infinitesimal lifting | III.2.1 (without completeness), III.3.1–III.3.2 at scheme level, III.4, III.5.1–III.5.4 (Čech form over an affine base), III.5.8 for affine formal schemes, III.6.7 and III.6.10 when `X₀` is the union of two affine opens, III.6.8. III.7.4 is proved (`smoothProperCurveLiftStatement`). Not formalized: III.5.8 for non-affine formal schemes, III.5.9, III.6.3 in general, III.6.9, III.7.1–III.7.3. |
| IV — Flat morphisms | Every numbered statement is proved. |
| V — The fundamental group: generalities | Every numbered statement is proved. V.5.9 and V.5.11 are for small Galois categories, V.2.2 in ring form (`B` noetherian), V.8.2 for `Spec R`, V.9 for finitely many connected components. V.6.12 (second assertion) is false and not formalized. |
| VI — Fibered categories and descent | Every numbered statement is proved, on mathlib's fibered categories. |
| VIII — Faithfully flat descent | Every numbered statement is proved: VIII.6.4 over a noetherian base, as in SGA, the rest over an arbitrary base; ampleness and quasi-projectivity (VIII.5.8, VIII.7.7–VIII.7.8) use `SGA.Foundations.Projective`. |
| IX — Descent of étale morphisms | IX.1.2–IX.1.9, IX.2, IX.3 and IX.4.1–IX.4.11 are proved over any base, with no exception among IX.2.6, IX.4.6 and IX.4.9: IX.2.6 is proved in both directions (`universallySubmersiveValuativeCriterion`; `g` quasi-compact, SGA's finite-type hypothesis unused); IX.4.6 is proved in SGA's form (`isEffectiveIffStrictlyLocal`); IX.4.9 is proved (`quasiSectionStatement`, EGA IV 14.5.4). IX.1.10 is proved for `X` projective over `A` and for `X` integral and normal (as X.2.1, `ExposeX.isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`); its full faithfulness is proved for every proper `X` (`full_pullback_closedFibre`, `faithful_pullback_closedFibre`). IX.4.12 is proved over an arbitrary base (`effectiveDescentOfProperStatement`). IX.6.9 is proved in full. IX.5.6 (for proper coverings), IX.6.1 (fibre also quasi-separated), IX.6.2, IX.6.4, IX.6.7, IX.6.8 and IX.6.11 are proved; IX.6.8 and IX.6.11 hold over an arbitrary base (`properDescentStatement`, `geometricFibresStatement`). IX.5.2 for a descent morphism `g` with `S'` and `S''` connected is proved only in the abstract form of Galois categories (`DescentDiagram.DiagonalPoint.exists_finite_topologicalClosure_eq_top`). For schemes, IX.5.2 is proved without IX.5.1, with `S'` and `S''` possibly disconnected, when `S` is noetherian and connected and `g` is proper and surjective instead of an effective descent morphism (`isTopologicallyFG_etaleFundamentalGroup_of_isProper_of_surjective`). Of IX.5.4 (pinching), only the consequence "`π₁(S')` is topologically finitely generated if `π₁(S)` is" is proved, under hypotheses that replace SGA's: `g` proper and surjective, `S` locally noetherian, `S'` connected, everything over a separably closed field `k`, the points of `S' ×_S S'` off the diagonal finitely many and closed, `S' ×_S S' ×_S S'` with finitely many connected components, all of these carrying `k`-points (`isTopologicallyFG_etaleFundamentalGroup_of_pinching`). These hold for a finite surjective morphism onto a scheme of finite type over an algebraically closed field that is an isomorphism off finitely many closed points (`isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict`), for example the normalization of a curve (`isTopologicallyFG_etaleFundamentalGroup_normalization_of_isTopologicallyFG`). IX.5.8 is formalized in its group-theoretic form only; IX.6.5 is stated (`LocalProperDescentStatement`). Not formalized: IX.5.1 when `S'` or `S''` is not connected, IX.5.3, IX.5.4 itself, IX.5.5 and IX.5.7 (profinite presentations), IX.6.3, IX.6.6 (except for an étale covering over `Spec 𝒪̂_{S,s}`, a step of the proof of IX.6.7, `exists_isActAt_fromSpecCompletedStalk`), IX.6.10 and IX.6.12. |
| X — Specialization of the fundamental group | X.1.1–X.1.5 and X.1.7–X.1.10 are proved (X.1.2 through EGA III 7.8.10 in `SGA.Foundations.Cohomology`; X.1.7 for a rational base point and `X` reduced, `bijective_map_prod`). X.2.1–X.2.4 are proved for `X` projective over the base, and for `X` proper from IX.1.10; X.2.1 also for `X` integral and normal (`isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`); X.2.2–X.2.3 also over a complete local base. X.2.9 and X.2.12 are proved for every proper connected `X` over an algebraically closed field `k` of characteristic 0 with `#k ≤ 𝔠`, in universe 0, without the Riemann existence theorem (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`, `finite_principalH1_of_mk_le_continuum`). In every characteristic, X.2.9 is reduced to normal proper curves and to the hyperplane step X.2.10 in an existence form (`topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`), and X.2.12 follows from X.2.9 (`finite_principalH1_of_topologicallyFiniteStatement`); what is missing is listed in the Foundations README. X.3.1–X.3.4 (Zariski–Nagata purity in every dimension) and X.3.6 are proved. For `f` proper and smooth with geometrically connected fibres over the spectrum `Y` of a complete discrete valuation ring with separably closed residue field, `y₀` closed and `y₁` generic, X.3.8 (`exists_tameSpecialization_of_isDiscreteValuationRing`) and X.3.9 (`exists_primeToQuotientEquiv_of_isDiscreteValuationRing`; an isomorphism in residue characteristic 0, `exists_bijective_specialization_of_isDiscreteValuationRing`) are proved, from the core of X.3.8, the case to which SGA reduces it in X.3.7 (`tameLiftingDVRStatement`). For a general `Y`, X.3.9 follows from X.3.8 (`exists_primeToQuotientEquiv_of_tameSpecialization`), which is open. Not stated: X.1.6, X.2.5–X.2.8, X.2.10–X.2.11, X.2.13–X.2.14, X.3.5, X.3.7, X.3.10–X.3.11. |
| XI — Examples and complements | XI.1.1 (`ℙʳ` simply connected, all `r`), XI.1.2 and XI.1.3 in SGA's form (proper normal `X`, from purity X.3.3 and XI.1.1: `rationalSimplyConnectedStatement`, `unirationalFiniteFundamentalGroupStatement`), XI.2 (`π₁` of a proper connected reduced group scheme over an algebraically closed field is commutative, `mul_comm_of_monObj`), XI.4–XI.6 (torsors, non-abelian `H¹`, `H¹(S, G) ≅ H¹(π₁, G(s̄))` for finite étale `G`, Kummer and Artin–Schreier theory, `Pic`). The key step of XI.2.1 (Serre–Lang: every connected étale covering of an abelian variety is dominated by multiplication by some `n`, `serreLangStatement`), without abelian-variety theory. XI.2 before XI.2.1, for connected coverings of an abelian variety `A` over an algebraically closed field: a connected étale covering `A' → A` with a marked point over the origin has a unique group law with the marked point as origin making it a homomorphism (`existsUnique_grpObj_coveringOver`), and is then an isogeny (`isFinite_coveringHom`, `surjective_coveringHom`); SGA's "every isogeny is a quotient of some `n_A`" holds for these coverings when the `n_A` are surjective (`exists_surjective_isMonHom_comp_eq_mulN`), in particular in characteristic 0 (`exists_surjective_isMonHom_comp_eq_mulN_of_charZero`). Out of scope, with what is proved (what is missing is in the Foundations README): XI.1.4 (Serre) is reduced to Hodge symmetry `h^{0,q} = h^{q,0}` (`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`; `HodgeSymmetryZeroStatement` is open); in every characteristic, for `X` proper and normal over an algebraically closed field, unirational curves are simply connected (`isSimplyConnected_of_isUnirational_of_trdeg_eq_one`) and `#π₁` divides the separable degree of a unirational parametrization (`natCard_etaleFundamentalGroup_dvd_finSepDegree`). XI.2.1 (`π₁(A) ≅ lim_n K_n`, the Tate module) is proved in characteristic 0 (`exists_tateModule_equiv_of_charZero`), its `ℓ`-primary clause for every prime `ℓ ≠ char k` (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`), and all of it from SGA's cited "`n_A` is an isogeny" (`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`, from `MulNIsogenyStatement`); in characteristic `p`, XI.2.1 is open and equivalent to its `p`-primary clause (`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`). Not formalized: the disconnected principal coverings in XI.2 (`Ext(A, G) ≅ H¹(A, G)`), and the identification of `H¹(S_Zar, GL_n(𝒪_S))` with locally free Modules of rank `n`. |
| XII — Algebraic geometry and analytic geometry | Affine analytification and local rings (XII.1–XII.2.1), XII.2.2–XII.2.3 (through Rückert's Nullstellensatz, proved in `SGA.Foundations.Analytic`; XII.2.2 for schemes is `SchemePoints.closureComparison`, its affine form is proved for `A : Type` only, `Points.closureComparisonStatement_zero`), XII.2.4 and XII.2.6 (connectedness, without GAGA). For separated `X` only: the analytic space `X^an` glued from affine charts, `φ : X^an → X` and `f^an` (XII.1.1–XII.1.2; `AnalyticGluing.analyticSpace`, `AnalyticGluing.analyticMap`), with underlying space `X(ℂ)` (`AnalyticGluing.pointsHomeomorph`); SGA's universal property of `X^an` is proved only for affine `X`. §3 on the spaces of points `X(ℂ)`: XII.3.1 (viii) and XII.3.2 (i), (ii) in both directions; XII.3.1 (vii), (xi) and XII.3.2 (v), (vi) in one direction (some only for affine schemes), with part of the converse of (v); XII.3.3 a) (étale morphisms give local homeomorphisms). §3 for `f^an`, with `X` and `Y` separated (all in `AnalyticGluing`): XII.3.1 (i) (`flat_iff_forall_flat_stalkMap_analyticMap`), (ii) (`formallyUnramified_iff_forall_map_maximalIdeal_analyticMap`), (iii) with "`f^an` étale" read as flat and unramified at every point, not shown to be a local isomorphism (`etale_iff_forall_analyticMap`), and (iv) with "`f^an` smooth" read as flat with regular fibres (`smooth_iff_forall_analyticMap`); XII.3.1 (ix) and (xi) for `f` quasi-compact (`isIso_iff_isIso_analyticMap`, `isOpenImmersion_iff_isOpenImmersion_analyticMap`; the direct implications need no quasi-compactness); XII.3.2 (i), (ii) (`surjective_analyticMap_iff`, `denseRange_analyticMap_iff`, for `f` quasi-compact, which is SGA's own hypothesis that `f` be of finite type); the direct implications of XII.3.1 (vii) (`injective_analyticMap_of_injective`), of XII.3.2 (v), topological part (`isProperMap_analyticMap`), and of XII.3.2 (vi) with "finite" read as `AnalyticGeometry.IsFiniteMap`, a proper map with finite fibres (`isFiniteMap_analyticMap`). Out of scope, with what is proved (what is missing is in `lean/SGA/Foundations/README.md`): the rest of XII.3.1 for `f^an`, and §4 (GAGA), where XII.4.3–XII.4.6 are stated (`ExposeXII/GAGA.lean`) but not proved and XII.4.1–XII.4.2 are not stated; XII.5.1, proved when `X(ℂ)` is simply connected (`isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`), for schemes locally of finite type over `ℂ` of dimension `≤ 1` (`curveRiemannExistence`, `schemeCurveRiemannExistence`), for `𝔾_m` (`riemannExistence_laurentPolynomial`), and for `ℂ` minus a finite set and its finite étale coverings (`PuncturedPlane.riemannExistence_coordRing`, `PuncturedPlane.riemannExistence_finiteEtale`; this project's route, not SGA's, through a meromorphic function with a single pole on a compact Riemann surface, `AnalyticGeometry.exists_meromorphic_single_pole`), with `Ψ` fully faithful for every `X` (`schemePointsFunctorFullyFaithful`) and the scheme and affine forms equivalent (`schemeRiemannExistence_iff`); XII.5.2, which follows from XII.5.1 alone for every connected `X` (`schemeFundamentalGroupComparison_of_riemannExistence`, with the isomorphism stated as `Nonempty`; affine form `fundamentalGroupComparison_of_riemannExistence`) because `X(ℂ)` is locally path-connected and semilocally simply connected (`locallyPathConnectedStatement`, `semilocallySimplyConnectedStatement`, without triangulation), while the surjection `π̂₁(X(ℂ)) ↠ π₁(X)` needs no XII.5.1 (`surjective_autWhiskerLeft_schemePointsFunctor`); for `ℙ¹_ℂ` minus `n + 1 ≥ 1` points, `π₁` is isomorphic to the profinite completion of a free group on `n` generators (`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`; an abstract isomorphism, with no generators identified with loops or inertia). Not formalized: XII.1.3.1 (only the functor `F ↦ F^an` is defined, `AnalyticGluing.analytification`), XII.2.5, `X^an` for non-separated `X`, the uniqueness of `f^an`, fibre products of analytic spaces (XII.1.2 is compared on points only), XII.3.2 (iii), (iv) and the converses of (v), (vi) for `f^an`, and XII.5.3–XII.5.5 (normal analytic spaces). |
| XIII — Cohomological properness | §1: the definitions 1.1–1.2, 1.5 a) and c), 1.6 and 1.13 1), with SGA 4 VIII 5.2 (degree 0), 5.5 and 5.8 proved and 5.6 for finite morphisms. 1.4 in dimension `≤ -1` for every universally closed `f`, for sheaves of sets (`isCohomologicallyProperLENegOne_of_universallyClosed`) and of groups (`isCohomologicallyProperLENegOneGroup_of_universallyClosed`), hence 1.8 for sheaves of sets and 1.9 in dimension `≤ -1`. 1.4 for sheaves of sets over a locally noetherian base (`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`, through Gabber's theorem), hence 1.8 for sheaves of sets in dimension `≤ 0` over such a base (`IsCohomologicallyProperLEZero.comp_of_isProper_of_isLocallyNoetherian`). 1.9 for sheaves of sets in dimension `≤ 0`: for finite morphisms (`isCohomologicallyProperLEZero_pushforward_iff_of_isFinite`), and for integral ones given `IntegralBaseChangeStatement` (`isCohomologicallyProperLEZero_pushforward_iff`). For sheaves of groups, XIII 1.3.1 (ii) is the definition, since stacks of torsors and their inverse images are not available, and 1.7 is proved in dimension `≤ -1` (`IsCohomologicallyProperLENegOneGroup.pushforward`). §2: 2.0–2.0.3, 2.1.1, locally constant sheaves; 2.3 b) for Galois coverings of degree prime to `p` of an open `U` with finite complement in a proper smooth connected curve over a separably closed field (`galoisCoveringsTameStatement`); 2.3 a) and 2.4 1) for sheaves of sets are stated. 2.12: its "in other words" form on `ℙ¹` over an algebraically closed `k`, with the inertia conditions, for `(g, n) = (0, 0)`, `(0, 1)` at the point `∞` and `(0, 2)` at the points `0, ∞`, without Riemann existence (`tameCurvePrimeToPConclusion_projectiveLine_zero`, `tameCurvePrimeToPConclusion_projectiveLine_one`, `tameCurvePrimeToPConclusion_projectiveLine_two`); 2.12 implies that form (`tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement'`). 2.13: the Artin–Schreier description of `Hom(π₁(𝔸¹_k), ℤ/p)` (`affineLineArtinSchreier`), `π₁(𝔸¹_k)` not topologically finitely generated (`not_isTopologicallyFG_fundamentalGroup_affineLine`), the necessary condition of Abhyankar's conjecture (`sylowSup_eq_top_of_affineLine`); for the sufficiency, `p`-groups (`exists_surjective_fundamentalGroup_affineLine_of_isPGroup`), `S₃` for `p = 2` and `A₄` for `p = 3` (`exists_surjective_of_mulEquiv_perm_fin_three`, `exists_surjective_of_mulEquiv_alternatingGroup_fin_four`), and Serre's theorem on `p`-group kernels (`SerrePKernel.affineLinePExtension`), with which the conjecture is reduced to Raynaud's cases A and B (`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`). §3: 3.2 1) for every field (`fieldCohomologicalPropernessStatement`); 3.1 1), 3.3, 3.4 and 3.5 are stated, and 3.3 and 3.4 are proved for étale `f` (`exists_isUniversallyLocallyOneAspherical_of_etale`) and for smooth `f` given SGA 4 XV 2.1 (`exists_isUniversallyLocallyOneAspherical_of_smooth`); over a field every morphism is locally, not universally, `1`-aspherical (`isLocallyOneAspherical_of_field`); the desingularization hypotheses hold for integral schemes of dimension `≤ 1` of finite type over a perfect field (`desingularizableUpTo_one`, `stronglyDesingularizableUpTo_one`). §4: 4.0, 4.4 first part at all geometric points, 4.5, 4.6 for `π₁^L` with `X` proper and reduced (`bijective_proLMap_prod_of_isProper`), the group theory of 4.7–4.8 (without closures); the second part of 4.4, without the section, over a field (`properSmoothHomotopyExactSequence_of_field`), at the closed point of a complete regular local base (`isProLShortExact_of_isRegularLocalRing`) and over a complete discrete valuation ring with separably closed residue field (`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`); for 4.6, with `k` algebraically closed (SGA: separably closed) and `X`, `Y` connected, the surjectivity half in every characteristic (`surjective_map_prod_of_isAlgClosed`) and, in characteristic 0 and without resolution of singularities, `π₁(X ×ₖ 𝔸¹) ≅ π₁(X)` for `X` normal and locally of finite type (`bijective_map_prod_affineLine_of_isNormalScheme`). Appendix I: 5.1, 5.3, 5.4 in full; 5.2 except in mixed characteristic over a ring that is not strictly henselian; the existence part of 5.5 is stated (`RelativeAbhyankarStatement`). What remains of 1.4 for sheaves of sets (an arbitrary base), 2.12, 2.13, §3, the second and third parts of 4.4 and 4.6 is listed in [`lean/SGA/Foundations/README.md`](../lean/SGA/Foundations/README.md). Not formalized: for sheaves of groups, 1.8, 1.4 in dimension `≤ 0` (neither proved nor stated), 1.7 and 1.9 in dimension `≤ 0`, dimension `≤ 1`, and 2.4 1); the equivalences of 1.3.1, 1.5 b), 1.13 2)–3) and 1.10–1.17 apart from 1.13 1) (see the module docstring of `ExposeXIII/CohomologicalProperness.lean`); 2.3 b) beyond Galois coverings of such curves; the items of §2 on sheaves of groups and stacks (2.1.3–2.1.6, 2.2, 2.5–2.9), 2.4 2) and 2.11; 3.1.1–3.1.3, 3.1 2) and 3.2 2); 4.3 as stated (its hypotheses are not defined); the uniqueness in 5.5, and 5.6–5.7; Appendix II (6.1–6.3). |

### Open statements

These `…Statement` definitions are the in-scope items that were still open after wave 1 (the
out-of-scope ones are in `lean/SGA/Foundations/README.md`). A row whose last cell is "—" was
proved in wave 2 (2026-10-04). The others are proved in the cases indicated.
Numbered items that are neither proved nor stated have no `…Statement` and are not in this
table; they are listed as "not formalized" or "not stated" in the coverage table above.

| Statement | Item | Proved so far | Missing |
| --- | --- | --- | --- |
| `GrothendieckExistenceStatement` (Foundations) | EGA III 5.1.4 | Full faithfulness for proper `X`; essential surjectivity for finite étale coverings of `X` projective, and its Chow/Stein descent step | Essential surjectivity for proper `X` (gluing along the conductor, noetherian induction) |
| `EtaleCoveringsOfClosedFibreStatement`, `CompleteLocalBaseStatement` | IX.1.10 = X.2.1 | `X` projective over `A` (`isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion`); `X` integral and normal (`isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`); full faithfulness for every proper `X` (`ExposeIX.full_pullback_closedFibre`, `ExposeIX.faithful_pullback_closedFibre`), with fullness also over a noetherian henselian local base (`ExposeXIII.full_pullback_closedFibre_of_henselianLocalRing`) and faithfulness over any local base (`ExposeXIII.faithful_pullback_closedFibre_of_isLocalRing`) | Essential surjectivity for proper `X` that is neither projective nor integral and normal (the existence theorem for proper morphisms) |
| `SpecializationSurjectiveStatement` | X.2.4 | `X` projective over `Y` (`exists_continuous_surjective_specialization_of_isClosedImmersion`); every proper `X`, given IX.1.10 (`specializationSurjectiveStatement_of_etaleCoveringsOfClosedFibreStatement`) | IX.1.10 for proper `X` |
| `SmoothProperCurveLiftStatement` | III.7.4 | Proved (`smoothProperCurveLiftStatement`, `ExposeIII/CurveLiftCurve.lean`), through a finite flat map to `ℙ¹` (`smoothProperCurveFiniteFlatStatement`) | — |
| `IsEffectiveIffStrictlyLocalStatement` | IX.4.6 in SGA's form | Proved (`isEffectiveIffStrictlyLocal`, `ExposeIX/StrictlyLocalDescentGeneral.lean`), from EGA 0_III 10.3.1 (`flatResidueExtensionStatement`) | — |
| `QuasiSectionStatement`, `EffectiveDescentOfUniversallyOpenStatement` | input of IX.4.9; IX.4.9 | Proved (`quasiSectionStatement`, `ExposeIX/QuasiSection.lean`), so IX.4.9 is unconditional | — |
| `UniversallySubmersiveValuativeCriterionStatement` | IX.2.6, sufficiency | Proved in both directions (`universallySubmersiveValuativeCriterion`, `ExposeIX/SubmersiveValuative.lean`). `g` is quasi-compact; SGA's finite-type hypothesis is not used. The input is EGA II 7.1.7 (`dominatingDVRStatement`) and Krull–Akizuki (`KrullAkizukiFinite.lean`) | — |
| `EffectiveDescentOfProperStatement` | IX.4.12 | Proved over an arbitrary base (`effectiveDescentOfProperStatement`, `ExposeIX/EffectiveDescentGeneral.lean`), from EGA IV 8.8.2 and 8.10.5 for proper morphisms (`spreadingOutStatement`, `properLimitStatement`) | — |
| `ProperDescentStatement`, `GeometricFibresStatement` | IX.6.8, IX.6.11 | Proved over an arbitrary base (`properDescentStatement`, `geometricFibresStatement`, `ExposeIX/ProperDescentGeneral.lean`) | — |
| `ExactSequenceStatement` | IX.6.1 | Closed fibre quasi-compact and quasi-separated | Nothing known without quasi-separatedness (the Stacks Project also assumes it) |
| `LocalProperDescentStatement` | IX.6.5 | — | Stein factorization and its compatibility with completion |
| `TameSpecializationStatement` | X.3.8 | The core of X.3.8 over a complete DVR with separably closed residue field (`TameLiftingDVRStatement`, proved as `tameLiftingDVRStatement`), hence X.3.8 and X.3.9 for `Y` the spectrum of such a ring, `y₀` closed, `y₁` generic (`exists_tameSpecialization_of_isDiscreteValuationRing`, `exists_primeToQuotientEquiv_of_isDiscreteValuationRing`); X.3.9 from X.3.8 for every `Y` (`exists_primeToQuotientEquiv_of_tameSpecialization`) | Reduction of a general `Y` to that case: a DVR dominating the local ring of the closure of `y₁` at `y₀` (EGA II 7.1.7, Krull–Akizuki), its completed strict henselization, and the comparison of the geometric fibres |
| `Points.ClosureComparisonStatement` | XII.2.2, affine form | `A : Type` (`Points.closureComparisonStatement_zero`); the scheme form, for `X : Scheme.{0}` (`SchemePoints.closureComparison`) | Universes above 0 |
| `AbsoluteAbhyankarStatement` | XIII.5.2 | Existence of the extension for every regular local ring; the full statement in equal characteristic and in dimension 1 | The exponents are prime to `p` in mixed characteristic over a ring that is not strictly henselian |
| `RelativeAbhyankarStatement` | XIII.5.5, existence part (the uniqueness is not stated) | — | SGA 2 XIV 1.20 (étale depth), to reduce to the maximal points of `Y'₁`, where X.3.6 applies; the descent showing that the `nᵢ` are prime to `p` |
| `TameRamificationAtMaximalPointsStatement`, `TameBaseChangeStatement` | XIII.2.3 a), XIII.2.4 1) (sheaves of sets) | — | The relative Abhyankar lemma XIII.5.5 (`RelativeAbhyankarStatement`) |
| `IntegralBaseChangeStatement` | SGA 4 VIII 5.6 (used in XIII 1.9) | Finite morphisms (`isCohomologicallyProperLEZero_of_isFinite`); dimension `≤ -1` for every integral `f` (`isCohomologicallyProperLENegOne_of_universallyClosed`); the limit theorems it uses, in degree 0: SGA 4 VII 5.7, surjectivity (`Scheme.exists_toLimitSections_eq`), and VIII 5.2 (`Scheme.pushforwardStalkStrictLocalizationStatement`) | Gabber's theorem for `B` integral over a strictly henselian local ring `A`: restriction of sections from `Spec B` to `Spec (B/𝔪_A B)` is bijective |

### Corrections to SGA 1

Points where SGA 1 is wrong or needs an extra hypothesis, found while formalizing, are recorded in
the table "Found during the Lean formalization" of each exposé's README under
`translation/SGA1/`, with the Lean declaration that proves or records the corrected form: I.9.8,
I.10.7 and I.10.9, V.6.8, V.6.11, V.6.12, the remarks after VI.6.1, VI.9, X.1.10 and the proof of
XIII.1.3.1 (recorded in the definition `IsCohomologicallyProperLEZeroGroup`). Misprints found by
the translators (for example IX.2.5, `S'' → S`) are in the same READMEs.

### Foundations

`SGA.Foundations` (`lean/SGA/Foundations/`, about 400 files) contains what SGA 1 needs and
mathlib lacks: quasi-affine, ample and quasi-projective morphisms, relative `Proj`, norms and
Chow's lemma (EGA II); regular local rings, Auslander–Buchsbaum, factoriality and Zariski–Nagata
purity; dimension theory; E. Noether's finiteness of integral closure and the finite
normalization of an integral scheme of finite type over a perfect field
(`Algebra.FiniteType.finite_integralClosure`,
`isFinite_fromNormalization_fromSpecStalk_genericPoint`); generic smoothness over a perfect
field, and smooth morphisms are geometrically reduced; henselization, strict henselization,
strict localization and étale stalks (EGA IV 18); limits of schemes and of finite étale
coverings, EGA IV 8 and 15.5.1; Čech and derived cohomology of quasi-coherent sheaves and the
EGA III theorems (Serre vanishing, finiteness, formal functions, Zariski connectedness, Stein
factorization, flat base change, Grothendieck existence); formal schemes; étale sheaves, torsors
and non-abelian `H¹`; pro-objects, and the profinite completion of a finitely generated group is
topologically finitely generated (`ProfiniteGrp.ProfiniteCompletion.exists_finset_dense_closure`);
embeddings into `ℂ` of fields of characteristic 0 with `#k ≤ 𝔠`
(`Complex.nonempty_ringHom_of_mk_le_continuum`); convergent power series, Rückert's
Nullstellensatz and analytification; topological coverings. The module docstring of
`SGA/Foundations.lean` lists the areas.

The out-of-scope campaign of 2026-10 added the following areas.

- Topology of `π₁` (`Topology/`): `π₁` of a compact, R₁, path-connected, locally path-connected
  and semilocally simply connected space is finitely generated
  (`FundamentalGroup.fg_of_compactSpace`); van Kampen for any open cover (groupoid and group
  forms, and a presentation); `π₁` of finite products and products of covering maps; connected
  finite coverings of punctured discs are Kummer coverings
  (`Complex.exists_homeomorph_powRestrict_of_connectedSpace`) and those of `(Δ*)ᵖ × Δ^q` are
  quotients of multi-Kummer coverings (`Complex.exists_subgroup_continuousMap_multiPowRestrict`);
  `π₁(C ∖ S)` is free on loops around the points of `S`, for `C ⊆ ℂ` open and convex and `S`
  finite (`Complex.exists_freeGroupBasis_fundamentalGroup_diff`); path lifting for proper maps
  with finite fibres that are coverings over a subset (`CoveringMapOn`); monodromy is transitive
  on path-connected finite coverings (`TopCat.FiniteCovering.exists_monodromy_eq`).
- Semialgebraic geometry (`Semialgebraic/`): Tarski–Seidenberg, the monotonicity theorem,
  semialgebraic choice for compact fibres, a Kurdyka–Łojasiewicz inequality and a gradient-descent
  retraction, so that real algebraic sets are locally contractible, locally path-connected and
  semilocally simply connected (`MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero`,
  `MvPolynomial.semilocallySimplyConnectedSpace_setOf_eval_eq_zero`).
- Analytic sheaves and Riemann surfaces (`Analytic/`): sheaves of modules on locally ringed spaces
  with pullback, pushforward and the maps `Hⁿ(Y, M) → Hⁿ(X, f^*M)`; finite and étale morphisms of
  analytic spaces; the localizations used to glue `X^an`; Oka's coherence theorem and Theorem B
  for `𝒪` on `Δ × ℂᵃ × (ℂ*)ᵇ`, stated, not proved (`Statements`); Dolbeault's lemma and the first
  Cousin problem on a disc (`AnalyticGeometry.exists_contDiffOn_dbar_eq_ball`,
  `AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`); L. Schwartz's theorem on compact
  perturbations; Montel's theorem; on a compact Riemann surface, every point is the only pole of
  some meromorphic function (`AnalyticGeometry.exists_meromorphic_single_pole`, Forster 14.13);
  the compact Riemann surface obtained by filling in the punctures of a finite covering of
  `ℂ ∖ S`.
- Field patching (`Patching/`): Cartan factorization and patching of free modules and of Galois
  algebras, on `ℙ¹` over `k⟦t⟧` and on a double cover of that configuration modelled on
  Harbater–Stevenson's node (the identification with their nodal model is not formalized).
- Group schemes (`GroupScheme/`): multiplication by `n` acts as `n` on the cotangent space at the
  origin of a monoid scheme over a field, so it is injective on the local ring there when the
  scheme is locally noetherian and `n` is invertible
  (`AlgebraicGeometry.GroupScheme.injective_stalkEnd_pow`); points with values in local rings.
- Euler characteristic (`Cohomology/EulerCharacteristic*`): `hᵖ` and `χ` of coherent modules on
  proper schemes over a field; `χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)` for `X` proper over a field and `Y → X`
  finite étale of degree `d`, in every characteristic, by dévissage and without Riemann–Roch
  (`eulerCharFiniteEtaleStatement`); on an integral noetherian scheme, an additive function of
  coherent modules that vanishes on modules supported in proper closed subsets is determined by
  the generic rank (`exists_additive_eq_mul_unitModule`).
- Gabber's theorem and proper base change in degree 0 (`Etale/Gabber*`, `Limits/EtaleSections*`,
  `EtaleStalkProper*`): Gabber's theorem for proper schemes over a noetherian henselian local ring
  (Stacks 0A3S, `properHenselianSectionsStatement`); SGA 4 VII 5.7 (surjectivity) in degree 0 for
  inverse images over a cofiltered limit of quasi-compact quasi-separated schemes with affine
  transition maps (`Scheme.exists_toLimitSections_eq`), and VIII 5.2 in degree 0
  (`Scheme.pushforwardStalkStrictLocalizationStatement`); the base change morphism of a
  universally closed morphism is injective on stalks
  (`injective_sheafFiber_etaleBaseChangeMap_of_universallyClosed`); an étale morphism with finite
  fibres and one geometric point in each fibre is an isomorphism
  (`isIso_of_forall_geometricFiberCard_eq_one`); for a proper scheme over a noetherian henselian
  local ring, every clopen subset of the closed fibre is the trace of a clopen subset
  (`exists_isClopen_preimage_closedFibre_of_henselianLocalRing`).
- Local acyclicity (`Etale/LocalAcyclicity*`): locally acyclic morphisms through Milnor fibres
  (SGA 4 XV 1.11), the base change form of Stacks 0A3H and 0EZX, base change morphisms on stalks
  through strict localizations; a connected scheme integral over a strictly henselian local ring
  is simply connected (`isIso_of_isFinite_of_etale_of_isIntegralHom`).

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
| I.10 normalisation | `Scheme.Hom.toNormalization` |

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

Entry point: `lean/SGA/SGA2/ExposeI.lean`.

Exposé I is topological (abelian sheaves on a space `X`, functors `Γ_Z`
and their derived functors `H_Z^*`). Mathlib supplies flasque sheaves,
pushforward/pullback, `Ext` on Grothendieck abelian sheaf categories, and
the *algebraic* local cohomology of modules. This repo defines topological
`H_Z^*` for closed supports as `Ext(ℤ_{Z,X}, −)` following I.2.3 bis.

| SGA 2 I | Mathlib / this repo |
| --- | --- |
| I.1 `Γ_Z` (closed `Z`) | `gammaZ`, `gammaZSections` (`GammaZ.lean`) |
| I.1 (8) `Γ̲_Z` sheaf | `underlineGammaZ` = `ker(F → j_* j^* F)` (`UnderlineGammaZ.lean`) |
| I.1 (8), actual section comparison | `underlineGammaZSectionsEquiv`, `underlineGammaZPresheafFunctorIso`: original kernel-sheaf sections are supported sections, naturally in coefficients and opens; the original functor is additive and left exact |
| I.1 (3) locally closed | `LocallyClosedIn`, `LocallyClosedIn.gamma` |
| I.1 independence of open | `gammaZSections_restrict_addEquiv` |
| I.1 special cases | closed pushforward, open restriction, `underlineGamma_locallyClosed`; `zZX_closed` |
| I.1.3–I.1.4, open case | `iBang_open`, `openExtensionByZeroAdjunction`: genuine exact open extension by zero, left adjoint to restriction; `restrictToOpen_injective` |
| I.1.3–I.1.4, closed and locally closed | `closedSupportAdjunction`, `locallyClosedSupportAdjunction`: genuine arbitrary-coefficient adjunctions; exact fully faithful closed extension and injective-preserving extraordinary inverse image; `closedSupportPushforwardIso` and `closedSupportPullbackIso` compare with the original kernel, including actual counit compatibility |
| I.1.6, closed case | `closedSupportHomEquiv`: actual `Hom(zZX_closed Z, F)` is naturally the additive group of supported sections |
| Internal Hom and sheaf Ext | `abelianSheafHom`, `internalHomSectionsRestrictEquiv`, `internalSheafExtSheafificationIso`: genuine sheaf of local morphisms, left exactness, actual restriction-Hom comparison, and right-derived sheaf Ext as sheafification of local Ext |
| Closed support under arbitrary open restriction | `closedSupportRestrictionIso`: actual pullback of the closed integer support sheaf is the support sheaf of the restricted closed set, compatibly with its full integer-presheaf presentation |
| I.1.6 / I.2.3 bis, closed support, sheaf-valued | `closedSupportInternalHomFunctorIso`, `closedSupportInternalSheafExtIso`, `closedSupportInternalSheafExtIsoModel`: actual internal Hom and its derived sheaf Ext identify naturally with the original supported-sheaf functor and unchanged model |
| I.1.6 / I.2.3, open case | `openSupportHomEquiv`, `openSupportExtEquiv`: actual open extension by zero represents sections on the open and its Ext is ordinary cohomology of restriction, naturally in coefficients and compatibly with coefficient boundaries |
| I.1.8 degree 0 | `exact_gammaZ_of_le`, `I_1_8_package`; global flasque extension |
| I.1.9–I.1.10, constant support objects | `constantSupportSequence_shortExact`: actual `0 → ℤ_{X\\Z,X} → ℤ_X → ℤ_{Z,X} → 0`; open inclusion agrees with restriction under the genuine adjunction |
| I.1, (13)/(17), arbitrary coefficients | `locallyClosedSingleExtensionSequence_shortExact`, `locallyClosedSingleExtensionSequenceFunctorIso`: genuine single-witness extension endpoints for every coefficient sheaf, with original counit/unit arrows and literal coefficient-map compatibility; the required closed/open composition cases are proved |
| I.1.10, general integer-support sequence | `locallyClosedNestedObjectSequence_shortExact`, `nestedClosedSubspaceObjectSequence_shortExact`: actual `0 → ℤ_{Z″,X} → ℤ_{Z,X} → ℤ_{Z′,X} → 0` for arbitrary locally closed `Z` and closed `Z′` in its literal support space; the witnesses represent the original closed subset and its set difference |
| I.1.10, internal-Hom arrows | `nestedSupportObjectRestriction_internalHom`, `nestedSupportObjectInclusion_internalHom`, `nestedSupportInternalHomSequenceIso`: internal Hom of both actual support-object arrows gives the original I.1.9 sheaf arrows in any open/closed presentation, with a genuine isomorphism of short complexes |
| I.1.9, general supported-sheaf sequence | `locallyClosedNestedSheafSequence_exact`, `locallyClosedNestedSheafInclusion_mono`, `locallyClosedNestedSheafSequence_shortExact`: actual ambient supported functors, actual section inclusion and restriction, left exactness for every coefficient, and short exactness for flasque coefficients |
| I.1.8, general original section groups | `locallyClosedNestedGammaSequence_exact_and_mono`, `locallyClosedNestedGammaSequence_shortExact`: the original locally closed section functors, with actual inclusion/restriction, form a natural left exact sequence, short exact on flasque coefficients |
| I.1.6 / I.2.3 bis, locally closed internal Hom and sheaf Ext | `locallyClosedSupportInternalHomFunctorIso`, `locallyClosedSupportInternalSheafExtIso`: the original ambient locally closed supported functor is actual internal Hom from the original integer-support object, and the all-degree original derived functors are its sheaf Ext; both coefficient and ambient-open naturality are proved |
| I.2.1 / I.2.3 bis `H_Z^n` | `H_Z Z F n` := `Ext (zZX_closed Z) F n` |
| I.2.1 original derived functor | `derivedGammaZSections`: right-derived actual supported sections, with proved left exactness and natural degree-zero comparison |
| I.2.1 / I.2.3 bis comparison, closed supports | `derivedGammaZSectionsIsoH_Z`: natural isomorphism from original right-derived supported sections to existing Ext-defined `H_Z` in every degree; generic derived-Hom/Ext comparison in `ExtRightDerived.lean` |
| I.2.2 degree-zero excision | `I_2_2_degree_zero`, `I_2_2_excision_degree_zero` |
| I.2.2, all degrees for closed supports | `supportedExcisionEquiv`: actual `H_Z` is unchanged by restricting to an open neighbourhood containing `Z`, naturally in coefficients; `closedSupportExcisionIso` compares the genuine support sheaves |
| I.2.1 / I.2.3 bis / I.2.12, chosen locally closed witnesses | `zZX_locallyClosed`, `derivedGammaLocallyClosedIsoExt`, `locallyClosedSupportExtEquiv`: genuine composite extension by zero represents the existing supported sections; its Ext computes their original derived functors and agrees with closed-support cohomology on the neighbourhood; flasque coefficients are acyclic |
| I.2.11 model for `ℋ_Z^n` | `sheafH_Z_n` defined by ker / coker / `rightDerived` |
| I.2.2, arbitrary locally closed witnesses | `locallyClosedSupportIsoOfSameSet`, `derivedGammaLocallyClosedIndependenceIso`, `locallyClosedCohomologyEquivOfSameSet`: the genuine support sheaf and all-degree cohomology are independent of the chosen witness, naturally in coefficients |
| I.2.4, closed support | `supportedCohomologySheafificationIso`: the original derived kernel-sheaf functor is naturally the sheafification of local supported cohomology; `supportedCohomologyPresheafSectionsEquiv` identifies its values with actual `H_Z` on each restricted open |
| I.2.4, locally closed support | `underlineGammaLocallyClosedFunctor`, `locallyClosedCohomologySheafificationIso`, `derivedUnderlineGammaLocallyClosedIndependenceIso`: actual ambient locally closed supported sheaves, their original derived functors, local-cohomology sheafification, and arbitrary witness independence in all degrees |
| I.2.5, open support | `derivedUnderlineGammaOfOpenIso`: original open-supported derived sheaves identify naturally with actual open restriction followed by higher direct image, with no assumed exactness of direct image |
| I.2.11, all degrees | `derivedUnderlineGammaZIsoModel`: the unchanged kernel/cokernel/derived-pushforward model is naturally the original derived kernel-sheaf functor; `sheafH_Z_nSheafificationIso` proves its sheafification interpretation |
| I.2.12, sheaf-valued closed support | `derivedUnderlineGammaZ_isZero_of_isFlasque`, `sheafH_Z_n_isZero_of_isFlasque`: original higher supported sheaves and the unchanged model vanish on flasque coefficients |
| I.2.12, sheaf-valued locally closed support | `derivedUnderlineGammaLocallyClosed_isZero_of_isFlasque`: all positive original ambient supported sheaves vanish on flasque coefficients |
| I.2.6 resolution inputs | `SupportedSheafInjective.lean`, `LocalToGlobalResolution.lean`: original supported sheaves preserve injectives and the supported resolution computes actual `H_Z` |
| I.2.6 closed-support spectral sequence construction | `supportedTruncationSpectralSequence`: canonical truncations and actual derived Hom give genuine pages, differentials, and next-page homology isomorphisms |
| I.2.6 E₂ identification | `supportedTruncationSpectralSequenceE2Equiv`: actual E₂ terms of that sequence are ordinary cohomology of original derived supported sheaves, including the E₂ universe comparison |
| I.2.6 first quadrant | `supportedLocalToGlobalAbelianSpectralObject_isFirstQuadrant`: the actual spectral object is first quadrant, and all pages Eᵣ, r ≥ 2, vanish outside it |
| I.2.6 total groups | `supportedSpectralObjectTotalEquivH_Z`: actual total-interval cohomology of the constructed spectral object identifies additively with original `H_Z`, using K-injectivity and the actual global-sections complex; finite convergence is proved separately below |
| I.2.6 convergence | `supportedCohomologyFiniteFiltration`, `supportedLocalToGlobalStablePageIsoGraded`: actual total cohomology, additively identified with original `H_Z`, has a finite image filtration from zero to the whole group; actual pages r ≥ n + 2 in total degree n are its associated-graded cokernels |
| I.2.6 spectral-object and total naturality | `supportedAbelianSpectralObjectMap`, `supportedSpectralObjectTotalEquivH_Z_naturality`: actual compatible resolution maps give spectral-object maps preserving every connecting map, and the existing total comparison intertwines these with `H_Z_map` |
| I.2.6, closed-support page morphisms | `supportedTruncationSpectralSequenceMap`, `_d`, `_next`: actual resolution maps induce actual spectral-sequence morphisms respecting all differentials and original next-page homology isomorphisms; `spectralSequence_hom_ext_firstPage` proves uniqueness from the first page |
| I.2.6, closed-support E₂ naturality | `supportedTruncationSpectralSequenceE2Equiv_naturality`: the original E₂ comparison intertwines actual coefficient maps, via naturality of the actual single-degree truncation and first-page comparisons |
| I.2.6, closed-support coefficient functor | `supportedTruncationSpectralSequenceFunctor`: actual coefficient maps are independent of compatible resolution lifts, satisfy identity and composition, and commute with canonical resolution-change isomorphisms satisfying the cocycle identity |
| I.2.6, closed-support filtered naturality | `supportedLocalToGlobalStablePageIsoGraded_coefficient_naturality`, `H_Z_map_mem_supportedCohomologyFiltration`, `supportedCohomologyFiltrationOnH_Z_independent`: original stable-page/graded-piece comparisons and the actual finite filtration are natural; total, filtration and graded maps are lift-independent, and the transported filtration on original `H_Z` is independent of the resolution |
| I.2.6, general locally closed support | `LocallyClosedLocalToGlobalResolution.lean`, `LocallyClosedLocalToGlobalSpectralSequence.lean`, `LocallyClosedLocalToGlobalConvergence.lean`: the original ambient support functor gives an actual spectral sequence with E₂ ordinary cohomology on `X` of the original derived locally closed sheaves, original `H_locallyClosed` abutment, first-quadrant vanishing, and actual finite convergence |
| I.2.6, locally closed functoriality | `LocallyClosedLocalToGlobalMaps.lean`, `LocallyClosedLocalToGlobalCoefficientFunctor.lean`, `LocallyClosedLocalToGlobalE2Naturality.lean`, `LocallyClosedLocalToGlobalTotalNaturality.lean`, `LocallyClosedLocalToGlobalConvergenceNaturality.lean`: coefficient functor, original E₂/total/stable-page/filtered naturality, lift independence, and resolution-independent filtration on original support Ext |
| I.2.7, locally closed boundary | `derivedUnderlineGammaLocallyClosed_stalkSupport_subset_closure`, `_subset_frontier`: original derived locally closed sheaves have actual stalk support inside the closure, and inside the boundary in positive degrees; the stronger open-restriction vanishing statements are also proved |
| I.2.7, locally closed cohomology | `derivedLocallyClosedSupportCohomologyEquiv`, `_naturality`: higher cohomology of the original derived supported sheaves is cohomology of their ordinary pullbacks to the actual closure; the comparison is natural in coefficients |
| I.2.7, closed support | `derivedSupportedSheafRestrictionIso`: original derived supported sheaves commute naturally with actual open restriction in every degree; `SupportedSheafBoundary.lean` proves vanishing off the support and positive-degree vanishing on its interior, including sheaf Ext and the unchanged model |
| I.2.7, literal stalk support | `derivedUnderlineGammaZ_stalkSupport_subset_frontier` and its model/sheaf-Ext analogues: positive original supported sheaves have actual stalk support in the boundary; all-degree support is contained in the closed set |
| I.2.7, closed-space cohomology | `closedPushforwardCohomologyEquiv`, `derivedSupportedSheafClosedCohomologyEquiv`: closed direct image preserves actual ordinary cohomology; cohomology of original derived supported sheaves is computed on the closed subspace using ordinary closed pullback, naturally in coefficients |
| Homological input for I.2.8 | `ext_contravariant_exact`, assuming a supplied short exact sequence |
| I.2.8 | `locallyClosedNestedCohomologySequence_exact`, `nestedClosedSubspaceCohomologySequence_exact`: the original ambient nested-support Ext sequence is exact in every degree, naturally in coefficients, with the extension class of the proved actual support-object sequence; open/closed degree-zero maps are actual section inclusion and restriction |
| I.2.10 | `locallyClosedNestedDerivedSheafSequence_exact`, `nestedClosedSubspaceDerivedSheafSequence_exact`: original ambient derived supported sheaves, their actual derived maps, and the genuine resolution connecting boundary form a natural long exact sequence in every degree; the initial map is monic and degree-zero maps recover the original supported-sheaf maps |
| I.2.9, closed/open relative sequence | `relativeCohomologySequence_exact`: actual `H_Z → H(X) → H(X\\Z) → H_Z[1]` is exact in all degrees, from the proved constant-support sequence and open Ext comparison; begins injectively in degree zero |
| I.2.9, section compatibility | `relativeRestriction_zero_sections`, `relativeSupportMap_zero_sections`: the degree-zero maps are actual restriction and inclusion of supported sections under the standard cohomology equivalences |
| Group-valued I.2.14 / III.3.1 input | `supported_vanishing_iff_relativeRestriction`: supported vanishing through degree `n` is equivalent to bijective relative restriction below `n` and injective restriction in degree `n`; `relativeBoundaryEquiv` identifies adjacent groups when ordinary cohomology vanishes |
| Inputs for I.2.12 | `isFlasque_of_injective`: every injective abelian sheaf is flasque; `H_pos_subsingleton_of_isFlasque`, `H_pos_restrict_subsingleton_of_isFlasque`: flasque sheaves have zero actual ordinary higher sheaf cohomology, also on every open subspace |
| Supported-section exactness | `gammaZSectionsFunctor_map_shortExact`: a short exact coefficient sequence with flasque kernel gives a short exact sequence of actual supported sections on every open |
| I.2.12 original supported acyclicity | `derivedGammaZSections_isZero_of_isFlasque`: actual right-derived supported sections vanish in positive degrees on flasque sheaves, proved using exactness of the supported-section resolution |
| I.2.12, closed supported acyclicity | `H_Z_pos_subsingleton_of_isFlasque`, `H_Z_pos_restrict_subsingleton_of_isFlasque`: the actual Ext-defined supported cohomology vanishes in positive degrees on flasque sheaves, also on every open subspace |
| I.2.12, converse | `isFlasque_iff_H_Z_one_subsingleton`, `isFlasque_iff_H_Z_pos_subsingleton`: flasqueness is exactly vanishing for all closed supports in degree one, equivalently every positive degree; the proof uses actual section restriction |
| I.2.13 degree 0 and 0–1 | kernel vanishing iff the unit is mono; kernel and cokernel vanishing iff it is an isomorphism |
| I.2.1 algebraic `H_J^i(M)` | `localCohomology` (`LocalCohomology.lean`) |
| III depth / Rees | `ModuleCat.exists_isRegular_tfae` |

### Remaining gaps in SGA 2 Exposé I

The modules compile without placeholders, but Exposé I remains partial.
The group-valued derived/Ext comparison and the sheafification comparison for
original derived supported sheaves are proved for closed supports; ambient
locally closed supported sheaves now have original derived functors,
sheafification, witness independence, and flasque acyclicity. In particular:

The internal-Hom/sheaf-Ext modules prove coefficient naturality in every
degree, first-variable bifunctoriality (`internalSheafExtPrecomp`), connecting
maps of local Ext (`localExtδ`), and nested-open restriction of the evaluation
equivalences (`localExtRestriction`). Ringed-space I.1.6/I.1.7 is
`ringedSpaceSupportHomEquiv`.

- I.1.1–I.1.7: first-variable Hom/Ext, nested-open local Ext restriction,
  connecting maps, and the ringed-space Hom identity are proved
  (`InternalHomBifunctor.lean`, `SheafExtRestriction.lean`,
  `SheafExtConnecting.lean`, `RingedSpaceSupportHom.lean`).
  The general closed and locally closed `i_! ⊣ i^!` adjunctions and
  preservation of injectives by extraordinary inverse image remain as previously
  proved, alongside exact open/closed extension and the closed Hom representation.
- I.2.6: the constructed sequence is identified with the Grothendieck
  spectral sequence of the supported-sheaf functor
  (`grothendieckSpectralSequenceOfSupportedSheaf`); for open support its
  E₂ page is the Leray page of the inclusion (`openInclusionLerayE2Equiv`).
  Spectral-level witness change is
  `locallyClosedTruncationSpectralSequenceE2WitnessEquiv`. Closed supports
  are the locally closed witness `LocallyClosedIn.ofClosed`.
  For closed supports, the actual sequence, E₂ identification and naturality, first-quadrant
  vanishing, total comparison to original `H_Z`, and finite convergence
  filtration are proved. Spectral-object coefficient maps preserve connecting
  maps, the total comparison is natural in compatible resolution maps, and
  actual spectral-sequence morphisms respect every differential and original
  next-page homology isomorphism. First-page equality determines morphisms.
  The actual coefficient functor is independent of compatible resolution lifts,
  with coherent natural resolution-change isomorphisms.
  The original stable-page/graded-piece comparison and actual convergence
  filtration are natural. Total, filtration and graded maps are lift-independent,
  and the filtration transported to original `H_Z` is resolution-independent.
  All these constructions now also exist for arbitrary locally closed supports,
  using the original ambient functor and cohomology on `X`, not merely
  replacing `X` by an open witness. The open-support case is included.
  I.2.7's locally closed boundary and closure bounds are now proved for literal
  stalks of the original derived locally closed sheaves. Their higher cohomology
  is naturally computed on the actual closure using ordinary closed pullback.
  Closed-support cohomology is also computed on the actual closed subspace, and the closed-support
  vanishing bounds apply to sheaf Ext and the unchanged kernel/cokernel model.

I.1.8–I.1.9's original group- and sheaf-valued nested sequences are proved in
general locally closed support, including flasque surjectivity. I.1.10's
integer-support short exact sequence is proved. I.2.8 and I.2.10's actual
nested group- and sheaf-valued long exact sequences are proved in all degrees,
with actual connecting maps and coefficient naturality. No support-object
short exact sequence or derived exactness is assumed. I.2.9's relative
sequence is also proved.
For every open/closed presentation, applying actual internal Hom to both
integer-support arrows recovers the actual original supported-sheaf arrows.
The arbitrary-coefficient extension sequence (17) is now proved using the
original open counit and closed unit, followed by exact locally closed
extension. Both endpoints are now actual single-witness extensions, with
literal subset equality, original arrow compatibility, and coefficient-map
naturality. Full arbitrary nested locally closed composition (13) is proved
for extension and extraordinary inverse image, with the actual support-space
homeomorphism and original unit/counit comparisons. No separate comparison of the group- and sheaf-sequence
connecting maps is claimed.

I.2.13's extra redundancy clause is proved for every `N > 0` by
`HigherRestrictionRedundancy.lean`, using actual complement-adapted injective
effacement and coefficient dimension shifting for arbitrary abelian sheaves.
The main higher-degree criterion is proved in Exposé III's
`derivedSupported_vanishes_iff_intersectionRestriction`; I.2.14's actual
group-valued criterion is `supported_vanishing_iff_ordinaryRestriction`.
Original closed and locally closed supported sheaves are proved acyclic on
flasque coefficients. The group-valued relative criterion and ordinary and
closed-supported flasque acyclicity are proved for both original right-derived
supported sections and the Ext-defined `H_Z`; the flasque converse is also proved.

## SGA 2, Exposé II — Algebraic and affine comparisons

Entry point: `lean/SGA/SGA2/ExposeII.lean`.
Source: `translation/SGA2/ExposeII/en-body.tex`.

| SGA 2 II | Proved content |
| --- | --- |
| (4.2), localization kernel | `localizationFamilyMap_ker`: ideal-power torsion is the kernel of the product of finitely many principal localization maps |
| II.4 affine input, noetherian rings | `affineTildeAb_H_pos_subsingleton`: actual ordinary higher sheaf cohomology of every associated module sheaf vanishes; no module finiteness assumption |
| II.(4.2)–(4.3), noetherian rings | `affineRelativeLowDegree_exact`, `affineSupportedCohomologyEquivOpen`: actual four-term low-degree cohomology sequence and higher supported/open-complement comparison, for arbitrary coefficient modules |
| Associated-sheaf exactness | `affineTildeAb_shortExact`, `affineTildeAb_globalSectionsEquiv`: the actual abelian associated-sheaf functor is exact and global sections recover the module, over arbitrary commutative rings |
| (4.2), actual affine supported sections | `powerTorsionEquivAffineSupportedSections`, `powerTorsionEquivGammaZ`: the kernel of actual associated-sheaf restriction outside `V(I)` agrees with torsion and exactly Exposé I's `gammaZ` |
| (5.1), degree zero | `stableKoszulCohomologyZeroIsoGammaZ`: stable Koszul degree zero agrees with the supported-section group |
| (4.2)/(5.1), principal degree-one calculation | `stableKoszulSingletonOneIsoRestrictionCokernel`: stable singleton Koszul H¹ is the cokernel of actual restriction from `Spec R` to `D(f)`; higher singleton cohomology vanishes |
| (7.3)–(7.4), reindexing | `generatorPowerIdeal_cofinal`, `generatorPowersLocalCohomologyIso`: finite generator powers and ordinary ideal powers give naturally isomorphic Ext colimits in each degree |
| (7.5), module algebra | `powerTorsion`, `quotientHomEquivTorsionBySet`: torsion is the union of annihilators, and evaluation at 1 identifies quotient Hom with annihilators |
| (7.5), categorical Hom colimits | `quotientHomColimitIso`, `generatorHomColimitIso`: both actual Hom systems have the torsion functor as colimit |
| (7.5), Koszul degree zero | `koszulHomologyZeroIsoQuotient`, `koszulCohomologyZeroIsoAnnihilator`, `stableKoszulCohomologyZeroIsoPowerTorsion`: the genuine finite Koszul complexes give the quotient, annihilator, and torsion comparisons |
| (7.3), affine degree zero | `localCohomologyZeroIsoAffineSupportedFunctor`, `localCohomologyZeroIsoGammaZ`: the Ext-colimit comparison reaches actual sheaf supported sections, naturally in coefficients at the module-valued level |
| (7.3), noetherian affine comparison, all degrees | `affineLocalCohomologyNatIso`, `affineLocalCohomologyAddEquiv`: actual algebraic local cohomology agrees with actual Ext-defined `H_Z` of the associated sheaf, naturally in every coefficient module; `affineLocalCohomologyNatIso_δ` proves compatibility with all coefficient boundaries |
| (7.6), canonical map | `koszulExtComparison`, `stableKoszulExtComparison`: lift the actual projective Koszul augmentation into a quotient resolution, dualize, and take cohomology and colimits; the maps are independent of the lift |
| Regular-sequence finite-stage comparison | `koszulProjectiveResolution`, `koszulExtComparisonIsoOfIsRegular`: the original augmentation is a quasi-isomorphism and the actual Koszul complex resolves the quotient for regular sequences over noetherian local rings; the original comparison is an isomorphism in all degrees, naturally in coefficients |
| (7.6), coefficient boundaries | `stableKoszulExtComparisonConnectingHom`: the constructed map commutes with actual connecting maps; finite and stable coefficient connecting maps and their exactness are proved |
| (7.3)–(7.6), cofinal boundaries | `localCohomologyIsoOfFinal_δ`, `localCohomologyToStableKoszul_δ`: cofinal reindexing and the canonical ordinary ideal-power Ext-to-Koszul comparison commute with coefficient boundaries, without a noetherian hypothesis |
| II.8 | `II_8`, `stableKoszulExtComparisonIso`: over a noetherian ring, the canonical generator-power Ext comparison is an isomorphism in every degree, naturally in coefficients |
| II.8, ordinary ideal powers | `localCohomologyIsoStableKoszul`: mathlib's algebraic local cohomology is naturally isomorphic to stable Koszul cohomology over a noetherian ring |
| II.9(b) ⇔ (c), each degree | `II_9_b_iff_c`: vanishing of actual stable Koszul cohomology on all injective coefficients detects essential vanishing of the corresponding Koszul homology system |
| II.9(a) ⇔ (b) ⇔ (c), all degrees | `II_9_a_iff_b`, `II_9_a_iff_c`: invertibility of the actual comparison in every degree is equivalent to positive-degree injective vanishing and essential vanishing of every positive homology system |
| II.10, noetherian-ring case | `affineTildeSheaf_isFlasque_of_injective`, `affineTildeAbSheaf_isFlasque_of_injective`: associated sheaves of injective modules are flasque; every section on any open extends globally |
| II.10, algebraic input | `powerTorsion_injective_of_injective`: supported torsion in an injective module is injective, using Artin–Rees and Baer's criterion |
| II.11 | `II_11`: for every finite list and noetherian coefficient module, every positive Koszul homology inverse system is essentially zero; the ring need not be noetherian |
| II.11, exact sequence | `scalarCofiberHomologyShortComplex_shortExact`: the genuine cofiber homology sits between the scalar cokernel and annihilator; its transition naturality supports induction on generators |

The Koszul complexes in `KoszulComplex.lean` are recursively defined homotopy
cofibers, with explicit chain maps for powers of the generators. Their terms
are noetherian for noetherian coefficients and projective for projective
coefficients. `KoszulCofiber.lean` proves the exact sequence from cycles and
boundaries. `KoszulProZero.lean` completes the induction in II.11 using the
varying-coefficient annihilator argument. `PrincipalKoszul.lean` also provides
explicit two-term calculations.

`InjectiveHomology.lean` proves the natural Hom–homology comparison for
injective coefficients. `InjectiveDetection.lean` proves the converse
vanishing criterion by embedding a term in an injective module and detecting
eventual equality in filtered colimits. `KoszulCoefficientSequence.lean`,
`ExtCoefficientSequence.lean`, and `ExtColimitSequence.lean` construct the
coefficient boundaries and prove exactness. `CohomologicalComparison.lean`
proves the general dimension-shifting isomorphism criterion; its hypotheses
are discharged for the actual map in `KoszulComparisonIsomorphism.lean`.

The formal II.9(a) equivalences quantify **all degrees simultaneously**.
The comparison argument uses vanishing in every positive degree; it does not
claim that vanishing in one isolated degree alone makes the full comparison
invertible. The equivalence II.9(b) ⇔ (c) is also proved degree by degree.

`AffineSupport.lean` uses mathlib's actual associated sheaf and its
restriction maps. Its degree-zero results require only a finitely generated
support ideal. `LocalizationCokernelColimit.lean` and
`PrincipalCechComparison.lean` identify principal degree-one stable Koszul
cohomology with the actual restriction cokernel over any commutative ring.
Over noetherian rings, `AffineCohomologyComparison.lean` now compares actual
algebraic local cohomology with the independently defined supported sheaf
cohomology of Exposé I in every degree.

Here `localCohomology` means mathlib's **algebraic Ext-colimit definition**.
Its comparisons with stable Koszul cohomology and actual group-valued
supported sheaf cohomology are proved over noetherian rings. The latter
comparison is a natural isomorphism respecting every coefficient boundary.
General-scheme and sheaf-valued comparisons remain open.

`Examples.lean` checks a nonzero principal homology module in an essentially
zero system, an explicit zero transition, and empty generating families.
Radical invariance of torsion is proved for finitely generated ideals.

### Remaining gaps in SGA 2 Exposé II

- II.1–II.3: quasi-coherence of `SheafH_Z^i(F)` for quasi-coherent `F` on
  general schemes remains. `II_1_open` identifies open-support derived
  sheaves with higher direct images; `II_3_restriction` is I.2.7 on charts.
- II.4 / II.7 on noetherian affines: the local-to-global sequence degenerates
  by ordinary affine vanishing (`II_7_affine_ordinary_vanishing`). Affine
  vanishing over arbitrary rings remains.
- II.5: `II_5` / `II_5_addEquiv` identify stable Koszul cohomology of an
  arbitrary finite family with topological supported cohomology over a
  noetherian ring; `II_5_zero` is the degree-zero comparison without
  noetherianity.
- II.6–II.7 on noetherian affines: `II_6_a_affine` / `II_6_b_affine`.
  General-scheme sheaf Ext colimits remain.
- II.10: over a noetherian ring, `II_10_koszul_vanishing_of_injective` and
  `II_10_flasque_implies_koszul`. The criterion under mere topological
  noetherianity of `Spec A` remains.

Exposé II remains partial.

## SGA 2, Exposé III — Cohomological invariants and depth

Entry point: `lean/SGA/SGA2/ExposeIII.lean`.

| SGA 2 III | Proved content |
| --- | --- |
| III.1 definitions | `sgaAssociatedPrimeSpectrum`: exact nonzero-element annihilators over arbitrary rings, with a proved noetherian comparison to mathlib's radical-annihilator convention |
| III.1.1 | Finiteness of associated primes, their union as the zero divisors, and the radical annihilator as the intersection of minimal associated primes |
| III.1.2 | Support membership is equivalent to containing an associated prime, the annihilator, or its radical |
| III.1.3 | `associatedPrimeSpectrum_linearMap`: `Ass Hom(N,M) = Supp N ∩ Ass M` |
| III.2.1 | `lemma_2_1`: all five conditions, including the localization criterion |
| III.2.2 | `III_2_2_a`, `III_2_2_b`: regular sequences and Ext vanishing with the hypotheses in the source |
| III.2.3–III.2.4 | `depth`, `le_depth_iff`, `le_depth_iff_exists_regular`, `le_depth_iff_exists_test_module`: the actual Ext-based definition and depth criteria |
| III.2.5 | `III_2_5`: `depth_I M = depth_I(M/fM) + 1` for a regular `f ∈ I`, including infinite depth |
| III.2.6, finite depth | `III_2_6`: any regular sequence extends to a maximal one of length equal to depth; `exists_regular_extension` also permits any intermediate finite length |
| III.2.6, infinite depth | `exists_infinite_regular_extension`: any finite regular prefix extends to one infinite sequence whose every finite prefix is regular |
| III.2.7 | `III_2_7`: depth is finite exactly when the support of the module meets `V(I)` |
| III.2.8 | `depth_eq_extDepth`: depth is the first nonzero Ext degree for any finite test module with the prescribed support; includes the residue-module case |
| III.2.9–III.2.10 | `III_2_9`, `III_2_10`: infimum of local depths over `V(I)`, and over maximal ideals for a semilocal ring |
| III.2.11 | `III_2_11_flat`, `III_2_11_faithfullyFlat`: flat base change cannot decrease depth, and faithful flatness gives equality |
| Algebraic input to III.§3 | `le_depth_iff_localCohomology_vanishes`, `depth_eq_iInf_localCohomology`: depth is detected by actual algebraic local cohomology, including infinite depth; the two Ext conventions are linked by a proved vanishing equivalence |
| Affine group-valued bridge for III.§3 | `le_depth_iff_affine_H_Z_vanishes`, `depth_eq_iInf_affine_H_Z`: depth is the first nonzero actual supported sheaf-cohomology degree; `affine_H_Z_vanishes_iff_localDepth` and the test-module/quotient criteria connect it to localized depths and genuine Ext |
| Literal affine stalk depth | `affineStalkRingEquiv`, `affineModuleStalkSemilinearEquiv`, `localDepth_eq_actual_stalk_depth`: the genuine structure and associated-module stalks identify with localizations compatibly with scalars, so original local depth is actual stalk depth |
| III.3.1(i) iff (iii) | `derivedSupported_vanishes_iff_local_H_Z`: for arbitrary actual abelian sheaves, lower vanishing of original derived supported sheaves is equivalent to lower vanishing of actual supported cohomology on every open; the proof uses actual spectral convergence and sheafification |
| III.3.3(i)/(iii)/(iv), all nonnegative thresholds | `coherent_depth_iff_derivedSupported_vanishes`, `coherent_depth_iff_local_H_Z_vanishes`: literal actual module-stalk depth along the support is equivalent to original derived supported-sheaf vanishing and local supported-cohomology vanishing, for coherent modules on arbitrary locally noetherian schemes; actual affine-chart cohomology transport and all finiteness conditions are proved |
| III.3.1(ii) / III.3.3(ii), all positive thresholds | `derivedSupported_vanishes_iff_intersectionRestriction`, `coherent_depth_iff_intersectionRestriction`: actual ordinary cohomology restriction from `V` to `V ∩ (X ∖ Z)` is bijective below the last degree and injective in the last degree; `relativeRestriction_eq_ordinary` proves the all-degree map comparison, and the actual nested-open/intersection sheaf and cohomology transport are proved |
| III.3.2, threshold two / I.2.13, `N = 1` | `derivedSupported_vanishes_two_iff_intersectionRestriction_zero`, `intersectionRestriction_one_injective_of_zero_bijective`: for arbitrary abelian sheaves, all-open actual degree-zero restriction bijectivity suffices; original supported sheaves vanish in degrees zero and one, and the discarded degree-one injectivity follows |
| III.3.2, every threshold at least two / I.2.13, every `N > 0` | `derivedSupported_vanishes_iff_intersectionRestriction_bijective`, `intersectionRestriction_highest_injective_of_lower_bijective`: lower actual ordinary restriction bijectivity on every open suffices; highest-degree injectivity follows, without assuming a separate local-effacement comparison |
| III.3.2–III.3.3, coherent form | `coherent_depth_iff_intersectionRestriction_bijective`: literal coherent module-stalk depth at least `n + 2` along the support iff actual ordinary restriction is bijective in degrees below `n + 1` on every open |
| III.3.4, positive thresholds | `example_3_4`: local depth, actual supported cohomology, relative restriction, and residue-field Ext criteria |
| III.3.5, affine Hartogs | `two_le_depth_iff_affineRestriction_bijective`, `affineRestriction_bijective_of_localDepth`: actual associated-sheaf section restriction is bijective at depth at least two, and injective at depth at least one |
| III.3.5, general locally noetherian schemes, structure sheaf | `structureStalkDepth_two_le_iff_restriction_bijective`, `structureGlobalHartogsRingEquiv`: literal local structure-ring depth at least two along the closed support is equivalent to bijective actual restriction on every open, via proved affine-open compatibility and sheaf gluing |
| III.3.5, coherent coefficients | `coherent_hartogs_iff`, `coherentHartogsEquiv`: for actual `M : X.Modules` with mathlib's local `M.IsFinitePresentation`, literal module-stalk depth at least two along the closed support is equivalent to actual bijective restriction on every open; finite affine coefficient charts, actual stalk modules, and semilinear restriction/stalk depth comparisons are proved |
| III.3.6, affine connectedness equivalence | `affine_connected_iff_of_localDepth`: removing the depth-two closed support preserves connectedness; proved using actual structure-sheaf restriction and clopen characteristic sections, with no assumed idempotent/section comparison |
| III.3.6, affine connected components | `affineConnectedComponents_bijective_of_localDepth`: the actual inclusion-induced map on connected components is bijective; `affineConnectedComponentsEquiv` has this map as its forward function |
| III.3.6, general locally noetherian schemes | `schemeConnectedComponents_bijective_of_stalkDepth`, `schemeConnectedComponentsEquiv`: actual complement inclusion induces a bijection on connected components under literal structure-stalk depth at least two; proved using genuine global-idempotent/clopen correspondence, with no global quasi-compactness hypothesis |

The source's regularity convention only requires injectivity of each
successive scalar multiplication. This is mathlib's `IsWeaklyRegular`.
It permits a zero final quotient. Consequently III.2.2 does not add the
condition `IM ≠ M` used in mathlib's existing Rees theorem. Part (a) also
does not add noetherian or finite-module hypotheses.

There is a necessary qualification to the unqualified wording of III.2.6:
finite maximal sequences exist at **finite depth**. At infinite depth,
`exists_regular_extension_of_depth_top` proves that every finite regular
sequence can be extended; `exists_infinite_regular_extension` constructs
one compatible infinite extension. The unit ideal provides a concrete example:
its depth is infinite and arbitrarily long lists of `1` are regular in
SGA's convention. `Examples.lean` also proves depth zero at the zero ideal
on a nonzero finite module, and depth one for `ℤ` along `(2)`. The English
translation has not been silently altered.

III.3.3(v)/(vi) are proved on noetherian affines (`III_3_3_v`, `III_3_3_vi`,
`III_3_3_vi_quotient`). III.3.7 is connectedness of complements under the
depth/dimension hypothesis (`III_3_7_complement`). III.3.8's antifilter and
finite-component chain data are in `AntifilterConnectedness.lean`. III.3.10's
depth-less-than-two obstruction is `III_3_10_depth_lt_two`. III.3.12's Koszul
vanishing above the number of equations, detected on the structure sheaf, is
`III_3_12`. III.3.3(v)/(vi) are affine module Ext (`III_3_3_v`,
`III_3_3_vi`); sheaf Ext on a general locally noetherian scheme remains.
III.3.7's complement π₀ bijection is `III_3_7_complement`; its actual finite
component chains are `III_3_7_list` and `III_3_7_codimension_list`, with the
numerical codimension defined by the infimum of actual structure-stalk dimensions.
III.3.8's full antifilter equivalence is `III_3_8`, on locally noetherian spaces
with the source's local-membership condition. Local finiteness of components
and closedness of arbitrary component unions are proved.
III.3.9 is `III_3_9` in `EquidimensionalityCriterion.lean`:
the actual localized depth/dimension hypothesis and equality of lengths of
saturated prime chains with fixed endpoints imply equidimensionality. The
adjacent-component dimension comparison is proved from that chain condition.
III.3.13's principal-curve vanishing, non-UFD obstruction, and relative
comparison `H_Y^{n+2} ≅ H^{n+1}(X-Y)` on a noetherian affine are
`III_3_13_principal`, `III_3_13_exists_non_principal`, and
`III_3_13_relative`; existence of a non-CI curve on a normal surface
remains.

The all-degree coherent depth criterion now uses original supported sheaves on
general locally noetherian schemes, with literal actual module-stalk depth.
The affine group-valued depth/supported-cohomology bridge, actual Hartogs
restriction, and full affine connected-components bijection are proved. Literal
affine stalk compatibility, structure-sheaf Hartogs, and the full III.3.6
connected-components bijection on every locally noetherian scheme are also
proved. The full III.3.5 Hartogs equivalence now covers actual coherent module
sheaves. Mathlib has no named `IsCoherent` class here: the theorem uses its
local finite-presentation condition, which is the coherent condition on a
locally noetherian scheme. Higher-threshold redundancy is proved using the
actual embedding into the direct image of an injective on the complement,
followed by coefficient dimension shifting. It does not require a separate
sheafification comparison for positive ordinary cohomology; that comparison
itself is not claimed here. Sections 1–2 are covered with the explicit
finite-depth qualification for maximal finite sequences in III.2.6.

## SGA 2 IV — Dualizing modules and functors

English: `translation/SGA2/ExposeIV/`. Lean: `lean/SGA/SGA2/ExposeIV/`.
This exposé is partial and imported by the root library.

| Source | Formalized result |
| --- | --- |
| IV.1 opening | `additiveFunctorModule`, `additiveFunctorModuleLift`: the original additive functor induces the scalar action through scalar endomorphisms; all its maps are linear for that action, and forgetting recovers the original functor |
| IV.1.1 | `additiveFiniteModuleEvaluation_isIso_iff`, `additiveFiniteModuleRepresentationIso`: the actual canonical evaluation map is an isomorphism precisely when the original abelian-group-valued additive contravariant functor is left exact; no pre-existing scalar action or representing module is assumed |
| IV.1 categorical equivalence | `finiteModuleFunctorEquivalence`: arbitrary modules are equivalent to additive left-exact contravariant functors on finite modules; the forward functor is actual restricted Hom, with full faithfulness proved by evaluation at the ring |
| IV.1.2 | `additiveModuleEvaluation_isIso_iff_preorderLimits`, `additiveModule_representable_iff_preorderLimits`: the original additive functor on all modules is canonically represented by its actual `T(R)` iff it preserves arbitrary preorder-indexed projective limits, without filteredness; actual finite-submodule colimits and the precise preorder-to-all-limits bridge are proved |
| IV.1.3 foundations | `SupportedFGModuleCat`, `supportedQuotientStage`, `supportedQuotientStage_covers`, `supportedFunctorDiagram`: the actual support-defined finite module category is abelian, genuine quotient-ring restriction gives fully faithful exact stages covering all objects, and `T(R/Jⁿ)` has its canonical linear quotient-induced transitions and proved annihilator bounds; transitions are injective for left-exact `T` |
| IV.1.3 representation | `additiveSupportedFunctorEvaluation_isIso_iff`, `additiveSupportedFunctorRepresentationIso`: the original canonical evaluation into the actual colimit of `T(R/Jⁿ)` is an isomorphism iff `T` is left exact; all scalar, transition, choice-independence, naturality and finite-source factorization steps are proved |
| IV.1.3 categorical equivalence | `supportedModuleFunctorEquivalence`: actual restricted Hom gives an equivalence of arbitrary modules supported in `V(J)` with additive left-exact functors on finite supported modules; full faithfulness is proved via actual finite cyclic submodules, and essential surjectivity uses the original colimit |
| IV.1.4 Hom detection input | `subsingleton_linearMap_iff_of_support_eq_zeroLocus`: a finite full-support test module detects zero arbitrary supported targets, without requiring the target to be finite; actual represented-functor vanishing detection is also proved |
| IV.1.4 | `supportedDeltaFunctor_vanishing_tfae`: all three lower-vanishing conditions for arbitrary integer-indexed bounded-below exact delta functors; `IntegerCohomologicalSequence` records actual natural connecting maps and all exactness pieces, and the needed left exactness is derived from preceding-degree vanishing |
| IV.2.1 | `finiteSupportedHomExact_iff_injective`: for an actual ideal-power-torsion module, exactness of contravariant Hom on finite supported modules is equivalent to categorical injectivity; the proof reduces to Baer using Artin–Rees |
| IV.2.1 support formulation | `powerTorsion_eq_top_iff_support_subset_zeroLocus`, `finiteSupportedHomExact_iff_injective_of_support`: actual support in `V(J)` agrees with elementwise ideal-power torsion, without assuming the module finite, giving the original support-hypothesis Hom criterion |
| IV.2.1 original functor | `supportedFunctorExact_iff_injective_colimit`, `supportedFunctor_preservesHomology_iff_injective_colimit`: for the original additive left-exact `T`, preservation of all genuine short exact sequences is equivalent to injectivity of its actual colimit in the category of all modules |
| IV.2.2 | Ideal-power torsion in an injective module is injective, reusing the proved Exposé II theorem |
| IV.3.1, Hom-duality implication | `moduleBidualEvaluation_isIso_of_artinian_support`, `moduleHomDual_finite_of_artinian_support`, `moduleHomDual_length_of_artinian_support`: arbitrary injective `H` with residue-field Hom tests gives original canonical Hom biduality, finite Hom values, and length preservation on every finite supported module; the actual finite-length property follows from noetherian `R` and Artinian `R/J`, not from an extra hypothesis |
| IV.3.1, original functor | `supportedFunctor_duality_tfae`: all four conditions for the original additive abelian-group-valued `T`, with left exactness and finite values inside condition (i), actual canonical `M → T(T(M))`, actual residue values, actual injective representations, and length preservation |
| IV.3.1, canonical comparisons | `supportedFunctorBidualEvaluationNatTrans`, `supportedFunctorValueIsoOfRepresentation`: actual twice-iterated functor evaluation is natural; any original abelian-group-valued representation automatically respects the canonical scalar actions |
| IV.3.2 | `supportedFunctor_exact_and_length_iff_length`, `supportedFunctor_duality_iff_length`: under IV §3's standing left-exactness hypothesis, length preservation alone implies exactness and canonical duality; finite values are derived |
| IV.4.3 | `finite_local_coinduction_supported_duality`: original `Hom_A(B,I)` with its actual `B`-action preserves all three supported-dualizing conditions; genuine Hom adjunction and canonical bidual-evaluation comparison are proved, with no extra local-homomorphism hypothesis |
| IV.4.4, proper quotients | `quotientCoinductionAnnihilatorIso`, `quotientAnnihilator_supported_duality`: evaluation at one identifies the actual coinduced module with the ideal annihilator equipped with the standard quotient action, and transfers supported duality |
| IV.4.2, existence | `nonlocalDualizingFunctor`, `nonlocalDualizingEvaluationIso`, `nonlocalDualizingAntiEquivalence`: actual exact linear Hom duality on the entire finite-length category, constructed using the injective envelope of the sum of all residue fields; actual maximal-ideal annihilators have length one |
| IV.4.2, local comparison | `localFiniteLengthEquivalence`: identity-on-modules equivalence with the original finite closed-point-supported category and literal compatibility with original Hom maps |
| IV.4.2, local Artinianness | `allResidueFieldEnvelope_locallyArtinian`: the actual nonlocal coefficient is locally Artinian, proved using associated primes under essential embeddings |
| IV.4.2, cofinite index | `quotient_annihilator_isFiniteLength`, `cofiniteRingQuotientDiagram`: actual annihilator quotients of finite-length modules have finite length; cofinite ideals form a reverse-inclusion filtered category with original quotient maps, over any commutative ring |
| IV.4.2, uniqueness foundation | `locallyArtinianRestrictedHomFullyFaithful`, `locallyArtinianIsoOfFiniteLengthHom`: actual Hom on finite-length tests is fully faithful on locally Artinian modules over a noetherian ring, recovering specified natural transformations and isomorphisms |
| IV.4.2, original nonlocal representation | `additiveCofiniteFunctorEvaluation_isIso_iff`, `additiveCofiniteFunctorRepresentationIso`: canonical evaluation into the actual cofinite-ideal colimit is invertible exactly for additive left-exact functors on the whole finite-length category; all original actions, point maps, quotient transitions, and stage comparisons are proved, over any commutative ring |
| IV.4.2, nonlocal Hom equivalence | `locallyArtinianFiniteLengthFunctorEquivalence`: original Hom identifies locally Artinian modules over a noetherian ring with additive left-exact finite-length functors; the constructed original colimit supplies essential surjectivity |
| IV.4.2, nonlocal injectivity | `finiteLengthHomExact_iff_injective`, `cofiniteFunctorExact_iff_injective_colimit`: original finite-length Hom exactness detects injectivity of arbitrary locally Artinian coefficients; exactness of any original additive left-exact functor is equivalent to injectivity of its actual colimit, via proved cofinite Artin–Rees/Baer reduction |
| IV.4.2, arbitrary original dualizing functor | `nonlocalInvolutiveRepresentationIso`, `nonlocalInvolutiveCoefficient_injective`, `nonlocalInvolutiveAnnihilator_length`: a linear finite-length functor with a natural involution has its original cofinite-colimit representation, locally Artinian injective coefficient, and actual maximal-ideal annihilators isomorphic to their residue fields; no residue tests or length preservation are assumed |
| IV.5.1, actual bidual completion | `finiteBidualCompletionIso`, `finiteBidualCompletionIso_evaluation`: double Hom of an arbitrary finite module is its actual adic completion, and original evaluation becomes the original completion map |
| IV.5.1, dual completeness | `homDualCompletionIso_hom`, `SupportedDualizingModule.supported_dual_isAdicComplete`, `matlisHomToComplete`: original Hom from locally Artinian finite-socle modules lands in the literal complete category with finite-length power quotients |
| IV.5.1, complete-base formulation | `matlisCompleteAntiEquivalence`, `matlisCompleteCategoryAntiEquivalence`: actual linear Hom functors in both directions, with canonical natural evaluations, give inverse equivalences over a complete noetherian local base |
| IV.5.1, `CA` completion transport | `matlisArtinianCompletionEquivalence`, `completionSocleRestrictionEquiv`: actual tensor/restriction identify finite-socle locally Artinian categories, with original maps, without assuming completed-ring noetherianity |
| Noetherian completion / IV.5.1 | `adicCompletion_isNoetherianRing`, `matlisCompletedRingAntiEquivalence`: actual adic completions of noetherian rings are noetherian for arbitrary ideals; actual `CA(R)` is opposite-equivalent to finite modules over the completion via original scalar change and completed-ring Hom |
| IV.5.1, original Hom comparison | `matlisCompletedRingHomIso`: the equivalence's actual forward functor, followed by restriction, is naturally original-ring Hom, with explicit tensor-unit formula, inverse actual tensor extension, and coefficient naturality |
| IV.5.1, full general-base proposition | `matlisAntiEquivalence`: literal `CA(R)ᵒᵖ ≌ DA(R)`, with forward exactly original-ring Hom and inverse actual completed-ring Hom through the original completion/restriction comparisons; no completeness assumption on `R` |
| IV.5.1, transport clause | `matlisCompleteCompletionEquivalence`, `matlisDualityForwardCompletionIso`, `matlisDualityInverseCompletionIso`: actual module completion and restriction identify `DA`, and both Hom transport squares commute naturally in the original categories |
| IV.5.1, finite-length intersection | `matlisFiniteLengthIntersectionEquivalence`, `finiteLength_matlisHomToComplete`: finite modules intersect `CA` exactly in the original finite-length category; actual Hom restrictions and canonical evaluations agree with finite-length duality |
| IV.5.1, finiteness and cogeneration | `finite_of_isHausdorff_of_finite_reduction`, `SupportedDualizingModule.moduleBidualEvaluation_isIso_of_dual`: topological Nakayama and original all-module Hom cogeneration are proved; actual finite socle has finite-length power annihilators |
| IV.5.1, full Artinian characterization | `matlisArtinianModuleProperty_iff_isArtinian`: the literal locally-Artinian finite-socle category consists exactly of all Artinian modules over every noetherian local base; original Hom orthogonals embed the submodule lattice into the dual's opposite lattice, and completion preserves the whole supported submodule lattice |
| Essential-extension socles | `EssentialIn.localSocle_le`, `EssentialModuleMap.localSocleMap_surjective`, `EssentialModuleMap.localSocle_finite`: every essential submodule contains the actual socle; the unchanged embedding induces a bijection on socles and preserves finite socle, including for the constructed injective envelopes |
| IV.5.3–5.4, regular-local foundations | `regularLocal_isDomain`, `regularLocal_exists_regular_parameters`: genuine regular local rings are domains and have regular systems of parameters of their actual Krull dimension; every minimal generating list is regular |
| IV.5.3–5.4, off-degree vanishing | `regularLocal_residueField_projectiveDimension`, `regularLocal_moduleExt_ring_isZero_of_finiteLength`: residue projective dimension equals Krull dimension, finite-length projective dimension is bounded by it, and original module-valued Ext into the ring vanishes in every other degree |
| IV.5.3, depth and arbitrary lower vanishing | `regularLocal_depth_eq`, `regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator`: literal depth equals Krull dimension, and lower Ext vanishes for arbitrary modules killed by a maximal-ideal power, in both Ext models |
| Finite-module projective-dimension bound | `finite_hasProjectiveDimensionLE_of_residueField`, `regularLocal_finite_hasProjectiveDimensionLE`: support-dimension induction removes actual closed-point torsion and quotients by an actual regular element; a residue-field bound extends to every finite module over a noetherian local ring |
| Baer and higher cyclic Ext tests | `injective_of_cyclic_ext_one`, `hasInjectiveDimensionLE_of_cyclic_ext`, `hasProjectiveDimensionLE_of_cyclic_bound`: actual cyclic Ext tests and genuine injective dimension shifting control arbitrary modules, without noetherianity in the cyclic-to-arbitrary step |
| IV.5.3, full global-dimension bound | `moduleGlobalDimension_eq_residueField`, `regularLocal_moduleGlobalDimension_eq`, `regularLocal_ext_subsingleton_of_gt`, `regularLocal_moduleExt_isZero_of_gt`: global projective dimension equals the residue-field dimension over every noetherian local ring (including infinite dimension), hence equals Krull dimension over a regular local ring; upper Ext vanishing has both arguments arbitrary |
| Ext comparison naturality | `moduleExtLinearIsoAbelianExt_naturality_first`, `moduleExtLinearIsoAbelianExt_naturality_coefficient`: the unchanged canonical linear comparison respects original maps in both variables in every degree, over any commutative ring |
| IV.5.4, exactness and actual representation | `regularLocalTopExtFunctor_exact`, `regularLocalTopExtRepresentationIso`, `regularLocalTopExtModule_injective`: the genuine derived-category top Ext functor is exact and canonically represented by its actual injective quotient-Ext colimit; no top residue value is assumed |
| IV.5.3, top residue value | `koszulTopCohomologyIsoQuotient`, `regularLocal_topResidueModuleExtIso`: actual top Hom–Koszul cohomology is the coefficient quotient, and original module-valued `Extⁿ_R(k,R)` is the actual residue module; `moduleExtAddEquivAbelianExt` also compares the two genuine Ext models as additive groups |
| IV.5.4, original functor duality | `moduleExtLinearIsoAbelianExt`, `regularLocalTopExtFunctor_duality`, `regularLocalTopExtModule_dualizing`: the genuine linear Ext comparison proves residue tests for the original canonical scalar action; top Ext and its actual representing quotient-Ext colimit are dualizing |
| IV.5.4, local cohomology identification | `regularLocalTopExtModuleIsoLocalCohomology`, `regularLocal_localCohomology_dualizing`, `regularLocalTopExtLocalCohomologyRepresentationIso`: genuine first-variable Ext naturality compares the original quotient diagrams and colimits, including stage maps; actual top local cohomology is supported dualizing and represents original top Ext |
| IV.5.4, geometric footnote | `regularLocalTopExtModuleIsoSupportedCohomology`: the actual representing module's underlying additive group is original affine supported-sheaf cohomology; no separately defined geometric scalar action is compared |
| IV.5.5, initial existence assertion | `regularLocal_localCohomology_nonempty_iso_macaulay`: the actual local cohomology and Macaulay modules are noncanonically isomorphic; explicit residue-pairing and parameter-independence clauses remain open |
| IV.5.5, power transitions | `koszulTopCohomologyRing_transition_add_apply`, `koszulTopCohomologyRing_transition_monomial`: the original top Koszul cohomology diagram becomes the stated product-multiplication transition on actual power-ideal quotients; monomial classes have all exponents shifted by the same amount, with no monomial-basis assertion |
| IV.5.5, explicit quotient colimit | `koszulTopQuotientDiagram`, `koszulTopQuotientColimitIsoLocalCohomology`: direct product-multiplication maps on the actual power-ideal quotients form a diagram whose colimit is original local cohomology in top Koszul degree over a noetherian ring, with original stage-map compatibility; arbitrary lists and coefficients are allowed |
| IV.5.2, continuous dual | `continuous_linearForm_adic_iff`, `macaulayModuleIsoContinuousDual`: continuity to the discrete coefficient field is exactly vanishing on an ideal power; original quotient-dual colimit is canonically the continuous dual of the original adic ring, without completeness |
| IV.5.5, actual power-series basis | `powerSeriesPowerQuotientBasis_apply_prod`, `powerSeriesPowerQuotient_finrank`: actual coordinate-power quotients have their bounded-monomial basis and dimension `r^d`, including zero-variable and zero-power cases |
| IV.5.5, finite-stage residue | `powerSeriesPowerQuotientResidue_mul_complement`, `powerSeriesPowerQuotientResidueEquiv`: actual product-residue pairing on positive coordinate-power quotients is perfect; complementary monomials recover every coefficient |
| IV.5.5, explicit power-series comparison | `powerSeriesLocalCohomologyIsoMacaulay`, `powerSeriesLocalCohomologyIsoContinuousDual_stage_apply`: original product transitions preserve the residue functionals; the actual quotient colimit gives an explicit ring-linear local-cohomology/Macaulay isomorphism, with literal product-coefficient formula at every original stage |
| IV.5.5, glued residue form | `powerSeriesLocalCohomologyResidue_basis`, `powerSeriesLocalCohomologyResidue_nondegenerate`, `powerSeriesTopLocalCohomology_supportedDualizing`: the original local-cohomology residue form is coefficient-field linear, has the stated monomial formula and nondegenerate product pairing, and its coefficient is supported dualizing; no Cohen presentation or completed differential module is assumed to have been constructed |
| IV.4.5 | `localArtinianTensorCompletionEquiv`, `supportedCompletionEquivalence`, `localArtinianCompletionEquivalence`: the actual tensor map is invertible on arbitrary locally Artinian modules, and original tensor/restriction give inverse equivalences on the actual supported and locally Artinian categories; no extra noetherianity hypothesis on the completed ring |
| IV.4.5, submodules and finiteness | `completion_submodule_smul_mem`, `completion_restrictScalars_finite`: every original-ring submodule of a supported completed-ring module is stable under its existing completed action; restriction preserves finite generation |
| IV.4.5, finite category | `finiteSupportedCompletionEquivalence`: original tensor/restriction give an equivalence on finite supported modules, retaining the actual unit/counit and commuting with the full supported equivalence |
| IV.4.6, supported convention | `completion_supportedDualizingModule_iff`, `SupportedDualizingModule.completion`: actual restriction and tensor extension preserve supported duality, with actual linear Hom restriction, canonical bidual-evaluation compatibility, and underlying-group identification; no extra noetherianity hypothesis on the completion |
| IV.4.9, canonical representing module | `supportedFunctorColimit_locallyArtinian`, `supportedFunctorColimit_annihilator_isFiniteLength`, `supportedFunctorAnnihilatorFiltrationIsColimit`: literal local Artinianness, finite-length actual annihilator stages under duality, and the original module as their categorical colimit with literal inclusions |
| IV.4.7, explicit supported convention | `nonempty_moduleInjectiveEnvelope`, `supportedDualizingModule_iff_injective_essential_residue`, `exists_supportedDualizingModule`, `SupportedDualizingModule.nonempty_iso`: actual envelopes constructed by Zorn, full supported characterization, existence, and noncanonical uniqueness |
| IV.4.1 / IV.4.3–4.4 / IV.4.9, supported convention | `supportedDualizingModule_iff_support_functorDuality` ties the definition to original abelian-group-valued Hom duality plus actual support; `SupportedDualizingModule.finite_coinduction`, `.quotient_annihilator`, and `.locallyArtinian` give the named transfers and local Artinian property |
| IV.5 opening, anti-equivalence | `supportedFunctorAntiEquivalence`: the actual original dual functor and its right opposite, with original inverse-evaluation counit and both coherent triangle identities; standard adjointification changes neither functor nor counit |
| IV.5 opening, orthogonality | `supportedHomOrthogonalOrderIso`, `supportedFunctorOrthogonalOrderIso`, `mem_supportedFunctorOrthogonalOrderIso`: the actual vanishing orthogonal and coorthogonal are inverse order-reversing submodule bijections; original-functor membership is literal canonical evaluation vanishing |
| IV.5 opening, length/colength | `supportedFunctorOrthogonal_length_eq_colength`, `supportedFunctorOrthogonal_colength_eq_length`: the original orthogonal bijection exchanges actual submodule length and quotient length, including infinite lengths |
| IV.5 opening, Artinian-local ideals | `artinianLocalHomIdealOrderIso`, `mem_artinianLocalHomIdealOrderIso`: the actual injective residue-tested coefficient has an order-reversing ideal/submodule bijection, whose image of an ideal is literally its annihilator in that coefficient |
| IV.5 opening, cyclic/socle criterion | `supportedFunctor_monogenic_iff_socle_length_le_one`: literal single generation is equivalent to the original dual's socle having length at most one, including zero; `localSocle_eq_sSup_simple` identifies the maximal-ideal annihilator with the sum of simple submodules |
| IV.5.2, Macaulay example | `macaulayFunctor_duality`, `macaulayModule_supportedDualizing`, `macaulayFunctorRepresentationIso`: literal `Hom_K(-,K)` with its source-induced ring action, actual quotient-dual colimit and canonical representation; only the residue field is required finite over `K`; `coefficientField_finrank_eq_residueDegree_mul_length` gives the dimension–length formula |

The IV.1.1 proof constructs the source's evaluation from maps `R → M`.
Finite free modules are handled by coordinate reconstruction; over a noetherian
ring the kernel of a finite free cover is finite, and left exactness descends
the reconstructed value. The representing module is the canonical module
on the functor's actual value at `R`, with no finiteness assumption on that value.

IV.1.2 extends the same actual evaluation to all modules. The genuine cocone
of finite submodule inclusions is colimiting, so IV.1.1 and preservation of
its opposite limit prove invertibility on arbitrary modules. The source's
preorder-only condition is sufficient: thin skeletons of discrete and cospan
categories give actual preorder presentations of products and pullbacks,
which force preservation of all small limits. All indexing sets and modules
use the stated universe; no filteredness is silently imposed.

IV.1.3 uses the actual quotient-induced diagram and its actual colimit.
The colimit support is proved without left exactness. Under left exactness,
its stage maps are injective, so the finite image of any map from a finite
module lies in one stage. The original stagewise evaluation then proves the
specified global evaluation bijective. IV.1.4 applies this result by integer
induction from the supplied lower bound, deriving each required left-exact
degree from the original connecting sequence.

The IV.3.1 Hom-model implication uses genuine double Hom evaluation
`x ↦ (f ↦ f x)`. Residue-field tests give the canonical simple-module
evaluation isomorphism by nonvanishing and Schur's lemma; the actual short
five lemma and finite-length induction extend this to all finite supported
modules. Their finite length is derived from an annihilating ideal power
and the Artinian power quotient. Neither finiteness of `H` nor duality on
all modules is assumed. Full transport to the original `T` and the four-way
equivalence are now proved: canonical biduality forces dual restriction maps
to be surjective by applying reflexivity to their actual cokernels. Residue
tests follow from their actual annihilators and simplicity. For IV.3.2,
left exactness of Hom and finite-length additivity force surjectivity; the
canonical representation transfers this to the original left-exact functor.
The original functor's scalar action, actual finite-valued factorization,
and natural map into actual `T(T(M))` are constructed, not assumed as extra
comparison data. IV §5's opening anti-equivalence and orthogonality results
are proved for the original functor. Canonical reflexivity of actual supported
quotients supplies separation of elements and both double-orthogonal identities;
the resulting actual lattice anti-isomorphism exchanges length and colength.
Over a local ring, Nakayama identifies actual single generation with residue
quotient length at most one. The orthogonal of the maximal-ideal multiple is
the actual dual socle, giving the cyclic/socle criterion for the original `T`.
Finite coinduction and quotient annihilators preserve the actual support,
not just the Hom tests. The tensor assertion of IV.4.5 holds for arbitrary
locally Artinian modules: finite nilpotent cyclic submodules and flatness of
the completed ring prove that the original scalar-extension map is bijective.
The result concerns tensoring with the completed ring, not taking the adic
completion of the coefficient module.
Finite length of all ideal-power annihilators is proved under duality only;
it is not assumed for arbitrary locally Artinian modules in the tensor proof.

IV.4.7 is proved with the supported representing-module convention explicit.
Raw Hom duality on finite closed-point-supported modules alone does not imply
that the coefficient has this support: off-support summands can be invisible.
The proof does not claim unqualified uniqueness for such arbitrary Hom targets.
With actual support, canonical Hom duality is equivalent to being an injective
essential extension of the residue field. Envelopes are constructed from
enough injectives using two Zorn arguments; support of an injective essential
residue extension is then derived using the injectivity of ideal-power torsion.
IV.4.2 now has a constructed exact linear finite-length duality, its canonical
evaluation isomorphism, length-one maximal-ideal annihilators, and local
Artinianness of its actual nonlocal coefficient. General nonlocal representation
is now proved: every additive left-exact finite-length functor is canonically
represented by its actual cofinite-ideal colimit. Over a noetherian ring,
original Hom gives an equivalence with locally Artinian modules. Exactness
of the original functor is equivalent to injectivity of its actual colimit,
by cofinite Artin–Rees/Baer reduction. For any original linear finite-length
functor with a natural involution, its actual representing coefficient is
injective and locally Artinian, and every maximal-ideal annihilator is the
corresponding residue module, of length one. No separate socle-decomposition
theorem is asserted, and the supplied involution is not identified with
canonical bidual evaluation. Local Artinianness and coefficient uniqueness
concern the constructed representative or already-locally-Artinian modules,
not arbitrary raw Hom targets with invisible summands.
IV.4.5's categorical completion equivalences are
proved using actual scalar change; the completed ring's finitely generated
maximal ideal suffices, without assuming a separate noetherianity theorem.
IV.5.2 has the actual Macaulay quotient-dual colimit and its canonical
identification with the continuous coefficient-field linear dual of the
original adic ring. Continuity is proved equivalent to vanishing on an
ideal power, and the comparison uses original quotient maps; completeness
of the ring is not assumed. IV.4.6 transfers the actual
supported-dualizing definition in both directions through completion, using
the actual Hom comparison and original canonical evaluation. The structural
remarks of IV.4.8 and later dualizing-module results remain incomplete.
IV.5.1 is proved over a complete noetherian local base with the actual Hom
functors and canonical evaluations. Over a general noetherian local base,
finite biduals are actual completions and the original `CA` dual lands in
literal `DA`. Completion transport of the actual `CA` category is proved;
noetherianity of actual adic completions is proved for every ideal, and the
resulting actual scalar-change/Hom equivalence with finite completed-ring
modules is constructed and naturally compared with original-ring Hom.
Actual module completion and scalar restriction identify the original `DA`
categories. `matlisAntiEquivalence` proves IV.5.1 over a general noetherian
local base with forward exactly original-ring Hom; both natural completion
transport squares are proved. The explicit supported representing-module
convention remains in force. The final packaged equivalence unit is not
claimed to be definitionally the canonical evaluation.
The regular-local domain and regular-parameter foundations for IV.5.3–5.4
are proved from the actual regular-local class, as are the actual residue
projective dimension and off-degree Ext vanishing for all finite-length
first arguments. The top Ext functor is exact and canonically represented
by its actual injective colimit. The original regular Koszul augmentation is
a proved resolution and its actual finite-stage Ext comparison is invertible.
The concrete top module-valued residue Ext is computed as an actual linear
isomorphism. The canonical comparison to derived-category Ext is proved
linear, exactly upgrading the existing additive comparison, and natural in
both variables. Literal maximal-ideal depth equals Krull dimension, and
lower Ext vanishing also holds for arbitrary modules annihilated by a
maximal-ideal power. Hence IV.5.4's original top-degree functor is dualizing,
and its actual representing colimit is original algebraic local cohomology,
with the actual quotient transitions and colimit stage maps respected.
Original affine supported-sheaf cohomology is compared as an additive group;
compatibility with a separately defined geometric scalar action is not claimed.
IV.5.3's global dimension equality and upper vanishing for arbitrary modules
are now proved. Induction on actual support dimension extends the finite-length
bound to all finite modules. Baer's criterion and actual injective dimension
shifting extend cyclic tests to all modules. The supremum of the original
projective dimensions equals the residue-field dimension over any noetherian
local ring, even when infinite; for regular local rings it equals Krull
dimension. Both arguments of upper Ext vanishing may be arbitrary.
IV.5.5's initial noncanonical local-cohomology/Macaulay
isomorphism is proved, as are the original product power transitions and
monomial-class shifts on actual quotient modules. The direct power-ideal
quotient diagram has original top local cohomology as its colimit, with
original stage maps preserved. For literal finite-variable power series
rings, coordinate-power quotients have the actual bounded-monomial basis
and dimension `r^d`, including the zero-variable and zero-power cases. For
positive powers, top-coefficient extraction of products is a perfect pairing
on the original quotient, with complementary monomials recovering every
coefficient. The finite forms now glue through the original product transitions
and the proved positive-index cofinality. This gives the explicit ring-linear
isomorphism from original maximal-ideal top local cohomology to the actual
continuous dual and Macaulay module. Its coefficient-field linear residue
form has the stated monomial formula and a nondegenerate product pairing.
The comparison is proved equal to its explicit colimit construction, not
obtained by abstract uniqueness. Constructing a coefficient field and Cohen
presentation for arbitrary complete regular local rings, completed
differentials, parameter independence, and field compatibility remain open.
IV.2.1 is proved for the original functor, using an actual
lift of finite supported short exact sequences and the canonical representation.
## SGA 2, Exposé V — Local duality and local cohomology

Entry point: `lean/SGA/SGA2/ExposeV.lean`. The main results and conventions
are summarized below, followed by the individual declarations.

- **§1:** The displayed Hom complex, both long exact sequences, composition,
  and comparisons with Ext are proved. Injective horseshoes and simultaneous
  row comparisons give coherent changes between chosen resolutions.
- **V.2.1:** The canonical map from quotient Ext stages is a natural
  isomorphism on finite modules over a regular local ring in every
  complementary degree. Its transpose identifies dual local cohomology with
  completed complementary Ext, and with Ext itself over a complete base.
- **V.3.1:** Upper vanishing, Artinianity, finite generation and dimension
  bounds for completed duals, top nonvanishing, and the top-dual associated
  primes are proved over noetherian local rings. The support criteria after
  formula (22) and the Ext support-codimension bound are also formalized.
- **V.3.2:** For closed supports and arbitrary morphisms of ringed spaces,
  the module-valued spectral sequence has genuine pages and differentials,
  module-linear E₂ and source-cohomology abutment comparisons, and a finite
  convergence filtration. Coefficient maps preserve these comparisons and
  the filtration; changes of resolution are coherent. Flatness is not
  assumed. Closed supports are the scope of the source lemma.
- **V.3.3–V.3.4:** The representing-module associated-prime criterion accepts
  actual irreducible component families. Every component of a closed subset
  with affine complement has codimension at most one, measured with the
  structure-stalk dimensions.
- **V.3.5–V.3.6:** Finite length is equivalent to shifted punctured
  local-cohomology vanishing, and finite length through a threshold is
  equivalent to the punctured depth bound, over quotients of regular local
  rings. Quotient transport, localization of Ext, regularity of prime
  localizations, and the dimension formula are proved.

### Declaration index

| Source | Formalization |
| --- | --- |
| V.1, literal Hom-complex signs | `sourceHomδ_v`, `sourceHomδ_comp`, `sourceHomComplexIso`, `sourceHomSign_smul_comp`: the original displayed differential is square-zero; actual Leibniz, cocycle/coboundary and homotopy formulas are proved. The explicit chain isomorphism multiplies degree `n` by `(-1)^(n(n+1)/2)`, with composition correction `(-1)^(ij)` |
| V.1.3, actual double-resolution comparison | `homComplexPrecomp_quasiIso`, `sourceInjectiveHomAugmentation_f`, `sourceInjectiveHomologyExtAddEquiv`: precomposition preserves cohomology into K-injective targets; the sign-normalized augmentation from the actual source Hom complex of two specified injective resolutions is a quasi-isomorphism, and its actual homology map computes Ext |
| V.1, original cohomology composition | `homClassComp_mk`, `homClassComp_assoc`, `homologyComp`: original graded composition gives a biadditive cohomology pairing with its actual representative formula and associativity, not just a separately transported operation |
| V.1, original source quotient and pairing | `sourceHomLeftHomologyData`, `sourceHomologyComp_mk`, `sourceHomologyAddEquiv_comp`: the source's actual kernel and quotient use unscaled cocycles and classes; their original composition acquires exactly `(-1)^(ij)` under the explicit normalization |
| V.1, Hom-complex/Yoneda product comparison | `injectiveHomologyExtAddEquiv_comp`, `sourceInjectiveHomologyExtAddEquiv_comp`: the previously specified double-resolution Ext equivalences carry the actual standard product to Yoneda composition and the literal source product to the precisely signed Yoneda composition; the proof retains the original augmentations |
| V.1, pairing naturality in all variables | `homologyComp_naturality_first`, `homologyComp_naturality_middle`, `homologyComp_naturality_last`, and their `sourceHomologyComp` counterparts: both homology products commute with the original chain maps in every integer degree |
| V.1, actual connecting cocycle | `connectingConeCocycle_postcomp`, `homCocycle_connecting_eq_derived`, `sourceHomCocycle_connecting_eq_derived`: original lift-and-differentiate is the derived connecting morphism through an actual mapping-cone cocycle; the literal source convention has its precise target-degree sign |
| V.1, projective-resolution Ext boundary | `projectiveExtCocycle_comp_extClass`, `projectiveExtMk_comp_extClass`, `exists_projectiveExtBoundaryFormula`: Yoneda composition with the actual extension class equals `(-1)^(n+1)` times the unchanged unsigned lift-and-differentiate representative; actual lifts and factorizations exist for every Ext class, and the original boundary is proved to be a cocycle |
| V.1, original coefficient boundaries in all degrees | `moduleCohomologyMk_δ`, `moduleExtLinearEquivAbelianExt_isoExt_inv_mk`, `moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ`: original module-cohomology representatives map to their unchanged `extMk` classes, including degree zero through the existing Ext-to-Hom isomorphism; the actual Yoneda coefficient boundary is `(-1)^(n+1)` times the independently constructed Hom boundary |
| V.1, original local-cohomology boundary comparison | `extColimitYonedaBoundary_eq_signed_extColimitδ`, `localCohomologyYonedaBoundary_eq_signed_localCohomologyδ`: the same signed equality holds for the existing maps on the unchanged Ext diagrams, filtered colimits, and ideal-power local-cohomology objects in every degree |
| V.1, actual contravariant Hom exactness and naturality | `homComplexContravariantSequence_shortExact`, `sourceHomContravariantSequence_shortExact`, `homComplexContravariant_exact₁`–`exact₃`, `sourceHomContravariant_exact₁`–`exact₃`, `sourceHomContravariantδ_naturality`: the original reversed Hom sequences into any degreewise-injective complex give natural long exact sequences in every integer degree, for both differentials |
| V.1, actual contravariant derived-boundary comparison | `homComplexContravariantδ_mk`, `homComplexContravariantδ_compare`, `sourceHomContravariantδ_compare`: original lift-and-differentiate representatives identify the actual boundary with precomposition by the original derived connecting arrow into a degreewise-injective K-injective target; the standard convention contributes exactly `(-1)^(n+1)`, and the literal source differential has no extra sign under its fixed unscaled, precomposition-natural quotient equivalence |
| V.1, actual pairing and boundaries | `extPairing_sequence_connecting`, `moduleExtPairing_naturality_middle`: actual derived Yoneda composition agrees with both original Ext connecting maps; canonical transport to original module-valued Ext is natural in all three variables |
| V.1, covariant Hom exactness and naturality | `homComplexCovariantSequence_shortExact`, `sourceHomCovariantSequence_shortExact`, `homComplexCovariant_exact₁`–`exact₃`, `sourceHomCovariantδ_naturality`: for arbitrary source complex, a coefficient short exact sequence with degreewise-injective first term induces actual natural long exact Hom sequences, for both differentials and all integer degrees; injectivity supplies the degreewise splittings |
| V.1, actual covariant derived-boundary comparison | `homComplexCovariantδ_compare`, `sourceHomCovariantδ_compare`: with K-injective endpoint coefficients, the original standard boundary is postcomposition with the original derived connecting arrow; the literal-source boundary contributes exactly `(-1)^(n+1)` under the fixed unscaled quotient equivalence, also natural for original coefficient maps |
| V.1, original Hom pairing and both connecting maps | `homologyComp_connecting`, `sourceHomologyComp_connecting`, `sourceHomologyComp_naturality_middle`: the actual Hom pairing is natural in the middle complex and intertwines the two original Hom boundaries with factors `(-1)^(j+1)` (standard) and `(-1)^(i+1)` (displayed source); the original composite of lifts is an explicit coboundary, with no boundedness or K-injectivity requirement |
| V.1, augmented chosen-resolution boundary comparison | `InjectiveResolutionSequence.extClass_augmentation`, `injectiveHomologyExtAddEquiv_contravariantδ`, `injectiveHomologyExtAddEquiv_covariantδ`: for a supplied augmented short exact sequence of chosen injective resolutions, the original augmentation squares identify its connecting arrow with the original extension class; the existing standard and normalized-source Ext equivalences respect the actual Hom boundaries with factor `(-1)^(n+1)` contravariantly and no factor covariantly, including degree zero |
| V.1, injective horseshoe existence | `InjectiveResolutionSequence.ofShortExact`, `nonempty_injectiveResolutionSequence`: enough injectives suffices to construct an actual augmented short exact sequence of injective resolutions; the snake lemma proves the successive categorical cokernel rows short exact, the projected augmentations are quasi-isomorphisms, and the original horizontal maps form a degreewise split integer-indexed sequence |
| V.1, simultaneous horseshoe comparison | `injective_splitRow`, `InjectiveHorseshoe.rowResolution`, `compareHomotopy`, `sequenceCompare_augmentation`: the unchanged horseshoe is an injective resolution of the whole short complex; simultaneous lifts and homotopies preserve the horizontal arrows, and the actual integer-indexed comparison strictly preserves all original augmentations |
| V.1, coherent row-resolution functor | `InjectiveHorseshoe.homotopyFunctor`, `homotopyFunctor_map_eq`, `InjectiveRowResolution.change_trans`, `change_naturality`: identity, composition, and independence of simultaneous lifts hold in the homotopy category; changes between arbitrary injective resolutions of the whole row satisfy naturality and the cocycle law |
| V.1, constructed-map Hom boundary naturality | `InjectiveHorseshoe.covariantδ_compare_naturality`, `contravariantδ_compare_naturality` and their literal-source counterparts: both original boundaries commute with the actual constructed augmented sequence maps in all integer degrees, without assuming a compatible resolution map |
| V.1, arbitrary supplied resolution models | `injectiveResolutionNatHom`, `InjectiveResolutionSequence.rowResolution`: full faithfulness recovers the actual original nonnegative maps with their augmentation squares; short exactness is retained and the transposed supplied sequence is an injective resolution of the entire short complex |
| V.1, arbitrary-model coherent maps | `InjectiveResolutionSequence.compare`, `compare_augmentation`, `rowCompareHomotopy`, `change_trans`, `change_naturality`: arbitrary supplied resolution models admit actual augmented sequence comparisons, simultaneous coherent homotopies, and natural model-change isomorphisms satisfying the cocycle law |
| V.1, fixed Hom/Ext model independence | `injectiveHomologyExtAddEquiv_precomp`, `injectiveHomologyExtAddEquiv_postcomp` and their normalized-source variants: the unchanged double-resolution equivalences respect the actual maps in both variables; model change over identities preserves the fixed Ext value, also under the original module-valued equivalences |
| V.1, arbitrary-model boundary naturality | `InjectiveResolutionSequence.covariantδ_compare_naturality`, `contravariantδ_compare_naturality` and their literal-source counterparts: both original Hom boundaries commute with the actual arbitrary-model comparison maps in every integer degree |
| V.1, original module-valued boundary specialization | `injectiveHomologyModuleExtAddEquiv_contravariantδ`, `sourceInjectiveHomologyModuleExtAddEquiv_covariantδ` and their opposite-convention counterparts: the unchanged canonical linear Ext comparison gives additive-group identifications carrying the actual Hom boundaries to the previously defined module-valued Yoneda boundaries with the same signs; uses an augmented exact resolution sequence, constructed by the horseshoe theorem |
| V.2, canonical natural map | `localDualityNatTrans`, `localDualityMap_stage`: original quotient-Ext stages define the actual natural map into `Hom_R(Ext^j(M,P), H^n_J(P))` for `i+j=n`, over any commutative ring |
| V.2, regular-local inputs | `regularLocal_localCohomology_isZero_of_gt`, `regularLocal_localCohomology_ring_isZero_of_ne`, `regularLocal_topLocalCohomology_not_isZero`: actual local cohomology vanishes above the dimension for any module; ring coefficients are concentrated and nonzero in that dimension |
| V.2, identity and rank-one normalization | `localDualityMap_identity_evaluation`, `localDualityMap_ring_top_isIso`: evaluation at the original identity Ext class retracts the canonical top-degree map with equal coefficients; for the rank-one ring module the canonical map is an isomorphism over every commutative ring |
| V.2.1, top degree for every finite module | `regularLocal_localDualityMap_top_isIso`, `regularLocal_localDualityTopNatIso`: the original canonical map is a natural isomorphism in the actual Krull dimension over a regular local ring; proved by additivity, actual finite free covers and their noetherian kernels, and right exactness of both unchanged functors |
| V.2.1, all complementary degrees | `regularLocal_localDualityMap_isIso`, `regularLocal_localDualityNatIso`: the unchanged canonical map is a natural isomorphism for every finite module and every `i+j=n`; descending induction uses exact transported Yoneda sequences on the original Ext/local-cohomology objects, their proved stagewise pairing compatibility, and actual finite-free vanishing. Above-dimension local-cohomology vanishing is already proved |
| V.3, formula (22), original dual comparison | `regularLocal_localCohomologyDualCompletionIso`, `regularLocal_localCohomologyDualCompletionIso_transpose`: over any regular local base, actual dual local cohomology is completed complementary Ext, with canonical transpose equal to the original completion map under this comparison |
| V.3, formula (22), complete regular base | `regularLocal_localDualityTransposeMap_isIso`, `regularLocal_localCohomologyDualIsoExt`, `regularLocal_localDualityTransposeNatIso`: the original transpose is invertible, naturally on finite modules, identifying the actual dual with original complementary Ext |
| V.3, regular-local finiteness | `regularLocal_localCohomology_isArtinian`, `regularLocal_localCohomology_socle_finite`, `regularLocal_localCohomology_annihilator_isFiniteLength`: all actual local-cohomology values of finite modules are Artinian with finite socle and finite-length power annihilators, even over a noncomplete regular base |
| V.3.1(ii), regular-base finite generation | `regularLocal_localCohomology_dual_completeProperty_of_dualizing`, `regularLocal_completedLocalCohomologyDual_finite_of_dualizing`: for every supported dualizing coefficient, actual duals satisfy the original complete-category conditions; their original completions are finite over the actual completed ring without completeness of the regular base; generalized to arbitrary noetherian local bases below |
| V.3.1(i), actual module parameters | `exists_localParameters`, `exists_localParameters_modulo`, `exists_moduleParameters`: converse Krull height produces genuine dimension-length parameters over every noetherian local ring; lifting parameters of the actual annihilator quotient gives a list of length equal to the module's support dimension |
| V.3.1(i), original transition calculation | `koszulTransition_comp_eq_zero_of_annihilating_prefix`, `stableKoszulCohomology_isZero_of_annihilating_prefix`: for annihilator generators followed by `d` parameters, the unchanged consecutive-power Hom--Koszul transition is zero in every degree above `d`, so its original cohomology colimit vanishes |
| V.3.1(i), sharp upper vanishing | `localRing_localCohomology_isZero_of_gt_moduleDim`: over every noetherian local base, original algebraic local cohomology of a finite module vanishes above its actual support dimension; the proof uses actual annihilator parameters, zero transitions, and original radical/Koszul comparisons, with no regularity or completeness hypotheses |
| General local-ring upper vanishing | `localRing_localCohomology_isZero_of_gt`: original local cohomology vanishes above the ring dimension for arbitrary coefficient modules over every noetherian local ring, using actual parameters and radical invariance |
| Actual residue Ext through injective envelopes | `FiniteResidueExt.injectiveEnvelope`, `FiniteResidueExt.cokernel_injectiveEnvelope`: finite original residue Ext is preserved through actual constructed injective envelopes and their categorical cokernels, using the unchanged degree-zero socle and genuine coefficient exact sequence |
| General-local Artinianity | `FiniteResidueExt.localCohomology_isArtinian`, `localRing_localCohomology_isArtinian`: all original local-cohomology values of modules with finite residue Ext are Artinian over every noetherian local ring, in particular for all finite modules; dimension shifting uses actual envelopes and original coefficient sequences |
| V.3.1(ii), general-local finite generation | `localRing_completedLocalCohomologyDual_finite`, `localRing_localCohomology_dual_finite`: for any actual supported dualizing coefficient, the completed original Hom dual is finite over the actual completed ring, and the original dual is finite over a complete base; no regularity or Cohen presentation is assumed |
| Original torsion quotient and scalar maps | `powerTorsion_quotient_eq_bot`, `exists_regular_on_powerTorsion_quotient`, `localCohomology_powerTorsion_mkQ_isIso`: the actual finite torsion quotient admits a regular element and its original projection preserves positive local cohomology; `localCohomology_linear` identifies original coefficient scalar maps with scalar maps on local cohomology |
| V.3.1(ii), general-local dimension bound | `localRing_completedLocalCohomologyDual_supportDim_le`: the original completed Hom dual in degree `i` has actual support dimension at most `i` over the completed ring, without completeness or regularity of the base; `completeLocal_localCohomology_dual_supportDim_le` gives the bound on the original dual over a complete base. The genuine dual regular-element sequence and original completion maps give induction on degree, without Cohen reduction |
| V.3.1(iii), complete-base top-dual dimension and nonvanishing | `completeLocal_topLocalCohomology_dual_supportDim_eq`, `completeLocal_topLocalCohomology_nontrivial`: over every complete noetherian local ring, the original top dual has exactly the finite coefficient module's support dimension, and original top local cohomology is nonzero. Simultaneous regular elements, actual support control modulo the closed point, and the genuine dual regular-element sequence give induction without regularity of the ring. The zero-dimensional base holds without completeness |
| V.3.1(iii), general-local top nonvanishing | `localRing_topLocalCohomology_nontrivial`, `localRing_completedTopLocalCohomologyDual_supportDim_eq`: original top local cohomology is nonzero over every noetherian local ring, and its original completed Hom dual has exactly the original coefficient support dimension over the actual completed ring. Original-ring parameters avoid contracted associated primes of the preceding completed dual, and the genuine completed scalar sequences give induction without a Cohen presentation or an assumed base-change comparison |
| V.3.2, module-valued ringed-space foundations | `moduleGammaZSectionsFunctor`, `moduleGammaZSectionsForgetIso`, `moduleToSheaf_map_shortExact`: supported sections are actual modules over the structure ring on each open; their additive groups recover Exposé I's section functor, and forgetting the sheaf's module structure is exact |
| V.3.2, general acyclicity input | `moduleIsFlasque_of_injective`, `derivedModuleGammaZSections_isZero_of_isFlasque`, `derivedModuleGammaZSections_isZero_pushforward_injective`: injective module sheaves are flasque, and the actual higher module-valued supported cohomology vanishes on flasque sheaves and on direct images of injectives under arbitrary ringed-space morphisms, without flatness |
| V.3.2, scalar-compatible composite comparison | `ringedModulePushforwardSupportedGlobalIso`, `ringedModuleSupportedGlobalRightDerivedIso`: actual supported sections and the right-derived direct-image/section composite agree naturally with source supported cohomology restricted along the actual map on global structure rings |
| V.3.2, original additive cohomology, naturally | `gammaZSections_quasiIso_of_boundedBelow_flasque`, `derivedModuleGammaZSectionsForgetIso`, `derivedModuleGammaZSectionsIsoH_Z`: mapping cones compare the actual module and additive resolutions in all degrees; augmentation-compatible chain homotopies prove that the unchanged objectwise comparisons commute with the original coefficient maps, without preservation of injectivity by forgetting scalars |
| V.3.2, retained scalar action | `moduleUnderlyingComplexGlobalScalarRingHom`, `moduleUnderlyingDerivedGlobalScalarRingHom`: actual global structure-ring actions on underlying additive complexes and derived objects satisfy all ring laws and commute with coefficient cochain maps |
| V.3.2, additive spectral sequence and E₂ | `ringedModulePushforwardAdditiveSpectralSequence`, `ringedModulePushforwardAdditiveSpectralSequenceE2Equiv`, `ringedModulePushforwardE2ModuleAddEquiv`: actual truncations of the original module direct-image resolution give genuine pages and differentials with E₂ the original supported cohomology of original higher module direct images |
| V.3.2, genuine module-valued spectral sequence | `spectralObjectModuleLift`, `ringedModulePushforwardModuleSpectralSequence`, `ringedModulePushforwardModuleSpectralSequenceForgetIso`: the original scalar action lifts the actual spectral object and its exactness to modules; canonical forgetful comparisons preserve all differentials and the original next-page homology isomorphisms |
| V.3.2, original module-linear E₂ identification | `ringedModulePushforwardModuleE2LinearEquiv`, `ringedModulePushforwardModuleE2LinearEquiv_toAddEquiv`: the actual E₂ page identifies module-linearly with original module-supported cohomology of the original higher module direct image; every original comparison factor intertwines the retained scalar endomorphisms, and the underlying additive equivalence is exactly the preexisting one, without commutativity or flatness assumptions |
| V.3.2, first quadrant and canonical finite module filtration | `ringedModulePushforwardModuleSpectralObject_isFirstQuadrant`, `ringedModulePushforwardSpectralFiniteFiltration`, `ringedModulePushforwardModuleStablePageIsoGraded`: the actual module pages vanish outside the first quadrant and, for `r ≥ n + 2`, are the associated graded of the canonical total object's finite exhaustive submodule filtration |
| V.3.2, actual module-linear abutment | `flasqueGammaComplexDerivedHomEquiv`, `ringedModulePushforwardSpectralAbutmentLinearEquiv`, `ringedModulePushforwardSourceFiniteFiltration`: the unchanged localization map computes supported derived Hom on bounded-below flasque complexes and respects all additive cochain maps; the actual filtered total module is original source supported cohomology with the prescribed scalar restriction, and the finite exhaustive filtration is transported to that source module |
| V.3.2, coefficient functoriality and original comparisons | `ringedModulePushforwardModuleSpectralSequenceFunctor`, `ringedModulePushforwardModuleSpectralSequenceCoefficientMap_E2`, `ringedModulePushforwardSpectralTotalCoefficientMap_abutment`: actual resolution maps induce module-linear maps of the entire spectral sequence; resolution homotopies prove lift-independence and the functor laws; the unchanged E₂ and abutment identifications retain the original higher-direct-image and source supported-cohomology coefficient maps |
| V.3.2, coefficient additivity | `ringedModulePushforwardModuleSpectralSequenceCoefficientMap_add`, `ringedModulePushforwardModuleSpectralSequencePageFunctor_additive`: every page complex is additive in the coefficient module sheaf, independently of the chosen resolution lift |
| V.3.2, natural and resolution-independent filtration | `ringedModulePushforwardModuleSpectralSequenceResolutionIso_naturality`, `ringedModulePushforwardModuleStablePageIsoGraded_naturality`, `ringedModulePushforwardSourceFiniteFiltration_map_le`, `ringedModulePushforwardSourceFiniteFiltration_eq`: canonical resolution changes are natural and satisfy the cocycle law; stable-page comparisons retain the genuine associated-graded maps; original source coefficient maps preserve the actual finite filtration, which is independent of resolution |
| V.3.3, component-generic-point criterion | `supportedFunctorColimit_associatedPrimeSpectrum_eq`, `supportedFunctorColimit_associatedPrimeSpectrum_eq_of_components`: IV's actual representing colimit has exactly the selected component generic points as associated primes when the original left-exact functor vanishes precisely on modules containing none of those components; original `R/p` tests prove the criterion, with components indexed by minimal primes of the support ideal |
| V.3.3, actual topological components | `supportedFunctorColimit_associatedPrimes_of_irreducibleComponents`: the original irreducible components of `V(J)` are accepted directly; their genuine generic points are constructed and the actual representing colimit has exactly their range as associated primes. No list of minimal primes or generic points is supplied as an assumption |
| V.3.1(iii), supported top-dual functor | `supportedLocalCohomologyFunctor_preservesFiniteColimits`, `supportedTopLocalCohomologyDual_isZero_iff`: original top local cohomology is right exact on the actual bounded supported category, and its actual Hom dual vanishes exactly when the coefficient support misses the top component generic points; actual chains of primes supply the dimension criterion |
| V.3.1(iii), associated-prime formula | `localRing_topLocalCohomologyDual_associatedPrimeSpectrum`: the original top Hom dual has precisely the dimension-`n` associated primes of the original finite coefficient module. V.3.3 and III.1.3 apply to the genuine supported representation; `additiveFunctorModuleLiftIsoOfLinear` retains the original scalar action. The formula holds even without completeness; finiteness over the original ring still uses completeness |
| Actual affine-open vanishing | `homeomorphismCohomologyFunctorIso`, `affineChartCohomologyEquiv`, `affineOpen_H_pos_subsingleton`: genuine direct image under homeomorphisms and canonical affine charts transport original ordinary cohomology; every actual quasi-coherent module is acyclic in positive degrees on an affine open of a locally noetherian scheme |
| V.3.4, local argument | `localCohomology_isZero_of_affineComplement`, `localRing_ringKrullDim_le_one_of_affinePuncturedSpectrum`: actual affine-complement vanishing and the original relative sequence give local-cohomology vanishing above one; original top nonvanishing then bounds the dimension of a noetherian local ring with affine punctured spectrum by one |
| V.3.4, component codimension | `irreducibleComponent_codimension_le_one_of_affineComplement`: every actual irreducible component of an arbitrary closed subset with affine complement in a noetherian affine spectrum has codimension at most one. Localization identifies the actual complement with the punctured local spectrum; codimension is the literal infimum of original structure-stalk dimensions. There is no principal-support hypothesis |
| V.3.5, finite-length duality | `SupportedDualizingModule.moduleHomDual_finiteLength_iff`, `.moduleHomDual_length`: actual Hom duality detects finite length and preserves extended length on arbitrary modules over a noetherian local ring, without completeness; the original bidual evaluation is invertible when the dual has finite length |
| Actual Ext localization | `finiteProjectiveResolution`, `localizedLinearYonedaObjIso`, `moduleExtLocalizationIso`, `moduleExtLocalizationRingIso`: degreewise finite genuine projective resolutions and termwise Hom localization give localized-ring-linear comparisons for original Ext, with finite first argument and arbitrary second argument, including actual ring coefficients |
| V.3.5, through localized Ext | `regularLocal_localCohomology_length_eq_ext`, `regularLocal_localCohomology_finiteLength_iff_ext_atPrime`: over a regular local ring, original local cohomology has the same extended length as complementary Ext; finite length is equivalent to vanishing of actual complementary Ext over every nonclosed prime localization |
| Koszul systems under arbitrary ring maps | `koszulSystemBaseChangeIso`, `koszulHomComplexSystemScalarChangeIso`: actual tensor extension identifies the original inverse Koszul systems, including every power transition; the source-ring-linear Hom adjunction identifies their actual Hom cochain systems, without flatness |
| Original local-cohomology scalar change | `localCohomologyScalarChangeIso`: for any map of noetherian commutative rings, scalar restriction of local cohomology at the image ideal is source-ring local cohomology of the restricted coefficient, for all ideals, degrees, and arbitrary coefficients |
| V, formula (19) and finite length | `localRing_localCohomologyScalarChangeIso`, `localRing_localCohomology_length_eq_of_surjective`, `localRing_localCohomology_finiteLength_iff_of_surjective`: surjective local-ring change preserves actual maximal-ideal local cohomology, extended length, and finite length; no flatness is assumed |
| V, formula (20), actual Hom duals | `surjectiveHomDualScalarChangeIso`, `surjectiveLocalCohomologyDualIso`: actual coinduction is dualizing over the target; one choice of coefficient isomorphism gives a natural source-ring-linear comparison of the specified Hom duals on all modules, and a comparison of duals of actual local cohomology |
| V, formula (21) and module dimension | `restrictScalarsAnnihilatorQuotientEquiv`, `restrictScalars_finite_iff_of_surjective`, `restrictScalars_supportDim_of_surjective`: the induced map identifies the original annihilator quotients; finite generation and actual finite-module support dimension are unchanged |
| V.3.5, original prime-localization transport | `localRingHom_surjective`, `localizedRestrictScalarsIso`, `localizedRestrictScalarsIso_hom_mk`, `ringKrullDim_quotient_comap_of_surjective`: the actual local ring map is surjective, the original localized coefficients agree with their original element maps, and the dimensions of corresponding prime quotients agree |
| V.3.5, quotient reduction of both conditions | `localCohomologyAtPrimeScalarChangeIso`, `puncturedLocalCohomologyVanishing_iff_of_surjective`, `localCohomologyFiniteLengthCriterion_iff_of_surjective`: actual local cohomology at corresponding points agrees after scalar restriction; both finite length and shifted punctured vanishing are quotient-invariant. Points outside the image vanish and negative degrees impose no condition |
| V.3.6, depth deduction | `puncturedLocalCohomologyVanishing_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_criterion`, `puncturedDepthBound_iff_of_surjective`: shifted vanishing through a threshold is equivalent to the actual localized depth bound, including infinite depth; the deduction from V.3.5 and quotient invariance hold over every noetherian local ring |
| V.3.5, homological prime-localization input | `localizedPrimeQuotientResidueFieldIso`, `localizedPrimeQuotientResidueFieldIso_hom_mk`, `regularLocal_atPrime_moduleGlobalDimension_le`: the original localization of `R/p` is the actual residue field of `R_p`, with the original element map; every prime localization has global dimension bounded by the original regular ring's Krull dimension, without assuming regularity of the localized ring |
| Homological regularity criterion | `isRegularLocalRing_of_residueField_bound`, `isRegularLocalRing_iff_residueField_projectiveDimension_ne_top`: a noetherian local ring is regular exactly when its actual residue field has finite projective dimension. Regular-element reduction preserves bounds over the quotient ring, a cotangent functional gives the actual residue-field retract of `m/xm`, and lifting minimal generators completes induction |
| V.3.5, regularity of prime localizations | `regularLocal_atPrime_isRegularLocalRing`, `regularLocal_isRegularRing`, `regularLocal_atPrime_moduleGlobalDimension_eq_ringKrullDim`: every actual prime localization of a regular local ring is regular, and its global dimension equals its own Krull dimension; no converse criterion or localization-regularity hypothesis is supplied |
| V.3.5, regular-local dimension formula | `regularLocal_top_associated_mem_ext_support`, `regularLocal_atPrime_dimension_add_quotient`: the top-dual associated-prime formula forces complementary Ext to be supported at the original top primes; localization and residue Ext concentration give `dim R_p + dim(R/p) = dim R`, without assuming catenarity |
| V.3.5, full criterion | `regularLocal_localCohomology_finiteLength_iff_punctured`, `localCohomology_finiteLength_iff_punctured_of_surjective`: for finite modules over quotients of regular local rings, original local cohomology has finite length exactly when the original shifted local cohomology vanishes at all nonclosed points. Both localization regularity and the dimension formula are proved; negative shifted degrees and upper vanishing are handled explicitly |
| V.3.6, full criterion | `regularLocal_localCohomology_finiteLength_le_iff_depth`, `localCohomology_finiteLength_le_iff_depth_of_surjective`: finite length through degree `n` is equivalent to the actual punctured depth bound for finite modules over quotients of regular local rings; no additional finite-length criterion is assumed, and zero modules retain infinite depth |
| General-local socle and annihilators | `localRing_localCohomology_socle_finite`, `localRing_localCohomology_annihilator_isFiniteLength`, `localRing_localCohomology_dual_completeProperty`: actual socles are finite, actual power annihilators have finite length, and actual Hom duals satisfy the original complete-category conditions over every noetherian local ring |
| V.3.1, support criteria after (22) | `regularLocal_supportDim_le_iff_localized_vanishing`, `regularLocal_supportDim_le_iff_codimension_ge`: support dimension at most `i`, vanishing at primes of height less than `j`, and support codimension at least `j` are equivalent when `i + j = dim R`, including zero modules |
| V.3.1(ii), Ext support bound | `regularLocal_ext_localized_subsingleton_of_lt`, `regularLocal_ext_supportCodimension_ge`, `regularLocal_ext_supportDim_le`: localized Ext vanishes below its degree in local dimension; hence Ext has the stated codimension and complementary support-dimension bounds, with a finite first argument and arbitrary second argument |

### Sign conventions

The source differential is identified with Mathlib's convention by the
factor `(-1)^(n(n+1)/2)` in degree `n`. Under this normalization, its
cohomology product contributes `(-1)^(ij)`. On the unchanged unsigned
projective representatives, the Yoneda coefficient boundary is
`(-1)^(n+1)` times lift-and-differentiate; this includes degree zero and
passes to the original Ext colimits and local cohomology.

The standard Hom boundary-pairing identity has factor `(-1)^(j+1)`; the
literal source convention has factor `(-1)^(i+1)`. The incompatible unsigned
augmentation and pairing formulas are not asserted. These are explicit
signed comparisons, not missing proofs of the unsigned claims.

### Remaining scope

Cohen's presentation theorem used in the source proof is not formalized.
The general local-ring conclusions of V.3.1 are proved directly, without
that reduction. Algebraic local cohomology is indexed by natural numbers;
the source's negative-degree vanishing is a convention rather than a
separate integer-indexed construction. In V.3.5–V.3.6, negative shifted
degrees impose no condition, and zero modules retain infinite depth.

## SGA 2, Exposé VI — Ext with support

Entry point: `lean/SGA/SGA2/ExposeVI.lean`.

The affine degree-zero algebra in the proof of VI.2.3 is now formalized in
`ExposeVI/AffineHomColimit.lean`.
`adicQuotientHomTorsionIsColimit` and
`adicQuotientHomColimitIsoPowerTorsion` identify the actual categorical colimit
of `Hom_R(M/IⁿM,N)` with the ideal-power torsion submodule of the original
`Hom_R(M,N)`. The comparison is the original quotient-precomposition map at
every stage, as proved by `adicQuotientHomColimitIsoPowerTorsion_ι` and
`adicQuotientHomTorsionCocone_apply`. It holds for arbitrary modules over any
commutative ring, and reuses the previously proved quotient-annihilator
identifications and actual annihilator colimits from Exposé IV.

`ModuleInternalHom.lean` constructs the actual sheaf of local module-linear
maps on arbitrary ringed spaces. It is the local-linear subpresheaf of the
additive internal Hom; its sheaf condition is proved by checking scalar
linearity on a covering sieve. `moduleLocalHomOverEquiv` identifies sections
with actual module-presheaf morphisms on the slice category. This proves left
exactness of `moduleSheafHomAbFunctor`; its maps are original postcomposition,
and original precomposition is constructed as well. Global sections are
the original module-sheaf Hom through `moduleSheafHomAbGlobalEquiv`.

For closed support, `moduleGammaZSheafFunctor` retains the actual supported
section submodules and is left exact. Its underlying additive sheaf agrees
naturally with the original kernel functor. `moduleSupportedHomFunctorIso`
proves VI.1.4.3 using the actual factorization and inclusion maps, with
contravariant naturality given by `moduleSupportedHomEquiv_precomp`.
`moduleSupportedInternalHomFunctorIso` gives the sheaf version, compatible
with all open restrictions.

`ModuleSupportedExt.lean` right-derives these genuine local-linear Hom functors
in the category of module sheaves. It constructs supported Ext groups and
underlying additive sheaves for closed and arbitrary locally closed support,
with natural degree-zero comparisons and positive-degree vanishing on
injective module sheaves. `moduleSupportedExtViaSupportedSheafIso` derives
the closed supported-Hom identity; it is a comparison of derived composites,
not the spectral sequence of VI.1.6.3.

`ModuleSheafExtLinear.lean` and `ModuleLocallyClosedSheafExtLinear.lean`
construct genuine scalar-valued sheaf Ext for ordinary and arbitrary locally
closed support, and global supported Ext modules over the global structure
ring. Their natural exact-forgetting isomorphisms recover the unchanged
additive derived functors.

VI.1.5's flasqueness and acyclicity inputs are proved in
`ModuleOpenSubpresheaf.lean` and `ModuleHomInjectiveFlasque.lean`.
The source module's open subpresheaf embeds into it, so injectivity extends
every local linear map globally. Applied to the underlying module presheaf
of an injective module sheaf, this proves that the genuine local-linear Hom
sheaf is flasque and has zero positive closed or locally closed supported
cohomology. No injectivity of its underlying additive sheaf is assumed.

VI.1.2's actual local values are `moduleExtPresheafEvalIso` for ordinary Ext
and `moduleLocallySupportedExtPresheafEvalIso` for locally supported Ext.
The latter are derived in the actual category of module sheaves on the open
slice site. `moduleLocallySupportedExtSheafificationIso` identifies their
sheafification with the original ambient supported sheaf Ext. Open and
nested-open module restriction are proved exact and injective-preserving.
`VI_1_3` gives all-degree excision for arbitrary locally closed supports,
natural in coefficients. Explicit compatibility with higher Ext restrictions
between nested opens and with coefficient connecting maps remains open.

`VI_1_4_1` now uses the actual structure-module support object, and `VI_1_4_2`
uses the genuine sheafification of the sectionwise tensor product.
`LocallyClosedTensorSupportHom.lean` extends both representations to arbitrary
locally closed support. `moduleLocallyClosedSupportedExtTensorIso` is the
all-degree original Ext comparison; its source naturality is
`moduleLocallyClosedSupportedExtTensorIso_precomp`. The actual closed supported
module-sheaf functor preserves injectives by a proved mono-preserving quotient
left adjoint (`ModuleSupportedSheafInjective.lean`). The original locally
closed module-support functor is also proved to preserve injectives by its
closed-support, open-restriction and direct-image decomposition.
`moduleLocallyClosedSupportedHomFunctorIso` proves its actual VI.1.4.3
factorization, and that factorization is derived in every degree.

VI.1.6.1, VI.1.6.2, and VI.1.6.3 have genuine coefficient spectral functors
for arbitrary locally closed supports. Each construction has actual pages and
differentials, an explicit original E₂ identification, an original supported
Ext abutment, and a finite filtration with stable pages identified with
successive quotients. VI.1.6.3's locally closed E₂ and abutment comparisons
are natural in coefficients
(`ModuleLocallyClosedSupportSpectralNaturality.lean`).

VI.1.8 is the actual module-derived Ext long exact sequence, for any locally
closed support and a closed subset of its literal support space. Both the
group-valued and sheaf-valued versions have the original inclusion and
restriction in degree zero, and all arrows and genuine boundaries are natural
in both module arguments (`LocallyClosedExtSequences.lean`,
`LocallyClosedSheafExtSequences.lean`, `ExtSequenceFirstVariable.lean`).
`ModuleRelativeExtSequence.lean` gives VI.1.9's actual exact sequence with
ordinary Ext endpoints on the ambient space and open complement.
`moduleRelativeExtRestriction_zero_standard` identifies its degree-zero map
with literal Hom restriction under the standard Ext₀ = Hom isomorphisms.
`moduleRelativeExtRestriction_eq_functor` identifies the restriction arrow
in every degree with the standard Ext map of the exact open-restriction
functor (`ExtRightDerivedMap.lean`).
VI.1.7's module support-object sequence and its tensor version are
`moduleNestedSupportObjectSequence_shortExact` and
`moduleNestedTensorSupportSequence_shortExact`.

VI.2.3's affine degree-zero and structure-sheaf comparisons are `VI_2_3_zero`
and `VI_2_3_structure`. Degree-zero supported Hom and sheaf Ext⁰ are
quasi-coherent for coherent source and quasi-coherent coefficients on
locally noetherian schemes (`schemeModuleGammaZ_isQuasicoherent`). Higher
supported sheaf Ext quasi-coherence and the general comparison
`colim Ext(M/IⁿM, N) → Ext_Y(X;F,G)` remain open.
The actual ordinary internal Hom is now canonically the associated sheaf
of module Hom on affines for finitely presented sources over arbitrary rings,
with both source and coefficient naturality. It commutes with actual open
restriction and is quasi-coherent for coherent source and quasi-coherent
target on locally noetherian schemes (`CoherentInternalHom.lean`).

## SGA 2, Exposé VII — Vanishing and coherence

Entry point: `lean/SGA/SGA2/ExposeVII.lean`.
`VII_1_3_locallyNoetherian` proves actual internal-Hom zero detection from
literal stalk-support containment, with a coherent source and an arbitrary
quasi-coherent target. The proof obtains finite affine coefficient charts
from the source's actual local presentations and uses genuine module
restriction and affine Hom comparisons. VII.1.3 without local noetherianity
and the remaining vanishing and coherence statements are open.

Exposés VIII–XIV still have no Lean formalization.

## Axiom verification

For SGA 1 and the foundations, run `lake env lean CheckSGA1Axioms.lean` from `lean/`: it checks
every declaration defined in an `SGA.SGA1.*` or `SGA.Foundations.*` module (selected by module,
since the foundations use mathlib namespaces) and permits only `propext`, `Classical.choice`
and `Quot.sound`.

For SGA 2, run `lake env lean CheckSGA2Axioms.lean` from `lean/`. The check traverses
every imported declaration in `SGA.SGA2` and its transitive axiom
dependencies. It permits only `propext`, `Classical.choice`, and `Quot.sound`;
additional mathematical axioms, `sorryAx`, and native evaluation axioms
cause failure. This verifies the axiom requirement for the imported library,
not completeness of the source coverage.

## Next geometric dependencies (SGA 2)

`InjectiveFlasque.lean` proves that injective abelian sheaves are flasque
using sheafification, free abelian groups, and Yoneda. `FlasqueCohomology.lean`
combines this with mathlib's section-exactness and quotient-flasqueness
theorems to prove ordinary flasque acyclicity for actual Ext-defined
cohomology. `ClosedSupportHom.lean` and `SupportedCohomologyComparison.lean`
now prove the genuine closed-support Hom representation, the natural
comparison of derived supported sections with Ext, and supported flasque acyclicity.
`AffineCohomologyVanishing.lean` now proves ordinary affine vanishing over
noetherian rings, using exactness of the actual associated-sheaf functor.
`AffineCohomologyComparison.lean` proves the higher supported affine comparison,
using exactness of the associated-sheaf functor and supported acyclicity of
associated sheaves of injective modules. Affine/local-stalk compatibility is
now proved, as are the full coherent-module Hartogs equivalence and the actual
connected-components bijection on general locally noetherian schemes.
The all-degree coherent-module depth criterion for original supported-sheaf
vanishing and actual higher ordinary restriction is now proved. The remaining
module-valued internal sheaf Ext criteria need further comparisons. Closed and locally closed supported sheaves have natural
sheafification and flasque acyclicity, and the closed-support model comparison
is proved, alongside the actual closed-support sheaf Ext and open higher-direct-image
comparisons. The canonical closed-support spectral sequence, E₂ identification,
and finite convergence filtration are constructed. Its spectral-object maps,
total and E₂ comparisons, and all-page/next-page coefficient compatibility are
proved. The actual coefficient functor is independent of resolution lifts,
with coherent natural resolution-change isomorphisms. The original convergence
filtration and stable-page/graded-piece comparison are natural, and the
transported filtration on `H_Z` is resolution-independent. The general locally
closed spectral sequence now has the same ambient construction and natural
convergence on original support Ext. The remaining general-scheme criteria and
later exposés are incomplete. Exposé IV now includes the actual supported colimit
representation and categorical equivalence, the full bounded-below delta-functor
vanishing theorem, the original functor's exactness/injectivity criterion,
IV.3.1's full four-condition equivalence and IV.3.2 under its standing hypothesis.
