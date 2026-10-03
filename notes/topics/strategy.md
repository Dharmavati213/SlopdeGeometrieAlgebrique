---
updated: 2026-10-03
---

# Strategy

Lessons on how to work in this repo: running many agents at once, Lean and mathlib technique,
claims that turned out false, and what was cheaper or dearer than expected. Edit the relevant
section in place and keep entries short. Put the date and your handle on new items, e.g.
`(2026-10-05, codex-1005)`. Delete items or mark them resolved once they stop being true.

Seeded 2026-10-03 (handle `claude-1003`) from the SGA 1 Lean campaign (2026-09-24 to 2026-09-27).
Sources: the campaign's 119 agent reports (named in parentheses), the coordinator's log (deps.md)
and its brief (common.md). Those files lived in a gitignored job directory that may be gone.
Hygiene items marked "still present" were checked against the code on 2026-10-03. For what is
hard mathematically, see [`hard-parts.md`](hard-parts.md).

## Before you start

- **Check the code before trusting a brief, a report or a note.** F-Limits was briefed that X.1.7
  was missing, but X.1.7 had already become unconditional (F-Limits). Several docstrings still
  said "statement only" after the proof had landed (F-CohBC, IX-11, F-CommAlg-4).
- **Is a statement still open?** Run
  `grep -rn "Statement" lean/SGA/SGA1 lean/SGA/Foundations --include=*.lean | grep "def "`, then
  search for a theorem whose type is that name. The campaign's regex tracker undercounted proofs:
  it missed `affineLineArtinSchreier`, a theorem that takes an argument, and
  `projectiveSpaceSimplyConnectedStatement`, which is in a namespace (deps.md). Search across
  line breaks, and allow for arguments and namespaces.
- **Several `…Statement` defs are not open items in their own right.** They are proved from other
  statements: `FundamentalGroupComparisonStatement` from Riemann existence, and
  `SpecializationSurjectiveStatement` from IX.1.10. The authoritative open list is the table in
  `docs/formalization.md`.

## Running many agents in parallel

- **Concurrency.** Wave 1 ran 18 work streams in parallel. On 2026-09-25 the user capped the
  campaign at 5 concurrent agents and paused the other 13 (deps.md). Even at 5, the session usage
  limit was hit twice.
- **Resuming.** After the reset, each agent was resumed with its context by messaging the same
  agent id rather than starting a new one: on 2026-09-25 at 12:40 and on 2026-09-27 at 07:30
  (deps.md).
- **Pause protocol.** Ask every running agent to wrap up and write a report with an exact TODO,
  save the reports, then resume in priority order. A paused report with a step-by-step plan, such
  as F-Limits-2's plan for X.1.8 and I.10.8, was finished in the next round (F-Limits-3). Fix
  integration problems such as clashes *before* resuming agents (deps.md, 2026-09-27).
- **File ownership.** Each agent owned explicit files and directories. The rules:
  - never edit `lean/SGA.lean`, `docs/`, or another exposé's files;
  - check that a file name is free before creating it in a shared directory;
  - import only modules that existed when you started, or that you wrote yourself (common.md).

  Ownership changed hands explicitly. For example, `ExposeX/HomotopySequence` and
  `TameSpecialization` passed from IX-11 to XI-12 (deps.md). In this repo, the `Touching:` line
  of `notes/now/<handle>.md` plays that role.
- **Never import a file someone is editing.** IX-a had to drop an Exposé I import because
  `ExposeI/Unramified.lean` did not build at the time.
- **Foundations cannot import SGA 1.** When a Foundations theorem needs an SGA 1 result, take
  that result as a hypothesis and discharge it in the exposé. Examples:
  - I.8.3 is the hypothesis `h83` of `FormalFiniteEtale.isEquivalence_toZero` and of the
    existence files. It is discharged by `finiteEtale_h83` in
    `lean/SGA/SGA1/ExposeIX/EtaleCoveringsClosedFibre.lean` (F-Coh-IX).
  - The converse of SGA 4 IX 2.2 needed descent from Exposé VIII/IX, so it went into
    `lean/SGA/SGA1/ExposeXIII/LocallyConstantSheaves.lean` rather than Foundations (F-Etale-3,
    F-Etale-4).
- **Name clashes: the `LineBundle.tensor` case.** Two agents independently defined
  `AlgebraicGeometry.Scheme.LineBundle.tensor`, the same construction, in
  `Foundations/Projective/Segre.lean` (F-Proj-3) and `Foundations/Etale/Picard.lean` (XI-6). Each
  file built alone, and the clash only showed when both were imported. It kept
  `ExposeXI/AbelianFundamentalGroup` out of its barrel until fixed. The coordinator moved
  `inf_inf_le_left`/`_right`, `tensorG`, `tensorG_cocycle` and `tensor` into
  `lean/SGA/Foundations/Ample.lean` (section `Tensor`), deleted Picard's copy, and patched
  `class_tensor` with `resUnits_resUnits` (deps.md).
  - Lesson: before defining a basic operation on a Foundations type, grep all of `lean/SGA` for
    the name and the concept, and put the construction next to the type's definition.
- **Other clashes**, found by loading every module at once:
  - `Pro.Representable` duplicated mathlib's `isCofiltered_elements` (F-Pro);
  - `DescentDatum.swapAct` was in both IX `QuasiAffineDescent` and `EffectiveGluing` (F-EGA-IX4).
  - Root-level helper names (`presheaf_map_map`, `StandardEtalePair.ext'`, `Subring.eval₂_mem`)
    were flagged as risks (F-Coh-II, F-Hens-3). Put helpers in a namespace or make them `private`.
- **Clash check.** Write one file that imports every built `SGA.SGA1.*` and `SGA.Foundations.*`
  module, followed by `example : True := trivial`, and run `lake env lean` on it. Retry without
  modules whose `.olean` vanished mid-run because another agent was rebuilding. In the campaign it
  found two clashes among 296 modules and one among 554.
- **Barrels.**
  - Agents often left new files out of their barrel:
    - eleven new Exposé V files (V-a-2, V-a-4);
    - `ExposeX/TameInertia`, missing for three rounds (TAME-2 to TAME-4);
    - `ExposeI/GeometricPoints` and `ExposeXI/AbelianFundamentalGroup` (deps.md).
  - `lean/SGA.lean` imported only SGA 1 I, VI and SGA 2 until wrap-up.
  - The coordinator wrote the V (38 modules), VIII (13), IX (21) and XIII (20) barrels and
    regenerated `SGA/Foundations.lean` many times as it grew from 261 to 300 modules.
  - Add a file to its barrel when you create it. The PR check is "every file is imported by its
    barrel".
- **Rebuilds and missing `.olean`s.**
  - The build directory is shared, so another agent's build can rebuild or remove an `.olean` you
    depend on. Reports saw "stale olean for downstream `lake env lean`" (F-Proj-4) and
    "Effectiveness.olean was missing during rebuild" (deps.md). The fix is
    `lake build <that module>`, then retry. Never `lake clean`.
  - Editing a widely imported file triggers rebuilds for everyone. Agents deferred docstring fixes
    for that reason (IX-11), and the docstrings went stale until wrap-up.
- **Build discipline** (common.md).
  - One Lean process per agent, in the foreground; never a bare `lake build` of the whole project.
  - Even so, up to 11 Lean processes ran at once. Free RAM fell to about 2.5 GB with 4 GB of swap
    (memory log, 2026-09-25 07:46).
  - Slow files: the 3500-line `Abhyankar.lean` took 130–140 s and was then split (TAME-6,
    TAME-8). `QuasiCoherent/Descent` took about 70 s (F-QCoh-2). `Sheaf.H'` declarations are
    heavy to build (F-Coh-I).
- **`lake env lean` vs `lake build`.** The lakefile sets `maxSynthPendingDepth = 3` and
  `relaxedAutoImplicit = false`. To make `lake env lean File.lean` agree with `lake build`, pass
  `-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false` (III-4, I-3).
- **Wrap-up checklist**, as used for PR #18:
  1. a full `lake build` (5917 jobs);
  2. grep `lean/SGA/SGA1` and `lean/SGA/Foundations` for `sorry`, `admit`, `native_decide`,
     `implemented_by` and `axiom`;
  3. check that every file is imported by its barrel;
  4. from `lean/`, run `lake env lean CheckSGA1Axioms.lean` (24,789 declarations, only `propext`,
     `Classical.choice`, `Quot.sound`) and `CheckSGA2Axioms.lean`;
  5. update barrel and module docstrings that still say "statement only";
  6. splice the result into `docs/formalization.md`.
- **Review passes pay.**
  - PI1 noticed that `XI.HasFiniteFundamentalGroup` bounded fibre sizes instead of saying "`π₁`
    finite", so it was redefined (XI-3).
  - REVIEW-1, over I–VI, found stale docs, mislabelled special cases and duplicates.
  - The planned REVIEW-2 (VIII, XI, XII) and REVIEW-3 (IX, X, XIII) were never run (deps.md).

## Hygiene debt left by the campaign (still present 2026-10-03)

- **Three `IsCompletelyDecomposed` definitions:** `lean/SGA/SGA1/ExposeV/GaloisCategories.lean`,
  `ExposeIX/ExactSequence.lean`, `ExposeX/GaloisFunctors.lean`.
- **Two `DescentDatum` structures that were never unified:** VIII §7
  (`ExposeVIII/Effectiveness.lean`) and IX's groupoid action
  (`ExposeIX/EtaleEffectiveDescent.lean`). See deps.md and VIII-b.
- **`ExposeV/GaloisEquivalence.lean` overlaps `ExposeV/GaloisCategories.lean`** (V-b1, PI1).
- **Duplicated instances and lemmas:**
  - the global instance `isStableUnderBaseChange_isFinite_inf_etale` is in both
    `Foundations/Formal/EtaleCovering.lean` and `ExposeIX/ConnectedFibres.lean`;
  - `locallyConnectedSpace_of_isLocallyNoetherian` has three copies (X `ConstantFamily`,
    XII `Connected`, SGA 2 III) and `finite_connectedComponents_of_noetherianSpace` two (V
    `MultiGalois`, XII `Connected`);
  - `ringKrullDim_eq_add_of_flat` is in `ExposeI/Permanence.lean` and
    `Foundations/CommAlg/FlatDepth.lean`.
- **Imports from SGA 2:** `ExposeIV/CompletionCriterion.lean` imports
  `SGA.SGA2.ExposeIV.NoetherianCompletion`, though Foundations has `AdicCompletion.isNoetherianRing`
  (F-Formal). deps.md flagged this one for moving.
  `Foundations/CommAlg/{Depth,RegularLocalRing,PurityScheme}.lean` also import SGA 2 III and V;
  nobody flagged those.
- **Convention breaks:**
  - capitalized theorem names `FinitePushforwardStalkStatement`
    (`Foundations/EtaleStalkPushforward.lean`) and `IntegralTorsorLocallyTrivialStatement`
    (`ExposeXIII/CohomologicalProperness.lean`), from F-Hens-4;
  - six snake_case `…_Statement` defs with `…_holds` theorems in Exposé I, and the lowercase def
    `genericPointMapKernelStatement` (REVIEW-1).
- **Already deduplicated:** `ExposeX/Henselian.lean` now aliases Foundations (X-3), and
  Cohomology's `isQuasicoherent_cokernel` is an alias of the QuasiCoherent one (F-QCoh-4).

## Statement conventions in practice

- **Recording an open result.** Keep `def FooStatement : Prop`. When it is proved, add
  `theorem fooStatement : FooStatement` (lowercase) and keep the def. Prove SGA's consequences
  with the statement as a hypothesis, so they become unconditional once it is proved.
- **When the full form is out of reach**, prove it under an extra hypothesis and say so in the
  docstring. IX.6.1 takes a quasi-separated fibre and I.10.11 a locally noetherian base.
- **Out of scope.** If a result needs a theory the project will not build, ask the user. The
  decision lives in `lean/SGA/Foundations/README.md`, not in docs/formalization.md (user's
  instruction, 2026-09-27).

## Lean and mathlib technique

- **Transparency options.** `set_option backward.isDefEq.respectTransparency false in` occurs
  about 560 times in SGA 1 and Foundations, `….types false` 235 times, and
  `backward.defeqAttrib.useBackward true` 24 times.
  - `respectTransparency false` together with `defeqAttrib.useBackward true` makes `simp` work
    across `Over.pullback` objects (F-Coh-IX).
  - `.types false` is needed for `IsZariskiLocalAtTarget` instances (existence resume notes) and
    for `isIso_morphismRestrict_of_bijective` (XI-7).
- **Finite étale coverings are definitionally the same.** `ExposeV.FEt S` is
  `MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ S` by `rfl`, and
  `ExposeV.finiteEtaleHom = @IsFinite ⊓ @Etale` (V-b2, F-Coh-IX). Use this to move between the
  Foundations and Exposé V versions.
- **Kernel and elaboration timeouts, with the fixes that worked:**
  - Unfolding `FEt.fiber` through `MonoidHom.comp` and `MulEquiv` coercions: rewrite explicitly
    with `rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]`, and `subst` inside small generic
    lemmas (XI-6). Work with geometric points rather than elements of `FEt.fiber` (V-b2).
  - Comparing concrete tensor and localization isomorphisms: prove a generic helper lemma
    (`ringEquiv_trans_algEquiv_commutes`) and apply it (TAME-5).
  - `simp` on `AdjoinRoot` tensor `rfl`-lemmas: use `rw` instead (XI).
  - `rw` across `thickeningDiagram.obj` and `thickening` types: prove an abstract lemma
    (`range_appLE_subset_of_eq_comp`) instead. `thickeningDiagram` is an `abbrev` whose
    `obj n` is `thickening f I n` (existence resume notes).
  - `Away.map`/`Proj.map` timeouts: give `sectionRing.instSemiring` priority 10000. `rw`/`set` on
    coercion-headed patterns time out, so use `simp only`, `congrArg` or `.trans`. Pass
    `(A := …)` to `Proj.toSpecBase` (F-Proj-3).
  - Quasi-coherent descent: use typed abbrevs and local instance abbrevs, and avoid letting `simp`
    unfold module maps (F-QCoh-2).
- **Rewriting and elaboration pitfalls:**
  - Proof terms for `c.W ≤ p ⁻¹ᵁ ⊤` must be literally `le_top.trans_eq p.preimage_top.symm`,
    or later `rw`s fail (III-8).
  - Use `erw` or `change` when `Γ(M, U)` and the presheaf object do not match syntactically.
    `open Scheme.Modules` shadows `map_smul`, so write `LinearMap.map_smul` (F-Coh-VIII).
  - Type synonyms such as `Sections` need explicit ascriptions. Avoid `set`, which shadows. When
    `rw` fails on a term ill-typed at an implicit argument, use `calc` or `congrArg` (existence
    resume notes).
  - When an index type is equal only by defeq, state a separate lemma and close with `exact`.
    Don't take `.2.2.2` of an `obtain` on a set-builder membership (F-Proj-4).
  - `let`/`set` on types inside ideals breaks instance search (II-2). `Fiber` is a `def`, so use
    `Fiber.mk` or `erw` (VI-2). Torsor restriction needs repeated `erw [obj_map_map]` (F-Etale-2).
  - Typeclass search did not find `(specFunctor (CommRingCat.of k[X])).IsEquivalence`. Prove an
    instance lemma for all `R` and apply it (XIII-b-2).
- **Universes.**
  - `H¹` and `R¹f_*` of étale sheaves of groups live in `Type (u+1)`, which blocked the `R¹` base
    change map (F-Etale, F-Etale-3).
  - The biproduct lemmas of cohomology need `σ : Type` (universe 0) (F-Coh-VIII).
  - `DecompositionInertiaEtaleStatement` is still stated in `Type`.
- **`maxHeartbeats`.** Use it only with a comment (CONVENTIONS.md). There are 11 overrides now,
  10 of them in `ExposeXIII/Abhyankar*.lean`, all commented. Split a file once it takes minutes
  to compile.
- **Global instances affect everyone downstream.** Grep before adding one. Examples added during
  the campaign:
  - `etale_residueField_tensor` (`ExposeI/StandardEtale.lean`);
  - `IsZariskiLocalAtSource @Etale` (`ExposeV/SchemeGaloisCategory.lean`);
  - two copies of `isStableUnderBaseChange_isFinite_inf_etale`;
  - the priority-10000 `sectionRing.instSemiring`.

## Already in mathlib (don't rebuild)

- **Galois categories.** Most of V.4–V.5: `PreGaloisCategory`, `GaloisCategory`, `FiberFunctor`
  and the equivalence with continuous actions (V-b1).
- **Fibered categories (VI):** `Functor.IsFibered`, `IsCartesian`, `∫ᶜ`, and
  `Pseudofunctor.DescentData`, `IsStack` (docs/formalization.md).
- **Limits of schemes:**
  - `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
    (`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`), for the morphism half of EGA IV
    8.8.2;
  - mathlib's noetherian approximation of étale algebras, for its affine case (F-Limits).
- **Zariski's main theorem:** `IsFinite.of_isProper_of_locallyQuasiFinite`
  (`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`). EGA IV 15.5.1 and IX.4.7 use it.
- **Gluing:** `Scheme.Cover.RelativeGluingData` and `relativeGluingData`
  (`Mathlib/AlgebraicGeometry/ColimitsOver.lean`). VIII.6.4 glues with it (F-Proj-7,
  `ExposeVIII/FiniteSubalgebraGluing.lean`), and so does IX.4.3 sufficiency
  (`ExposeIX/EffectiveGluing.lean`). VIII.7.2 came from colimits of locally directed open
  immersions, `IsLocallyDirected` (F-QA).
- **Henselian rings and flat descent:**
  - `IsAdicComplete.henselianRing` (`Mathlib/RingTheory/Henselian.lean`);
  - `Flat.isQuotientMap_of_surjective` (VIII.4.3);
  - `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`
    (`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, VIII.5.4);
  - fpqc effective epimorphisms (VIII.5.3, `Mathlib/AlgebraicGeometry/EffectiveEpi.lean` and
    `Sites/Fpqc`) (VIII-b).
- **Cohomology and torsors:**
  - non-abelian `H¹`: `PresheafOfGroups` in
    `Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean`, matched to the torsor version
    through `trivializedByEquiv` (`lean/SGA/Foundations/Etale/TorsorCech.lean`; F-Etale);
  - stacks: `isStack_iff` (XIII-a).
- **Closed here, worth upstreaming.** These closed mathlib TODOs:
  - relative differentials as a sheaf (`PresheafOfModules.DifferentialsConstruction`, F-Omega);
  - `IsGeometricallyReduced.isReduced_tensorProduct` (F-Fields);
  - flat base change of `Γ`, used in VIII.5.6 (VIII-b).

  IV also suggested generic freeness, openness of the flat locus and `flat_tfae` (IV).
- **Restated mathlib lemmas still in SGA 1** (REVIEW-1, check before deleting):
  `appLE_comp_appLE_eq`, `range_lid_rTensor`, `isContinuous_iff_isOpen_stabilizer`,
  `finitePresentation_of_finite_etale`.

## Claims that turned out false

Each correction to SGA is recorded with its Lean proof in the "Found during the Lean formalization"
tables of `translation/SGA1/Expose*/README.md`. The list below adds false claims that came from
briefs and from agents.
- **Brief, F-Limits:** "`n` is upper semicontinuous for finite `f`". False:
  `k[x,t]/(x² − t)` over `k[t]`. What is proved is that `n` is locally constant for finite étale
  `f`.
- **I.10.7, I.10.9:** SGA says upper semicontinuous, but the true direction is lower; the upper
  version fails for an open immersion. The Lean statement uses the right direction, but the def
  is still named `geometricFiberCard_upperSemicontinuous_Statement` (I-5).
- **I.9.8:** literally false; it needs `F ∈ A[t]`. Counterexample: `t² + t/2` over `ℤ ⊆ ℚ` (I-2).
- **I.9.11 and I.11:** the first Lean statements were false. They translated SGA's "of finite
  type" as `LocallyOfFiniteType` without `QuasiCompact`, and a connected infinite grid of lines in
  the plane is dominant and unramified but not étale (I; see the docstring of
  `lean/SGA/SGA1/ExposeI/DominantUnramified.lean`). Translate SGA's "de type fini" as both
  conditions. I.5.8 likewise needed `LocallyOfFiniteType` added (I).
- **V.6.8** needs `X'` connected; it fails for `∅` (V-b1).
- **V.6.12**, second claim: false, with `A₃ ⊂ S₃` as counterexample (V-b1). V.6.11 has its
  inclusions swapped (V-b1, X).
- **VI.9:** SGA's step is false for normalized splittings; counterexample `threeToTwo` (VI-2).
- **IX.2.5:** `S'' → S'` should read `S'' → S`; the literal reading has a counterexample
  (F-EGA-IX4).
- **X.1.10:** the coverings `x^p − x = ct` are not pairwise non-isomorphic, since `c` and `jc`
  give the same one (X).
- **IX.6.1:** SGA assumes only that `X_s` is quasi-compact. The proof here also needs it
  quasi-separated, and so does Stacks 0BTX (F-Limits). This is not known to be false, only
  unproved.

## Cheap and expensive surprises

**Cheaper than feared: a different route made it work.**
- **Purity (X.3.1–X.3.4) in every dimension.** The coordinator's queue labelled purity in
  dimension ≥ 3 "big: SGA 2 X Lefschetz". It went through an algebraic induction instead:
  completion, `f`-adic lifting, depth-2 hull, Hartogs, Krull and factoriality
  (`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`,
  `lean/SGA/Foundations/CommAlg/PurityInduction.lean`; F-CommAlg-3). The general forms took one
  more round (F-CommAlg-4).
- **XII.2.4 (connectedness) without GAGA.** The route: Noether normalization, then connectedness
  of the root locus via symmetric functions of the roots, removable singularities and Liouville,
  then "polynomial along lines ⇒ polynomial" by Lagrange interpolation. About 1600 lines in
  `ExposeXII/{Connected,RootLocus,PolynomialLines,EntirePolynomial,RootFunctions,PrimitiveElement}.lean`
  (XII-4).
- **`ℙʳ` simply connected (XI.1.1) for all `r`, without birational invariance (X.3.4).** The
  case `r = 1` used a lattice-index and discriminant argument rather than the genus formula;
  higher `r` used a generic line (`isSimplyConnected_projectiveSpace`,
  `ExposeXI/GenericLine.lean`; XI-7, XI-8).
- **XIII.2.12 for `g = 0`, `n = 1`, without Riemann existence.** The core is a tame different and
  discriminant bound (`finrank_eq_one_of_tame`, XI-10). The bridge was estimated at 800–1100
  lines; it took 833 (`TameGaloisCovering.lean`, 637, and `AffineLinePrimeToP.lean`, 196; XI-11).
- **X.1.2 (Stein factorization is étale).** It reduced to EGA III 7.8.10 (i),
  `etale_fromNormalization` (`Foundations/Cohomology/SteinEtale.lean`). That made X.1.3, X.1.4 and
  X.1.7 unconditional in one round (F-CohBC).
- **I.10.12 for every residue field.** Using that `A^sh` of a normal ring is a normal domain
  avoided SGA's reduction through `A(t)` (F-Limits-4).
- **VIII.6.4.** The finite quasi-coherent subalgebra of the normalization was glued with mathlib's
  `relativeGluingData`, instead of going through EGA I 9.4.7 (F-Proj-7).
- **`FEt.hasQuotients` for every base `S`.** This made `π₁` unconditional, in one round (V-a-2).

**Estimates against outcomes.** The estimates came from the agents themselves. Several large ones
were met in a single round:
- I.10.11, estimated at 1000+ lines: proved by F-Limits-4.
- VIII.7.8, estimated at 2500+: proved, `ExposeVIII/LineBundleDescent.lean` is 910 lines plus
  `AmpleEffectiveness.lean` at 649 (F-Proj-6).
- SGA 4 VIII 5.5 (finite pushforward stalks), estimated at 1.5–2.5k: proved, with
  `EtaleStalkPushforward.lean` at 463 lines plus helper files (F-Hens-4).

**Dearer than hoped.**
- **Grothendieck existence.** Ten rounds by one agent, and the proper case is still open. Most of
  the cost went into EGA III §§1–4, which had to come first (hard-parts §1).
- **XIII Appendix I in mixed characteristic.** About 5000 lines in all, and the last case is open
  (hard-parts §5).
- **Strict henselization, noetherianity (06LJ).** It blocked two exposés for about two days
  before it was proved (F-Hens-3).
- **Sheaf-level Exposé III.** Hand-built chart presheaves could not be connected to the
  Foundations cohomology. When you build a sheaf, build it as `Scheme.Modules` from the start
  (hard-parts §2).
