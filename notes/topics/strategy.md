---
updated: 2026-10-04
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
- **Before each milestone, not only at the start of the round, re-read `ls -t notes/log | head`
  and the registry** (2026-10-04, xii4). A reply to my question arrived while I worked. I had
  already written a duplicate of the other stream's separation step, and had to delete it. It
  was my own new file, so nobody depended on it.
- **Foundations cannot import SGA 1.** When a Foundations theorem needs an SGA 1 result, take
  that result as a hypothesis and discharge it in the exposé. (Three Foundations files break this
  rule; see the hygiene debt below.) Examples:
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
  - Run it before you report, not only at integration (2026-10-04, xii4). A scratch file importing
    my modules next to the barrel and the neighbouring Foundations modules found that my
    `AnalyticGeometry.extendByZero` already existed in `Foundations/Analytic/Sheaf.lean`, with the
    same lemma names. Grep found nothing because I had searched for the concept under different
    words. Import only modules whose `.olean` is newer than the source.
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
- **Checking a patch to a shared file without editing it** (xi14, 2026-10-04). To check a
  refactor of a tracked file that many modules import (e.g. moving lemmas into `Devissage.lean`)
  without making everyone rebuild:
  1. copy the patched files into `<scratch>/tree/SGA/...`;
  2. make a shadow build tree, with one symlink per file of `.lake/build/lib/lean/SGA` except the
     patched modules;
  3. compile each patched module and each downstream module you care about, in import order:
     `LEAN_PATH=<LEAN_PATH with .lake/build/lib/lean replaced by the shadow tree> lean -R
     <scratch>/tree -o <shadow>/SGA/.../M.olean <scratch>/tree/SGA/.../M.lean`.

  Lean resolves the whole `SGA` package from the first `LEAN_PATH` entry that contains it, so the
  shadow tree must hold every module, not only the patched ones. `rm` the symlink before writing an
  `.olean` with `-o`, or the write goes through the link into the real build directory. xi14 used
  this to hand the coordinator a dedup patch that was checked to compile.
- **`lake env lean` vs `lake build`.** The lakefile sets `maxSynthPendingDepth = 3` and
  `relaxedAutoImplicit = false`. To make `lake env lean File.lean` agree with `lake build`, pass
  `-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false` (III-4, I-3).
- **Wrap-up checklist**, as used for PR #18:
  1. a full `lake build` (5917 jobs; 6367 after wave 1 of the out-of-scope campaign,
     2026-10-04);
  2. grep `lean/SGA/SGA1` and `lean/SGA/Foundations` for `sorry`, `admit`, `native_decide`,
     `implemented_by` and `axiom`;
  3. check that every file is imported by its barrel;
  4. from `lean/`, run `lake env lean CheckSGA1Axioms.lean` (24,789 declarations, only `propext`,
     `Classical.choice`, `Quot.sound`; 30,063 on 2026-10-04) and `CheckSGA2Axioms.lean`;
  5. update barrel and module docstrings that still say "statement only";
  6. splice the result into `docs/formalization.md`.
- **Review passes pay.**
  - PI1 noticed that `XI.HasFiniteFundamentalGroup` bounded fibre sizes instead of saying "`π₁`
    finite", so it was redefined (XI-3).
  - REVIEW-1, over I–VI, found stale docs, mislabelled special cases and duplicates.
  - The planned REVIEW-2 (VIII, XI, XII) and REVIEW-3 (IX, X, XIII) were never run (deps.md).
  - Out-of-scope wave 1 (2026-10-04, sga1-oos-coord): every round of every stream was reviewed,
    then six cleanup agents worked through the reviews, each reviewed again. This caught a
    duplicate of an existing lemma, an unfaithful definition (`IsCohomologicallyProperLEZeroGroup`),
    two overclaims in docstrings and logs (see "Claims that turned out false") and docstrings
    crediting SGA with a route it does not take (the plane model and pinching for X.2.9).

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

### Reported during out-of-scope wave 1, not fixed (2026-10-04, sga1-oos-coord)

Pre-existing or new duplicates that the streams and the cleanup agents reported but left alone.
Checked against the code on 2026-10-04. Paths under `lean/SGA/`.

- Three `IsNormalScheme`: `SGA1/ExposeI/Permanence.lean` and `SGA1/ExposeX/Purity.lean` (same body); `SGA1/ExposeXI/Geometry.lean` is weaker (no `IsDomain`), so it cannot become an abbrev.
- Three `exists_isConnected_stabilizer_eq`: `ExposeV/GaloisCategories`, `ExposeX/GaloisFunctors`, `ExposeXIII/HomotopySequence`.
- Three `isConnected_of_isPretransitive` (same statement): `ExposeV/GaloisCategories`, `ExposeIX/GaloisFunctors`, `ExposeX/GaloisFunctors`.
- Two structure maps of `ℙ¹`: `ExposeXI.ProjectiveLine.toSpec k` (`ProjectiveLinePower`) and `ExposeXI.ProjectiveSpace.toSpec k 1` (`ProjectiveSpaceSimplyConnected`).
- Two lift-uniqueness lemmas: `ExposeX.eq_of_comp_eq_of_connectedSpace` (`CoveringOfBase`) and `ExposeIX.eq_of_connectedSpace` (`ProperDescentRigidity`).
- X.1.8's argument twice: `ExposeX.hom_app_eq_id_of_forall_hom_app_pullback_eq_id`, `ExposeX.isEquivalence_pullback_fst_of_isReduced` (`BaseChangeAlgClosed`) vs `ExposeXIII.hom_app_eq_id_of_injective_map_prod`, `isEquivalence_pullback_fst_of_injective_map_prod` (`KunnethInvariance`).
- `ExposeX.connectedSpace_primeSpectrum_of_isLocalRing` (`ExposeX/SpecializationGeometric`) = SGA 2's instance `SGA2.ExposeIII.connectedSpace_primeSpectrum` (`SGA2/ExposeIII/Equidimensionality`).
- `ExposeV.geometricPointAt` (`FundamentalGroupFunctoriality`) and `ExposeX.geometricPoint` (`ExposeX/EtaleCoverings`) have the same body.
- `Scheme.isField_stalk_spec` (`Foundations/Etale/LocalAcyclicityStrictLocalization`) generalizes `ExposeI.maximalIdeal_stalk_spec_residueField` (`ExposeI/FiberStalk`, which imports only mathlib); move the former to a light file first.
- `Scheme.Hom.eq_of_comp_toSpecStrictLocalization` (`Foundations/StrictLocalizationLift`) should follow from `Scheme.Hom.eq_of_comp_eq_of_formallyUnramified` (`Foundations/StrictLocalizationFunctorial`), which imports it through `StrictlyHenselianLift`: move the latter down first.
- `SGA2.ExposeIV.isIso_app_conePt_of_preservesLimit` (`SGA2/ExposeIV/ModuleRepresentation`) = `CategoryTheory.isIso_app_conePt_of_preservesLimit` (`Foundations/Etale/ProperBaseChangeClosure`).
- XII Nullstellensatz: `ExposeXII.Points.{exists_ker_eq, isNilpotent_of_forall_apply_eq_zero}` and half of `Points.nonempty_iff_nontrivial` (`ExposeXII/Comparison`) restate three `IsAlgClosed` lemmas of `Foundations/Fields/GeometricallyConnected`, which pulls in about 75 modules: move those to a light file first.
- Foundations files importing SGA 1: `Foundations/Smooth/GeometricallyReduced` (`ExposeII.Permanence`) and `Foundations/Etale/GabberFiniteCover` (`ExposeI.Unramified`, `ExposeV.QuotientDescent`, `ExposeVIII.QuasiFiniteOpenInFinite`), both new in wave 1; `Foundations/CommAlg/FlatDepth` (`ExposeIV.LocalCriterion`) is older.

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
  - Points of `FEt.fiber`: a definition that builds a fibre point with
    `(FEt.fiberInclIso Ω s).app X).toEquiv.symm` makes the *kernel* time out whenever it has to
    compare it with a coercion (`Equiv.ext fun y ↦ …` in a `Perm`, `σ • y` against the definition):
    the kernel unfolds the larger definition first and lands in the fibre functor. Even
    `fiberPoint x = (fiberEquiv x).left := rfl` times out. Fix: make the constructor an
    `irreducible_def` (`fiberMk` in `ExposeXI/TateModule.lean`) and use `pointOfIso_toEquiv_symm`
    (2026-10-03, xi21t). Likewise a long proof whose statement mentioned `FEt.fiberPoint k y`
    took 135 s in the kernel and timed out; stating it for a plain point `y : Spec k ⟶ Y.left`
    with `hy : y ≫ Y.hom = s`, and plugging in `fiberPoint k y` and `fiberPoint_comp` at the call
    site, brought it to 3 s (`exists_torsionPoints_of_lift`, 2026-10-04, xi21t).
  - `CommRingCat.ofHom { toFun := …, map_mul' := by simp … }` on a stalk: inside the structure the
    stalk type is unfolded to `colimit.cocone …`, and `simp` no longer applies `map_one`/`map_mul`
    of other ring maps. State the function and its `map_*` lemmas separately and plug them in
    (`cotangentPointFun` in `Foundations/GroupScheme/MulNCotangent.lean`; 2026-10-03, xi21t).
  - Transporting an iso through an equivalence of categories of coverings
    (`(TopCat.FiniteCovering.equivalenceAction b).fullyFaithfulFunctor.preimageIso i`) and then
    applying `Over.w` to it timed out in `whnf`; `clear_value j` on the resulting iso fixed it.
    Give the `FiniteCovering` instances (`PathConnectedSpace`, …) on `TopCat.of B` explicitly
    rather than letting instance search unfold `TopCat.of` (2026-10-03, cx-top,
    `Foundations/Topology/PuncturedDisc.lean`).
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
  - Points of `Spec`: `f (closedPoint K)` fails to typecheck inside `rw`/`simp` when the source of
    `f` is `Spec R` for `R : CommRingCat` (a residue field) or `(Over.mk …).left`, because
    `closedPoint K : PrimeSpectrum K` is not syntactically a point of that scheme. Evaluate at
    `t` from `obtain ⟨t⟩ : Nonempty (Spec R) := inferInstance` and use `Subsingleton.elim` for the
    image in `Spec k` (`eq_one_of_mem_inertiaGroup_translate`, 2026-10-04, xi21t).
  - `refine h.mpr fun K _ x y hxy ↦ ?_` for a goal `∀ (K : Type u) [Field K], …` does not make the
    `Field K` binder a local instance in `?_`; use `refine h.mpr ?_; intro K _ x y hxy`
    (2026-10-04, xi21t). With `open MonObj`/`GrpObj`, `ι` is the inverse notation: `let ι := …`
    fails with "Invalid pattern variable" (2026-10-04, xi21t).
  - `MorphismProperty.pullback_fst (P := @UniversallyInjective)` needs
    `set_option backward.isDefEq.respectTransparency.types false in`, as in mathlib's
    `Morphisms/Integral.lean`; `UniversallyInjective (f ≫ g)` is not an instance, use
    `MorphismProperty.comp_mem` (2026-10-04, xi21t).
  - `rw [← Nat.ordProj_mul_ordCompl_eq_self n p]` rewrites every `n`, including inside
    `n.factorization p`. Prove the statement for `ordProj * ordCompl` and rewrite back in the
    hypothesis, or name the pieces with `obtain ⟨v, hv⟩ : ∃ v, n.factorization p = v := ⟨_, rfl⟩`
    first (`pow_tateModuleOfAtFun`, 2026-10-04, xi21t).
  - `(⟨ℓ, hℓ⟩ : ℕ+) ^ r` is elaborated with inferred type `{n // 0 < n}`, not `ℕ+`, so instance
    search and `rw` patterns break (`continuous_apply` found no `TopologicalSpace` on the Pi
    type). Write `ℓ.toPNat hℓ ^ r`. Even then, `exact` with a goal mentioning
    `torsionPoints G ↑(ℓ.toPNat hℓ ^ r)` against one with `torsionPoints G (ℓ ^ r)` can time out
    in `whnf` (the unifier unfolds `torsionPoints`/`mulN` instead of the exponent). State the
    one rewrite you need as a lemma at that exact form (`coe_tateModuleOfAt_apply_toPNat_pow`) and
    `rw` with it, and convert hypotheses with `by rw [coe_toPNat_pow]; exact hg`
    (`TateModulePrimary.lean`, 2026-10-04, xi21t).
  - With `open MonObj`, `mul_assoc`/`mul_one` resolve to the monoid-object lemmas; write
    `_root_.mul_assoc` (2026-10-04, xi21t).
  - Sections of étale coverings through a fixed point: use V.6.4
    (`ExposeX.exists_section_iff_forall_smul_eq`, `ExposeX.smul_eq_of_mem_range_section`) on
    `⊤_ (FEt T)`, whose structure map is an isomorphism (`isIso_terminal_hom`, in `SerreLang.lean`
    since the 2026-10-04 cleanup);
    no need to redo the connected-component argument (2026-10-04, xi21t).
  - Building a group object from structure maps you lifted (say through an étale covering): do
    not check the `MonObj` axioms in monoidal form. Put a `Group` on every `S ⟶ X` with
    `Group.ofLeftAxioms` (`f * g := lift f g ≫ m`), reduce each axiom by `comp_lift_assoc` to one
    universal case on `X ⊗ X ⊗ X` or `X`, prove that by rigidity of lifts, and take
    `GrpObj.ofRepresentableBy` with `homEquiv := Equiv.refl _`. Its `one`/`mul` are then your
    maps up to `toUnit_unique`/`lift_fst_snd`, and uniqueness of the structure is `GrpObj.ext` +
    `MonObj.ext` (`mul` determines everything). Write `IsMonHom` for a non-instance structure as
    `@IsMonHom _ _ _ _ _ G.toMonObj _ f`, and inside proofs use `let _ := G`
    (`AbelianVarietyCovering.lean`, 2026-10-04, xi21t).
- **`rw` on `Scheme.Etale` objects (2026-10-03, xiii14).** Goals about `W.left` for `W : X.Etale`
  often fail `rw` with "motive is not type correct at the implicit transparency". What works:
  evaluate a morphism equation at a point with `congrArg (fun φ ↦ φ x) h` then
  `simp only [Scheme.Hom.comp_apply] at h ⊢; exact h`; for "range ⊆ U" use
  `Scheme.Hom.comp_preimage` on opens instead of points; `(a ≫ b).left = a.left ≫ b.left` is `rfl`
  (`Scheme.Etale.comp_left'`); plain `simp [defs]` succeeds where `simp only [...]` fails;
  replace `let x := …` by `obtain ⟨x, hx⟩ : ∃ x, P x := ⟨_, h⟩` when a `let` makes `rw`/`exact` time
  out; split `exact f a b c` into `have`s when elaboration times out. Mixing `A : Type` and
  `CommRingCat` lemmas: pass `(A := CommRingCat.of A)` explicitly.
- **Étale sheaves: reusable tools (2026-10-03, xiii14).** Agreement locus of two sections
  (`Scheme.etaleAgreementLocus`, `Foundations/EtaleStalkProper.lean`): open, sections agree on
  étale `W`-schemes mapping into it, contains points where germs agree. Every mono of étale
  sheaves is regular (`Scheme.isRegularMonoCategory_sheaf`). `h^* h_E ≅ h_{X'×_X E}` on images of
  sections is base change of morphisms (`Scheme.etalePullbackYonedaIso_hom_unit`).
- **Universes.**
  - `H¹` and `R¹f_*` of étale sheaves of groups live in `Type (u+1)`, which blocked the `R¹` base
    change map (F-Etale, F-Etale-3).
  - The biproduct lemmas of cohomology need `σ : Type` (universe 0) (F-Coh-VIII).
  - `DecompositionInertiaEtaleStatement` is still stated in `Type`.
- **Restricting to `U ∩ V` without rewriting opens** (2026-10-03, xiii43): to use `IsIso (p ∣_ U)`
  on a subset of `U`, take `W := U.ι ''ᵁ (U.ι ⁻¹ᵁ V)`; `morphismRestrict_app` then gives
  `p.app W ≫ (eqToHom map)` directly and `IsIso.of_isIso_comp_right` finishes, with no dependent
  rewrite of `W` (`ExposeX.app_bijective_of_isNormalScheme`).
- **`maxHeartbeats`.** Use it only with a comment (CONVENTIONS.md). There are 11 overrides now,
  10 of them in `ExposeXIII/Abhyankar*.lean`, all commented. Split a file once it takes minutes
  to compile.
- **Global instances affect everyone downstream.** Grep before adding one. Examples added during
  the campaign:
  - `etale_residueField_tensor` (`ExposeI/StandardEtale.lean`);
  - `IsZariskiLocalAtSource @Etale` (`ExposeV/SchemeGaloisCategory.lean`);
  - two copies of `isStableUnderBaseChange_isFinite_inf_etale`;
  - the priority-10000 `sectionRing.instSemiring`.

- **Points that are only propositionally equal** (2026-10-03, xiii3). `(ξ ≫ f).imagePoint` is not
  syntactically `f ξ.imagePoint`, so stalks at the two points don't match. State the helper with the
  point as a variable plus an equation and `subst` it (`Scheme.exists_SpecMap_fromSpecStalk_eq` in
  `Foundations/StrictLocalizationFunctorial.lean`); compare ring maps out of a stalk with
  `cancel_mono (X.fromSpecStalk x)` and `Spec.map_injective` (mathlib knows `fromSpecStalk` is a
  mono; no locality needed). For `(ξ ≫ f) ≫ g` vs `ξ ≫ f ≫ g`, use an `eqToIso` and prove its
  properties in a lemma about a general equation, by `subst`.
- **`attribute [local instance] specializationOrder` also applies to `ℕ∞`** (2026-10-03, xiii3), which
  is a topological space, and breaks `nonpos_iff_eq_zero` and friends on `coheight`. Write
  `let _ : PartialOrder Z := specializationOrder Z` inside the proof instead. Schemes already carry
  the global specialization `Preorder` used by `ringKrullDim_stalk_eq_coheight`.

- **Instances stated for `R : CommRingCat` are not found at `CommRingCat.of A`** (2026-10-03, xii51).
  `#synth (ExposeV.specFunctor (CommRingCat.of A)).Full` fails although `instance : (specFunctor
  R).Full` exists: the discrimination tree reduces `↑(CommRingCat.of A)` to `A`, the instance key
  keeps `↑R`. Use a definition built inside the generic context instead, e.g.
  `(ExposeV.specEquivalence (.of A)).isEquivalence_functor`, and pass it with `@`. XIII-b-2 hit
  the same trap with `(specFunctor (CommRingCat.of k[X])).IsEquivalence` and fixed it the same
  way: prove the instance as a lemma for all `R` and apply it.
- **Kernel deterministic timeouts from `subst` in data** (2026-10-03, xii51). A homeomorphism
  defined by `obtain ⟨f⟩ := inst; subst h; exact …` (to change the `Over` instance) elaborated
  fine, but every lemma about its values hit `(kernel) deterministic timeout`. Define data with
  explicit fields (`toFun χ := ⟨Spec.map …, proof⟩`) and keep `subst` inside `Prop` fields
  (`continuous_toFun`). Then the value lemma is `rfl`
  (`SchemePoints.specPointHomeomorph'` in `ExposeXII/RiemannLocalAffine.lean`).
- **`(specFunctor R).obj S).left` is `Spec S` only up to heavy unfolding** (2026-10-03, xii51).
  Build your own objects with `MorphismProperty.Over.mk ⊤ (Spec.map …) prop`, so that `.left` is
  syntactically `Spec (.of S)`, and relate them to `specFunctor` once, by `Over.isoMk (Iso.refl _)`
  (`specCoveringFunctor`, `specCoveringFunctorIso`). With two `Over` instances on `Spec (.of S)`
  (`specOver` and `overOfCovering`), type class search picks the wrong one: state types through the
  bundled object (`((schemePointsFunctor ℂ X).obj Y).obj.left`) instead of `SchemePoints ℂ (Spec S)`.
- **`U.2 : U.1 ∈ X.affineOpens` blocks `rw` with `IsAffineOpen` lemmas** (2026-10-04, xii51).
  Terms built from `U.2` (`U.2.isoSpec`, `SchemePoints.chart U.2`) make `rw [IsAffineOpen.…]`
  fail with "motive is not type correct at implicit transparency" (`U.1 ∈ X.affineOpens` is only
  defeq to `IsAffineOpen U.1`). Build everything from a lemma with the right statement,
  `private lemma isAffineOpen_val (U : X.affineOpens) : IsAffineOpen U.1 := U.2`
  (`ExposeXII/RiemannLocalChart.lean`). Same trap for elements `⟨e, he⟩` of a subtype whose type is
  a `TopCat` object: give the element the bundled type (`let q : E.obj.left := ⟨e, he⟩`) and use
  `congrArg … (h.apply_symm_apply q)` instead of `rw`.
- **Structure literals with `let`-bound chosen data time out** (2026-10-04, xii51). A `LocalModels`
  instance written as `let S U := F.objPreimage …; { φ U := …, hom_φ U := by … }` hit
  `whnf` timeouts in the `Prop` fields. Split it: a `def` taking the data `S`, `ψ` as arguments
  (`RiemannLocal.localModelsOfIso`), with each field proved by a separate lemma, and apply it to
  the chosen data last. Pass implicit arguments explicitly (`hom_chartφ (U := ⟨U.1, _⟩)`) when the
  index is a re-packaged subtype element.
- **`IsZariskiLocalAtTarget (@IsFinite ⊓ @Etale)` and `Scheme.Cover.pullbackHom` need
  `set_option backward.isDefEq.respectTransparency false`** (2026-10-04, xii51), as in mathlib's
  `ColimitGluingData.glued`; then `inferInstanceAs (IsZariskiLocalAtTarget (@IsFinite ⊓ @Etale))`
  gives `ExposeV.finiteEtaleHom` locality (`RiemannLocal.LocalModels.glued`).
- **Name clash: mathlib has `AffineBasis`** (affine geometry). Inside your own namespace a structure
  called `AffineBasis` still loses to the root one when applied to `X : Scheme` (it coerces `X` to a
  type). Hence `RiemannLocal.AffineOpenBasis`.
- **Objects built by a `def` with `letI` instances inside (round 3, xii51).** For
  `liftObj e S₀ := letI : Algebra A S₀ := …; FiniteEtale.of A (ULift S₀)`, writing
  `CommAlgCat.ofHom f` or `CommAlgCat.isoMk e` makes Lean unfold the `def` to unify
  `of A ?X ≟ (liftObj e S₀).obj`, set `?X := ULift S₀` and then fail to synthesize the local
  `Algebra A (ULift S₀)`. Fix: `(ConcreteCategory.ofHom f : X.obj ⟶ Y.obj)`, morphisms as structure
  literals with the type `X.obj →ₐ[A] Y.obj` written out, and `ULift.ringEquiv (R := S₀.obj)` with its
  implicit argument given (`RiemannReductionUniverse.lean`). Likewise `Points.ext`, `AlgHom.ext`,
  `Points.homeomorph` *synthesize* their `[Algebra K A]` argument, so they fail on points of
  `pointsFunctor`'s objects (whose `ℂ`-structure is a `letI := algebraOfFiniteEtale …` inside the
  functor): use `DFunLike.ext` or `ext; rfl`, or restate the `letI` before the call.
- **A finite set of points of a sub-covering**: `Finset.subtype p s` has type `Finset (Subtype p)`,
  which is the carrier of a restricted `FiniteCovering` only up to unfolding, so `Finset.mem_subtype`
  then fails to rewrite. Take the covering's own fibre `(E.property.2 ψ).toFinset` and compare products
  with `Finset.prod_bij` (`SeparatingData.mem_essImage_chartCovering`). An anonymous constructor
  `⟨e, h⟩` at such a carrier can time out in `whnf`: `let q : (chartCovering E U).obj.left := ⟨e, h⟩`.
- **`λ` is a keyword**, so `λ'` is not an identifier (xii51).
- **`List.TFAE.out` is 1-indexed** in this mathlib (`(h.out 2 3)` for the second and third items),
  and `(h.out i j).mp` must be split into a `have` before projecting `.1`.
- **Gluing along paths without subdivisions (2026-10-03, cx-top, Seifert–van Kampen).** To glue
  local data along a path `γ` (here: functors `π(W i) ⥤ G` into a group), define a *development*
  `D : I → G` by a filter condition (`∀ t, ∃ i, ∀ᶠ s in 𝓝 t, γ '' uIcc t s ⊆ W i ∧ D s = … * D t`),
  prove uniqueness by `IsLocallyConstant` of `fun t ↦ D t = D' t`, and existence by showing the
  set of `τ` admitting a development "up to `τ`" is clopen (`Path.eventually_image_uIcc_subset`,
  `unitInterval.eventually_uIcc_subset` in `Foundations/Topology/PathConnectedHelpersBasic.lean`).
  Homotopy invariance: the value is locally constant in the homotopy parameter (Lebesgue number on
  `{s₀} × I`, `lebesgue_number_lemma_of_metric`), and every local homotopy is the image of one in
  the simply connected `I` or `I × I` (clamp the interval, or parametrize a small box), so no
  explicit subdivision is ever written. See `Foundations/Topology/VanKampenPushout.lean`. Trap: a
  `change` that has to unfold a functor whose `map` uses `inv` (an `IsIso` instance) timed out in
  `whnf`; write the inverse as the class of the reversed path (`⌈p.symm⌉`) and state the `map`
  formula as an `rfl` lemma.
- **Statements about subsets of `ℂ` that must survive van Kampen (2026-10-04, cx-top).** State them
  for *any* space `X` with an open embedding `j : X → ℂ` onto the set, and phrase the conclusion
  relative to `j` (e.g. `FundamentalGroup.IsLoopAround j s σ`). Then the van Kampen pieces
  `↥(j ⁻¹' W)` (subtypes of subtypes) are instances via `j ∘ Subtype.val`, with no homeomorphism to
  transport; one transport lemma along `X' ≃ₜ X` (`FundamentalGroup.mapHomeomorph`) covers the base
  case. See `Complex.exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding`
  (`Foundations/Topology/SurfaceGenusZero.lean`). Free bases: prove the universal property
  `∀ {H : Type} [Group H] (g : ι → H), ∃! φ, …` and finish with `FreeGroupBasis.ofUniqueLift`.
- **Small traps (2026-10-04, cx-top).** `C ∩ {z | p z} \ S` does not parse (`∩` is `infixl:70`,
  `\` is `infix:70`): parenthesize. `ContractibleSpace (C ∩ D)` elaborates `∩` on `Type`: write
  `↥(C ∩ D)`. In `refine ⟨…, fun g ↦ ?_⟩` against `∀ {H : Type} [Group H] (g : …), …` the bound
  `H` is inaccessible; write `fun {H : Type} [Group H] g ↦ ?_`. `Path.Homotopic.Quotient.mk_map`
  only matches `p.map f.continuous` with `f : C(X, Y)`; for a bare `Continuous` proof use
  `Path.Homotopic.Quotient.eq.mpr (h.map ⟨_, hcont⟩)` and let defeq do the rest. Products of
  covering maps: `IsEvenlyCovered`'s trivialization `f ⁻¹' U ≃ₜ U × I` is built by hand
  (`IsEvenlyCovered.prodMap/piMap`, `Foundations/Topology/CoveringProd.lean`); the preimage of a
  box under `Pi.map`/`Prod.map` is a box by `rfl`.

- **`Scheme.Modules` traps (2026-10-04, xi14).**
  - `Scheme.Modules` is a `def`, so `SheafOfModules.unit X.ringCatSheaf` does not get the
    `X.Modules` instances (`Module Γ(X,⊤) (M.H n)`), and `rw` fails with "motive is not type
    correct". Write `CohomologyAux.unitModule X` (an abbrev typed `X.Modules`).
  - `open Scheme.Modules` makes `pullback` ambiguous with `Limits.pullback`; write
    `Scheme.Modules.pullback π` in full.
  - A `ShortComplex` built inline (`ShortComplex.mk 0 0 _`) and passed to a lemma with implicit
    `{S}` timed out in `isDefEq` (unifying `?S.X₂` against `M` unfolds `eulerChar`). Pass `S`
    explicitly with `@`.
  - `biproduct.ι_desc` and friends sometimes fail to `rw` in `X.Modules` (instance paths to the
    zero morphisms); `erw` or `simp` works. `(hom).app U (r • x) = r • …` with `r` of type
    `Γ(F' j, U)` (a defeq copy of `Γ(X, U)`) does not `rw`; close it with
    `exact (Hom.app_smul φ r x).symm`.
  - No need for the extension of sections (Stacks 01PD) to compare two coherent modules that agree
    on an open `U`: map both to `Q = j_* j^* G` (`j : U ⟶ X`, quasi-coherent by
    `isQuasicoherent_pushforward_ι`) and take the image of the biproduct; see
    `CohomologyAux.additive_eq_of_bijective_app_comp` (`Foundations/Cohomology/EulerCharacteristicGeneric.lean`).
- **Algebra traps (2026-10-03, xi14).** `local notation "F" => FractionRing …` breaks named
  arguments `(A := A)` and `variable` lines (hygiene, "unknown constant σ✝"): write the type out.
  There is no `AlternatingMap.restrictScalars`; build it from `toMultilinearMap.restrictScalars`.
  `IsBaseChange` is a `def`, so `h.basis` dot notation fails: write `IsBaseChange.basis b h`.
  To move a basis or `Module.Free` between two localizations away from the same element, use the
  semilinear `Module.Free.of_equiv` with `RingHomInvPair.of_ringEquiv`
  (`Module.exists_ne_zero_free_of_isLocalizedModule`).

- **Complex analysis on manifolds (2026-10-04, xii4).**
  - A `ChartedSpace ℂ M` with `IsManifold 𝓘(ℂ) ω M` is a real smooth manifold for the *same*
    charted space: `isManifold_of_contDiffOn` plus `restrict_scalars`
    (`AnalyticGeometry.isManifold_real_of_complex`). It is a `theorem`, so use `have := …`
    locally, not an instance. `extChartAt 𝓘(ℝ, ℂ) p = extChartAt 𝓘(ℂ) p` is `rfl`. This gives
    `SmoothPartitionOfUnity` on Riemann surfaces for free.
  - Holomorphy in charts: `AnalyticGeometry.mdifferentiableAt_iff_differentiableAt_chart` (any
    chart whose source contains the point), `MDifferentiableOn.differentiableOn_chart`
    (`Foundations/Analytic/Montel.lean`).
  - `∂̄`: mathlib's convolution API (`HasCompactSupport.contDiff_convolution_left`,
    `hasFDerivAt_convolution_left`) plus `locallyIntegrable_of_norm_le_rpow` for `1/z` gives the
    Cauchy transform's smoothness and derivative. Only the generalized Cauchy formula needs work
    (`Complex.integral_comp_polarCoord_symm`, Fubini, `HasCompactSupport.integral_Ioi_deriv_eq`).
  - `convert … using 1` on `HasDerivAt` goals for `ℝ → ℂ` functions descends into the
    `AddCommGroup` instance arguments. Use `HasDerivAt.congr_deriv` instead.
  - Normed products over `[Fintype ι]`: theorems whose *statement* mentions only the topology
    trigger `linter.unusedFintypeInType`. Switching to `[Finite ι]` makes the Pi topology and the
    normed-Pi topology differ syntactically, and elaboration times out. Keep `Fintype` and disable
    that linter locally, with a comment.
- **Building a manifold by hand (2026-10-04, xii4, compactification of coverings).**
  - A space glued from pieces: make it an `inductive` type, not a `def … := A ⊕ B`. The `def`
    unfolds to `Sum` and picks up `Sum`'s `TopologicalSpace` instance.
  - The final topology for a family of maps `jᵢ : Yᵢ → M` is `⨆ i, coinduced (jᵢ) _`: in mathlib
    `t ≤ t'` means *finer*, so it is a `⊔`, not a `⊓`. Then `isOpen_sup` and `isOpen_iSup_iff`
    give `IsOpen s ↔ ∀ i, IsOpen (jᵢ ⁻¹' s)` (by `Iff.rfl` for `coinduced`). Each `jᵢ` is an open
    embedding as soon as the `jₖ⁻¹(jᵢ(U))` are open.
  - Charts: `(hj.toOpenPartialHomeomorph j).symm.trans (hk.toOpenPartialHomeomorph k)` for open
    embeddings `j : Y → M` and `k : Y → ℂ` with the same domain. The source is `range j`, and
    `toOpenPartialHomeomorph_left_inv` computes everything. If rewriting `z` as `↑⟨z, hz⟩` hits
    "motive is not type correct", use `congrArg _ (h.toOpenPartialHomeomorph_left_inv (x := ⟨z, hz⟩))`.
  - `IsManifold 𝓘(ℂ) ω`: `isManifold_of_contDiffOn`, then `DifferentiableOn.analyticOnNhd` and
    `AnalyticOnNhd.contDiffOn_of_completeSpace`. A coordinate change that is a continuous local
    inverse of a holomorphic map with nonzero derivative is holomorphic by
    `HasDerivAt.of_local_left_inverse`; no inverse function theorem is needed.
  - Pass instance-carrying data in a structure with `attribute [instance] top` (here
    `PuncturedPlaneCovering S`). The compactification `C.Fill` then gets genuine instances,
    `T2Space`, `CompactSpace`, `ChartedSpace`, `IsManifold`. Proof arguments (`hp`, `hfin`)
    cannot be found by instance search.
- **`π₁` lives one universe up (2026-10-04, xiii212).** `ExposeV.etaleFundamentalGroup Ω ξ` is
  in `Type (u+1)`, but statements such as A14 quantify over finite test groups `G : Type u`. So
  `π₁ ⧸ N` cannot be fed back into such a hypothesis. Transfer it through `Shrink.{u}` and
  `Shrink.mulEquiv`, as in `ExposeXIII.bijective_eval_of_small`
  (`SGA1/ExposeXIII/MultiplicativeGroupInertia.lean`).
- **`PrimeSpectrum.basicOpen r` against `(Spec R).Opens` (2026-10-04, xiii212).** The coercion
  makes `rw [Scheme.isoOfEq_inv_ι]` and similar rewrites fail with a "motive is not type correct"
  error. Restate the lemma with `Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)` and use
  `erw`. Also write `basicOpenIsoSpecAway (R := .of A) r` out, because `R` is not inferred from
  `r : A`.
- **`IsIso (pullback.fst f e.hom)` with `e` an iso is sometimes not found by instance search**
  (2026-10-04, xiii212). Pass `pullback_fst_iso_of_right_iso _ _` to `@asIso` explicitly.
- **Smoothness checked on charts (2026-10-04, xiii212).** `HasRingHomProperty.of_iSup_eq_top`
  takes `P` implicitly, so call it as `(P := @SmoothOfRelativeDimension n)`. Its ring-level `Q` is
  `RingHom.Locally (IsStandardSmoothOfRelativeDimension n)`, so wrap the chart fact in
  `RingHom.locally_of isStandardSmoothOfRelativeDimension_respectsIso`. For a standard smooth
  `R[X]`, use mathlib's `PreSubmersivePresentation.naive` with no relations
  (`ProjectiveLineCurve.isStandardSmoothOfRelativeDimension_polynomial`). To compute
  `f.appLE ⊤ V le_top x`, state it as `rfl` against `X.presheaf.map (homOfLE _).op (f.appTop x)`:
  `rw [Scheme.Hom.appLE]` does not fire under the coercion.
- **Kernel `deterministic timeout` from `eqToHom` between sheaves (2026-10-04, xiii3).** A `def`
  whose body contains `eqToHom (congrArg (fun v ↦ (etalePullback v).obj F) e)` gets its proof
  abstracted to `foo._proof_1` (nested proof abstraction), while theorem statements keep the
  inline proof. Matching the two apparently makes the kernel reduce the `Eq.rec` in `eqToHom`; `Eq`
  is K-like, so it tries to decide whether the two inverse-image sheaves are definitionally equal,
  which unfolds sheafification and does not finish (the elaborator is fine, only `lake build` or
  `lake env lean` fail, about 50 s later). Fix: put the transport in an `irreducible_def` that
  takes the equation as a variable (`Scheme.etalePullbackCongr`,
  `Foundations/Etale/LocalAcyclicityStrictLocalization.lean`) and prove its lemmas by
  `subst e; rw [foo_def]; rfl`. Bisect such timeouts with small `lemma`s using `sorry` and
  `set_option maxHeartbeats 20000` (the kernel respects it, so failures come fast), and use a small
  `MetaM` diff of the two elaborated terms to find the differing subterm.
- **Flatness over a strict henselization for free (2026-10-04, xiii3).** An `R^sh`-algebra which is
  flat over `R` is flat over `R^sh`: it is flat over each neighbourhood `N.Stalk` by mathlib's
  `Algebra.FormallyUnramified.flat_of_restrictScalars` (Iversen I.2.7; `N.Stalk` is unramified and
  essentially of finite type over `R`), and `IsLocalRing.StrictHenselization.flat_of_forall_flat`
  (HenselizationNoetherian) passes to the colimit. So any map `R^sh ⟶ R'^sh` over a flat `R ⟶ R'` is
  flat (`StrictHenselization.flat_of_comp_algebraMap`), with no identification of `R'^sh` as a
  strict henselization of `R^sh ⊗ R'` (which I had planned, and would have cost hundreds of lines).
- **`set` traps.** Besides shadowing (see "Rewriting and elaboration pitfalls"):
  - `set c := chartAt ℂ x` hides `c` from `simp`/`rw` lemmas stated with `chartAt`: restate them
    with a type ascription (`have : coord p ι (c.symm t) = t := coord_chart_symm …`) (xii51).
  - `set s := e with h` on a term that occurs in the type of an instance-implicit hypothesis
    (`Z : FEt (pullback f e)` with `[IsGalois Z]`) gives you a new `Z` whose type mentions `s`. The
    instance still refers to the old `Z`, so `IsConnected Z` fails. Use `let` (2026-10-04, xiii43).
  - `set x := e with hx` hides instances (2026-10-04, xiii3). After `set ν := f.fromNormalization`,
    instance search failed for `LocallyOfFiniteType (ν ≫ p)`, `QuasiCompact ν`, `Surjective ν`
    although `IsFinite ν` was in context. Use a `local notation` in a `section` (as for `η`) and
    write the term out instead.
- **Points of a curve via `Spec` charts (2026-10-04, xiii3).** For statements about closed points of
  a regular curve, charts `Spec A_t ⟶ X` (`Spec.map (algebraMap A A_t) ≫ hV.fromSpec`, an open
  immersion) with an explicit generator of the maximal ideal are much easier than open subschemes:
  `Spec.map_apply` makes points `PrimeSpectrum.comap`, `basicOpen_eq_of_affine` and
  `Scheme.zeroLocus_singleton` turn `zeroLocus {(ΓSpecIso R).inv r}` into
  `PrimeSpectrum.zeroLocus {r}`, and `IdealSheafData.subschemeCover` at `⊤` (an open immersion that
  is surjective, hence an iso) identifies `V(I) ⊆ Spec R` with `Spec (R/I)`
  (`SGA.SGA1.ExposeXIII.exists_chart_of_ne_genericPoint`,
  `AlgebraicGeometry.etale_subschemeι_ofIdealTop_comp`).
- **Comparing sections of `(b ≫ u)^* F` and `b^* u^* F` (2026-10-04, xiii3).** Work with
  "sections along a morphism" `sectionAlong F u A a ha t = (u^*F).map (T ⟶ T ×_X A) (η t)` and the
  one lemma `etalePullbackComp_hom_app_unit_unit` (the unit of `(b ≫ u)^*` is the composite of the
  units, from `unit_conjugateEquiv` + `conjugateEquiv_etalePullbackComp_hom`); everything else is
  naturality and `Etale.pullback_hom_ext` on first projections.
- **Keep canonical pullbacks of schemes out of unification problems (2026-10-04, xiii43).** If
  `pullback f g` (or an open subscheme of it, or a `FEt.pullback` object's `left`) and another
  scheme end up in one `isDefEq` problem, Lean unfolds the limit construction and times out:
  `whnf`/`isDefEq` timeouts in `rw`, `obtain ⟨x, hx⟩ : ∃ x, … := ⟨_, rfl⟩`, `change`, and in instance
  search for `Algebra Γ(U, …) Γ(V, …)` once several such local instances are in context (they are
  tried in turn and their `Γ(_, _)` arguments unified). Fix: state the computation as a lemma about
  an abstract square `(hsq : IsPullback fst snd f g)` with fvar schemes and call it with
  `IsPullback.of_hasPullback`; `AlgebraicGeometry.CohomologyAux.isPushout_app_of_isPullback`
  (`Foundations/Cohomology/FlatBaseChange.lean`; it was `ExposeX.isPushout_app_of_isPullback` until
  the 2026-10-04 cleanup) is the `IsPullback` form, and `CohomologyAux.isPushout_app_pullback_snd`
  is now its corollary. Avoid `let`s whose bodies mention such schemes in goals you then `rw`:
  `kabstract` unfolds them. Example: `ExposeX.isEtaleAt_chart`.
- **`Γ(D(t))` from `Γ(V)` without `Algebra R Γ(Spec R, U)` (2026-10-04, xiii212).** Mathlib's
  instance `Algebra R Γ(Spec R, U)` was not found for `R = .of k[X]`, `U = PrimeSpectrum.basicOpen X`
  (even with `backward.isDefEq.respectTransparency.types false`). For an affine open `V` and
  `t : Γ(V)`, use `hV.isLocalization_basicOpen t` (algebra `algebra_section_section_basicOpen`,
  found fine) and `IsLocalization.ringEquivOfRingEquiv` to get `Γ(D(t)) ≃+* k[T, T⁻¹]` from
  `Γ(V) ≃+* k[t]`. Pass `(T := Submonoid.powers X)` explicitly; otherwise `rw [Submonoid.map_powers]`
  closes the goal by unifying `T` with the wrong submonoid. Example:
  `ExposeXIII.AffineLineChart.basicOpenEquiv`.
- **Statements about an open that several names denote (2026-10-04, xiii212).** The torus of
  `ℙ¹` is `basicOpen chartCoord₀`, `basicOpen chartCoord₁` and `projectiveSpace.torus` at once, and
  `π₁(U, ξ)` depends on the syntactic `U`. Take `U` as a variable with
  `hU : X.basicOpen t = U` and start with `subst hU`. `homOfLE` with different proofs is defeq, so
  the restriction maps still match afterwards.
- **`local notation` inside `variable` (2026-10-04, xiii212).** A `local notation "ℙ¹" => Proj …`
  that mentions a section variable fails inside a `variable` command with "Unknown constant `k✝`".
  Write the expression out there.
- **From a Galois object in `FEt U` to an étale algebra over a field (2026-10-04, xiii212).**
  `ExposeV.geometricFiber R Ω` is by definition `specEquivalence.inverse ⋙ fiberFunctor R Ω`, and
  mathlib's `FiniteEtale.fiber` acts by `φ ↦ φ.comp f.unop.hom.hom`. So for `κ : Spec K ⟶ U`, the
  fibre functor `FEt.pullback κ ⋙ geometricFiber K Ω` is `Hom_K(A, Ω)` with `A` the algebra of
  `E ×_U Spec K`. `Functor.mapAut`, then `MulEquiv.inv'`, then
  `AffineLinePGroups.autOpMulEquivAlgEquiv` turns `Aut E` into a group of `K`-algebra
  automorphisms of `A`, and the action identity is `rfl`. Transport the Galois property along
  `FEt.pullbackFiberIso` and `FEt.fiberSpecIso`. Example:
  `ExposeXIII.TameGaloisAlgebra.bijective_comp_autHom`.
- **An iso in `FEt S` as an iso in `S.Etale` (2026-10-04, xiii212).** Use
  `MorphismProperty.Over.isoMk ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso c)` with
  `by exact Over.w ((MorphismProperty.Over.forget _ ⊤ _).map c.inv)` for the triangle. Example:
  `ExposeXIII.TameGaloisAlgebra.pullbackEtaleIso`.
- **Pullback bookkeeping traps (2026-10-04, xiii43, round 3).** (Its `set` trap is under "`set`
  traps".)
  - `rw [hs]`, where `s` also appears in `pullback.snd f s`, rewrites inside the type: motive
    error. Write `(pullback.condition).trans (congrArg (pullback.snd f s ≫ ·) hs)`.
  - `simp [pullback.lift_fst]` does not fire when the pullback's morphism is a `let`-bound fvar
    (`pullback.fst h ιL` with `let ιL := …`); `erw [pullback.lift_fst_assoc]` does.
  - `IsPullback.of_right'` returns a square with *its own* lift. To keep your morphism, use
    `IsPullback.of_right outer hcomm right`.
  - `K̄` (a letter with a combining macron) is not a Lean identifier; the parser reports
    "expected token".

  Example: `ExposeX.exists_isGalois_finiteDimensional_of_isGalois`.
- **Descending a Galois object along a limit (2026-10-04, xiii43).** Don't descend the group action;
  descend every endomorphism (`ExposeX.exists_liftsEndos_of_isLimit`). Then get Galois-ness once at
  the end: `ExposeX.isGalois_of_liftsEndos` (`H Y` Galois and every endomorphism of `H Y` comes from
  `Y`). Full functors (X.1.8, IX.4.10 equivalences) satisfy `LiftsEndos` for free, and the property
  composes and transports along natural isomorphisms (`LiftsEndos.comp`, `.of_natIso`).

## Already in mathlib (don't rebuild)

- **Covering spaces and `π₁` (2026-10-03, cx-top).** `π₁` of the base of a quotient covering map
  with simply connected total space: `IsQuotientCoveringMap.fundamentalGroupEquiv`
  (`Mathlib/Topology/Homotopy/Lifting.lean`). Hence `π₁(S¹)` is
  `Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv`. `exp : ℂ → ℂ∖{0}` and `z ↦ zⁿ` are
  (quotient) covering maps (`Complex.isAddQuotientCoveringMap_exp`, `isCoveringMapOn_npow`,
  `Mathlib/Analysis/Complex/CoveringMap.lean`, imported through
  `SGA.Foundations.Topology.PuncturedDisc`). Subpaths and their composition up to homotopy: `Path.subpath`, `Path.Homotopy.subpathTransSubpath`
  (`Mathlib/Topology/Subpath.lean`). Lebesgue subdivisions of `I` and `I × I`:
  `exists_monotone_Icc_subset_open_cover_unitInterval(_prod_self)`. The unique uniformity of a
  compact R₁ space: `uniformSpaceOfCompactR1`.
- **Resultants and discriminants (xii51)** (`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`:
  `resultant f g m n`, `resultant_map_map`, `isUnit_resultant_iff_isCoprime`, `discr`).
  `exists_mul_add_mul_eq_C_resultant` only needs *bounds* `deg f ≤ m`, `deg g ≤ n`, so a unit
  `Res(P, P')` gives `P` separable after any base change (`PuncturedPlane.separable_map_of_isUnit`) without
  computing degrees: the clean way to say "étale over `D(δ)`".
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
- **"Coverings of degree prime to `p` are tame"** (xiii212 log, 2026-10-04): false without
  "Galois". In characteristic 2 a degree-3 subcover of an `S₃`-covering of `𝔸¹` (XIII.2.13 for
  `S₃`) has degree prime to `p` but is not tame. What is proved is the Galois case,
  `ExposeXIII.galoisCoveringsTameStatement`.
- **"Every isogeny is a quotient of `n_A`" from `exists_isMonHom_comp_eq_mulN`** (xi21t log,
  2026-10-04): that theorem gives a homomorphism `g` with `g ≫ p = n_A`, not its surjectivity. SGA's
  remark, for connected étale coverings, is `exists_surjective_isMonHom_comp_eq_mulN` (every `n_A` surjective) and
  `…_of_charZero` (`ExposeXI/AbelianVarietyCovering.lean`).
- **XIII 1.3.1, proof:** "`P` and `Q` are locally isomorphic over `Y₁`" must be read near the image
  of `Y'₁`. Read over all of `Y₁`, the condition fails for every proper `f` with `R¹f_* F`
  non-trivial, already for `Y' = ∅`. The first Lean definition of `IsCohomologicallyProperLEZeroGroup`
  read it that way; xiii14 found it and the cleanup corrected it (2026-10-04).
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
- **XI.2.1 (Serre–Lang key step) without abelian-variety theory** (2026-10-03, sga1-xi21). It was
  listed as out of scope ("needs rigidity, isogenies"). `π₁(A)` commutative (XI.2) and Künneth
  (X.1.7) give `(n_A)_* σ = σⁿ`; `σ^deg` fixes the fibre, so `n_A` lifts by the lifting
  criterion. About 360 lines, one session (`ExposeXI/SerreLang.lean`). Trick for base points:
  when the target `π₁` is commutative, `autMap H e` does not depend on `e` or on `H` up to iso
  (`autMap_eq_of_iso_of_comm`), so `π₁` is strictly functorial (`pointedMap_pointedMap`).

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
