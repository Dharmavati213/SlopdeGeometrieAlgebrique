---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 X XI XII XIII, Foundations, out of scope
kind: handoff
---

# Out-of-scope wave 1 integrated: what each stream did, what is left, wave-2 streams

Wave 1 of the out-of-scope campaign (2026-10-03/04) is finished and integrated in the working
tree of `formalization/sga1-out-of-scope`. Nothing is committed. Thirteen streams ran three
rounds each (xii52 two), and every round was reviewed. None of the `…Statement`s in the
out-of-scope table of [`lean/SGA/Foundations/README.md`](../../lean/SGA/Foundations/README.md) is
proved in full. That table, rewritten at integration, is the reference for what is proved and what
is missing per item. Owners and shared rows: [`../topics/out-of-scope-plan.md`](../topics/out-of-scope-plan.md).

## Per item (main result; handoff)

- **X.2.9, X.2.12** (x29). Proved in characteristic 0 for `#k ≤ 𝔠`, universe 0, without XII.5.1
  (`ExposeX.isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`). Also: IX.5.2 for
  disconnected `S'`, `S''`, Noether finiteness of normalization, a plane-curve scheme.
  `2026-10-04-x29-round3-charzero-pinching-planemodel.md`.
- **XI.1.4** (xi14). Reduced to `HodgeSymmetryZeroStatement`
  (`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`); `χ` is multiplicative in
  finite étale coverings in every characteristic (`eulerCharFiniteEtaleStatement`).
  `2026-10-04-xi14-round3-review-fixes.md`.
- **XI.2.1** (xi21t). Stated in SGA's form; proved in characteristic 0, for every `ℓ ≠ char k`,
  and from "`n_A` is an isogeny". In characteristic `p` it is equivalent to the open `p`-primary
  clause. `2026-10-04-xi21t-round3.md`.
- **Topology of `π₁`** (cx-top). `FundamentalGroup.fg_of_compactSpace`, van Kampen in Hatcher's
  form (`FundamentalGroup.vanKampenMulEquiv`), punctured discs and the normal-crossings local
  model, products, `π₁(C ∖ S)` free on loops. `2026-10-04-cx-top-round3-products-hatcher-genus0.md`.
- **XII.5.2** (xii52). XII.5.2 for every connected `X`, given XII.5.1
  (`schemeFundamentalGroupComparison_of_riemannExistence`); LPC and SLSC of `X(ℂ)` by
  semialgebraic geometry, no triangulation. `2026-10-04-xii52-round2-handoff.md`.
- **XII.5.1** (xii51, with xii4's compactification). `Ψ` fully faithful, locality, universes; RET
  for `ℂ ∖ S` and its finite étale covers (`PuncturedPlane.riemannExistence_coordRing`).
  `2026-10-04-xii51-round3-punctured-plane.md`.
- **GAGA** (xii4). `X^an` for separated `X`; XII.3.1 (i)–(iv), (ix), (xi); Forster 14.13
  (`compactRiemannSurfaceMeromorphic`); Cousin I on a disc. Theorem B and Oka not started.
  `2026-10-04-xii4-round3-compactification-iso-cousin.md`.
- **XIII 1.4** (xiii14). Every sheaf of sets over a locally noetherian base
  (`isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`), via Gabber's theorem over a
  noetherian henselian base. `2026-10-04-xiii14-round3-gabber-xiii14-noetherian.md`.
- **XIII.4.3, XIII.4.4** (xiii43). The X.3.8 core (`ExposeX.tameLiftingDVRStatement`), hence the
  second part of XIII.4.4 over a complete DVR with separably closed residue field; XIII.5.5
  stated. `2026-10-04-xiii43-round3.md`.
- **XIII §3** (xiii3). 3.1 1), 3.2 1), 3.3–3.5 stated; 3.2 1) proved for every field (`fieldCohomologicalPropernessStatement`);
  desingularization hypotheses in dimension `≤ 1` over perfect fields. `2026-10-04-xiii3-round3.md`.
- **XIII.4.6** (xiii46). Surjectivity half in every characteristic; the normal finite-type case
  reduced, without resolution, to `AffineLineOpenInvarianceStatement`. `2026-10-04-xiii46-kunneth-round3.md`.
- **XIII.2.13** (xiii213). `p`-groups, `S₃`, `A₄`, Serre's `p`-kernel theorem; reduced to
  Raynaud's cases A and B; field patching in `Foundations/Patching/`.
  `2026-10-04-xiii213-round3-nodal-patching.md`.
- **XIII.2.12** (xiii212). `(g, n) = (0, 0), (0, 1), (0, 2)` on `ℙ¹`; `π₁^{p'}(𝔾_m)`; Galois
  coverings of degree prime to `p` are tame. `2026-10-04-xiii212-round3.md`.

## Integration

1. Barrels: every new module added to `SGA/Foundations.lean` and to the ExposeIX, X, XI, XII and
   XIII barrels, whose docstrings were updated.
2. Full `lake build`: passes, 6367 jobs.
3. `lake env lean CheckSGA1Axioms.lean`: passes, 30,063 declarations, standard axioms only. It
   imports the whole `SGA` barrel, so it also served as the clash check.
4. Cleanup pass: six agents (fix-top, fix-x, fix-xi, fix-xii, fix-xiii-a, fix-xiii-b) worked
   through the reviews' open items, each reviewed again. The fix-x review found two more
   docstrings crediting pinching to X.2.9; a repair pass fixed them. Logs:
   `2026-10-04-fix-xi-cleanup.md`, `2026-10-04-fix-xiii-b-cleanup.md`; the other four wrote none.
5. README out-of-scope table rewritten; registry, `strategy.md` and `hard-parts.md` checked against
   the code (this entry).

## Unfaithful definition fixed

`ExposeXIII.IsCohomologicallyProperLEZeroGroup` (`SGA1/ExposeXIII/CohomologicalProperness.lean`),
found by xiii14. Its second clause (injectivity of `a₁` on `R¹`) concluded "`P` and `Q` are locally
isomorphic over `Y₁`" at every point of `Y₁` from a hypothesis over `Y'₁` only. With `Y' = ∅` it
forced any two torsors to be locally isomorphic, so no proper `f` with `R¹f_* F` non-trivial could
satisfy it. Now it concludes only at points `g₁ y'` over `Y'`, from the hypothesis at `y'`
(`IsLocallyIsoOverAt`). `IsLocallyIsoOver` is kept but now unused.

## Moves by the coordinator and the cleanup agents

- `TopCat.FiniteCovering.exists_monodromy_eq`: from `ExposeXII/FundamentalGroupQuotient.lean` to
  `Foundations/Topology/FiniteCoveringMonodromy.lean`.
- x29's `CurveFiniteSmooth` lemmas: now `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`
  and `IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one` in
  `Foundations/Dimension/StalkKrullDim.lean`; the `ExposeX` names are aliases.
- Deleted duplicate `ExposeIX.PinchingCurve.isClosed_singleton_of_isClosed_singleton_image`; use
  `Scheme.Hom.isClosed_singleton_of_isClosed_singleton_apply` (`Foundations/GroupScheme/Points.lean`).
  `2026-10-04-x29-round3-charzero-pinching-planemodel.md` still lists it.
- Others, each answered in a reply to the stream log it affects
  (`notes/log/2026-10-04-sga1-oos-coord-reply-*.md`): xi14's dévissage patch applied; dimension `≤ -1` results moved
  to `CohomologicalProperness.lean`; `CohomologyAux.isPushout_app_of_isPullback`;
  `isTameExtension_of_isGalois` and friends in `ExposeXIII/TameRamification.lean`;
  `infinite_continuousMonoidHom_aut_fiberFunctor` in `AffineLineFundamentalGroup.lean`;
  `ExposeX.surjective_map_pullback_fst_of_isAlgClosed`; `Scheme.functionFieldIsoSections` public;
  `fromPath_mk_*` and `LocallyContractibleSpace.semilocallySimplyConnectedSpace` moved in
  `Foundations/Topology`; `exists_surjective_isMonHom_comp_eq_mulN` (XI.2's isogeny remark).

## What remains, and suggested wave-2 streams

Per item, from each stream's remaining plan (details in the handoffs above):

- X.2.9: the finite birational `C ⟶ planeCurve` (gives the curve case from plane curves);
  `#k > 𝔠` by descent to a countable field; in characteristic `p`, `𝔭 = (F)`, the lift to `W(k)`,
  the projective X.2.4; Bertini (X.2.10); universes.
- XI.1.4: Hodge symmetry for `q ≥ 1`, analytic Hodge theory. Not a wave-2 item.
- XI.2.1: the theorem of the cube and an ample line bundle, for `p_A`. A separate multi-round
  project; the user should decide whether to start it.
- XII.5.1: all smooth curves (extension across finitely many points, reduction to a finite étale
  cover of some `ℂ ∖ S`), singular curves, higher dimension. Unblocks XIII.2.12 in characteristic 0
  and XIII.2.13 case B.
- GAGA: a Cartan criterion for infinite covers (edits `Foundations/Cohomology/Cartan.lean`), derived
  `H¹(Δ, 𝒪) = 0`, then Theorem B in several variables; fibre products of analytic spaces.
- XIII 1.4: an arbitrary base (EGA IV 8, registry A4, plus constructible sheaves);
  `IntegralBaseChangeStatement`; degree-1 essential surjectivity (Artin approximation).
- XIII.4.3/4.4: EGA II 7.1.7 (Krull–Akizuki; no owner) for general X.3.8; regular bases; XIII.5.5.
- XIII §3: Stacks 0EYS (EGA IV 15.6); the converse comparison; SGA 4 XV 2.1 universally.
- XIII.4.6: `AffineLineOpenInvarianceStatement` (blueprint in the handoff, §4), then descent to
  non-normal schemes and qcqs `X` with arbitrary `Y`.
- XIII.2.13: Harbater–Stevenson's node lemma, then étale lifting, branch locus, specialization
  (needs A4 and EGA IV 9.7.7). Case B waits on curve RET and semistable reduction.
- XIII.2.12: `(0, 2)` for any two points (PGL₂), tame `π₁(𝔾_m)`; general `(g, n)` waits on curve
  RET and III.7.4.
- Topology (optional): the loop around `∞` in genus 0 (consumer: XIII.2.12 on `ℙ¹` in
  characteristic 0); the fibre-bundle exact sequence (claim a registry row first).

Suggested wave-2 streams, unblocked and in my order: (1) curve RET (xii51's plan); (2)
`AffineLineOpenInvarianceStatement`; (3) the plane-model morphism and `#k > 𝔠` for X.2.9; (4) the
HS node lemma; (5) EGA IV 8 (registry A4), shared by XIII 1.4, XIII.2.13, X.2.9 and the in-scope
IX.4.12; (6) EGA II 7.1.7, shared by X.3.8 and the in-scope IX.2.6; (7) the Cartan criterion and
`H¹(Δ, 𝒪) = 0`. The theorem of the cube needs the user's decision first.

## Left for the coordinator

- `docs/formalization.md` is not updated (line 40 still says X.2.9 uses the transcendental X.2.6).
- Docstrings the reviews flagged, still present: `ExposeXIII/NormalCrossings.lean` says 2.3 b) is
  not formalized (it is, for Galois coverings); `ExposeXII/Nullstellensatz.lean:43` says
  "statement only" (proved by `AffineAnalytification.rueckertNullstellensatz`);
  `ExposeXII/LocalTopology.lean` says "open in dimension `≥ 2`" (for singular `X`).
  `CoveringFundamentalGroupStatement` is provable from the LPC/SLSC instances but has no theorem.
- Duplicates reported and not fixed: the wave-1 list in the hygiene debt of `../topics/strategy.md`.

## Notes housekeeping

Deleted the stream files in `notes/now/` (cx-top, x29, xi14, xii4, xii51, xii52, xiii14, xiii212,
xiii213, xiii3, xiii43, xiii46); each stream has a final `kind: handoff` entry, linked above.
xi21t's now-file was already gone. Registry: stale rows fixed (A3, A11, A12, A15, A16, A20, A24,
A39 and others); `hard-parts.md` "Out of scope" rewritten to match the README.
