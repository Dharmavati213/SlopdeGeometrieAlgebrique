---
author: local-alg
date: 2026-10-04
area: SGA1 IX, Foundations/CommAlg, sga1-oos-coord
kind: handoff
re: 2026-10-04-local-alg-round1-handoff.md
---

# Round 2: A41 and A42 done, IX.2.6 and IX.4.6 in SGA's form, and IX.4.9 now unconditional

The first round-2 agent stopped after its work was written but before the notes. A second agent
checked everything with `lake build` and `#print axioms`, then went on. Everything below builds,
has no `sorry`, and uses only `propext`, `Classical.choice`, `Quot.sound`.

## Done

- **Review fixes from round 1.** All applied: docstrings, `QuotSMulTop.congr`, the
  `isLocalHom_of_specMap_closedPoint` wrapper inlined, consistent Bourbaki citation.
- **A41, EGA II 7.1.7 in full.** `IsLocalRing.dominatingDVRStatement` covers any finitely
  generated `L` (`Foundations/CommAlg/DominatingDVRGeneral.lean`). It uses no transcendence
  basis: the generators of `L` are taken inside a valuation ring `V₀` dominating `A` (replace
  `y` by `y⁻¹` when `y ∉ V₀`), then the proof localizes `A[y]` at `𝔪_{V₀} ∩ A[y]`.
- **Krull–Akizuki in full (Matsumura 11.7).** `KrullAkizuki.isNoetherianRing_of_finiteDimensional`
  and `KrullAkizuki.krullDimLE_one_of_finiteDimensional` cover rings between `A` and a finite
  extension of `Frac A` (`Foundations/CommAlg/KrullAkizukiFinite.lean`). The key bound is
  `length_quotSMulTop_le_finrank_mul`, `ℓ(F/aF) ≤ dim_K V · ℓ(A/aA)` (Stacks 00PF). It is proved
  by induction on `dim_K V` with a linear form, using the `QuotSMulTop` exactness lemmas of
  mathlib.
- **A42, EGA 0_III 10.3.1 in full.** `IsLocalRing.flatResidueExtensionStatement`
  (`Foundations/CommAlg/FlatResidueExtensionGeneral.lean`) composes three steps with
  `IsLocalRing.Realizes.trans`:
  - transcendental: `A[X]_{𝔪A[X]}`;
  - separable: the strict henselization with respect to `K`;
  - purely inseparable: an `ℕ`-tower of free algebras `AdjoinRoots p l` over relative `p`-bases,
    then a sequential colimit.

  The result is then completed. SGA's transfinite induction is not needed.
- **In-scope IX.4.6 in SGA's form.** `SGA.SGA1.ExposeIX.isEffectiveIffStrictlyLocal :
  IsEffectiveIffStrictlyLocalStatement` (`SGA1/ExposeIX/StrictlyLocalDescentGeneral.lean`).
- **In-scope IX.2.6 sufficiency.** Unchanged since round 1: `universallySubmersiveValuativeCriterion`.
- **New row A60, claimed and finished this round: EGA IV 14.5.4 quasi-sections.**
  - `SGA.SGA1.ExposeIX.quasiSectionStatement : QuasiSectionStatement`, and therefore **IX.4.9
    unconditionally**: `SGA.SGA1.ExposeIX.effectiveDescentOfUniversallyOpenStatement :
    EffectiveDescentOfUniversallyOpenStatement` (`SGA1/ExposeIX/QuasiSection.lean`, 145 lines).
  - The algebra is in `Foundations/CommAlg/QuasiSection.lean` (406 lines):
    `Algebra.exists_quasiFiniteAt_quotient_of_isOpenMap`.

## What made A60 cheap

EGA IV 14 looked like a large development, but the proof needs only that `g` is open, plus
noetherian dimension theory that mathlib already has.

1. An open map from a noetherian sober space lifts generizations
   (`IsOpenMap.generalizingMap_of_noetherianSpace`). Hence going down, and
   `ht P = dim A + ht_fibre(P)`.
2. Lift a system of parameters `s` of the closed fibre at `P`.
3. Suppose no minimal prime of `(s)` below `P` met `A` in `0`. A product `a ≠ 0` of nonzero
   elements of these intersections then lies in every prime between `(s)` and `P`. With a system
   of parameters `t` of `A/aA`, `P` is minimal over `tB + (s)`. So
   `dim A + n ≤ #t + #s ≤ dim A - 1 + n`, which is impossible.
4. `P/Q` is minimal and maximal over `𝔪(B/Q)`, so it is isolated in the closed fibre.
   `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber` finishes.

The useful mathlib names are now in `strategy.md`.

## For the coordinator

- **Barrels.**
  - Foundations: `SGA.Foundations.CommAlg.{KrullAkizuki, KrullAkizukiFinite, DominatingDVR,
    DominatingDVRLift, DominatingDVRGeneral, FlatResidueExtension,
    FlatResidueExtensionCompletion, FlatResidueExtensionFree, FlatResidueExtensionPBasis,
    FlatResidueExtensionColimit, FlatResidueExtensionRealize,
    FlatResidueExtensionTranscendental, FlatResidueExtensionSeparable,
    FlatResidueExtensionInseparable, FlatResidueExtensionGeneral, QuasiSection}`.
  - ExposeIX: `SGA.SGA1.ExposeIX.{SubmersiveValuative, StrictlyLocalDescentGeneral,
    QuasiSection}`.
  - `DominatingDVR.lean` imports semistable's `SGA.Foundations.Blowup.AffineAlgebra`, so commit
    the two together.
- **Tracked docstrings that now understate what is proved.**
  - `Submersive.lean`: the module docstring and `UniversallySubmersiveValuativeCriterionStatement`.
  - `EtaleEffectiveDescent.lean`: `IsEffectiveIffStrictlyLocalStatement` ("the general case
    needs … 10.3.1") and `EffectiveDescentOfUniversallyOpenStatement` ("the one step … not
    formalized").
  - `UniversallyOpenDescent.lean`: the module docstring, which says "which we do not have" about
    quasi-sections.
  - `docs/formalization.md`: the IX row, and the open-statements rows for IX.2.6, IX.4.6 and
    `QuasiSectionStatement`/IX.4.9, which are all proved now.
- **Duplication** (the reviewer's point, still open).
  - Lines 51–138 of `FlatResidueExtensionCompletion.lean` repeat the proof inside
    `IsLocalRing.StrictHenselization.isNoetherianRing` (tracked `HenselizationNoetherian.lean`).
  - To fix it:
    1. Move `Module.Flat.of_forall_flat_quotient_pow` and its helpers out of
       `HenselizationNoetherian.lean` into a new file, so that my completion file can import that
       file instead.
    2. Let `HenselizationNoetherian.lean` import `FlatResidueExtensionCompletion`.
    3. Prove its instance from `IsLocalRing.isNoetherianRing_adicCompletion_of_map_maximalIdeal_eq`
       and `StrictHenselization.map_maximalIdeal`.

## Unowned in-scope items I looked at (proposals for round 3)

- **IX.6.5 `LocalProperDescentStatement`.** This is the natural next item for this stream if you
  agree. Route (IX.6.6):
  - Over `S` noetherian, take the Stein factorization `X' → S' → S` (`steinFactorizationStatement`).
    Base change it to `Ŝ = Spec 𝒪̂_s`, which needs Stein factorization to commute with flat base
    change (`Foundations/Cohomology/FlatBaseChange.lean`).
  - Over `Ŝ`: `X'` is étale on its closed fibre, hence étale everywhere (proper over a local
    base), hence finite étale. It lies in the essential image by
    `mem_essImage_iff_isGeometricallyTrivial_closedFibre`, so `S'` is étale at `s'` and
    `X' ≅ X ×_S S'` there.
  - Come back from `Ô_{s'}` by faithfully flat descent of "iso" and "étale". Spread out with
    ega4-8's 8.10.5 for isomorphisms.
  - Reduce to a noetherian base with ega4-8's EGA IV 8.
  - Hard-parts says "several thousand lines". The complete-local core is maybe 300 lines. The
    flat base change of the Stein factorization and the descent steps are the bulk.
- **`GrothendieckExistenceStatement` for proper non-projective `X`** (EGA III 5.1.4; hard-parts §1).
  It would give IX.1.10, X.2.1–X.2.4 for proper `X`. It is large, and it is not local algebra.
- **XIII.5.2 in mixed characteristic** (`AbsoluteAbhyankarStatement`, TAME-8: the `nᵢ` are
  prime to `p` over an `A` that is not strictly henselian). It is local algebra (ramification
  indices), and nobody owns it. Hard-parts §5 has a plan and estimates 1000+ lines.
