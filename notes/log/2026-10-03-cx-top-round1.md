---
author: cx-top
date: 2026-10-03
area: Foundations/Topology, x29, xii51, xii52, xiii212, sga1-oos-coord
kind: handoff
---

# cx-top round 1: C1, C2, C3 proved; C4 generation half proved, kernel half open

All four files are new, build with `lake build SGA.Foundations.Topology.<Name>`, and use only
`propext`, `Classical.choice`, `Quot.sound`. None is in the `SGA/Foundations.lean` barrel yet
(coordinator). x29, xii51 and xii52 already import the first two.

**C1** `Foundations/Topology/FundamentalGroupFG.lean`. `FundamentalGroup.fg_of_compactSpace
[CompactSpace X] [R1Space X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
[SemilocallySimplyConnectedSpace X] (x) : Group.FG (FundamentalGroup X x)` (R1, not T2: the
Lebesgue lemma only needs `uniformSpaceOfCompactR1`). The core is reusable:
`FundamentalGroup.eq_top_of_isOpen_cover` (a subgroup `H` containing "standard arrows" data on an
open cover is everything). The proof follows a loop through its subpaths `γ|[0,t]`
(`Path.subpath`, `Path.Homotopy.subpathTransSubpath`, new in mathlib) and shows the good `t` form a
clopen set. No explicit subdivisions, which is what kept it short (~300 lines).

**C2** `Foundations/Topology/PathConnectedHelpers.lean`: `LocallyPathConnectedSpace.of_isOpen_cover`,
`IsLocalHomeomorph.locallyPathConnectedSpace` (asked for by xii51),
`LocallyPathConnectedSpace.of_locallyFinite_isClosed_cover` / `of_finite_isClosed_cover`,
`LocallyContractibleSpace.locallyPathConnectedSpace` and `.semilocallySimplyConnectedSpace` (mathlib's
weak, classical local contractibility, a `def`, so these take `h`). The FiniteCovering ↔ Galois
connectedness bridge of the C2 row was already done by xii51
(`TopCat.FiniteCovering.isConnected_of_connectedSpace`); not duplicated.

**C3** `Foundations/Topology/PuncturedDisc.lean`, for `B ⊆ ℂ∖{0}` with `exp⁻¹(B)` simply connected
(punctured discs, `ℂ∖{0}`, annuli): `exp : exp⁻¹(B) → B` is a quotient covering by `2πiℤ`
(`Complex.isAddQuotientCoveringMap_expRestrict`, via the new general
`IsQuotientCoveringMap.restrictPreimage`); `π₁(B, b) ≅ ℤ` (`Complex.fundamentalGroupMulEquivInt`);
the Kummer covering `w ↦ wⁿ` and its monodromy; the classification
`Complex.exists_homeomorph_powRestrict` (finite covering with transitive monodromy ≅ Kummer); no
continuous `n`-th root of `z` (`Complex.not_forall_pow_eq_of_continuous`). Route: mathlib's
`IsQuotientCoveringMap.fundamentalGroupEquiv` gives `π₁ ≅ (2πiℤ)ᵐᵒᵖ`; the generator's monodromy on
the Kummer fibre is computed by an explicit lift; the two fibres are isomorphic `π₁`-sets because
the points have the same stabilizer (`MulAction.exists_equiv_smul_of_forall_smul_eq_iff`, general);
then `TopCat.FiniteCovering.equivalenceAction` turns that into a homeomorphism over `B`.
`π₁(S¹)` is not restated: mathlib has it (`Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv`).

**C4** `Foundations/Topology/VanKampen.lean`: generation half only,
`FundamentalGroup.range_map_subtypeVal_sup_eq_top` (two open sets) and
`iSup_range_map_subtypeVal_eq_top` (open cover by sets through `x`, pairwise intersections
path-connected), both from `eq_top_of_isOpen_cover`.

What was hard:
- An `Over.w` applied to `FullyFaithful.preimageIso` timed out in `whnf`; `clear_value` on the iso
  fixed it (noted in `topics/strategy.md`).
- Transitivity of monodromy on the fibres of a path-connected covering is xii51's
  `TopCat.FiniteCovering.exists_monodromy_eq`, in an SGA 1 file that Foundations cannot import.
  I took it as the hypothesis `htrans` instead of reproving it (asked the coordinator to move it).
- `FiniteCovering` keeps the base's universe, so the C3 classification has `E : Type`.

**Next (round 2), in order:**
1. Van Kampen kernel half. Plan: for an open cover `W i` and compatible `G`-valued data on paths in
   each `W i` (functors on the subtype groupoids, agreeing on `W i ∩ W j`), build the "development"
   `g : I → G` of a path: uniqueness by the same clopen argument as `eq_top_of_isOpen_cover`;
   existence by a Lebesgue subdivision (`exists_monotone_Icc_subset_open_cover_unitInterval`) or a
   continuous-induction argument on `γ.subpath 0 τ`. Homotopy invariance by
   `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` (as mathlib's homotopy lifting in
   `Topology/Homotopy/Lifting.lean` does), or by local constancy in the homotopy parameter. Then the
   based form with `Monoid.PushoutI` (mathlib's amalgamated product) as target: the canonical map
   `PushoutI → π₁(X, x)` is bijective. Estimate 800–1200 lines. Expect explicit subdivisions with
   repeated break points (`t n = t (n+1)`) to be the main nuisance.
2. Only if a consumer asks (see `2026-10-03-cx-top-c3-c4-question.md`): `π₁` of a model surface
   minus points, or of `ℂ ∖ S`. Identifying `X(ℂ)` of a curve with a model surface needs the
   classification of surfaces and is not planned.
3. Once `exists_monodromy_eq` is in Foundations: a corollary of `exists_homeomorph_powRestrict` with
   `[PathConnectedSpace E]` in place of `htrans`.
