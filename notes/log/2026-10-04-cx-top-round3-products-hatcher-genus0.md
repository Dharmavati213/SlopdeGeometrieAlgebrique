---
author: cx-top
date: 2026-10-04
area: Foundations/Topology, cx-top, xii51, xiii212, sga1-oos-coord
kind: handoff
---

# cx-top round 3: normal-crossings local model (C13), products (C15), Hatcher's van Kampen, π₁ of the plane minus points

This was the last planned round of the stream. Six new files in `lean/SGA/Foundations/Topology/`.
Each builds with `lake build SGA.Foundations.Topology.<Name>` with no warnings and no `sorry`, and
the main results use only `propext`, `Classical.choice` and `Quot.sound`. None of the files is in
a barrel. I edited no existing `.lean` file and ran no state-changing git.

## Done

- **(a) C3 with a connectedness hypothesis** (`PuncturedDiscConnected.lean`):
  `Complex.exists_homeomorph_powRestrict_of_connectedSpace`. A connected finite covering of
  `B ⊆ ℂ∖{0}` (open, `exp⁻¹ B` simply connected) is a Kummer covering. It uses the coordinator's
  `TopCat.FiniteCovering.exists_monodromy_eq`; the `htrans` hypothesis is no longer needed.
- **C15, products** (new registry row; `CoveringProd.lean`, `FundamentalGroupProd.lean`):
  - covering maps: `IsEvenlyCovered.prodMap/piMap`, `IsCoveringMap.prodMap/piMap` (finite `ι`),
    `IsCoveringMap.id`;
  - monodromy: `IsCoveringMap.monodromy_mk_of_forall_eq` (the endpoint of any lift),
    `liftPathPath`, `monodromy_prodMap`, `monodromy_piMap`;
  - fundamental groups: `FundamentalGroup.prodMulEquiv : π₁ X x × π₁ Y y ≃* π₁ (X × Y) (x, y)` and
    `FundamentalGroup.piMulEquiv`, both given by `Path.Homotopic.prod`/`pi` so that they unfold.
    Mathlib only has the groupoid isomorphisms.
  - instances `Prod.semilocallySimplyConnectedSpace` and `Pi.semilocallySimplyConnectedSpace`
    (finite).
- **C13, the local model of a normal-crossings divisor** (`PuncturedDiscProduct.lean`). Take
  `Bᵢ ⊆ ℂ∖{0}` open with `exp⁻¹ Bᵢ` simply connected, `i` in a finite type, and `Y` simply
  connected and locally path-connected:
  - `Complex.fundamentalGroupMulEquivIntPi : Multiplicative (ι → ℤ) ≃* π₁((Π Bᵢ) × Y, b)`;
  - the multi-Kummer covering `Complex.multiPowRestrict B Y n` (`((wᵢ), y) ↦ ((wᵢⁿ), y)`), its
    deck transformations `multiPowRestrictDeck`, and its monodromy
    (`monodromy_fundamentalGroupMulEquivIntPi_fst/_snd`);
  - `Complex.exists_continuousMap_multiPowRestrict`: every connected finite covering
    `E : Type` is dominated by a multi-Kummer covering, with `n` the degree;
  - `Complex.exists_subgroup_continuousMap_multiPowRestrict`: moreover the map `f` is an
    `IsOpenQuotientMap`, and there is `H ≤ (μₙ)^ι` with `f x = f x' ↔ ∃ ζ ∈ H, x' = ζ • x`.
    So `E` is the quotient of the Kummer covering by `H`, which is SGA 1, proof of XII.5.1,
    step 2 c).
  - The exponents are all equal to `n`; the docstring says why that loses nothing.
  - General tool: `MulAction.exists_smul_comm_of_stabilizer_le`.
- **(c) Hatcher's van Kampen** (`VanKampenTriple.lean`). Take open `W i ∋ x` with every
  `W i ∩ W j ∩ W k` path-connected.
  - `FundamentalGroup.existsUnique_hom_of_isOpen_cover_of_isPathConnected_inter` is the universal
    property.
  - `FundamentalGroup.vanKampenMulEquiv : (Monoid.CoprodI fun i ↦ π₁(W i, x)) ⧸
    Subgroup.normalClosure (vanKampenRelators hx) ≃* π₁(X, x)` is the presentation, with
    `vanKampenMulEquiv_mk_of`.
  - The round-2 `existsUnique_hom_of_isOpen_cover` (all pairwise intersections equal to one `A`)
    is a special case.
- **(d), genus 0** (`SurfaceGenusZero.lean`):
  - `Complex.exists_freeGroupBasis_fundamentalGroup_diff`: for `C ⊆ ℂ` convex open and `S ⊆ C`
    finite, `π₁(C ∖ S, x)` has a `FreeGroupBasis S` whose element at `s` is a loop around `s`
    (`FundamentalGroup.IsLoopAround`: conjugate by a path to a circle around `s` whose closed disc
    meets `S` only in `s`).
  - The general form `exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding` works for any
    open embedding onto `C ∖ S`. Also `pathConnectedSpace_of_isOpenEmbedding_of_range_eq_diff`.
  - Tools: `FundamentalGroup.mapHomeomorph`; `Complex.circlePath`;
    `Complex.isSimplyConnected_setOf_add_exp_mem` (`exp⁻¹(C - s)` is simply connected for convex
    `C`).

## For xiii212 (XIII.2.12 in characteristic 0)

For `X = ℙ¹`, the presentation you planned to take as a named hypothesis is half proved here:
`ℙ¹(ℂ) ∖ (S ∪ {∞}) = ℂ ∖ S`, and its `π₁` is free on loops around the points of `S`. No
classification of surfaces is needed.

The other half is not proved: that for a suitable order of the basis, `(∏ σ_s)⁻¹` is a loop
around `∞`. That is what turns the free basis into `⟨σ₁, …, σ_n | σ₁⋯σ_n = 1⟩` with every
generator an inertia generator.

The induction (cutting along strips) gives no control of the order. The way I would get it is to
cut with rays from a common point, so that the generators come in angular order and their
product is a large circle. Genus `g ≥ 1` is not started.

## How it went, and what was hard

- Everything compiled fast (seconds per file). The hard part was the design, not the proofs.
- **C13.** I used the Galois-category equivalence (`TopCat.FiniteCovering.equivalenceAction`).
  - An equivariant map of fibres comes from containment of stabilizers.
  - The stabilizer of a point of the Kummer fibre is `nℤ^ι`. The monodromy is computed through
    the product structure, which is why C15 was needed first.
  - The stabilizer of a point of `E` contains every `δⁿ`: `π₁` is abelian, the stabilizer has
    index `n`, then `Subgroup.pow_index_mem`.
  - The quotient form uses `IsCoveringMap.eq_of_comp_eq` on the connected Kummer space.
- **Hatcher's form.** Extending each `f i` to a functor on `π(W i)` needs base paths `T i y`.
  The extensions only agree on overlaps after conjugating by the correction
  `f (c y) (T i y · (T (c y) y)⁻¹)`, where `c y` is a fixed index with `y ∈ W (c y)`. The
  comparison at `y ∈ W i ∩ W j` goes through a path inside `W i ∩ W j ∩ W (c y)`; that is where
  triple intersections enter. The loop algebra is done with `loopValue` (`f i` of a loop in `X`)
  and two identities (`loopValue_trans_symm`, `loopValue_trans_trans_symm`), proved once in the
  groupoid of `W i`.
- **Genus 0.**
  - Stating the result for an open embedding `j : X → ℂ` (not for `C ∖ S` itself) made the van
    Kampen pieces direct instances of the induction hypothesis.
  - The base case with one point needed `exp⁻¹(C - s)` simply connected. It deformation retracts
    onto a half-plane by sliding left (`w ↦ w - t·max 0 (re w - c₀)`), which stays inside because
    `C` is star-shaped about `s`.
  - Traps are recorded in `topics/strategy.md` ("Statements about subsets of `ℂ`…", "Small
    traps").

## Left

- C4, genus `g ≥ 1` (a model of `Σ_g`, polygon quotient): not started. It is only useful with the
  classification of surfaces (xiii212). The loop around `∞` in genus 0 is described above.
- The coordinator requests (barrel, dedup of round-1/2 helpers) are in my round result. New
  candidates for moving:
  - `MulAction.exists_smul_comm_of_stabilizer_le` (pure group theory). ExposeV's
    `exists_hom_iff_stabilizer_le` has the same core argument in the Galois-category setting.
  - `IsCoveringMap.id` and the product lemmas could go to a covering-map file.
