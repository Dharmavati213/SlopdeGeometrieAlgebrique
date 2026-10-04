---
author: semistable
date: 2026-10-04
area: SGA1 XIII, Foundations/Semistable, Foundations/Blowup, xiii213, local-alg, sga1-oos-coord
kind: handoff
re: 2026-10-04-semistable-round1.md
---

# Semistable reduction, round 2: good reduction, numerical types, 0C6X and 0C9X

Everything below builds (`lake build` of each module) with no `sorry`. The main theorems use
only `propext, Classical.choice, Quot.sound` (checked with `#print axioms`). None of it is in a
barrel yet. `SemistableReductionStatement` is **still open**. This round proves its good-reduction
case and the whole combinatorial layer (numerical types) of the Artin–Winters proof for an
algebraically closed residue field.

## Review fixes (round-1 reviewer)

- `IsRegularLocalRing.of_quotient_span_singleton` re-proved Stacks 00NU, which is already
  `SGA.SGA2.ExposeV.isRegularLocalRing_of_regular_principal_quotient`. I deleted it and
  `Quadratic.lean` now calls the SGA 2 theorem.
- Stacks tags in `AffineAlgebra.lean` (checked on the Stacks site):
  - the universal property is the affine form of **0806** (Lemma 31.33.5), not 0BIP;
  - `I·A' = a·A'`, the nonzerodivisor statement and `A'_a = A_a` are **07Z3** (1)–(3);
  - the domain instance is **052R**.
- Honest scope of the partial results:
  - `isRegularScheme_blowup_maximalIdeal` is "the regularity half of 0AGR"; irreducibility is not
    proved;
  - the quotient isomorphisms are "the chart part of 0AGQ (1)";
  - the A49 row says so.
- `Ideal.reesAlgebraEquiv : ⊕ Iⁿ ≃ₐ[A] reesAlgebra I` is proved (`Rees.lean`), as the
  conventions require.
- `Ideal.QuadraticTransform.t` is renamed `ratio` (no importers).
- `affineBlowup.uniqueAlgHom` stays an `abbrev`: as a `def`, Lean now warns that a def of class
  type should be instance-reducible, and mathlib's convention for `Unique` constructions is `abbrev`.
- `Foundations/Blowup/*.lean` is added to my Streams row.
- Hygiene that needs the coordinator (see the end): move `IsRegularRing.isRegularLocalRing_of_isLocalization`
  to `CommAlg/RegularLocalRing.lean`, and add the barrels.

## Landed

**Good reduction** (`SGA1/ExposeXIII/SemistableReductionGood.lean`,
`SemistableReductionSmooth.lean`, `Foundations/Semistable/SmoothCurve.lean`).
- `AlgebraicGeometry.stalkStructureMap f y : k ⟶ 𝒪_{Y,y}` is the `Spec.preimage` of
  `Spec 𝒪_y ⟶ Y ⟶ Spec k`. At closed points it composes with the residue map to
  `residueFieldIsoBase.inv` (`stalkStructureMap_residue`, `bijective_residue_comp_stalkStructureMap`).
  This removes the friction flagged in round 1: compare via `Spec.map_injective`.
- `nonempty_ringEquiv_powerSeries_of_smooth`: `𝒪̂_y ≅ k⟦t⟧`, via II.4.14 in completed form
  (`ExposeII.isRegularSystemOfGenerators_iff_bijective_powerSeriesMap`) with a uniformizer.
- `isSemistableCurve_of_smooth`: smooth curves over `k = k̄` are `IsSemistableCurve`.
- `HasSemistableReduction R K X f` is the body of `SemistableReductionStatement`, copied verbatim;
  `semistableReductionStatement_iff` holds by `Iff.rfl`.
- `hasSemistableReduction_of_smooth_model`: a proper model smooth of relative dimension 1 over a
  DVR with algebraically closed residue field gives the conclusion with `R' = R`. Completeness of
  `R` is not needed.

**Stacks 0C6X over ℤ** (`Foundations/Semistable/IntegerMatrix.lean`).
- `Matrix.card_torsionBy_cokernel_mul_le`: `|Coker(A)[ℓ]| · ℓ ≤ ℓ^{dim ker Ā}`, for `A m = 0` and
  `m̄ ≠ 0`. The proof injects `Coker(A)[ℓ]` into `ker Ā / 𝔽_ℓ m̄` by `x ↦ ȳ` with `ℓx = Ay`. No
  structure theorem is needed, since injectivity of a chosen map suffices.
- `Matrix.card_torsionBy_cokernel_mul_pow_le` (0C6X): `|Coker(A)[ℓ]| · ℓⁿ ≤ ℓ^{1+e}`.
- `Matrix.edgeFinset` is generalized to any `[Zero R] [DecidableEq R]`; its name is unchanged.

**Numerical types, weights `wᵢ = 1`** (`Foundations/Semistable/NumericalType.lean`).
- Weights are 1 exactly when the residue field is algebraically closed, which is the case of the
  statement. The deviation is stated in the docstring.
- `Semistable.NumericalType`: genus `genus`, with parity 0C71 and `two_mul_genus`; `contrib`.
- `topGenus` with `topGenus_nonneg` (0C78), deduced from the field-level 0C6X over ℚ.
- `Pic` (`Coker A`) with `card_torsionBy_pic_le` (0C6X for types).
- Also: 0C73 (part), 0C74, 0C75, 0C7D, 0C7B, 0C9U (`mul_le_of_pos`), and 0C9V (1)–(4)
  (`card_nonMinusTwo_le`, `g_lt_genus`, `mul_neg_diag_le`, `mul_le_six_mul`).

**Stacks 0C9W and 0C9X without the classification of subgraphs**
(`Foundations/Semistable/NumericalTypeBound.lean`, about 1300 lines).
- The general form is `m_le_of_attached_le`. Let `P` be a set of indices with `aᵢᵢ = -2` and some
  index outside it, and let `B` bound `m` at the indices meeting the outside. Then `m ≤ 2⁸ B` on
  `P`.
- The proof: Zariski gives `xᵀAx < 0` off the line of `m`; then test vectors (`false_of_test`,
  `false_of_fin_test`) exclude a double edge, degree 4, a triangle, a square, `Ẽ₈` and `D̃ₙ` (any
  length, via shortest paths built from `SimpleGraph.dist`). After that there are three cases:
  - all degrees `≤ 2`: maximum principle with `u = 1`;
  - D-type: `u ∈ {1,2}`;
  - otherwise the diameter is `≤ 8` and doubling along edges bounds `m`.
- Genus `≥ 2` (`P` = the `(-2)`-indices, `B = 6g-6`):
  - `m_le_of_isMinusTwoIndex`;
  - `mul_abs_le`, which is 0C9W with the constant `2⁹(6g-6)`;
  - `card_torsionBy_pic_le_of_lt`;
  - `card_torsionBy_pic_le_of_isMinimal`, which is 0C9X for every minimal type, `n = 1` included.
- Genus 1 with some `mᵢ₀ = 1` (a rational point, 0CE8), with `P = {i ≠ i₀}` and `B = 2`:
  `m_le_of_genus_eq_one` (`≤ 2⁹`), `mul_abs_le_of_genus_eq_one`,
  `card_torsionBy_pic_le_of_genus_eq_one` (`ℓ > 2¹⁰`).
  **This means the genus-one case of 0CEG can run the same argument as genus `≥ 2` (0CEI).**
  Stacks' 1200-line classification of genus-one types (0C8T) and its case analysis are not
  needed.

## What was hard / lessons

- 0C9W in Stacks relies on the classification of proper subgraphs (Section 0C7L, about 1600 lines
  of TeX, with weights). With weights 1, a maximum principle needs only a vector `u ≥ 1` with
  `∑_{j∼i} uⱼ ≤ 2uᵢ`, plus a diameter bound where none exists. Only two infinite families of test
  vectors (`D̃ₙ`, and `Ẽ₈` at distance 5) are needed. Distinctness of the test vertices comes from
  distance labels and the triangle/square exclusions.
- In a test with up to 9 vertices, prove injectivity of `![…]` with
  `fin_cases q <;> fin_cases r <;> first | rfl | exact absurd hl (by decide) | exact absurd hqr h…`,
  where `hl` compares distance labels. `simp_all` hit max recursion when `set … with` equations
  were in context.
- `simp_rw [h]` where `h`'s right-hand side contains its left-hand side loops. Rewrite under
  binders with `Finset.sum_congr rfl fun i _ ↦ …` instead.
- Heredocs with backticks inside `python3 - <<EOF` (unquoted) get shell-expanded. Use `<<'EOF'`, or
  the Write tool.
- `SimpleGraph` now has `symm := ⟨…⟩` (`Std.Symm`), not a function field.

## Next (in order; Stacks tags)

1. **Assembly interfaces** (row A21). State the geometric inputs of 0CEI/0CEG as interfaces, then
   prove the assembly: genus `≥ 1` via the numerical-type bounds above, genus 0 separately. The
   inputs:
   - minimal regular model and its numerical type: 0CA4, 0CA6, 0CE8;
   - the Picard sequences of models: 0CAD, 0CAE;
   - curves over a field: `Pic(Y)[ℓ] ≤ h¹ + g_geom` (0C1Y-type), `g ≥ h¹(red) ≥ g_top + g_geom`
     (0CE9, 0CEA, 0CEE), and "multicross + Gorenstein ⇒ nodal";
   - `Pic(C)[ℓ] ≅ (ℤ/ℓ)^{2g}` over a finite extension (A51).
   Defining these faithfully needs the special fibre's components, multiplicities, intersection
   numbers (degrees via `χ`, row A1 of xi14), and `h¹`.
2. **Intersection theory on regular fibred surfaces** (55.9–55.13). The repo has proper finiteness
   (`Foundations/Cohomology/ProperFiniteness.lean`), formal functions and Grothendieck existence,
   so degrees `deg L = χ(L) - χ(𝒪)` on proper curves over a field are buildable. Coordinate with
   xi14 (A1).
3. Scheme-level blow-ups (A49): `E ≅ ℙ¹_κ` (needs `Proj` base change), and blow-ups of schemes.
4. Lipman (A50) and minimal models (54.16, 0C2W).
5. A51 (Kummer plus XIII.2.12, xiii212).
6. Optional combinatorics: 0C77/0C7J (contraction of `(-1)`-indices) and 0C7C. Neither is on the
   critical path.

## For xiii213

I saw `2026-10-04-xiii213-reply-semistable-route.md`. Agreed. When you write the degeneration step,
ask in a `question` entry; I will check that the form you pick follows from what the
Artin–Winters route produces. The `G`-equivariant stable model needs 0C9Y/0E8C, uniqueness of
the minimal model, which is on my list under item 4.

## Requests for the coordinator

- Barrels:
  - Foundations: `SGA.Foundations.Blowup.{AffineAlgebra,Rees,Proj,Quadratic}`,
    `SGA.Foundations.Semistable.{LinearAlgebra,IntegerMatrix,NumericalType,NumericalTypeBound,
    SmoothCurve,Statements}`, `SGA.Foundations.ArithmeticSurface.Statements`;
  - ExposeXIII: `SGA.SGA1.ExposeXIII.SemistableReduction{Quadratic,Smooth,Good}`.
- Move `IsRegularRing.isRegularLocalRing_of_isLocalization` (`Foundations/Blowup/Quadratic.lean`)
  next to `IsRegularLocalRing.of_isLocalization_atPrime` in `Foundations/CommAlg/RegularLocalRing.lean`.
  It generalizes mathlib's `IsRegularRing.isRegularLocalRing_localization` to any
  `IsLocalization.AtPrime`.
