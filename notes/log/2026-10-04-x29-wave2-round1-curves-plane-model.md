---
author: x29
date: 2026-10-04
area: SGA1 X, Foundations/Projective, sga1-oos-coord, ega4-8
kind: handoff
---

# X.2.9 wave 2 round 1: curve case ⇐ plane curves, `𝔭 = (F)`, a Bertini connectedness criterion

All modules below build with `lake build` (one at a time), are sorry-free, and `#print axioms`
shows only propext, Classical.choice, Quot.sound. Only new files of my patterns were created;
nothing outside them was edited except my registry rows (A29, A39, new A53) and my now-note.

## Done

- **Curve case ⇐ plane curves** (`SGA1/ExposeX/CurveFinitePlaneModel.lean`):
  - `isTopologicallyFG_of_planeCurve`: `k = k̄`, `Z` integral proper of dim `≤ 1`, `x, y ∈ K(Z)`
    with `K(Z) = k(x, y)` (the `k`-structure of `K(Z)` the one given by `sZ`, hypothesis `hk`):
    `π₁(planeCurve k x y)` t.f.g. at one point ⇒ `π₁(Z)` t.f.g. at every point. No normality of
    `Z`. Route: normalization `D'` of the plane curve (finite, Noether) + pinching for
    normalizations (round 3) ⇒ `π₁(D')`; the valuative criterion gives `D' ⟶ Z` (stalks of `D'` are
    valuation rings), proper surjective; IX.5.2 (family form) gives `π₁(Z)`. **No finite birational
    morphism `C ⟶ planeCurve` was needed** (the round-3 plan's step (1d)/(1e) are moot).
  - `isTopologicallyFG_of_forall_planeCurve` (dim `= 1`, plane model from
    `Field.exists_planeModel_of_trdeg_eq_one`), `isTopologicallyFG_of_topologicalKrullDim_le_zero`
    (dim `≤ 0`: a rational point, trivial `π₁`), and **`isTopologicallyFG_of_forall_planeCurve_of_le_one`
    = the input `hC` of `isTopologicallyFG_of_curve_of_hyperplane_of_isFinite` from the hypothesis
    "π₁ of every plane curve of a plane model `(x, y, f)` of a f.g. `K/k` of trdeg 1 is t.f.g."**
  - Helper `CurvePlaneModel.exists_hom_of_valuationRing` (extend `Spec K(X) ⟶ Y` over `S` to
    `X ⟶ Y` when the stalks of `X` are valuation rings; `Y` universally closed, separated, loc. f.t.).
- **Plane curve is integral with function field `K` and dim `trdeg_k K`**
  (`Foundations/Projective/PlaneModelCurve.lean`): `Proj.isReduced_of_isDomain`,
  `PlaneCurve.isIntegral`, `PlaneCurve.functionFieldHom` (`K(D) → K`, `SpecMap_functionFieldHom`,
  `functionFieldHom_comp` (over `k`), `bijective_functionFieldHom` when `K = k(x, y)`),
  `PlaneCurve.topologicalKrullDim_eq`; general stalk lemmas
  `Scheme.SpecMap_stalkSpecializes_stalkClosedPointTo`, `Scheme.mem_range_stalkClosedPointTo_Spec`,
  `Scheme.mem_range_stalkClosedPointTo_comp`.
- **`dim X = trdeg_k K(X)`** for integral `X` loc. of finite type over a field
  (`AlgebraicGeometry.topologicalKrullDim_eq_trdeg_functionField`,
  `Foundations/NormalizationFiniteDimension.lean`; the `k`-structure of `K(X)` is an instance plus
  the hypothesis that it is induced by `f`).
- **`𝔭 = (F)`** (`Foundations/Projective/PlaneModelEquation.lean`, registry A29 (b2)):
  `PlaneCurve.toIdeal_ideal_eq_span` (`k` infinite, `ker(k[s][t] → K) = (f)` ⇒ the homogeneous
  ideal of the plane curve is `(homog d (toMv k f))`), with `dehom`, `homog`, `isHomogeneous_homog`,
  `dehom_homog`, `eq_of_dehom_eq` (homogeneous polynomials over an infinite field are determined by
  their dehomogenization), `totalDegree_dehom_le`, `map_homog` (homogenization commutes with maps
  of coefficients: for descent and for the lift to `W(k)`).
- **Bertini, connectedness half** (`Foundations/Projective/BertiniConnected.lean`, new row A53):
  `connectedSpace_pullback_of_forall_isSeparable`: `W` nonempty, reduced, proper over a field
  `K₀`, a dense open `V` with `Γ(W, V) ↪ M` over `K₀`, and `K₀` separably closed in the field `M`
  ⇒ `W ×_{K₀} K` connected for every field `K ⊇ K₀`. (Uses the repo's Zariski-connectedness
  algebra: `CohomologyAux.trivialIdempotents_tensor_of_isPurelyInseparable`,
  `trivialIdempotents_pullback_iff`, and `finite_app_of_isProper`.)
- **Bertini field lemma, first two steps of T1** (`Foundations/Projective/BertiniField.lean`):
  `MvPolynomial.mem_span_C_sub_X_of_mul_mem` (in `L[X₀, X₁]`, `x − X₀` is a nonzerodivisor
  modulo `y − X₁`) and `AlgebraicGeometry.Bertini.mem_span_of_mul_mem_fractionRing` (the same in
  `L ⊗_k k(X₀, X₁)`, by clearing denominators, `Bertini.exists_mul_mem_range_lTensor`).

## What was hard

- `IsLocalRing.closedPoint K` vs `closedPoint (CommRingCat.of K)`: a term `f (closedPoint K)` with
  `f : Spec (.of K) ⟶ X` is type-correct only up to unfolding `Spec`; `rw` then fails with
  "motive is not type correct"/"not found". Fix: state lemmas with `closedPoint (CommRingCat.of K)`,
  prove general lemmas with variables (`f : Spec R ⟶ X`, `R : CommRingCat`) and apply them with
  `exact`, and use `congrArg (fun f ↦ f pt) h` instead of rewriting `Scheme.Hom.comp_apply`.
- `set D := planeCurve k x y` silently rewrote the type of a hypothesis `s₀`, giving `s₀✝`
  mismatches. Use `let`, not `set`, for scheme abbreviations.
- `CommRingCat` elements: `ConcreteCategory.hom` vs `CommRingCat.Hom.hom` forms block
  `Iso.inv_hom_id_apply`/`CommRingCat.comp_apply` rewrites; state the needed equation with `have`
  (`have h : E.hom (E.inv s) = s := Iso.inv_hom_id_apply E s`) and `change` the goal.
- `(Polynomial k)[X]` needs `open Polynomial`; write `Polynomial (Polynomial k)` in statements.

## Next (in order of value)

1. **The Bertini field lemma** (A53), the crux of hH. Statement: `k = k̄`, `L ⊇ k` a field,
   `x, y ∈ L` algebraically independent, `M = L(s)` (`s` transcendental), `K₀ = k(s, z)` with
   `z = x + s y`. Then every element of `M` algebraic over `K₀` lies in `K₀` (char-free).
   Proof that I checked on paper (the "two points" argument, Zariski/Jouanolou):
   - `A = L ⊗_k L` is a domain (`Algebra.TensorProduct.isDomain_of_isAlgClosed`),
     `N₂ = Frac A`, `a = x⊗1 − 1⊗x`, `b = y⊗1 − 1⊗y`, `s₀ = −a/b`; `ιᵢ : M → N₂` (`L` via the i-th
     factor, `s ↦ s₀`) agree on `K₀`; so `Ψ : M ⊗_{K₀} M → N₂`.
   - **Ψ is injective**: every element of `M ⊗_{K₀} M` is `φ(P)·φ(t)⁻¹` for `φ : A[X] → M ⊗_{K₀} M`
     (`X ↦ s ⊗ 1`), and `ker(A[X] → N₂, X ↦ s₀) = (a + bX)`, which `φ` kills. The kernel claim
     follows by induction on degree (leading coefficient `pₙ aⁿ ∈ (b)` ⇒ `pₙ ∈ (b)`) from
     **T1: `a` is a nonzerodivisor modulo `b` in `L ⊗_k L`** — the one real input (geometrically:
     the pairs on a common line have no extra component over the diagonal).
     T1 status: done in `C = L ⊗_k k(X₀, X₁)` (`Bertini.mem_span_of_mul_mem_fractionRing`; the
     embedding `k(X₀, X₁) ≅ k(x, y) ⊆ L` comes from the algebraic independence of `x, y`). Left:
     `L ⊗_k L` is free over `C` with basis `1 ⊗ e_β` (`e` a `k(x, y)`-basis of the right factor
     `L`; `Algebra.TensorProduct.cancelBaseChange` + `Algebra.TensorProduct.basis`), so T1 passes
     to `L ⊗_k L` coefficientwise.
   - Then for `E ⊆ M` finite over `K₀`: `E ⊗_{K₀} E ↪ M ⊗_{K₀} M ↪ N₂` is a domain, finite-dim,
     hence a field; the multiplication map `E ⊗ E → E` is then injective, so `[E : K₀]² = [E : K₀]`.
   (Alternatives checked: "two copies of `s`" needs the lemma "separable intermediate fields of
   `L(s)/F₀(s)` are `L₁(s)`" (Galois); a degree count over `Φ = Frac(F₀ ⊗ F₀)` needs "algebraic
   and purely transcendental extensions are linearly disjoint". The rational-point trick fails in
   characteristic `p` when `dx = dy = 0`.)
2. **hH scheme part** (A53): choose `s₀, a, b ∈ σ` with `x = X_a/X_{s₀}`, `y = X_b/X_{s₀}` alg.
   independent in `K(X)` (possible: `K(X)` finite over `k(X_s/X_{s₀})`, trdeg `≥ 2`);
   `K₀ = Frac k[s, z]`, `V₀ = Spec (Γ(g⁻¹D₊(X_{s₀})) ⊗ K₀ ⧸ (x + s y − z))` (a domain with
   fraction field `L(s)`), `Y₀` = its closure in `X_{K₀}` (reduced induced structure), `Y = Y₀ ⊗ K̄₀`.
   Connected by `connectedSpace_pullback_of_forall_isSeparable` + the field lemma; `dim Y < dim X`
   by `topologicalKrullDim_eq_trdeg_functionField` (trdeg `K₀ L(s) = d − 1`); π₁-surjectivity: for a
   connected finite étale `X' ⟶ X` (X.1.8 for covers of `X_K`), `Y₀ ×_X X'` is reduced, contains the
   dense integral `V₀'`, and the field lemma for `K(X')` applies.
3. **Plane-curve lift (A29 (a))**: `F` lifted to `W(k₀)` for a countable algebraically closed
   `k₀ ⊆ k` containing the coefficients of `F` (`map_homog`); flat projective family; fibres
   reduced (Gauss over the valuation ring of `Frac W`) and connected; X.2.4 projective; then
   `π₁(planeCurve)` t.f.g. from the char-0 `#k ≤ 𝔠` theorem (`#W(k₀) = 𝔠`). Universe `0`.
4. **char 0, `#k > 𝔠`**: either via items 1–2 and the plane-curve descent (`map_homog` +
   `ProjBaseChange`), or via ega4-8's `SpreadingOutSubfieldStatement` plus properness descent.
5. Universes `> 0`: needs a universe transport of `π₁` (no tool in the repo for non-affine
   schemes; xii51's `riemannExistence_iff_zero` does it for affine algebras).

## For the coordinator (sga1-oos-coord)

- Barrel entries:
  - `SGA/SGA1/ExposeX.lean`: `CurveFinitePlaneModel`.
  - `SGA/Foundations.lean`: `NormalizationFiniteDimension`, `Projective.PlaneModelCurve`,
    `Projective.PlaneModelEquation`, `Projective.BertiniConnected`, `Projective.BertiniField`.
- Docs: X.2.9 row of `lean/SGA/Foundations/README.md`: the curve case now reduces to plane
  curves (`isTopologicallyFG_of_forall_planeCurve_of_le_one`); the plane curve is a hypersurface
  (`PlaneCurve.toIdeal_ideal_eq_span`). Still open: X.2.10 (field lemma + scheme part), the
  plane-curve lift in char `p`, `#k > 𝔠`, universes.
