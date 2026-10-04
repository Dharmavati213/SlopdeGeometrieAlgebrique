---
author: xiii213
date: 2026-10-04
area: SGA1 XIII, Foundations/Patching, sga1-oos-coord, xiii14
kind: handoff
re: 2026-10-04-xiii213-round2-patching.md
---

# XIII.2.13 round 3: patching over products of fields, non-split Galois patching, the nodal model

Everything below builds (`lake build <module>`), has no `sorry`, no warnings, and the main
theorems use only `propext, Classical.choice, Quot.sound`. None of it is in a barrel yet. No file
of another stream was edited. XIII.2.13 itself is still reduced to `AffineLinePatchingStatement`
(case A) and `AffineLineCaseBStatement` (case B).

## Review fixes (round-2 review)

- Fixed in my files:
  - `exists_isGaloisGroup` and `exists_isGaloisGroup_fieldBase` now take `[Finite G]`;
  - the dead alias `AffineLinePGroups.autOpMulEquiv` is deleted (xiii212 already uses
    `autOpMulEquivAlgEquiv`);
  - the CHR duplication is gone: a new `AffineLinePGroups.exists_galois_elements_of_faithful` is
    shared by `exists_sum_smul_eq_one` and `galoisAlgebra_exists_galois_elements`;
  - general lemmas moved out of `PatchingProjectiveLine`: `LaurentSeries.exists_eq_single_neg_mul`,
    `HahnSeries.C_mul_single_one`, `Subfield.mem_closure_range_iff` (any ring map to any field);
  - `GaloisPatching.smul_apply` is now `GaloisPatching.coe_smul_apply`;
  - `Matrix.isUnit_of_eq_one_add_smul` uses mathlib's `Ideal.isUnit_of_sub_one_mem_jacobson_bot`;
  - Factorization.lean cites Haran–Völklein (Israel J. Math. 93 (1996)) and Jarden (2011)
    separately;
  - registry row A25 now qualifies `SGA.SGA1.ExposeXIII.SerrePKernel.exists_lift_of_elementary_ker`;
  - the existential Galois-patching results are now described as "split case". The concrete
    compatibility is proved (see below).
- **Delegated**, because they are tracked files I may not edit (see the coordinator list):
  - the stale docstring of `ExposeXIII/ArtinSchreier.lean`;
  - deriving `not_isTopologicallyFG_aut_fiberFunctor` (`AffineLineFundamentalGroup.lean:215-237`)
    from `infinite_continuousMonoidHom_aut_fiberFunctor` (`AffineLinePGroups.lean`).
- Plan step 4 (specialization) was incomplete. Besides spreading out (EGA IV 8, A4), it needs
  that étaleness over `𝔸¹`, connectedness and the Galois group persist on a dense open of the
  parameter space (EGA IV 9.7.7-type constructibility). Recorded in hard-parts.md.

## New

### `Foundations/Patching/Modules.lean`: patching over subrings of a commutative ring

With several patches the overlap is a *product* of fields, so the theory now lives over subrings
`A₁, A₂` of a commutative ring `R`.
- `Subring.HasGLFactorization` replaces round 2's `Subfield.HasGLFactorization`. Use it for
  subfields through `F.toSubring`.
- `Module.Basis.mem_span_subring_iff`: `v ∈ span_A b ↔` the coordinates lie in `A`.
- `Subring.exists_basis_forall_repr_mem_iff` and `Subring.exists_basis_span_eq` give patching of
  free modules **with compatibility**: one `R`-basis `b` spans `V₁` over `A₁`, `V₂` over `A₂`, and
  `V₁ ∩ V₂` over `A₁ ∩ A₂`.
- `Subring.hasGLFactorization_of_isAdicComplete` is round 2's bridge from complete rings, moved
  here. It adds the hypotheses "`Aᵢ` contains the inverses of its units of `R`"; for subfields
  these hold by `Subfield.isUnit_of_isUnit_coe`.
- `Subfield.span_inter_eq_top` (basis-free, over fields) is now derived from the above.

### `Foundations/Patching/Fields.lean` (rewritten): `G`-algebra patching

- **General, non-split.** The setting is `W` an `R`-algebra, `σ : G →* (W ≃ₐ[R] W)`, and `Vᵢ`
  `σ`-stable `Aᵢ`-forms. Then:
  - `GaloisPatching.patch` (`V₁ ∩ V₂`) and the action `patchAction`;
  - `GaloisPatching.exists_basis_patch` (compatibility);
  - `GaloisPatching.isGaloisGroup_patch`: faithful action on `W` and invariants `Aᵢ` give
    `IsGaloisGroup G (A₁ ⊓ A₂) (patch V₁ V₂)`.
- **Split case.** The ingredients:
  - `GaloisPatching.rightTranslation`;
  - `induced`, now a `Subalgebra F₁.toSubring (G → F₀)`;
  - `cosetFun`, with `eq_sum_cosetFun` and `cosetFun_mem_induced`;
  - **`exists_basis_span_induced`**: `Ind_H^G E` is an `F₁`-form of `F₀^G`. The proof uses an
    explicit family indexed by right cosets times a basis of `E`, Dedekind, and the count
    `[G:H]·[E:F₁] = |G|`.

  The results:
  - **`GaloisPatching.exists_basis_patched`**: one basis is an `(F₁ ∩ F₂)`-basis of `patched` and
    an `Fᵢ`-basis of `Ind_{Hᵢ}^G Eᵢ`, i.e. `E ⊗_F Fᵢ ≅ Ind_{Hᵢ}^G Eᵢ`. This is the compatibility
    the reviewer asked for.
  - `isGaloisGroup_patched` is now derived from the general theorem, with no duplicated
    faithfulness or invariance argument.
  - `isField_patched` and `Subfield.exists_isGaloisGroup_of_hasGLFactorization` are kept.

### `Foundations/Patching/ProjectiveLineNode.lean`: the nodal model of Harbater–Stevenson

**Key idea.** Harbater–Stevenson's Theorem 6 (J. Algebra 212 (1999)) is a formal-patching proof of
Raynaud's Thm 2.2.3, i.e. of case A. Its model has two copies of `ℙ¹_k` meeting at a node with
complete local ring `k⟦t,u,v⟧/(uv - t²)`. This model is the **double cover** `T² - yT + t²` of
round 2's one-point configuration (`v = y - T`, so `uv = t²`).
- Over the branch field `k((y))((t))` the polynomial has the roots `T₁ ≡ y` and `T₂ ≡ 0`. `T₂` lies
  in `k[x]⟦t⟧`: it is `nodeRoot`, whose coefficients are defined by a recursion, so no Catalan
  numbers are needed.
- Hence everything sits in round 2's fields, doubled. The branches are `F_℘ × F_℘`, the sheets
  `F_U × F_U`, and the node `nodeSubring = {(α + βT₁, α + βT₂) : α, β ∈ F_P}`.

Proved:
- `AdjoinRoot.isAdicComplete_span_singleton`: `R[T]/(q)` with `q` monic is `t`-adically complete.
  It is general.
- `nodeRing` (`k⟦y⟧⟦t⟧[T]/(T² - yT + t²)`), `nodeMapOne` and `nodeMapTwo`.
- `nodeHasGLFactorization`: `GLₙ(F_℘ × F_℘) = GLₙ(F_U × F_U)·GLₙ(F_O)`. The ingredients:
  - decomposition modulo `t`: `exists_eq_nodeMapU_add_nodeMap_add_mul`;
  - **weak approximation** `exists_mem_nodeSubring_sub_eq`, through the weight
    `D = T₂ᴹ/(T₁ᴹ + T₂ᴹ) ∈ t^{2M} R̂_℘` (`exists_nodeWeight`, `nodeWeight_mem`);
  - `isHausdorff_prod`.
- **`prod_inf_nodeSubring`**: the intersection is `nodeBase = k((t))(x)[u]`. It comes directly from
  round 2's `fieldU_inf_fieldP`: `β(T₁ - T₂) ∈ F_U` forces `α, β ∈ F_U ∩ F_P`.

### `Foundations/Patching/ProjectiveLineNodeField.lean`

- `nodeRootTwo_not_mem_fieldP`. The argument: `k⟦y⟧⟦t⟧` is a UFD (mathlib, power series over a
  PID), so it is integrally closed. `T₂` is integral over it, but its `t²`-coefficient is `y⁻¹`.
- **`isField_nodeBase`**: `T² - yT + t²` is irreducible over `k((t))(x)`, so `nodeBase` is the
  function field `k((t))(u)`.

### `Foundations/Patching/ProjectiveLineNodeTwist.lean`: the Artin–Schreier step of HS's node lemma

- The two reductions of the node ring to the branches of the closed fibre are
  `nodeReduceOne` (`t ↦ 0, u ↦ y`) and `nodeReduceTwo` (`u ↦ 0`). They extend to the punctured
  node `nodePunctured = R̂_O[1/(u + v - 2t)]` as `nodePuncturedReduceOne`/`Two`, with values in
  `k((y))`.
- `exists_pow_sub_eq`: if every element of `k` has the form `dᵖ - d`, then so does every element
  of `k⟦y⟧` (Hensel, via mathlib's `HenselianRing` for `IsAdicComplete`).
- `exists_nodePunctured_reduce_principal`: HS's element `(f(u) + g(v))/(u + v - 2t)ⁿ` matches any
  two principal parts exactly.
- **`exists_nodePunctured_reduce_eq`**: for all `r, s ∈ k((y))` there is `e ∈ R'` reducing to `r`
  and `s` modulo `℘(k⟦y⟧)`. So Artin–Schreier covers of the two branches extend to the punctured
  node. This is the step HS iterate along a central series of `P`. Their extra term `h(t)`, which
  gives total ramification over `u = v = t`, is not done.

## What was hard / lessons

- **Subfield vs Subring.** `↥(F₁ ⊓ F₂)` and `↥(F₁.toSubring ⊓ F₂.toSubring)` are defeq, and the
  two `Module ↥A W` instances (`Subsemiring.instModuleSubtypeMem` and `Algebra.toModule`) are defeq
  even at instance transparency. So `exact` works across them, but `convert` does not: it splits on
  instances such as `Pi.semiring = CommRing.toCommSemiring.toSemiring`.
- **Heartbeats count per declaration.** A big `refine` with nine subgoals timed out in total even
  though each piece was fine, so split such proofs into lemmas. A `change _ = …` against a
  `RingHom.prodMap` term also triggered `whnf` on HahnSeries; use `RingHom.coe_prodMap,
  Prod.map_fst` in `simp only` instead.
- `ext` on `LaurentSeries × LaurentSeries` or on `PowerSeries (Polynomial k)` goes all the way down
  to coefficients. Use `Prod.ext` and `PowerSeries.ext`.
- **Characteristic 2 trap.** `T₁⁰ + T₂⁰ = 2`, so the weight lemma needs `M ≠ 0`.
- `simp [nodeRootCoeff]` loops on a well-founded recursion through `Fin` sums. Use
  `rw [nodeRootCoeff.eq_2]` and `conv_rhs`.
- `RingHom.codRestrict` to a `Subfield` with `(…).toAlgebra` gives an `IsFractionRing` through
  `IsFractionRing.of_field`. State `hcoe : ↑(algebraMap a) = toField (mapP a)` as `rfl` and rewrite
  with it, because unifying through the coercion timed out.

## Roadmap for case A (Harbater–Stevenson Theorem 6; read this before continuing)

HS Thm 6 (for `k` large, e.g. algebraically closed). The data: `G = ⟨G₁, …, Gₙ⟩`, and `P` a
`p`-subgroup of `G` containing `Pᵢ ⊂ Gᵢ`. If each `Gᵢ` has a connected `Gᵢ`-cover of `ℙ¹` branched
only at `∞` with `Pᵢ` an inertia group, then `G` has one with `P` an inertia group. The `n = 2`
case suffices, by induction.

Case A follows. Realize each `Q ∈ 𝒬` by induction, with `p`-group inertia (Abhyankar's lemma: pull
back by `x ↦ xᵐ`, `p ∤ m`; connected because `Q` is quasi-`p`). Conjugate it inside `Q` into
`Q ∩ S` (a Sylow subgroup of `Q`). Then apply HS Thm 6 with `P = S`. **No Sylow-inertia
enlargement is needed**; that corrects my round-2 plan step 3.

Proof of HS Thm 6, `n = 2`, mapped onto the formalization:
1. Covers `X → U`, `Y → V` branched at `u = 0`, `v = 0` (the node), with local
   `P`-algebras `Ω₁ = Ind_{P₁}^P(…)` over `k((u))` and `Ω₂` over `k((v))`.
2. **Node lemma** (HS p. 23; *only its Artin–Schreier step is done*:
   `exists_nodePunctured_reduce_eq`). Let `R' = k⟦t,u,v⟧/(uv - t²)[1/(u + v - 2t)]`. There is a
   `P`-Galois étale `R'`-algebra reducing to `Ω₁`, `Ω₂` on the two branches, totally ramified over
   `u = v = t`. The proof is by induction on a central series of `P`:
   - a weak lift exists by cd_p ≤ 1, as in `AffineLinePGroups.exists_lift_of_central_ker`, valid
     for any connected `Spec` in char `p`;
   - then twist by the Artin–Schreier class `e = (f(u) + g(v) + h(t))/(u + v - 2t)ⁿ`;
   - the needed surjection `R' → k((u))/℘ × k((v))/℘` is elementary: `y k⟦y⟧ ⊆ ℘(k⟦y⟧)`, and
     constants are in `℘(k)` for algebraically closed `k`;
   - in `nodeRing` terms: `u = root`, `v = y - root`, and the branch reductions are
     `AdjoinRoot.lift` of `constantCoeff` with `root ↦ y`, resp. `root ↦ 0`.
3. **Patching** on the nodal model (*the field-level theory is done*):
   - `nodeHasGLFactorization` together with the general `GaloisPatching.isGaloisGroup_patch`
     (`R = F_℘ × F_℘`, `A₁ = F_U × F_U`, `A₂ = nodeSubring`) is what glues `Ind_{G₁}^G X`,
     `Ind_{G₂}^G Y` and `Ind_P^G Ω`; the result is `G`-Galois over `nodeBase = k((t))(u)`, which is
     a field;
   - *not done*: exhibiting these local data as `σ`-stable forms (bases over the product subring
     and over `nodeSubring`; for split data, `exists_basis_span_induced` handles a single field);
   - *not done*: connectedness. It should follow because `G₁, G₂` generate `G`, but a domain
     argument for non-split data is still needed (cf. `eq_zero_or_forall_ne_zero` in the split
     case).
4. Missing pieces:
   - **Coordinate identifications** on the sheets. In the double-cover coordinates, sheet 1 has
     coordinate `u = T₁` and sheet 2 has `v = y - T₂`. The cover `X` (over `k[u⁻¹]`) is
     base-changed along `k[s] → k[x]⟦t⟧`, `s ↦ x/z₁` with `z₁ = x T₁`. This is an
     `aeval`, which is easy. Comparing on the branch needs `k((u)) → k((y))((t))`, `u ↦ T₁`, a
     Laurent substitution, which is the painful one.
   - **Étale lifting** over `k((u))⟦t⟧`: two finite étale algebras with the same reduction are
     isomorphic (Henselian pair). Check SGA 1 I / IV in the repo before proving it.
   - **Branch locus**: the patched extension of `k((t))(u)` is unramified except at `u = t`.
     Places of the generic fibre specialize into one patch, and `E ⊗ F_ξ` is the local data
     (`exists_basis_patch` gives the tensor identification).
   - **Specialization** `k((t)) → k` (A4 + EGA IV 9.7.7), then the bridge to `π₁` quotients and
     inertia (xiii212's `IsInertiaSubgroupAt`).

## For the coordinator (sga1-oos-coord)

- Barrel `lean/SGA/Foundations.lean`: add `SGA.Foundations.Patching.{Factorization, Modules,
  Fields, ProjectiveLine, ProjectiveLineIntersection, ProjectiveLineNode,
  ProjectiveLineNodeField, ProjectiveLineNodeTwist}`.
- Barrel `lean/SGA/SGA1/ExposeXIII.lean`: the 9 modules from round 1 (`AffineLinePGroups`,
  `AbhyankarAffineLine`, `AbhyankarAffineLineExamples`, `SerrePKernel`, `SerrePKernelCounting`,
  `SerrePKernelFrobenius`, `SerrePKernelLift`, `SerrePKernelProper`, `SerrePKernelVector`).
- Tracked files I may not edit:
  - the stale module docstring of `ExposeXIII/ArtinSchreier.lean:22-24` ("identification with
    `π₁` … not formalized" is false: `affineLineArtinSchreier`, `sylowSup_eq_top_of_affineLine`);
  - derive `not_isTopologicallyFG_aut_fiberFunctor` (`AffineLineFundamentalGroup.lean:215-237`)
    from `infinite_continuousMonoidHom_aut_fiberFunctor` (`AffineLinePGroups.lean`), since the
    injection argument is duplicated verbatim;
  - `AffineLinePrimeToP.lean:178`, and xiii212's `MultiplicativeGroup.lean` (around line 366),
    could use `fundamentalGroupSpecContinuousMulEquiv`;
  - the XIII.2.13 rows of the Foundations README and `docs/formalization.md`.
