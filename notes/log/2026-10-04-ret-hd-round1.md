---
author: ret-hd
date: 2026-10-04
area: SGA1 XII, ret-hd, xii51, cx-top, sga1-oos-coord
kind: handoff
---

# ret-hd round 1: XII.5.1 in dimension ≥ 2 — interfaces, descent, smooth reduction, d ≤ 1, topology

New stream (registry C20, plus C28–C30 added this round). Everything below builds with
`lake build SGA.SGA1.ExposeXII.<File>`, is sorry-free, has axioms `propext, Classical.choice,
Quot.sound` (checked with `#print axioms` on the main theorems), uses no `maxHeartbeats`, and
passes a clash check against the `ExposeXII` barrel, xii51's `RiemannExtensionTopology` and cx-top's
`CoveringProd`/`FundamentalGroupProd`. No file is in a barrel. All files are new, in
`lean/SGA/SGA1/ExposeXII/` (about 1950 lines).

## Why not Artin's elementary fibrations (the brief's plan)

The brief proposed SGA 4 XI 3 (good neighbourhoods) plus the homotopy exact sequences. The
diagram chase `π̂₁^top(F) → π̂₁^top(T) → π̂₁^top(W) → 1` over `π₁^et(F) → π₁^et(T) → π₁^et(W) → 1`
proves `π̂₁^top(T) ≅ π₁^et(T)` only if `ker(π₁^et(F) → π₁^et(T))` is controlled, i.e. the *étale*
sequence is exact on the left (and in the middle) for an elementary fibration `T → W` (a curve
fibration minus an étale divisor). That is XIII.4.4, third part
(`ExposeXIII.NormalCrossingsShortExactSequenceStatement`/`…HomotopyExactSequenceStatement`), which
needs XIII.2.9 / `R¹f_*`: out of scope by the user's decision. X.1.4 and the proved first part of
XIII.4.4 are for *proper* `f` and do not apply to open fibres. Topology alone does not give the
étale side: whatever one does, one must *construct algebraic covers of `T`* restricting to given
covers of a fibre, which is the content of the theorem. So I did not use elementary fibrations;
SGA 4 material is not needed for my route either.

## Route (this project's, not SGA's)

Statements in `RiemannHigher.lean` (namespace `SGA.SGA1.ExposeXII`):
`HypersurfaceComplementRiemannExistenceStatement d` (RET for `ℂ[x₁..x_d][1/f]`),
`DivisorExtensionStatement` (per covering: smooth `A`, `g` a nonzerodivisor, `E|_{D(g)}` algebraic
⇒ `E` algebraic), `SmoothRiemannExistenceStatement`, `TopologicallyUnibranchStatement` (normal
domain, every point has small open `V` with `V ∖ V(g)` connected), `RiemannExistenceFiniteDescentStatement`.

1. **Hypersurface complements, induction on `d`.** After a change of coordinates `f` is monic in
   the last variable; replace it by its squarefree part over `Frac R` (`R = ℂ[x₁..x_{d-1}]`),
   clear denominators: over `A = R_s`, `T = A[X]_{h}` with `h` monic separable is a dense basic
   open of `𝔸^d ∖ V(f)`, and its fibres over `W = Spec A` are `ℂ ∖ {roots of h_w}`.
   Given a covering `E` of `T(ℂ)`:
   - (a) each fibre `E_w` is algebraic (`riemannExistence_polynomial_away`, done);
   - (b) **parameter algebra** `Q_κ` over `A` (κ = degree bounds): variables for
     `P = Y^n + Σ_{i<n} c_i(X) Y^i` (`deg_X c_i ≤ M`), `G = X^r + Σ_{l<r} g_l X^l`, `U` (`deg ≤ rN`),
     relation ideal = coefficients of `U·h·Res_Y(P, P') - G^N`, then invert `disc_X(G)` (or
     `Res_X(G, G')`). Universal family: `T'_Q = Q[X]_G`, `𝒴 = T'_Q[Y]/(P)` finite étale
     (`SeparableCovering.finiteEtale`, `ExposeI.etale_adjoinRoot_of_separable`), and
     `A[X]_h → Q[X]_G` (h | G^N);
   - (c) the matching locus `Q^E = {q | 𝒴_q(ℂ) ≅ E|_{T'_q(ℂ)}}` is **clopen** in `Q(ℂ)`:
     `RiemannHigher.isClopen_setOf_fibreIso_polyComplement` (done) applied with `B = Points ℂ Q`
     (LPC: xii52's instance), `G_q` the specialized `G`, `p₁ = 𝒴(ℂ) → PolyComplement`,
     `p₂ = E` pulled back. Missing: the identification of `Points ℂ (Q[X]_G)` with
     `PolyComplement G` and of `Ψ(𝒴)` with a covering of it (cf. `PuncturedPlane.homeomorph`);
   - (d) clopen ⇒ idempotent `e` of `Q` (affine XII.2.4; scheme form
     `SchemePoints.exists_isClopen_preimage_pt_eq` in `RiemannFull.lean`);
   - (e) **Baire**: `W(ℂ) = ⋃_κ image(Q^E_κ)` (by (a) and primitive elements: for each `w`
     some `q` over `w`), so some `A → (Q_κ)_e` is injective (else every image lies in some
     `V(t)(ℂ)`, nowhere dense; `closureComparison` / identity theorem; `BaireSpace` from locally
     compact T2);
   - (f) **quasi-section**: `(Q_κ)_e ⊗ Frac A ≠ 0`, a maximal ideal with residue field `L` finite
     separable over `K = Frac A` (Zariski's lemma), `L = K(θ)`, `θ` integral, minimal polynomial
     `m ∈ A[T]` (A normal), clear the finitely many denominators: an `A`-algebra map
     `(Q_κ)_e → Z := A_t[T]/(m)`, `Z` finite étale over `A_t` (`disc m` inverted), `t ≠ 0`;
   - (g) the covering `J̃` of `T'_Z(ℂ)` of ordered fibre bijections `𝒴_x → E_x` (a clopen of the
     `n`-fold fibre power of `𝒴 ×_{T'} E`), its part `J̃'` of bijections that extend to isos over
     the whole fibre (clopen by `FibreIso`-type transport), which is **trivial on every fibre**;
     hence `J̃' ≅ π^*σ^*J̃'` for a continuous section `σ` (e.g. `x = 1 + Σ|g_l|`) — this
     "fibrewise trivial ⇒ comes from the base" lemma is the remaining topology (pieces in
     `RiemannHigherFibrewise.lean`; proof: KT `sliceHomeomorph` over contractible neighbourhoods
     of `Z(ℂ)` (finite étale over an open of `ℂ^{d-1}`, so balls) + `continuous_uncurry_sectionThrough`);
     then `σ^*J̃'` is algebraic by RET for `Z` (induction + `isEquivalence_pointsFunctor_of_finiteEtale`);
   - (h) over `J̃'^{alg}` the tautological bijection is continuous, so `E` pulled back is algebraic;
     restrict to a basic open of `T` over which `J̃'^{alg} → T` is finite étale surjective and
     descend (`riemannExistenceFiniteDescent`, done); then `DivisorExtensionStatement`.
2. **Divisor extension in dim ≥ 2** (mine; dim 1 is xii51's C26, agreed in
   `2026-10-04-xii51-reply-ret-hd-extension.md`): sheet counting at general points of `V(g)`.
   xii51 will generalize `RiemannExtension.exists_continuous_extension`/`injective_of_extension`
   (`RiemannExtensionTopology.lean`) to "dense open `U`, local connectedness of traces on `U`" at
   the start of their next round — **don't write a second one**. The algebra is there too:
   `RiemannExtension.isUnramifiedAt_of_finrank_le_card` (finite flat over a domain; apply at the
   DVR of a height-one prime). Missing: local connectedness of `V ∖ V(g)` near regular points in
   dim ≥ 2 (étale coordinates `Points.exists_isOpenEmbedding_isLocalHomeomorph_of_smooth`, and
   "a ball minus the zeros of a nonzero polynomial is connected" via complex lines), general
   points of `V(g)`, purity `ExposeX.purityCoverings` for codim ≥ 2.
3. **Smooth domains**: done (below). Non-domain smooth `A`: scheme locality
   (`RiemannLocal.mem_essImage_schemePointsFunctor`) with the basis of affine opens with domain
   sections (in a reduced noetherian ring with `A_𝔭` a domain, invert one element of each other
   minimal prime).
4. **Normal `X`**: needs `TopologicallyUnibranchStatement` (C30, mine; hard: Zariski's analytic
   irreducibility of normal points, i.e. ascent of normality to `𝒪^an`, plus local
   parametrization; or Artin approximation for factorizations of monic polynomials over `ℂ{x}`).
   Then: normalization `Ȳ` of `X` in a cover of the smooth locus, `#Ȳ_x ≥ n` by sheets, étale by
   counting over the henselization.
5. **All `X`**: descent along the normalization (done), at the scheme level, the normalization
   being a disjoint union of normal integral schemes (handle by scheme locality, not products).

## Done (files, main declarations)

- `RiemannHigherPullback.lean` (C28): `IsCoveringMap.pullbackFst`, `TopCat.FiniteCovering.baseChange`
  (renamed from `pullback` an hour after my question entry, clash with `Limits.pullback`),
  `baseChangeMk/Snd`, `baseChange_ext`.
- `RiemannHigher.lean`: the statements above; `RiemannHigher.pointsHom`, `restrictAway`.
- `RiemannHigherDescent.lean` (C29, scheme form):
  `RiemannHigher.mem_essImage_schemePointsFunctor_of_isFinite` (`g : X' ⟶ X` finite surjective
  over `ℂ`, `Scheme.{0}`, loc. finite type): descent datum from `exists_hom_map_eq`, axioms by
  `eq_of_forall_comp_eq`, effectiveness IX.4.12 (`isEffective_etaleCovering_of_isProper`),
  comparison through the quotient map `Y'(ℂ) → Y(ℂ)` (`isProperMap_map`).
- `RiemannHigherDescentAffine.lean`: **`riemannExistenceFiniteDescent :
  RiemannExistenceFiniteDescentStatement`**; `RiemannHigher.mem_essImage_pointsFunctor_iff`
  (affine vs scheme essential image), `baseChangeSpecIso`, `specMap`.
- `RiemannHigherSmooth.lean`: `exists_finiteEtale_hypersurfaceComplement` (domain `A`: `A_g` ≅ a
  finite étale algebra over `ℂ[x₁..x_s][1/r]`), `isEquivalence_pointsFunctor_of_isEquivalence_away`,
  **`isEquivalence_pointsFunctor_of_smooth_of_isDomain (hH : ∀ d, HypersurfaceComplement… d)
  (hD : DivisorExtensionStatement)`** (conditional on both).
- `RiemannHigherBase.lean`: `riemannExistence_polynomial_away` (RET for `ℂ[t][1/p]`, from
  `PuncturedPlane.riemannExistence_coordRing`), **`hypersurfaceComplementRiemannExistence_zero`,
  `…_one`** (unconditional), `RiemannHigher.isLocalization_away_of_dvd_pow`.
- `RiemannHigherProductCovering.lean`: `RiemannHigher.sliceHomeomorph` (covering of `B × F`,
  contraction of `B` ⇒ `≃ₜ B × slice`), `p_sliceHomeomorph`.
- `RiemannHigherIsotopy.lean`: tent-function isotopies, `famIsotopy` (homeomorphism of `ℂ` moving
  `s b₀` to `s b`, bijective by the contraction principle), `norm_famIsotopyInv_sub_le`,
  `isotopyTriv`, `isotopyTrivOn` (local triviality of `ℂ` minus moving points).
- `RiemannHigherTransport.lean`: `intervalSliceHomeomorph`, `fibreTransport`, `FibreIso`,
  `FibreIso.iff_of_path`, `FibreIso.iff_of_isPathConnected`, `isClopen_setOf_fibreIso`.
- `RiemannHigherPolyFamily.lean`: `exists_continuousOn_roots`,
  `exists_trivialization_polyComplement`, `isClopen_setOf_fibreIso_polyComplement`.
- `RiemannHigherFibrewise.lean`: `isOpen_range_of_section`, `section_eq_of_eq`,
  `IsSectionCovered`, `sectionThrough`, `continuous_uncurry_sectionThrough` (start of (g)).

## What was hard

- Deciding the route (above): the elementary-fibration plan hides the étale left exactness.
- Lean details are in `strategy.md` ("Covering-space bookkeeping", "Descent data for `Ψ` from
  topology", 2026-10-04, ret-hd). Most time went into subtype/`Θ ⟨p c, proof⟩` rewriting and
  implicit-argument `rw` failures; the descent itself went through with
  `exists_hom_map_eq` + `eq_of_forall_comp_eq` without fighting.

## Next (in order)

1. (g) "fibrewise trivial ⇒ pulled back from the base" over contractible neighbourhoods
   (`RiemannHigherFibrewise.lean`), then the covering `J̃'` of fibre bijections.
2. (b) the parameter algebra and the identification of its points with `PolyComplement`;
   (c)–(f); then assemble the induction step `HypersurfaceComplement… d → d + 1` conditional on
   `DivisorExtensionStatement`.
3. Divisor extension in dim ≥ 2 once xii51's generalized topological lemma lands.
4. Coordinates/squarefree reduction (mathlib `NoetherNormalization` has the monic-making
   automorphism, maybe private: check), non-domain smooth `A`.
5. C30 (unibranch) — the deepest remaining input; consider handing it to `an-coh` if they build
   normality of analytic local rings.

## For the coordinator

- Barrel candidates (`SGA/SGA1/ExposeXII.lean`): `RiemannHigher`, `RiemannHigherPullback`,
  `RiemannHigherDescent`, `RiemannHigherDescentAffine`, `RiemannHigherSmooth`, `RiemannHigherBase`,
  `RiemannHigherProductCovering`, `RiemannHigherIsotopy`, `RiemannHigherTransport`,
  `RiemannHigherPolyFamily`, `RiemannHigherFibrewise`. `RiemannHigherSmooth` imports
  `ExposeXIII.KunnethCurveOpen` (for `exists_finite_etale_away`), so ExposeXII then depends on
  ExposeXIII: move `exists_finite_etale_away` to Foundations if that matters.
- General topology in SGA1 files that could move to `Foundations/Topology`:
  `IsCoveringMap.pullbackFst`, `TopCat.FiniteCovering.baseChange`, `sliceHomeomorph`,
  the isotopy and transport files.
- Docs: XII.5.1 row of the Foundations README can add `riemannExistenceFiniteDescent` (XII.5.1
  2) a)) and `hypersurfaceComplementRiemannExistence_one`.
