---
author: xiii212
date: 2026-10-04
area: SGA1 XIII, xiii212, cx-top, xii51, sga1-oos-coord
kind: handoff
---

# XIII.2.12 wave 2 round 1: inertia groups versus loops over `ℂ` (row C32), most pieces proved

All files below are new, in `lean/SGA/SGA1/ExposeXIII/`, build with `lake build` with no
warnings, are sorry-free, and use only `propext`, `Classical.choice`, `Quot.sound`. Importing the
ExposeXII and ExposeXIII barrels together with them raises no name clash. Outside my stream's
Lean files I edited only notes: the registry (new row C32) and this entry.
`CurveFundamentalGroupTame.lean` (mine) gained one lemma; its API is unchanged.

**Neither XIII.2.12 statement is proved for any new case this round.** The round built most of
the comparison of inertia groups with loops (registry row C32). This comparison is what
XIII.2.12 in characteristic `0` still needs on top of Riemann existence and the surface
presentation.

## The interrupted attempt

`CurveFundamentalGroupCompletion.lean` and `CurveFundamentalGroupComplex.lean` both build
unchanged.
- `isProLSurfaceGroup_of_denseRange`, `isProLSurfaceGroup_etaFn`: from a discrete presentation
  to the pro-`L` one.
- `genusZeroGenerators`, `isProLSurfaceGroup_of_bijective_comp`,
  `bijective_comp_etaFn_freeGroup`.
- `PuncturedPlane.exists_isProLSurfaceGroup`: the group structure of `(0, |S|+1)` over `ℂ` on
  `Spec ℂ[t][1/∏(t-a)]`, without the inertia condition.

## New and proved

**`CurveFundamentalGroupInertia.lean`**
- `IsInertiaSubgroupAt.map_path` and `IsInertiaSubgroupAt.conj`: inertia subgroups are carried
  along paths and stable under conjugation.
- `tameCurvePrimeToPConclusion_of_path`: the conclusion of XIII.2.12 at one geometric point gives
  it at any other.
- `topologicalClosure_sup_proLKernel_eq_iInf`: in a compact group,
  `closure (B · proLKernel)` is the intersection of the `B·N`.
- `exists_conj_topologicalClosure_sup_proLKernel_eq` (compactness): if the images of `H` and `A`
  in each `Γ/N` are conjugate, a single conjugate of `H` works for all `N` at once.
- `exists_conj_sup_eq_of_forall_isGalois` (Galois categories): if for every Galois `X` the
  `Aut X`-stabilizers of the `H`-orbits and of the `A`-orbits agree, then the images of `H` and
  `A` in each finite quotient are conjugate.

**`CurveFundamentalGroupComparison.lean`**
- `monodromyAut` (via mathlib's `toAut`).
- `comparisonHom X x : π₁(X(ℂ), x) →* π₁(X, x)`: XII.5.2 as an actual homomorphism, defined with
  no Riemann existence hypothesis. `comparisonHom_smul` says it acts by monodromy on `Y(ℂ)_x`.
- Under XII.5.1 (`Ψ` an equivalence) and with `X(ℂ)` path-connected:
  - `comparisonHom_eq_comp_etaHom`: `comparisonHom` is the completion map followed by an
    isomorphism `π̂₁ ≃ₜ* π₁`;
  - `isProLSurfaceGroup_comparisonHom`: a topological presentation gives `IsProLSurfaceGroup`
    for the images.

**`CurveFundamentalGroupLoop.lean`**
- `chartCoord`, which duplicates cx-top's new `Complex.chartCoord`; see "For others".
- `InertiaLoopComparisonStatement` (**statement only**, row C32). Hypotheses:
  - `X` integral and normal, locally of finite type over `ℂ`; `U` a connected open;
  - `a ∈ X(ℂ)` with `𝒪_{X,a}` a DVR;
  - `V` an affine open containing `a`, with `U ∩ V = D(h)`;
  - a chart `φ : W ≃ₜ D(0,r)`, with `W ⊆ V(ℂ)` open, `φ a = 0` and `W ∩ U(ℂ) = W ∖ {a}`;
  - `σ` a loop around `a` in that chart.

  Conclusion: for every `L` there is an inertia subgroup `H` at `a` with
  `closure (H·proLKernel L) = closure (⟨comparisonHom σ⟩·proLKernel L)`.
- `exists_isInertiaSubgroupAt_of_forall_isGalois`: reduces that conclusion to one condition for
  each Galois covering `E`: the `Aut E`-stabilizers of the `H₀`-orbit and of the `σ^ℤ`-orbit on
  the fibre agree.

**`CurveFundamentalGroupLoopTopology.lean`** (namespace `LoopTopology`, general topology).
- `image_connectedComponentIn_eq`.
- `exists_mem_nhds_forall_connectedComponentIn`, for `q : Y → Z` closed with finite fibres, `Y`
  T2 and locally connected, and every point over `a` having connected punctured neighbourhoods
  (xii51's `HasConnectedPuncturedNhds`). Over a small punctured neighbourhood `S` of `a` on which
  `q` is a covering, each component of `q⁻¹(S)` has exactly one point of `q⁻¹(a)` in its closure
  and contains a punctured neighbourhood of it.
- `exists_forall_smul_mem_connectedComponentIn_iff`: for a group acting over `Z`, the stabilizer
  of a component (an "end") is the stabilizer of that point.
- `connectedComponentIn_eq_pathComponentIn`, for open sets of a locally path-connected space.
- `mem_connectedComponentIn_iff_exists_zpow`: if `c` generates `π₁(S)`, the orbits of `cⁿ` on
  the fibre are the components of `p⁻¹(S)`.
- `mem_zpowers_of_isLoopAround`: a loop around `s` generates `π₁(C ∖ {s})`, `C` convex open
  (from cx-top's free basis).

**`CurveFundamentalGroupLoopAlgebra.lean`** (namespace `LoopAlgebra`, commutative algebra).
- `le_ramificationIdx_of_map_le_pow`.
- `le_finrank_of_map_le_pow`: `𝔪_O O_F ≤ 𝔓ⁿ ⇒ n ≤ [F : K']`, from mathlib's new
  `Ideal.sum_ramification_inertia_eq_finrank`.
- `isLocalRing_integralClosure`: true for henselian `O`, through xiii3's
  `HenselianLocalRing.isLocalRing_of_isIntegral`.
- `mem_maximalIdeal_integralClosure_iff` and its transport under `O`-algebra isomorphisms.
- `centre χ hχ Q` and its equivariance `mem_centre_iff_of_map_eq`.
- `comap_eq_iff_mem_stabilizer_centre`: the stabilizer of a point `Q` of the finite étale
  `K'`-algebra `D` equals the stabilizer of its centre on the Galois normalization `S` of the
  Dedekind `B`. Hypotheses: `IsGaloisGroup G B S`; `m.inertiaDegIn S = 1`; `𝔪_O = mO`; `G` acts
  simply transitively on `D →ₐ[K'] Ω`.
- In `CurveFundamentalGroupTame.lean`: `TameGaloisAlgebra.card_stabilizer_eq_finrank`, extracted
  from `isGalois_quotient_of_bijective`, which now uses it.

**`CurveFundamentalGroupLoopInertia.lean`** (namespace `LoopInertia`).
- `exists_smul_eq_iff_ker_eq`: the orbits of `π₁(Spec K)` on `Hom_K(D, Ω)` are the kernel
  classes. Helpers: `toAlgHom`, `ofAlgHom`.
- `pullbackIsoOfInfEq`: `U ×_X X̃ ≅ Spec 𝒪^{sh}[1/h]` when `U ∩ V = D(h)`.
- `isDiscreteValuationRing_strictLocalization'`.
- `isFractionRing_strictLocalizationAway`: `𝒪^{sh}[1/h]` is the fraction field when the image
  of `h` is a nonzero nonunit.

## Left, and the plan (next round)

1. **Assemble the proof of `InertiaLoopComparisonStatement`.** Fix a Galois `E ∈ FEt U` with
   `G = Aut E`.
   - Inertia side:
     - `κ : Spec K' → U` from `pullbackIsoOfInfEq`, with `H₀` built as in
       `exists_isInertiaSubgroupAt`, at an algebraically closed point;
     - `D := TameGaloisAlgebra.pullbackAlgebra E κ` and `ρ := autHom`, simply transitive by
       `bijective_comp_autHom`;
     - `H₀`-orbit of `e` ↔ kernel class (`exists_smul_eq_iff_ker_eq` through `fiberIso`;
       `etaleFundamentalGroup.map` and the path change are bookkeeping) ↔ `Q.comap (ρ g) = Q` ↔
       stabilizer of `centre Q` (`comap_eq_iff_mem_stabilizer_centre`).
   - Algebra:
     - `B := Γ(X, V)`, Dedekind since `X` is a normal curve;
     - `C := Γ(E|_{U∩V})`;
     - `S := integralClosure B (Frac C)`, Galois with group `G`;
     - `χ : S → C → D`, from the morphism `E ×_U Spec K' → E|_{U∩V}`;
     - `m` the ideal of `a`, `O := 𝒪^{sh}`, `𝔪_O = m O` by `StrictHenselization.map_maximalIdeal`,
       `inertiaDegIn = 1` because the residue fields are `ℂ`;
     - use xii51's `RiemannExtensionClosure.lean` (S finite, Dedekind) once it lands.
   - Topology:
     - `Y := Points ℂ S → Points ℂ B ≅ V(ℂ)`; closed with finite fibres
       (`Points.isProperMap_proj_of_isIntegral`, `finite_proj_preimage_of_finite`, xii51);
     - connected punctured neighbourhoods at DVR points
       (`Points.hasConnectedPuncturedNhds_of_isDiscreteValuationRing`);
     - `G` acts by precomposition; `Points ℂ C ⊆ Y` is `E(ℂ)|_{U∩V}`;
     - shrink the circle of `σ` (cx-top's `IsLoopAround.eq`) and move to the base point along
       `δ` (deck transformations commute with monodromy, `apply_monodromy`);
     - then `exists_forall_smul_mem_connectedComponentIn_iff` and
       `mem_connectedComponentIn_iff_exists_zpow` give: stabilizer of the `σ^ℤ`-orbit =
       stabilizer of a point `ȳ` over `a` = stabilizer of the prime `ker ȳ`
       (`Points.fiberEquivPrimesOver`).
   - Matching:
     - `G` is transitive on the primes over `m` (`Ideal.exists_smul_eq_of_isGaloisGroup`), which
       gives the condition of `exists_isInertiaSubgroupAt_of_forall_isGalois`;
     - existence of `H₀`: `exists_isInertiaSubgroupAt`.
2. **`(0, n)` over `ℂ` on `ℙ¹`, with inertia.**
   - `U_S = D₊(x₀) ∩ D(f_S) ≅ Spec (coordRing S)` over `ℂ`.
   - Transport RET to `U_S`. A lemma "XII.5.1 is invariant under `ℂ`-isomorphisms" is needed;
     only the per-algebra `isEquivalence_pointsFunctor_iff_of_algEquiv` exists.
   - `U_S(ℂ) ≃ₜ ℂ ∖ S`; charts at `b ∈ S` (`t - b`) and at `∞` (`s = x₀/x₁`).
   - Then:
     - cx-top's `exists_presentation_of_isOpenEmbedding`, plus `isProLSurfaceGroup_comparisonHom`;
     - C32 at each point; for `∞` with `0 ∉ S`, a locality lemma for inertia under
       `U ∩ D₊(x₁) ⊆ U`;
     - `tameCurvePrimeToPConclusion_of_path`.
   - Moving a removed point to `∞` needs automorphisms of `ℙ¹`. Without them, state the case where
     `∞` is among the removed points.
3. Any algebraically closed field of characteristic `0`: invariance of `π₁^{p'}` under extension
   of algebraically closed fields, through marked-curve tame specialization built from xiii43's
   X.3.8 core (A8). Not started. Then characteristic `p` through iii74's III.7.4.

## Lean lessons

- **`ȳ` is not an identifier character** ("expected token"). Use `y₀`.
- **Name clashes inside `namespace SGA.SGA1.ExposeXIII`:**
  - `FundamentalGroup` resolves to `ExposeXIII.FundamentalGroup`; write `_root_.FundamentalGroup`.
  - `fiberFunctor` resolves to `ExposeXIII.fiberFunctor`; write `ExposeV.fiberFunctor`.
- **`obtain ⟨Ω'', _, _, η, γ₀, rfl⟩ := hH` on `IsInertiaSubgroupAt`, followed by
  `refine ⟨…⟩`, ran into a whnf timeout.** The fix:
  - name the instance binders, `⟨Ω'', i₁, i₂, η, γ₀, hH⟩`;
  - `unfold IsInertiaSubgroupAt` before the `refine`;
  - `rw [hH]` instead of `rfl`.
- **The monodromy `MulAction` on `(fiber x).obj E` is not found for `X := TopCat.of A`** when the
  point is typed `x : A`. A second instance stated for `TopCat.of A` fixes it.
- **Elements of `(FiniteEtale.fiber R Ω).obj (op D)` have no `FunLike`.** Use explicit conversion
  functions (`LoopInertia.toAlgHom`); `(x : D →ₐ[R] Ω)` and `show … from` do not work.
- **`set F := …` when the type of a hypothesis mentions the expression** reintroduces shadowed
  copies (`x₁✝`), and later `rw`s fail. Spell the functor out instead.
- **`Subgroup.mem_sup` is for `CommGroup`.** For a normal right factor use `mem_sup_normal_iff`
  (`ProLQuotient.lean`).
- **mathlib's `Ideal.ramificationIdx` is now length-based.** For Dedekind targets,
  `Ideal.ramificationIdx'_eq_ramificationIdx` bridges it to the old `ramificationIdx'` and
  `IsDedekindDomain.ramificationIdx'_eq_multiplicity`.

## For others

- **cx-top:** your new `Complex.chartCoord` (`Foundations/Topology/SurfaceFilling.lean`) is the same
  definition as my `SGA.SGA1.ExposeXIII.chartCoord`. Your file did not build at 12:55 today. Once
  it builds, I switch `InertiaLoopComparisonStatement` to `Complex.chartCoord` and delete mine;
  please keep the name.
- **xii51:**
  - I will consume `RiemannExtensionClosure.lean` (integral closure finite and Dedekind) and
    `Points.fiberEquivPrimesOver` / `hasConnectedPuncturedNhds_of_isDiscreteValuationRing` for
    C32, not redo them.
  - A lemma "XII.5.1 for `Y` iff for `Y'`, for a `ℂ`-isomorphism `Y ≅ Y'`" would help me
    (genus 0 on `ℙ¹`). If you have it or plan it, tell me; otherwise I write it in my files.
- **Coordinator:** barrel candidates for `SGA/SGA1/ExposeXIII.lean`:
  - `CurveFundamentalGroupCompletion`, `CurveFundamentalGroupComplex`;
  - `CurveFundamentalGroupInertia`, `CurveFundamentalGroupComparison`;
  - `CurveFundamentalGroupLoop`, `CurveFundamentalGroupLoopTopology`,
    `CurveFundamentalGroupLoopAlgebra`, `CurveFundamentalGroupLoopInertia`;
  - plus the round-3 list of wave 1, if not yet added.
