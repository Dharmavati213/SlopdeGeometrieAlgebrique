---
author: xiii212
date: 2026-10-04
area: SGA1 XIII, xiii212, cx-top, xii51, sga1-oos-coord
kind: handoff
---

# XIII.2.12 wave 2 round 2: both halves of C32 proved; the assembly is left

**Neither XIII.2.12 statement gained a new proved case this round.** All new files are in
`lean/SGA/SGA1/ExposeXIII/`. Each builds with `lake build` and no warnings, is sorry-free, and uses
only `propext`, `Classical.choice`, `Quot.sound`. Importing the ExposeXII and ExposeXIII barrels
together with the new modules raises no name clash.

## Reviewer fixes (round 1)

- `InertiaLoopComparisonStatement` now uses cx-top's `Complex.chartCoord`. My
  `SGA.SGA1.ExposeXIII.chartCoord` and its two lemmas are deleted; they had no other users.
- `proLKernel_map_le` is deleted. Its uses now call `proLKernel_le_comap`.
- `isDomain_strictLocalization_of_isDiscreteValuationRing` and
  `isDiscreteValuationRing_strictLocalization_of_isDiscreteValuationRing` are the general
  versions, in namespace `SGA.SGA1.ExposeXIII`, file `MultiplicativeGroupInertiaChart.lean`.
  - The A¹-chart versions now call them.
  - The primed copies in `CurveFundamentalGroupLoopInertia.lean` are gone; they had no importers.
- Docstrings:
  - `comap_eq_iff_mem_stabilizer_centre` now lists every hypothesis.
  - `exists_smul_eq_iff_ker_eq` now says "a consequence of V.8.1".
- Not done:
  - moving `LoopAlgebra.isLocalRing_integralClosure` next to
    `HenselianLocalRing.isLocalRing_of_isIntegral` (that file belongs to xiii3; see "For others");
  - the optional refactor of `topologicalClosure_sup_proLKernel_eq_top`.

## New and proved

**`CurveFundamentalGroupLoopEnds.lean`**, the topological half of C32 (namespace `LoopTopology`).

- `image_connectedComponentIn_preimage` and `mem_connectedComponentIn_iff_of_isEmbedding`:
  embeddings carry connected components.
- `fundamentalGroupMulEquivOfPath_symm_apply` and `monodromy_zpow_conj`: the monodromy of
  `(δ c δ⁻¹)ⁿ` is `δ⁻¹ ∘ cⁿ ∘ δ`.
- `exists_forall_exists_monodromy_zpow_eq_smul_iff`. The setting:
  - a covering `p : E → U'` with `E` locally path-connected, and an open embedding `u : U' → X̂`;
  - a continuous closed map `q : Y → Z` with finite fibres, `Y` T2 and locally connected, and an
    open embedding `c : Z → X̂`;
  - a chart `φ : W ≃ₜ D(0,r)` with `W ⊆ c(Z)` open, `φ(c a) = 0` and `W ∩ u(U') = W ∖ {c a}`;
  - `q` is a covering over `c⁻¹W ∖ {a}`, and the points of `Y` over `a` have connected punctured
    neighbourhoods;
  - a space `P` with embeddings `ιE : P → E` and `ιY : P → Y` over `X̂`, whose ranges contain the
    parts over `W ∖ {c a}`;
  - a group `G` acting on `E`, `P` and `Y` compatibly, continuously on `E` and `Y`.

  Conclusion: for a loop `σ` around `a` in the coordinate `chartCoord φ ∘ u` and a point `e` over
  the base point, some `y₀ ∈ q⁻¹(a)` satisfies `(∃ n, σⁿ • e = g • e) ↔ g • y₀ = y₀` for all
  `g ∈ G`.

  Proof outline:
  - shrink the circle with `IsLoopAround.exists_radius_lt` into a disc lying in the
    neighbourhood `M` given by the ends lemma;
  - conjugate by `δ`, using `apply_monodromy` to commute deck transformations with monodromy;
  - the circle generates `π₁` of the punctured disc (`mem_zpowers_of_isLoopAround`), and its
    orbits are the components (`mem_connectedComponentIn_iff_exists_zpow`);
  - carry the components through `P`, then conclude with
    `exists_forall_smul_mem_connectedComponentIn_iff`.

**`CurveFundamentalGroupLoopOrbits.lean`**, the inertia half of C32 (namespace `LoopInertia`).

- Orbits along functors:
  - `autMap_smul` and `exists_mem_range_autMap_smul_eq_iff`: orbits of the image of `autMap H e`;
  - `surjective_autMap`, and `exists_smul_eq_iff_of_surjective_autWhiskerLeft` (via V.6.9,
    `surjective_autWhiskerLeft_tfae`).
- `exists_mem_map_conjAut_smul_eq_iff`: orbits are carried along paths.
- `exists_smul_eq_iff_ker_eq_of_isIso`. For `κ : Spec K ⟶ T` an isomorphism, the orbits of
  `π₁(T, η ≫ κ)` on `F(Y)` are the kernel classes of the geometric points of
  `pullbackAlgebra Y κ`. The proof uses V.6.9 for `FEt.pullback κ ⋙ specEquivalence.inverse`.
- `toAlgHom_fiberIso_map` (equivariance of `TameGaloisAlgebra.fiberIso`).
- `autHomPullback f κ E : Aut E →* Aut_K(D)`, with `D = pullbackAlgebra (f^* E) κ`; and
  `pointOfPath f κ η γ E e`, the geometric point of `D` attached to `e ∈ F(E)_ξ` through the path
  `γ`.
- **`exists_mem_map_smul_eq_iff_comap_eq`**. Let `H` be the image of `π₁(T, η ≫ κ) → π₁(U, ξ)`
  (`π₁(f)` followed by the path `γ`), which is exactly the shape of `IsInertiaSubgroupAt` when
  `T = U ×_X X̃`. Then `(∃ k ∈ H, k • e = g • e) ↔ (ker ψ_e).comap (ρ g⁻¹) = ker ψ_e`, where
  `ψ_e = pointOfPath …` and `ρ = autHomPullback`.
- `toAlgHom_fiberIso_pullbackFiberIso_map`, and **`bijective_comp_autHomPullback`**: for `E`
  Galois and `U` connected, `Aut E` acts simply transitively on `Hom_K(D, Ω)`. This is the
  hypothesis `hS` of `comap_eq_iff_mem_stabilizer_centre`.

**`CurveFundamentalGroupLoopGalois.lean`** (namespace `LoopAlgebra`).

- `isGaloisGroup_of_finrank_le`: a faithful action of a finite `G` on `L/K` by
  `K`-automorphisms with `[L:K] ≤ |G|` makes `G` a Galois group of `L/K`.
- `isGaloisGroup_integralClosure` gives `IsGaloisGroup G B (integralClosure B C)` under these
  hypotheses:
  - `B` and `C` are integrally closed domains, with `FaithfulSMul B C`;
  - the fraction fields satisfy `[L:K] < ∞`, and `[L:K] ≤ |G|`;
  - `G` acts faithfully by `B`-algebra automorphisms.

  This is not a duplicate of `Foundations/Ramification/IntegralClosure.isGaloisGroup`, which is
  for `Gal(M/K)` and the closure in a field.

**`CurveFundamentalGroupLoopBaseChange.lean`** (namespace `LoopInertia`). This is step 1 of the
plan below, in generic form.
- `algebraFunctor κ` and `algebraOf E κ`: the finite étale `R`-algebra of `E ×_U Spec R`, for any
  ring `R`.
- `autHomOf E κ`: the `Aut E`-action on it, definitionally `TameGaloisAlgebra.autHom` when `R` is
  a field.
- `algebraFunctorBaseChangeIso`: if `κ' = Spec R' ⟶ Spec R ⟶ U`, then `algebraFunctor κ ⋙
  baseChange R R' ≅ algebraFunctor κ'`. It comes from
  `AlgebraicGeometry.Scheme.FiniteEtale.baseChangeSpecIso`, the counits, `pullbackComp` (with its
  optional `fg`/`hfg` arguments) and `FullyFaithful.whiskeringRight … |>.preimageIso`.
- `baseChangeAlgEquiv : R' ⊗[R] C' ≃ₐ[R'] D'`, and `algebraMapOfBaseChange`, with lemmas `_algebraMap`
  and `_autHomOf` (equivariance).
- `algebraFunctorCompIso` and `compAlgEquiv`: the algebra along `κ ≫ f` versus that of
  `(f^* E) ×_T Spec R`, equivariantly (`compAlgEquiv_autHomOf`).
- **`algebraMapToPullback f κ κR hκ E`**. This is the map `C' → D` of the plan; it needs
  `hκ : κ ≫ f = Spec.map (R → R') ≫ κR`. Its lemmas are `_algebraMap` (scalars) and `_autHomOf`
  (equivariance with `autHomPullback`).

**`CurveFundamentalGroupLoop.lean`** (added): `exists_forall_iff_of_forall_iff_smul_eq`. It matches
the stabilizers of the `A`-orbit and of the `B`-orbit through a transitive `G`-set (the points of
the normalization over `a`). This is the group theory of the final assembly.

## Left for C32: the plan (next round)

Fix a Galois `E ∈ FEt U` with `G = Aut E`. Notation:
- `B = Γ(X, V)`, `m = ker a`;
- `T = pullback U.ι a.fromSpecStrictLocalization`, `i = LoopInertia.pullbackIsoOfInfEq : T ≅ Spec K'`
  with `K' = StrictLocalizationAway hxV h`;
- `κ = i.inv`, `f = pullback.fst`.

The inertia subgroup is built by us:
- `Ω' = AlgebraicClosure K'` and `η = Spec.map (algebraMap K' Ω')`;
- `H₀ = (map Ω' f (η ≫ κ)).range.map (conj γ)`, with `γ` from `etalePaths.nonempty`;
- `IsInertiaSubgroupAt` then holds by definition, with the point `η ≫ κ`.

1. **`C'` and `D ≅ C' ⊗ K'`.** The generic part is done (`CurveFundamentalGroupLoopBaseChange.lean`).
   Use `C' = algebraOf E κ_h` and `χ₀ = algebraMapToPullback`. What is left:
   - the factorization `hκ`;
   - `dim_{K'} D = [Frac C' : Frac B]`: from `baseChangeAlgEquiv`, and
     `Frac B ⊗_{B_h} C' = Frac C'` because `C'` is a domain finite over `B_h`.
   The old sub-steps:
   - `κ_h : Spec B_h ≅ D(h) ↪ U`, and
     `C' = ((ExposeV.specEquivalence (.of B_h)).inverse.obj ((FEt.pullback κ_h).obj E)).unop.obj`.
     `TameGaloisAlgebra.pullbackAlgebra` and `autHom` only use a field through a `variable`.
     Copy them for `CommRing` bases into my files, or ask for the generalization.
   - Prove `κ ≫ f = Spec.map (B_h → K') ≫ κ_h`, using `pullbackIso_inv_snd`-style lemmas and
     `fromSpecStrictLocalization_eq`.
   - Then `D ≅ C' ⊗_{B_h} K'`, as `K'`-algebras and natural in `E`, hence `Aut E`-equivariant.
     The pieces:
     - `AlgebraicGeometry.Scheme.FiniteEtale.baseChangeSpecIso`
       (`Foundations/Formal/FiniteEtaleSpec.lean`). Caution: that file has its own
       `finiteEtaleHom`/`specFunctor`; `FEt (Spec R)` and `(Spec R).FiniteEtale` agree only up to
       δ-unfolding of two copies of `finiteEtaleHom`;
     - the counit isos of `specEquivalence`;
     - `MorphismProperty.Over.pullbackComp` and `pullbackCongr`;
     - full faithfulness of `specFunctor`.
2. **`S` and its properties.**
   - `C'` is a domain: `RiemannExtension.isDomain_of_connectedSpace_of_etale`, because
     `E|_{D(h)}` is connected (E connected, normal, hence irreducible). `C'` is normal:
     `ExposeI.isIntegrallyClosed_of_etale`.
   - `S = integralClosure B C'`, with mathlib's `MulSemiringAction` on the closure.
   - `S` is finite, Dedekind and flat: `RiemannExtension.finite_integralClosure`,
     `isDedekindDomain_integralClosure`, `flat_integralClosure`.
   - `IsGaloisGroup G B S` comes from `isGaloisGroup_integralClosure`. Faithfulness and
     `|G| = dim D = rank C' = [L:K]` both come from step 1 and `bijective_comp_autHomPullback`.
   - **Risk:** `B` Dedekind needs `dim B = 1`. Argument: f.t. domains over a field are
     equidimensional, and one local ring is a DVR. Check mathlib for this; otherwise prove it by
     Noether normalization. The C32 statement is true as stated.
3. **The `comap_eq_iff_mem_stabilizer_centre` hypotheses.**
   - `O = a.strictLocalization`: henselian, DVR (`isDiscreteValuationRing_strictLocalization_of_…`),
     with `IsFractionRing O K'` (`isFractionRing_strictLocalizationAway`; needs `h(a) = 0` and
     `h ≠ 0` near `a`).
   - `𝔪_O = m O`: `StrictHenselization.map_maximalIdeal`, plus "the stalk is `B_m`".
   - `m.inertiaDegIn S = 1`: `Points.inertiaDeg_ker_eq_one`.
   - `χ : S → C' → C' ⊗ K' ≅ D`.
   - This gives hA: `g` maps `e₀` into its `H₀`-orbit iff `g` fixes `P₀ = centre(ker ψ_{e₀})`
     (apply the lemma to `g⁻¹`).
4. **Topological package.** Apply `exists_forall_exists_monodromy_zpow_eq_smul_iff` with:
   - `X̂ = X(ℂ)`, `U' = U(ℂ)`, `u = SchemePoints.map U.ι`;
   - `Z = Points ℂ B`, `c = SchemePoints.chart hV`;
   - `Y = Points ℂ S`, `q = Points.proj B S`: closed by `isProperMap_proj_of_isIntegral`, finite
     fibres by `finite_proj_preimage_of_finite`, punctured neighbourhoods by
     `hasConnectedPuncturedNhds_of_isDedekindDomain`, covering over `{h ≠ 0}` by transporting
     `Points.isCoveringMap_proj` for `C'/B_h`;
   - `P = Points ℂ C'`;
   - `ιY = Points.map (S → C')`, an open embedding onto `{h ≠ 0}` by
     `isOpenEmbedding_map_of_isLocalizationAway` and `isLocalization_away_integralClosure`;
   - `ιE`: the points of the open immersion `κ_h^* E → E`;
   - `G` acts on `E(ℂ)` by `SchemePoints.map g.hom.left` and on points by precomposition with
     `g⁻¹`.
   This gives hB: `g` maps `e'` into its `σ`-orbit iff `g` fixes `ker y₀`. On the way:
   - translate `F(E)_x ↔ E(ℂ)_x` and `comparisonHom σ ↔ monodromy` with `comparisonHom_smul`;
   - get the `Aut E`-equivariance from the naturality of `schemePointsFunctorCompFiberIso`.
5. **Assembly.**
   - Feed hA, hB and `exists_smul_eq_of_isGaloisGroup` (transitivity on `m.primesOver S`) into
     `exists_forall_iff_of_forall_iff_smul_eq`;
   - then `exists_isInertiaSubgroupAt_of_forall_isGalois`;
   - the commutation `k • g • e = g • k • e` is `mulAction_naturality`, and the `Aut E` action on
     fibres is mathlib's `autMulFiber`.

After C32, the next step is `(0, n)` over `ℂ` on `ℙ¹`, as in the round-1 plan:
- cx-top's genus-0 presentation `Complex.exists_presentation_fundamentalGroup_compl` (C17, now
  proved for every finite `T ⊆ ℙ¹(ℂ)`);
- `schemeCurveRiemannExistence` (xii51) for XII.5.1 on `U`;
- `isProLSurfaceGroup_comparisonHom`;
- C32 at each removed point.

Characteristic `0` over other fields, and characteristic `p`, are as before (A8, A43).

## Lean lessons

- **`X̂` is not an identifier** (`expected token`), like `ȳ`. Use `XC`.
- **`set z₁ := ⟨…⟩` when the type of an obtained path mentions that term** (`δ : Path x (κ ⟨…⟩)`)
  creates a shadowed `δ✝`, and the goal and hypotheses stop matching. Use `let` for such terms.
- **`(mk p : FundamentalGroup X x) ^ n` fails** ("HPow (Path.Homotopic.Quotient …)"). The ascription
  does not change the elaborated type. Use `FundamentalGroup.fromPath (mk p) ^ n`.
- **`fundamentalGroupMulEquivOfPath δ.symm γ = mk δ ⬝ γ ⬝ mk δ.symm`**: unfold with `Iso.conj_apply`,
  then `simp only [Path.Homotopic.Quotient.mk''_eq_mk, …isoEquivHom_symm_apply_inv/hom]`, then
  `← Groupoid.inv_eq_inv`. `Groupoid.inv (mk δ).symm` is `mk δ` by `mk_symm` and `Path.symm_symm`.
- **Inside `namespace SGA.SGA1.ExposeXIII…`, `fiberFunctor` resolves to ExposeXIII's.** Write
  `ExposeV.fiberFunctor`. With `open ExposeV`, `autHom` resolves to `ExposeV.autHom`; write
  `TameGaloisAlgebra.autHom`.
- **`surjective_autWhiskerLeft_tfae`** needs `[FiberFunctor (H ⋙ F')]`. Get it from
  `ExposeV.fiberFunctor_comp H _`. TFAE indices start at 1 (`.out 1 3`).
- **`exists_smul_eq_iff_of_surjective_autWhiskerLeft H e`** with `e : P ⋙ (inverse ⋙ F) ≅ _`: pass
  `(F := …)` explicitly so that `H ⋙ F` unifies.
- **Integral closure as a `Subalgebra`**: it already has `Algebra S L` (`Subalgebra.toAlgebra`) for
  any `C`-algebra `L`. A `let : Algebra S L := …` of your own creates an `SMul` diamond.
- **`IsCoveringMapOn.isCoveringMap_restrictPreimage`** takes the set explicitly. Call it with
  `(s := …) (hf := …)`.

## For others

- **Coordinator:**
  - barrel candidates for `SGA/SGA1/ExposeXIII.lean`: `CurveFundamentalGroupLoopEnds`,
    `CurveFundamentalGroupLoopOrbits`, `CurveFundamentalGroupLoopGalois`,
    `CurveFundamentalGroupLoopBaseChange`, plus the round-1 list
    (`Completion`, `Complex`, `Inertia`, `Comparison`, `Loop`, `LoopTopology`, `LoopAlgebra`,
    `LoopInertia`);
  - the reviewer suggested moving `LoopAlgebra.isLocalRing_integralClosure` (henselian `O`: the
    integral closure in a field is local) to `Foundations/Etale/LocalAcyclicityHenselian.lean`,
    next to `HenselianLocalRing.isLocalRing_of_isIntegral`. That file is xiii3's (stopped stream),
    so I cannot edit it. Move it if you want.
  - Duplication noticed, not mine: `ExposeV.finiteEtaleHom`/`ExposeV.specFunctor`
    (`SGA1/ExposeV/FiniteEtaleSpec.lean`) and `AlgebraicGeometry.finiteEtaleHom`/
    `Scheme.FiniteEtale.specFunctor` (`Foundations/Formal/{EtaleCovering,FiniteEtaleSpec}.lean`)
    are the same definitions twice.
- **cx-top:** the switch to `Complex.chartCoord` is done; thanks for keeping the name.
- **xii51:** I will use, without reproving, `RiemannExtensionClosure`, `Points.fiberEquivPrimesOver`,
  `Points.inertiaDeg_ker_eq_one`, `hasConnectedPuncturedNhds_of_isDedekindDomain` and
  `schemeCurveRiemannExistence`.
