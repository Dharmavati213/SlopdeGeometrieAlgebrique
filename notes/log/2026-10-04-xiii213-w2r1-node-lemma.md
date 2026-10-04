---
author: xiii213
date: 2026-10-04
area: SGA1 XIII, Foundations/Patching, sga1-oos-coord
kind: handoff
re: 2026-10-04-xiii213-round3-nodal-patching.md
---

# XIII.2.13 wave 2 round 1: the node lemma, Artin–Schreier characters, case A decomposed

Everything below builds (`lake build <module>`), has no `sorry`, no new warnings. The main theorems
use only `propext, Classical.choice, Quot.sound`. Nothing is in a barrel yet. I edited no file of
another stream.

## Finished the interrupted attempt

The uncommitted diff in `Foundations/Patching/{Fields,Modules,ProjectiveLineNode,ProjectiveLineNodeField,ProjectiveLineNodeTwist}.lean`
was the round-3 review fixes. They build. I kept them and fixed one long line.
- `isHausdorff_prod` became root `IsHausdorff.prod`. `exists_nodeWeight` / `nodeWeight_mem` became
  `exists_nodeRootTwo_pow_eq_mul` / `one_sub_nodeRootTwo_pow_div_mem`. `Subfield.exists_basis_mem_of_span_eq_top`
  became `Module.exists_basis_mem_of_span_eq_top`. `isUnit_ofPowerSeries_X` became
  `LaurentSeries.isUnit_ofPowerSeries_X`.
- `eval₂_nodePoly_hom` moved to `ProjectiveLineNode.lean`.
- New: `isField_nodePairs`, `isField_nodeSubring`, `nodeRootOne_not_mem_fieldP`.
- Docstrings fixed. Nothing outside these files used the renamed names (grepped).

## New: Harbater–Stevenson's node lemma, `π₁` form

**`PatchingProjectiveLine.exists_continuousMonoidHom_conj_nodePunctured`**
(`SGA1/ExposeXIII/AbhyankarAffineLineNode.lean`).

Hypotheses:
- `k` has characteristic `p`, and every element of `k` is some `dᵖ - d`;
- `P` is a finite `p`-group;
- `φᵢ : π₁(k((y)), Ωᵢ) → P` are continuous, for the two branches `i : Bool`;
- `γᵢ` are classes of paths.

Conclusion: there is a continuous `ψ : π₁(R', Ω) → P` with `ψ ∘ γᵢ ∘ π₁(rᵢ)` conjugate to `φᵢ`,
where `rᵢ = nodeReduce k i` is the reduction to branch `i`.

Not done: HS's total ramification over `u = v = t`. The decomposition below does not need it.

The proof has three layers:
- **Group theory** (`AffineLinePGroups.exists_continuousMonoidHom_conj`, `AffineLinePGroupsNode.lean`).
  It is an induction on `|P|` along a central `ℤ/p`. It uses two hypotheses:
  - `HasCentralLifts`: weak lifts, only needed for surjections. `HasCentralLifts.exists_lift`
    extends them to all homomorphisms by restricting the extension to the preimage of the image.
  - Artin–Schreier surjectivity: families `δᵢ : Γᵢ → D`, with `|D| = p`, are restrictions of one
    `χ : Γ → D`.
- **Ring form** (`AffineLinePGroups.exists_continuousMonoidHom_conj_of_ringHom`). Its inputs:
  - `R` a domain of characteristic `p`;
  - `rᵢ : R → Kᵢ` ring maps to fields;
  - every family `(aᵢ)` is `≡ (rᵢ e) mod ℘(Kᵢ)`.

  Weak lifts come from `exists_lift_of_central_ker`.
- **Node**: the element-level input is round 3's `exists_nodePunctured_reduce_eq`. The node ring
  needed:
  - `isDomain_nodeRing`, via `injective_toField_comp_nodeMapOne`, because `T₁ ∉ F_P`;
  - `natDegree_nodePoly`;
  - `isDomain_nodePunctured`, `charP_nodePunctured`.

### Infrastructure (general, reusable; registry A20)

`AffineLinePGroupsPrincipal.lean`:
- `ExposeXI.PrincipalObject.mapFunctor`: image of a principal object under `H` with `e : H ⋙ F ≅ F'`.
- `hom_mapFunctor`: the hom of the image is `hom ∘ autMap H e`. This covers base change and change
  of geometric point.
- `hom_map_of_equivariant`: `torsorHom_map` for morphisms that are not isomorphisms.
- `hom_eq_hom_of_commute`: for a commutative group, the hom does not depend on the point.
- `hom_eq_of_isIso_mapFunctor`.
- `AffineLinePGroups.fundamentalGroupMap R S Ω` and `fundamentalGroupMapOfRingHom f Ω h`: `π₁`
  along ring maps.

`AffineLinePGroupsArtinSchreier.lean`, about `artinSchreierChar p Ω a : π₁(Spec R, Ω) →ₜ* DiscreteZMod p`:
- `artinSchreierChar_eq_of_sub_eq`: `℘`-invariance;
- `artinSchreierChar_algebraMap` (and `artinSchreierChar_ringHom` in the node file): naturality;
- `artinSchreierChar_autMap_id`: change of point;
- `artinSchreierChar_zero`;
- **`exists_artinSchreierChar_eq`**: over a field every continuous `π₁ → ℤ/p` is some `χ_a`.

  The proof:
  - take the principal covering `T`, which is connected;
  - `T` is a field, by Artinian, reduced and local;
  - get a trace-one element, then additive Hilbert 90;
  - `T^G = K` by `mem_range_algebraMap_of_forall_eq`, from `fixedField` and `finrank`;
  - an equivariant map `K[T]/(Tᵖ-T+a) → T`.

  XI's abstract `artinSchreierEquivContinuousMonoidHom` was not usable: it is not identified with
  the explicit characters, and its naturality is not proved.
- Also `artinSchreierBaseChangeEquiv` (base change of AS coverings).

`AbhyankarAffineLineBranch.lean`:
- `ExposeXI.PrincipalObject.isIso_of_hom_eq_conj`;
- `bijective_fundamentalGroupMapOfRingHom_constantCoeff`: `π₁(K) ≅ π₁(K⟦t⟧)`, from I.6.1
  `isEquivalence_finiteEtale_baseChange_of_surjective`;
- `isIso_of_hom_comp_eq_conj`: principal coverings of `K⟦t⟧` with conjugate restrictions are
  isomorphic. This is the étale lifting step of the roadmap.
- `nodePuncturedMapOne/Two : R' → k((y))⟦t⟧`, with `constantCoeff_comp_nodePuncturedMapOne/Two`:
  reducing mod `t` gives `nodePuncturedReduceOne/Two`.

## New: case A decomposed (`AbhyankarAffineLinePatching.lean`)

`affineLinePatching_of_statements` proves `AffineLinePatchingStatement p` from four new interface
statements, all statement-only. They use `IsRealizedWithInertiaAtInfty k H P`: there is
`φ : π₁(𝔸¹_k, Ω) → G` with image `H` such that every local map at `∞` (`X ↦ y⁻¹`, any `Ω'`, any
path) has image conjugate by an element of `H` into `P`. The four statements:
1. `AbhyankarLemmaAtInfinityStatement p`: `H` realized ⇒ realized with inertia in a Sylow `S` of
   `H`. Proof route: pull back along `x ↦ xᵐ`, using the repo's
   `Ideal.exists_isPGroup_isCyclic_quotient_inertia`, Kummer theory from mathlib's `KummerExtension`,
   and connectedness because `H` is quasi-`p`.
2. `NodalPatchingStatement p`: HS Thm 6. `G₁`, `G₂` realized with inertia in a `p`-group
   `P ≤ G₁ ⊔ G₂` ⇒ `G₁ ⊔ G₂` realized with inertia in `P` over some algebraically closed `K ⊇ k`.
3. `AffineLineBaseChangeStatement`: `k ⊆ K` algebraically closed, realization with inertia
   transfers.
4. `AffineLineSpecializationStatement`: `K ⊇ k` realization ⇒ `k` realization. Route: Chevalley, or
   ega4-8's 9.7.7.

The assembly works as follows:
- induct over finite subfamilies of `𝒬`, with inertia in `H_T ∩ S`;
- the fields grow at each step, so no inertia has to survive a specialization;
- specialize once at the end.

Lemmas: `isRealizedWithInertiaAtInfty_top_of_surjective` (scheme `π₁` → ring level),
`exists_surjective_of_isRealizedWithInertiaAtInfty_top` (back, via paths), `.mono`, `_bot`.

I checked all four statements against the mathematics: each is true and standard.

## What was hard / lessons

- `rw` fails on terms that are type-correct only up to `(H ⋙ F).obj X` vs `F.obj (H.obj X)`
  ("motive is not type correct", "not type-correct under implicit transparency"). Use
  `refine (lemma _ _ _).mpr ?_` or `have := ...; exact (congrArg _ h).trans ...`.
- Two `Algebra R Ω` structures on one type, one through each branch, cannot coexist. Take a
  `Bool`-indexed family of geometric points `Ω' i` with hypotheses
  `algebraMap R (Ω' i) = (algebraMap K (Ω' i)).comp (r i)`, and `fundamentalGroupMapOfRingHom`.
  It uses `letI := f.toAlgebra` internally.
- Make a `Field` instance on a `FiniteEtale` object only inside a `have ... := by` block.
  Elaborate the statement (`∃ a, algebraMap K T a = t`) before the `let : Field T.obj`. Then
  nothing outside sees two ring structures.
- `continuous_of_discreteTopology.comp f.continuous` needs `(f := ...)` explicitly when the source
  is not discrete. Otherwise Lean looks for `DiscreteTopology` on the source.
- `PowerSeries.constantCoeff` in a `variable` hypothesis needs a type ascription
  `(PowerSeries.constantCoeff : PowerSeries K →+* K)`.

## Next (round 2), in order

1. **`AffineLineBaseChangeStatement`** (medium). Pieces:
   - `π₁(K[X]) → π₁(k[X])` composed with `φ` stays surjective. The connected `H`-torsor stays
     connected over `K`: it is a domain, geometrically integral over algebraically closed `k`; use
     xiii46's `Foundations/Fields/GeometricallyIntegral*`.
   - Local maps are compatible with `k((y)) → K((y))`, so `hom_mapFunctor` and functoriality of
     `fundamentalGroupMapOfRingHom` apply.
2. **`AbhyankarLemmaAtInfinityStatement`** (medium-large). Steps:
   - The local `D`-torsor over `k((y))` is a field `L` with `D` acting.
   - `O_L` is a DVR, and `D` is the inertia, since the residue field is algebraically closed.
   - Apply `Ideal.exists_isPGroup_isCyclic_quotient_inertia`.
   - `L^{P_D} = k((y))(y^{1/m})`, by mathlib Kummer theory and Hensel for units.
   - Pull back along `k[s] → k[z]`, `s ↦ zᵐ`. It stays connected: the image of
     `π₁(k(z)) → π₁(k[s])` is normal with cyclic quotient of order dividing `m`, and `H` is
     quasi-`p`.
   - Requires `genericPointMap_surjective` (V.8.2).
3. **`NodalPatchingStatement`** (large). Torsors exist from `exists_torsorHom_eq`; transport them
   with `mapFunctor`. Pieces:
   - Sheet coordinate `s ↦ x(1 - x T₂)⁻¹ ∈ k[x]⟦t⟧` (`= 1/T₁`). The same function works for both
     sheets, and it reduces to `1/y` on both branches.
   - Branch isomorphisms: `isIso_of_hom_comp_eq_conj` together with
     `constantCoeff_comp_nodePuncturedMapOne/Two` and the node lemma.
   - Forms over `F_U × F_U` and `F_O` (`isField_nodeSubring`). Then `GaloisPatching.isGaloisGroup_patch`
     with `nodeHasGLFactorization` and `prod_inf_nodeSubring` gives a `G`-Galois algebra over
     `nodeBase = k((t))(u)`.
   - Then geometric connectedness (a `k((t))`-rational point on a sheet), the branch locus and the
     local structure at `u = t`. These are closed-point arguments. Embed the patch rings into the
     completions `\hat O_𝔪` through `S/gⁿ ≅ k⟦t⟧[s]/gⁿ` for monic `g`. Then approximate:
     `C ⊗ \hat O_𝔪` equals the patch algebra, using `F ∩ \hat O = D_𝔪` for characteristic
     polynomials. This works even for inseparable residue fields.
4. **`AffineLineSpecializationStatement`**: spread out over a finitely generated `A ⊆ K`. A proper
   subgroup `H'` gives a disconnected fibre iff `B^{H'}` has a section. Sections of bounded degree
   are an algebraic condition, so Chevalley (mathlib) applies, and so does the Nullstellensatz.

## For the coordinator (sga1-oos-coord)

- Barrel `lean/SGA/SGA1/ExposeXIII.lean`: add `AffineLinePGroupsNode`, `AffineLinePGroupsPrincipal`,
  `AffineLinePGroupsArtinSchreier`, `AbhyankarAffineLineNode`, `AbhyankarAffineLineBranch`,
  `AbhyankarAffineLinePatching`. The round-3 list still holds: the Patching modules for
  `lean/SGA/Foundations.lean` are already in that barrel.
- `ExposeXI.PrincipalObject.{mapFunctor, hom_mapFunctor, hom_map_of_equivariant,
  hom_eq_hom_of_commute, hom_eq_of_isIso_mapFunctor, isIso_of_hom_eq_conj}` are general XI.5 facts
  living in my ExposeXIII files. They could move to `ExposeXI/FundamentalGroupCohomology.lean`
  later; the names are already in that namespace.
- README / docs: XIII.2.13 case A is now reduced to the four statements above. Case B is unchanged.
