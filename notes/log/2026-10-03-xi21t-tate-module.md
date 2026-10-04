---
author: xi21t
date: 2026-10-03
area: SGA1 XI, Foundations/GroupScheme, sga1-oos-coord
kind: handoff
---

# XI.2.1 in SGA's form: stated faithfully, proved in characteristic 0

Round 1 of stream `xi21t` (registry row A15). Everything below builds with `lake build`, has no
`sorry`, and `#print axioms` shows only propext, Classical.choice and Quot.sound.

**Result.** `exists_tateModule_equiv_of_charZero` (`lean/SGA/SGA1/ExposeXI/AbelianVarietyMulN.lean`):
let `A` be an abelian variety over an algebraically closed field of characteristic 0. Then the
canonical map `T(A) = lim_n K_n → π₁(A, 0)` is an isomorphism of topological groups. That is the
conclusion of the faithful statement `AbelianVarietyFundamentalGroupStatement` for such `A`.
Characteristic `p` is not covered: the `p`-part needs `p_A` to be an isogeny.

**New files**

- `SGA1/ExposeXI/AbelianVariety.lean`:
  - `isCommMonObj_of_smooth`: SGA's abelian varieties are commutative, from mathlib's
    `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed` plus
    `connectedSpace_pullback` (the critic's idea);
  - `torsionPoints` (`K_n`, discrete);
  - `tateModule` (compatible families, a subspace of `∏ K_n`).
- `SGA1/ExposeXI/TateModule.lean`:
  - `AbelianVarietyFundamentalGroupStatement`. It asks for `φ : T(A) ≃ₜ* π₁(A, 0)` such that
    `φ x` sends `g(0)` to `g(x_n)` for every lift `g` of `n_A` through every étale covering. That
    clause pins `φ` down (`tateModuleToFundamentalGroup_unique`); only SGA's ℓ-primary corollary
    is left unstated.
  - `exists_lift_of_forall_smul_eq_of_apply`, `exists_mulNLifts`: the lifting criterion and
    Serre–Lang, both in pointed form.
  - `tateModuleToFundamentalGroup`: the canonical continuous homomorphism, in every
    characteristic.
  - `tateModuleContinuousMulEquiv`: the isomorphism when every `n_A` is étale; the inverse reads
    `σ(0)` in the fibres of the coverings `n_A`.
  - `MulNEtaleStatement` and `abelianVarietyFundamentalGroup_of_charZero`.
- `SGA1/ExposeXI/AbelianVarietyMulN.lean`:
  - `etale_mulN` and `mulNEtaleStatement`: `n_A` is étale for `n` invertible in `k`.
  - The étaleness goes through I.9.11 (`ExposeI.etale_of_dominant_of_formallyUnramified`), which
    needs no flatness and no formal smoothness at the stalk level.
  - Unramified at `0`: `formallyUnramified_stalkMap_mulN_origin`. The residue-field separability
    comes from the `k`-structures via `Spec.map_inj`.
  - Unramified everywhere: `formallyUnramified_mulN`, using translations `τ_x ∘ n_A = n_A ∘ τ_{xⁿ}`
    and the Jacobson property.
  - Dominant: `isDominant_mulN`, because the map is injective on `𝒪_{A,0}`, so the generic point
    is fixed.
  - Normal: `isNormalScheme_of_smooth`.
- `Foundations/GroupScheme/MulNCotangent.lean` (mathlib-only imports):
  - `GroupScheme.powStalkEnd_sub_mem_sq`: `[n]^♯ t - n t ∈ 𝔪²` at the origin of any monoid scheme
    over any field.
  - This is the infinitesimal Eckmann–Hilton argument, using `k[ε]`-points instead of the local
    ring of `A ×ₖ A`. A `k ⊕ k²`-point restricts to `v`, `w` on the axes and to `v·w` on the
    diagonal (`tangentDeriv_mul`).
  - Points `Spec C ⟶ X` with `C` local are handled through `specPt`, the inverse of
    `SpecToEquivOfLocalRing`.
- `Foundations/GroupScheme/LocalEndomorphism.lean`: Nakayama and Krull intersection for a local
  endomorphism acting on `𝔪/𝔪²` by a unit, giving `φ(𝔪)R = 𝔪` and injectivity.

**What I avoided.** No rigidity and no theorem of the cube. In characteristic 0 nothing about
`A[n]` is needed beyond `n_A` being étale. The covering `n_A` itself realises `K_n` as its fibre,
which gives the inverse map. Finiteness comes from ZMT (`isFinite_mulN`).

**What was hard**

- Kernel deterministic timeouts on fibre points of `FEt.fiber`. Fixed with `irreducible_def fiberMk`
  (recorded in `strategy.md`).
- `(MorphismProperty.Over.mk …).left` is equal to `A.left` only after unfolding, so `rw` fails.
  Fix: typed wrapper defs (`mulNCoveringPoint`).
- Ring homs from stalks built inside `CommRingCat.ofHom {…}`: `simp` cannot apply `map_*` there
  (recorded in `strategy.md`).
- Dependent stalk types `stalk (f x)` versus `stalk x` when `f x = x`. Fix: state everything with
  `eqToHom ≫ stalkMap` (`stalkEnd`), and change points through `specPt_congr`.

**Next (round 2)**

1. Characteristic `p`. The `p`-part needs `A[p]` finite, i.e. `p_A` quasi-finite. That is genuine
   abelian-variety theory (theorem of the cube plus ampleness, or the dual abelian variety).
   Given `p_A` quasi-finite, the rest is reachable with repo tools:
   - quotient `A → A/K_{p^r}` (V.1.8 `isAdmissible_of_forall_exists_isAffineOpen`: translate an
     affine open so that it contains an orbit; V.2.3 trivial inertia gives étale);
   - the factor `A/K → A` is radicial, so topological invariance (IX.4.10) turns it into an étale
     covering of `A` with fibre `K_{p^r}`;
   - then the inverse map as in `tateModuleContinuousMulEquiv`.
   I would state the isogeny input as an interface `MulNQuasiFiniteStatement` and prove the
   conditional reduction.
2. A faithful prime-to-`p` statement in characteristic `p`: `π₁(A)` modulo its pro-`p` part, or
   the prime-to-`p` coverings. It follows from `etale_mulN` exactly as in characteristic 0.

**For the coordinator** (also in my result)

- Barrel entries for the five new modules.
- The `SerreLangStatement` docstring (Geometry.lean) and `SerreLang.lean` lines 33–34 should
  point to `AbelianVarietyFundamentalGroupStatement` as SGA's XI.2.1, proved in characteristic 0
  by `exists_tateModule_equiv_of_charZero`. The docs and README rows for XI.2.1 need the same
  update.
- Near-duplicate proofs: SerreLang's `exists_section_of_forall_smul_eq` and
  `exists_lift_of_forall_smul_eq` are special cases of my `…_of_apply` versions. Derive them from
  mine, or merge the two files, when Exposé XI is rebuilt anyway.
