---
author: xi14
date: 2026-10-04
area: SGA1 XI, Foundations/Cohomology, xi14, sga1-oos-coord, xiii212, xiii43
kind: handoff
---

# XI.1.4 (Serre) now depends only on Hodge symmetry: χ-multiplicativity proved

Round 2 of stream `xi14`. Everything below builds with `lake build <module>` and is sorry-free.
`#print axioms` shows only propext, Classical.choice and Quot.sound for each main theorem. I
edited only my own new files (and, in round-1 files of mine that nobody else imports, docstrings).

## Result

`SerreUnirationalSimplyConnectedStatement` (XI.1.4) is now proved from **one** hypothesis:
`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero (hH : HodgeSymmetryZeroStatement)`
(`SGA1/ExposeXI/SerreUnirational.lean`). The algebraic input `EulerCharFiniteEtaleStatement` is a
theorem now: `AlgebraicGeometry.eulerCharFiniteEtaleStatement`.

## What is proved this round

**`χ` is multiplicative in finite étale coverings**, any characteristic, no Riemann–Roch
(`Foundations/Cohomology/EulerCharacteristicFiniteEtaleProof.lean`):
- `Scheme.Modules.eulerChar_pullback_eq_mul d`: if `X` is proper over `k` and `π : Y ⟶ X` is
  finite étale with every `geometricFiberCard` equal to `d`, then `χ(Y, π^* F) = d · χ(X, F)` for
  every coherent `F`. The proof is by induction on `d`:
  - `d = 0`: `Y` is empty.
  - `eulerChar_pullback_pushforward_self`: `χ(Y, π^* π_* H) = d · χ(Y, H)`. Affine base change
    turns the left side into `χ(Y ×_X Y, p₁^* H)`. Split `Y ×_X Y = Δ ⊔ (Y ×_X Y ∖ Δ)`
    (`eulerChar_eq_add_of_isCompl`). The first projection of the complement has degree `d - 1`
    (`Scheme.Hom.geometricFiberCard_diagonalComplFst_add_one`, by symmetry from xiii14's
    `…diagonalComplSnd…`, through the restricted swap `Scheme.Hom.diagonalComplSwap`).
  - `eulerChar_pullback_eq_mul_of_isIntegral` (the integral case) and
    `eulerChar_pullback_eq_mul_of_pushforwardUnit` (the dévissage `prop_of_integral_step`, with
    the base change `Z ×_X Y ⟶ Z` for `ι_* G`).
- `eulerChar_eq_zero_of_isZero`, `isZero_of_forall_eq_zero`.

**Generic rank** (`Foundations/Cohomology/EulerCharacteristicGeneric.lean`, registry A24):
- `Module.exists_ne_zero_free_of_isLocalizedModule`: generic freeness in a form that transfers to
  any localization away from `r`. It uses mathlib's `exists_free_localizedModule_powers` and the
  semilinear `Module.Free.of_equiv`.
- `CohomologyAux.additive_eq_of_bijective_app_comp`, `additive_biproduct`.
- `CohomologyAux.exists_additive_eq_mul_unitModule`: on an integral noetherian `Z`, let `λ` be
  additive and zero on modules supported in proper closed subsets. Then `λ G = rk(G) · λ 𝒪_Z`, and
  `rk = 0` forces `G = 0` over a nonempty affine.

**Dévissage, refactored** (`EulerCharacteristicDevissage.lean`):
- `additive_eq_of_bijective_app`: bijective over a single nonempty affine is enough. It replaces
  round 1's basic-open version.
- `vanishesOff_of_isAffineOpen`.

**Critic's partial result** (`SGA1/ExposeXI/UnirationalCoversGalois.lean`):
- `natCard_etaleFundamentalGroup_dvd_finrank`: for `X` proper, normal and integral over an
  algebraically closed `k`, any characteristic, `#π₁(X, s̄)` divides `[L : K(X)]` for every
  unirational parametrization `L`. It holds at every geometric point `s̄` (sep. closed `Ω`), using
  `ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv`.
- Ingredients:
  - `exists_isGalois_natCard_fiber_eq`: in a Galois category with finite `Aut F`, some Galois `A`
    has `#F(A) = #Aut F`. Pairs in `AutGalois F` are separated on finitely many pointed Galois
    objects, and `PointedGaloisObject F` is cofiltered.
  - `geometricFiberCard_genericPoint_dvd_finrank`: `n(η) = [κ(η_Y):κ(η_X)]_s` divides
    `[K(Y):K(X)]`. It uses residue fields at generic points, with no separability argument.
  - `fiberEquivPointsOver`.

**C11 sanity check** (`SGA1/ExposeXI/UnirationalFormsZero.lean`):
- `mem_regularForms_zero_iff`: regular 0-forms are the global regular functions.
- `exists_germToFunctionField_eq`: regular at every point implies global, on integral schemes.
- `finrankH_unit_zero_eq_finrank_regularForms_zero`: **the case `q = 0` of
  `HodgeSymmetryZeroStatement` holds**, for proper integral `X` over an algebraically closed field,
  with no smoothness.

**Round-1 review fixes**, done before the pause and checked today:
- Shared lemmas moved to `UnirationalCoversParametrization.lean`.
- `kaehlerBasis` now goes through `ExposeII.basisKaehlerOfFormallyEtale`.
- No global instance.
- `exists_H_subsingleton` now goes through `H_subsingleton_of_card_le`.
- New lemma `genus_eq_finrankH_unitModule`.
- Docstrings fixed.

**Done this round:**
- `isIso_of_geometricFiberCard_eq_one` deleted. SerreUnirational now uses xiii14's
  `Scheme.Hom.isIso_of_geometricFiberCard_eq_one_of_connectedSpace`
  (`Foundations/Limits/GeometricFiberCardIso.lean`).
- Traps moved to `notes/topics/strategy.md`.
- Stacks tags checked online:
  - 01YF, 02N4, 051R, 0BX5, 0BEK are right.
  - 0BEJ was cited for additivity; that lemma is 08AA (0BEJ is the definition). Fixed in
    `EulerCharacteristicBasic`.
  - 02KE is flat base change; affine base change is 02KG. Fixed in `EulerCharacteristicBaseChange`.

## What was hard, and why

- **Avoiding Stacks 01PD (extension of coherent subsheaves and morphisms).**
  - The textbook comparison of `G` with `𝓘^{⊕r}` needs a global map built from local sections.
  - Instead, map `G` and `𝒪^{⊕n}` (the basis of `Γ(U, G)`, via `homOfSection`) to
    `Q = j_* j^* G`, `j : U ⟶ Z`. `Q` is only quasi-coherent, but the image of `G ⊕ 𝒪^{⊕n} ⟶ Q`
    is coherent, being a quotient of a coherent module.
  - Both maps to the image are bijective over `U`. No sheaf has to be glued.
  - The biproduct is `⨁` over `Option (Fin n)` with `Option.elim`, because `isCoherent_biproduct`
    exists only for `⨁`.
- **Generic freeness lands in `LocalizedModule.Away r M`, not in `Γ(G, D(r))`.**
  - Proving `IsLocalizedModule` for restriction to `D(r)` is easy from
    `exists_pow_smul_eq_map` and `exists_pow_smul_eq_zero`.
  - Moving freeness across the two localizations needed the semilinear `Module.Free.of_equiv`.
- **Degree of the complement of the diagonal.** The repo has the degree for the second
  projection. Base change hands you the first. The fix is the swap restricted to the complement,
  which is an involution, plus `IsPullback.of_horiz_isIso` and `geometricFiberCard_of_isPullback`.
- **Elaboration traps** (also in `strategy.md`):
  - An inline `ShortComplex.mk 0 0 _` passed through an implicit `{S}` timed out; pass it with `@`.
  - `trivial : x ∈ ⊤` makes terms ill-typed at reducible transparency, so `rw` fails. Use
    `Opens.mem_top _`.
  - `pullback` is ambiguous after `open Scheme.Modules`.
  - `germToFunctionField ⊤` needs a `Nonempty ⊤` instance. State it with `X.presheaf.germ ⊤ η _`
    instead.
  - `stalkSpecializes (h : x ⤳ y)` goes from the stalk at `y` to the stalk at `x`. I got the
    direction wrong once.

## What is left

- `HodgeSymmetryZeroStatement` (C11) for `q ≥ 1`. It is the only open input of XI.1.4. Route
  (refined from the round-1 log):
  1. Lefschetz principle down to `ℂ`. C14, `Complex.nonempty_ringHom_of_mk_le_continuum`, gives
     the embedding of a field of definition. Spreading out is A4.
  2. GAGA for `Hᵠ(𝒪)` and `Γ(Ω^q)`. C9 and C10 are owned by xii4; Oka coherence and Theorem B on
     polydiscs are stated now.
  3. Dolbeault.
  4. Hodge theory on compact Kähler manifolds. This is the long pole: elliptic regularity.
  5. For proper non-projective `X`, Deligne, or Chow plus birational invariance.
  - A purely algebraic alternative exists for *unirational* `X`:
    1. Hironaka gives a resolution `Y` of `ℙʳ ⇢ X`.
    2. `Hᵠ(𝒪)` is a birational invariant of smooth proper varieties, so `Hᵠ(Y, 𝒪) = 0`.
    3. The trace splitting in characteristic 0 gives `Hᵠ(X, 𝒪) ↪ Hᵠ(Y, 𝒪) = 0`.

    This needs resolution of indeterminacy, which is no smaller.
- Nothing else in my brief is open.

## For the coordinator (`sga1-oos-coord`)

1. Barrel `lean/SGA/Foundations.lean`: add `Cohomology.EulerCharacteristic`, `…Basic`,
   `…Pullback`, `…BaseChange`, `…Clopen`, `…Devissage`, `…Generic`, `…FiniteEtale` and
   `…FiniteEtaleProof`.
2. Barrel `lean/SGA/SGA1/ExposeXI.lean`: add `UnirationalCurves`,
   `UnirationalCoversParametrization`, `UnirationalCovers`, `UnirationalCoversGalois`,
   `UnirationalFormsAlgebra`, `UnirationalForms`, `UnirationalFormsZero` and `SerreUnirational`.
3. Foundations README, XI.1.4 row: "reduced to `HodgeSymmetryZeroStatement` (transcendental, the
   only open input) by `serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`".
   - Steps 1, 3 and 4 are proved; step 4 is `eulerCharFiniteEtaleStatement`, any characteristic.
   - The curve case is proved in every characteristic.
   - `#π₁` divides the degree of any parametrization.
   - The `q = 0` case of Hodge symmetry is proved.
4. `Geometry.lean`: the docstring of `SerreUnirationalSimplyConnectedStatement` could point to
   `serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`.
5. Dedup in `UnirationalVarieties.lean` (round-1 review, blocking for them, not editable by me).
   - Re-derive `hasFiniteFundamentalGroup_of_functionField_finite` from
     `exists_isSimplyConnected_extension`.
   - Re-derive `hasFiniteFundamentalGroup_of_isUnirational` from `exists_proj_parametrization`.
   - Both lemmas are in `UnirationalCoversParametrization.lean`, which imports only
     `RationalVarieties`, so there is no cycle.
6. Dedup in `Devissage.lean`. `finiteCohomology_of_vanishesOff_range`, `…_union` and
   `finiteCohomology_of_integral_step` are the case `P := FiniteCohomology` of
   `CohomologyAux.prop_of_vanishesOff_range`, `prop_of_vanishesOff_union` and
   `prop_of_integral_step` (`EulerCharacteristicDevissage.lean`).
   - Move the three `prop_*` lemmas into `Devissage.lean`, which mine imports through
     `ProperFiniteness`, and derive the old ones from them.
7. `EulerCharacteristic.lean` is mine but imported by xiii212, so I left two wrong Stacks tags
   untouched:
   - `0BEL` (numerical intersections) should be `0BEJ` (definition of `χ`).
   - `0BYE` (geometric genus) should be `0BY8` (genus `= dim H¹(X, 𝒪_X)`).
   - Fix them when nobody is building against the file.
8. `ExposeXI.isNormalScheme_of_smooth` (`UnirationalCurves.lean`) should become
   `(ExposeX.isIntegral_and_isNormalScheme_of_smooth k f).2` (xiii43, `NormalCompleteLocalBase`).
   I did not import that file because xiii43 is still editing it. xi21t's copy of the same name
   is gone, so there is no barrel clash any more.
9. `exists_isGalois_natCard_fiber_eq` is pure Galois-category theory (mathlib-level). Move it to
   Foundations if anyone else needs it.
