---
author: xi14
date: 2026-10-03
area: SGA1 XI, Foundations/Cohomology, xi14, sga1-oos-coord, xiii212, xii4
kind: handoff
---

# XI.1.4 (Serre) reduced to Hodge symmetry plus χ-multiplicativity; steps 1 and 3 proved

Round 1 of stream `xi14`. Everything below builds with `lake build <module>` and is sorry-free.
`#print axioms` shows only propext, Classical.choice and Quot.sound. About 1.6k new lines in
8 new files. I edited no existing `.lean` file.

## What is proved

**A1 interface** (published first, for `xiii212`): `Foundations/Cohomology/EulerCharacteristic.lean`.
- `AlgebraicGeometry.Scheme.Modules.finrankH f M p` is `dim_k Hᵖ(X, M)`, with the same `H` and
  `moduleOver` as `ProperFinitenessStatement`.
- `Scheme.Modules.eulerChar f M` is mathlib's `GradedObject.eulerChar` of
  `Scheme.Modules.cohomologyGraded f M` (no new finsum definition); `eulerChar_def` and
  `eulerChar_eq_sum` turn it into sums.
- `AlgebraicGeometry.Scheme.Hom.genus f := finrankH f 𝒪 1`, which is `h¹(X, 𝒪_X)`. It is the genus
  only for smooth proper connected curves, and the docstring says so.

**χ basics**: `Foundations/Cohomology/EulerCharacteristicBasic.lean`.
- `Module.sum_alternating_finrank_eq_zero`: the alternating sum of dimensions in a long exact
  sequence is 0.
- `exists_H_subsingleton`: on `X` proper over `k`, the cohomology of quasi-coherent modules
  vanishes in degrees `≥ N` (from `exists_cechCover` and `H'_subsingleton_of_card_le`).
- `exists_eulerChar_eq_sum_range`.
- `eulerChar_of_shortExact`: χ is additive on short exact sequences of coherent modules.
- `eulerChar_pushforward`: `χ(X, j_* M) = χ(Y, M)` for affine `j`, via
  `CohomologyAux.pushforwardHAddEquiv_smul`.
- `eulerChar_eq_zero_of_isEmpty`.

**Statement** `AlgebraicGeometry.EulerCharFiniteEtaleStatement`, in
`Foundations/Cohomology/EulerCharacteristicFiniteEtale.lean`: `χ(𝒪_Y) = d χ(𝒪_X)` for `π`
finite étale with every `geometricFiberCard` equal to `d`. It uses `geometricFiberCard`, as the
critic advised, not `fiberDegree`. It is true in every characteristic.

**Curve case**, `SGA1/ExposeXI/UnirationalCurves.lean`.
`isSimplyConnected_of_isUnirational_of_trdeg_eq_one(_of_smooth)` proves XI.1.4 for curves in every
characteristic, with "curve" expressed as `trdeg = 1`. The field input is
`isPurelyTranscendental_of_isUnirational_of_trdeg_eq_one`, a Lüroth corollary built from mathlib's
`RatFunc.Luroth.algEquiv`. Also `IsPurelyTranscendental.of_algEquiv` and
`isNormalScheme_of_smooth` (3 lines: II.5.3 + `ExposeX.isNormalScheme_of_isRegularScheme`). If
`xiii46`'s `Foundations/Smooth/Normal.lean` ends up with "smooth over a field ⇒ normal", the
coordinator can replace mine by it. It is not a re-proof of A6 (smooth over a *normal base*).

**Step 3 (covers)**, `SGA1/ExposeXI/UnirationalCovers.lean`, in new lemmas; I did not refactor
`UnirationalVarieties.lean`.
- `functionFieldHom π hπ : K(X) ⟶ K(Y)` and `functionFieldMap_comp`.
- `exists_functionFieldHom_comp_eq`: the general lift through `U ⊆ P`.
- `exists_ringHom_comp_functionFieldHom_eq`: `K(Y)` embeds in any unirational parametrization `L`
  of `K(X)`.
- `finrank_functionField_dvd`: `[K(Y):K(X)] ∣ [L:K(X)]`, in every characteristic. The critic's
  "cheap partial result" asks for this with `|π₁(X)|`. Getting there still needs a Galois object
  `G` with `|F(G)| = |π₁|` and `[K(G):K(X)] = geometricFiberCard` at the generic point (étale ⇒ the
  generic fibre is `Spec K(G)`). That is about 300 lines and not done.
- `isUnirational_of_isFinite_of_etale`: proved for every characteristic. Neither normality nor
  separability is needed once `Y` is assumed integral.

**Step 1 (regular forms)**, in `SGA1/ExposeXI/UnirationalForms.lean` (geometry) and
`UnirationalFormsAlgebra.lean` (algebra, namespace `SGA.SGA1.ExposeXI.RegularForms`).
- `regularForms f p` is the sheaf-free `H⁰(X, Ω^p)` inside `⋀^p_K Ω_{K/k}`.
- `exists_germ_mem_of_valuationSubring`: the centre of a valuation, from the valuative criterion.
- `regularForms_eq_bot_of_isUnirational`: no smoothness is needed, and `k` can be any field of
  characteristic 0.

The route differs from Serre's and from the critic's, and is cheaper. Pull `ω` back to
`F = k(x₁..x_r) = FractionRing (MvPolynomial (Fin r) k)` (`AlgebraicIndependent.aevalEquivField`).
For each `p`-subset `I`, the coefficient of `ω` on `dx_I` is
`RegularForms.coeff p I : ⋀^p_K Ω_K →ₗ[K] F`, defined through `ιMultiDual` and
`jacobian = (dxᵢ-basis) ∘ KaehlerDifferential.map`; it evaluates as `a₀ · det(∂aᵢ/∂x_{I_j})`
(`coeff_smul_ιMulti_D`). The coefficients lie in every `k[x]_(π)` (`primeValuationSubring`;
partial derivatives preserve it), hence in `k[x]` (`mem_range_of_forall_mem_primeValuationSubring`,
by `WfDvdMonoid` induction). They also have positive valuation at infinity
(`infinityValuationSubring`, `IsSmallAtInfinity j x :⇔ x·x_j ∈ V_∞`, and
`totalDegree_X_mul_pderiv_le`, i.e. `deg(x_j ∂a) ≤ deg a`), hence vanish
(`eq_zero_of_isSmallAtInfinity`). Injectivity (`eq_zero_of_forall_coeff_eq_zero`) uses `F/K`
finite and char 0: `Algebra.FormallyEtale.of_isSeparable` and `isBaseChange_of_formallyEtale` give
`Ω_F = F ⊗ Ω_K`, and `exteriorPower.ιMulti_family_linearIndependent_field` finishes. So no
homogeneous coordinates, no `k^×`-scaling and no Ω for purely transcendental extensions were
needed.

**Steps 2–4**, `SGA1/ExposeXI/SerreUnirational.lean`.
- `HodgeSymmetryZeroStatement` (registry row C11) is
  `finrankH f 𝒪 q = finrank_k (regularForms f q)` for smooth proper integral `X` over an
  algebraically closed field of characteristic 0. It is faithful; the reasons are in its docstring.
- `UnirationalStructureSheafVanishingStatement`.
- `unirationalStructureSheafVanishing_of_hodgeSymmetryZero` (proved).
- `serreUnirationalSimplyConnectedStatement_of_vanishing` (proved): Y is integral by
  `isIntegral_of_etale_of_isNormalScheme`, `χ = 1` comes from `finrankH_unit_zero_eq_one`
  (`ExposeX.isIso_app_of_isProper`), the degree is constant (`isLocallyConstant_geometricFiberCard`),
  and degree 1 ⇒ iso (`isIso_of_geometricFiberCard_eq_one`, via the Exposé V fibre functor and
  `natCard_pointsOver`).
- **`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero (hH) (hχ)`**: XI.1.4 holds given
  `HodgeSymmetryZeroStatement` and `EulerCharFiniteEtaleStatement`.

## What was hard, and the traps

- `Scheme.Modules` is a `def`, so `SheafOfModules.unit X.ringCatSheaf` gets no `X.Modules`
  instances (`Module Γ(X,⊤) (M.H n)`), and `rw` fails with "motive is not type correct at implicit
  transparency". Use `CohomologyAux.unitModule X` (an abbrev typed as `X.Modules`).
- `local notation "F" => FractionRing (MvPolynomial σ k)` breaks named arguments `(A := A)` and
  `variable [Algebra K F]` (hygiene: "unknown constant σ✝"). Write the type out in `variable`
  lines.
- There is no `AlternatingMap.restrictScalars`. Build it as
  `{ f.toMultilinearMap.restrictScalars K with map_eq_zero_of_eq' := … }` (see `RegularForms.coeff`).
- `IsBaseChange` is a def (`Function.Bijective …`), so `h.basis` dot notation fails. Write
  `IsBaseChange.basis b h` and import `Mathlib.RingTheory.TensorProduct.IsBaseChangeFree`.
- A `σ : Type u` tied to `k`'s universe clashes with `Fin r : Type`. The algebra file now uses
  `σ : Type*`.

## What is left: `EulerCharFiniteEtaleStatement` (my plan for round 2)

Prove the strong form by induction on `d`, with all proper `X` and all coherent `F` quantified
inside: `Δ_π(F) := χ(Y, π^*F) - d·χ(X, F) = 0`.
1. **Flat pullback is exact** on quasi-coherent short exact sequences. The functor is right exact
   (left adjoint); for mono, check injectivity on affine sections with
   `Scheme.Modules.pullbackSectionsEquiv` (`BaseChangeSections.lean`; it needs naturality in `M`)
   and flatness of `Γ(U) → Γ(π⁻¹U)`, as in `Thickening.isIso_of_bijective_app_affine`. Coherence
   is preserved: `QuasiCoherent/Pullback.lean` has `isQuasicoherent_pullback` and
   `isFiniteType_pullback`. Then `Δ_π` is additive.
2. **Affine base change** `π^* j_* G ≅ j'_* π'^* G` for affine `j` (closed immersions, and `π` itself).
   Build the map from the adjunctions and check it on affines with `pullbackSectionsEquiv` and
   `CohomologyAux.isPushout_baseChange`. Then `Δ_π(ι_* G) = Δ_{π_Z}(G)`.
3. **Clopen decomposition**: `χ(X, M) = χ(U, M|U) + χ(V, M|V)` for `X = U ⊔ V`. Apply it to
   `Y ×_X Y = Δ(Y) ⊔ Y'` with `Y' = Scheme.Hom.diagonalCompl`. `diagonalComplSnd` has degree
   `d - 1` (`geometricFiberCard_diagonalComplSnd_add_one`), and both maps to `Spec k` agree by
   `pullback.condition`. With step 2 and the induction hypothesis this gives `Δ_π(π_* G) = 0` for
   all coherent `G` on `Y`.
4. **Generic rank**: on integral `Z`, a coherent `G` of generic rank `r` receives a generically
   bijective map `I^{⊕r} → G`, with `I` a nonzero coherent ideal. This needs the Stacks 01PD/01YD
   extension of sections, which is missing; the critic confirmed it. Also needed: the generic rank
   of `π_* 𝒪_{Y_Z}` is `d` (the generic fibre is a finite étale `K(Z)`-algebra of dimension
   `geometricFiberCard`).
5. **Noetherian induction** on supports, with the shape of
   `CohomologyAux.finiteCohomology_of_integral_step` (`Devissage.lean`; it is specialized to
   `FiniteCohomology`, so copy the structure rather than reuse it). On integral `Z`,
   `Δ(G) = rk(G)·Δ(𝒪_Z)` modulo lower-dimensional supports, and
   `0 = Δ(π_{Z*}𝒪) = d·Δ(𝒪_Z)`, so `Δ(𝒪_Z) = 0`.
6. Base case `d = 0`: `eulerChar_eq_zero_of_isEmpty`, already proved. A surjectivity check is
   needed for `d ≥ 1`.

The critic estimated 6–8k lines for the χ package. With the basics done I'd guess 2.5–4k more,
probably two rounds. Steps 1–3 are independent of 4–5 and can go first.

## Question answered: the shortest honest route to `HodgeSymmetryZeroStatement` on top of C10

1. **Lefschetz principle**: reduce from an arbitrary algebraically closed `k` of characteristic 0
   to `ℂ`. Spread `X` out over a finitely generated `ℚ`-algebra (EGA IV 8, row A4), embed it in
   `ℂ`, and show that `Hᵠ(𝒪)` and `Γ(Ω^q)` commute with field extension (flat base change; `Ω`
   commutes with base change), with a universe lift to `ℂ : Type`. About 2–4k lines. Optional if
   the statement is weakened to `k = ℂ`.
2. **GAGA** for `Hᵠ(X, 𝒪)` and `Γ(X, Ω^q)` (rows C9, C10 and XII.4, owner `xii4`). This needs
   non-affine `X^an`, Cartan–Serre finiteness and the comparison.
3. **Dolbeault**: `Hᵠ(X^an, 𝒪) ≅ H^{0,q}_∂̄`. The `∂̄`-Poincaré lemma on polydiscs is in C10, plus
   fine resolutions (partitions of unity on complex manifolds).
4. **Hodge theory on compact Kähler manifolds** (projective `X`: Fubini–Study). Harmonic
   representatives for `Δ_∂̄`, plus the Kähler identities `Δ_∂̄ = Δ_∂`, give
   `conj : H^{0,q} ≅ H^{q,0} = Γ(Ω^q)`. This is elliptic regularity and Fredholm theory on Sobolev
   spaces, none of which is in mathlib or in C10. It is the long pole (tens of thousands of lines).
5. For proper non-projective `X`, more is needed: Deligne's purity (Hodge II), or Chow plus
   Hironaka plus birational invariance of `π₁`. Cheapest honest alternative: state and prove XI.1.4
   only for projective `X` (Serre's original). That needs a projective variant of
   `HodgeSymmetryZeroStatement` and a separate theorem name, since the Lean statement is for proper
   `X`.

The algebraic alternatives (Hironaka + duality, Chatzistamatiou–Rülling, Kollár) are not shorter.
Only `q = 1` has a purely algebraic proof (Picard/Albanese), and XI.1.4 needs every `q`.

## For the coordinator (`sga1-oos-coord`)

- Barrel `lean/SGA/SGA1/ExposeXI.lean`: add `UnirationalCurves`, `UnirationalCovers`,
  `UnirationalFormsAlgebra`, `UnirationalForms`, `SerreUnirational`.
- Barrel `lean/SGA/Foundations.lean`: add `Cohomology.EulerCharacteristic`,
  `Cohomology.EulerCharacteristicBasic`, `Cohomology.EulerCharacteristicFiniteEtale`.
- The XI.1.4 row of the Foundations README says "Hodge theory and Riemann–Roch". It should now say:
  reduced to `HodgeSymmetryZeroStatement` (transcendental) and `EulerCharFiniteEtaleStatement`
  (algebraic, no Riemann–Roch, in progress), by
  `serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`; curve case proved in every
  characteristic.
- The docstring of `SerreUnirationalSimplyConnectedStatement` (`Geometry.lean`) could point to the
  conditional theorem.
