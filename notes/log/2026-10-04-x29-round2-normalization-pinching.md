---
author: x29
date: 2026-10-04
area: SGA1 X, SGA1 IX, Foundations/CommAlg, Foundations, sga1-oos-coord, xiii3, xiii212
kind: handoff
---

# X.2.9 round 2: Noether finiteness, Chow + normalization discharged, pinching IX.5.4

Every module below builds with `lake build`, has no sorry, and `#print axioms` gives only
propext, Classical.choice and Quot.sound. No existing tracked `.lean` file was edited and nothing
went into a barrel; the coordinator requests are listed below.

## Done

- **Reviewer fixes on round 1.** An interrupted earlier attempt had already made them; I checked
  each one against the files and rebuilt everything:
  - hC is now X.2.6 for normal curves;
  - X.2.12 is `finite_principalH1_of_isTopologicallyFG` (the PrincipalH1 form);
  - IX.5.2 is renamed `…_of_isProper_of_surjective`;
  - labels fixed and helpers made private;
  - C14 is in `Foundations/Fields/ComplexEmbedding.lean`;
  - `ExposeX/CurveFiniteSmooth.lean` (normal curve over a perfect field ⇒ smooth) and
    `ExposeX/TopologicallyFiniteCharZero.lean` are present.
- **New registry row A30, proved: E. Noether's finiteness theorem over perfect fields.**
  - `Foundations/CommAlg/NoetherFiniteness.lean`:
    - `Algebra.FiniteType.finite_integralClosure`: `A` a domain of finite type over a perfect
      `k`, `L` finite over `Frac A` ⇒ `Module.Finite A (integralClosure A L)`;
    - the integrally closed case, `…_of_isIntegrallyClosed`;
    - `IsIntegralClosure.finite_of_finiteType`;
    - helpers `RingHom.finite_iterateFrobenius` (the Frobenius of a finite-type algebra over a
      perfect field is finite) and `Module.Finite.of_injective_of_ringHomFinite`.
    - The proof: Noether normalization, then the separable closure `Kₛ`, then mathlib's separable
      `IsIntegralClosure.finite`; the purely inseparable part via
      `IsPurelyInseparable.iterateFrobenius` (`y ↦ y^q`, semilinear over the Frobenius of `B`).
      In characteristic 0 the exponent is 0.
  - `Foundations/NormalizationFinite.lean`, on the normalization `X' = (X.fromSpecStalk
    (genericPoint X)).normalization` (mathlib's relative normalization):
    - `isFinite_fromNormalization_fromSpecStalk_genericPoint` (locally of finite type over a
      perfect field);
    - normality, `isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint`;
    - surjectivity (instance);
    - the packaged `exists_isFinite_surjective_isIntegrallyClosed_stalk`.
  - Dimension lemmas in the same file:
    - `Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite` (discrete fibres ⇒ strict mono
      on specializations);
    - `topologicalKrullDimAt_eq_of_isIntegral` (the local dimension of an integral scheme of
      finite type over a field is constant);
    - `topologicalKrullDim_opens_eq_of_isIntegral`;
    - `topologicalKrullDim_eq_of_isIso_morphismRestrict` (modifications, e.g. Chow's cover,
      keep the dimension).
- **hN of the X.2.9 skeleton is discharged.**
  - `ExposeX.exists_isNormalScheme_isFinite_projectiveSpace` (Chow's lemma + normalization)
    gives a normal integral `X' ↠ X`, proper, of no larger dimension, with a finite morphism to
    `ℙ(σ; k)`. `X'` is not shown H-projective; this follows the critic's suggestion.
  - The skeleton is now generic: `isTopologicallyFG_of_curve_of_hyperplane_of_model` takes a
    class `Q` of models. `isTopologicallyFG_of_curve_of_hyperplane` (H-projective models) is a
    corollary.
  - New: **`topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`**: X.2.9 ⇐ hC
    (normal proper curves) ∧ hH (normal integral proper `X` with a finite map to `ℙ`). The
    characteristic-0 file now uses it, so **X.2.9 in characteristic 0 for `#k ≤ 𝔠` (universe 0)
    follows from hH alone** (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum_of_hyperplane`).
- **Pinching IX.5.4, finite-generation half, abstract form (row A12):**
  `ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_pinching` in `SGA1/ExposeIX/Pinching.lean`.
  - Hypotheses:
    - `g` proper surjective, `S` locally noetherian, `S'` connected, `k` separably closed;
    - the points of `S' ×_S S'` off the diagonal are finitely many closed points, each with a
      `k`-point;
    - `S'''` has finitely many components, each with a `k`-point.
  - Conclusion: `π₁(S)` t.f.g. ⇒ `π₁(S')` t.f.g.
  - Construction: a natural `gluingIso : p₁^* ≅ p₂^*`. On the open diagonal it is the canonical
    iso, through IX.1.7 for `S' ⟶ U_Δ`. On each off-diagonal point it uses chosen paths, since
    `FEt` of a one-point scheme is trivial (`full_fiber`).
  - The fibre formula `gluingFiber_eq` holds at every `k`-point. With it, `isCocycle_gluingIso`
    is checked on fibres at `k`-points of the components of `S'''`.
  - IX.4.12 then gives the section `pinchFunctor` of `g^*`, and V.6.9 gives the surjection
    `π₁(S) ↠ π₁(S')`.

## What was hard (traps for the next agent)

- **Kernel deterministic timeouts.** Three causes, and their fixes:
  - (a) Closing a goal `(a ≫ b) ≫ c = …` with a term stated as `a ≫ (b ≫ c) = …`. The elaborator
    accepts it, but the kernel unfolds composition of scheme morphisms. Fix: `rw [Category.assoc]`
    first.
  - (b) Any elementwise (`FintypeCat.hom_ext` / `fiber_ext_point`) proof whose types mention
    `tripleProj₃₁ g`, which is an `abbrev` for a `pullback.lift` with a proof inside. Even the
    first two tactics time out. Fix: state the lemma for arbitrary morphisms
    (`fiber_fetPullbackCompCongr`, `fiber_cocycle` with `q₂₁ q₃₂ q₃₁`) and instantiate it.
  - (c) The same for `by simp only [tripleProj₃₁, …]` proofs inside statements. Fix: use named
    lemmas `tripleProj₃₁_fst/snd`.
- **`P : ConnectedComponents T → Spec k ⟶ T`** parses as `(… → Spec k) ⟶ T`. Write the
  parentheses.
- **Uniqueness of `k`-points removes all "factor through" problems.** Two `k`-points with the
  same image are equal (`Pinching.eq_of_comp_eq_id`, proved via `SpecToEquivOfField` and the
  residue maps). Use it instead of factoring maps through closed immersions or reductions.
- **Preimages under `FullyFaithful.whiskeringRight`.** State the wanted equation with `have h : … :=
  by have := (…).map_preimage e.hom; exact congrArg (fun α ↦ NatTrans.app α Y) this`. A direct
  `congrArg` does not unify. Give `NatIso.pi'` its own `def` (`piIso`); otherwise the
  restriction lemma times out.

## Next (round 3, in order of value)

1. **Pinching for curves.** Verify the hypotheses of `isTopologicallyFG_etaleFundamentalGroup_of_pinching`
   for the normalization `ν : C ⟶ D` of an integral proper curve over `k = k̄`:
   - `ν` is an iso over a dense open, so the off-diagonal points lie over a finite set and are
     closed with residue field `k`;
   - `S'''` is noetherian, hence has finitely many components; each component contains a closed
     point, which is a `k`-point.
   This yields "π₁(plane model) t.f.g. ⇒ π₁(C) t.f.g.".
2. The char-p curve engine (row A29): first the `W(k)` base, then the plane model and the lift
   of `F`.
3. hH (X.2.10). This needs the Bertini field lemma. I found no short proof. The geometric proof
   (incidence variety, Stein factorization, a section through a fixed point, purity) is long.
   Look at Fried–Jarden ch. 10 or Jouanolou 6.3 for an algebraic proof before starting.

## For the coordinator (sga1-oos-coord)

- **Barrel entries.**
  - `SGA.Foundations.CommAlg.NoetherFiniteness` and `SGA.Foundations.NormalizationFinite` go in
    `SGA/Foundations.lean`.
  - `SGA.SGA1.ExposeIX.Pinching` goes in `SGA/SGA1/ExposeIX.lean`.
  - `SGA.SGA1.ExposeX.{CurveFiniteSmooth, TopologicallyFiniteCharZero}` go in
    `SGA/SGA1/ExposeX.lean`, together with round 1's entries.
- **Stale docstring.** The `ExposeIX/FundamentalGroupDescent.lean` module doc says IX.5.4 is not
  formalized. Its finite-generation half now is, in `ExposeIX/Pinching.lean`.
