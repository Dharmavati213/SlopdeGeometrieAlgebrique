---
updated: 2026-10-04
---

# Hard parts

The mathematical and formal obstacles in the SGA 1 formalization: what each open item is, why it
is hard, what already exists, what was tried, and what to do next. Edit the relevant section in
place and keep entries short. Put the date and your handle on new items, e.g. `(2026-10-05,
sga1-ix-ega4)`. When an item is resolved, delete it or mark it `RESOLVED` and name the
declaration that closed it.

Seeded 2026-10-03 (handle `claude-1003`) from the agent reports of the SGA 1 Lean campaign
(2026-09-24 to 2026-09-27), the coordinator's log and the code. Names in parentheses such as
(F-Coh-X) are those reports. They lived in a gitignored job directory that may be gone, so
everything that matters from them is copied here. Paths are repo-relative.

What is proved and what is open: [`docs/formalization.md`](../../docs/formalization.md) (the
"Open statements" table lists the 17 in-scope ones) and
[`lean/SGA/Foundations/README.md`](../../lean/SGA/Foundations/README.md) (out of scope). On
2026-10-03, every `…Statement` named as open below was checked to still be an unproved `def`;
the out-of-scope ones were checked again on 2026-10-04 (sga1-oos-coord).
Routes that solved problems which had looked hard are in [`strategy.md`](strategy.md), under
"Cheap and expensive surprises".

## 1. Grothendieck existence and algebraization (EGA III 5)

### Existence theorem, proper non-projective case

- **What.** `GrothendieckExistenceStatement` (EGA III 5.1.4) in
  `lean/SGA/Foundations/Cohomology/Statements.lean`. It blocks IX.1.10
  (`EtaleCoveringsOfClosedFibreStatement`, `lean/SGA/SGA1/ExposeIX/EtaleMorphismDescent.lean`),
  which is X.2.1 (`CompleteLocalBaseStatement`, `lean/SGA/SGA1/ExposeX/Semicontinuity.lean`). Through
  them it also blocks X.2.2–X.2.4 for proper `X` (proved for projective `X`), and it is an input to
  X.3.8 (section 5).
- **Why hard.** Mathlib has abstract sheaf cohomology but none of the quasi-coherent theory:
  no Čech comparison, Serre vanishing or finiteness, no coherent theory of proper morphisms, no
  relative `Spec` of a quasi-coherent algebra, and no formal schemes. EGA III §§1–4 had to be
  built first in `lean/SGA/Foundations/Cohomology/` (about 90 files). That part is proved: Čech
  and derived cohomology, Serre vanishing, `H^i(ℙ^r, 𝒪(d))`, proper finiteness
  (`properFinitenessStatement`, by dévissage and Chow), formal functions
  (`formalFunctionsStatement`, through the Rees algebra), `zariskiConnectednessStatement`,
  `steinFactorizationStatement`. One agent spent ten rounds on this chain (F-Coh-I to F-Coh-X).
- **What exists for existence itself.**
  - Full faithfulness for proper `X`: `grothendieckExistence_fullyFaithful`
    (`lean/SGA/Foundations/Cohomology/ExistenceFullyFaithful.lean`). Clopen subsets of `X` match
    those of the closed fibre: `existsUnique_isClopen_preimage_closedFibre` (`ClosedFibre.lean`).
  - Essential surjectivity, only for *locally free* adic systems on `X` closed in `ℙ(τ; Spec A)`:
    `AdicSystem.exists_iso_quotientIdealPow_of_isLocallyFree` (`ExistenceLocallyFree.lean`). It is
    built on `GradedSheaf`, `UniformVanishing`, `TwistGeneration`, `LocallyFreeAlgebraization`,
    `AlgebraAlgebraization` and `RelativeSpec` (also `…Universal`, `…Etale`, `…Functoriality`), all
    in the same directory.
  - The finite étale corollary FEt(X) ≌ FEt(X₀) for `X` projective over a complete noetherian
    local `A` is `isEquivalence_pullback_closedFibre` (`FiniteEtaleEquivalence.lean`). Full
    faithfulness for any proper `f` is `faithful_pullback_thickening` and
    `full_pullback_thickening`. On the Exposé IX side, see
    `lean/SGA/SGA1/ExposeIX/EtaleCoveringsClosedFibre.lean`:
    `etaleCoveringsOfClosedFibre_of_isClosedImmersion` (projective case), and
    `etaleCoveringsOfClosedFibreStatement_of_essSurj` (IX.1.10 for proper `X` follows from
    essential surjectivity of base change along the first thickening).
  - Proper-case pieces (F-Coh-X):
    - `FormalAlgebraizable I f`, `essSurj_pullback_thickening_of_formalAlgebraizable` and
      `formalAlgebraizable_of_essSurj` (`FiniteEtaleAlgebraization.lean`): given I.8.3,
      algebraizability of the systems `(Yₙ ⟶ X)_* 𝒪` is equivalent to essential surjectivity on
      étale coverings.
    - `exists_finiteEtale_of_algebraization` drops projectivity through
      `projective_sections_of_liftingProperty_of_isProper` (`ProperProjectivity.lean`).
    - `exists_iso_quotientIdealPow_of_proIso` (`ProIsoAlgebraization.lean`) is the Artin–Rees
      pro-isomorphism criterion.
    - `formalAlgebraizable_of_stein` (`SteinAlgebraization.lean`) descends algebraizability along
      a proper `p` with `p_* 𝒪 = 𝒪`.
    - Chow's lemma: `exists_isHProjective_of_isProper` (`lean/SGA/Foundations/Projective/Chow.lean`),
      only for `X` integral and `S` affine.
- **Route chosen.** The route is specific to finite étale coverings and handles locally free
  systems only. It does not prove the general coherent 5.1.4 (F-Coh-X). Chow and the Stein step
  cover integral `X`. Remaining steps, in order (F-Coh-X):
  1. Milnor gluing along the normalization `ν` (finite) and a closed immersion `j`.
  2. The conductor ideal sheaf.
  3. `X` reduced but reducible, using the vanishing ideals of the components.
  4. `X` non-reduced, through I.8.3.
  5. Noetherian induction over closed subschemes, with Chow.
  6. `IsAffineHom` of the diagonal (`X'` separated over an affine base).
  7. The final theorems.
- **Milnor step design** (resume notes, not started in the repo).
  - Let `P := ν_* F^c`, `Q := j_* F^W` and `M := ν_* i'_* i'^* F^c` (with `i' : W' ⟶ X^c`), with
    `φ := ν_*(unit)`.
  - Get `ψ : Q ⟶ M` from `existsUnique_comp_toQuotientIdealPow_eq`.
  - Set `B := ker(φ ∘ fst − ψ ∘ snd : P ⊞ Q ⟶ M)` and `Eₙ := steinE ν ⊞ steinE j`, then apply the
    pro-isomorphism theorem.
  - The per-affine hypotheses are (Mn-ii) `ker(R^c_n → R'_n) ⊆ ν_n(ker(R_n → R^W_n))` and (Mn-i)
    Artin–Rees for `ν(J) ⊆ R^c`.
- **Not done.** The general coherent route (F-Coh-VIII plan: graded sheaf `coker φ_{≤M₀}`,
  retractions, uniform Serre vanishing, kernel system `Kₙ`, algebraize `βₙ`) was carried out only
  for locally free systems. Kernel systems of non-locally-free adic systems were not done, and
  neither was the Chow reduction for coherent sheaves (F-Coh-IX). The FEt-only route above will not give
  III.7.4 (next item).

### III.7.4 and algebraization of formal schemes

- `SmoothProperCurveLiftStatement` (`lean/SGA/SGA1/ExposeIII/Schemes.lean`) needs EGA III 5.4.5
  (algebraizing a formal scheme with an ample line bundle). It also needs a smooth proper curve
  to be projective and covered by two affines (III-7). IX-9 called it out of scope, but
  docs/formalization.md keeps it in scope.
- III.5.9 needs EGA III 5.4.1 (algebraization of morphisms). III.7.2–III.7.3 need coherent
  existence on `ℙⁿ`, a formal embedding and the lifting of an ample bundle (III-7). None of these
  is stated.
- **RESOLVED** (2026-10-04, iii74): III.7.4 is proved,
  `SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement` (`lean/SGA/SGA1/ExposeIII/CurveLiftCurve.lean`).
  The route avoids coherent existence and ample bundles:
  1. a smooth proper curve has a finite flat `X₀ ⟶ ℙ¹_k`
     (`AlgebraicGeometry.smoothProperCurveFiniteFlatStatement`: per connected component, a
     transcendental rational function, extended by the valuative criterion, finite by Zariski's
     main theorem, flat over the PID charts; glued over the components);
  2. lift `X₀` and the two chart coordinates level by level (`CurveLift.Stage.exists_succ`;
     obstruction `H¹(X₀, g^*𝒪(2))`, killed by replacing `g` with `g` followed by `t ↦ tᵈ`);
  3. algebraize the finite flat cover of `ℙ¹_A` with the *locally free* existence theorem
     (`CohomologyAux.exists_finite_flat_of_formalFiniteFlat`);
  4. the algebraization is flat and proper with smooth closed fibre, hence smooth
     (`CurveLift.smoothOfRelativeDimension_of_isPullback`, Stacks 00TF).
  Still not formalized from this item: coherent existence on `ℙⁿ`, EGA III 5.4.5 with an ample
  bundle, III.5.9, III.7.1–III.7.3.

### Formal schemes (`lean/SGA/Foundations/Formal/`)

- **Exists.**
  - `Spf` and its morphisms: `homEquiv`, `hom_ext_of_toΓ` in `SpfMorphisms.lean`.
  - `formalCompletion`.
  - `CommAlgCat.FiniteEtale.isEquivalence_baseChange_quotient` (I.8.4, affine).
  - `Spf.isEquivalence_formalFiniteEtale_toZero` (I.8.4 for `Spf A`, with no I.8.3 hypothesis).
  - `FormalFiniteEtale.isEquivalence_toZero` (takes I.8.3 as a hypothesis).
- **Gaps** (F-Formal-2).
  - I.8.4 for a non-affine `X̂`. I.8.3 for schemes is in
    `lean/SGA/SGA1/ExposeIX/NilImmersion.lean`, but Foundations cannot import SGA 1. Pass it as a
    hypothesis; see strategy.md.
  - EGA I 10.4.6 existence in general.
  - Coherent sheaves on formal schemes, which III.5.8 for non-affine schemes and III.7 need.

## 2. Infinitesimal lifting at sheaf level (Exposé III)

- **What.** Not formalized and not stated: III.5.8 for non-affine formal schemes, III.5.9,
  III.6.3 in general, III.6.7 uniqueness, III.6.9, III.7.1–III.7.3.
- **Why.** The extension sheaf and its torsor structure were built by hand on affine charts:
  - `isSheaf_extensionPresheaf` (`lean/SGA/SGA1/ExposeIII/ExtensionSheaf.lean`);
  - `derivationPresheaf` (`DerivationSheaf.lean`);
  - `extensionTorsor` (`ExtensionTorsor.lean`);
  - `exists_extension_of_cech` (`RelativeExtension.lean`).

  So `𝒢 = ℋom(g₀^* Ω, 𝒥)` is a presheaf of derivations on charts, not a `Scheme.Modules`. That
  means the Foundations cohomology (Čech comparison, Serre vanishing) cannot be applied to it.
  Identifying the two ran into a `Module` instance problem (III-8). III.6.3 in general needs
  non-abelian Čech 2-cocycles. III-6 noted that the `H²` obstruction has no downstream use.
- **Exists.**
  - `globalExtensionStatement` (III.5.5) and `smoothLiftAffineStatement` (III.6.8).
  - `exists_smooth_lift_of_isAffine`.
  - III.5.8 for affine formal schemes: `isoSeq_eq_of_isAffine` (`FormalUniqueness.lean`) and
    `FormalIsomorphism.lean`.
  - III.6.7 and III.6.10 for two charts: `TwoChartLift.lean`.
- **Plan** (III-8 resume notes):
  - A: coordinates `(Fin d → B/𝔪B) ≃ I·B`, for `B` flat with a basis.
  - B: a derivation lemma for étale maps and descent.
  - C: on an affine `W`, identify the tangent sheaf with `Der_{R₀}(Γ(W), Γ(W))`, via
    `sheafHomAffineEquiv` (`lean/SGA/Foundations/Cohomology/SheafHomCoherent.lean`) and
    `relativeDifferentialsAppEquiv` (`lean/SGA/Foundations/Differentials/AffineOpens.lean`).
  - D: transport Čech complexes with `CechTransport.exactAt_iff`.
  - E: the step theorem, using `cechComplex_exactAt_iff_subsingleton_H'`
    (`lean/SGA/Foundations/Cohomology/AffineOpenVanishing.lean`, needs `IsAffineHom` of the
    diagonal).
  - F: III.5.8 for non-affine schemes, and uniqueness in III.6.7 and III.6.9.
  - G: `Ω` coherent for locally finite type, so `𝒢` is quasi-coherent (`isQuasicoherent_sheafHom`).

  New foundation files were to go in `lean/SGA/Foundations/Deformation/`. The first of them,
  `TangentAffine.lean` (81 lines: `Γ(W, 𝒯_{Z/S})` as derivations, EGA IV 16.5.4, Stacks 01UQ),
  was unfinished. It was moved out before the PR and survives only in the job scratch directory,
  if at all.

## 3. EGA IV limit arguments (Exposé IX over a general base)

- **What.** `EffectiveDescentOfProperStatement` (IX.4.12,
  `lean/SGA/SGA1/ExposeIX/EtaleEffectiveDescent.lean`), and `ProperDescentStatement` and
  `GeometricFibresStatement` (IX.6.8 and IX.6.11, `lean/SGA/SGA1/ExposeIX/ExactSequence.lean`).
- **Exists** (locally noetherian base):
  - `isEffectiveDescentMorphism_of_isProper` (`ProperEffectiveDescent.lean`);
  - `properDescentStatement_of_isLocallyNoetherian` (`ProperDescentLocal.lean`);
  - `ker_autMap_eq_geometricFibres_of_isLocallyNoetherian` (`ProperDescentGeometricFibres.lean`).

  IX.6.9 holds in full: `universalProperDescentStatement`, from
  `isEffectiveDescentMorphism_pullback_snd_of_isProper` (`ProperDescentLimit.lean`). That file
  already handles descent data over a limit of noetherian affine schemes, *given* that `g` is the
  base change of some `g_j`.
- **Missing** (IX-11, IX-12):
  - Producing `g_j`. A finitely presented, proper, surjective `g` over an arbitrary base must be
    shown to be a base change of one over a noetherian base: EGA IV 8.8.2 for finitely presented
    schemes and morphisms, and 8.10.5 for properness and surjectivity.
  - EGA IV 9.7.7, for the geometric fibres in IX.6.8 and IX.6.11.
  - A base-change API for `DescentDatum`, estimated at several hundred lines.
- **Limit tools already there.**
  - `lean/SGA/Foundations/Limits/FiniteEtale.lean`: finite étale schemes over a cofiltered limit of
    qcqs schemes with affine transitions. Objects:
    `Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale`; morphisms:
    `Scheme.exists_hom_of_isPullback`, from mathlib's
    `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`; isomorphisms:
    `Scheme.exists_iso_of_isPullback`.
  - `Limits/BaseChange.lean`: filtered colimits of rings, and `exists_isFinite_etale_morphismRestrict`
    (EGA IV 8.10.5 for finite étale).
  - `Limits/IntegralApproximation.lean`.
  - `lean/SGA/Foundations/NoetherianApproximation.lean`: `Algebra.exists_finite_model_of_isNilpotent`,
    `Algebra.Etale.exists_model_of_subset_range`.
- **Next step.** Build the EGA IV 8 reduction for finitely presented proper morphisms. IX.4.12,
  IX.6.8 and IX.6.11 then follow from the noetherian case.

### IX.6.1 without quasi-separatedness

`ExactSequenceStatement` (`lean/SGA/SGA1/ExposeIX/ExactSequence.lean`) is SGA's statement, which
assumes the fibre `X_s` only quasi-compact. The proved version,
`exactSequence_of_quasiSeparatedSpace` (`lean/SGA/SGA1/ExposeIX/FiniteEtaleLimit.lean`), adds
`QuasiSeparatedSpace (f.fiber s)`, because the limit theorem it uses (EGA IV 8.8.2) needs qcqs.
Stacks 0BTX also assumes qcqs. No agent found either an argument or a counterexample (F-Limits,
F-Limits-2).

### IX.6.5–IX.6.6

`LocalProperDescentStatement` needs the Stein factorization, which exists as
`steinFactorizationStatement`, together with its compatibility with completing the base along
`Ô_s`. IX-12 estimated several thousand lines. IX.6.6 is not stated.

## 4. Local algebra from EGA 0_III, EGA II and EGA IV 14

- **IX.4.6 in SGA's form**, `IsEffectiveIffStrictlyLocalStatement`
  (`lean/SGA/SGA1/ExposeIX/EtaleEffectiveDescent.lean`). **Resolved 2026-10-04 (local-alg)**:
  `isEffectiveIffStrictlyLocal` in `SGA1/ExposeIX/StrictlyLocalDescentGeneral.lean`, from the
  separably closed version (`DescentDatum.isEffective_iff_forall_isSepClosed`,
  `StrictlyLocalDescent.lean`) and EGA 0_III 10.3.1 (`IsLocalRing.flatResidueExtensionStatement`,
  `Foundations/CommAlg/FlatResidueExtensionGeneral.lean`; the case used is
  `exists_flat_isAlgClosed_residueField`). 10.3.1 is proved without SGA's transfinite induction:
  a transcendence basis (`A[X]_{𝔪A[X]}`), the strict henselization (separable part), and an
  `ℕ`-indexed tower of `R[Y]/(Y^p - l)` over relative `p`-bases (purely inseparable part).
- **IX.4.9 input**, `QuasiSectionStatement` (`lean/SGA/SGA1/ExposeIX/UniversallyOpenDescent.lean`):
  quasi-sections of universally open morphisms (EGA IV 14.3.13, 14.5.4). **Resolved 2026-10-04
  (local-alg, row A60)**: `quasiSectionStatement` and IX.4.9 itself,
  `effectiveDescentOfUniversallyOpenStatement`, in `SGA1/ExposeIX/QuasiSection.lean`. No EGA IV 14
  machinery was needed: openness of `Spec B → Spec A` gives going down, so
  `ht P = dim A + dim` of the fibre; cutting by a system of parameters of the fibre leaves a
  component through `P` of dimension `≥ dim A`, and the dimension inequality forces it to
  dominate (`Foundations/CommAlg/QuasiSection.lean`, all from mathlib's Krull height theorem).
- **IX.2.6 sufficiency**, `UniversallySubmersiveValuativeCriterionStatement`
  (`lean/SGA/SGA1/ExposeIX/Submersive.lean`). **Resolved 2026-10-04 (local-alg)**:
  `universallySubmersiveValuativeCriterion` in `SGA1/ExposeIX/SubmersiveValuative.lean` (only
  quasi-compactness of `g` is used). Route: DVR criterion ⇒ "lifts to local domains dominating
  any given one" by an algebraic descent to a noetherian local subring plus EGA II 7.1.7
  (`Algebra.exists_hasDominatingPoint_of_forall_isDiscreteValuationRing`,
  `Foundations/CommAlg/DominatingDVRLift.lean`); then specializations lift in every base change, and
  a quasi-compact morphism with that property is submersive (Stacks 01K9 for images of closed
  sets). Krull–Akizuki and 7.1.7 are in
  `Foundations/CommAlg/{KrullAkizuki,KrullAkizukiFinite,DominatingDVR,DominatingDVRGeneral}.lean`
  (7.1.7 in full: `IsLocalRing.dominatingDVRStatement`; Krull–Akizuki for finite extensions of the
  fraction field: `KrullAkizuki.isNoetherianRing_of_finiteDimensional`).
- EGA II 7.1.7 and EGA 0_III 10.3.1 are also inputs to X.3.8 (XI-12), so building them serves
  more than one item.

## 5. Tame ramification, Abhyankar's lemma, X.3.8 (Exposés X, XIII)

### XIII.5.2 in mixed characteristic

- **What.** `AbsoluteAbhyankarStatement` (`lean/SGA/SGA1/ExposeXIII/AbhyankarBasic.lean`).
- **Proved.**
  - The extension part, for every regular local `A`: `absoluteAbhyankar_extension`
    (`AbhyankarDescent.lean`).
  - The full statement in equal characteristic: `absoluteAbhyankarAt_of_ringChar_eq`.
  - XIII.5.3 in every characteristic: `tameCoveringsOfStrictlyLocalStatement`.
  - XIII.5.4: `rootAdjunctionSmoothStatement`.
- **Missing** (TAME-8): in mixed characteristic over an `A` that is not strictly henselian, show
  that the `nᵢ` (lcm of the ramification indices) are prime to `p`. Plan: show that `e(Q)` divides
  the Kummer exponent, using multiplicativity of ramification indices in towers and a reduction
  to `A^sh`. Estimated at 1000+ lines.
- **Route used for the rest.**
  1. Reduce to codimension one with `exists_etale_of_forall_isEtaleAt` (`AbhyankarPurity.lean`).
     This uses purity from `lean/SGA/Foundations/CommAlg/Purity*.lean` in place of SGA 2
     XIV 1.11.
  2. Apply X.3.6 over the DVR `A_(f_j)` at height-one primes
     (`etale_integralClosure_of_forall_isTamelyRamifiedOver`).
  3. In mixed characteristic, descend through the strict henselization (TAME-5 to TAME-8).
- **Cost.** About 5000 lines over `Abhyankar*.lean`, with ten `maxHeartbeats` overrides, each
  with a comment. Before it was split, one 3500-line file took 130–140 s to compile.

### XIII.2.3 a) and XIII.2.4 1)

`TameRamificationAtMaximalPointsStatement` and `TameBaseChangeStatement`
(`lean/SGA/SGA1/ExposeXIII/NormalCrossings.lean`) need the relative Abhyankar lemma XIII.5.5,
which is stated (existence part, `RelativeAbhyankarStatement`,
`lean/SGA/SGA1/ExposeXIII/RelativeAbhyankar.lean`, 2026-10-04, xiii43) but not proved; it needs
étale depth (SGA 2 XIV 1.19/1.20). XIII.2.4 1) also needs cohomological properness (TAME-6).
Already proved:
- the characterization `isLocallyConstantConstructible_and_isTamelyRamifiedSheaf_iff`;
- locally constant constructible sheaves ≌ FEt, as `fetEquivLocallyConstantFiniteSheaf`
  (`lean/SGA/SGA1/ExposeXIII/LocallyConstantSheaves.lean`).

### X.3.8 (specialization of the tame fundamental group)

- **What.** `TameSpecializationStatement` (`lean/SGA/SGA1/ExposeX/TameSpecialization.lean`).
  X.3.9 follows from it (`exists_primeToQuotientEquiv_of_tameSpecialization`,
  `exists_bijective_of_tameSpecialization`).
- **Needs** (XI-12):
  - DVR domination (EGA II 7.1.7) and EGA 0_III 10.3.1;
  - the limit argument X.3.7, which is not stated, though its limit step is
    `Scheme.exists_iso_of_isPullback` (F-Limits);
  - Kummer base change, relative normalization, Abhyankar and purity, glued together;
  - IX.1.10.
- **Uncompiled WIP** (XI-12, only in the job scratch directory). It reduces X.3.8 over a
  complete noetherian local base to this statement:

  ```lean
  def TameLiftingCompleteLocalStatement : Prop :=
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (maximalIdeal R) R] ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of R)) [IsProper f]
      [Smooth f], (∀ U : (Spec (.of R)).Opens, IsIso (f.app U)) →
      ∀ (y₁ : Spec (.of R)) (Ω₁ : Type u) [Field Ω₁] [IsAlgClosed Ω₁]
        [Algebra (AlgebraicClosure ((Spec (.of R)).residueField y₁)) Ω₁] (Ω₁' : Type u)
        [Field Ω₁'] [IsSepClosed Ω₁'] (a₁ : Spec (.of Ω₁') ⟶ pullback f (geometricPointOf y₁ Ω₁)),
        FactorsPrimeTo
          (ExposeV.etaleFundamentalGroup.map Ω₁' (pullback.fst f (geometricPointOf y₁ Ω₁)) a₁)
          (ringExpChar ((Spec (.of R)).residueField (closedPt R)))
  ```

- **How the WIP uses it.** Its theorem `exists_tameSpecialization_of_completeLocal` takes `hT` (the
  statement above) and `hlift : ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint R))`. It builds
  a `SpecializationDiagram` from `injective_map_closedFibre_of_completeLocal`,
  `range_map_eq_ker_map_closedFibre_of_completeLocal` and `ker_map_le_range_map_geometricPointOf`
  (all in `lean/SGA/SGA1/ExposeX/SpecializationGeometric.lean`). It also adds four new lemmas:
  - `SpecializationDiagram.factorsPrimeTo`: if every map of `π₁` to a finite group of order prime
    to `q` factors through `i₁`, it factors through the specialization map;
  - `FactorsPrimeTo.comp_continuousMulEquiv`;
  - `geometricallyReduced_of_smooth`;
  - `isSeparable_of_smooth`.
- **`hlift`.** This hypothesis is IX.1.10 for the closed fibre. `liftsFiniteEtale_of_essSurj`
  (`lean/SGA/SGA1/ExposeIX/FiniteEtaleLimit.lean`) derives it from essential surjectivity, which
  is proved for projective `X`.
- **Left.** Prove the tame lifting statement. SGA reduces to a complete DVR with algebraically
  closed residue field (X.3.7), then applies purity (X.3.1, X.3.4) and Abhyankar (X.3.6).
- **Update (2026-10-03, xiii43).** The `hlift`/X.2.1 obstacle is gone for normal `X`:
  `ExposeX.isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme` and
  `liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme` (`ExposeX/NormalCompleteLocalBase.lean`,
  Chow + `formalAlgebraizable_of_stein`). The DVR target is now stated as
  `ExposeX.TameLiftingDVRStatement` (`ExposeX/TameLifting.lean`, separably closed residue field,
  specific map). Proved so far: the π₁ glue (`ExposeX/TameLiftingReduction.lean`, reduces to "Galois
  coverings of `X_η̄` of degree prime to `p` come from `X`"), `FEt(X) ≃ FEt(X_{R'})` for
  purely inseparable residue extensions and for `R[T]/(Tⁿ - π)` (`TameLiftingBaseChange`,
  `TameLiftingKummer`), finiteness of integral closures in finite étale algebras
  (`TameLiftingAlgebra`). Left: the extension over the generic point of the closed fibre and its
  gluing, the descent from `X_η̄` to `X_{K'}`; plan in `notes/log/2026-10-03-xiii43-round1.md`.
- **Update (2026-10-04, xiii43).** The geometric core is proved:
  `ExposeX.exists_iso_pullback_adjoinRoot_of_isGalois` (`TameLiftingExtension.lean`): a Galois
  covering with `n` automorphisms (`n` prime to `p`) of the generic fibre of `X` proper smooth over a
  DVR extends to `X ×_V V[T]/(Tⁿ - π)`; over a complete `V` it then comes from `FEt(X)`
  (`exists_iso_pullback_of_isGalois_of_isAdicComplete`). Galois-ness reaches the function field via
  the Galois category of `Spec Γ(chart)` (`TameLiftingGalois.lean`), tameness via inertia orders.
  Left for `TameLiftingDVRStatement`: descend a Galois covering of `X_{Ω₁}` to `X_{K'}` (`K'/K`
  finite separable; X.1.8 + `Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale` + IX.4.10),
  pass to `V'` = normalization of `R` in `K'` (`TameLiftingNormalization.lean`), assemble.
  Lean lesson (keep canonical pullbacks out of unification problems): see `strategy.md`.
- **Update (2026-10-04, xiii43, round 3). The core is proved:**
  `ExposeX.tameLiftingDVRStatement : TameLiftingDVRStatement` (`ExposeX/TameLiftingProof.lean`).
  - The descent of a Galois covering of `X_Ω` to a Galois covering of `X_{K₀}` is
    `exists_isGalois_finiteDimensional_of_isGalois` (`TameLiftingFiniteLevel.lean`). The automorphisms
    descend because every endomorphism descends (`exists_liftsEndos_of_isLimit`,
    `TameLiftingDescent.lean`).
  - Consequences, over complete DVRs with separably closed residue field:
    - the second part of XIII.4.4 (`ExposeXIII.properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`);
    - X.3.8/X.3.9 for `y₀` closed, `y₁` generic
      (`ExposeX.exists_tameSpecialization_of_isDiscreteValuationRing`, `TameLiftingSpecialization.lean`).
  - **Resolved (2026-10-04, xiii43, wave 2): `TameSpecializationStatement` is proved over every
    locally noetherian `Y`**, `ExposeX.tameSpecializationStatement` (`ExposeX/TameLiftingGeneral.lean`).
    The passage to a complete DVR uses local-alg's EGA II 7.1.7
    (`IsLocalRing.exists_isDiscreteValuationRing_dominating`, row A41) and the completed strict
    henselization (`ExposeX.exists_isAdicComplete_isDiscreteValuationRing`, row A45). Existence form:
    up to an inner automorphism the map built is SGA's specialization map, which the statement does
    not record. X.3.9 follows by `exists_primeToQuotientEquiv_of_tameSpecialization`.

## 6. Étale sheaves, torsors, XIII §1

- **Not formalized and not tracked as statements** (see the module docstring of
  `lean/SGA/SGA1/ExposeXIII/CohomologicalProperness.lean`):
  - XIII 1.7 and 1.9 in dimension ≤ 0;
  - dimension ≤ 1 for sheaves of groups;
  - XIII 1.13 2)–3);
  - XIII 1.10–1.17, apart from 1.13 1).
- **Why.** SGA defines cohomological properness for stacks, and nothing here provides inverse
  images or stackification of stacks on étale sites. So for groups, condition (ii) of XIII 1.3.1
  is used as the definition (`IsCohomologicallyProperLENegOneGroup`, and the `…LEZero…`
  version). Its `R¹` clause first concluded "locally isomorphic over all of `Y₁`" from a
  hypothesis over `Y'₁` only, which for `Y' = ∅` forced any two torsors to be locally isomorphic;
  since 2026-10-04 it concludes only at points `g₁ y'` over `Y'` (`IsLocallyIsoOverAt`; see the
  docstring of `IsCohomologicallyProperLEZeroGroup`). The cases in dimension ≤ 0 need `Q ↦ P` to
  be compatible with base change, and 1.13 2)–3) need quotient sheaves `Q/F` (F-Etale-5).
  F-Etale-4 estimated about 1000 lines.
- **`IntegralBaseChangeStatement`** (SGA 4 VIII 5.6). The finite case is
  `isIso_etaleBaseChangeMap_of_isFinite` (`lean/SGA/Foundations/EtaleStalkBaseChange.lean`). The
  integral case needs SGA 4 VII 5.7, étale sheaves on a limit of schemes. The algebraic input,
  that étale algebras over an integral algebra come from a finite subalgebra, is already in
  `lean/SGA/Foundations/Limits/IntegralApproximation.lean` (F-Hens-4). Since 2026-10-04 (xiii14,
  xiii3) VII 5.7 in degree 0 has its surjectivity half (`Scheme.exists_toLimitSections_eq`) and
  the stalk criterion through strict localizations is proved (registry A2, A31), which reduces the
  statement to `Γ(Spec B, F) ≅ Γ(Spec B/𝔪B, F)` for `B` integral over a strictly henselian `A`.
  Plan, and the missing "integral over henselian ⇒ henselian pair", in
  `../log/2026-10-04-xiii14-round3-gabber-xiii14-noetherian.md`.
- **Technical blockers.**
  - `H¹` and `R¹f_*` live in `Type (u+1)` (F-Etale).
  - The `R¹` base change map is stuck on a universe and naturality problem (F-Etale-3,
    F-Etale-4).
  - Mathlib has no colimits of non-abelian `GrpCat` (F-Etale).
  - `Pic ≃ H¹(X_et, 𝔾_m)` is not formalized. Exposé XI proves the fpqc version,
    `h1GmMulEquivPic` (`lean/SGA/SGA1/ExposeXI/PicardComparison.lean`), from Hilbert 90
    (`isLocallyTrivial_Gm`, `ExposeXI/MultiplicativeTorsors.lean`). The docstring of
    `lean/SGA/Foundations/Etale/Picard.lean` now says so (fixed 2026-10-03, claude-1003).

## 7. Henselization and strict localization (mostly resolved)

- **Built from scratch** (F-Hens):
  - `IsLocalRing.Henselization`;
  - `StrictHenselization R K`, as a direct limit of étale neighbourhoods;
  - `IsStrictlyHenselian`;
  - strict localization at a geometric point;
  - finite étale algebras over a henselian ring ≃ over its residue field:
    `isEquivalence_baseChange_residueField` (`lean/SGA/Foundations/HenselianFiniteEtale.lean`).
- **RESOLVED: noetherianity** (Stacks 06LJ). It blocked XIII 2.0.2 and X.3.2 for quasi-finite
  `B` for about two days (2026-09-25 to 2026-09-27). Now `Henselization.isNoetherianStatement`
  and `StrictHenselization.isNoetherianStatement` (`lean/SGA/Foundations/HenselizationNoetherian.lean`,
  F-Hens-3).
- **Étale stalks.**
  - The stalk of `𝒪_et` is `O^sh`: `etaleStructureStalkIso`.
  - Finite pushforward stalks (SGA 4 VIII 5.5): `Scheme.Hom.bijective_etalePushforwardStalkMap`
    (`lean/SGA/Foundations/EtaleStalkPushforward.lean`).
- **Still missing:** henselian pairs (F-Hens).

## 8. Complex analytic geometry (Exposé XII)

- **Out of scope:** GAGA and Riemann existence (XII.5.1), see "Out of scope" below. XII.5.2 needs
  no triangulation (2026-10-04, xii52).
- **In scope but not done**, and not recorded as statements (XII barrel docstring):
  - RESOLVED for separated `X` (2026-10-03, xii4): the non-affine `X^an`, glued with
    `LocallyRingedSpace.GlueData` from the charts of all affine opens (about 900 lines,
    `SGA1/ExposeXII/AnalyticGluing.lean`), and `f^an` (`AnalyticGluingMap.lean`). The cocycle is
    cheap if you identify the fibre products with the triple-intersection charts
    (`isIso_tripleToPullback`); `f^an` needs re-gluing along affines mapping into affines
    (`isIso_gluedToAnalytic`). Non-separated `X` is still open;
  - RESOLVED (2026-10-03, xii4): XII.3.1 (i)–(iii) for separated `X`
    (`SGA1/ExposeXII/MorphismComparisonGlobal.lean`); (iv) (2026-10-04,
    `MorphismComparisonSmooth.lean`); XII.3.2 (i), (ii), (v) (direct, topological) and XII.3.1
    (vii) (one direction) for `f^an` by transport along `pointsHomeomorph`
    (`MorphismComparisonPoints.lean`). Round 3 (2026-10-04): XII.3.1 (ix)
    (`isIso_iff_isIso_analyticMap`, `MorphismComparisonIso.lean`) and (xi)
    (`isOpenImmersion_iff_isOpenImmersion_analyticMap`, `MorphismComparisonOpenImmersion.lean`),
    both for quasi-compact `f`; XII.3.2 (vi) direct (`isFiniteMap_analyticMap`). The trick for (ix)
    and (xi): no inverse function theorem is needed. For the direct direction of (xi), `f` is
    locally the inclusion of a basic open, so `f^an` is in the charts the analytification of a
    localization. For the converses, `f` is étale (stalk isos, XII.3.1 (iii)) and injective on
    `ℂ`-points; corestrict to the open image and use xii51's `SchemePoints.isIso_of_bijective_map`.
    Still open: (v), (vi) (they need normality descent along faithfully flat maps and the ascent,
    i.e. excellence), the converse of (vii), (viii) and (x) (fibre products of analytic spaces),
    XII.3.2 (iii), (iv), converse of (v), (vi), XII.5.3–XII.5.5;
  - RESOLVED (2026-10-04, xii4): the analytic heart of curve RET, Forster 14.13
    (`AnalyticGeometry.exists_meromorphic_single_pole`; `compactRiemannSurfaceMeromorphic :
    CompactRiemannSurfaceMeromorphicStatement`). Forster 14.9 with sup norms instead of `L²`:
    Dolbeault for compact support via the Cauchy transform (mathlib's convolution API does the
    smoothness; the generalized Cauchy formula is one polar-coordinates computation), L. Schwartz
    by the iteration of the open mapping theorem, Montel by Arzelà–Ascoli plus mathlib's Schwarz
    lemma in charts, mathlib's smooth partitions of unity after showing that a complex manifold is
    a real one (`isManifold_real_of_complex`). About 2000 lines in `Foundations/Analytic/`;
  - RESOLVED (2026-10-04, xii4, registry C8a): filling in the punctures of a finite covering of
    `ℂ ∖ S`, `puncturedPlaneCompactification : PuncturedPlaneCompactificationStatement`
    (`SGA1/ExposeXII/GAGAFiberSeparating.lean`). With xii51's derivations, XII.5.1 is now
    unconditional for `ℂ ∖ S` and its finite étale covers (`PuncturedPlane.riemannExistence_coordRing`,
    `…_finiteEtale`), and so is the genus-0 `π₁` (`…etaleFundamentalGroup_mulEquiv_completion_freeGroup`).
    About 1000 lines (`Foundations/Analytic/RiemannSurface{Punctures,Compactification}.lean`).
    How it was kept short: see "Building a manifold by hand" in `strategy.md`; compactness comes
    from `IsCoveringMap.isProperMap_of_finite` (a covering with finite fibres is proper).
  - the irreducibility half of XII.2.4, which needs analytic irreducible components (XII-4);
  - ascent of reducedness and normality, which needs excellence (XII-3);
  - RESOLVED (2026-10-04, an-coh): Oka coherence, `AnalyticGeometry.okaCoherence`
    (`Foundations/Analytic/Oka.lean`; the Weierstrass half came from the unmerged branch
    `codex/foundations-missing-inputs`), with Hilbert's syzygy theorem for the stalks and local
    finite free resolutions (`Syzygy*.lean`). Open (an-coh): Theorems A and B for coherent
    sheaves, Cartan–Serre (registry row C10). RESOLVED (2026-10-04, an-cohom): Theorem B for `𝒪` on
    `Δ × ℂᵃ × (ℂ*)ᵇ` (`AnalyticGeometry.polydiscProductVanishing`), on products of discs, planes,
    punctured planes and open rectangles (`H'_holomorphicAbSheaf_pi_subsingleton`), and near
    compact boxes (`TheoremB.lean`). Route: Cartan's criterion for covers indexed by arbitrary
    types (`Cohomology/CartanInfinite.lean`; the repo's `TopCat.Sheaf.H'_subsingleton_of_cech`
    needs finite refining families, which a non-compact open set never has), the Dolbeault
    resolution of `𝒪` by fine sheaves of coordinate `(0,q)`-forms, the Dolbeault–Grothendieck
    lemma near compact products (parametric Cauchy transform), and Hörmander's exhaustion
    argument; degree `0` needs Runge approximation, by truncated Laurent expansions (annuli) and
    Cauchy integrals over the sides of rectangles, with holomorphic parameters, one coordinate at
    a time (`RungeScheme.lean`). Done (2026-10-04, xii4): Cousin I on a disc for arbitrary covers
    (`AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`, `Foundations/Analytic/Cousin.lean`,
    about 250 lines: mathlib's `SmoothPartitionOfUnity` on the open submanifold `B`, moved to `ℂ` with
    `contMDiffAt_subtype_iff`, plus `exists_contDiffOn_dbar_eq_ball`). The factors `ℂ` and `ℂ*` of
    `PolydiscProductVanishingStatement` needed `∂̄` on the plane and on annuli (Runge): done, see
    above.
- **Exists** (`lean/SGA/Foundations/Analytic/`):
  - convergent power series, and Weierstrass division and preparation;
  - `𝕜{X}` noetherian and henselian;
  - local models;
  - affine analytification with its universal property (`existsUnique_comp_toSpec`);
  - `completionEquiv`, and flatness of `φ`;
  - Rückert's Nullstellensatz (`rueckertPrime`);
  - open subspaces, and principal opens (`principalOpenIso`).

## 9. Galois categories and π₁: leftovers (Exposés V, IX §5)

None of these is recorded as a statement:
- V.5.9 and V.5.11 are done only for small Galois categories. The general case needs `Π` as a
  group object (F-Pro-3).
- V.8.2 is done only for `Spec R` (PI1).
- V.9 is done only for finitely many connected components (PI1).
- IX.5.3–IX.5.5 and IX.5.7 need topologically finitely presented profinite groups and free
  profinite products (IX-b). IX.5.2 for disconnected `S'`, `S''` (finite-generation form) and the
  finite-generation consequence of IX.5.4 are proved since 2026-10-04 (x29,
  `ExposeIX/DescentFiniteGeneration.lean`, `ExposeIX/Pinching.lean`; registry A12).
- `DecompositionInertiaEtaleStatement` (`lean/SGA/SGA1/ExposeV/DecompositionInertia.lean`) is
  still stated with `Type`, i.e. universe 0. REVIEW-1 asked for `Type u`.

## 10. Multiplicity theory (Exposé II)

II.2.5 (Hironaka's flatness criterion) and the sufficiency half of II.2.6 need multiplicity theory.
Neither is stated (II-6, REVIEW-1). Necessity in II.2.6 is in
`lean/SGA/SGA1/ExposeII/FibreMultiplicity.lean`.

## Out of scope

The reference for what is proved and what is missing in each item is the table in
[`lean/SGA/Foundations/README.md`](../../lean/SGA/Foundations/README.md); owners and shared
prerequisites are in [`out-of-scope-plan.md`](out-of-scope-plan.md). Each item stays a faithful
`…Statement`, and its consequences are proved from it. Wave 1 of the campaign (2026-10-03/04,
13 streams) proved none of these statements in full (checked 2026-10-04, sga1-oos-coord). The
triage's cheaper routes (`../log/2026-10-03-sga1-oos-out-of-scope-triage.md`) held: X.2.9 in
characteristic 0 needs no Riemann existence, XII.5.2 no triangulation, XIII.4.6 no resolution.
Below, for each item: the main results, and what is hard in the rest.

- **X.2.9, X.2.12** (`TopologicallyFiniteStatement`). Proved in characteristic 0 for `#k ≤ 𝔠`,
  universe 0 (`ExposeX.isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`,
  `finite_principalH1_of_mk_le_continuum`). In every characteristic, X.2.9 follows from the curve
  case and X.2.10 (`topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`). Hard:
  X.2.10 (Bertini; no formalizable proof of the Matsusaka–Zariski field lemma found yet); the
  curve case in characteristic `p`, where SGA lifts the curve by III.7.4 (§1) and this
  formalization plans a plane model, its lift to `W(k)` and pinching instead (registry A12, A29,
  A39; missing: the finite birational map onto `planeCurve`, `𝔭 = (F)`, the lift); `#k > 𝔠`;
  universes above 0. Handoff: `../log/2026-10-04-x29-round3-charzero-pinching-planemodel.md`.
- **XI.1.4** (`SerreUnirationalSimplyConnectedStatement`). Reduced to `HodgeSymmetryZeroStatement`
  (`h^{0,q} = h^{q,0}`) by `ExposeXI.serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`;
  the other steps hold in every characteristic, with no Riemann–Roch (`χ(𝒪)` multiplicative in
  finite étale coverings: `eulerCharFiniteEtaleStatement`). Hard: Hodge symmetry for `q ≥ 1` is
  analytic Hodge theory (Lefschetz principle, GAGA, Dolbeault, harmonic forms on compact Kähler
  manifolds), far beyond the analytic layer of §8. Route: `../log/2026-10-03-xi14-serre-unirational.md`.
  Wave 2 (2026-10-04, stream `hodge`): interfaces `ExposeXI.HodgeSymmetryZeroComplexStatement` (over
  `ℂ`, projective `X`), `Hodge.CompactKahlerHodgeSymmetryStatement`, `Hodge.DolbeaultIsomorphismStatement`;
  proved foundations in `Foundations/Hodge` (forms of type `(p,q)`, `∂`, `∂̄`, Dolbeault cohomology,
  Kähler forms, integration and Stokes on compact complex manifolds). Still open: wedge product and
  Leibniz, Kähler linear algebra (Hodge–Riemann), elliptic theory (the long pole), Dolbeault
  isomorphism, `X(ℂ)` as a manifold. Note: `HodgeSymmetryZeroStatement` is stated for proper `X`;
  Kähler Hodge theory covers projective `X` only (SGA's XI.1.4 is for projective `X`).
- **XI.2.1** (`AbelianVarietyFundamentalGroupStatement`, `AbelianVarietyPrimaryComponentStatement`).
  RESOLVED: the key step `SerreLangStatement` (`serreLangStatement`, 2026-10-03, sga1-xi21), with
  no abelian-variety theory. Proved: characteristic 0 (`exists_tateModule_equiv_of_charZero`), the
  `ℓ`-primary clause for every prime `ℓ ≠ char k` (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`),
  and all of XI.2.1 from "`n_A` is an isogeny" (`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`).
  Open: the `p`-primary clause in characteristic `p`, to which XI.2.1 is equivalent there
  (`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`). It follows from `p_A`
  finite and surjective, which needs the theorem of the cube and an ample line bundle. No
  elementary route is known: `𝔾_a` is killed by `p`, so properness must enter, and excluding an
  abelian subvariety `B` killed by `p` needs `T_ℓ(B) ≠ 0`, i.e. degree theory. XI.2's disconnected
  principal coverings (`Ext(A, G) ≅ H¹(A, G)`) are not done.
- **XII.3.1, XII.4 (GAGA).** See §8. Hard: Theorem B on polydiscs and Oka coherence
  (`PolydiscProductVanishingStatement`, `OkaCoherenceStatement`), Cartan–Serre finiteness, and
  `Rᵖf_*` on both sides before XII.4.1–4.2 can be stated.
- **XII.5.1** (`RiemannExistenceStatement`, `SchemeRiemannExistenceStatement`). Proved: `Ψ` fully
  faithful, `π̂₁(X(ℂ)) ↠ π₁(X)`, scheme form ⇔ affine form (`schemeRiemannExistence_iff`), any
  universe (`riemannExistence_iff_zero`); RET for `X(ℂ)` simply connected, for `𝔾_m`, and for
  `ℂ ∖ S` and its finite étale covers (`PuncturedPlane.riemannExistence_coordRing`, from xii4's
  `puncturedPlaneCompactification`). Hard: all smooth curves (extending a covering across finitely
  many points, i.e. the normalization of `X` in `Y'` is étale over them, and reducing a smooth
  affine curve to a finite étale cover of some `ℂ ∖ S`), singular curves (normalization descent),
  higher dimension (resolution, or a hypersurface-complement analogue of the `ℂ ∖ S` argument plus
  `ExposeX.purityCoverings`). Handoff: `../log/2026-10-04-xii51-round3-punctured-plane.md`.
  - RESOLVED for curves (2026-10-04, xii51, registry C8/C26): `curveRiemannExistence :
    CurveRiemannExistenceStatement` (any affine `A` of dimension `≤ 1`, singular, reducible,
    non-reduced; scheme form `schemeCurveRiemannExistence`; XII.5.2 for curves
    `curveFundamentalGroupComparison`), `SGA1/ExposeXII/RiemannCurvesExistence.lean`. What made
    it short (about 2700 lines over two rounds, a third of them general topology): the extension
    across a puncture needs **no holomorphy and no Puiseux**. A uniformizer is an étale
    coordinate (algebra), so punctured neighbourhoods are connected; the covering map then
    extends continuously and injectively to the normalization `C` of `B` in `C'` (general
    topology); and `C` is étale by **counting
    points** with mathlib's `∑ e f = rank` (`n` distinct points over `p` force `e = f = 1`). The
    normalization is finite and Dedekind by mathlib's trace-form theorems once it is presented as
    `IsIntegralClosure C B (Frac C')`. Singular curves come from descent along
    `A → ∏_{p minimal} normalization(A/p)` (finite and surjective on spectra, so the nilradical
    needs no separate topological-invariance step), together with XII.5.1 for finite products.
    Handoff: `../log/2026-10-04-xii51-wave2-round2-curves-proved.md`.
  - Higher dimension (2026-10-04, ret-hd, registry C20): Artin's elementary fibrations (SGA 4 XI)
    need `π₁` of a fibre to inject into `π₁` of the total space *étale*-ly, which is the
    out-of-scope XIII.4.4 third part (and even middle exactness is); topology alone does not
    supply the étale side. Route taken instead: hypersurface complements by induction on the
    dimension through the family of punctured lines over `𝔸^{d-1} ∖ V(disc)`, an algebraic
    parameter space of fibrewise covers (made algebraic by curve RET on each fibre), Baire + a
    quasi-section over a dense open of the base, and the covering of fibrewise isomorphisms,
    made algebraic by RET in dimension `d - 1`; then divisor extension and Noether normalization.
    Done: descent (C29), the reduction of smooth domains, `d ≤ 1`, and the topology (local
    triviality of `ℂ` minus moving points, transport of coverings, clopen matching locus). Open:
    the parameter algebra, the quasi-section, the fibrewise-trivial descent, divisor extension in
    dim `≥ 2`, normal `X` (needs local irreducibility of normal varieties, C30). Handoff:
    `../log/2026-10-04-ret-hd-round1.md`.
- **XII.5.2 for singular `X`** (`LocallyContractibleStatement`). No triangulation is needed:
  XII.5.2 holds for every connected `X` given XII.5.1
  (`ExposeXII.schemeFundamentalGroupComparison_of_riemannExistence`), because SGA uses only that
  `X(ℂ)` is locally path-connected and semilocally simply connected, both proved by semialgebraic
  geometry. The literal statement (a basis of contractible neighbourhoods) is open for singular `X`
  of dimension `≥ 2`, needs the local conic structure (Hardt triviality or triangulation), and is
  not used; classical local contractibility does not imply it (Borsuk's example).
- **XIII 1.4** (`ProperBaseChangeStatement`). Proved for every sheaf of sets over a locally
  noetherian base (`ExposeXIII.isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`),
  through Gabber's theorem over a noetherian henselian base (`properHenselianSectionsStatement`).
  Hard: an arbitrary base (EGA IV 8 spreading out plus constructible sheaves, or Gabber over
  non-noetherian henselian rings, which needs Stacks 09Z0 and clopen lifting without noetherian
  hypotheses); essential surjectivity in `HenselianEtaleCoveringsOfClosedFibreStatement` (no route
  short of Grothendieck existence plus Artin approximation); `IntegralBaseChangeStatement` (§6).
  Handoff: `../log/2026-10-04-xiii14-round3-gabber-xiii14-noetherian.md`.
- **XIII.4.3, XIII.4.4** (`ProperSmoothHomotopyExactSequenceStatement`, the two normal-crossings
  statements). The second part of XIII.4.4 holds over a field, at closed points of complete
  regular local bases, and, from the X.3.8 core (`ExposeX.tameLiftingDVRStatement`), over a
  complete DVR with separably closed residue field
  (`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`).
  Hard: a general base (finiteness when the base is not geometrically unibranch; X.3.8 itself is
  proved over every locally noetherian base, `ExposeX.tameSpecializationStatement`, §5); regular bases (`ProperSmoothHomotopyExactSequenceRegularStatement`, estimated
  5–8.5k lines); the third part, which needs XIII.5.5 (`RelativeAbhyankarStatement`, stated; needs
  étale depth, SGA 2 XIV 1.19/1.20) and XIII.2.9. Handoff: `../log/2026-10-04-xiii43-round3.md`.
- **XIII §3** (`ExposeXIII/LocalAcyclicity.lean`). 3.2 1) is proved for every field
  (`fieldCohomologicalPropernessStatement`); 3.3 and 3.4 for étale `f`, and for smooth `f` given
  SGA 4 XV 2.1; SGA's desingularization hypotheses in dimension `≤ 1` over perfect fields
  (`desingularizableUpTo_one`, `stronglyDesingularizableUpTo_one`). Hard: SGA 4 XV 2.1
  universally (smooth ⇒ universally locally acyclic in degrees 0 and 1; no route short of SGA 4
  XV's reduction to curves); XV 4.1 in degree 0 (Stacks 0EYS needs 37.38.8 / 37.46.3, openness of
  the connected component along a section, EGA IV 15.6); degree-1 proper base change for 3.1 2). The
  converse comparison (base-change form ⇒ Milnor form) is a few hundred lines on top of registry
  A31. Handoff: `../log/2026-10-04-xiii3-round3.md`.
- **XIII.4.6 in characteristic 0** (`KunnethCharZeroStatement`). The surjectivity half holds in
  every characteristic (`surjective_map_prod_of_isAlgClosed`); a resolution-free route reduces
  normal schemes of finite type to `AffineLineOpenInvarianceStatement` (invariance for opens of
  `𝔸¹`). That statement is proved (2026-10-04, wave 2 round 2,
  `affineLineOpenInvarianceStatement` in `SGA1/ExposeXIII/KunnethCurveInvariance.lean`: Kummer
  cover, compactification by normalization, Abhyankar in dimension 1, purity, X.1.8, about 2500
  lines over seven files). Still hard: descent to non-normal `X`, `Y`, and qcqs `X` with arbitrary
  `Y` and base points. Blueprint: `../log/2026-10-04-xiii46-kunneth-round3.md` §5 and
  `../log/2026-10-04-xiii46-wave2-round2.md`. "Smooth over normal is normal" is II.3.1
  (`ExposeII/PermanenceSmooth.lean`), not new.
- **XIII.2.12** (`TameCurveFundamentalGroupStatement`, `TameCurvePrimeToPStatement`). Proved on
  `ℙ¹` for `(g, n) = (0, 0)`, `(0, 1)`, and `(0, 2)` with inertia
  (`tameCurvePrimeToPConclusion_projectiveLine_two`); `π₁^{p'}(𝔾_m) = Ẑ^{(p')}`; *Galois* coverings
  of degree prime to `p` are tame (`galoisCoveringsTameStatement`, hence
  `primeToPCoveringsTameStatement`), so XIII.2.12 implies its "in other words" form. Without
  "Galois" this is false: in characteristic 2 a degree-3 subcover of an `S₃`-covering of `𝔸¹`
  (XIII.2.13 for `S₃`) has degree prime to `p` but is not tame, since `π₁^tame(𝔸¹) = 1`. Hard:
  general `(g, n)`. Characteristic 0 needs Riemann existence for curves, surface topology (genus
  `≥ 1` needs the classification of surfaces; genus 0 lacks the loop around `∞`) and, for the
  inertia condition, a comparison of strict localizations with punctured discs that nobody has.
  Characteristic `p` also needs III.7.4 and tame specialization.
- **XIII.2.13** (`AbhyankarAffineLineStatement`, Raynaud's theorem). Proved: `p`-groups, `S₃`
  (`p = 2`), `A₄` (`p = 3`), Serre's `p`-kernel theorem (`SerrePKernel.affineLinePExtension`), and
  the reduction to Raynaud's two cases (`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`).
  Case A (`AffineLinePatchingStatement`) follows from Harbater–Stevenson's Theorem 6 (formal
  patching) and Abhyankar's lemma; the patching layer, with HS's nodal model, is in
  `Foundations/Patching/` (registry A32). HS's node lemma (`π₁` form) and the étale lifting over
  `K⟦t⟧` are done (xiii213, 2026-10-04, wave 2). Case A is reduced to four statements
  (`affineLinePatching_of_statements`, `SGA1/ExposeXIII/AbhyankarAffineLinePatching.lean`):
  Abhyankar's lemma at `∞`, HS's nodal patching over `k((t))` (still missing: torsors as
  `σ`-stable forms, geometric connectedness and branch-locus control of the patched algebra),
  base change to an algebraically closed extension, and specialization `K → k` (Chevalley or
  EGA IV 9.7.7). Base change is proved (`affineLineBaseChange`, wave 2 round 2). For Abhyankar's
  lemma, the global half is proved (connected coverings of `𝔸¹` stay connected under `x ↦ xᵐ`,
  `AffineLinePGroups.isConnected_bcRingHom_expand`); the local half (the tame inertia at `∞` dies
  in `k((y^{1/m}))`) is planned via XIII.2.0.1, Kummer and Hensel (plan in
  `../log/2026-10-04-xiii213-w2r2-base-change.md`). Case B (`AffineLineCaseBStatement`) needs
  Riemann existence for curves (proved by xii51, `curveRiemannExistence`), semistable reduction
  (`SemistableReductionStatement`, open, stream `semistable`) and Raynaud's tail analysis (not
  started). Roadmap: `../log/2026-10-04-xiii213-round3-nodal-patching.md`.
