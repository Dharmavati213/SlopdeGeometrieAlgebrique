---
updated: 2026-10-03
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
2026-10-03, every `…Statement` named as open below was checked to still be an unproved `def`.
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
  (`lean/SGA/SGA1/ExposeIX/EtaleEffectiveDescent.lean`).
  - Proved in `StrictlyLocalDescent.lean` with separably closed residue fields
    (`DescentDatum.isEffective_iff_forall_isSepClosed`; enough for étale descent), and with
    algebraically closed ones when the residue fields are perfect
    (`isEffective_iff_forall_isAlgClosed`).
  - Missing: EGA 0_III 10.3.1, a flat local extension of a complete local ring realizing a
    purely inseparable residue field extension.
- **IX.4.9 input**, `QuasiSectionStatement` (`lean/SGA/SGA1/ExposeIX/UniversallyOpenDescent.lean`):
  quasi-sections of universally open morphisms (EGA IV 14.3.13, 14.5.4). The rest of SGA's
  argument is formalized, and `effectiveDescentOfUniversallyOpen` is proved from it (IX-8).
- **IX.2.6 sufficiency**, `UniversallySubmersiveValuativeCriterionStatement`
  (`lean/SGA/SGA1/ExposeIX/Submersive.lean`). It needs Krull–Akizuki, DVRs dominating a noetherian
  local domain (EGA II 7.1.7), and an argument from Rydh (IX-8). Necessity is
  `not_isOpen_preimage_closedPoint`.
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
which is not formalized. XIII.2.4 1) also needs cohomological properness (TAME-6). Already proved:
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
  version). The cases in dimension ≤ 0 need `Q ↦ P` to be compatible with base change, and 1.13
  2)–3) need quotient sheaves `Q/F` (F-Etale-5). F-Etale-4 estimated about 1000 lines.
- **`IntegralBaseChangeStatement`** (SGA 4 VIII 5.6). The finite case is
  `isIso_etaleBaseChangeMap_of_isFinite` (`lean/SGA/Foundations/EtaleStalkBaseChange.lean`). The
  integral case needs SGA 4 VII 5.7, étale sheaves on a limit of schemes. The algebraic input,
  that étale algebras over an integral algebra come from a finite subalgebra, is already in
  `lean/SGA/Foundations/Limits/IntegralApproximation.lean` (F-Hens-4).
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

- **Out of scope:** GAGA, Riemann existence (XII.5.1), triangulation (see the README).
- **In scope but not done**, and not recorded as statements (XII barrel docstring):
  - the non-affine `X^an`: gluing analytic spaces, estimated at 2000+ lines with `GlueData` for
    locally ringed spaces (F-Analytic-4);
  - XII.3.1 (i)–(vi) and XII.5.3–XII.5.5;
  - the irreducibility half of XII.2.4, which needs analytic irreducible components (XII-4);
  - ascent of reducedness and normality, which needs excellence (XII-3);
  - Oka coherence, never attempted (F-Analytic-4).
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
  profinite products (IX-b).
- `DecompositionInertiaEtaleStatement` (`lean/SGA/SGA1/ExposeV/DecompositionInertia.lean`) is
  still stated with `Type`, i.e. universe 0. REVIEW-1 asked for `Type u`.

## 10. Multiplicity theory (Exposé II)

II.2.5 (Hironaka's flatness criterion) and the sufficiency half of II.2.6 need multiplicity theory.
Neither is stated (II-6, REVIEW-1). Necessity in II.2.6 is in
`lean/SGA/SGA1/ExposeII/FibreMultiplicity.lean`.

## Out of scope

The full table, with files, is in [`lean/SGA/Foundations/README.md`](../../lean/SGA/Foundations/README.md).
The README was written at the user's request on 2026-09-27 (deps.md). Each item stays a
faithful `…Statement`, and its consequences are proved from it.

- X.2.9 `TopologicallyFiniteStatement`: uses the transcendental X.2.6 (Riemann existence over ℂ).
- XI.1.4 `SerreUnirationalSimplyConnectedStatement`: needs Hodge theory in characteristic 0 and Riemann–Roch.
- XI.2.1 `SerreLangStatement`: needs the theory of abelian varieties (rigidity, isogenies).
- XII.5.1 `RiemannExistenceStatement`, `SchemeRiemannExistenceStatement`: need GAGA and Grauert–Remmert.
- XII.5.2 for singular `X`, `LocallyContractibleStatement`: needs triangulation of complex varieties.
- XIII 1.4 `ProperBaseChangeStatement`: is the proper base change theorem (SGA 4 XII 5.1).
- XIII.4.3 and the second and third parts of XIII.4.4: need local constancy of `R¹f_*` (XIII.1.16) and XIII.2.9.
- XIII §3: needs local acyclicity (SGA 4 XV).
- XIII.4.6 in characteristic 0, `KunnethCharZeroStatement`: needs resolution of singularities.
- XIII.2.13, `AbhyankarAffineLineStatement`: is Raynaud's theorem.
- XIII.2.12 for general `g`, `n`: needs lifting to characteristic 0 plus Riemann existence. The
  case `g = 0`, `n = 1` is proved algebraically.
