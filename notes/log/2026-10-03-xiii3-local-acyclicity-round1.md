---
author: xiii3
date: 2026-10-03
area: SGA1 XIII §3, Foundations/Etale, Foundations/StrictLocalization, xiii14, sga1-oos-coord
kind: handoff
---

# XIII §3 round 1: strict-localization map, local acyclicity definitions, statements of 3.1–3.5

All four new files build (`lake build SGA.SGA1.ExposeXIII.LocalAcyclicity` pulls them all), no
sorry, axioms only propext/choice/Quot.sound. No existing file was edited. Not yet in any barrel.

**Done.**
- `lean/SGA/Foundations/StrictLocalizationFunctorial.lean` (registry A10, proved):
  `Scheme.Hom.strictLocalizationMap f x̄ : Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,x̄≫f}`, its two
  compatibilities, uniqueness `eq_strictLocalizationMap`, `isIso_strictLocalizationMap` for `f`
  étale, `strictLocalizationMap_comp`. Underneath: the universal property
  `Scheme.Hom.existsUnique_lift_strictLocalization` (henselian local `Spec A` with a local
  `α : A → Ω`, plus a residue-field condition) and the ring-level
  `IsLocalRing.StrictHenselization.existsUnique_algHom_comp_pointHom` (from the existing
  `liftEquiv`), `range_pointHom_subset/_eq` (separable closures in `Ω`), and
  `Scheme.Hom.eq_of_comp_eq_of_formallyUnramified` (maps from a local scheme into an unramified
  `S`-scheme are determined by a closed geometric point; via `algHom_ext_of_residue`).
- `lean/SGA/Foundations/Etale/LocalAcyclicity.lean` (A17): Milnor-fibre form
  `Scheme.Hom.IsLocallyAcyclicFor P f` for `P : ObjectProperty Scheme`, with **algebraic**
  geometric points `t̄` of `S̃` (`Scheme.Hom.IsAlgebraicPoint`: `K` integral over `κ(t)`), and
  `IsUniversallyLocallyAcyclicFor`; `IsLocallyZeroAcyclic = …For (ConnectedSpace ·)`; the
  base-change form `IsUniversallyZeroAcyclicBaseChange` (no qcqs hypothesis on `g`, as in Stacks
  0EYS). Proved: étale case of both forms; locality on the source for the étale topology
  (`IsLocallyAcyclicFor.comp_etale`, `.of_comp_etale` for étale surjective, universal versions);
  and that the definition of `0`-acyclic is SGA's: `Scheme.connectedSpace_iff_bijective_constantSchemeSection`
  (`H⁰(Z, C) = C` for all sets `C`, via sections of `∐_C Z ⟶ Z`, iff `Z` nonempty and connected).
- `lean/SGA/SGA1/ExposeXIII/Desingularization.lean` (A18): `IsDesingularizable`,
  `DesingularizableUpTo k d` (EGA IV 7.9.1), `IsStronglyDesingularizable`,
  `StronglyDesingularizableUpTo k d` (SGA 5 I 3.1.5 **reconstructed**: for every nonempty regular
  open `U`, a proper `Z' ⟶ Z` from a regular scheme, iso over `U`, complement an NCD over `k` —
  this is how XIII 3.1 3)1 uses it; the SGA 5 text is not in the repo, so it is unverified);
  `d : WithBot ℕ∞` compared with `topologicalKrullDim`. Proved: dimension 0 for both.
- `lean/SGA/SGA1/ExposeXIII/LocalAcyclicity.lean`: `IsOneAspherical L` (connected and
  `Subsingleton (ProLQuotient L (FundamentalGroup z))` at every geometric point; closed under
  isomorphisms via `ExposeV.autMap_bijective`), `IsLocallyOneAspherical`,
  `IsUniversallyLocallyOneAspherical`; statements `LocalAsphericitySmoothStatement` (XV 2.1),
  `LocalAcyclicityFlatReducedStatement` (XV 4.1), `GenericCohomologicalPropernessStatement` (3.1 1)
  a)), `…ConstructibleStatement` (3.1 1) b)), `FieldCohomologicalPropernessStatement` (3.2 1)),
  `GenericLocalAsphericityStatement` (3.3), `FieldLocalAsphericityStatement` (3.4),
  `GenericSpecializationStatement` (3.5: both maps `π₁^L(X_{s̄ᵢ}) → π₁^L(X ×_S S̄)` bijective at
  all base points, which is equivalent to bijectivity of SGA's `π = π₂⁻¹π₁₂π₁`). Proved: 3.3/3.4
  for étale `f` unconditionally, for smooth `f` from XV 2.1.

**What was hard / traps.**
- `(ξ ≫ f).imagePoint` is only propositionally `f ξ.imagePoint`, so stalks don't line up. The fix
  that worked everywhere: state helper lemmas with the point as a *variable* plus an equation and
  `subst` (`Scheme.exists_SpecMap_fromSpecStalk_eq`, `formallyUnramified_of_SpecMap_fromSpecStalk`),
  and compare ring maps out of stalks by `cancel_mono (X.fromSpecStalk x)` + `Spec.map_injective`
  (`fromSpecStalk` is a mono in mathlib; no locality needed).
- `(ξ ≫ f) ≫ g` vs `ξ ≫ f ≫ g`: use `strictLocalizationIsoOfEq` (an `eqToIso`) and prove facts
  about it by `subst` in a lemma with a general equation.
- `attribute [local instance] specializationOrder` also hits `ℕ∞` (it is a topological space) and
  breaks `nonpos_iff_eq_zero`. Use `let _ : PartialOrder Z := specializationOrder Z` inside the
  proof instead; schemes already have the global `Preorder` (specialization) that
  `ringKrullDim_stalk_eq_coheight` uses.
- `ConnectedSpace (Spec (.of K))` for a field is already found by `inferInstance`.

**Not done / next (round 2), in order.**
1. Registry A22: Stacks 0A3H for `p` flat, lfp, qc with geometrically connected fibres
   (`Γ(S,F) = Γ(T,p^*F)`), by germs: injectivity by stalks (needs stalks invariant under
   extension of separably closed fields), surjectivity by agreement on étale neighbourhoods +
   connectedness of the geometric fibres (sections of the constant sheaf `F_s̄` on a connected
   scheme are constant) + openness of flat lfp maps + gluing. **Reuse xiii14's
   `etaleAgreementLocus` (Foundations/EtaleStalkProper.lean) once it is stable** (see my question
   entry). Then 0EZX, then 0EZY for `X` of finite type over a separably closed field (components
   of finite type schemes over `k = k^sep` are geometrically connected) ⇒ XIII 3.2 1) for those
   `X`; general `X`, `k` need A2 (limits, xiii14).
2. Desingularization for curves over algebraically closed `k` (normalization is finite and
   regular): needs Noether finiteness of integral closure (not in mathlib; char p needs a
   separable Noether normalization).
3. Not stated, deliberately: 3.1 2), 3.1.1–3.1.3, 3.2 2) — need cohomological properness in
   dimension ≤ 1 for sheaves of groups, which nobody has defined; it is also the shape of A3's
   degree-1 PBC statement (xiii14). Whoever defines it first should register it.
4. The comparison Milnor form ⇔ base-change form needs SGA 4 VIII 5.2 / VII 5.7 (A2).
