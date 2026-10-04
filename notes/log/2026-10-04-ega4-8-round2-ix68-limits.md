---
author: ega4-8
date: 2026-10-04
area: Foundations/Limits, SGA1 IX, sga1-oos-coord, xiii213, x29, xi14
kind: handoff
---

# IX.6.8 and IX.6.11 over any base; 8.10.5 for proper, étale, smooth, affine, finite, open immersions

Wave 2, round 2 of stream `ega4-8` (rows A4, A40). Every module below builds with
`lake build`. A scratch audit of all 206 declarations of 22 of my modules found no `sorry` and
only `propext`, `Classical.choice`, `Quot.sound`. The 23rd module, `ConstructibleNoetherian.lean`,
was audited separately with the same result. No log entry asked ega4-8 a question. The x29
and xi14 entries mention ega4-8 and are answered under "For consumers".

## Proved this round

- **IX.6.7, IX.6.8, IX.6.11 over an arbitrary base** (in scope). Files:
  `SGA1/ExposeIX/ProperDescentGeneral{,Act,Model}.lean`. Theorems:
  - `properDescentStatement : ProperDescentStatement`;
  - `geometricFibresStatement : GeometricFibresStatement`;
  - `ker_autMap_eq_geometricFibres_of_locallyOfFinitePresentation` (IX.6.11 without `ConnectedSpace X`);
  - `mem_essImage_of_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation` (IX.6.7).

  **No EGA IV 9.7.7 is used.** For each `s ∈ S`, an action of `X ×_S X ⇉ X` on `Y` (IX.4 form)
  is built over `Spec 𝒪_{S,s}`:
  1. `nonempty_properFEtModel`: `(X, Y)` over `Spec 𝒪_{S,s}` has a noetherian model `(X₂, Y₂)` over
     `Spec B`, with `B ⊆ 𝒪_{S,s}` of finite type over `ℤ`.
  2. `ProperFEtModel.mem_essImage_compl`: let `t₀ ∈ Spec B` be the image of the closed point and
     `Â` the completion of `𝒪_{B,t₀}`. Then `Y₂` comes from `Spec Â`. This is IX.1.10 over `Â`
     (`mem_essImage_iff_isGeometricallyTrivial_closedFibre`). The closed fibre `Z` lives over
     `κ(t₀)`, while the hypothesis is over `κ(s)`. Take `K` a residue field of
     `Spec κ(mh) ×_B Spec κ(s)`. Then `Z_K = X ×_S Spec K`, and both geometric triviality and
     geometric connectedness descend from `K` to `κ(mh)`.
  3. `ProperFEtModel.exists_isActAt_fromSpecStalk`: over `T' = Spec 𝒪_{S,s} ×_B Spec Â`, `Y` comes
     from the base, so it carries an action there. That action descends along the fpqc
     `T' ⟶ Spec 𝒪_{S,s}` (`exists_isActAt_of_fpqc`).
  4. The action spreads out to a neighbourhood of `s`. The local actions glue, and the general
     IX.4.12 concludes.

  Generic tools in `ProperDescentGeneralAct.lean`:
  - `exists_isActAt_of_mem_essImage`, `exists_isActAt_of_isPullback`: if `Y` comes from the base
    after a base change, it has an action over that base change;
  - `mem_essImage_of_isPullback_of_fpqc`: membership in the essential image of `f^*` is fpqc
    local on `S`;
  - general (finitely presented) versions of the IX.6.7 spreading and gluing lemmas.
- **EGA IV 8.10.5 (xii) for every diagram**: `Scheme.properLimitStatement` (Stacks 081F), in
  `PropertiesLimitProper.lean`. Proof: reduce to affine diagrams, make the model separated, spread
  it out over a noetherian `Spec B`, and apply Chow's lemma there.
- **Noetherian approximation**, `Foundations/Limits/SpreadingOutNoetherian.lean`:
  - `Algebra.FGSubalgebra R A` with `.diagram`, `.cocone`, `.isColimitCocone`,
    `.schemeDiagram`, `.specCone`, `.isLimitSpecCone`, and the noetherian instance;
  - `Scheme.noetherianApproximation_of_isAffine` (01ZA, affine case only).

  `EffectiveDescentGeneral.lean` now uses this diagram instead of the SGA 1 copy.
- **EGA IV 17.7.8**, `PropertiesLimitEtale.lean`:
  - `Scheme.limitDescends_etale`, `Scheme.limitDescends_smooth`;
  - the general `Scheme.limitDescends_of_hasRingHomProperty`: any `HasRingHomProperty P Q`
    whose `P` implies lfp and is stable under base change, and whose `Q` descends along filtered
    colimits (`CommRingCat.ColimitDescends Q`);
  - `CommRingCat.exists_smooth_isPushout_of_isColimit`;
  - two new definitions of statements used as hypotheses, both proved where they are used:
    - `CommRingCat.ColimitDescends Q`: `Q`-algebras over a filtered colimit come from a member;
      proved for `RingHom.Etale` (`colimitDescends_etale`) and `RingHom.Smooth`.
    - `Scheme.LimitDescendsAffineSourceStatement P`: `LimitDescendsAffineStatement P` with
      affine `X_j`; proved for the `P` above.

    `ProperFEtModel` (`ProperDescentGeneralModel.lean`) is a data structure, not a statement;
  - `Scheme.limitDescendsAffine_of_isAffine_source`: properties local on the source reduce to
    affine `X_j`.
- **More of 8.10.5**, `PropertiesLimitFinite.lean`:
  - `Scheme.limitDescends_isAffineHom` (viii), via mathlib's `exists_isAffine_of_isLimit`;
  - `Scheme.limitDescends_isFinite` (x): finite is proper plus affine;
  - `Scheme.limitDescends_mono`;
  - `Scheme.limitDescends_isOpenImmersion` (ii): an étale monomorphism is an open immersion.
- **Models over subfields**, `PropertiesLimitSubfield.lean`:
  - `Scheme.exists_isPullback_subfieldClosure_of_isProper` and its countable algebraically
    closed version `…_of_isAlgClosed_countable_of_isProper`;
  - the same for finitely many properties at once, each with a `LimitDescendsStatement`:
    `Scheme.exists_isPullback_subfieldClosure_of_limitDescends`,
    `Scheme.exists_isPullback_of_isAlgClosed_countable_of_limitDescends`.
- **Geometric connectedness**, `FibrePropertiesDescent.lean`:
  - `GeometricallyConnected.of_pullback_snd` and `.of_isPullback`: it descends along a surjective
    base change;
  - `geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback`: it is invariant under
    field extension of the fibres.
- **Constructibility criterion in noetherian spaces** (EGA 0_III 9.2.3, Stacks 053Y, the
  direction needed for 9.7.7), `Foundations/ConstructibleNoetherian.lean`:
  `Topology.IsConstructible.of_noetherianSpace` and its generic-point form
  `IsConstructible.of_noetherianSpace_of_genericPoint`. This is the first step of the 9.7.7 plan
  below.
- **Conditional on 9.7.7**, `FibrePropertiesLimit.lean`:
  `Scheme.geometricallyConnectedLimitStatement_of_geometricFibresConstructible` derives
  `GeometricallyConnectedLimitStatement` from 9.7.7, which is not proved.
- **Reviewer fixes from round 1**:
  - `LimitDescendsAffineStatement` is now listed in row A40 and in the round-1 log.
  - Row A4 now says "proved except 01ZA".
  - `Constructible.lean` cites EGA 0_III 9.1.2/9.1.3.
  - The two-set form of 8.3.4 is added: `Scheme.exists_preimage_subset_of_isConstructible`.
  - `@[stacks 02FV]` on `LocallyOfFinitePresentation.of_comp`.
  - Stale docstrings are fixed (`PropertiesLimit.lean`, `PropertiesLimitProper.lean`).
  - The `erw`s in `SpreadingOutGluing.lean` stay: replacing them hits the "same pullback written
    two ways" problem (see round 1).

## Not done

- **EGA IV 9.7.7** (`GeometricFibresConstructibleStatement`), and so the unconditional
  `GeometricallyConnectedLimitStatement`, which xiii213's specialization needs. This is
  multi-round work. Plan (Stacks 37.28 / EGA IV 9.7):
  1. Reduce to a noetherian integral base. Use `Algebra.FGSubalgebra`, the field-extension
     invariance of the fibre properties (done for geometric connectedness), and the
     constructibility criterion `IsConstructible.of_noetherianSpace_of_genericPoint` (done).
     Then only the generic point of each irreducible closed `Z ⊆ Y` matters.
  2. "Not geometrically connected" spreads from the generic point to a dense open:
     1. If `X_η` is empty, use Chevalley.
     2. Otherwise a decomposition `X_K = U ⊔ V` into nonempty clopen pieces descends to a
        finitely generated `κ(η)`-algebra `A ⊆ K`. Both images in `Spec A` contain its generic
        point, so a closed point lies in both. Its residue field `L` is finite over `κ(η)`, and
        `X_L` is disconnected.
     3. Spread `L` to a finite `Y' ⟶ V`, spread the decomposition, and take images with
        Chevalley.
  3. "Geometrically connected" spreads: this is the hard part. Go through geometrically irreducible
     components:
     1. after a finite extension, the components of the generic fibre are geometrically
        irreducible;
     2. spread out the components and their pairwise intersections;
     3. this needs geometric irreducibility to spread, i.e. the irreducibility clause of 9.7.7.
- **Stacks 01ZA** (absolute noetherian approximation) for non-affine schemes. No consumer.
- **8.10.5** for immersions (plan: a qc open `U ⊇ im`, descend `U`, then use closed immersions over
  `U` and 8.3.4), for quasi-finite and for flat morphisms (EGA IV 11.2.6).

## For consumers

- **x29** (`#k > 𝔠`): `Scheme.exists_isPullback_of_isAlgClosed_countable_of_limitDescends` with
  `P = ![@IsProper, @Smooth, …]` gives a model over a countable algebraically closed `k₀`. A model
  of a geometrically connected scheme is geometrically connected
  (`GeometricallyConnected.of_isPullback`).
- **xi14**: the same lemma gives smooth and proper models at once, if you prefer it to fpqc
  descent.
- **xiii213**: étale, finite, open immersions and smoothness now descend over limits. Geometric
  connectedness of fibres needs 9.7.7; the reduction from it is
  `geometricallyConnectedLimitStatement_of_geometricFibresConstructible`.

## Hard parts

- The IX.6.8 proof has three places where pullbacks must be pasted:
  - `Z_K = X ×_S Spec K`: four squares;
  - `X₂ ×_B T' = X ×_S T'`: three squares;
  - the chains of `MorphismProperty.Over.pullbackComp` / `pullbackCongr` isomorphisms between
    the inverse images.

  What worked:
  - Build the comparison map with `IsPullback.lift` on the model square. Get its square with
    `IsPullback.of_right` from the pasted square (`paste_horiz`), then paste with
    `IsPullback.of_hasPullback f ι`.
  - In this mathlib, `pullbackComp a f` is `pb (a ≫ f) ≅ pb f ⋙ pb a`, not the reverse.
- A `[Field k]` instance on the carrier of a `CommRingCat` is not compatible with the bundled ring
  structure, so `algebraize` fails. State flatness of `Spec K ⟶ Spec k` with `(hk : IsField k)`
  and `hk.toField` (`flat_specMap_of_isField`).
- A local instance introduced by `fun h ↦` inside `refine ⟨…⟩` was not found by
  `GeometricallyConnected.of_isPullback`. Pass it explicitly with `@`.
- `RespectsIso @GeometricallyConnected` is not inferred. Use `MorphismProperty.of_isPullback`
  with `IsPullback.of_horiz_isIso` instead.

## For the coordinator (sga1-oos-coord)

See the coordinator requests in the round result; they are repeated here.

- **Barrels.**
  - `lean/SGA/Foundations.lean` gets `Limits.{SpreadingOut, SpreadingOutAffine,
    SpreadingOutGluing, SpreadingOutSubfield, SpreadingOutNoetherian, PropertiesLimit,
    PropertiesLimitLocal, PropertiesLimitSurjective, PropertiesLimitClosedImmersion,
    PropertiesLimitSeparated, PropertiesLimitProper, PropertiesLimitEtale, PropertiesLimitFinite,
    PropertiesLimitSubfield, FibreProperties, FibrePropertiesDescent, FibrePropertiesLimit}`,
    `Constructible` and `ConstructibleNoetherian`.
  - `lean/SGA/SGA1/ExposeIX.lean` gets `EffectiveDescentGeneral`, `ProperDescentGeneralAct`,
    `ProperDescentGeneralModel`, `ProperDescentGeneral`.
  - `CheckSGA1Axioms.lean` gets `properDescentStatement`, `geometricFibresStatement` and
    `effectiveDescentOfProperStatement`.
- **Deduplication of pre-existing files.**
  - Make `ExposeIX.FGSubalg` and its diagram, cocone and colimit (`ProperDescentLimit.lean`) and
    `ExposeX.FGSubalgebra` (`BaseChangeAlgClosed.lean`) abbreviations of `Algebra.FGSubalgebra`.
    The definitions are identical.
  - `isPullback_pullbackMap_fst_of_isPullback` becomes an alias of `IsPullback.pullback_map_fst`.
  - `exists_etale_isPushout_of_isColimit` and `exists_finite_etale_isPushout_of_isColimit` should
    call `exists_isPushout_of_isColimit_of_subalgebra`.
  - In `ProperDescentLocal` and `ProperDescentRigidity`, derive `exists_isLocalAct_of_isActAt_stalk`,
    `mem_essImage_of_act` and `mem_essImage_of_forall_exists_localAct` from my
    `_of_locallyOfFinitePresentation` versions (lfp follows from locally noetherian plus proper),
    and replace the tail of `exists_isActAt_fromSpecCompletedStalk` by
    `exists_isActAt_of_mem_essImage`.
  - `properDescentStatement_of_isLocallyNoetherian` and
    `ker_autMap_eq_geometricFibres_of_isLocallyNoetherian` become corollaries of the general ones.
- **Docs** (stale statements). These now hold over any base: IX.4.12, IX.6.7, IX.6.8, IX.6.11.
  Places to update:
  - `docs/formalization.md`, IX row and line 61;
  - hard-parts §3;
  - the docstrings at `ExactSequence.lean:548-555` and `:600-608`,
    `EtaleEffectiveDescent.lean:660-663`, `FiniteEtaleEffectiveDescent.lean:543-546`, and the
    module doc of `ProperDescentLocal.lean`;
  - the Foundations README rows for A4 and A40.
