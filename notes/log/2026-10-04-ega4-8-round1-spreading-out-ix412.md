---
author: ega4-8
date: 2026-10-04
area: Foundations/Limits, SGA1 IX, sga1-oos-coord, xiii213, x29, xi14
kind: handoff
---

# EGA IV 8.8.2 (ii), 8.3.4 and most of 8.10.5 proved; IX.4.12 over any base proved

Wave 2, round 1 of stream `ega4-8` (rows A4, A40). Everything below builds with
`lake build`, is sorry-free, and `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`.

## Proved

- **EGA IV 8.8.2 (ii) in general** (Stacks 01ZM), `Foundations/Limits/SpreadingOutGluing.lean`:
  `Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation` and
  `Scheme.spreadingOutStatement`. It works for any cofiltered diagram of qcqs schemes with affine
  transition maps. Affine pieces lying over an affine open of some `E i` descend by the affine
  case (`SpreadingOutAffine.lean`, run on the `opensDiagram`). Pieces are glued two at a time
  (`Scheme.spreadsOut_of_sup_eq_top`):
  1. the qc open `U ∩ W` descends to opens of both models (`LimitModel.exists_preimage_eq`,
     mathlib's `exists_preimage_eq`);
  2. the two models of `U ∩ W` become isomorphic (`exists_iso_of_isPullback`);
  3. we glue by a pushout of open immersions (`Scheme.spreadsOut_of_glue`).

  Helpers:
  - `Scheme.LimitModel c q j` is a model of `q` over `E j`, with `.lower`, `.lowerFst`, `.ofIso`;
  - `Scheme.SpreadsOut`;
  - `Scheme.openCoverOfTwo` and `Scheme.isPullback_of_two_openImmersions`;
  - `Scheme.pushout_inl_or_inr` and `Scheme.exists_eq_of_pushout_inl_eq_inr`;
  - `Scheme.quasiSeparatedSpace_of_two_openImmersions`.
- **Over subfields**, `Limits/SpreadingOutSubfield.lean`:
  - `Scheme.spreadingOutSubfieldStatement` and `Scheme.exists_isPullback_subfieldClosure`: if
    `X` is of finite type and quasi-separated over a field `K`, it descends to `Subfield.closure s`
    for some finite `s`;
  - `Scheme.exists_isPullback_of_isAlgClosed_countable`: if `K` is algebraically closed, `X`
    descends to a countable algebraically closed subfield `k₀`. For xi14's Lefschetz principle
    (A47), `k₀` embeds into `ℂ` in characteristic 0. x29 may use it for `#k > 𝔠`.
- **EGA IV 8.3.4**, `Limits/PropertiesLimitSurjective.lean`: a constructible `T ⊆ E j` whose
  preimage in the limit is empty (resp. everything) already has empty (resp. full) preimage in
  some `E k` (`Scheme.exists_preimage_eq_empty_of_isConstructible`, `…_univ_…`). The proof
  splits `T` into finitely many pieces `U ∩ Z`, with `U` a quasi-compact open and `Z` closed
  (`Foundations/Constructible.lean`, `IsConstructible.isFiniteUnionOpenInterClosed`), and applies
  Stacks 01Z3 over `U`.
- **EGA IV 8.10.5**: each property is a theorem
  `Scheme.LimitDescendsStatement P` over every diagram as above.

  | `P` | declaration | file |
  | --- | --- | --- |
  | surjective (vi) | `Scheme.limitDescends_surjective` | `PropertiesLimitSurjective.lean` |
  | closed immersion (iv) | `Scheme.limitDescends_isClosedImmersion` | `PropertiesLimitClosedImmersion.lean` |
  | isomorphism (i) | `Scheme.limitDescends_isIso` | `PropertiesLimitClosedImmersion.lean` |
  | separated (v) | `Scheme.limitDescends_isSeparated` | `PropertiesLimitSeparated.lean` |

  Tools used by these proofs:
  - `Scheme.limitDescends_of_affine`, in `PropertiesLimitLocal.lean`: for `P` local on the target
    and stable under base change, it is enough to treat diagrams of affine schemes.
  - `Scheme.limitDescends_relative`: the statement for a morphism `Y_j ⟶ Z_j` of `E j`-schemes.
  - `IsPullback.diagonal` and `IsPullback.pullback_map_fst`.
  - `LocallyOfFinitePresentation.of_comp` (Stacks 00F4), and an instance making the diagonal
    lfp when `f` is lft.
- **Proper**, 8.10.5 (xii), by Chow's lemma, in `PropertiesLimitProper.lean`:
  - `Scheme.limitDescends_isProper_of_isNoetherian` covers diagrams of noetherian affine schemes.
  - `Scheme.exists_isProper_of_isNoetherian_model` covers `X_j = Y ×_T E j` with `Y` separated
    and of finite type over a noetherian affine `T`. It applies the repo's
    `exists_isHProjective_isIso_morphismRestrict` on each of the finitely many irreducible
    components of `Y`. On the limit, each H-quasi-projective piece becomes a proper immersion,
    hence a closed immersion, and closed immersions descend.
  - `Scheme.universallyClosed_of_jointly_surjective`: universal closedness from a finite
    jointly surjective family.
- **IX.4.12 over any base** (in scope), `SGA1/ExposeIX/EffectiveDescentGeneral.lean`:
  `effectiveDescentOfProperStatement : EffectiveDescentOfProperStatement` and
  `isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation`. The proof:
  1. IX.4.5 reduces to `Spec 𝒪_{S,x}`.
  2. 8.8.2 (ii) over the diagram of finitely generated `ℤ`-subalgebras gives a model.
  3. The model is proper and surjective at a finite level.
  4. `DescentDatum.isEffective_of_isPullback_specMap` from `ProperDescentLimit.lean` finishes.

## Not done; what I would do next

- **`Scheme.ProperLimitStatement` for arbitrary diagrams.** Use `limitDescends_of_affine`.
  1. For an affine member `Spec A_j`, approximate `A_j` by the diagram of its finitely
     generated `ℤ`-subalgebras.
  2. Descend `X_j` to a separated `Y` over some `B` (8.8.2 (ii) and
     `limitDescends_isSeparated` on that diagram).
  3. Apply `exists_isProper_of_isNoetherian_model`, which already accepts any `t : E j ⟶ T`.

  This is about 100 lines. Blocker: the diagram (`FGSubalg`, `fgSubalgDiagram`,
  `fgSubalgCocone`, `isColimitFgSubalgCocone`, and the noetherian instance) lives in
  `SGA1/ExposeIX/ProperDescentLimit.lean`, which Foundations cannot import. I asked the
  coordinator to move it.
- **IX.6.8 and IX.6.11 over any base.** The local route needs no 9.7.7.
  1. For `s ∈ S`, spread `f` and `Y` over `𝒪_{S,s}` to `f_λ, Y_λ` over a noetherian `B_λ`.
     The fibre condition at the image `t` of the closed point follows from the fibre at `s` by
     field extension.
  2. `exists_isActAt_fromSpecCompletedStalk f_λ Y_λ t` needs only `[IsLocallyNoetherian]` and
     `[IsProper]`, not geometric connectedness. It gives an action over `Spec 𝒪̂_{B_λ,t}`.
  3. Base change the action to `Spec (𝒪̂ ⊗_{B_λ} 𝒪_{S,s})`, which is fpqc over `Spec 𝒪_{S,s}`.
     Descend it with `exists_isActAt_of_fpqc` for the original `f`, whose fibres are
     geometrically connected.
  4. Spread out to a neighbourhood and glue.

  Step 4 is `exists_isLocalAct_of_isActAt_stalk` and `mem_essImage_of_forall_exists_localAct` /
  `mem_essImage_of_act`. These assume `[IsLocallyNoetherian S]`. As far as I can see, the
  hypothesis is used only to get `LocallyOfFinitePresentation (Y.hom ≫ f)` and the noetherian
  IX.4.12. With `[LocallyOfFinitePresentation f] [Surjective f]` and the general IX.4.12 above,
  the proofs should go through unchanged. I asked the coordinator to weaken them, instead of
  copying them. Step 3 also needs a lemma transferring `IsActAt` between `(f_λ, Y_λ)` and
  `(f, Y)` along the base change.
- **EGA IV 9.7.7** (`GeometricFibresConstructibleStatement`) and
  `NoetherianApproximationStatement` (Stacks 01ZA) are untouched.

## Hard parts

- **Heartbeats are per declaration.** My first version of the gluing step was a single theorem
  and timed out at random places. Splitting it into `spreadsOut_of_glue` (the pushout and the
  cartesian square) and `spreadsOut_of_sup_eq_top` (producing the data) fixed it.
- **The same pullback written two ways fails to unify.** Writing
  `pullback.fst NW.hom (E.map g)` for a model `NW := M.lower g` gave "Application type mismatch"
  between `(M.lower g).obj` and `pullback …`; `rw` also fails, at instance transparency.
  Workarounds:
  - Name the projection once (`LimitModel.lowerFst`).
  - State element equations through `congrArg (fun F ↦ F.appTop b) h` rather than `rw` with
    `comp_apply`.
  - Transport along equalities of the arguments of `pullback.snd` with `subst` lemmas
    (`Scheme.of_pullback_snd_eq`, `…_eq_left`), not with `rw [E.map_comp]`, whose motive is not
    type correct.
- `Topology.IsConstructible` is reducible enough that `hT.foo` dot notation fails. Call
  `IsConstructible.foo hT`.
