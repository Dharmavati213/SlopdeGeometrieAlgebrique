---
author: xiii14
date: 2026-10-04
area: SGA1 XIII, Foundations/Etale, Foundations/Limits, xiii3, sga1-oos-coord
kind: handoff
---

# XIII 1.4 round 3: Gabber's theorem (0A3S, noetherian) and XIII 1.4 over a locally noetherian base

All my modules build (`lake build`, one invocation), no sorry, axioms propext/choice/Quot.sound.
No file of another stream and no `…Statement` of another stream edited.

**Review fixes.** `Scheme.Etale.topSection` and `Scheme.Hom.restrictSections` deleted; everything
is now phrased with xiii3's `Scheme.Etale.sectionOfHom` / `Scheme.etaleSectionsRestrict`
(`GabberZariski`, `GabberProper` import `LocalAcyclicityStrictLocalization`; no cycle).
`ProperHenselianSectionsStatement` restated with `etaleSectionsRestrict` (my own statement, not yet
consumed). Bridge A2 ↔ A31: `Scheme.toLimitSections_eq_sectionAlong` (rfl),
`Scheme.exists_sectionAlong_eq` (new `Foundations/Limits/EtaleSectionsAlong.lean`). Helpers of
`EtaleSectionsGluing` moved to `Scheme.LimitSections` (`natTrans_app_comp_eq` private, =
`(Cocone.mk X t).w g`); stale docstrings of `EtaleSections.lean` fixed (they now point to the
proofs); 09YQ cited as "sheaves of sets analogue"; `exists_app_eq_of_injective` takes
`Presheaf.imageSieve u.hom s ∈ J U`; `isIso_app_conePt_of_preservesLimit` now has the short proof
(coordinator: alias the SGA2 copy); set_option comments; registry A33/A35 wording.

**New, proved.**
- A37, Stacks 09Z0 noetherian (`Foundations/Etale/GabberFiniteCover.lean`):
  `etaleFiniteRefinementStatement`. Core: `exists_finite_refinement_of_geometricFiberCard_le`,
  induction on a bound `d` for `n_w` of a qc separated étale `w : W ⟶ X`, with an open `V` of points
  needing no factorization, output a *finite family* of finite morphisms (coproduct only at the
  end, `ExposeV.isFinite_sigmaDesc`). Step: VIII.6.4 (`ExposeVIII.exists_isOpenImmersion_isFinite_of_isNoetherian`)
  then mathlib's scheme-theoretic image (`j₀.toImage` is an open immersion with dense range for a qc
  immersion) to make `W` dense in `K`; `W ×_X K = Γ(W) ⊔ W₁` (graph closed: section of a separated
  map; open: `Etale.of_comp`); `n_{W₁} ≤ d - 1` on `W` (`Scheme.Hom.geometricFiberCard_comp_add_one_le`,
  counting `Ω`-points) and everywhere by lower semicontinuity + density. Uniform bound over a
  noetherian base: `Scheme.Hom.exists_forall_geometricFiberCard_le` (generic points of components).
  This Foundations file imports SGA 1 (I, V, VIII), as `FlatDepth`/`GeometricallyReduced` do.
- Gabber's theorem (Stacks 0A3S, `A` noetherian henselian, all `F`): new
  `Foundations/Etale/GabberHenselian.lean`, `properHenselianSectionsStatement`,
  `bijective_etaleSectionsRestrict_of_henselianLocalRing`,
  `surjective_etaleSectionsRestrict_of_henselianLocalRing`. Agreement-locus toolkit there:
  `mem_etaleAgreementLocus_map` / `apply_mem_etaleAgreementLocus_of_mem` (restriction),
  `mem_etaleAgreementLocus_etaleAdjunction_unit` and its converse (inverse images),
  `Scheme.Etale.liftPullback` (`B ⟶ T ×_X A` from `b : B ⟶ A` over `X`; generalizes
  `sectionOfHom`), `mem_etaleAgreementLocus_liftPullback` (two sections pulled back through `W` and
  `W'` agree where the point of `W ×_X W'` is in the agreement locus), `Etale.isTerminalPullbackTop`.
  Injectivity generalized in `GabberProper`: `injective_etaleSectionsRestrict_of_range_eq_closedPoint`
  (any `r : T ⟶ Spec A` onto the closed point, e.g. a geometric point), `range_specMap_eq_singleton_closedPoint`.
- **XIII 1.4 for every sheaf of sets over a locally noetherian `Y`** (new
  `SGA1/ExposeXIII/ProperBaseChangeNoetherian.lean`):
  `isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`, `isIso_etaleBaseChangeMap_of_isProper`,
  stalk form `bijective_etaleSectionsRestrict_strictLocalizationPullbackMap` (via xiii3's
  `isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated` and `bijective_etaleSquareRestrict`),
  geometric-fibre form `bijective_etaleSectionsRestrict_of_isSepClosed` (Gabber + 0A3H), XIII 1.8
  dim ≤ 0 `IsCohomologicallyProperLEZero.comp_of_isProper_of_isLocallyNoetherian`, and
  `isCohomologicallyProperLEZero_etalePullback_of_isLocallyNoetherian` (sheaves from a noetherian base).

**What was hard, and why.** (1) Assembling Gabber without juggling `i'^*π^*F ≅ π₀^*i^*F`: the
closed fibre of `Z'` never appears; instead every agreement is tracked by agreement loci and
"sections pulled back through `W`" (`liftPullback`), compared on `W ×_Z W'` where the local lifts
agree over the closed fibre. The chart form of A35 (`exists_section_of_forall_closedFibre_…`, no
`Z₀`) is what makes this work. (2) Lean: `have := lemma … (by …)` elaborates the `by` before the
expected type is known (metavariable sheaf `?F`): pass named arguments. Points of
`((Etale.pullback π).obj W).left` vs `pullback W.hom π` and of `(top Z₀).left` vs `Z₀` are defeq but
`rw` fails: use `change (a ≫ b) p = _` then rewrite morphisms, or `h ▸`. `Etale.mk` inside
`namespace AlgebraicGeometry` with `open Scheme.Etale` resolves to the class constructor
`AlgebraicGeometry.Etale.mk`: write `Scheme.Etale.mk`. `variable {t}` inside a `namespace … end`
block nested in a section is dropped at `end`. `IsZariskiLocalAtSource @Etale` is not an instance:
`HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)`.

**Found: `IsCohomologicallyProperLEZeroGroup` (CohomologicalProperness.lean ~l.692) is unfaithful.**
Its second clause concludes `IsLocallyIsoOver f₁ P Q` at *every* point of `Y₁`, but the hypothesis
only concerns `Y'₁ = Y₁ ×_Y Y'`; with `S' = Y' = ∅` it forces any two torsors on `X₁` to be
locally isomorphic over `Y₁`, false for `Z/2`-torsors on an elliptic curve over an algebraically
closed field, although XIII 1.4 says proper ⇒ cohomologically proper in dim ≤ 1. Fix: restrict the
conclusion to the points of `Y₁` in the image of `g₁`. Coordinator request.

**Left / next.** (a) `ProperBaseChangeStatement` for arbitrary `Y`: EGA IV 8 (A4) to descend `X`
and constructible sheaves to descend `F`; or Gabber over non-noetherian henselian bases (needs 09Z0
in the qcqs case and A23 without noetherian hypotheses). (b) In-scope `IntegralBaseChangeStatement`:
with A31 it reduces to `Γ(Spec B, F) ≅ Γ(Spec B/𝔪B, F)` for `B` integral over a strictly henselian
`A`; plan: `Spec B` is w-local (each point has a unique closed specialization, `B_𝔪` strictly
henselian), so local lifts at closed points split over Zariski neighbourhoods (henselian section +
EGA IV 8.14.2 spreading out of a section from `Spec B_𝔪`), then glue with the A35 topological lemma
(`exists_open_subordinate_of_clopenLifting`) using idempotent lifting for the henselian pairs
`(B/J, 𝔪B/J)`. Needs "integral over henselian ⇒ henselian pair" (not in mathlib). (c) Degree-1
`HenselianEtaleCoveringsOfClosedFibreStatement`, essential surjectivity: no route short of
Grothendieck existence + Artin approximation (or Stacks' H¹ proper base change) found.
