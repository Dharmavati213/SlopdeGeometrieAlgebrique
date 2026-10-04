---
author: xiii14
date: 2026-10-04
area: SGA1 XIII, Foundations/Limits, Foundations/Etale, xiii3, xi14, sga1-oos-coord
kind: handoff
---

# XIII 1.4 round 2: A2 (VIII 5.2 in degree 0) proved; Gabber's H⁰ half built (Zariski H⁰, descent, local lifts)

All files build (`lake build` of each, one at a time), no sorry, axioms propext/choice/Quot.sound.
No existing file of another stream edited; nothing in a barrel.

**Review fixes of round 1** (done in the interrupted attempt, checked now): docstrings and dangling
names; `etaleCoveringsOfClosedFibreStatement_of_henselian` (henselian IX.1.10 ⇒ IX.1.10);
`[IsLocalRing A]` binder; cross-references to `ExposeIX.full/faithful_pullback_closedFibre`;
finite limits `IsCohomologicallyProperLEZero.of_isLimit`, `.pi`, `isCohomologicallyProperLEZero_of_isTerminal`;
`CategoryTheory.isIso_app_conePt_of_preservesLimit` moved to Foundations; the geometric-fibre-card
lemmas moved to the new `Foundations/Limits/GeometricFiberCardIso.lean` (registry A33; xi14's
`ExposeXI.isIso_of_geometricFiberCard_eq_one` is its connected-base case — coordinator request).
Still open (needs edits of CohomologicalProperness.lean, coordinator): the five dim ≤ -1 results
there are superseded by `ProperBaseChange.lean` (see coordinator requests); constant sheaves are
still only for finite `C` (`IsSeparated (constantSchemeHom X C)` is missing for infinite `C`).

**New, proved.**
- `Foundations/Limits/EtaleSectionsGluing.lean` (A2): `Scheme.exists_toLimitSections_eq` (VII 5.7
  degree 0, surjectivity, for a cofiltered limit of qcqs schemes with affine transitions, each
  étale over `X` via `t : E ⟶ const X`); `Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`
  and `Scheme.pushforwardStalkStrictLocalizationStatement` (SGA 4 VIII 5.2 / Stacks 03Q9 in degree
  0, `f` qcqs). Helpers: `exists_forall_pullback_fst_notMem` (Stacks 01Z3 for `T ×_{E j} E k`),
  `pullbackDiagram`/`isLimitPullbackDiagramCone`, `exists_mem_etaleAgreementLocus_etaleAdjunction_unit`,
  `AgreesWith` (+ `.comp`, `.restrict`), `exists_agreesWith`, `exists_forall_mem_etaleAgreementLocus`.
  Separate log entry `2026-10-04-xiii14-a2-proved.md` for xiii3.
- `Foundations/Etale/GabberZariski.lean` (A35, Stacks 0A0B noetherian): pure topology
  `exists_open_subordinate_of_clopenLifting` (finitely many charts glue after shrinking over a closed
  `X₀` whose closed subsets lift clopens; replaces the constructible-sheaf reduction of 09ZG by
  "patterns" of charts), `exists_eventually_eq_of_clopenLifting`; schemes:
  `exists_isClosed_diff_of_henselianLocalRing` (A23 for every closed subset, via
  `IdealSheafData.vanishingIdeal`), `exists_section_of_forall_closedFibre_of_henselianLocalRing`,
  `exists_eq_of_forall_closedFibre_of_henselianLocalRing`; Zariski gluing in the étale site
  (`Scheme.Etale.ofOpens`, `ofOpensHom`, `liftOfOpens`, `topSection`, `Scheme.eq_of_forall_mem_opens`,
  `Scheme.exists_eq_of_forall_opens`).
- `Foundations/Etale/GabberDescent.lean` (A36): `CategoryTheory.exists_app_eq_of_injective`,
  `Scheme.exists_etaleAdjunction_unit_eq_of_surjective` (imports xiii3's
  `injective_map_etaleAdjunction_unit`, not redone).
- `Foundations/Etale/GabberProper.lean`: `Scheme.Hom.restrictSections`, statement
  `ProperHenselianSectionsStatement` (0A3S noetherian, all `F`), injectivity
  `injective_restrictSections_of_universallyClosed` (any local `A`), local lifts
  `exists_etaleAdjunction_unit_eq_of_isClosedImmersion` (Gabber step 1).
- `Foundations/Etale/GabberFiniteCover.lean` (A37): statement `EtaleFiniteRefinementStatement`
  (Stacks 09Z0 noetherian).

**What was hard.** (1) A2's overlaps: the agreement of two local models only descends to "every
point of `T ×_{E k} E m` lies in the agreement locus" at a level `m` depending on the pair; a common
level with commuting triangles is taken in `Over k₂` (`IsCofiltered.inf_objs_exists` there), and the
point form survives precomposition. (2) The Zariski H⁰ lemma: Stacks reduces 09ZG to constant
sheaves on closed subsets via constructible sheaves on spectral spaces; for finitely many charts one
can instead index by the finitely many "patterns" (which charts contain the point, which pairs agree
there) and lift the class function on each closed set `T_y ∩ X₀` (clopen lifting, A23) — about 150
lines of pure topology. (3) Lean: `T ∩ X₀ \ K` does not parse (∩ and \ at the same precedence): write
`(T ∩ X₀) \ K`; `Set.range Y.hom ⊆ U` for `Y : X.Etale` needs `(U : Set X)`; a missing
`set_option backward.isDefEq.respectTransparency false` makes `IsOpenImmersion U.ι` fail to
synthesize in Etale contexts; `let`-bound section families get unfolded by `rw`, make them opaque with
`obtain ⟨b, hb⟩ : ∃ b, … := ⟨_, …⟩`.

**Next (round 3), in order.** (a) A37: prove `EtaleFiniteRefinementStatement` (Stacks 09Z0,
noetherian; induction on the fibre degree bound of `∐ U_j ⟶ X`: VIII.6.4 gives `U ⊆ Ū` finite,
`U ×_X Ū = U ⊔ W` with `W ⟶ Ū` of smaller degree on the dense `U`; degree semicontinuity
`isOpen_setOf_le_geometricFiberCard`; scheme-theoretic closure). (b) Gabber assembly
`ProperHenselianSectionsStatement` (file GabberProper or a new Gabber*.lean): step 1 local lifts
(done) + compactness ⇒ finitely many affine `W_j` covering `Z`; A37 ⇒ `π : Z' ⟶ Z` finite surjective
with Zariski charts `g_α : W'_α ⟶ W_j`; on `Z'` (proper over `A`) the pulled back sections
`s'_α` agree near the closed fibre (germs at geometric points over `Z₀`: all equal the germ of
`τ₀`, via `sheafFiberEtalePullbackIso`); `exists_section_of_forall_closedFibre_of_henselianLocalRing`
gives `t` on `Z'`; near points of `Z₀`, `t` is the image of some `a_j` on `Z' ×_Z V`
(agreement locus + `π` universally closed, as in `toPresheafFiber_etalePushforward_eq_of_universallyClosed`),
so the good locus is open and contains `Z₀`, hence is `Z`; `exists_etaleAdjunction_unit_eq_of_surjective`
descends `t`; compare germs on `Z₀`. Trap: geometric points `z̄' ≫ π` vs `x̄₀ ≫ i` are only
propositionally equal; state germ lemmas with a variable point and an equation, then `subst`
(xiii3's trick). (c) XIII 1.4 for `Y` locally noetherian, all `F`: with A2 and xiii3's A31
(stalks of base change maps through strict localizations, in progress) it reduces to
`ProperHenselianSectionsStatement` + xiii3's 0A3H for `κ ⊆ κ'` separably closed (as in round 1 for
`h_E`). (d) Then `IntegralBaseChangeStatement` needs Gabber for integral morphisms (09ZH), not just A2.
