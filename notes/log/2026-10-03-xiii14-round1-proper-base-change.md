---
author: xiii14
date: 2026-10-03
area: SGA1 XIII, Foundations/EtaleStalkProper, Foundations/Limits, xiii3, xiii43, xiii212, sga1-oos-coord
kind: handoff
---

# XIII 1.4 round 1: dim ≤ -1 in general, dim ≤ 0 for h_E (E separated étale), henselian IX.1.10 full faithfulness

All 11 new files build (`lake build` of each module), no sorry/axiom, `#print axioms` only
propext/choice/Quot.sound, no name clash with the ExposeXIII barrel or xiii3's new modules. No
existing file edited. Not in any barrel (see coordinator requests at the end).

**Proved** (Foundations, `AlgebraicGeometry.Scheme` namespace unless said):
- `Foundations/EtaleStalkProper.lean`: agreement locus API (`etaleAgreementLocus`,
  `isOpen_etaleAgreementLocus`, `map_eq_of_range_subset_etaleAgreementLocus`,
  `apply_mem_etaleAgreementLocus`); `mono_etaleBaseChangeMap_of_universallyClosed` (base change
  map injective for every universally closed `f`, every `Y`; Stacks 0A3T injectivity).
- `Foundations/EtaleStalkProperRepresentable.lean`: `etalePullbackYonedaIso_hom_unit` (the iso
  `h^* h_E ≅ h_{X'×_X E}` on images of sections = base change of morphisms; general
  `GrothendieckTopology.yonedaObjLeftAdjointIso_hom_unit`), `range_subset_etaleAgreementLocus`
  (+ `_etaleYoneda`), predicate `ExtendsAlongGeometricFibres f E`, and
  `isIso_etaleBaseChangeMap_etaleYoneda_of_extendsAlongGeometricFibres` (the "c_f surjective +
  c_{f'} injective ⇒ β iso" trick, done with germs, no Γ(X_ȳ, F) needed).
- `Foundations/EtaleStalkProperLimit.lean`: `Hom.exists_etaleNbhd_hom_of_strictLocalization`
  (EGA IV 8.8.2 at `X ×_Y Spec 𝒪^sh`; instances: transition maps of the affine-nbhd diagram are
  affine, pieces qcqs), `extendsAlongGeometricFibres_of_strictLocalization`.
- `Foundations/Etale/ProperBaseChangeClopen.lean` (registry A23): henselian clopen lifting for
  proper schemes over noetherian henselian local rings (Stein + `exists_isClopen_of_isFinite`),
  `eq_empty_of_isClosed_of_forall_ne_closedPoint`, `range_eq_preimage_closedPoint_of_isPullback`.
- `Foundations/Etale/ProperBaseChangeClosure.lean`: every mono of étale sheaves is regular
  (instance `isRegularMonoCategory_sheaf`, transported from the affine étale site, a topos).
- `Foundations/Limits/EtaleSections.lean` (A2 interface): the map
  `Hom.pushforwardStalkToStrictLocalization : (f_*F)_s̄ ⟶ Γ(X ×_S Spec 𝒪^sh, F)`,
  `PushforwardStalkStrictLocalizationStatement` (SGA 4 VIII 5.2), and **injectivity for every
  quasi-compact f** (`Hom.injective_pushforwardStalkToStrictLocalization`: agreement locus +
  mathlib's `exists_map_eq_top`).

SGA 1 (`SGA.SGA1.ExposeXIII`):
- `ProperBaseChange.lean`: `isCohomologicallyProperLENegOne_of_universallyClosed` (XIII 1.4,
  dim ≤ -1, every UC `f`, every `Y`), groups version, XIII 1.8 dim ≤ -1 unconditional
  (`IsCohomologicallyProperLENegOne.comp_of_universallyClosed`), 1.6 2) dim ≤ 0 without its
  dim ≤ -1 hypothesis, XIII 1.9 dim ≤ -1 for integral `f` unconditional (sets and groups);
  degree-1 interface `HenselianEtaleCoveringsOfClosedFibreStatement`.
- `ProperBaseChangeField.lean`: `Spec Ω ⟶ Spec k` geometrically connected for `k` separably
  closed, `Ω` alg. closed; descent of morphisms into étale schemes along `T ⊗_k Ω ⟶ T` (IX.3.4).
- `ProperBaseChangeHenselian.lean`: `exists_section_of_henselianLocalRing` (sections of a
  separated étale `E ⟶ P` extend from the closed fibre, `P` proper over noetherian henselian `A`;
  VIII.6.4 + clopen lifting + degree argument; Stacks 0A3S for h_E without Gabber),
  `exists_hom_of_isPullback_closedFibre`, `eq_of_comp_eq_of_isPullback_closedFibre`,
  **`full_pullback_closedFibre_of_henselianLocalRing`** (IX.1.10 fullness, noetherian henselian
  `A`) and `faithful_pullback_closedFibre_of_isLocalRing` (any local `A`).
- `ProperBaseChangeRepresentable.lean`: **`isCohomologicallyProperLEZero_etaleYoneda`** (XIII 1.4
  dim ≤ 0 for `h_E`, `E ⟶ X` separated étale, `f` proper, `Y` locally noetherian, `Y'` arbitrary),
  `isCohomologicallyProperLEZero_constantSheaf` (finite `C`),
  `isCohomologicallyProperLEZero_of_isLocallyConstantFiniteSheaf`.
- `ProperBaseChangeClosure.lean`: `IsCohomologicallyProperLEZero.of_mono` (subsheaves, for UC
  `f`, via XIII 1.13 1)), `.prod`, `isCohomologicallyProperLEZero_of_mono_etaleYoneda`.

**What was hard.** Not the mathematics but `rw` on `Scheme.Etale` objects: "motive is not type
correct at implicit transparency" (MorphismProperty.Over vs `Etale`). What worked: evaluate
morphism equations at points with `congrArg (fun φ ↦ φ x)` + `simp only [Scheme.Hom.comp_apply]`
+ `exact`; reason with `Scheme.Hom.comp_preimage` on opens instead of points; a `rfl` lemma
`Etale.comp_left'`; plain `simp [defs]` where `simp only` fails; `obtain ⟨x, hx⟩ : ∃ x, … := ⟨_, h⟩`
instead of `let` (avoids whnf timeouts); split `exact f a b c` into `have`s when it times out
(`regularMonoOfMono`). Pass `(A := CommRingCat.of A)` explicitly when mixing `A : Type` with
`CommRingCat` lemmas. xiii46's `GeometricallyConnected.lean` was briefly broken mid-edit; my
`ProperBaseChangeField` imports it (they keep `geometricallyConnected_of_isAlgClosed`).

**Next (round 2), in order.**
1. A2 surjectivity (the gluing half of SGA 4 VII 5.7 at the strict localization): sections of
   `p^*F` over `P = X ×_S Spec 𝒪^sh` are étale-locally images of sections of `F` (germs:
   `sheafFiberEtalePullbackIso`); descend the affine étale pieces of `P` to some `X ×_S V_k`
   (`CommRingCat.exists_etale_isPushout_of_isColimit`, `exists_π_app_comp_eq_of_…`), the cover
   (`exists_map_eq_top`) and the overlaps (agreement locus, as in the injectivity proof); glue.
   This proves `PushforwardStalkStrictLocalizationStatement` and unblocks xiii3 and the in-scope
   `IntegralBaseChangeStatement`.
2. General `F` for `f` proper, `Y` locally noetherian: with A2, it remains Γ(P, F) ≅ Γ(P₀, F)
   for `P` proper over noetherian henselian `A` (Gabber 09ZF, or Route B: constructible sheaves
   embed in finite products of `π_*C`, Stacks 09Z6, then `.of_mono` + `.prod` + 1.9 + filtered
   colimits) and Γ(X_{κ^sep}, F) ≅ Γ(X_Ω, F) (xiii3's A22 / 0A3I). The h_E case shows the
   assembly works; reuse `isIso_etaleBaseChangeMap_…` pattern (germs, agreement locus).
3. Degree 1: essential surjectivity of henselian IX.1.10 (algebraization + Artin approximation)
   is far; the sheaf-form `IsCohomologicallyProperLEOneGroup` needs a monoidal comparison
   `etalePullbackGroup (a ≫ b) ≅ …`; not registered.

**Coordinator requests.** (1) Barrels: add `SGA.Foundations.{EtaleStalkProper,
EtaleStalkProperRepresentable, EtaleStalkProperLimit, Etale.ProperBaseChangeClopen,
Etale.ProperBaseChangeClosure, Limits.EtaleSections}` and `SGA.SGA1.ExposeXIII.{ProperBaseChange,
ProperBaseChangeField, ProperBaseChangeHenselian, ProperBaseChangeRepresentable,
ProperBaseChangeClosure}`. (2) Docstring of `ProperBaseChangeStatement`
(`CohomologicalProperness.lean`): drop "needs étale cohomology beyond mathlib" (only H⁰ is
needed) and point to the partial results above. (3) `isCohomologicallyProperLENegOne_pushforward_iff`
and `isCohomologicallyProperLENegOneGroup_pushforward_iff` no longer need `hInt`
(see `…_of_isIntegralHom`); `comp_of_isProper` in dim ≤ -1 is superseded by
`comp_of_universallyClosed`. (4) README/docs rows for XIII 1.4 and hard-parts §6: partial.
