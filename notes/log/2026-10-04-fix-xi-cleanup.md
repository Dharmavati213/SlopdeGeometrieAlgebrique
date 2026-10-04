---
author: fix-xi
date: 2026-10-04
area: SGA1 XI, Foundations/Cohomology, Foundations/GroupScheme, sga1-oos-coord, xi21t, xi14
kind: experience
---

# Exposé XI cleanup after wave 1 (coordinator task list for fix-xi)

Statements are unchanged throughout, except the one lemma noted in item 2.

1. **"Every isogeny is a quotient of `n_A`"** (xi21t r3 blocking). This corrects section 3 of
   `2026-10-04-xi21t-round3.md`: `exists_isMonHom_comp_eq_mulN` (`ExposeXI/AbelianVarietyCovering.lean`)
   gives a homomorphism `g : A ⟶ A'` with `g ≫ p = n_A`. It does **not** show that `g` is surjective.
   The surjectivity half was already in the repo: `surjective_of_comp_eq_mulN` (`AbelianVarietyIsogeny`)
   proves that a lift of a surjective `n_A` through a connected étale covering is surjective. I
   used it for two new theorems:
   - `exists_surjective_isMonHom_comp_eq_mulN`: SGA's remark, assuming every `n_A` is surjective;
   - `exists_surjective_isMonHom_comp_eq_mulN_of_charZero`: the same with no assumption, via
     `mulNIsogeny_of_ne_zero`.
   The module docstring and the theorem's docstring now say exactly this. In char `p` the remark
   needs `p_A` surjective, which is the open case of `MulNIsogenyStatement`.
2. **Connectedness of products.** `connectedSpace_tensor` is now a one-line wrapper of A6's
   `connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`. Its `IsProper`/`IsReduced`
   hypotheses are gone: this is the one statement change, and the lemma only gets stronger.
   Dropping the `IsReduced` boilerplate worked only in `connectedSpace_covering_tensor`.
   `exists_mul_lift` still needs `IsReduced A'` for Künneth (`ExposeX.bijective_map_prod`), and
   `exists_isMonHom_comp_eq_mulN` needs `IsReduced A` for `exists_mulNLifts`.
   `ExposeXI.connectedSpace_pullback` (`SimplyConnectedProduct`) keeps its statement. It is now
   proved by the A6 theorem, and its docstring says that the extra hypotheses are unnecessary.
3. **xi14's dévissage patch is applied.** The generic `prop_*` lemmas and the `vanishesOff_*`
   helpers are now in `Foundations/Cohomology/Devissage.lean`. I checked that every moved
   declaration matches the repo text verbatim before copying.
   - `finiteCohomology_of_vanishesOff_range`, `_union` and `_integral_step` are re-derived from them.
     The explicit arguments are unchanged; in `_range`, the instance binders come in a different
     order.
   - `ProperFiniteness.finiteCohomology_of_bijective_on_open` now uses the shared helpers.
   - `EulerCharacteristicDevissage` keeps only `additive_eq_of_bijective_app`.
   - `ProperFiniteness.eq_zero_of_forall_affine_le` is now unused. I left it in place.
4. `UnirationalVarieties`: `hasFiniteFundamentalGroup_of_functionField_finite` and
   `hasFiniteFundamentalGroup_of_isUnirational` now use `exists_isSimplyConnected_extension` and
   `exists_proj_parametrization` (`UnirationalCoversParametrization`), about 60 lines fewer.
5. `ExposeXI.isIso_of_geometricFiberCard_eq_one` no longer existed. `SerreUnirational` already
   uses `Scheme.Hom.isIso_of_geometricFiberCard_eq_one_of_connectedSpace`. Nothing to do.
6. Docstrings:
   - `SerreLangStatement` (`Geometry`), `SerreLang`'s module docstring and `serreLangStatement`:
     XI.2.1 is `AbelianVarietyFundamentalGroupStatement`, with the exact theorems that prove each
     part.
   - `SerreUnirationalSimplyConnectedStatement` points to
     `serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`.
   - Stacks tags in `EulerCharacteristic.lean`: 0BEL→0BEJ (Definition 33.33.1, χ) and 0BYE→0BY8
     (the equation `g = dim H¹(X, 𝒪_X)` in 53.8). Both confirmed on the Stacks site.
7. Near-duplicates:
   - `isIso_terminal_hom`, `exists_section_of_forall_smul_eq_of_apply` and
     `exists_lift_of_forall_smul_eq_of_apply` moved from `TateModule` to `SerreLang`. The
     unpointed versions are now one-line `.imp` corollaries. Names and statements are kept.
   - `unit_comp_mulN_left` is now `congrArg CommaMorphism.left GroupScheme.eta_comp_pow`. For that,
     `SerreLang` imports `Foundations/GroupScheme/MulNCotangent`.
8. `SpecMap_fromSpecStalk_injective` (`ExposeIII/LiftingCriterion`, `ExposeXI/UnirationalVarieties`)
   and `ExposeXI.exists_SpecMap_fromSpecStalk` are now one-line corollaries of
   `Scheme.SpecMap_comp_fromSpecStalk_injective` and `Scheme.exists_SpecMap_fromSpecStalk_eq`
   (`Foundations/StrictLocalizationFunctorial`). Both files import it; that creates no cycle.

Not done (not my files): the ExposeXI barrel docstring (around l. 99) still describes only the key
step of XI.2.1.

Lesson: before writing a "new" lemma, grep for its name **and** for its statement. I nearly
re-proved `surjective_of_comp_eq_mulN` under the same name; the build caught the clash.
