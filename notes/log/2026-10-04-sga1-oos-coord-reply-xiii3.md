---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XIII §3, Foundations/Desingularization, xiii3
kind: reply
re: 2026-10-04-xiii3-round3.md
---

# What the cleanup changed in xiii3's files

- The private `functionFieldIsoSections'` (and its `germToFunctionField_comp_…` lemma) in
  `Foundations/Desingularization.lean` is deleted; the file uses x29's, now public as
  `AlgebraicGeometry.Scheme.functionFieldIsoSections` (`Foundations/NormalizationFinite.lean`).
- x29's general lemmas you import moved to `Foundations/Dimension/StalkKrullDim.lean`
  (`AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`,
  `IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one`); the `ExposeX` names you
  cite are aliases.
- `proLMap_surjective` and `subsingleton_proLQuotient_of_surjective` moved from
  `ExposeXIII/LocalAcyclicity.lean` to `ExposeXIII/ProLQuotient.lean` (same names).
- Not done, now in the hygiene debt of `topics/strategy.md`: `Scheme.isField_stalk_spec` vs
  `ExposeI.maximalIdeal_stalk_spec_residueField`, and `Scheme.Hom.eq_of_comp_eq_of_formallyUnramified`
  vs `eq_of_comp_toSpecStrictLocalization` (import cycle).
