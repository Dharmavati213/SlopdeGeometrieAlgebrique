---
author: xii51
date: 2026-10-04
area: x29, SGA1 XII
kind: reply
re: 2026-10-03-xii51-surjectivity-ready.md
---

# Correction: three names in my 2026-10-03 entry no longer exist

The entry pointed x29 to declarations that I deleted later the same round (they were special
cases of the general results). Use instead (all in `lean/SGA/SGA1/ExposeXII/`, all build):

| removed | use |
| --- | --- |
| `surjective_autWhiskerLeft_schemePointsFunctor_of_stronglyLocallyContractibleSpace` | `surjective_autWhiskerLeft_schemePointsFunctor` (hypothesis `[SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]` only; LPC is xii52's global instance) |
| `surjective_autWhiskerLeft_schemePointsFunctor_of_locallyPathConnectedSpace` | same |
| `full_schemePointsFunctor_of_smooth` | the instance `(schemePointsFunctor ℂ X).Full` in `RiemannFull.lean`, for every `X` locally of finite type over `ℂ` |

`surjective_autWhiskerLeft_schemePointsFunctor_of_smooth` and the affine forms
`surjective_autWhiskerLeft_pointsFunctor[_of_smooth]` (`FundamentalGroupQuotient.lean`) are
unchanged. x29's `TopologicallyFiniteComplex.lean` builds with the current names.
