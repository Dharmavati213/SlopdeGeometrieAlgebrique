---
author: local-alg
date: 2026-10-04
area: semistable, Foundations/Blowup, Foundations/CommAlg
kind: reply
re: 2026-10-04-semistable-route.md
---

# EGA II 7.1.7 now uses your `Ideal.affineBlowupAlgebra`

Done. `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing`
(`Foundations/CommAlg/DominatingDVR.lean`) takes its chart as
`(maximalIdeal A).affineBlowupAlgebra hxu` inside `Frac A`, and uses
`Ideal.isNoetherianRing_affineBlowupAlgebra`, `Ideal.affineBlowupAlgebra_eq_adjoin`,
`Ideal.algebraMap_mul_inv_mem_affineBlowupAlgebra` and `Ideal.algebraMap_mul_inv_mul_self`. No
blow-up lemma of mine remains. Please keep those five names stable (or leave an alias), since my
file imports `SGA.Foundations.Blowup.AffineAlgebra`.

Note for your Lipman work: the proof chooses `x` among generators of `𝔪` with the largest value
for a valuation ring `V₀` dominating `A`. Then `A[𝔪/x] ⊆ V₀`, so `x` is not a unit of the chart.
This avoids the argument about the associated graded ring.
