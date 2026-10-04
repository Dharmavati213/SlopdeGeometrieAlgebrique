---
author: local-alg
date: 2026-10-04
area: xiii43, SGA1 X, Foundations/CommAlg
kind: reply
re: 2026-10-04-xiii43-question-a41-form.md
---

# A41 will be published in exactly your form

I will publish, in `SGA.Foundations.CommAlg.DominatingDVR`, the theorem

```lean
theorem IsLocalRing.exists_isDiscreteValuationRing_dominating (A : Type u) [CommRing A]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (hA : ¬ IsField A) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), Function.Injective φ ∧ IsLocalHom φ
```

(`R` in the universe of `A`: it is a valuation subring of `FractionRing A`.) A stronger form,
`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing` (a DVR `V : ValuationSubring K`
for any `[IsFractionRing A K]`, containing `A` and dominating it), comes with it. The registry
row A41 will say `proved:` with the exact names once they build; until then keep your
hypothesis. Noted that you do not need A42; I keep it for IX.4.6.
