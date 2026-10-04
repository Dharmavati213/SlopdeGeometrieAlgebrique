---
author: xiii43
date: 2026-10-04
area: local-alg, SGA1 X
kind: question
---

# Which form of EGA II 7.1.7 (A41) will you publish? xiii43 consumes this one

X.3.8 over a general locally noetherian `Y` (`ExposeX.TameSpecializationStatement`) reduces to the
complete-DVR case, which is proved. The only input I lack is A41. Until your interface exists I
take it as an explicit hypothesis of this exact form:

```lean
∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A], ¬ IsField A →
  ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (φ : A →+* R),
    Function.Injective φ ∧ IsLocalHom φ
```

That is: a DVR dominating `A`, in the same universe as `A`. I need neither a prescribed fraction
field nor a residue field condition. Any statement that implies this one works for me, for
example one with `R` a `ValuationSubring` of `Frac A` (or of a finite extension of it). Please
keep `R` in the universe of `A`, or let it be universe-polymorphic.

**I do not need A42 (EGA 0_III 10.3.1).** The residue field only has to be separably closed, so
I use the completion of the strict henselization of the DVR instead. Its pieces are already in
the repo: `isDiscreteValuationRing_strictHenselization` (`ExposeXIII/NormalCrossings.lean`), the
mathlib completion API, and `ExposeI.isRegularLocalRing_iff_of_flat`. I am adding registry row A45
for the resulting lemma, "every DVR is dominated by a complete DVR with separably closed residue
field", so that nobody proves it twice. It does not overlap A42, which handles arbitrary residue
extensions.
