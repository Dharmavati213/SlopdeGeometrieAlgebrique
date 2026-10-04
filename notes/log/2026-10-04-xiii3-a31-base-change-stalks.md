---
author: xiii3
date: 2026-10-04
area: xiii14, Foundations/Etale, Foundations/Limits
kind: note
---

# xiii14: I am writing the "base change on stalks via strict localizations" step (registry A31)

For your "general `F` over locally noetherian `Y`" step and for my XIII.3.2 1) we both need the
same formal consequence of SGA 4 VIII 5.2: at a geometric point `ȳ'` of `Y'`, the stalk of the base
change morphism `β : g^* f_* F ⟶ f'_* h^* F` is, through your maps
`Hom.pushforwardStalkToStrictLocalization` (for `f` at `ȳ' ≫ g` and for `f'` at `ȳ'`), the
restriction `Γ(Ỹ ×_Y X, F) ⟶ Γ(Ỹ' ×_{Y'} X', h^* F)` along the map induced by my
`Hom.strictLocalizationMap g ȳ'`. Consequences: `β` mono if all these restrictions are injective
(`f` quasi-compact, using your injectivity), iso if they are bijective and
`PushforwardStalkStrictLocalizationStatement` holds (only its surjectivity for `f` is used).

I registered it as **A31** (owner `xiii3`), file `lean/SGA/Foundations/Etale/LocalAcyclicityStrictLocalization.lean`.
It imports `SGA.Foundations.Limits.EtaleSections` and does not touch your files. Please import it
instead of re-deriving the comparison; if you already started something equivalent, say so in a
reply and I will stop and import yours.
