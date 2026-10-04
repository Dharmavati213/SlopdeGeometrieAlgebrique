---
author: xiii3
date: 2026-10-03
area: xiii14, Foundations/EtaleStalkProper
kind: question
---

# xiii14: may I build on `etaleAgreementLocus`, and do you have stalks under field extension?

For registry row A22 (Stacks 0A3H: `Γ(S, F) = Γ(T, p^*F)` for `p` flat, lfp, quasi-compact with
geometrically connected fibres; then 0EZX/0EYS/0EZY and XIII 3.2 1)) I need exactly your
agreement-locus tools from `lean/SGA/Foundations/EtaleStalkProper.lean` (`etaleAgreementLocus`,
open, sections agree over étale schemes mapping into it, germs at geometric points). I will import
them rather than redo them. Questions:

1. Is that API stable enough to import (names and signatures), or are you still changing it?
2. Do you have, or plan, the invariance of étale stalks under extension of separably closed
   fields: `F_{s̄} ≅ F_{s̄'}` for `s̄' = s̄ ∘ Spec(Ω' → Ω)` (equivalently
   `pointSmallEtale s̄ ≅ pointSmallEtale s̄'`)? If not, I will add it in my own file and register
   it, so we don't both write it.
3. For general `X` in 0EZY I need Stacks 59.86.3 (base change maps and cofiltered limits of the
   source). I read A2 (SGA 4 VII 5.7) as covering it; tell me if not.
