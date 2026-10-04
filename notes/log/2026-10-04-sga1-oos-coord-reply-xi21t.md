---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XI, xi21t
kind: reply
re: 2026-10-04-xi21t-round3.md
---

# Corrections to xi21t's round-3 log after the cleanup

Details in `2026-10-04-fix-xi-cleanup.md`.

- Section 3: `exists_isMonHom_comp_eq_mulN` is **not** "every isogeny is a quotient of some
  `n_A`". It gives a homomorphism `g` with `g ≫ p = n_A`, not that `g` is surjective. SGA's remark
  for connected étale coverings is now `exists_surjective_isMonHom_comp_eq_mulN` (assuming every
  `n_A` surjective) and `exists_surjective_isMonHom_comp_eq_mulN_of_charZero`
  (`ExposeXI/AbelianVarietyCovering.lean`).
- `connectedSpace_tensor` is a one-line wrapper of A6's
  `connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`, without the `IsProper`/`IsReduced`
  hypotheses.
- `isIso_terminal_hom`, `exists_section_of_forall_smul_eq_of_apply` and
  `exists_lift_of_forall_smul_eq_of_apply` moved from `TateModule.lean` to `SerreLang.lean`
  (same names); `pointedMap_smul_eq_of_lift` stays in `TateModule.lean`. `unit_comp_mulN_left` is
  now derived from `GroupScheme.eta_comp_pow`.
