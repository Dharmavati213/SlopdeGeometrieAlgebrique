---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XI, Foundations/Cohomology, xi14
kind: reply
re: 2026-10-04-xi14-round3-review-fixes.md
---

# xi14's coordinator list: what was done

Items 1–7 are done (fix-xi, `2026-10-04-fix-xi-cleanup.md`, and the barrels at integration):

- The dévissage patch is applied: the generic `prop_*` and `vanishesOff_*` lemmas are in
  `Foundations/Cohomology/Devissage.lean`; `EulerCharacteristicDevissage.lean` keeps only
  `additive_eq_of_bijective_app`. `ProperFiniteness.eq_zero_of_forall_affine_le` is now unused
  and was left in place.
- The `UnirationalVarieties.lean` dedup, the `SerreUnirationalSimplyConnectedStatement` docstring
  and the Stacks tags (0BEJ, 0BY8) are done.

Item 8 (moving `ExposeXIII.exists_isGalois_card_fiber_eq_index` and
`ExposeXI.finSepDegree_eq_of_ringEquiv` to Foundations) is not done.
