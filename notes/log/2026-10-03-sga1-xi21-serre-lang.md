---
author: sga1-xi21
date: 2026-10-03
area: SGA1 XI, SGA1 V, sga1-oos
kind: experience
---

# XI.2.1 (Serre–Lang key step) is proved, no abelian-variety theory needed

`SGA.SGA1.ExposeXI.serreLangStatement : SerreLangStatement.{u}` is in the new file
`lean/SGA/SGA1/ExposeXI/SerreLang.lean` (about 360 lines), imported by the barrel
`lean/SGA/SGA1/ExposeXI.lean`. `#print axioms` lists only propext, Classical.choice and Quot.sound.
`lake build SGA.SGA1.ExposeXI.SerreLang` and `lake build SGA.SGA1.ExposeXI` both pass. No shared
file was touched (Geometry, AbelianFundamentalGroup, Exposé V and X, Foundations are unchanged).

Route (the coordinator's plan, slightly simplified):
1. `pointedMap Ω f t s h : π₁(T, t) →* π₁(S, s)` for `t ≫ f = s`, defined as `autMap (pullback f)`
   with the iso `pullbackFiberIso ≪≫ fiberCongr h`. If the target group is commutative, `autMap H e`
   depends neither on `e` nor on `H` up to iso (`autMap_eq_of_comm`, `autMap_eq_of_iso_of_comm`).
   That gives strict functoriality (`pointedMap_pointedMap`, `pointedMap_id`) and kills every
   conjugation of V.6.3. Each conjugation is by an element of `Aut F_e`, since both isos have the
   same source and target.
2. `pointedMap_lift_comp_mul`: on an H-space, `x ↦ m(u x, v x)` induces `σ ↦ u_*σ · v_*σ`.
   Künneth (`ExposeX.bijective_map_prod`, injectivity only) shows
   `w_*σ = i₁_*(u_*σ) · i₂_*(v_*σ)` in `π₁(X ×ₖ X, c)`, then apply `m_*`. Every composite used
   lands in `π₁(X, e)`, so commutativity of `π₁(X ×ₖ X)` is never needed.
   `pointedMap_mulN` gives `(n_A)_* σ = σⁿ` by induction (`pow_succ`, `Hom.mul_def`).
3. `exists_lift_of_forall_smul_eq`, the lifting criterion: if `u_*π₁` fixes a point of `F_s(Y)`,
   then `u^•Y` has a section (`exists_section_of_forall_smul_eq`). The connected component through
   the fixed point has a one-point fibre, so it maps isomorphically to the final object.
4. `pow_card_smul_eq`: in a commutative group acting transitively on `d` points, the stabilizer is
   normal of index `d`, so `σ^d` fixes everything (`Subgroup.pow_index_mem`). Take `n = d`, the
   degree.

What was hard: almost nothing. Two traps:
- `simp` does not fire `pullback.lift_fst` inside `e ≫ pullback.lift u v _ ≫ pullback.fst _ _` here
  ("simp made no progress"), but `rw` does. State `w ≫ fst = u` etc. as `have`s and rewrite.
- `IsReduced A.left` comes from `ExposeII.isReduced_of_smooth_of_isReduced A.hom`.

Not done: SGA's XI.2.1 proper, `π₁(A) ≅ lim_n K_n` (Tate module), is not stated anywhere. It needs
the kernels `A[n]` (finite, étale for `p ∤ n`) and that every isogeny is a quotient of some `n_A`.
`SerreLangStatement`'s docstring already calls itself "the key step", so the docs must not claim
the Tate-module isomorphism. For the coordinator: the docstring of `SerreLangStatement` in
`Geometry.lean` still says "statement only". I updated the barrel docstring, `notes/topics/hard-parts.md`
(marked resolved) and `strategy.md`.

General lemmas that could move to Exposé V (`FundamentalGroupFunctoriality.lean`), if someone is
rebuilding it anyway: `autMap_eq_of_comm`, `autMap_eq_of_iso_of_comm`, `pointedMap` and its API,
`exists_section_of_forall_smul_eq`, `exists_lift_of_forall_smul_eq`. `pow_card_smul_eq` is pure
group theory, mathlib-style.
