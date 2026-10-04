---
author: xiii213
date: 2026-10-04
area: SGA1 XIII, sga1-oos-coord
kind: handoff
re: 2026-10-04-xiii213-round1.md
---

# XIII.2.13: Serre's p-kernel theorem proved; Abhyankar for 𝔸¹ reduced to patching + case B

The plan in `2026-10-04-xiii213-round1.md` ("Next") is done. New since that entry:

- `SerrePKernel.affineLinePExtension : AffineLinePExtensionStatement p` (Serre 1990, `p`-group
  kernels, `SGA1/ExposeXIII/SerrePKernel.lean`), hence
  `SerrePKernel.abhyankarAffineLine_of_patching_of_caseB : AffineLinePatchingStatement p →
  AffineLineCaseBStatement p → AbhyankarAffineLineStatement p`.
- Pieces: `SerrePKernel.exists_invariant_forall_not_root` (`SerrePKernelProper.lean`: an invariant
  class in `(B ⊗ (ℤ/p)ʳ)^H` that is not `bᵖ - b`, from the degree count),
  `SerrePKernel.exists_lift_of_split` (lifts through split extensions, with domination),
  `exists_lift_of_principal'` (`AffineLinePGroups.lean`: the V.5.11 glue now also says that if
  `ker ψ ⊆ ker ψ'` the covering is dominated by the Galois covering),
  `SerrePKernel.exists_minimal_normal_elementary`, `SerrePKernel.ker_le_of_not_surjective`,
  `SerrePKernel.exists_surjective_of_minimal_ker`, `SerrePKernel.exists_surjective_of_isPGroup_ker`.
- Axioms of `affineLinePExtension`, `abhyankarAffineLine_of_patching_of_caseB`, the S₃/A₄ theorems:
  `propext, Classical.choice, Quot.sound`.

**Barrel (coordinator):** 9 new modules, all mine, none in `lean/SGA/SGA1/ExposeXIII.lean` yet:
`AffineLinePGroups`, `AbhyankarAffineLine`, `AbhyankarAffineLineExamples`, `SerrePKernel`,
`SerrePKernelCounting`, `SerrePKernelFrobenius`, `SerrePKernelLift`, `SerrePKernelProper`,
`SerrePKernelVector`. README out-of-scope row for XIII.2.13 can now say: proved for `p`-groups,
for `S₃` (p = 2) and `A₄` (p = 3), Serre's `p`-kernel theorem proved, and the full statement
reduced to Raynaud's patching and degeneration cases (both stated).

**What remains of XIII.2.13** (research-scale): `AffineLinePatchingStatement` (Harbater/Raynaud
patching; needs Grothendieck existence for proper curves over `k⟦t⟧`, the open
`GrothendieckExistenceStatement`, plus specialization from `k((t))` to `k`, EGA IV 8) and
`AffineLineCaseBStatement` (XIII.2.12 in char 0 / Riemann existence, `SemistableReductionStatement`,
tail analysis). Cheapest entry point for a next round: the algebraic core of formal patching
(Beauville–Laszlo / Milnor patching of finite projective modules and finite étale algebras over
`k⟦t⟧[x]` and its localizations). I did not start it.

**What was hard / lessons.**
- `ZMod p` modules: `Module.finBasis (ZMod p) A` gets "typeclass problem stuck" when the module
  instance is a `let` (`AddCommGroup.zmodModule`) in the same proof; putting the basis in a separate
  lemma with instance arguments (`SerrePKernel.exists_addEquiv_of_zmodModule`) fixed it. Also import
  `Mathlib.Algebra.Field.ZMod`, or `Module.Free (ZMod p) A` is not found.
- Serre's degree count is cleaner than the critic's sketch: the `k`-dimension of `M_{≤E}` is exactly
  linear for large `E` (leading coefficients stabilize), and `℘(M) ∩ M_{≤D}` lies in
  `span(F(X)) + X` with `X = M_{≤D/p}`, of dimension `≤ 2 dim X - dim M_{≤D/p²}`; the
  overlap term is what makes `p = 2` work.
- Frobenius lower bound from `discr(bᵖ) = discr(b)ᵖ` (needs `tr(Mᵖ) = tr(M)ᵖ`, proved via
  `charpoly(Mᵖ) = charpoly(M)^{(p)}`), so the matrix of `bᵢᵖ` is invertible over `k[T]`.
