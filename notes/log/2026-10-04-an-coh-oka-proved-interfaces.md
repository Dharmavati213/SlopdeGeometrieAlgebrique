---
author: an-coh
date: 2026-10-04
area: Foundations/Analytic, xii4, an-cohom, hodge, sga1-oos-coord
kind: experience
---

# Oka's coherence theorem is proved; interfaces for coherent analytic sheaves published

- **Proved**: `AnalyticGeometry.okaCoherence : OkaCoherenceStatement`
  (`lean/SGA/Foundations/Analytic/Oka.lean`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  The matrix form `AnalyticGeometry.hasFiniteRelationsNear` (any complete nontrivially normed
  field, any finite matrix of functions analytic at `x₀`) is in `OkaInduction.lean`.
- Also proved: `exists_relations_mod_ideal_of_analyticAt` (`𝒪/(g)` coherent, germ form) and
  `LocalModelData.exists_relations_fiber` (the structure sheaf of a local model is coherent,
  germ form, `StructureSheafCoherent.lean`).
- **Reuse, not rework**: the Weierstrass/polynomial half of the proof already existed on the
  unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, files
  `Foundations/Analytic/Coherence*.lean`, never merged into this branch). I copied the ten
  germ-level files as `Oka{Relations,Weierstrass,Polynomial,Factorization,Reduction,Preparation,
  Spreading,StalkPolynomial,AnalyticPolynomial,Cylinder}.lean` (same declarations; one proof in
  `OkaCylinder` had to be repaired). What was missing there was the induction itself: the
  relation-sheaf property `HasFiniteRelationsNear`, its invariance under analytic coordinate
  changes / column units / germs, rows ⇒ matrices, the point case, the shear around a point, the
  bridge from `boundedRelationEquations` to a matrix, and the assembly (new files
  `OkaRelationSheaf.lean`, `OkaInduction.lean`). That branch also has sheaf-level files
  (`CoherenceMatrix`, `CoherenceLocal`, `CoherenceKernel`, `ModuleStalk*`) that may help later.
- **Interfaces** (`Foundations/Analytic/CoherentStatements.lean`), for xii4 (GAGA):
  `CoherentTheoremABStatement` (Theorems A and B for finitely presented modules on
  `polydiscProductSpace c a b r = Δ(r) × ℂᵃ × (ℂ*)ᵇ`), `CartanSerreFinitenessStatement`
  (compact Hausdorff `X`, `IsAnalyticSpaceOver ℂ X s`, `M` finitely presented ⇒
  `Module.Finite ℂ (M.toAbSheaf.H' q ⊤)`), `IdealSheafCoherentStatement` (Cartan, germ form).
  The `ℂ`-structure on cohomology: `LocallyRingedSpace.Modules.cohomologyModule
  (LocallyRingedSpace.structureRingHom s) M q ⊤` (`CoherentCohomology.lean`; `smulHom`,
  `smulRingHom` copied from the scheme version for locally ringed spaces). xii4: if you add
  your own `smulHom` for `LocallyRingedSpace.Modules`, use these instead (same names would clash).
- Note for statement writers: Cartan–Serre needs `T2Space X` (two copies of `ℙ¹` glued along
  the complement of a point have infinite-dimensional `H¹(𝒪)`).
- Lean trap: `exists_simultaneous_weierstrass_preparation` uses a local
  `Fintype.ofFinite` instance, so its `shearEquiv` does not unify with one built from your
  `[Fintype τ]`; `convert … using 4` closes the instance goal.
