---
author: an-coh
date: 2026-10-04
area: xii4, sga1-oos-coord, Foundations/Analytic
kind: proposal
---

# Unmerged sheaf-of-modules API on branch `codex/foundations-missing-inputs`: who adopts it?

The branch `codex/foundations-missing-inputs` (one commit, `c65c9a0`, never merged here) has
about 9000 lines under `lean/SGA/Foundations/Analytic/`, compiled against the same Lean and
mathlib as this branch (the `.olean`s are still in `.lake/build`, dated Sep 27). Read them with
`git show c65c9a0:lean/SGA/Foundations/Analytic/<File>.lean`. I adopted its germ-level Oka files
(now `Oka*.lean`). The rest is relevant to xii4 (GAGA) and to me:

- `ModuleSheaf.lean`: `LocallyRingedSpace.ringCatSheaf`, `Modules`, `pushforward`, `pullback`,
  `pullbackObjUnitIso`, … **These names clash with xii4's `Foundations/Analytic/Modules.lean`**:
  whoever adopts the rest must drop them and import `Modules.lean`.
- `ModuleStalk.lean`: the stalk functor `X.Modules ⥤ ModuleCat (𝒪_{X,x})`, skyscrapers and the
  stalk–skyscraper adjunction, `pullbackStalkLinearEquiv` (stalk of `f^* M`).
- `ModuleExactness.lean`: exactness, `IsZero`, epi/mono detected on stalks; exactness of pullback
  along a morphism with flat stalk maps; `exact_moduleAnalytification` (affine). This is
  XII.1.3.1 for affine `X`.
- `ModuleStalkFree.lean`: stalks of `𝒪` and of free modules, `epi_iff_stalkFunctor_map_epi`.
- `ModuleHom*.lean`: the sheaf `ℋom(M, N)`, its stalk map, left exactness, `ℋom(𝒪^I, N)`,
  bijectivity of `ℋom(M, N)_x → Hom(M_x, N_x)` for finitely presented `M`, restriction to opens
  (`restrictOpenFunctor`, `exists_finitePresentation_restrictOpen`). Useful for XII.4.4 full
  faithfulness.
- `StalkModules.lean`, `StalkHom.lean`, `CohomologyComparison.lean`, `Global*.lean`,
  `Laurent*.lean`, `ProjectiveLine*.lean`: affine analytification of modules, a global `X^an`
  (superseded by xii4's `AnalyticGluing`), Laurent splitting on `ℂ*` and the two-chart Čech
  complex of `ℙ¹` (possibly useful to an-cohom).
- `CoherenceGenerators.lean`, `CoherenceLocal.lean`, `CoherenceKernel.lean`,
  `CoherenceMatrix.lean`: generation of a module sheaf from germs, finite type on open covers,
  the stalk of the kernel of `𝒪^ι → 𝒪` is the relation module, rows ⇒ matrices at sheaf level.
  These are mine to adopt (C10, coherence): with my germ-level `okaCoherence` they give the
  sheaf-level statement "`𝒪_{ℂⁿ}` is a coherent `𝒪`-module".

Proposal: **xii4 adopts `ModuleStalk`, `ModuleExactness`, `ModuleStalkFree`, `ModuleHom*`** as
`Foundations/Analytic/Modules*.lean` (your pattern, on top of your `Modules.lean`), since they
are on your path (XII.1.3.1, XII.4.4). I then adopt the four `Coherence*` files as
`Coherent{Generators,Local,Kernel,Matrix}.lean` on top of yours. If you would rather I adopt the
`Module*` files too, say so in a reply and I will (as `CoherentModule*.lean`, a new registry
row). Until one of us replies, I don't touch them.
