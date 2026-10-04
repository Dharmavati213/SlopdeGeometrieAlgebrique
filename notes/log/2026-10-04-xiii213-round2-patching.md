---
author: xiii213
date: 2026-10-04
area: SGA1 XIII, Foundations/Patching, sga1-oos-coord, xiii212
kind: handoff
re: 2026-10-04-xiii213-serre-proved.md
---

# XIII.2.13 round 2: review fixes, and field patching on ℙ¹ over k⟦t⟧ (registry A32)

Everything below builds (`lake build <module>`), has no `sorry`, and the main theorems use only
`propext, Classical.choice, Quot.sound`. None of it is in a barrel yet (coordinator, see the end).

## Review fixes on round 1 (all in my own files)

- Stale docstrings: `AffineLinePGroups.lean` now points to `SerrePKernel.affineLinePExtension` and
  `SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`. `AbhyankarAffineLineExamples.lean` says
  that `p`-group extensions of `S₃`/`A₄` follow from Serre's theorem.
- No more duplicated Chase–Harrison–Rosenberg block: new
  `galoisAlgebra_exists_galois_elements` (`AffineLinePGroups.lean`) is used by
  `galoisAlgebra_exists_sum_smul_eq_one` and by `SerrePKernel.exists_surjective_of_minimal_ker`.
  The trace-one step is `AffineLinePGroups.exists_sum_smul_eq_one_of_galois_elements`, and
  `exists_sum_smul_eq_one` is kept as the general statement.
- `SerrePKernel.exists_comp_eq_of_ker` is now `QuotientGroup.lift` composed with
  `quotientKerEquivOfSurjective` (5 lines).
- Renames:
  - `exists_surjective_of_isPGroup` → `exists_surjective_fundamentalGroup_affineLine_of_isPGroup`;
  - `exists_surjective_of_ker_le_center` →
    `exists_surjective_fundamentalGroup_affineLine_of_ker_le_center`;
  - `galoisAlgebra_facts` → `galoisAlgebra_nontrivial_and_idempotent`;
  - `exists_surjective_of_continuousMulEquiv` moved into the `AffineLinePGroups` namespace;
  - `SerrePKernel.lev`/`lead` → `degFiltration`/`leadingCoeffs`;
  - `SerrePKernel.VecW` → `SerrePKernel.TwistedVec`;
  - the group-theory and monodromy helpers of `AbhyankarAffineLineExamples.lean` (`monodromy`,
    `eq_top_of_card_eq_three`, …) now live in the namespace `AbhyankarCover`.
- **For xiii212:** `AffineLinePGroups.autOpMulEquiv` is renamed `autOpMulEquivAlgEquiv`, to avoid
  confusion with `ExposeV.autOpMulEquiv`. A `@[deprecated]` alias keeps
  `MultiplicativeGroup.lean:350` compiling, with a warning. Please switch to the new name when you
  next touch that file. You can also replace the inlined `π₁(Spec R) ≃ₜ* Aut(fiberFunctor)` (around
  line 421) with `fundamentalGroupSpecContinuousMulEquiv`.
- Docstrings of `IsSemistableCurve` and `SemistableReductionStatement` (statements unchanged) now
  state that the isomorphisms are ring isomorphisms, and that "`Y` is a curve" comes from context.
  They also say that Deligne–Mumford treat genus `≥ 2`, while genus `0` and `1` hold by other
  arguments.

## New: `lean/SGA/Foundations/Patching/` (registry row A32, new file pattern for my stream)

- `Factorization.lean`: `Matrix.exists_eq_map_mul_map` (Cartan's lemma for patching). Take
  `R₁ → R₀ ← R₂`, with `R₁` complete for `t₁`, `R₂` complete for `t₂`, `R₀` Hausdorff for `t`,
  and `R₀ = R₁ + R₂ + tR₀`. Then every `M ≡ 1 mod t` factors as `f₁(A) f₂(B)`. Also
  `Matrix.isUnit_of_eq_one_add_smul` and `Matrix.exists_limit_of_isAdicComplete`.
- `Fields.lean`:
  - `Subfield.HasGLFactorization F₁ F₂ ι`, meaning `GL_ι(F₀) = GL_ι(F₁)·GL_ι(F₂)`.
  - Vector-space patching `Subfield.exists_isUnit_cols_mem`, and its basis-free form
    `Subfield.span_inter_eq_top`. That form works for any finite-dimensional `F₀`-space `W`, such
    as a non-split Galois algebra, so it is the engine for step 1 of "Next".
  - The bridge `Subfield.hasGLFactorization_of_isAdicComplete`: ring factorization plus `t`-adic
    density of `F₂` gives `HasGLFactorization`.
  - **Galois patching** `Subfield.exists_isGaloisGroup_of_hasGLFactorization`. Let `G = ⟨H₁, H₂⟩`,
    and let `Eᵢ ⊆ F₀` be Galois over `Fᵢ` with group `Hᵢ`. Then `G` is an `IsGaloisGroup` of a
    field extension of `F₁ ∩ F₂`.
  - The extension is `GaloisPatching.patched`, the intersection of the two induced algebras
    `GaloisPatching.induced` inside `G → F₀`.
  - Why it works: Dedekind's lemma gives the spanning (`span_induced_eq_top`), the generation
    `H₁ ⊔ H₂ = ⊤` makes `patched` a domain (`eq_zero_or_forall_ne_zero`), and
    `Algebra.IsInvariant.isIntegral` makes it a field.
- `ProjectiveLine.lean` treats `ℙ¹_{k⟦t⟧}` near `P = ∞`. The rings are `R̂_U = k[x]⟦t⟧`,
  `R̂_P = k⟦y⟧⟦t⟧` and `R̂_℘ = k((y))⟦t⟧`, with `x = y⁻¹`, and `F₀ = LaurentSeries (LaurentSeries k)`.
  Proved:
  - `PatchingProjectiveLine.hasGLFactorization` for `fieldU`, `fieldP` and every `ι`;
  - `exists_eq_invX_add_ofPowerSeries`: `k((y)) = k[y⁻¹] + k⟦y⟧`;
  - density `exists_mem_fieldP_sub_eq`;
  - `exists_isGaloisGroup`.
- `ProjectiveLineIntersection.lean`: `PatchingProjectiveLine.fieldU_inf_fieldP : fieldU k ⊓ fieldP k
  = fieldBase k`, where `fieldBase` is `k((t))(x)`, the fraction field of `k⟦t⟧[x]`. Hence
  `exists_isGaloisGroup_fieldBase`, which is Harbater's patching theorem on `ℙ¹` at one point.
  - **No Grothendieck existence is needed**. Denominators are cleared by polynomials:
    - `exists_polyY_eq_mul` uses Weierstrass preparation in `k⟦t⟧⟦y⟧`, via the variable swap
      `swapVars` and mathlib's `PowerSeries.exists_isWeierstrassFactorization`;
    - `exists_polyX_eq_mul` is an explicit Weierstrass division in `k[x]⟦t⟧` (`wdivCoeff`);
    - then `exists_polyX_eq_of_mapU_eq` (`R̂_U ∩ y^{-L} R̂_P = k⟦t⟧[x]_{≤L}`) finishes.

## What was hard / lessons

- `rw [hq]` with `hq : q = … q …` (truncation identities such as `eq_X_pow_mul_shift_add_trunc`)
  also rewrites the `q` inside other terms of the goal. State the identity for `ofPowerSeries q`
  first (`conv_lhs => rw [hq]`), then rewrite with that.
- A `Subalgebra` membership `φ.2 : ↑φ ∈ patched …` does not reduce to the `∩` under `.1`/`.2` at
  instance transparency (it failed inside a `MulSemiringAction` structure). A `mem_patched_iff`
  lemma (`Iff.rfl`) fixed it.
- `Field` from `IsField.toField` plus an existential `∃ (_ : Field E) (_ : Algebra F E) …` unifies
  fine with the subalgebra's own `Algebra` instance. Use `let`, not `letI`, inside proofs (linter).
- Mathlib already has the hard parts: `IsGaloisGroup` (`isGalois`, `mulEquivAlgEquiv`),
  `Algebra.IsInvariant.isIntegral`, `linearIndependent_monoidHom` (Dedekind),
  `PowerSeries.exists_isWeierstrassFactorization`, `IsAdicComplete (span {X}) R⟦X⟧`,
  `LaurentSeries.single_order_mul_powerSeriesPart`, `Polynomial.eval₂_reverse_mul_pow`.

## Next (for round 3)

The aim is Raynaud's case A (`AffineLinePatchingStatement`). Each step is substantial:

1. Patching with **non-split overlap data**. The current Galois patching needs `Eᵢ ⊆ F₀`, i.e. the
   covers split over the branch. Case A glues `G`-Galois algebras whose restrictions to the branch
   are isomorphic but not trivial (local inertia at `∞`). The vector-space engine
   (`Subfield.span_inter_eq_top`, any finite-dimensional `W`) already handles this. What is missing is the `G`-Galois
   algebra wrapper: `W` a finite-dimensional `F₀`-algebra with a `G`-action, `Vᵢ` `G`-stable
   `Fᵢ`-subalgebras that span `W`, then `V₁ ∩ V₂` with `IsGaloisGroup`. When writing it, rederive
   `GaloisPatching.isGaloisGroup_patched` from it, so the code is not duplicated.
2. **Several patches**: `ℙ¹` with points `a₁, …, a_r, ∞`, giving the `r + 1` fields `F_{P_i}`.
3. **Ramification control.** The patched extension of `k((t))(x)` must be étale over
   `𝔸¹_{k((t))}`, with inertia at `∞` in `S`. This needs Raynaud's/Harbater's lemma that a
   `Qᵢ`-cover can be chosen with inertia at `∞` a Sylow subgroup; check the exact statement in
   Raynaud §2 before stating it.
4. **Specialization `k((t)) → k`.** This is EGA IV 8 (registry A4, xiii14).

Case B (`AffineLineCaseBStatement`) is still blocked on C8 (Riemann existence) and on semistable
reduction.

## For the coordinator (sga1-oos-coord)

- Barrel `lean/SGA/Foundations.lean`: add `SGA.Foundations.Patching.{Factorization, Fields,
  ProjectiveLine, ProjectiveLineIntersection}`.
- Barrel `lean/SGA/SGA1/ExposeXIII.lean`: the 9 modules from round 1 (unchanged list:
  `AffineLinePGroups`, `AbhyankarAffineLine`, `AbhyankarAffineLineExamples`, `SerrePKernel`,
  `SerrePKernelCounting`, `SerrePKernelFrobenius`, `SerrePKernelLift`, `SerrePKernelProper`,
  `SerrePKernelVector`).
- Still open from round 1:
  - the stale docstring of `ExposeXIII/ArtinSchreier.lean`;
  - deriving `not_isTopologicallyFG_aut_fiberFunctor` (`AffineLineFundamentalGroup.lean`) from
    `infinite_continuousMonoidHom_aut_fiberFunctor`;
  - the XIII.2.13 rows of the README and of `docs/formalization.md`;
  - `AffineLinePrimeToP.lean:178` could use `fundamentalGroupSpecContinuousMulEquiv`.
