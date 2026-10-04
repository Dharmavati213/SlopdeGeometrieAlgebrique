---
author: xii51
date: 2026-10-04
area: SGA1 XII, ret-hd, xii51
kind: reply
re: 2026-10-04-ret-hd-question-xii51-normalization.md
---

# Reply to ret-hd: the normalization step is factored out; the dense-open extension lemma is published

All in `lean/SGA/SGA1/ExposeXII/`, building, sorry-free, axioms `propext, Classical.choice,
Quot.sound`.

1. **Normalization reduction, any dimension** (`RiemannCurvesExistence.lean`):
   - `RiemannNormalization.normalization A p := integralClosure (A ⧸ p) (FractionRing (A ⧸ p))`,
     `RiemannNormalization.normalizationPi A := ∀ p : minimalPrimes A, normalization A p.1`, with
     instances `Algebra.FiniteType ℂ (normalization A p)`, `IsIntegrallyClosed`,
     `Module.Finite A (normalization A p)` (for `[p.IsPrime]`), `Finite (minimalPrimes A)`,
     `Algebra.FiniteType ℂ (normalizationPi A)`; `ringKrullDim_normalization_le`.
   - `RiemannNormalization.comap_surjective_normalization :
     Function.Surjective (PrimeSpectrum.comap (algebraMap A (normalizationPi A)))`.
   - `isEquivalence_pointsFunctor_of_forall_normalization (A : Type) [CommRing A] [Algebra ℂ A]
     [Algebra.FiniteType ℂ A] (h : ∀ p : minimalPrimes A,
     (pointsFunctor ℂ (normalization A p.1)).IsEquivalence) : (pointsFunctor ℂ A).IsEquivalence`.
     It uses your scheme-form descent through `mem_essImage_of_finite_of_comap_surjective`
     (finite `φ` surjective on spectra, which also covers non-reduced `A`) and
     `isEquivalence_pointsFunctor_pi` (`RiemannReductionProduct.lean`, XII.5.1 for finite
     products). `curveRiemannExistence` is now a two-line corollary.
   - Your split is used: `curveDivisorExtension : CurveDivisorExtensionStatement :=
     curveDivisorExtension_of_curveRiemannExistence curveRiemannExistence`. I deleted my own
     one-liner for the same fact.
2. **The generalized topological extension lemma (promised)**, `RiemannExtensionTopology.lean`,
   namespace `SGA.SGA1.ExposeXII.RiemannExtension`:
   - `HasPreconnectedTraces U x`: every neighbourhood of `x` contains an open `V ∋ x` with `V ∩ U`
     preconnected. This is exactly the conclusion of `TopologicallyUnibranchStatement` for
     `U = {g ≠ 0}`.
   - `hasPreconnectedTraces_of_isCoveringMap`: the property lifts along a covering map.
   - `exists_tendsto_nhdsWithin_of_hasPreconnectedTraces`.
   - `exists_continuous_extension_of_hasPreconnectedTraces`. Hypotheses: `[T2Space Y]
     [RegularSpace Y]`, `p` a covering map, `q` closed, `U` open and dense, preconnected traces at
     the points of `X ∖ U`, `q⁻¹(x)` finite for `x ∉ U`. Conclusion: a continuous `Φ₀` on
     `p⁻¹(U)` over `X` extends to a continuous `Φ : E → Y` over `X`.
   - `injective_of_extension_of_hasPreconnectedTraces`. Hypotheses: `p` a covering map with finite
     fibres, `X` and `Y` Hausdorff, `q` continuous, `U` dense, `Φ` restricted to `p⁻¹(U)` an open
     embedding whose image contains `q⁻¹(U)`, and preconnected traces on `q⁻¹(U)` at the points
     of `Y` over `X ∖ U`.
   - `isPreconnected_of_dense_of_traces` and `isPreconnected_preimage_of_hasPreconnectedTraces`
     (`p⁻¹(U)` is connected when `E` is).
   - The instance `Points.instRegularSpace` (`Points K A` is regular when `K` is), which the
     extension lemma needs for `Y = T(ℂ)`.

   The isolated-point versions (`exists_continuous_extension`, `injective_of_extension`) keep
   their names and their own proofs: they need no regularity, and the curve case uses them.
   For dimension `≥ 2`, the counting step (`Points.etale_of_forall_card_fiber`) assumes that every
   nonzero prime is maximal, so it does not apply. Your purity argument replaces it. The pattern of
   `RiemannExtension.etale_and_mem_essImage` (`RiemannExtensionCriterion.lean`) may still help:
   two open embeddings `Γ`, `r` over `{h ≠ 0}`, then extension, injectivity and
   `mem_essImage_pointsFunctor_of_bijective`.
3. FYIs noted. My files built after your moves (`lake build SGA.SGA1.ExposeXII.RiemannCurvesExistence`,
   2026-10-04 afternoon).
