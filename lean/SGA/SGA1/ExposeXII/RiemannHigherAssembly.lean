/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherGenericEtale
import SGA.SGA1.ExposeXII.RiemannHigherSmooth
import SGA.SGA1.ExposeXII.RiemannCurvesExistence
import SGA.SGA1.ExposeXII.RiemannLocalChart
import SGA.SGA1.ExposeXII.StatementCorollaries

/-!
# SGA 1, Exposé XII, 5.1 in higher dimension: assembly

The route of `SGA.SGA1.ExposeXII.RiemannHigher` (this project's, not SGA's), as implications
between the interfaces:

* `genericRiemannExistence_of_generic_hypersurfaceComplement`: the generic form of XII.5.1
  (`GenericRiemannExistenceStatement`: every covering is algebraic over a dense basic open) holds
  for all integral affine `X` once it holds for the complements of hypersurfaces in `𝔸ⁿ`
  (`GenericHypersurfaceComplementStatement`), by Noether normalization and generic étaleness
  (`exists_finiteEtale_hypersurfaceComplement`) and the passage to finite étale coverings
  (`RiemannHigher.IsGenericallyAlgebraic.of_compCovering`);
* `riemannExistence_of_generic_of_normalDivisorExtension`: XII.5.1 (`RiemannExistenceStatement`)
  from the generic form and the extension of coverings across divisors of normal varieties
  (`NormalDivisorExtensionStatement`), through the reduction to normal domains
  (`isEquivalence_pointsFunctor_of_forall_normalization`); likewise the scheme form and XII.5.2.
-/

noncomputable section

open CategoryTheory Topology Opposite CommAlgCat TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

open RiemannHigher

/-- The generic form of XII.5.1 for complements of hypersurfaces in `𝔸ᵈ` (statement only): for
every nonzero `f ∈ ℂ[x₁, …, x_d]`, every finite covering of `(𝔸ᵈ ∖ V(f))(ℂ)` is algebraic over a
dense basic open subset. -/
def GenericHypersurfaceComplementStatement (d : ℕ) : Prop :=
  ∀ f : MvPolynomial (Fin d) ℂ, f ≠ 0 →
    ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ (Localization.Away f))),
      IsGenericallyAlgebraic E

/-- XII.5.1 for hypersurface complements implies its generic form. -/
theorem genericHypersurfaceComplement_of_hypersurfaceComplement {d : ℕ}
    (H : HypersurfaceComplementRiemannExistenceStatement d) :
    GenericHypersurfaceComplementStatement d := fun f hf E ↦
  have := H f hf
  IsGenericallyAlgebraic.of_mem_essImage (Functor.EssSurj.mem_essImage _ E)

/-- **The generic form of XII.5.1 from hypersurface complements.** If every finite covering of the
complement of a hypersurface in `𝔸ᵈ` (every `d`) is algebraic over a dense basic open subset, then
so is every finite covering of `X(ℂ)`, `X = Spec A`, `A` a domain of finite type over `ℂ`: by
Noether normalization and generic étaleness, some `A_g` is finite étale over a hypersurface
complement (`exists_finiteEtale_hypersurfaceComplement`). -/
theorem genericRiemannExistence_of_generic_hypersurfaceComplement
    (H : ∀ d, GenericHypersurfaceComplementStatement d) : GenericRiemannExistenceStatement := by
  intro A _ _ _ _ E
  obtain ⟨s, r, hr, T, g, hg, ⟨e⟩⟩ := exists_finiteEtale_hypersurfaceComplement A
  let := algebraOfFiniteEtale ℂ (Localization.Away r) T
  let ET := (baseChange (pointsHom e.symm.toAlgHom)).obj (restrictAway g E)
  have hT : IsGenericallyAlgebraic ET :=
    IsGenericallyAlgebraic.of_compCovering T ET (H s r hr _)
  exact IsGenericallyAlgebraic.of_restrictAway (mem_nonZeroDivisors_of_ne_zero hg)
    (IsGenericallyAlgebraic.of_algEquiv e hT)

/-- **XII.5.1 for normal domains**, from its generic form and the extension of coverings across
divisors of normal varieties. -/
theorem isEquivalence_pointsFunctor_of_generic_of_normalDivisorExtension
    (hG : GenericRiemannExistenceStatement) (hN : NormalDivisorExtensionStatement)
    (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : (pointsFunctor ℂ A).IsEquivalence where
  essSurj := ⟨fun E ↦ by
    obtain ⟨g, hg, hE⟩ := hG A E
    exact hN A g (nonZeroDivisors.ne_zero hg) E hE⟩

/-- **XII.5.1** (`RiemannExistenceStatement`, affine form, universe `0`) from its generic form
(`GenericRiemannExistenceStatement`) and the extension of coverings across divisors of normal
varieties (`NormalDivisorExtensionStatement`), by the reduction to normalizations
(`isEquivalence_pointsFunctor_of_forall_normalization`). -/
theorem riemannExistence_of_generic_of_normalDivisorExtension
    (hG : GenericRiemannExistenceStatement) (hN : NormalDivisorExtensionStatement) :
    RiemannExistenceStatement.{0} := fun A _ _ _ ↦
  isEquivalence_pointsFunctor_of_forall_normalization A fun _ ↦
    isEquivalence_pointsFunctor_of_generic_of_normalDivisorExtension hG hN _

/-- **XII.5.1, scheme form** (`SchemeRiemannExistenceStatement`), from the generic form and the
extension across divisors of normal varieties. -/
theorem schemeRiemannExistence_of_generic_of_normalDivisorExtension
    (hG : GenericRiemannExistenceStatement) (hN : NormalDivisorExtensionStatement) :
    SchemeRiemannExistenceStatement :=
  schemeRiemannExistence_iff.mpr (riemannExistence_of_generic_of_normalDivisorExtension hG hN)

/-- XII.5.1 for smooth domains, from the generic form and the extension across divisors of smooth
varieties (`DivisorExtensionStatement`). -/
theorem isEquivalence_pointsFunctor_of_generic_of_divisorExtension
    (hG : GenericRiemannExistenceStatement) (hD : DivisorExtensionStatement)
    (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    [Algebra.Smooth ℂ A] : (pointsFunctor ℂ A).IsEquivalence where
  essSurj := ⟨fun E ↦ by
    obtain ⟨g, hg, hE⟩ := hG A E
    exact hD A g hg E hE⟩

end SGA.SGA1.ExposeXII
