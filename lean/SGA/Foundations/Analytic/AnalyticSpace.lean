/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.UniversalProperty
import SGA.Foundations.Analytic.Flatness

/-!
# Analytic spaces

A `𝕜`-analytic space is a locally ringed space which is locally isomorphic to a local model
`Z(D) ⊆ 𝕜ⁿ` (`IsAnalyticSpace`); local models, in particular the analytifications `Spec(A)^an`
of finitely presented `𝕜`-algebras, are analytic spaces.

We also record the first consequences of the faithful flatness of `𝒪_{X,φ(x)} → 𝒪_{X^an,x}`
(`faithfullyFlat_stalkMap_toSpec`) for the comparison of local rings (SGA 1 XII.2.1): the map is
injective, and reducedness and integrality descend from `𝒪_{X^an,x}` to `𝒪_{X,φ(x)}`.
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace AnalyticGeometry

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- A locally ringed space is a `𝕜`-analytic space if every point has an open neighbourhood which
is isomorphic, as a locally ringed space, to a local model `Z(D) ⊆ 𝕜ⁿ`. -/
def IsAnalyticSpace (X : LocallyRingedSpace.{0}) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (n : ℕ) (D : LocalModelData 𝕜 (Fin n → 𝕜)),
    Nonempty (X.restrict U.isOpenEmbedding ≅ D.toLocallyRingedSpace)

variable {𝕜}

/-- Local models are analytic spaces. -/
theorem LocalModelData.isAnalyticSpace {n : ℕ} (D : LocalModelData 𝕜 (Fin n → 𝕜)) :
    IsAnalyticSpace 𝕜 D.toLocallyRingedSpace :=
  fun _ ↦ ⟨⊤, trivial, n, D, ⟨D.toLocallyRingedSpace.restrictTopIso⟩⟩

variable {n k : ℕ} (g : Fin k → MvPolynomial (Fin n) 𝕜)

/-- **XII.1.1**: the analytification of `Spec 𝕜[z]/(g)` is an analytic space. -/
theorem isAnalyticSpace_analytification : IsAnalyticSpace 𝕜 (analytification g) :=
  (polynomialModel g).isAnalyticSpace

variable (x : (polynomialModel g).zeroSet)

/-- **XII.2.1**: the map `𝒪_{X,φ(x)} → 𝒪_{X^an,x}` is injective (it is faithfully flat). -/
theorem injective_stalkMap_toSpec : Function.Injective ((toSpec g).stalkMap x).hom :=
  (faithfullyFlat_stalkMap_toSpec g x).injective

/-- **XII.2.1**: if `𝒪_{X^an,x}` is reduced, so is `𝒪_{X,φ(x)}`. -/
theorem isReduced_stalk_of_isReduced_stalk_analytification
    [IsReduced ((analytification g).presheaf.stalk x)] :
    IsReduced ((Spec.locallyRingedSpaceObj (CommRingCat.of (PresentedAlgebra g))).presheaf.stalk
      ((toSpec g).base x)) :=
  isReduced_of_injective _ (injective_stalkMap_toSpec g x)

/-- **XII.2.1**: if `𝒪_{X^an,x}` is a domain, so is `𝒪_{X,φ(x)}`. -/
theorem isDomain_stalk_of_isDomain_stalk_analytification
    [IsDomain ((analytification g).presheaf.stalk x)] :
    IsDomain ((Spec.locallyRingedSpaceObj (CommRingCat.of (PresentedAlgebra g))).presheaf.stalk
      ((toSpec g).base x)) :=
  Function.Injective.isDomain _ (injective_stalkMap_toSpec g x)

end AnalyticGeometry
