/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.GAGA
import SGA.Foundations.Projective.Morphisms
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import SGA.Foundations.Cohomology.ProjectiveSpaceTwist
import SGA.Foundations.Cohomology.TwistProjection
import SGA.Foundations.Cohomology.HProjective

/-!
# SGA 1, Exposé XII, 4.3 for projective schemes (Serre's GAGA): statements

SGA 1 XII.4.3 says that for a proper `ℂ`-scheme `X` and a coherent `𝒪_X`-module `F` the canonical
maps `Hᵖ(X, F) → Hᵖ(X^an, F^an)` are bijective (`CohomologyComparisonStatement`, in
`SGA.SGA1.ExposeXII.GAGA`). SGA proves it through the projective case, which is Serre's GAGA
(GAGA, no. 12, théorème 1), itself reduced to the twisting sheaves `𝒪(d)` on `ℙⁿ`. This file
records the two intermediate statements, so that they can be consumed (Hodge theory for SGA 1
XI.1.4 needs the projective case) and proved separately:

* `ProjectiveCohomologyComparisonStatement`: XII.4.3 for `X` H-projective over `ℂ` (a closed
  subscheme of some `ℙ(σ; Spec ℂ)`, `IsHProjective`);
* `ProjectiveSpaceTwistComparisonStatement`: XII.4.3 for `X = ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]` and
  `F = 𝒪(d)` (the sheaves `projectiveSpace.twist` whose algebraic cohomology is computed in
  `SGA.Foundations.Cohomology.ProjectiveSpaceTwist`).

`projectiveCohomologyComparison_of_cohomologyComparison` and
`projectiveSpaceTwistComparison_of_projectiveCohomologyComparison` are the trivial implications
(general ⇒ projective ⇒ `𝒪(d)` on `ℙⁿ`). The converse implications are the content of SGA's
proof: Serre's resolutions `𝒪(-m)ᵏ ↠ F` and descending induction on `p` for the second, Chow's
lemma and dévissage (EGA III 3.1.2) for the first.

`ℙⁿ_ℂ` is given the `ℂ`-structure `ProjectiveSpace.projToSpec`, i.e.
`Proj ℂ[x] → Spec ℂ[x]₀ = Spec ℂ` (instance `projectiveSpaceOverC`); it is H-projective over `ℂ`
through `ProjectiveSpace.isoProj : Proj ℂ[x] ≅ ℙ(σ; Spec ℂ)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AnalyticGeometry

namespace SGA.SGA1.ExposeXII

open AnalyticGluing LocallyRingedSpace.Modules

section ProjectiveSpace

variable (σ : Type)

/-- The `ℂ`-structure of `ℙ(σ)_ℂ = Proj ℂ[xᵢ : i ∈ σ]`: the structure morphism
`Proj ℂ[x] → Spec ℂ[x]₀ = Spec ℂ` (`ProjectiveSpace.projToSpec`). -/
instance projectiveSpaceOverC : (Proj (ProjectiveSpace.grading σ ℂ)).Over (Spec (.of ℂ)) :=
  ⟨ProjectiveSpace.projToSpec σ ℂ⟩

lemma projectiveSpace_over_eq :
    Proj (ProjectiveSpace.grading σ ℂ) ↘ Spec (.of ℂ) = ProjectiveSpace.projToSpec σ ℂ :=
  rfl

/-- `Proj ℂ[xᵢ : i ∈ σ]` is H-projective over `ℂ` for finite `σ`: its structure morphism is
`ProjectiveSpace.isoProj` followed by `ℙ(σ; Spec ℂ) → Spec ℂ`. -/
instance isHProjective_projectiveSpace [Finite σ] :
    IsHProjective (Proj (ProjectiveSpace.grading σ ℂ) ↘ Spec (.of ℂ)) := by
  rw [projectiveSpace_over_eq, ← ProjectiveSpace.isoProj_hom_over]
  infer_instance

end ProjectiveSpace

/-- XII.4.3 for projective `X` (statement only; Serre, GAGA no. 12, théorème 1): for a `ℂ`-scheme
`X` H-projective over `ℂ` (a closed subscheme of some `ℙ(σ; Spec ℂ)`, `IsHProjective`) and a
coherent `𝒪_X`-module `F`, the canonical map `Hᵖ(X, F) → Hᵖ(X^an, F^an)`
(`pullbackCohomologyMap (toScheme X) F p`, see `CohomologyComparisonStatement`) is bijective for
every `p`. H-projective morphisms are proper (`IsHProjective.isProper`, an instance), so this is
`CohomologyComparisonStatement` restricted to projective `X`. Stated in universe `0`. -/
def ProjectiveCohomologyComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsHProjective (X ↘ Spec (.of ℂ))] (F : X.Modules)
    [F.IsCoherent] (p : ℕ),
    Function.Bijective (pullbackCohomologyMap (X := analyticSpace X)
      (Y := X.toLocallyRingedSpace) (toScheme X) F p)

/-- XII.4.3 for the twisting sheaves on projective space (statement only; Serre, GAGA no. 12,
proof of théorème 1, and SGA 1 XII.4.2, step 1): for `ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]` and every
`d ∈ ℤ`, the canonical map `Hᵖ(ℙⁿ, 𝒪(d)) → Hᵖ((ℙⁿ)^an, 𝒪(d)^an)` is bijective for every `p`.
Here `𝒪(d)` is `projectiveSpace.twist (Fin (n + 1)) ℂ d` (whose algebraic cohomology is computed
in `SGA.Foundations.Cohomology.ProjectiveSpaceTwist`) and `ℙⁿ_ℂ` has the `ℂ`-structure
`projectiveSpaceOverC`. -/
def ProjectiveSpaceTwistComparisonStatement : Prop :=
  ∀ (n : ℕ) (d : ℤ) (p : ℕ),
    Function.Bijective (pullbackCohomologyMap
      (X := analyticSpace (Proj (ProjectiveSpace.grading (Fin (n + 1)) ℂ)))
      (Y := (Proj (ProjectiveSpace.grading (Fin (n + 1)) ℂ)).toLocallyRingedSpace)
      (toScheme _) (projectiveSpace.twist (Fin (n + 1)) ℂ d) p)

/-- XII.4.3 implies its projective case. -/
theorem projectiveCohomologyComparison_of_cohomologyComparison
    (h : CohomologyComparisonStatement) : ProjectiveCohomologyComparisonStatement :=
  fun X _ _ F _ p ↦ h X F p

/-- The projective case of XII.4.3 implies the case of the twisting sheaves `𝒪(d)` on `ℙⁿ`. -/
theorem projectiveSpaceTwistComparison_of_projectiveCohomologyComparison
    (h : ProjectiveCohomologyComparisonStatement) : ProjectiveSpaceTwistComparisonStatement := by
  intro n d p
  exact @h _ _ _ _ (Scheme.LineBundle.isCoherent_twist _ (CohomologyAux.unitModule _) d) p

end SGA.SGA1.ExposeXII
