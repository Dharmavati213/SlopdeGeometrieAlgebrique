/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlaneExistence
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.Foundations.Topology.SurfaceGenusZero

/-!
# SGA 1, Exposé XII, 5.2 for `ℂ ∖ S`, conditionally on the analytic input

With the Riemann existence theorem for `X = Spec ℂ[t][1/∏_{a ∈ S} (t - a)]`
(`PuncturedPlane.isEquivalence_pointsFunctor_coordRing`, conditional on
`FiberSeparatingFunctionStatement`), XII.5.2 identifies the étale fundamental group of `X` with
the profinite completion of `π₁(ℂ ∖ S)`, which is free on loops around the points of `S`
(`Complex.exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding`). So the étale fundamental
group of `ℙ¹_ℂ` minus `|S| + 1` points is the free profinite group on `|S|` generators
(`PuncturedPlane.nonempty_etaleFundamentalGroup_continuousMulEquiv_completion_freeGroup`): the
genus-`0` case of XIII.2.12 over `ℂ`, conditionally on `FiberSeparatingFunctionStatement`.
That hypothesis is proved; the unconditional form is
`PuncturedPlane.etaleFundamentalGroup_mulEquiv_completion_freeGroup`
(`SGA.SGA1.ExposeXII.GAGAFiberSeparating`).
-/

noncomputable section

open CategoryTheory Topology Set AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace PuncturedPlane

attribute [local instance] SchemePoints.specOver locallyOfFiniteType_specOver

/-- An isomorphism of profinite groups, as a continuous multiplicative equivalence. -/
def continuousMulEquivOfIso {X Y : ProfiniteGrp} (i : X ≅ Y) : X ≃ₜ* Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := congr($(i.hom_inv_id) x)
  right_inv y := congr($(i.inv_hom_id) y)
  map_mul' := map_mul i.hom.hom
  continuous_toFun := i.hom.hom.continuous
  continuous_invFun := i.inv.hom.continuous

/-- **XII.5.2 (and XIII.2.12 in genus `0`) for `ℂ ∖ S`, conditionally on the analytic input**: if
every fibre of a connected finite covering of `ℂ ∖ S` is separated by a holomorphic function of
moderate growth (`FiberSeparatingFunctionStatement`), then the étale fundamental group of
`X = Spec ℂ[t][1/∏_{a ∈ S} (t - a)]` (`ℙ¹_ℂ` minus `|S| + 1` points) at any `ℂ`-point is the
profinite completion of the free group on `S`. -/
theorem nonempty_etaleFundamentalGroup_continuousMulEquiv_completion_freeGroup
    (H : FiberSeparatingFunctionStatement) (S : Finset ℂ)
    (x : SchemePoints ℂ (Spec (.of (coordRing S)))) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ*
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup S))) := by
  have : (schemePointsFunctor ℂ (Spec (.of (coordRing S)))).IsEquivalence :=
    (isEquivalence_pointsFunctor_iff (coordRing S)).mp (isEquivalence_pointsFunctor_coordRing H S)
  have hne : Nonempty {z : ℂ // z ∉ S} := ⟨schemeHomeomorph S x⟩
  have hpre : PreconnectedSpace {z : ℂ // z ∉ S} := preconnectedSpace_compl
  have : ConnectedSpace {z : ℂ // z ∉ S} := { toPreconnectedSpace := hpre, toNonempty := hne }
  have : ConnectedSpace (SchemePoints ℂ (Spec (.of (coordRing S)))) :=
    (schemeHomeomorph S).symm.surjective.connectedSpace (schemeHomeomorph S).symm.continuous
  have : StronglyLocallyContractibleSpace {z : ℂ // z ∉ S} :=
    S.finite_toSet.isClosed.isOpen_compl.stronglyLocallyContractibleSpace
  have : StronglyLocallyContractibleSpace (SchemePoints ℂ (Spec (.of (coordRing S)))) :=
    (schemeHomeomorph S).isLocalHomeomorph.stronglyLocallyContractibleSpace
  obtain ⟨e⟩ := nonempty_etaleFundamentalGroup_continuousMulEquiv ℂ x
  have hj : IsOpenEmbedding fun y ↦ (schemeHomeomorph S y : ℂ) :=
    S.finite_toSet.isClosed.isOpen_compl.isOpenEmbedding_subtypeVal.comp
      (schemeHomeomorph S).isOpenEmbedding
  have hjr : range (fun y ↦ (schemeHomeomorph S y : ℂ)) = univ \ (S : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨trivial, (schemeHomeomorph S y).2⟩
    · rintro ⟨-, hz⟩
      exact ⟨(schemeHomeomorph S).symm ⟨z, hz⟩, by simp⟩
  obtain ⟨b, -⟩ := Complex.exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding
    convex_univ isOpen_univ (subset_univ _) hj hjr x
  exact ⟨e.trans (continuousMulEquivOfIso
    (ProfiniteGrp.profiniteCompletion.mapIso (MulEquiv.toGrpIso b.repr)))⟩

end PuncturedPlane

end SGA.SGA1.ExposeXII
