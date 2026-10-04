/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeXIII.AbhyankarAffineLineNode

/-!
# XIII.2.13, case A: the branches of the nodal model

In Harbater–Stevenson's patching on the nodal model (see
`SGA.SGA1.ExposeXIII.AbhyankarAffineLineNode`), the local Galois data on the sheets and at the node
are compared over the branch rings `R̂_℘ = k((y))⟦t⟧`. A finite étale algebra over `K⟦t⟧` is
determined by its reduction modulo `t` (I.6.1,
`SGA.SGA1.ExposeI.isEquivalence_finiteEtale_baseChange_of_surjective`), so the reduction
`K⟦t⟧ → K` induces an isomorphism of fundamental groups
(`AffineLinePGroups.bijective_fundamentalGroupMapOfRingHom_constantCoeff`). Hence two principal
coverings of `Spec K⟦t⟧` under a finite group `G` are isomorphic as soon as their homomorphisms
`π₁ → G`, restricted along `π₁(Spec K) → π₁(Spec K⟦t⟧)`, are conjugate
(`AffineLinePGroups.isIso_of_hom_comp_eq_conj`, with the general
`ExposeXI.PrincipalObject.isIso_of_hom_eq_conj`).

For the node, the branch maps `R' → k((y))⟦t⟧` of the punctured node
(`PatchingProjectiveLine.nodePuncturedMapOne`, `nodePuncturedMapTwo`, with reductions modulo `t`
`PatchingProjectiveLine.constantCoeff_comp_nodePuncturedMapOne`, `…Two`) are in
`SGA.Foundations.Patching.ProjectiveLineNodeTwist`.
-/

universe u

open CategoryTheory PreGaloisCategory CommAlgCat

namespace SGA.SGA1.ExposeXI.PrincipalObject

variable {C : Type*} [Category C] [GaloisCategory C] {F : C ⥤ FintypeCat.{u}} [FiberFunctor F]
  {G : Type u} [Group G]

/-- XI.5: two principal objects whose homomorphisms `π → G` are conjugate are isomorphic. -/
theorem isIso_of_hom_eq_conj (P Q : PrincipalObject F G) (x : F.obj P.X) (y : F.obj Q.X) (c : G)
    (h : ∀ σ, P.hom x σ = c * Q.hom y σ * c⁻¹) : P.IsIso Q := by
  refine P.exists_iso_of_torsorHom_eq Q x (Q.act c⁻¹ y) (MonoidHom.ext fun σ ↦ ?_)
  rw [torsorHom_act, h σ, inv_inv]

end SGA.SGA1.ExposeXI.PrincipalObject

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [Algebra (PowerSeries K) Ω]
  (h : algebraMap (PowerSeries K) Ω = (algebraMap K Ω).comp PowerSeries.constantCoeff)

-- The reduction `π₁(Spec K, a) → π₁(Spec K⟦t⟧, a)` along `K⟦t⟧ → K`.
local notation "πred" => fundamentalGroupMapOfRingHom
  (PowerSeries.constantCoeff : PowerSeries K →+* K) Ω h

lemma ker_constantCoeff_eq_span_X :
    RingHom.ker (PowerSeries.constantCoeff : PowerSeries K →+* K) =
      Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- I.6.1 for `K⟦t⟧`: the reduction `K⟦t⟧ → K` induces an isomorphism
`π₁(Spec K, a) → π₁(Spec K⟦t⟧, a)`. -/
theorem bijective_fundamentalGroupMapOfRingHom_constantCoeff :
    Function.Bijective (πred) := by
  let := (PowerSeries.constantCoeff : PowerSeries K →+* K).toAlgebra
  have : IsScalarTower (PowerSeries K) K Ω := IsScalarTower.of_algebraMap_eq' h
  have hsurj : Function.Surjective (algebraMap (PowerSeries K) K) := fun c ↦
    ⟨PowerSeries.C c, PowerSeries.constantCoeff_C c⟩
  have : IsAdicComplete (RingHom.ker (algebraMap (PowerSeries K) K)) (PowerSeries K) := by
    change IsAdicComplete (RingHom.ker (PowerSeries.constantCoeff : PowerSeries K →+* K)) _
    rw [ker_constantCoeff_eq_span_X]
    infer_instance
  have := ExposeI.isEquivalence_finiteEtale_baseChange_of_surjective hsurj
  exact ExposeV.autMap_bijective _ _

variable [IsSepClosed Ω]

/-- I.6.1, XI.5: principal coverings of `Spec K⟦t⟧` with conjugate restrictions to `Spec K` are
isomorphic. -/
theorem isIso_of_hom_comp_eq_conj {G : Type u} [Group G]
    (P Q : ExposeXI.PrincipalObject (ExposeV.fiberFunctor (PowerSeries K) Ω) G)
    (x : (ExposeV.fiberFunctor (PowerSeries K) Ω).obj P.X)
    (y : (ExposeV.fiberFunctor (PowerSeries K) Ω).obj Q.X) (c : G)
    (hc : ∀ σ, P.hom x (πred σ) =
      c * Q.hom y (πred σ) * c⁻¹) :
    P.IsIso Q := by
  refine P.isIso_of_hom_eq_conj Q x y c fun τ ↦ ?_
  obtain ⟨σ, rfl⟩ := (bijective_fundamentalGroupMapOfRingHom_constantCoeff K Ω h).2 τ
  exact hc σ

end SGA.SGA1.ExposeXIII.AffineLinePGroups
