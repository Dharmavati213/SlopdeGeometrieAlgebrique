/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.Product
import SGA.Foundations.Topology.SemilocallySimplyConnected

/-!
# Fundamental groups of products

The fundamental group of a product is the product of the fundamental groups, and finite products
of semilocally simply connected spaces are semilocally simply connected. Mathlib has the
groupoid-level isomorphisms `FundamentalGroupoid.prodIso` and `FundamentalGroupoid.piIso`; here
are the group-level statements, with the product of loops `Path.Homotopic.prod` /
`Path.Homotopic.pi` as the map, so that monodromy computations can unfold it.

## Main results

* `FundamentalGroup.prodMulEquiv : π₁(X, x) × π₁(Y, y) ≃* π₁(X × Y, (x, y))`;
* `FundamentalGroup.piMulEquiv : (Π i, π₁(X i, x i)) ≃* π₁(Π i, X i, x)`;
* instances `SemilocallySimplyConnectedSpace (X × Y)` and, for finitely many factors,
  `SemilocallySimplyConnectedSpace (Π i, X i)`.

## References

* [A. Hatcher, *Algebraic Topology*, Proposition 1.12][hatcher02]
-/

open Topology Set Filter

namespace FundamentalGroup

section Prod

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The fundamental group of a product is the product of the fundamental groups:
`(γ, δ) ↦ γ × δ`. -/
def prodMulEquiv (x : X) (y : Y) :
    FundamentalGroup X x × FundamentalGroup Y y ≃* FundamentalGroup (X × Y) (x, y) where
  toFun g := Path.Homotopic.prod g.1 g.2
  invFun g := (Path.Homotopic.projLeft g, Path.Homotopic.projRight g)
  left_inv _ := Prod.ext (Path.Homotopic.projLeft_prod _ _) (Path.Homotopic.projRight_prod _ _)
  right_inv g := Path.Homotopic.prod_projLeft_projRight g
  map_mul' g h := (Path.Homotopic.comp_prod_eq_prod_comp h.1 h.2 g.1 g.2).symm

@[simp] lemma prodMulEquiv_apply (x : X) (y : Y) (g : FundamentalGroup X x × FundamentalGroup Y y) :
    prodMulEquiv x y g = Path.Homotopic.prod g.1 g.2 :=
  rfl

end Prod

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- The fundamental group of a product is the product of the fundamental groups:
`(γᵢ)ᵢ ↦ Π i, γᵢ`. -/
noncomputable def piMulEquiv (x : ∀ i, X i) :
    (∀ i, FundamentalGroup (X i) (x i)) ≃* FundamentalGroup (∀ i, X i) x where
  toFun g := Path.Homotopic.pi g
  invFun g i := Path.Homotopic.proj i g
  left_inv g := funext fun i ↦ Path.Homotopic.proj_pi i g
  right_inv g := Path.Homotopic.pi_proj g
  map_mul' g h := (Path.Homotopic.comp_pi_eq_pi_comp h g).symm

@[simp] lemma piMulEquiv_apply (x : ∀ i, X i) (g : ∀ i, FundamentalGroup (X i) (x i)) :
    piMulEquiv x g = Path.Homotopic.pi g :=
  rfl

end Pi

end FundamentalGroup

section SemilocallySimplyConnected

/-- A product of two semilocally simply connected spaces is semilocally simply connected. -/
instance Prod.semilocallySimplyConnectedSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SemilocallySimplyConnectedSpace X] [SemilocallySimplyConnectedSpace Y] :
    SemilocallySimplyConnectedSpace (X × Y) where
  exists_nhds_homotopic_refl z := by
    obtain ⟨U, hU, hUγ⟩ := SemilocallySimplyConnectedSpace.exists_nhds_homotopic_refl z.1
    obtain ⟨V, hV, hVγ⟩ := SemilocallySimplyConnectedSpace.exists_nhds_homotopic_refl z.2
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, fun γ hγ ↦ ?_⟩
    have h₁ := hUγ (γ.map continuous_fst) (by
      rintro _ ⟨t, rfl⟩
      exact (hγ ⟨t, rfl⟩).1)
    have h₂ := hVγ (γ.map continuous_snd) (by
      rintro _ ⟨t, rfl⟩
      exact (hγ ⟨t, rfl⟩).2)
    rw [← Path.Homotopic.Quotient.eq] at h₁ h₂ ⊢
    rw [← Path.Homotopic.prod_projLeft_projRight (Path.Homotopic.Quotient.mk γ)]
    change Path.Homotopic.prod (Path.Homotopic.Quotient.mk (γ.map continuous_fst))
      (Path.Homotopic.Quotient.mk (γ.map continuous_snd)) = _
    rw [h₁, h₂, Path.Homotopic.prod_lift]
    rfl

/-- A product of finitely many semilocally simply connected spaces is semilocally simply
connected. -/
instance Pi.semilocallySimplyConnectedSpace {ι : Type*} [Finite ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, SemilocallySimplyConnectedSpace (X i)] :
    SemilocallySimplyConnectedSpace (∀ i, X i) where
  exists_nhds_homotopic_refl z := by
    choose U hU hUγ using fun i ↦ SemilocallySimplyConnectedSpace.exists_nhds_homotopic_refl (z i)
    refine ⟨univ.pi U, set_pi_mem_nhds finite_univ fun i _ ↦ hU i, fun γ hγ ↦ ?_⟩
    have h (i : ι) := hUγ i (γ.map (continuous_apply i)) (by
      rintro _ ⟨t, rfl⟩
      exact hγ ⟨t, rfl⟩ i trivial)
    simp only [← Path.Homotopic.Quotient.eq] at h ⊢
    rw [← Path.Homotopic.pi_proj (Path.Homotopic.Quotient.mk γ)]
    change Path.Homotopic.pi (fun i ↦ Path.Homotopic.Quotient.mk (γ.map (continuous_apply i))) = _
    simp only [h, Path.Homotopic.pi_lift]
    rfl

end SemilocallySimplyConnected
