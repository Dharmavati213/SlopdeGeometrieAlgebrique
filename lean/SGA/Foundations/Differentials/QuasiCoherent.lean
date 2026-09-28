/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.AffineOpens
import SGA.Foundations.QuasiCoherent.Pullback

/-!
# Quasi-coherence of `Ω_{X/Y}`

The sheaf of relative differentials of a morphism of schemes is quasi-coherent
(Stacks Project, Tag 01UT; EGA IV 16.5.5): on an affine open `U ⊆ f⁻¹ V` with `V` affine it is
`Ω_{Γ(X, U)/Γ(Y, V)}^~` (`Scheme.Hom.relativeDifferentialsFromSpecIso`).
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every point of `X` lies in an affine open `U` mapped by `f` into an affine open `V`. -/
lemma Scheme.Hom.exists_affineOpens_le_preimage (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
  exact ⟨U, V, hU, hV, hxU, hUV⟩

open Scheme.Modules in
/-- The sheaf of relative differentials is quasi-coherent (Stacks Project, Tag 01UT). -/
instance Scheme.Hom.isQuasicoherent_relativeDifferentials :
    f.relativeDifferentials.IsQuasicoherent := by
  choose U V hU hV hx he using f.exists_affineOpens_le_preimage
  refine isQuasicoherent_of_forall_pullback (fun x ↦ (hU x).fromSpec)
    (fun x ↦ ⟨x, by rw [(hU x).range_fromSpec]; exact hx x⟩) fun x ↦ ?_
  exact isQuasicoherent_of_iso ((f.relativeDifferentialsFromSpecIso (hU x) (hV x) (he x)).symm ≪≫
    (restrictFunctorIsoPullback _).app _)

end AlgebraicGeometry
