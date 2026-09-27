/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Modules.Tilde
import SGA.Foundations.QuasiCoherent.Pullback

/-!
# Cokernels of quasi-coherent modules

The cokernel of a morphism of quasi-coherent modules is quasi-coherent
(`Scheme.Modules.isQuasicoherent_cokernel`; EGA I, 2.2.2 (iii); [Stacks, Tag 01LA]). On an affine
scheme this holds because `M ↦ M^~` is a left adjoint, and in general because the inverse image
along an open immersion is a left adjoint too.

This is the canonical statement in `SGA.Foundations`; `CohomologyAux.isQuasicoherent_cokernel`
(`SGA.Foundations.Cohomology.QuasiCoherentAbelian`) proves the same statement and can be made an
alias of it.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine scheme, cokernels of morphisms of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_cokernel_Spec {R : CommRingCat.{u}} {E F : (Spec R).Modules}
    [E.IsQuasicoherent] [F.IsQuasicoherent] (φ : E ⟶ F) : (cokernel φ).IsQuasicoherent := by
  let ε := (tilde.adjunction (R := R)).counit
  have hE : IsIso (ε.app E) := isIso_fromTildeΓ_of_isQuasicoherent E
  have hF : IsIso (ε.app F) := isIso_fromTildeΓ_of_isQuasicoherent F
  let f := moduleSpecΓFunctor.map φ
  let e : cokernel ((tilde.functor R).map f) ≅ cokernel φ :=
    cokernel.mapIso _ _ (asIso (ε.app E)) (asIso (ε.app F)) (ε.naturality φ)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((PreservesCokernel.iso (tilde.functor R) f) ≪≫ e)
    (inferInstance : ((tilde.functor R).obj (cokernel f)).IsQuasicoherent)

set_option backward.isDefEq.respectTransparency.types false in
/-- Cokernels of morphisms of quasi-coherent modules are quasi-coherent. -/
@[stacks 01LA]
theorem isQuasicoherent_cokernel {X : Scheme.{u}} {E F : X.Modules} [E.IsQuasicoherent]
    [F.IsQuasicoherent] (φ : E ⟶ F) : (cokernel φ).IsQuasicoherent := by
  have hk : ∀ V : X.affineOpens,
      IsOpenImmersion ((fun V : X.affineOpens ↦ V.2.fromSpec) V) :=
    fun V ↦ V.2.isOpenImmersion_fromSpec
  refine isQuasicoherent_of_forall_pullback (fun V : X.affineOpens ↦ V.2.fromSpec) (fun x ↦ ?_)
    fun V ↦ ?_
  · obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rw [hV.range_fromSpec]; exact hxV⟩
  · have := isQuasicoherent_cokernel_Spec ((pullback V.2.fromSpec).map φ)
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, V.1)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso (pullback V.2.fromSpec) φ).symm this

end AlgebraicGeometry.Scheme.Modules
