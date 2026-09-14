/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.AffineExactness
import SGA.SGA2.ExposeII.InjectiveFlasque
import SGA.SGA2.ExposeI.FlasqueCohomology
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Higher cohomology of associated sheaves on a noetherian affine scheme

The associated-sheaf functor carries module short exact sequences to genuine
short exact sequences of abelian sheaves. Its global sections recover the
original module. Applying this to injective embeddings, whose associated
sheaves are flasque, proves higher cohomology vanishing by dimension shifting.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Abelian

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- Actual global sections of the associated abelian sheaf recover the
coefficient module as an abelian group. -/
def affineTildeAb_globalSectionsEquiv (M : ModuleCat.{u} R) :
    M ≃+ (affineTildeAbSheaf M).presheaf.obj (op ⊤) :=
  (tilde.isoTop M).toLinearEquiv.toAddEquiv

/-- Surjections of modules give surjections on actual degree-zero sheaf
cohomology of their associated sheaves, over any commutative ring. -/
theorem affineTildeAb_H_zero_map_surjective {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (CategoryTheory.Sheaf.H.map.{u} (affineTildeAbFunctor.map f) 0) := by
  intro x
  let t := CategoryTheory.Sheaf.H.equiv₀.{u} (affineTildeAbFunctor.obj N) isTerminalTop x
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance
    ((tilde.isoTop N).inv t)
  refine ⟨(CategoryTheory.Sheaf.H.equiv₀.{u} (affineTildeAbFunctor.obj M) isTerminalTop).symm
    ((tilde.isoTop M).hom m), ?_⟩
  apply (CategoryTheory.Sheaf.H.equiv₀.{u} (affineTildeAbFunctor.obj N) isTerminalTop).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  simp only [AddEquiv.apply_symm_apply]
  change (affineTildeAbFunctor.map f).hom.app (op ⊤) ((tilde.isoTop M).hom m) = t
  have h := ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) m
  change (affineTildeAbFunctor.map f).hom.app (op ⊤) ((tilde.isoTop M).hom m) =
    (tilde.isoTop N).hom (f m) at h
  rw [h, hm]
  exact (tilde.isoTop N).inv_hom_id_apply t

/-- Every associated sheaf on a noetherian affine scheme has vanishing
ordinary sheaf cohomology in every positive degree. -/
theorem affineTildeAb_H_pos_subsingleton [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (ExposeI.H (affineTildeAbSheaf M) (n + 1)) := by
  induction n generalizing M with
  | zero =>
    let C := ShortComplex.cokernelSequence (Injective.ι M)
    have hC : C.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι M); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι M)); infer_instance }
    let S := C.map affineTildeAbFunctor
    have hS : S.ShortExact := affineTildeAb_shortExact hC
    have : Injective C.X₂ := inferInstanceAs (Injective (Injective.under M))
    have : TopCat.Sheaf.IsFlasque S.X₂ := affineTildeAbSheaf_isFlasque_of_injective C.X₂
    have : Subsingleton (ExposeI.H S.X₂ 1) := ExposeI.H_pos_subsingleton_of_isFlasque S.X₂ 0
    have : Epi C.g := hC.epi_g
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
      (Subsingleton.elim _ _) (n₀ := 0) rfl
    obtain ⟨z, rfl⟩ := affineTildeAb_H_zero_map_surjective C.g y
    rw [← hy]
    simp only [CategoryTheory.Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero]
    change z.comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) = 0
    rw [hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    let C := ShortComplex.cokernelSequence (Injective.ι M)
    have hC : C.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι M); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι M)); infer_instance }
    let S := C.map affineTildeAbFunctor
    have hS : S.ShortExact := affineTildeAb_shortExact hC
    have : Injective C.X₂ := inferInstanceAs (Injective (Injective.under M))
    have : TopCat.Sheaf.IsFlasque S.X₂ := affineTildeAbSheaf_isFlasque_of_injective C.X₂
    have : Subsingleton (ExposeI.H S.X₂ (n + 1 + 1)) :=
      ExposeI.H_pos_subsingleton_of_isFlasque S.X₂ (n + 1)
    have : Subsingleton (ExposeI.H S.X₃ (n + 1)) := ih C.X₃
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
      (Subsingleton.elim _ _) (n₀ := n + 1) rfl
    have hyzero : y = 0 := Subsingleton.elim _ _
    rw [← hy, hyzero, Ext.zero_comp]

end SGA.SGA2.ExposeII
