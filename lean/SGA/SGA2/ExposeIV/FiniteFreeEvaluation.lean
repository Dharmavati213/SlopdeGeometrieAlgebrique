/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteModuleEvaluation

/-!
# Evaluation on finite free modules

The canonical map of IV.1.1 is invertible on finite free modules. The
module-valued statement uses linearity; for an additive abelian-group-valued
functor, that linearity is supplied by the canonical module lift. The inverse
is the finite sum of the images of coordinate projections.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped BigOperators

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (T : (FGModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R) [T.Additive] [T.Linear R]

private theorem moduleHom_sum_apply {M N : ModuleCat.{u} R} {ι : Type*}
    (s : Finset ι) (f : ι → (M ⟶ N)) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  change (∑ i ∈ s, f i).hom x = _
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]

private theorem finiteModuleHom_sum_apply {M N : FGModuleCat.{u} R} {ι : Type*}
    (s : Finset ι) (f : ι → (M ⟶ N)) (x : M) :
    (∑ i ∈ s, f i).hom x = ∑ i ∈ s, (f i).hom x := by
  change ((forget₂ (FGModuleCat R) (ModuleCat R)).map (∑ i ∈ s, f i)) x = _
  rw [Functor.map_sum]
  exact moduleHom_sum_apply s _ x

theorem finiteModuleEvaluation_ring_apply (t : T.obj (op (FGModuleCat.of R R))) (r : R) :
    finiteModuleEvaluation T (FGModuleCat.of R R) t r = r • t := by
  conv_lhs => rw [← mul_one r]
  change (finiteModuleEvaluation T (FGModuleCat.of R R) t).hom (r • (1 : R)) = _
  rw [LinearMap.map_smul, finiteModuleEvaluation_ring_one]

/-- The actual coordinate projection of a finite free module. -/
def finiteFreeProjection (n : ℕ) (i : Fin n) :
    FGModuleCat.of R (Fin n → R) ⟶ FGModuleCat.of R R :=
  FGModuleCat.ofHom (LinearMap.proj i)

/-- Finite coordinate inclusions and projections decompose the identity. -/
theorem finiteFree_identity (n : ℕ) :
    ∑ i : Fin n, finiteFreeProjection (R := R) n i ≫
      finiteModulePoint (FGModuleCat.of R (Fin n → R)) (Pi.single i 1) = 𝟙 _ := by
  classical
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [finiteModuleHom_sum_apply]
  change (∑ i : Fin n, x i • Pi.single i (1 : R)) = x
  ext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- Additivity reconstructs any functor value from its finite coordinates. -/
theorem finiteFree_reconstruct (n : ℕ) (t : T.obj (op (FGModuleCat.of R (Fin n → R)))) :
    ∑ i : Fin n, T.map (finiteFreeProjection (R := R) n i).op
      (finiteModuleEvaluation T (FGModuleCat.of R (Fin n → R)) t (Pi.single i 1)) = t := by
  classical
  change ∑ i : Fin n, T.map (finiteFreeProjection (R := R) n i).op
    (T.map (finiteModulePoint (FGModuleCat.of R (Fin n → R)) (Pi.single i 1)).op t) = t
  have h := ConcreteCategory.congr_hom
    (congrArg T.map (congrArg Quiver.Hom.op (finiteFree_identity (R := R) n))) t
  simpa only [op_sum, op_comp, T.map_sum, T.map_comp, op_id, T.map_id,
    moduleHom_sum_apply, ModuleCat.comp_apply, ModuleCat.id_apply,
    ] using h

/-- The canonical evaluation map is injective on finite free modules. -/
theorem finiteModuleEvaluation_free_injective (n : ℕ) :
    Function.Injective (finiteModuleEvaluation T (FGModuleCat.of R (Fin n → R))) := by
  intro t s h
  rw [← finiteFree_reconstruct T n t, ← finiteFree_reconstruct T n s]
  congr 1
  funext i
  rw [h]

/-- The canonical evaluation map is surjective on finite free modules. -/
theorem finiteModuleEvaluation_free_surjective (n : ℕ) :
    Function.Surjective (finiteModuleEvaluation T (FGModuleCat.of R (Fin n → R))) := by
  classical
  intro h
  refine ⟨∑ i : Fin n, T.map (finiteFreeProjection (R := R) n i).op (h (Pi.single i 1)), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change finiteModuleEvaluation T (FGModuleCat.of R (Fin n → R))
    (∑ i : Fin n, T.map (finiteFreeProjection (R := R) n i).op (h (Pi.single i 1))) x = h x
  rw [map_sum]
  rw [moduleHom_sum_apply]
  trans ∑ i : Fin n, x i • h (Pi.single i 1)
  · apply Finset.sum_congr rfl
    intro i hi
    exact (finiteModuleEvaluation_naturality T (finiteFreeProjection n i)
      (h (Pi.single i 1)) x).trans
        (finiteModuleEvaluation_ring_apply T (h (Pi.single i 1)) (x i))
  simp_rw [← h.hom.map_smul]
  rw [← map_sum h.hom]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

theorem finiteModuleEvaluation_free_bijective (n : ℕ) :
    Function.Bijective (finiteModuleEvaluation T (FGModuleCat.of R (Fin n → R))) :=
  ⟨finiteModuleEvaluation_free_injective T n, finiteModuleEvaluation_free_surjective T n⟩

end SGA.SGA2.ExposeIV
