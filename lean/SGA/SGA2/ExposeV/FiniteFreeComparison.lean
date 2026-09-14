/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteFreeEvaluation

/-!
# Additive comparison on finite free modules

A natural comparison of additive module-valued functors that is invertible
on the rank-one ring module is invertible on every finite free module. This
is the first finite-presentation step in the proof of V.2.1.
-/

noncomputable section
universe u
open CategoryTheory
open scoped BigOperators

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A finite decomposition of the identity transports an isomorphism of
additive functors from the coordinate object to the decomposed object. -/
theorem isIso_app_of_finite_identity
    {C : Type*} [Category C] [Preadditive C]
    {F G : C ⥤ ModuleCat.{u} R} [F.Additive] [G.Additive]
    (α : F ⟶ G) (A M : C) {ι : Type*} [Fintype ι]
    (p : ι → (M ⟶ A)) (s : ι → (A ⟶ M))
    (h : ∑ i, p i ≫ s i = 𝟙 M) [IsIso (α.app A)] : IsIso (α.app M) := by
  classical
  let β : G.obj M ⟶ F.obj M := ∑ i, G.map (p i) ≫ inv (α.app A) ≫ F.map (s i)
  refine ⟨⟨β, ?_, ?_⟩⟩
  · dsimp [β]
    rw [Preadditive.comp_sum]
    simp_rw [← Category.assoc, ← α.naturality, Category.assoc,
      IsIso.hom_inv_id_assoc, ← F.map_comp]
    rw [← F.map_sum, h, F.map_id]
  · dsimp [β]
    rw [Preadditive.sum_comp]
    simp_rw [Category.assoc, α.naturality, IsIso.inv_hom_id_assoc, ← G.map_comp]
    rw [← G.map_sum, h, G.map_id]

/-- Invertibility at the original ring implies invertibility at its actual
finite coordinate modules. -/
theorem isIso_app_finiteFree
    {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [F.Additive] [G.Additive]
    (α : F ⟶ G) [IsIso (α.app (ModuleCat.of R R))] (n : ℕ) :
    IsIso (α.app (ModuleCat.of R (Fin n → R))) := by
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  apply isIso_app_of_finite_identity α (ModuleCat.of R R) _
    (fun i => U.map (ExposeIV.finiteFreeProjection n i))
    (fun i => U.map (ExposeIV.finiteModulePoint
      (FGModuleCat.of R (Fin n → R)) (Pi.single i 1)))
  simpa only [Functor.map_sum, Functor.map_comp, U.map_id] using
    congrArg U.map (ExposeIV.finiteFree_identity (R := R) n)

end SGA.SGA2.ExposeV
