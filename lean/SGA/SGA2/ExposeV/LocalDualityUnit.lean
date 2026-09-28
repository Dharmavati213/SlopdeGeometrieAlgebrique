/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityMap

/-!
# Identity normalization of the canonical local-duality map

The actual identity class in degree-zero Ext is a unit for the original
module-valued pairing. Evaluation at this class retracts the canonical
top-degree local-duality map with equal middle and final coefficients.
This proves its injectivity over every commutative ring, without claiming
the full finite-module isomorphism theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The genuine identity class, in the original module-valued degree-zero Ext. -/
def moduleExtIdentity (M : ModuleCat.{u} R) : moduleExtValue M M 0 :=
  (moduleExtLinearEquivAbelianExt M M 0).symm (Abelian.Ext.mk₀ (𝟙 M))

@[simp]
theorem moduleExtPairing_identity_right (N M : ModuleCat.{u} R) (i : ℕ)
    (x : moduleExtValue N M i) :
    moduleExtPairing N M M i 0 i (add_zero i) x (moduleExtIdentity M) = x := by
  simp [moduleExtPairing_apply, moduleExtIdentity]

@[simp]
theorem moduleExtPairing_identity_left (M P : ModuleCat.{u} R) (j : ℕ)
    (y : moduleExtValue M P j) :
    moduleExtPairing M M P 0 j j (zero_add j) (moduleExtIdentity M) y = y := by
  simp [moduleExtPairing_apply, moduleExtIdentity]

/-- Evaluation at the original identity Ext class. -/
def localDualityIdentityEvaluation (J : Ideal R) (P : ModuleCat.{u} R) (n : ℕ) :
    localDualityTargetValue J P P 0 n ⟶ (_root_.localCohomology J n).obj P :=
  ModuleCat.ofHom
    { toFun := fun φ => φ (moduleExtIdentity P)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The canonical local-duality map is normalized by the genuine identity
class: evaluating its output at that class recovers the original input. -/
@[reassoc (attr := simp)]
theorem localDualityMap_identity_evaluation (J : Ideal R) (P : ModuleCat.{u} R) (n : ℕ) :
    localDualityMap J P P n 0 n (add_zero n) ≫ localDualityIdentityEvaluation J P n = 𝟙 _ := by
  apply (cancel_epi (moduleExtPowerColimitIsoLocalCohomology J P n).hom).mp
  apply colimit.hom_ext
  intro k
  simp only [← Category.assoc, moduleExtPowerColimitIsoLocalCohomology_ι, Category.comp_id]
  change (localCohomologyPowerStageι J P n k ≫ _) ≫ _ = localCohomologyPowerStageι J P n k
  rw [localDualityMap_stage]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change localCohomologyPowerStageι J P n k
    (moduleExtPairing (ModuleCat.of R (R ⧸ J ^ k)) P P n 0 n (add_zero n)
      x (moduleExtIdentity P)) = localCohomologyPowerStageι J P n k x
  rw [moduleExtPairing_identity_right]

/-- The canonical top-degree map with equal coefficients is injective,
over every commutative ring and for every module. -/
theorem localDualityMap_self_top_injective (J : Ideal R) (P : ModuleCat.{u} R) (n : ℕ) :
    Function.Injective (localDualityMap J P P n 0 n (add_zero n)) := by
  have h : Function.LeftInverse (localDualityIdentityEvaluation J P n)
      (localDualityMap J P P n 0 n (add_zero n)) := by
    intro x
    exact congrArg (fun f => f x) (localDualityMap_identity_evaluation J P n)
  exact h.injective

end SGA.SGA2.ExposeV
