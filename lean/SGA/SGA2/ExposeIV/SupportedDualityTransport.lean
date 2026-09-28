/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes

/-!
# Transport of actual canonical Hom duality

Changing the coefficient by a specified isomorphism preserves the actual
canonical evaluation maps, not just the existence of some bidual isomorphism.
The same applies to changing the original test module by an isomorphism.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {H K : ModuleCat.{u} R}

/-- Actual postcomposition by a specified coefficient isomorphism. -/
def moduleHomCoefficientIso (e : H ≅ K) (M : ModuleCat.{u} R) :
    (moduleHomDual H).obj (op M) ≅ (moduleHomDual K).obj (op M) :=
  ((linearYoneda R (ModuleCat R)).mapIso e).app (op M)

/-- The induced actual double-Hom comparison. -/
def moduleBidualCoefficientIso (e : H ≅ K) (M : ModuleCat.{u} R) :
    (moduleHomBidual H).obj M ≅ (moduleHomBidual K).obj M :=
  moduleHomCoefficientIso e ((moduleHomDual H).obj (op M)) ≪≫
    (moduleHomDual K).mapIso (moduleHomCoefficientIso e M).symm.op

/-- Coefficient transport intertwines the original evaluation itself. -/
@[reassoc] theorem moduleBidualCoefficientIso_evaluation (e : H ≅ K)
    (M : ModuleCat.{u} R) :
    moduleBidualEvaluation H M ≫ (moduleBidualCoefficientIso e M).hom =
      moduleBidualEvaluation K M := by
  apply ModuleCat.hom_ext
  ext x
  apply ModuleCat.hom_ext
  ext g
  change e.hom (e.inv (ModuleCat.Hom.hom g x)) = ModuleCat.Hom.hom g x
  exact ConcreteCategory.congr_hom e.inv_hom_id (ModuleCat.Hom.hom g x)

/-- Canonical reflexivity is invariant under the specified coefficient iso. -/
theorem moduleBidualEvaluation_isIso_of_coefficientIso (e : H ≅ K)
    (M : ModuleCat.{u} R) [IsIso (moduleBidualEvaluation H M)] :
    IsIso (moduleBidualEvaluation K M) := by
  rw [← moduleBidualCoefficientIso_evaluation e M]
  infer_instance

/-- Canonical reflexivity is invariant under the specified test-module iso. -/
theorem moduleBidualEvaluation_isIso_of_testIso (H : ModuleCat.{u} R)
    {M N : ModuleCat.{u} R} (e : M ≅ N) [IsIso (moduleBidualEvaluation H M)] :
    IsIso (moduleBidualEvaluation H N) := by
  have h : IsIso (e.hom ≫ moduleBidualEvaluation H N) := by
    rw [moduleBidualEvaluation_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-- Finite original Hom values transfer by actual postcomposition. -/
theorem finiteSupportedHomValues_of_coefficientIso (J : Ideal R) (e : H ≅ K)
    (h : FiniteSupportedHomValues J H) : FiniteSupportedHomValues J K := by
  intro M hM hs
  have := h M hM hs
  exact Module.Finite.of_surjective (moduleHomCoefficientIso e M).hom.hom
    (moduleHomCoefficientIso e M).toLinearEquiv.surjective

/-- All original supported canonical evaluations transfer by the same iso. -/
theorem supportedModuleBiduality_of_coefficientIso (J : Ideal R) (e : H ≅ K)
    (h : SupportedModuleBiduality J H) : SupportedModuleBiduality J K := by
  intro M hM hs
  have := h M hM hs
  exact moduleBidualEvaluation_isIso_of_coefficientIso e M

/-- Transport of the named supported-dualizing property, with its support retained. -/
theorem SupportedDualizingModule.of_iso [IsLocalRing R] (e : H ≅ K)
    (h : SupportedDualizingModule H) : SupportedDualizingModule K :=
  ⟨(supportedModuleProperty (IsLocalRing.maximalIdeal R)).prop_of_iso e h.1,
    finiteSupportedHomValues_of_coefficientIso _ e h.2.1,
    supportedModuleBiduality_of_coefficientIso _ e h.2.2⟩

end SGA.SGA2.ExposeIV
