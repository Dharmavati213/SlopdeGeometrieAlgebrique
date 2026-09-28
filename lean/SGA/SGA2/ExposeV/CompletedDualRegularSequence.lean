/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualRegularSequence
import SGA.SGA2.ExposeV.CompletedDualDimension

/-!
# Support control on the original completed dual sequence

The complete original Hom duals give exact sequences on their actual
completions. Both scalar maps become multiplication by the original
scalar's image in the completed ring. The completed scalar kernel therefore
controls the support error in the completed dual regular-element sequence.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open scoped Pointwise
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Original scalar injectivity persists on the actual completion of
an already complete module, with its original completed scalar action. -/
theorem completion_isSMulRegular_of_complete (J : Ideal R)
    (M : ModuleCat.{u} R) [IsAdicComplete J M] (x : R) (hx : IsSMulRegular M x) :
    IsSMulRegular (AdicCompletion J M) (algebraMap R (AdicCompletion J R) x) := by
  have hi := completion_map_injective_of_complete J (x • 𝟙 M).hom hx
  change Function.Injective
    (algebraMap R (AdicCompletion J R) x • 𝟙 (ModuleCat.of (AdicCompletion J R)
      (AdicCompletion J M))).hom
  rw [← completion_map_smul_id J M x]
  exact hi

variable [IsNoetherianRing R] [IsLocalRing R]

/-- Positive support dimension in the completed middle dual comes from
the principal quotient of the completed higher dual, if the original
scalar's kernel on the completed lower dual is supported at the closed point. -/
theorem localRing_completedDual_quotient_supportDim_le_quotSMulTop
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D)
    (x : R) (hx : IsSMulRegular M x) (i : ℕ)
    (hker : supportedModuleProperty (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (ModuleCat.of (AdicCompletion (maximalIdeal R) R) (LinearMap.ker
        (algebraMap R (AdicCompletion (maximalIdeal R) R) x •
          𝟙 (ModuleCat.of (AdicCompletion (maximalIdeal R) R)
            (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
              (op ((_root_.localCohomology (maximalIdeal R) i).obj M)))))).hom)))
    (hpos : 0 < Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj
          (ModuleCat.of R (QuotSMulTop x M))))))) :
    Module.supportDim (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj
          (ModuleCat.of R (QuotSMulTop x M)))))) ≤
      Module.supportDim (AdicCompletion (maximalIdeal R) R)
        (QuotSMulTop (algebraMap R (AdicCompletion (maximalIdeal R) R) x)
          (AdicCompletion (maximalIdeal R) ((moduleHomDual D).obj
            (op ((_root_.localCohomology (maximalIdeal R) (i + 1)).obj M))))) := by
  have : Injective D := ((supportedDualizingModule_iff_injective_essential_residue D).mp hD).1
  let T := localCohomologyDualBoundarySequence (maximalIdeal R) M D x hx i
  let V := localCohomologyDualScalarSequence (maximalIdeal R) M D x hx i
  have : IsAdicComplete (maximalIdeal R) T.X₁ :=
    (localRing_localCohomology_dual_completeProperty M D hD (i + 1)).2
  have : IsAdicComplete (maximalIdeal R) T.X₂ :=
    (localRing_localCohomology_dual_completeProperty
      (ModuleCat.of R (QuotSMulTop x M)) D hD i).2
  have : IsAdicComplete (maximalIdeal R) T.X₃ :=
    (localRing_localCohomology_dual_completeProperty M D hD i).2
  have : IsAdicComplete (maximalIdeal R) V.X₁ :=
    (localRing_localCohomology_dual_completeProperty M D hD (i + 1)).2
  have : IsAdicComplete (maximalIdeal R) V.X₂ :=
    (localRing_localCohomology_dual_completeProperty M D hD (i + 1)).2
  have : IsAdicComplete (maximalIdeal R) V.X₃ :=
    (localRing_localCohomology_dual_completeProperty
      (ModuleCat.of R (QuotSMulTop x M)) D hD i).2
  let C := completionShortComplex (maximalIdeal R) T
  let U := completionShortComplex (maximalIdeal R) V
  let a := algebraMap R (AdicCompletion (maximalIdeal R) R) x
  have hC : C.Exact := completionShortComplex_exact_of_complete _ T
    (localCohomologyDualBoundarySequence_exact _ M D x hx i)
  have hU : U.Exact := completionShortComplex_exact_of_complete _ V
    (localCohomologyDualScalarSequence_exact _ M D x hx i)
  have hfU : U.f = a • 𝟙 C.X₁ := by
    change ModuleCat.ofHom (AdicCompletion.map (maximalIdeal R) V.f.hom) = _
    have hf : V.f = x • 𝟙 T.X₁ := localCohomologyDualScalarSequence_f _ M D x hx i
    rw [hf]
    exact completion_map_smul_id _ T.X₁ x
  have hk : a • (⊤ : Submodule (AdicCompletion (maximalIdeal R) R) C.X₁) =
      LinearMap.ker C.f.hom := by
    have hr := (C.X₁.smulShortComplex_exact a).moduleCat_range_eq_ker
    have he := hU.moduleCat_range_eq_ker
    rw [hfU] at he
    have hr' := hr.trans
      (a • (⊤ : Submodule (AdicCompletion (maximalIdeal R) R) C.X₁)).ker_mkQ
    exact hr'.symm.trans he
  have hg : C.g ≫ (a • 𝟙 C.X₃) = 0 := by
    let W := ShortComplex.mk T.g (x • 𝟙 T.X₃)
      (localCohomologyDualBoundarySequence_g_comp_smul (maximalIdeal R) M D x hx i)
    have hw := (completionShortComplex (maximalIdeal R) W).zero
    change C.g ≫ ModuleCat.ofHom (AdicCompletion.map (maximalIdeal R) (x • 𝟙 T.X₃).hom) = 0 at hw
    rwa [completion_map_smul_id] at hw
  exact supportDim_le_quotSMulTop_of_scalar_exact C hC a hk hg hker hpos

end SGA.SGA2.ExposeV
