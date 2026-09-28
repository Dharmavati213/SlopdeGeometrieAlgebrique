/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ClosedPointSupportDimension
import SGA.SGA2.ExposeV.SimultaneousRegularElements

/-!
# Support control from the original dual regular-element sequence

The original dual boundary factors through the principal quotient of the
higher dual. Its cokernel is controlled by the original scalar kernel on
the lower dual. If that kernel is supported at the closed point, a positive
support dimension of the middle term must come from the principal quotient.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open scoped Pointwise
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original dual boundary followed by the dual quotient-coefficient map. -/
def localCohomologyDualBoundarySequence (I : Ideal R) (M D : ModuleCat.{u} R)
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  (ShortComplex.mk _ _ (comp_localCohomologyYonedaBoundary I
    (M.smulShortComplex x) hx.smulShortComplex_shortExact i)).op.map (moduleHomDual D)

theorem localCohomologyDualBoundarySequence_exact (I : Ideal R)
    (M D : ModuleCat.{u} R) [Injective D]
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    (localCohomologyDualBoundarySequence I M D x hx i).Exact :=
  (localCohomologyYoneda_exact₃ I (M.smulShortComplex x)
    hx.smulShortComplex_shortExact i).op.map (moduleHomDual D)

/-- The original last map lands in the original scalar kernel on the lower dual. -/
theorem localCohomologyDualBoundarySequence_g_comp_smul (I : Ideal R)
    (M D : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    (localCohomologyDualBoundarySequence I M D x hx i).g ≫
      (x • 𝟙 ((moduleHomDual D).obj (op ((_root_.localCohomology I i).obj M)))) = 0 := by
  let S := M.smulShortComplex x
  have h := ((S.map (_root_.localCohomology I i)).op.map (moduleHomDual D)).zero
  have hf : (moduleHomDual D).map ((_root_.localCohomology I i).map (x • 𝟙 M)).op =
      x • 𝟙 ((moduleHomDual D).obj (op ((_root_.localCohomology I i).obj M))) := by
    rw [Functor.map_smul, (_root_.localCohomology I i).map_id]
    exact moduleHomDual_map_smul_id D _ x
  change (localCohomologyDualBoundarySequence I M D x hx i).g ≫
    (moduleHomDual D).map ((_root_.localCohomology I i).map (x • 𝟙 M)).op = 0 at h
  rwa [hf] at h

/-- If the quotient coefficient's cohomology vanishes, the higher dual's
original scalar map is injective. -/
theorem localCohomology_dual_regular_of_quotient_vanishing
    (I : Ideal R) (M D : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular M x) (i : ℕ)
    (hz : IsZero ((_root_.localCohomology I i).obj (ModuleCat.of R (QuotSMulTop x M)))) :
    IsSMulRegular ((moduleHomDual D).obj (op ((_root_.localCohomology I i).obj M))) x := by
  let S := M.smulShortComplex x
  have : Epi ((_root_.localCohomology I i).map S.f) :=
    (localCohomology_map_shortExact_exact I i S hx.smulShortComplex_shortExact).epi_f
      (hz.eq_zero_of_tgt _)
  have hmono := moduleHomDual_map_mono D ((_root_.localCohomology I i).map S.f)
  change Mono ((moduleHomDual D).map ((_root_.localCohomology I i).map (x • 𝟙 M)).op) at hmono
  rw [Functor.map_smul, (_root_.localCohomology I i).map_id,
    moduleHomDual_map_smul_id] at hmono
  exact (ModuleCat.mono_iff_injective _).mp hmono

variable [IsLocalRing R]

/-- The principal quotient in a scalar exact sequence accounts for all
positive-dimensional support once the last scalar kernel is supported at
the closed point. This applies to original or completed scalar actions. -/
theorem supportDim_le_quotSMulTop_of_scalar_exact
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.Exact) (x : R)
    (hk : x • (⊤ : Submodule R T.X₁) = LinearMap.ker T.f.hom)
    (hg : T.g ≫ (x • 𝟙 T.X₃) = 0)
    (hker : supportedModuleProperty (maximalIdeal R)
      (ModuleCat.of R (LinearMap.ker (x • 𝟙 T.X₃).hom)))
    (hpos : 0 < Module.supportDim R T.X₂) :
    Module.supportDim R T.X₂ ≤ Module.supportDim R (QuotSMulTop x T.X₁) := by
  let p : Submodule R T.X₁ := x • ⊤
  let f := p.liftQ T.f.hom hk.le
  let K : Submodule R T.X₃ := LinearMap.ker (x • 𝟙 T.X₃).hom
  let g : T.X₂ →ₗ[R] K := T.g.hom.codRestrict K (fun b =>
    ConcreteCategory.congr_hom hg b)
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT
  have hfg : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (he b).mp (congrArg Subtype.val hb)
      exact ⟨p.mkQ a, ha⟩
    · rintro ⟨a, ha⟩
      obtain ⟨a, rfl⟩ := p.mkQ_surjective a
      apply Subtype.ext
      exact (he b).mpr ⟨a, ha⟩
  exact supportDim_le_of_exact_last_supported (ModuleCat.of R (QuotSMulTop x T.X₁))
    T.X₂ (ModuleCat.of R K) f g hfg hker hpos

/-- A lower dual whose scalar kernel is supported at the closed point
cannot contribute positive-dimensional support to the middle dual. -/
theorem localCohomology_dual_quotient_supportDim_le_quotSMulTop
    (I : Ideal R) (M D : ModuleCat.{u} R) [Injective D]
    (x : R) (hx : IsSMulRegular M x) (i : ℕ)
    (hker : supportedModuleProperty (maximalIdeal R)
      (ModuleCat.of R (LinearMap.ker
        (x • 𝟙 ((moduleHomDual D).obj (op ((_root_.localCohomology I i).obj M)))).hom)))
    (hpos : 0 < Module.supportDim R ((moduleHomDual D).obj
      (op ((_root_.localCohomology I i).obj (ModuleCat.of R (QuotSMulTop x M)))))) :
    Module.supportDim R ((moduleHomDual D).obj
      (op ((_root_.localCohomology I i).obj (ModuleCat.of R (QuotSMulTop x M))))) ≤
      Module.supportDim R (QuotSMulTop x
        ((moduleHomDual D).obj (op ((_root_.localCohomology I (i + 1)).obj M)))) := by
  let T := localCohomologyDualBoundarySequence I M D x hx i
  let p : Submodule R T.X₁ := x • ⊤
  have hr : LinearMap.range (x • 𝟙 T.X₁).hom = p :=
    (T.X₁.smulShortComplex_exact x).moduleCat_range_eq_ker.trans p.ker_mkQ
  have hk : p = LinearMap.ker T.f.hom := by
    rw [← hr]
    have he :=
      (localCohomologyDualScalarSequence_exact I M D x hx i).moduleCat_range_eq_ker
    rw [localCohomologyDualScalarSequence_f] at he
    exact he
  exact supportDim_le_quotSMulTop_of_scalar_exact T
    (localCohomologyDualBoundarySequence_exact I M D x hx i) x hk
    (localCohomologyDualBoundarySequence_g_comp_smul I M D x hx i) hker hpos

end SGA.SGA2.ExposeV
