/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.PowerTorsionLocalCohomology
import SGA.SGA2.ExposeV.LocalCohomologyLinear
import SGA.SGA2.ExposeV.LocalCohomologyYonedaSequence
import SGA.SGA2.ExposeV.LocalRingFiniteness
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Category

/-!
# V.3.1(ii): the dual-dimension bound over a complete local ring

The original regular-element coefficient sequence gives an injection of
the principal quotient of the higher dual into the lower dual. Removing
actual maximal-ideal torsion allows induction on the cohomological degree.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open scoped Pointwise
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual scalar map remains that scalar map after Hom duality. -/
theorem moduleHomDual_map_smul_id (D X : ModuleCat.{u} R) (x : R) :
    (moduleHomDual D).map (x • 𝟙 X).op = x • 𝟙 ((moduleHomDual D).obj (op X)) := by
  apply ModuleCat.hom_ext
  ext f
  apply ModuleCat.hom_ext
  ext y
  exact f.hom.map_smul x y

/-- Exactness after scalar multiplication embeds the actual principal
quotient into the next module, and hence bounds its support dimension. -/
theorem supportDim_quotSMulTop_le_of_exact
    (N P : ModuleCat.{u} R) (x : R) (g : N ⟶ P)
    (hw : (x • 𝟙 N) ≫ g = 0)
    (he : (ShortComplex.mk _ _ hw).Exact) :
    Module.supportDim R (QuotSMulTop x N) ≤ Module.supportDim R P := by
  let p : Submodule R N := x • ⊤
  have hr : LinearMap.range (x • 𝟙 N).hom = p :=
    (N.smulShortComplex_exact x).moduleCat_range_eq_ker.trans p.ker_mkQ
  have hk : p = LinearMap.ker g.hom := hr.symm.trans he.moduleCat_range_eq_ker
  exact Module.supportDim_le_of_injective (p.liftQ g.hom hk.le)
    ((LinearMap.ker_eq_bot).mp (p.ker_liftQ_eq_bot _ hk.le hk.ge))

/-- The dual of the actual regular-element boundary sequence. -/
def localCohomologyDualScalarSequence
    (I : Ideal R) (M D : ModuleCat.{u} R)
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  (ShortComplex.mk _ _ (localCohomologyYonedaBoundary_comp I
    (M.smulShortComplex x) hx.smulShortComplex_shortExact i)).op.map (moduleHomDual D)

theorem localCohomologyDualScalarSequence_exact
    (I : Ideal R) (M D : ModuleCat.{u} R) [Injective D]
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    (localCohomologyDualScalarSequence I M D x hx i).Exact :=
  (localCohomologyYoneda_exact₁ I (M.smulShortComplex x)
    hx.smulShortComplex_shortExact i).op.map (moduleHomDual D)

/-- The first map is the original scalar endomorphism on the higher dual. -/
theorem localCohomologyDualScalarSequence_f
    (I : Ideal R) (M D : ModuleCat.{u} R)
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    (localCohomologyDualScalarSequence I M D x hx i).f =
      x • 𝟙 ((moduleHomDual D).obj (op ((_root_.localCohomology I (i + 1)).obj M))) := by
  change (moduleHomDual D).map ((_root_.localCohomology I (i + 1)).map (x • 𝟙 M)).op = _
  rw [Functor.map_smul, (_root_.localCohomology I (i + 1)).map_id]
  exact moduleHomDual_map_smul_id D _ x

/-- Dualizing the original regular-element boundary controls the dimension
of the actual principal quotient of the higher local-cohomology dual. -/
theorem localCohomology_dual_quotSMulTop_supportDim_le
    (I : Ideal R) (M D : ModuleCat.{u} R) [Injective D]
    (x : R) (hx : IsSMulRegular M x) (i : ℕ) :
    Module.supportDim R (QuotSMulTop x
      ((moduleHomDual D).obj (op ((_root_.localCohomology I (i + 1)).obj M)))) ≤
      Module.supportDim R ((moduleHomDual D).obj
        (op ((_root_.localCohomology I i).obj (ModuleCat.of R (QuotSMulTop x M))))) := by
  let T := localCohomologyDualScalarSequence I M D x hx i
  have he := localCohomologyDualScalarSequence_exact I M D x hx i
  have hf := localCohomologyDualScalarSequence_f I M D x hx i
  have hw := T.zero
  rw [show T.f = x • 𝟙 _ from hf] at hw
  apply supportDim_quotSMulTop_le_of_exact _ _ x T.g hw
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (x • 𝟙 ((moduleHomDual D).obj
    (op ((_root_.localCohomology I (i + 1)).obj M)))).hom = LinearMap.ker T.g.hom
  rw [← hf]
  exact he.moduleCat_range_eq_ker

variable [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- Support at the closed point has dimension at most zero, including
the zero module whose support dimension is bottom. -/
theorem supportDim_le_zero_of_supported_maximalIdeal (N : ModuleCat.{u} R)
    (hN : supportedModuleProperty (maximalIdeal R) N) :
    Module.supportDim R N ≤ 0 := by
  have hs : Module.support R N ⊆ {⟨maximalIdeal R, inferInstance⟩} := by
    simpa only [supportedModuleProperty, PrimeSpectrum.zeroLocus_eq_singleton] using hN
  have : Subsingleton (Module.support R N) := ⟨fun a b =>
    Subtype.ext ((Set.mem_singleton_iff.mp (hs a.property)).trans
      (Set.mem_singleton_iff.mp (hs b.property)).symm)⟩
  exact Order.krullDim_nonpos_of_subsingleton

/-- The original degree-zero dual is supported at the closed point. -/
theorem localRing_localCohomologyZero_dual_supportDim_le
    (M D : ModuleCat.{u} R) [Module.Finite R M] (hD : SupportedDualizingModule D) :
    Module.supportDim R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))) ≤ 0 := by
  let T := ModuleCat.of R (powerTorsion (maximalIdeal R) M)
  have hs : supportedModuleProperty (maximalIdeal R) T :=
    support_powerTorsion_subset_zeroLocus _ M
  have : Module.Finite R ((moduleHomDual D).obj (op T)) := hD.2.1 T inferInstance hs
  let e := (moduleHomDual D).mapIso (localCohomologyZeroIsoPowerTorsion (maximalIdeal R) M).op
  rw [← Module.supportDim_eq_of_equiv e.toLinearEquiv]
  exact supportDim_le_zero_of_supported_maximalIdeal _
    ((moduleHomDual_support_subset D T).trans hs)

/-- **V.3.1(ii), complete-base dimension assertion.** For any finite
module over a complete noetherian local ring, the original dual of its
degree-`i` local cohomology has support dimension at most `i`. -/
theorem completeLocal_localCohomology_dual_supportDim_le
    [IsAdicComplete (maximalIdeal R) R]
    (M D : ModuleCat.{u} R) [Module.Finite R M]
    (hD : SupportedDualizingModule D) (i : ℕ) :
    Module.supportDim R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) i).obj M))) ≤ i := by
  have : Injective D := ((supportedDualizingModule_iff_injective_essential_residue D).mp hD).1
  induction i generalizing M with
  | zero => exact localRing_localCohomologyZero_dual_supportDim_le M D hD
  | succ i ih =>
    let Q := ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M)
    have := localCohomology_powerTorsion_mkQ_isIso (maximalIdeal R) M (i + 1) (by omega)
    let e := asIso ((_root_.localCohomology (maximalIdeal R) (i + 1)).map
      (ModuleCat.ofHom (powerTorsion (maximalIdeal R) M).mkQ))
    rw [← Module.supportDim_eq_of_equiv ((moduleHomDual D).mapIso e.op).toLinearEquiv]
    obtain ⟨x, hxm, hx⟩ := exists_regular_on_powerTorsion_quotient M
    let N := (moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) (i + 1)).obj Q))
    have : Module.Finite R N := localRing_localCohomology_dual_finite Q D hD (i + 1)
    calc
      Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop x N) + 1 :=
        Module.supportDim_le_supportDim_quotSMulTop_succ hxm
      _ ≤ Module.supportDim R ((moduleHomDual D).obj
          (op ((_root_.localCohomology (maximalIdeal R) i).obj
            (ModuleCat.of R (QuotSMulTop x Q))))) + 1 :=
        _root_.add_le_add (localCohomology_dual_quotSMulTop_supportDim_le
          (maximalIdeal R) Q D x hx i) le_rfl
      _ ≤ (i : WithBot ℕ∞) + 1 := _root_.add_le_add
        (ih (ModuleCat.of R (QuotSMulTop x Q))) le_rfl
      _ = (i + 1 : ℕ) := by simp

end SGA.SGA2.ExposeV
