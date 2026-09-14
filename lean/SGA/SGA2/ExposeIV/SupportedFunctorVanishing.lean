/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorRepresentation

/-!
# Detecting vanishing of actual supported left-exact functors

The functor's actual colimit and any finite module of full support detect
its vanishing. Unlike a conditional representability lemma, the needed
representation is supplied here by the proved canonical IV.1.3 theorem.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- A zero functor has zero actual quotient colimit, without a left-exactness
assumption. -/
theorem supportedFunctorColimit_isZero_of_isZero (h : IsZero T) :
    IsZero (supportedFunctorColimit J T) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  obtain ⟨n, y, rfl⟩ := supportedFunctorColimit_exists_rep J T x
  have : Subsingleton (supportedFunctorStage J T n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (h.obj _)
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy]
  exact (supportedFunctorColimitι J T n).hom.map_zero

/-- Vanishing of the actual representing colimit forces vanishing of a
left-exact functor. -/
theorem supportedFunctor_isZero_of_colimit [PreservesFiniteLimits T]
    (h : IsZero (supportedFunctorColimit J T)) : IsZero T := by
  apply (additiveSupportedFunctorRepresentationIso J T).isZero_iff.mpr
  apply Functor.isZero
  intro M
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  change Subsingleton (M.unop.obj.obj ⟶ supportedFunctorColimit J T)
  exact ⟨fun f g ↦ h.eq_of_tgt f g⟩

/-- The original left-exact functor vanishes precisely when its actual
quotient colimit vanishes. -/
theorem supportedFunctor_isZero_iff_colimit [PreservesFiniteLimits T] :
    IsZero T ↔ IsZero (supportedFunctorColimit J T) :=
  ⟨supportedFunctorColimit_isZero_of_isZero J T, supportedFunctor_isZero_of_colimit J T⟩

/-- Any actual finite module of full support detects zero left-exact
functors. The colimit target is not assumed finite. -/
theorem supportedFunctor_isZero_iff_at [PreservesFiniteLimits T]
    (M : SupportedFGModuleCat J)
    (hM : Module.support R M.obj = PrimeSpectrum.zeroLocus (J : Set R)) :
    IsZero T ↔ IsZero (T.obj (op M)) := by
  constructor
  · exact fun h ↦ h.obj _
  · intro h
    have hHom := (additiveSupportedFunctorRepresentationIso J T).app (op M)
      |>.isZero_iff.mp h
    have hSupp : Module.support R (supportedFunctorColimit J T) ⊆ Module.support R M.obj := by
      rw [hM]
      exact supportedFunctorColimit_support J T
    apply supportedFunctor_isZero_of_colimit J T
    exact (isZero_hom_iff_of_support_subset M.obj.obj (supportedFunctorColimit J T) hSupp).mp hHom

/-- The canonical cyclic test module has exactly the required full support. -/
theorem supportedRingQuotient_one_support :
    Module.support R (supportedRingQuotient J 1).obj = PrimeSpectrum.zeroLocus (J : Set R) := by
  change Module.support R (R ⧸ J ^ 1) = _
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, pow_one]

end SGA.SGA2.ExposeIV
