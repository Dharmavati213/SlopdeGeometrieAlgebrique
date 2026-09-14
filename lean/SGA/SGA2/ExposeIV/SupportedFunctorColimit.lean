/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDiagram
import SGA.SGA2.ExposeIV.SupportedHomDetection
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The actual representing colimit for supported functors

The module in IV.1.3 is the categorical colimit of the original diagram
`T(R/Jⁿ)`. It is supported on `V(J)`. For a left-exact functor the actual
stage maps are injective, and every map from a finite module into this
colimit factors through one stage. No representing property is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The actual colimit specified in IV.1.3. -/
def supportedFunctorColimit : ModuleCat.{u} R := colimit (supportedFunctorDiagram J T)

/-- The original structural map from `T(R/Jⁿ)` to its colimit. -/
def supportedFunctorColimitι (n : ℕ) :
    supportedFunctorStage J T n ⟶ supportedFunctorColimit J T :=
  colimit.ι (supportedFunctorDiagram J T) n

@[reassoc]
theorem supportedFunctorColimitι_transition {n m : ℕ} (h : n ≤ m) :
    supportedFunctorTransition J T h ≫ supportedFunctorColimitι J T m =
      supportedFunctorColimitι J T n :=
  colimit.w (supportedFunctorDiagram J T) (homOfLE h)

/-- Every colimit element has a representative in an original stage. -/
theorem supportedFunctorColimit_exists_rep (x : supportedFunctorColimit J T) :
    ∃ (n : ℕ) (y : supportedFunctorStage J T n), supportedFunctorColimitι J T n y = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  exact Concrete.colimit_exists_rep (supportedFunctorDiagram J T) x

/-- The actual colimit is ideal-power torsion, without requiring left exactness. -/
theorem supportedFunctorColimit_powerTorsion :
    powerTorsion J (supportedFunctorColimit J T) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, y, rfl⟩ := supportedFunctorColimit_exists_rep J T x
  apply (mem_powerTorsion_iff J _ _).mpr
  refine ⟨n, fun r hr ↦ ?_⟩
  rw [← (supportedFunctorColimitι J T n).hom.map_smul]
  rw [Module.mem_annihilator.mp (supportedFunctorStage_annihilator J T n hr) y]
  exact (supportedFunctorColimitι J T n).hom.map_zero

/-- Its support is the actual module support, contained in `V(J)`. -/
theorem supportedFunctorColimit_support :
    Module.support R (supportedFunctorColimit J T) ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
  support_subset_zeroLocus_of_powerTorsion_eq_top J _ (supportedFunctorColimit_powerTorsion J T)

/-- The images of the original stage maps form an increasing family. -/
theorem supportedFunctorColimit_range_monotone :
    Monotone (fun n : ℕ ↦ LinearMap.range (supportedFunctorColimitι J T n).hom) := by
  intro n m h x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨supportedFunctorTransition J T h y, ?_⟩
  exact ConcreteCategory.congr_hom (supportedFunctorColimitι_transition J T h) y

/-- The images of all stages exhaust the actual colimit. -/
theorem supportedFunctorColimit_iSup_range :
    (⨆ n : ℕ, LinearMap.range (supportedFunctorColimitι J T n).hom) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, y, rfl⟩ := supportedFunctorColimit_exists_rep J T x
  exact Submodule.mem_iSup_of_mem n (LinearMap.mem_range_self _ y)

section LeftExact

variable [PreservesFiniteLimits T]

/-- Left exactness makes every actual colimit stage map injective. -/
theorem supportedFunctorColimitι_injective (n : ℕ) :
    Function.Injective (supportedFunctorColimitι J T n) := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  intro x y h
  obtain ⟨k, f, g, hfg⟩ :=
    Concrete.colimit_exists_of_rep_eq (supportedFunctorDiagram J T) x y h
  have hg : g = f := Subsingleton.elim _ _
  subst g
  exact (ModuleCat.mono_iff_injective
    (supportedFunctorTransition J T (leOfHom f))).mp inferInstance hfg

instance (n : ℕ) : Mono (supportedFunctorColimitι J T n) :=
  (ModuleCat.mono_iff_injective _).mpr (supportedFunctorColimitι_injective J T n)

omit [PreservesFiniteLimits T] in
/-- The image of a finite module in the actual colimit lies in one stage. -/
theorem supportedFunctorColimit_range_le_stage (M : ModuleCat.{u} R) [Module.Finite R M]
    (f : M ⟶ supportedFunctorColimit J T) :
    ∃ n : ℕ, LinearMap.range f.hom ≤ LinearMap.range (supportedFunctorColimitι J T n).hom := by
  classical
  obtain ⟨S, hS⟩ := Submodule.fg_range f.hom
  have hrep (x : S) : ∃ n : ℕ, x.val ∈ LinearMap.range (supportedFunctorColimitι J T n).hom := by
    obtain ⟨n, y, hy⟩ := supportedFunctorColimit_exists_rep J T x.val
    exact ⟨n, y, hy⟩
  choose k hk using hrep
  refine ⟨S.attach.sup k, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact supportedFunctorColimit_range_monotone J T
    (Finset.le_sup (S.mem_attach ⟨x, hx⟩)) (hk ⟨x, hx⟩)

/-- A map from a finite module to the actual colimit factors through an
original stage. Finiteness of the source suffices because the stage maps
are genuinely injective. -/
theorem supportedFunctorColimit_exists_factor (M : ModuleCat.{u} R) [Module.Finite R M]
    (f : M ⟶ supportedFunctorColimit J T) :
    ∃ (n : ℕ) (g : M ⟶ supportedFunctorStage J T n),
      g ≫ supportedFunctorColimitι J T n = f := by
  obtain ⟨n, hn⟩ := supportedFunctorColimit_range_le_stage J T M f
  let e := LinearEquiv.ofInjective (supportedFunctorColimitι J T n).hom
    (supportedFunctorColimitι_injective J T n)
  let g : M →ₗ[R] supportedFunctorStage J T n := e.symm.toLinearMap.comp
    (f.hom.codRestrict _ (fun x ↦ hn (LinearMap.mem_range_self f.hom x)))
  refine ⟨n, ModuleCat.ofHom (X := M) (Y := supportedFunctorStage J T n) g, ?_⟩
  ext x
  exact LinearEquiv.ofInjective_symm_apply _
    (h := supportedFunctorColimitι_injective J T n) _

end LeftExact

end SGA.SGA2.ExposeIV
