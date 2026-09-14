/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MacaulayDualizingModule
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# IV.5.2: Macaulay's module is the genuine continuous dual

The source ring carries its actual ideal-adic topology and the coefficient
field the discrete topology. Continuity of a linear functional is equivalent
to vanishing on an ideal power. The comparison uses precomposition with the
original quotient maps, not completion of the source ring.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing Filter
open scoped Topology

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- Actual continuous `K`-linear functionals, with the ideal-adic source
topology and the discrete coefficient-field topology. -/
abbrev adicContinuousDual (I : Ideal A) : Type u := by
  letI : TopologicalSpace A := I.adicTopology
  letI : TopologicalSpace K := ⊥
  exact A →L[K] K

instance adicContinuousDualAddCommGroup (I : Ideal A) :
    AddCommGroup (adicContinuousDual (K := K) I) := by
  letI : TopologicalSpace A := I.adicTopology
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := discreteTopology_bot K
  exact inferInstanceAs (AddCommGroup (A →L[K] K))

/-- The genuine continuity criterion: a linear functional to the discrete
field is continuous exactly when its kernel contains an actual ideal power. -/
theorem continuous_linearForm_adic_iff (I : Ideal A) (φ : A →ₗ[K] K) :
    letI : TopologicalSpace A := I.adicTopology
    letI : TopologicalSpace K := ⊥
    Continuous φ ↔ ∃ n : ℕ, ∀ a ∈ I ^ n, φ a = 0 := by
  let : TopologicalSpace A := I.adicTopology
  let : TopologicalSpace K := ⊥
  let : DiscreteTopology K := discreteTopology_bot K
  let : NonarchimedeanRing A := I.nonarchimedean
  constructor
  · intro hφ
    have hzero : φ ⁻¹' ({0} : Set K) ∈ 𝓝 (0 : A) :=
      hφ.continuousAt.preimage_mem_nhds (by simp [nhds_discrete])
    obtain ⟨n, _, hn⟩ := I.hasBasis_nhds_zero_adic.mem_iff.mp hzero
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    apply continuous_of_tendsto_nhds_zero φ
    rw [nhds_discrete K]
    apply tendsto_pure.mpr
    exact I.hasBasis_nhds_zero_adic.mem_iff.mpr ⟨n, trivial, hn⟩

/-- Scalar multiplication acts by precomposition with multiplication in the
original source ring. Its continuity uses the genuine adic ring topology. -/
def adicContinuousDualSMul (I : Ideal A) (a : A)
    (φ : adicContinuousDual (K := K) I) : adicContinuousDual (K := K) I := by
  letI : TopologicalSpace A := I.adicTopology
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := discreteTopology_bot K
  letI : NonarchimedeanRing A := I.nonarchimedean
  exact
    { toFun := fun x => φ (x * a)
      map_add' := fun x y => by rw [add_mul, map_add]
      map_smul' := fun r x => by rw [smul_mul_assoc, map_smul]; rfl
      cont := φ.cont.comp (continuous_id.mul_const a) }

instance adicContinuousDualModule (I : Ideal A) :
    Module A (adicContinuousDual (K := K) I) := by
  letI : TopologicalSpace A := I.adicTopology
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := discreteTopology_bot K
  exact
    { smul := adicContinuousDualSMul I
      one_smul := fun φ => by ext x; exact congrArg φ (mul_one x)
      mul_smul := fun a b φ => by ext x; exact congrArg φ (mul_assoc x a b).symm
      smul_zero := fun a => by ext x; rfl
      smul_add := fun a φ ψ => by ext x; rfl
      add_smul := fun a b φ => by
        ext x
        exact (congrArg φ (mul_add x a b)).trans (map_add φ _ _)
      zero_smul := fun φ => by
        ext x
        exact (congrArg φ (mul_zero x)).trans (map_zero φ) }

@[simp]
theorem adicContinuousDual_smul_apply (I : Ideal A) (a : A)
    (φ : adicContinuousDual (K := K) I) (x : A) :
    (a • φ) x = φ (x * a) := rfl

variable [IsNoetherianRing A] [IsLocalRing A]

/-- Identity comparison with the quotient's original coefficient-field action. -/
def macaulayQuotientCoefficientEquiv (n : ℕ) :
    (A ⧸ maximalIdeal A ^ n) ≃ₗ[K]
      (restrictScalars (algebraMap K A)).obj (ModuleCat.of A (A ⧸ maximalIdeal A ^ n)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := (IsScalarTower.algebraMap_smul A r x).symm

/-- A quotient functional gives a genuine continuous functional by
precomposition with the original quotient map. -/
def macaulayQuotientDualToContinuous (n : ℕ) :
    macaulayQuotientDual (K := K) (A := A) n ⟶
      ModuleCat.of A (adicContinuousDual (K := K) (maximalIdeal A)) := by
  letI : TopologicalSpace A := (maximalIdeal A).adicTopology
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := discreteTopology_bot K
  letI := (macaulayQuotientDual (K := K) (A := A) n).isModule
  refine ModuleCat.ofHom (X := macaulayQuotientDual (K := K) (A := A) n)
    (show macaulayQuotientDual (K := K) (A := A) n →ₗ[A]
    adicContinuousDual (K := K) (maximalIdeal A) from
    { toFun := fun φ =>
        { toLinearMap := (macaulayQuotientDualEquiv n φ).comp
            ((macaulayQuotientCoefficientEquiv (K := K) n).toLinearMap.comp
              (((maximalIdeal A ^ n).mkQ).restrictScalars K))
          cont := ?_ }
      map_add' := ?_
      map_smul' := ?_ })
  · apply (continuous_linearForm_adic_iff _ _).mpr
    refine ⟨n, fun a ha => ?_⟩
    change macaulayQuotientDualEquiv n φ (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro φ ψ
    ext a
    rfl
  · intro a φ
    ext x
    change macaulayQuotientDualEquiv n φ
        (a • Ideal.Quotient.mk (maximalIdeal A ^ n) x) =
      macaulayQuotientDualEquiv n φ (Ideal.Quotient.mk (maximalIdeal A ^ n) (x * a))
    congr 1
    change Ideal.Quotient.mk (maximalIdeal A ^ n) a * Ideal.Quotient.mk _ x =
      Ideal.Quotient.mk _ (x * a)
    rw [map_mul, mul_comm]

@[simp]
theorem macaulayQuotientDualToContinuous_apply (n : ℕ)
    (φ : macaulayQuotientDual (K := K) (A := A) n) (a : A) :
    macaulayQuotientDualToContinuous n φ a =
      macaulayQuotientDualEquiv n φ (Ideal.Quotient.mk (maximalIdeal A ^ n) a) := rfl

/-- The literal quotient-dual transitions preserve the continuous functional. -/
@[reassoc]
theorem macaulayQuotientDualToContinuous_transition {n m : ℕ} (h : n ≤ m) :
    macaulayQuotientDualTransition (K := K) (A := A) h ≫
      macaulayQuotientDualToContinuous m = macaulayQuotientDualToContinuous n := by
  let : TopologicalSpace A := (maximalIdeal A).adicTopology
  let : TopologicalSpace K := ⊥
  apply ModuleCat.hom_ext
  ext φ a
  exact macaulayQuotientDualTransition_apply h φ a

/-- The original quotient-dual diagram maps to the actual continuous dual. -/
def macaulayContinuousDualCocone :
    Cocone (macaulayQuotientDualDiagram (K := K) (A := A)) where
  pt := ModuleCat.of A (adicContinuousDual (K := K) (maximalIdeal A))
  ι :=
    { app := macaulayQuotientDualToContinuous
      naturality := fun n m f => by
        have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
        rw [hf]
        change macaulayQuotientDualTransition (leOfHom f) ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact macaulayQuotientDualToContinuous_transition (K := K) (A := A) (leOfHom f) }

/-- The canonical comparison from Macaulay's original colimit to continuous
linear functionals on the original ring, not its completion. -/
def macaulayModuleToContinuous : macaulayModule (K := K) (A := A) ⟶
    ModuleCat.of A (adicContinuousDual (K := K) (maximalIdeal A)) :=
  colimit.desc (macaulayQuotientDualDiagram (K := K) (A := A))
    (macaulayContinuousDualCocone (K := K) (A := A))

@[reassoc (attr := simp)]
theorem macaulayModuleToContinuous_ι (n : ℕ) :
    macaulayModuleι (K := K) (A := A) n ≫ macaulayModuleToContinuous =
      macaulayQuotientDualToContinuous n :=
  colimit.ι_desc _ n

/-- A zero continuous functional has zero representative at every quotient
stage; consequently the original colimit comparison is injective. -/
theorem macaulayModuleToContinuous_injective :
    Function.Injective (macaulayModuleToContinuous (K := K) (A := A)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨n, φ, rfl⟩ := macaulayModule_exists_rep x
  have hφ : φ = 0 := by
    apply (macaulayQuotientDualEquiv n).injective
    ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hh := congrArg (fun ψ : adicContinuousDual (K := K) (maximalIdeal A) => ψ a) hx
    change (macaulayModuleι n ≫ macaulayModuleToContinuous) φ a = 0 at hh
    rw [macaulayModuleToContinuous_ι] at hh
    change macaulayQuotientDualEquiv n φ (Ideal.Quotient.mk _ a) = 0 at hh
    simpa using hh
  rw [hφ, map_zero]

/-- Every actual continuous functional factors through an actual ideal-power
quotient, by the proved continuity criterion. -/
theorem macaulayModuleToContinuous_surjective :
    Function.Surjective (macaulayModuleToContinuous (K := K) (A := A)) := by
  let : TopologicalSpace A := (maximalIdeal A).adicTopology
  let : TopologicalSpace K := ⊥
  intro φ
  obtain ⟨n, hn⟩ := (continuous_linearForm_adic_iff (maximalIdeal A) φ.toLinearMap).mp φ.cont
  let ψ : macaulayQuotientDual (K := K) (A := A) n :=
    (macaulayQuotientDualEquiv n).symm
      ((((maximalIdeal A ^ n).restrictScalars K).liftQ φ.toLinearMap hn).comp
        (macaulayQuotientCoefficientEquiv (K := K) n).symm.toLinearMap)
  refine ⟨macaulayModuleι n ψ, ?_⟩
  change (macaulayModuleι n ≫ macaulayModuleToContinuous) ψ = φ
  rw [macaulayModuleToContinuous_ι]
  apply ContinuousLinearMap.ext
  intro a
  change macaulayQuotientDualEquiv n ψ (Ideal.Quotient.mk _ a) = φ a
  simp only [ψ, AddEquiv.apply_symm_apply]
  rfl

/-- **IV.5.2, topological clause:** the actual Macaulay module is canonically
the continuous `K`-linear dual of the original adic ring. Completeness is
not assumed. -/
def macaulayModuleIsoContinuousDual : macaulayModule (K := K) (A := A) ≅
    ModuleCat.of A (adicContinuousDual (K := K) (maximalIdeal A)) :=
  (LinearEquiv.ofBijective (macaulayModuleToContinuous (K := K) (A := A)).hom
    ⟨macaulayModuleToContinuous_injective, macaulayModuleToContinuous_surjective⟩).toModuleIso

@[simp]
theorem macaulayModuleIsoContinuousDual_hom :
    (macaulayModuleIsoContinuousDual (K := K) (A := A)).hom =
      macaulayModuleToContinuous := rfl

end SGA.SGA2.ExposeIV
