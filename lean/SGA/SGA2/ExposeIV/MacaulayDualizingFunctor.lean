/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CoefficientFieldDuality
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes

/-!
# IV.5.2: Macaulay's actual coefficient-field dualizing functor

The original functor has literal `Hom_K(M,K)` values. Its `A`-action is
induced by precomposition with scalar multiplication on `M`, not an
independently chosen action. The genuine coinduction adjunction proves an
injective representation and the actual residue tests. The source's
canonical functor biduality and length preservation follow.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable [IsNoetherianRing A] [IsLocalRing A]

/-- The original functor `M ↦ Hom_K(M,K)` on finite closed-point-supported
modules, before giving its values their canonical `A`-action. -/
def macaulayFunctor : (SupportedFGModuleCat (maximalIdeal A))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (supportedFiniteInclusion (maximalIdeal A)).op ⋙
    (forget₂ (FGModuleCat A) (ModuleCat A)).op ⋙
    (restrictScalars (algebraMap K A)).op ⋙ moduleHomDual (ModuleCat.of K K) ⋙
    forget₂ (ModuleCat K) AddCommGrpCat

instance macaulayFunctor_additive : (macaulayFunctor (K := K) (A := A)).Additive := by
  unfold macaulayFunctor
  infer_instance

/-- The source-induced module structure on the literal field-Hom value. -/
abbrev macaulayValue (M : SupportedFGModuleCat (maximalIdeal A)) : ModuleCat.{u} A :=
  supportedFunctorValue (maximalIdeal A) (macaulayFunctor (K := K)) M

omit [IsNoetherianRing A] in
/-- The actual `A`-action is `(aφ)(x)=φ(ax)`. -/
theorem macaulayValue_smul_apply (M : SupportedFGModuleCat (maximalIdeal A))
    (a : A) (φ : macaulayValue (K := K) M) (x : M.obj.obj) :
    ModuleCat.Hom.hom (a • φ) x = ModuleCat.Hom.hom φ (a • x) := rfl

/-- Classical coinduction represents the literal field-Hom functor naturally. -/
def macaulayFunctorCoinductionIso :
    macaulayFunctor (K := K) (A := A) ≅
      supportedModuleHomFunctor (maximalIdeal A)
        (coefficientFieldCoinduced (K := K) (A := A)) ⋙
          forget₂ (ModuleCat A) AddCommGrpCat :=
  NatIso.ofComponents (fun M ↦
    ((forget₂ (ModuleCat K) AddCommGrpCat).mapIso
      (coinducedHomDualIso (algebraMap K A) (ModuleCat.of K K) M.unop.obj.obj)).symm)
    (fun {M N} g ↦ by
      apply AddCommGrpCat.hom_ext
      ext φ
      apply ModuleCat.hom_ext
      ext x
      rename_i a
      change ModuleCat.Hom.hom φ (g.unop.hom.hom.hom ((show A from a) • x)) =
        ModuleCat.Hom.hom φ ((show A from a) • g.unop.hom.hom.hom x)
      rw [LinearMap.map_smul])

variable [Module.Finite K (ResidueField A)]

/-- The actual coinduced module meets the original residue-field test,
using only finiteness of the residue field over the coefficient field. -/
theorem coefficientFieldCoinduced_residueTests :
    moduleHomDualResidueTests (maximalIdeal A)
      (coefficientFieldCoinduced (K := K) (A := A)) := by
  have := fieldModule_injective (ModuleCat.of K K)
  have := coinduced_injective (algebraMap K A) (ModuleCat.of K K)
  intro m hm _
  have : m.IsMaximal := hm
  have : IsSimpleModule A (A ⧸ m) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl A (A ⧸ m)⟩⟩
  have hM : IsFiniteLength A (A ⧸ m) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have := coefficientFieldCoinduced_bidual_finiteLength (K := K)
    (ModuleCat.of A (A ⧸ m)) hM
  exact moduleHomDual_residue_iso_of_bidually_reflexive _ m hm

/-- Macaulay's original functor is exact and has the original residue values. -/
theorem macaulayFunctor_exact_residue :
    SupportedFunctorExact (maximalIdeal A) (macaulayFunctor (K := K)) ∧
      SupportedFunctorResidueTests (maximalIdeal A) (macaulayFunctor (K := K)) := by
  have := fieldModule_injective (ModuleCat.of K K)
  have hI := coinduced_injective (algebraMap K A) (ModuleCat.of K K)
  exact (supportedFunctor_exact_residue_iff_injectiveRepresentation _ _).mpr
    ⟨coefficientFieldCoinduced (K := K) (A := A), hI,
      coefficientFieldCoinduced_residueTests, ⟨macaulayFunctorCoinductionIso⟩⟩

/-- **IV.5.2:** the literal field-Hom functor is dualizing, with its actual
canonical scalar action and canonical twice-iterated-functor evaluation. -/
theorem macaulayFunctor_duality :
    SupportedFunctorDuality (maximalIdeal A) (macaulayFunctor (K := K)) := by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact supportedFunctor_duality_of_exact_residue _ _
    (macaulayFunctor_exact_residue (K := K) (A := A)).1
    (macaulayFunctor_exact_residue (K := K) (A := A)).2

/-- **IV.5.2:** the actual `A`-module values preserve `A`-length. -/
theorem macaulayFunctor_lengthPreserving :
    SupportedFunctorLengthPreserving (maximalIdeal A) (macaulayFunctor (K := K)) := by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact supportedFunctor_length_of_exact_residue _ _
    (macaulayFunctor_exact_residue (K := K) (A := A)).1
    (macaulayFunctor_exact_residue (K := K) (A := A)).2

/-- Exactness, needed for the actual supported colimit representation, is
proved for the original field-Hom functor. -/
instance macaulayFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (macaulayFunctor (K := K) (A := A)) := by
  have : (macaulayFunctor (K := K) (A := A)).PreservesHomology :=
    (supportedFunctorExact_iff_preservesHomology _ _).mp
      (macaulayFunctor_exact_residue (K := K) (A := A)).1
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end SGA.SGA2.ExposeIV
