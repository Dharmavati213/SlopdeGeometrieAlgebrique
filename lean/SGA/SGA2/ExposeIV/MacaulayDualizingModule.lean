/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MacaulayDualizingFunctor
import SGA.SGA2.ExposeIV.SupportedRestrictedHom

/-!
# IV.5.2: the actual quotient-dual colimit representing Macaulay duality

The stages are the original `Hom_K(A/m^n,K)`, with their source-induced
`A`-action, and the transition maps are precomposition with the actual
quotient projections. Their actual categorical colimit is supported and
represents the literal field-Hom functor by the proved IV.1.3 construction.
It is a supported dualizing module. Any other supported representation is
identified with this actual colimit by full faithfulness of restricted Hom.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable [IsNoetherianRing A] [IsLocalRing A]

/-- The literal `n`-th quotient dual with the canonical `A`-action. -/
abbrev macaulayQuotientDual (n : ℕ) : ModuleCat.{u} A :=
  supportedFunctorStage (maximalIdeal A) (macaulayFunctor (K := K)) n

/-- Stage elements are exactly the original coefficient-field linear maps. -/
def macaulayQuotientDualEquiv (n : ℕ) :
    macaulayQuotientDual (K := K) (A := A) n ≃+
      ((restrictScalars (algebraMap K A)).obj
        (ModuleCat.of A (A ⧸ maximalIdeal A ^ n)) →ₗ[K] K) :=
  ModuleCat.homAddEquiv

/-- The stage action is ordinary precomposition by the quotient's scalar action. -/
theorem macaulayQuotientDual_smul_apply (n : ℕ) (a : A)
    (φ : macaulayQuotientDual (K := K) (A := A) n) (x : A ⧸ maximalIdeal A ^ n) :
    macaulayQuotientDualEquiv n (a • φ) x =
      macaulayQuotientDualEquiv n φ (a • x) := rfl

/-- The genuine transition dualizes the original quotient projection. -/
def macaulayQuotientDualTransition {n m : ℕ} (h : n ≤ m) :
    macaulayQuotientDual (K := K) (A := A) n ⟶ macaulayQuotientDual (K := K) m :=
  supportedFunctorTransition (maximalIdeal A) (macaulayFunctor (K := K)) h

/-- On representatives the transition is precomposition, with no chosen
comparison or alternate transition map. -/
theorem macaulayQuotientDualTransition_apply {n m : ℕ} (h : n ≤ m)
    (φ : macaulayQuotientDual (K := K) (A := A) n) (a : A) :
    macaulayQuotientDualEquiv m (macaulayQuotientDualTransition h φ)
        (Ideal.Quotient.mk (maximalIdeal A ^ m) a) =
      macaulayQuotientDualEquiv n φ (Ideal.Quotient.mk (maximalIdeal A ^ n) a) := rfl

/-- The original direct diagram `n ↦ Hom_K(A/m^n,K)`. -/
def macaulayQuotientDualDiagram : ℕ ⥤ ModuleCat.{u} A :=
  supportedFunctorDiagram (maximalIdeal A) (macaulayFunctor (K := K))

@[simp]
theorem macaulayQuotientDualDiagram_map {n m : ℕ} (h : n ≤ m) :
    (macaulayQuotientDualDiagram (K := K) (A := A)).map (homOfLE h) =
      macaulayQuotientDualTransition h := rfl

/-- Macaulay's module is the actual categorical quotient-dual colimit. -/
def macaulayModule : ModuleCat.{u} A :=
  colimit (macaulayQuotientDualDiagram (K := K) (A := A))

/-- The original structural maps into the actual representing module. -/
def macaulayModuleι (n : ℕ) :
    macaulayQuotientDual (K := K) (A := A) n ⟶ macaulayModule (K := K) (A := A) :=
  colimit.ι (macaulayQuotientDualDiagram (K := K) (A := A)) n

/-- Every element of the actual module is represented by a finite quotient dual. -/
theorem macaulayModule_exists_rep (x : macaulayModule (K := K) (A := A)) :
    ∃ n : ℕ, ∃ φ : macaulayQuotientDual (K := K) (A := A) n,
      macaulayModuleι n φ = x :=
  supportedFunctorColimit_exists_rep (maximalIdeal A) (macaulayFunctor (K := K)) x

/-- The quotient-dual colimit is genuinely supported at the closed point. -/
theorem macaulayModule_supported :
    supportedModuleProperty (maximalIdeal A) (macaulayModule (K := K) (A := A)) :=
  supportedFunctorColimit_support (maximalIdeal A) (macaulayFunctor (K := K))

variable [Module.Finite K (ResidueField A)]

/-- **IV.5.2:** the original canonical colimit evaluation represents the
literal field-Hom functor, naturally on all original finite supported modules. -/
def macaulayFunctorRepresentationIso :
    macaulayFunctor (K := K) (A := A) ≅
      supportedModuleHomFunctor (maximalIdeal A) (macaulayModule (K := K)) ⋙
        forget₂ (ModuleCat A) AddCommGrpCat :=
  additiveSupportedFunctorRepresentationIso (maximalIdeal A) (macaulayFunctor (K := K))

/-- The original stage inclusions are injective. -/
theorem macaulayModuleι_injective (n : ℕ) :
    Function.Injective (macaulayModuleι (K := K) (A := A) n) :=
  supportedFunctorColimitι_injective (maximalIdeal A) (macaulayFunctor (K := K)) n

/-- **IV.5.2:** the actual original quotient-dual colimit is supported dualizing. -/
theorem macaulayModule_supportedDualizing :
    SupportedDualizingModule (macaulayModule (K := K) (A := A)) := by
  obtain ⟨hleft, href⟩ := macaulayFunctor_duality (K := K) (A := A)
  have := hleft
  exact ⟨macaulayModule_supported,
    (supportedFunctor_reflexive_iff_homBidual (maximalIdeal A)
      (macaulayFunctor (K := K))).mp href⟩

/-- Every supported module representing the original Macaulay functor is
canonically identified, through that representation, with its actual colimit. -/
def macaulayModuleIsoOfRepresentation (H : ModuleCat.{u} A)
    (hH : supportedModuleProperty (maximalIdeal A) H)
    (e : macaulayFunctor (K := K) (A := A) ≅
      supportedModuleHomFunctor (maximalIdeal A) H ⋙
        forget₂ (ModuleCat A) AddCommGrpCat) : H ≅ macaulayModule (K := K) := by
  let H' : SupportedModuleCat (maximalIdeal A) := ⟨H, hH⟩
  let I' : SupportedModuleCat (maximalIdeal A) :=
    ⟨macaulayModule (K := K), macaulayModule_supported⟩
  let e' : (supportedModuleRestrictedHom (maximalIdeal A)).obj H' ≅
      (supportedModuleRestrictedHom (maximalIdeal A)).obj I' :=
    e.symm ≪≫ macaulayFunctorRepresentationIso
  exact (supportedModuleProperty (maximalIdeal A)).ι.mapIso
    ((supportedModuleRestrictedHomFullyFaithful (maximalIdeal A)).preimageIso e')

end SGA.SGA2.ExposeIV
