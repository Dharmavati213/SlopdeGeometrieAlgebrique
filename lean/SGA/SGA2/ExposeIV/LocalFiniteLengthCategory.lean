/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.NonlocalDualizingFunctor
import SGA.SGA2.ExposeIV.LocalArtinianSupport

/-!
# Local identification of the original finite-length category

For a noetherian local ring, the finite-length category of IV.4.2 is the
same category, up to the explicit identity-on-modules equivalence below,
as the original finite maximal-ideal-supported category of IV.4.1.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

local instance localFiniteLengthResidueField : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
  Ideal.Quotient.field _

/-- A finite-length original module has the actual closed-point support. -/
theorem finiteLengthModule_support (M : FiniteLengthModuleCat R) :
    supportedModuleProperty (IsLocalRing.maximalIdeal R) M.obj :=
  (support_subset_zeroLocus_iff_exists_pow_le_annihilator
    (IsLocalRing.maximalIdeal R) M.obj).mpr
      (finite_artinian_exists_maximalIdeal_pow_annihilator M.obj)

/-- Retain the original module and maps, recording their proved finite support. -/
def finiteLengthToLocalSupported :
    FiniteLengthModuleCat R ⥤ SupportedFGModuleCat (IsLocalRing.maximalIdeal R) where
  obj M := ⟨FGModuleCat.of R M.obj, finiteLengthModule_support R M⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom)

/-- Retain the original supported module, recording its proved finite length. -/
def localSupportedToFiniteLength :
    SupportedFGModuleCat (IsLocalRing.maximalIdeal R) ⥤ FiniteLengthModuleCat R where
  obj M := ⟨M.obj.obj, supportedFinite_isFiniteLength (IsLocalRing.maximalIdeal R) M⟩
  map f := ObjectProperty.homMk f.hom.hom

instance : (finiteLengthToLocalSupported R).Additive where
  map_add := rfl
instance : (finiteLengthToLocalSupported R).Linear R where
  map_smul _ _ := rfl
instance : (localSupportedToFiniteLength R).Additive where
  map_add := rfl
instance : (localSupportedToFiniteLength R).Linear R where
  map_smul _ _ := rfl

/-- The comparison is literally the identity on original underlying modules. -/
theorem finiteLengthToLocalSupported_forget :
    finiteLengthToLocalSupported R ⋙ supportedFiniteToModule (IsLocalRing.maximalIdeal R) =
      finiteLengthInclusion R := rfl

/-- The explicit identity-on-modules local category equivalence. -/
def localFiniteLengthEquivalence :
    FiniteLengthModuleCat R ≌ SupportedFGModuleCat (IsLocalRing.maximalIdeal R) :=
  CategoryTheory.Equivalence.mk (finiteLengthToLocalSupported R) (localSupportedToFiniteLength R)
    (NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Iso.refl _)) (by intros; rfl))
    (NatIso.ofComponents (fun _ => ObjectProperty.isoMk _
      (ObjectProperty.isoMk _ (Iso.refl _))) (by intros; rfl))

instance : (finiteLengthToLocalSupported R).PreservesHomology := by
  change (localFiniteLengthEquivalence R).functor.PreservesHomology
  infer_instance

/-- The local category comparison commutes with the actual Hom dual maps,
not merely with the isomorphism classes of their values. -/
theorem localFiniteLengthHomDual_forget (H : ModuleCat.{u} R) [Injective H]
    (hres : moduleHomDualResidueTests (⊥ : Ideal R) H) :
    (finiteLengthToLocalSupported R).op ⋙
        supportedModuleHomFunctor (IsLocalRing.maximalIdeal R) H =
      finiteLengthHomDual H hres ⋙ finiteLengthInclusion R := rfl

/-- The nonlocal constructed functor gives precisely the local original
abelian-group-valued Hom functor after the identity-on-modules comparison. -/
theorem nonlocalDualizingFunctor_local_forget :
    (finiteLengthToLocalSupported R).op ⋙
        supportedModuleHomFunctor (IsLocalRing.maximalIdeal R) (allResidueFieldEnvelope R).obj =
      nonlocalDualizingFunctor R ⋙ finiteLengthInclusion R := rfl

/-- On a noetherian local ring the constructed Hom functor satisfies the
literal original IV.4.1 dualizing-functor condition. -/
theorem nonlocalDualizingFunctor_local_duality :
    SupportedFunctorDuality (IsLocalRing.maximalIdeal R)
      (supportedModuleHomFunctor (IsLocalRing.maximalIdeal R) (allResidueFieldEnvelope R).obj ⋙
        forget₂ (ModuleCat R) AddCommGrpCat) := by
  let H := (allResidueFieldEnvelope R).obj
  let T := supportedModuleHomFunctor (IsLocalRing.maximalIdeal R) H ⋙
    forget₂ (ModuleCat R) AddCommGrpCat
  have hres : moduleHomDualResidueTests (IsLocalRing.maximalIdeal R) H :=
    fun m hm _ => allResidueFieldEnvelope_residueTests m hm bot_le
  have hexres := (supportedFunctor_exact_residue_iff_injectiveRepresentation
    (IsLocalRing.maximalIdeal R) T).mpr ⟨H, inferInstance, hres, ⟨Iso.refl _⟩⟩
  exact supportedFunctor_duality_of_exact_residue (IsLocalRing.maximalIdeal R) T
    hexres.1 hexres.2

end SGA.SGA2.ExposeIV
