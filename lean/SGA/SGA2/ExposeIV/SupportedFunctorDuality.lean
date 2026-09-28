/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDualityConditions
import SGA.SGA2.ExposeIV.SupportedFunctorBidualNaturality
import SGA.SGA2.ExposeIV.HomDualResidueConverse

/-!
# SGA 2, IV.3.1: the original functor's four equivalent conditions

This is the full original additive abelian-group-valued functor statement.
No representing module, finite values, or left exactness is assumed before
the four conditions: the first condition includes left exactness and
finite values, and uses the actual canonical map into the actual `T(T(M))`.
The remaining conditions use actual exactness, residue values, injective
representations, and length of the original canonically structured values.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

section LeftExact

variable [PreservesFiniteLimits T]

/-- Finiteness of the original functor's values is finiteness of actual
Hom into its proved representing colimit, on every finite supported module. -/
theorem supportedFunctor_finiteValues_iff_homFinite :
    SupportedFunctorFiniteValues J T ↔
      FiniteSupportedHomValues J (supportedFunctorColimit J T) := by
  constructor
  · intro h M hM hSupp
    let S : SupportedFGModuleCat J := ⟨⟨M, hM⟩, hSupp⟩
    have : Module.Finite R (supportedFunctorValue J T S) := h S
    exact Module.Finite.equiv
      ((supportedFunctorRepresentationIso J T).app (op S)).toLinearEquiv
  · intro h M
    have : Module.Finite R
        ((supportedModuleHomFunctor J (supportedFunctorColimit J T)).obj (op M)) :=
      h M.obj.obj inferInstance M.property
    exact Module.Finite.equiv
      ((supportedFunctorRepresentationIso J T).app (op M)).symm.toLinearEquiv

/-- The original canonical twice-iterated-functor maps are invertible iff
the original canonical Hom-bidual maps are, on exactly the same modules. -/
theorem supportedFunctor_reflexive_iff_homBidual :
    SupportedFunctorReflexive J T ↔
      FiniteSupportedHomValues J (supportedFunctorColimit J T) ∧
        SupportedModuleBiduality J (supportedFunctorColimit J T) := by
  constructor
  · rintro ⟨hfin, hbid⟩
    refine ⟨(supportedFunctor_finiteValues_iff_homFinite J T).mp hfin, ?_⟩
    intro M hM hSupp
    let S : SupportedFGModuleCat J := ⟨⟨M, hM⟩, hSupp⟩
    exact (supportedFunctorBidualEvaluation_isIso_iff J T hfin S).mp (hbid S)
  · rintro ⟨hfin, hbid⟩
    let hfinT := (supportedFunctor_finiteValues_iff_homFinite J T).mpr hfin
    refine ⟨hfinT, fun M => ?_⟩
    exact (supportedFunctorBidualEvaluation_isIso_iff J T hfinT M).mpr
      (hbid M.obj.obj inferInstance M.property)

/-- Actual length preservation transfers through the proved canonical
representation, without assuming the original values finite. -/
theorem supportedFunctor_lengthPreserving_iff_homLength :
    SupportedFunctorLengthPreserving J T ↔
      SupportedHomLengthPreserving J (supportedFunctorColimit J T) := by
  constructor
  · intro h M hM hSupp
    let S : SupportedFGModuleCat J := ⟨⟨M, hM⟩, hSupp⟩
    exact ((supportedFunctorRepresentationIso J T).app (op S)).toLinearEquiv.length_eq.symm.trans
      (h S)
  · intro h M
    exact ((supportedFunctorRepresentationIso J T).app (op M)).toLinearEquiv.length_eq.trans
      (h M.obj.obj inferInstance M.property)

end LeftExact

/-- **IV.3.1(i) implies (ii)**. The original canonical reflexivity forces
injectivity of its actual colimit and the original residue tests. -/
theorem supportedFunctor_exact_residue_of_duality
    (h : SupportedFunctorDuality J T) :
    SupportedFunctorExact J T ∧ SupportedFunctorResidueTests J T := by
  obtain ⟨hleft, href⟩ := h
  let := hleft
  obtain ⟨hfin, hbid⟩ := (supportedFunctor_reflexive_iff_homBidual J T).mp href
  have : Injective (supportedFunctorColimit J T) :=
    injective_of_supported_bidually_reflexive J (supportedFunctorColimit J T)
      (supportedFunctorColimit_support J T) hfin hbid
  have hres := moduleHomDualResidueTests_of_supported_bidually_reflexive J
    (supportedFunctorColimit J T) (supportedFunctorColimit_support J T) hfin hbid
  exact ⟨(supportedFunctorExact_iff_injective_colimit J T).mpr inferInstance,
    (supportedFunctorResidueTests_iff_of_representation J T _
      (additiveSupportedFunctorRepresentationIso J T)).mpr hres⟩

/-- **IV.3.1(iv) implies (ii)**. Length-one residue values are the same
residue modules, using their actual annihilator, not just abstract simplicity. -/
theorem supportedFunctor_residue_of_exact_length
    (hex : SupportedFunctorExact J T) (hlen : SupportedFunctorLengthPreserving J T) :
    SupportedFunctorResidueTests J T := by
  have : T.PreservesHomology := (supportedFunctorExact_iff_preservesHomology J T).mp hex
  have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  have hres := moduleHomDualResidueTests_of_length_preserving J (supportedFunctorColimit J T)
    ((supportedFunctor_lengthPreserving_iff_homLength J T).mp hlen)
  exact (supportedFunctorResidueTests_iff_of_representation J T _
    (additiveSupportedFunctorRepresentationIso J T)).mpr hres

/-- **SGA 2, IV.3.1**, all four conditions for the unchanged original
additive functor, including canonical finite-valued biduality. -/
theorem supportedFunctor_duality_tfae [IsArtinianRing (R ⧸ J)] : List.TFAE
    [SupportedFunctorDuality J T,
      SupportedFunctorExact J T ∧ SupportedFunctorResidueTests J T,
      SupportedFunctorInjectiveRepresentation J T,
      SupportedFunctorExact J T ∧ SupportedFunctorLengthPreserving J T] := by
  tfae_have 1 → 2 := supportedFunctor_exact_residue_of_duality J T
  tfae_have 2 → 1 := fun h => supportedFunctor_duality_of_exact_residue J T h.1 h.2
  tfae_have 2 ↔ 3 := supportedFunctor_exact_residue_iff_injectiveRepresentation J T
  tfae_have 2 → 4 := fun h => ⟨h.1, supportedFunctor_length_of_exact_residue J T h.1 h.2⟩
  tfae_have 4 → 2 := fun h => ⟨h.1, supportedFunctor_residue_of_exact_length J T h.1 h.2⟩
  tfae_finish

end SGA.SGA2.ExposeIV
