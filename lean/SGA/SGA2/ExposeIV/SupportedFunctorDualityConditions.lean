/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDual
import SGA.SGA2.ExposeIV.SupportedArtinianDuality

/-!
# The original functor conditions of IV.3.1

The four conditions are formulated for the original additive functor into
abelian groups, with its canonical scalar action and actual twice-iterated
functor. Representation comparisons are actual natural isomorphisms, not
additional hypotheses. This file proves (ii) iff (iii), and the forward
implications to finite canonical biduality and length preservation.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual quotient residue module with its derived support property. -/
def supportedResidueField (J m : Ideal R) (hJ : J ≤ m) : SupportedFGModuleCat J :=
  ⟨FGModuleCat.of R (R ⧸ m),
    (support_subset_zeroLocus_iff_exists_pow_le_annihilator J (R ⧸ m)).mpr
      ⟨1, by simpa only [pow_one, Ideal.annihilator_quotient] using hJ⟩⟩

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The source's tests on the original canonically structured `T(k)`. -/
def SupportedFunctorResidueTests : Prop :=
  ∀ m : Ideal R, m.IsMaximal → ∀ hJ : J ≤ m,
    Nonempty (supportedFunctorValue J T (supportedResidueField J m hJ) ≅
      ModuleCat.of R (R ⧸ m))

/-- Length preservation refers to the original values, not to assumed
finite objects or chosen replacements. -/
def SupportedFunctorLengthPreserving : Prop :=
  ∀ M : SupportedFGModuleCat J,
    Module.length R (supportedFunctorValue J T M) = Module.length R M.obj

/-- IV.3.1(i), including the original left-exactness requirement. -/
def SupportedFunctorDuality : Prop :=
  ∃ hleft : PreservesFiniteLimits T, letI := hleft; SupportedFunctorReflexive J T

/-- IV.3.1(iii): a genuine representation by an injective coefficient
with the specified residue-field tests. No support hypothesis on `H` is added. -/
def SupportedFunctorInjectiveRepresentation : Prop :=
  ∃ H : ModuleCat.{u} R, Injective H ∧ moduleHomDualResidueTests J H ∧
    Nonempty (T ≅ supportedModuleHomFunctor J H ⋙ forget₂ (ModuleCat R) AddCommGrpCat)

/-- Any original representation is automatically linear for its canonical action. -/
def supportedFunctorValueIsoOfRepresentation (H : ModuleCat.{u} R)
    (e : T ≅ supportedModuleHomFunctor J H ⋙ forget₂ (ModuleCat R) AddCommGrpCat)
    (M : SupportedFGModuleCat J) :
    supportedFunctorValue J T M ≅ (moduleHomDual H).obj (op M.obj.obj) :=
  (additiveFunctorModuleRepresentationIso (supportedModuleHomFunctor J H) e).app (op M)

/-- Residue tests transfer through actual original representations. -/
theorem supportedFunctorResidueTests_iff_of_representation (H : ModuleCat.{u} R)
    (e : T ≅ supportedModuleHomFunctor J H ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :
    SupportedFunctorResidueTests J T ↔ moduleHomDualResidueTests J H := by
  constructor
  · intro h m hm hJ
    exact ⟨(supportedFunctorValueIsoOfRepresentation J T H e
      (supportedResidueField J m hJ)).symm ≪≫ (h m hm hJ).some⟩
  · intro h m hm hJ
    exact ⟨supportedFunctorValueIsoOfRepresentation J T H e
      (supportedResidueField J m hJ) ≪≫ (h m hm hJ).some⟩

/-- **IV.3.1(ii) iff (iii)** for the original additive functor, with no
prior left-exactness or representing-module hypothesis. -/
theorem supportedFunctor_exact_residue_iff_injectiveRepresentation :
    (SupportedFunctorExact J T ∧ SupportedFunctorResidueTests J T) ↔
      SupportedFunctorInjectiveRepresentation J T := by
  constructor
  · rintro ⟨hex, hres⟩
    have : T.PreservesHomology := (supportedFunctorExact_iff_preservesHomology J T).mp hex
    have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
    refine ⟨supportedFunctorColimit J T,
      (supportedFunctorExact_iff_injective_colimit J T).mp hex, ?_,
      ⟨additiveSupportedFunctorRepresentationIso J T⟩⟩
    exact (supportedFunctorResidueTests_iff_of_representation J T _
      (additiveSupportedFunctorRepresentationIso J T)).mp hres
  · rintro ⟨H, hH, hres, ⟨e⟩⟩
    have := hH
    refine ⟨?_, (supportedFunctorResidueTests_iff_of_representation J T H e).mpr hres⟩
    apply (supportedFunctorExact_iff_of_iso J e).mpr
    apply (supportedHomFunctorExact_iff J H).mpr
    intro S _ _ hS
    exact (moduleHomDual_shortExact H hS).map_of_exact (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Finiteness of the original values follows from exactness and the
residue tests under the original Artinian-support hypothesis. -/
theorem supportedFunctor_finiteValues_of_exact_residue [IsArtinianRing (R ⧸ J)]
    (hex : SupportedFunctorExact J T) (hres : SupportedFunctorResidueTests J T) :
    SupportedFunctorFiniteValues J T := by
  have : T.PreservesHomology := (supportedFunctorExact_iff_preservesHomology J T).mp hex
  have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  have : Injective (supportedFunctorColimit J T) :=
    (supportedFunctorExact_iff_injective_colimit J T).mp hex
  have hH := (supportedFunctorResidueTests_iff_of_representation J T _
    (additiveSupportedFunctorRepresentationIso J T)).mp hres
  intro M
  have : Module.Finite R ((supportedModuleHomFunctor J (supportedFunctorColimit J T)).obj (op M)) :=
    moduleHomDual_finite_of_artinian_support J (supportedFunctorColimit J T) hH M.obj.obj M.property
  exact Module.Finite.equiv ((supportedFunctorRepresentationIso J T).app (op M)).symm.toLinearEquiv

/-- **IV.3.1(ii) implies (i)** with the actual canonical map into `T(T(M))`. -/
theorem supportedFunctor_duality_of_exact_residue [IsArtinianRing (R ⧸ J)]
    (hex : SupportedFunctorExact J T) (hres : SupportedFunctorResidueTests J T) :
    SupportedFunctorDuality J T := by
  have : T.PreservesHomology := (supportedFunctorExact_iff_preservesHomology J T).mp hex
  have hleft : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  have : Injective (supportedFunctorColimit J T) :=
    (supportedFunctorExact_iff_injective_colimit J T).mp hex
  have hH := (supportedFunctorResidueTests_iff_of_representation J T _
    (additiveSupportedFunctorRepresentationIso J T)).mp hres
  let hfin := supportedFunctor_finiteValues_of_exact_residue J T hex hres
  refine ⟨hleft, hfin, fun M => ?_⟩
  exact (supportedFunctorBidualEvaluation_isIso_iff J T hfin M).mpr
    (moduleBidualEvaluation_isIso_of_artinian_support J (supportedFunctorColimit J T)
      hH M.obj.obj M.property)

/-- **IV.3.1(ii) implies (iv)**: length equality is proved for the actual
canonically structured values of the original functor. -/
theorem supportedFunctor_length_of_exact_residue [IsArtinianRing (R ⧸ J)]
    (hex : SupportedFunctorExact J T) (hres : SupportedFunctorResidueTests J T) :
    SupportedFunctorLengthPreserving J T := by
  have : T.PreservesHomology := (supportedFunctorExact_iff_preservesHomology J T).mp hex
  have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  have : Injective (supportedFunctorColimit J T) :=
    (supportedFunctorExact_iff_injective_colimit J T).mp hex
  have hH := (supportedFunctorResidueTests_iff_of_representation J T _
    (additiveSupportedFunctorRepresentationIso J T)).mp hres
  intro M
  exact ((supportedFunctorRepresentationIso J T).app (op M)).toLinearEquiv.length_eq.trans
    (moduleHomDual_length_of_artinian_support J (supportedFunctorColimit J T)
      hH M.obj.obj M.property)

end SGA.SGA2.ExposeIV
