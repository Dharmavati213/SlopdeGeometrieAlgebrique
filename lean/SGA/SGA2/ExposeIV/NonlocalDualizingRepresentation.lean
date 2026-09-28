/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorRepresentation
import SGA.SGA2.ExposeIV.CofiniteFunctorExactness
import SGA.SGA2.ExposeIV.AdditiveFunctorModuleNaturality
import SGA.SGA2.ExposeIV.SupportedFunctorAnnihilatorStages
import SGA.SGA2.ExposeIV.HomDualResidueConverse
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# IV.4.2: the coefficient of an original nonlocal dualizing functor

An original linear contravariant endofunctor on all finite-length modules,
equipped with a natural involution, is represented by its actual cofinite
quotient colimit. This coefficient is locally Artinian over a noetherian
ring, and its actual annihilator by each maximal ideal has length one.

The supplied natural involution is not asserted to be canonical bidual
evaluation. It gives a genuine anti-equivalence with the original functor
and therefore preserves simple objects. Exactness follows from this
anti-equivalence, so it need not be repeated as an extra hypothesis.
The representing map itself is the previously proved original canonical
cofinite evaluation, with its scalar action identified by `R`-linearity.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Simplicity in the genuine finite-length category is ordinary module
simplicity, since every submodule of a finite-length module has finite length. -/
theorem finiteLength_simple_iff_isSimpleModule (M : FiniteLengthModuleCat R) :
    Simple M ↔ IsSimpleModule R M.obj := by
  constructor
  · intro hM
    have : Simple M := hM
    apply (simple_iff_isSimpleModule' M.obj).mp
    constructor
    intro N f hf
    let N' : FiniteLengthModuleCat R :=
      ⟨N, M.property.of_injective ((ModuleCat.mono_iff_injective f).mp hf)⟩
    let f' : N' ⟶ M := ObjectProperty.homMk f
    have : Mono f' := (finiteLengthInclusion R).mono_of_mono_map hf
    have h := Simple.mono_isIso_iff_nonzero f'
    constructor
    · intro hi hz
      have : IsIso f := hi
      have : IsIso ((finiteLengthInclusion R).map f') := hi
      have : IsIso f' := isIso_of_reflects_iso f' (finiteLengthInclusion R)
      exact h.mp this (by apply ObjectProperty.hom_ext; exact hz)
    · intro hn
      have : IsIso f' := h.mpr (by intro hz; exact hn (congrArg (fun g => g.hom) hz))
      exact inferInstanceAs (IsIso ((finiteLengthInclusion R).map f'))
  · intro hM
    have : Simple ((finiteLengthInclusion R).obj M) :=
      (simple_iff_isSimpleModule' M.obj).mpr hM
    exact (finiteLengthInclusion R).simple_of_simple_obj M

/-- A simple object stays simple on passing to the opposite finite-length
category; this uses the actual abelian category, not a replacement duality. -/
theorem finiteLength_simple_op (M : FiniteLengthModuleCat R) [Simple M] :
    Simple (op M) := by
  constructor
  intro N f hf
  constructor
  · intro hi hz
    have : IsIso f.unop := inferInstance
    have hM := CategoryTheory.id_nonzero M
    apply hM
    have hzero : f.unop = 0 := by rw [hz]; rfl
    calc
      𝟙 M = f.unop ≫ inv f.unop := (IsIso.hom_inv_id f.unop).symm
      _ = 0 := by simp only [hzero, zero_comp]
  · intro hn
    have : IsIso f.unop := isIso_of_epi_of_nonzero (f := f.unop) (by
      intro hz
      apply hn
      apply Quiver.Hom.unop_inj
      exact hz)
    exact (isIso_unop_iff f).mp inferInstance

/-- The actual residue field, viewed in the entire finite-length category. -/
def finiteLengthResidue (m : Ideal R) (hm : m.IsMaximal) : FiniteLengthModuleCat R :=
  ⟨ModuleCat.of R (R ⧸ m), by
    have : IsSimpleModule R (R ⧸ m) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl R _⟩⟩
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩⟩

instance finiteLengthResidue_simple (m : Ideal R) (hm : m.IsMaximal) :
    IsSimpleModule R (finiteLengthResidue m hm).obj :=
  isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl R _⟩⟩

variable (F : (FiniteLengthModuleCat R)ᵒᵖ ⥤ FiniteLengthModuleCat R)
variable [F.Additive] [F.Linear R]

/-- The genuine anti-equivalence retains both original functors. Standard
adjointification supplies coherence; the given involution is not relabelled
as canonical evaluation. -/
def finiteLengthInvolutiveAntiEquivalence
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) :
    (FiniteLengthModuleCat R)ᵒᵖ ≌ FiniteLengthModuleCat R :=
  CategoryTheory.Equivalence.mk F F.rightOp (NatIso.op hself).symm hself.symm

/-- The original underlying abelian-group-valued functor. -/
def nonlocalInvolutiveGroupFunctor : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (F ⋙ finiteLengthInclusion R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat

instance : (nonlocalInvolutiveGroupFunctor F).Additive := by
  unfold nonlocalInvolutiveGroupFunctor
  infer_instance

/-- The representing coefficient is the actual quotient-induced colimit. -/
def nonlocalInvolutiveCoefficient : ModuleCat.{u} R :=
  cofiniteFunctorColimit (nonlocalInvolutiveGroupFunctor F)

omit [F.Linear R] in
/-- The involution already forces exactness of the original functor. -/
theorem finiteLengthInvolutive_preservesHomology
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) : F.PreservesHomology := by
  change (finiteLengthInvolutiveAntiEquivalence F hself).functor.PreservesHomology
  infer_instance

/-- The original abelian-group functor is represented by its genuine cofinite
colimit through the original canonical evaluation. -/
def nonlocalInvolutiveGroupRepresentationIso
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) :
    nonlocalInvolutiveGroupFunctor F ≅
      finiteLengthModuleHomFunctor (nonlocalInvolutiveCoefficient F) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat := by
  have : F.IsEquivalence :=
    inferInstanceAs (finiteLengthInvolutiveAntiEquivalence F hself).functor.IsEquivalence
  have : PreservesFiniteLimits (nonlocalInvolutiveGroupFunctor F) := by
    unfold nonlocalInvolutiveGroupFunctor
    have : PreservesFiniteLimits (F ⋙ finiteLengthInclusion R) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact additiveCofiniteFunctorRepresentationIso (nonlocalInvolutiveGroupFunctor F)

/-- Linearity identifies the original coefficient action with the canonical
source-induced action, without any scalar-compatibility assumption. -/
def nonlocalInvolutiveRepresentationIso
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) :
    F ⋙ finiteLengthInclusion R ≅
      finiteLengthModuleHomFunctor (nonlocalInvolutiveCoefficient F) := by
  have : F.IsEquivalence :=
    inferInstanceAs (finiteLengthInvolutiveAntiEquivalence F hself).functor.IsEquivalence
  have : PreservesFiniteLimits (nonlocalInvolutiveGroupFunctor F) := by
    unfold nonlocalInvolutiveGroupFunctor
    have : PreservesFiniteLimits (F ⋙ finiteLengthInclusion R) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact (linearFunctorModuleLiftForgetIso (F ⋙ finiteLengthInclusion R)).symm ≪≫
    cofiniteFunctorRepresentationIso (nonlocalInvolutiveGroupFunctor F)

@[simp]
theorem nonlocalInvolutiveRepresentationIso_hom_apply
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F)
    (M : FiniteLengthModuleCat R) (x : (F.obj (op M)).obj) :
    ((nonlocalInvolutiveRepresentationIso F hself).hom.app (op M)) x =
      cofiniteFunctorEvaluation (nonlocalInvolutiveGroupFunctor F) M x := rfl

omit [F.Linear R] in
/-- The actual representing colimit is locally Artinian. -/
theorem nonlocalInvolutiveCoefficient_locallyArtinian [IsNoetherianRing R] :
    ModuleLocallyArtinian (R := R) (nonlocalInvolutiveCoefficient F) :=
  cofiniteFunctorColimit_locallyArtinian (nonlocalInvolutiveGroupFunctor F)

omit [F.Linear R] in
/-- The actual representing coefficient is injective among all original
modules, by genuine exactness and the proved nonlocal injectivity criterion. -/
theorem nonlocalInvolutiveCoefficient_injective [IsNoetherianRing R]
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) :
    Injective (nonlocalInvolutiveCoefficient F) := by
  have : F.IsEquivalence :=
    inferInstanceAs (finiteLengthInvolutiveAntiEquivalence F hself).functor.IsEquivalence
  have : PreservesFiniteLimits (nonlocalInvolutiveGroupFunctor F) := by
    unfold nonlocalInvolutiveGroupFunctor
    have : PreservesFiniteLimits (F ⋙ finiteLengthInclusion R) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  apply (cofiniteFunctorExact_iff_injective_colimit (nonlocalInvolutiveGroupFunctor F)).mp
  intro S hS
  exact ((hS.op.map_of_exact F).map_of_exact (finiteLengthInclusion R)).map_of_exact
    (forget₂ (ModuleCat R) AddCommGrpCat)

omit [F.Additive] [F.Linear R] in
/-- Original simple modules are sent to original simple modules. -/
theorem finiteLengthInvolutive_simple
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F)
    (M : FiniteLengthModuleCat R) [IsSimpleModule R M.obj] :
    IsSimpleModule R (F.obj (op M)).obj := by
  have : F.IsEquivalence :=
    inferInstanceAs (finiteLengthInvolutiveAntiEquivalence F hself).functor.IsEquivalence
  have : Simple M := (finiteLength_simple_iff_isSimpleModule M).mpr inferInstance
  have : Simple (op M) := finiteLength_simple_op M
  have : Simple (F.obj (op M)) := simple_obj F (op M)
  exact (finiteLength_simple_iff_isSimpleModule (F.obj (op M))).mp inferInstance

/-- Simplicity of the original residue-field value transfers along the
original module-valued representation, with no assumed residue test. -/
theorem nonlocalInvolutiveCoefficient_residue_simple
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F)
    (m : Ideal R) (hm : m.IsMaximal) :
    IsSimpleModule R ((moduleHomDual (nonlocalInvolutiveCoefficient F)).obj
      (op (ModuleCat.of R (R ⧸ m)))) := by
  have : IsSimpleModule R ((F ⋙ finiteLengthInclusion R).obj
      (op (finiteLengthResidue m hm))) :=
    finiteLengthInvolutive_simple F hself (finiteLengthResidue m hm)
  exact IsSimpleModule.congr
    ((nonlocalInvolutiveRepresentationIso F hself).app
      (op (finiteLengthResidue m hm))).symm.toLinearEquiv

/-- The actual coefficient satisfies every original residue-field Hom test.
The maximal ideal annihilates this Hom module intrinsically, so simplicity
identifies it with the same residue field. -/
theorem nonlocalInvolutiveCoefficient_residueTests
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F) :
    moduleHomDualResidueTests (⊥ : Ideal R) (nonlocalInvolutiveCoefficient F) := by
  intro m hm _
  have := nonlocalInvolutiveCoefficient_residue_simple F hself m hm
  exact simpleModule_iso_residue_of_annihilator m hm _
    (moduleHomDual_residue_annihilator (nonlocalInvolutiveCoefficient F) m)

/-- The actual maximal-ideal annihilator of the original representing
colimit is one copy of the same residue field. -/
def nonlocalInvolutiveAnnihilatorIso
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F)
    (m : Ideal R) (hm : m.IsMaximal) :
    ModuleCat.of R (Submodule.torsionBySet R (nonlocalInvolutiveCoefficient F)
      (m : Set R)) ≅ ModuleCat.of R (R ⧸ m) :=
  (quotientHomAnnihilatorIso m (nonlocalInvolutiveCoefficient F)).symm ≪≫
    (nonlocalInvolutiveCoefficient_residueTests F hself m hm bot_le).some

/-- **IV.4.2:** every actual maximal-ideal annihilator of the original
representing module has length exactly one. -/
theorem nonlocalInvolutiveAnnihilator_length
    (hself : 𝟭 (FiniteLengthModuleCat R) ≅ F.rightOp ⋙ F)
    (m : Ideal R) (hm : m.IsMaximal) :
    Module.length R
      (Submodule.torsionBySet R (nonlocalInvolutiveCoefficient F) (m : Set R)) = 1 := by
  rw [(nonlocalInvolutiveAnnihilatorIso F hself m hm).toLinearEquiv.length_eq]
  have : IsSimpleModule R (R ⧸ m) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl R _⟩⟩
  exact Module.length_eq_one R (R ⧸ m)

end SGA.SGA2.ExposeIV
