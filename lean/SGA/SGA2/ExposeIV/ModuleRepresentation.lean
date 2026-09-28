/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ModuleEvaluation
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation
import SGA.SGA2.ExposeIV.FiniteSubmoduleColimit

/-!
# Representation on arbitrary modules

IV.1.2: canonical evaluation is an isomorphism if and only if the
contravariant additive functor preserves all small limits. The forward
construction uses the actual filtered colimit of finite submodules,
not an assumed representation or an assumed presentation.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

/-- An isomorphism on every object of a diagram is an isomorphism at its
limit when both original functors preserve that limit. -/
theorem isIso_app_conePt_of_preservesLimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (K : J ⥤ C) {L L' : C ⥤ D} (α : L ⟶ L') [IsIso (whiskerLeft K α)]
    (c : Cone K) (hc : IsLimit c) [PreservesLimit K L] [PreservesLimit K L'] :
    IsIso (α.app c.pt) := by
  let e := IsLimit.conePointsIsoOfNatIso
    (isLimitOfPreserves L hc) (isLimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  have he : e.hom = α.app c.pt := by
    apply (isLimitOfPreserves L' hc).hom_ext
    intro j
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ j).trans
      (α.naturality (c.π.app j))
  rw [← he]
  infer_instance

variable {R : Type u} [CommRing R]

variable (T : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R) [T.Additive] [T.Linear R]

/-- On a finite module, the all-module evaluation is exactly IV.1.1. -/
theorem moduleEvaluation_finite_isIso [IsNoetherianRing R] [PreservesFiniteLimits T]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsIso ((moduleEvaluationNatTrans T).app (op M)) := by
  let i := (forget₂ (FGModuleCat R) (ModuleCat R)).op
  have : PreservesFiniteLimits i := preservesFiniteLimits_op _
  have : PreservesFiniteLimits (i ⋙ T) := comp_preservesFiniteLimits _ _
  change IsIso ((finiteModuleEvaluationNatTrans (i ⋙ T)).app (op (FGModuleCat.of R M)))
  infer_instance

/-- The actual limit over finite submodules transports the finite-module
isomorphisms to canonical evaluation on an arbitrary module. -/
instance [IsNoetherianRing R] [PreservesLimits T] : IsIso (moduleEvaluationNatTrans T) := by
  have (M : (ModuleCat.{u} R)ᵒᵖ) : IsIso ((moduleEvaluationNatTrans T).app M) := by
    let K := (finiteSubmoduleDiagram M.unop).op
    have : PreservesLimitsOfSize.{0, u} T :=
      preservesLimitsOfSize_of_univLE.{u, u, 0, u} T
    have : PreservesLimitsOfSize.{0, u}
        ((linearYoneda R (ModuleCat R)).obj (T.obj (op (ModuleCat.of R R)))) :=
      preservesLimitsOfSize_of_univLE.{u, u, 0, u} _
    have (P : (FiniteSubmoduleIndex M.unop)ᵒᵖ) :
        IsIso ((whiskerLeft K (moduleEvaluationNatTrans T)).app P) :=
      moduleEvaluation_finite_isIso T (ModuleCat.of R P.unop.val)
    have : IsIso (whiskerLeft K (moduleEvaluationNatTrans T)) :=
      NatIso.isIso_of_isIso_app _
    exact isIso_app_conePt_of_preservesLimit K (moduleEvaluationNatTrans T)
      (finiteSubmoduleCocone M.unop).op (finiteSubmoduleCoconeIsColimit M.unop).op
  exact NatIso.isIso_of_isIso_app _

/-- IV.1.2 with the specified canonical map and the actual value on the ring. -/
theorem moduleEvaluation_isIso_iff [IsNoetherianRing R] :
    IsIso (moduleEvaluationNatTrans T) ↔ PreservesLimits T := by
  constructor
  · intro h
    exact preservesLimits_of_natIso (asIso (moduleEvaluationNatTrans T)).symm
  · intro h
    infer_instance

def moduleRepresentationIso [IsNoetherianRing R] [PreservesLimits T] :
    T ≅ (linearYoneda R (ModuleCat R)).obj (T.obj (op (ModuleCat.of R R))) :=
  asIso (moduleEvaluationNatTrans T)

section AbelianGroupValued

variable (A : (ModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [A.Additive]

/-- The canonical scalar lift preserves limits of the original functor. -/
instance [PreservesLimits A] : PreservesLimits (additiveFunctorModuleLift (R := R) A) := by
  have : PreservesLimits
      (additiveFunctorModuleLift (R := R) A ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    preservesLimits_of_natIso (additiveFunctorModuleLiftForgetIso (R := R) A).symm
  exact preservesLimits_of_reflects_of_preserves _ (forget₂ (ModuleCat R) AddCommGrpCat)

/-- The original abelian-group-valued functor's evaluation; scalar structure
is induced, not added as a hypothesis. -/
def additiveModuleEvaluationNatTrans : A ⟶
    (linearYoneda R (ModuleCat R)).obj
      ((additiveFunctorModuleLift (R := R) A).obj (op (ModuleCat.of R R))) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat :=
  (additiveFunctorModuleLiftForgetIso (R := R) A).inv ≫
    whiskerRight (moduleEvaluationNatTrans (additiveFunctorModuleLift (R := R) A))
      (forget₂ (ModuleCat R) AddCommGrpCat)

/-- SGA 2, IV.1.2: the original additive functor is canonically represented
precisely when it preserves all small limits. -/
theorem additiveModuleEvaluation_isIso_iff [IsNoetherianRing R] :
    IsIso (additiveModuleEvaluationNatTrans A) ↔ PreservesLimits A := by
  constructor
  · intro h
    exact preservesLimits_of_natIso (asIso (additiveModuleEvaluationNatTrans A)).symm
  · intro h
    unfold additiveModuleEvaluationNatTrans
    infer_instance

/-- Representation by the original functor's canonically structured value on `R`. -/
def additiveModuleRepresentationIso [IsNoetherianRing R] [PreservesLimits A] :
    A ≅ (linearYoneda R (ModuleCat R)).obj
      ((additiveFunctorModuleLift (R := R) A).obj (op (ModuleCat.of R R))) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat := by
  letI := (additiveModuleEvaluation_isIso_iff A).mpr inferInstance
  exact asIso (additiveModuleEvaluationNatTrans A)

/-- Abstract representability is equivalent to the same limit criterion. -/
theorem additiveModule_representable_iff [IsNoetherianRing R] :
    (∃ H : ModuleCat.{u} R,
      Nonempty (A ≅ (linearYoneda R (ModuleCat R)).obj H ⋙
        forget₂ (ModuleCat R) AddCommGrpCat)) ↔ PreservesLimits A := by
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    exact preservesLimits_of_natIso e.symm
  · intro h
    exact ⟨_, ⟨additiveModuleRepresentationIso A⟩⟩

end AbelianGroupValued

end SGA.SGA2.ExposeIV
