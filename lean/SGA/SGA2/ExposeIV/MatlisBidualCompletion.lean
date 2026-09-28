/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisFiniteDual
import SGA.SGA2.ExposeIV.SupportedAnnihilatorColimit
import SGA.SGA2.ExposeIV.AdicQuotientLimit

/-!
# The actual bidual of a finite module is its adic completion

Original finite supported reflexivity is applied only to the actual power
quotients. Their duals are exactly the annihilators in the original dual.
Taking Hom of the genuine annihilator colimit gives an inverse limit,
identified with mathlib's actual adic completion. The final comparison sends
the canonical bidual evaluation to the original completion map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (J : Ideal R) (H M : ModuleCat.{u} R)

/-- Dualizing the original quotient diagram gives the literal annihilator
filtration in the original Hom module, including its inclusion maps. -/
def dualQuotientAnnihilatorDiagramIso :
    (adicQuotientDiagram J M).rightOp ⋙ moduleHomDual H ≅
      annihilatorFiltration J ((moduleHomDual H).obj (op M)) :=
  NatIso.ofComponents (fun n => quotientHomIdealAnnihilatorIso (J ^ n) H M)
    (fun {n m} f => by
      apply ModuleCat.hom_ext
      ext g
      apply Subtype.ext
      apply ModuleCat.hom_ext
      ext x
      change ModuleCat.Hom.hom
          ((quotientHomIdealAnnihilatorIso (J ^ m) H M).hom
            ((moduleHomDual H).map ((adicQuotientDiagram J M).map f.op).op g)).val x =
        ModuleCat.Hom.hom ((quotientHomIdealAnnihilatorIso (J ^ n) H M).hom g).val x
      rw [quotientHomIdealAnnihilatorIso_apply, quotientHomIdealAnnihilatorIso_apply]
      rfl)

variable [IsNoetherianRing R] [Module.Finite R M]

local instance matlisQuotientFinite (n : ℕᵒᵖ) :
    Module.Finite R ((adicQuotientDiagram J M).obj n) :=
  inferInstanceAs (Module.Finite R (M ⧸ (J ^ n.unop • (⊤ : Submodule R M))))

/-- Canonical original bidual evaluation is an isomorphism on every actual
power quotient of a finite module. -/
def adicQuotientBidualEvaluationIso (hbid : SupportedModuleBiduality J H) :
    adicQuotientDiagram J M ≅ adicQuotientDiagram J M ⋙ moduleHomBidual H := by
  haveI (n : ℕᵒᵖ) : IsIso (moduleBidualEvaluation H ((adicQuotientDiagram J M).obj n)) :=
    hbid _ inferInstance (finiteSource_powerQuotient_supported J M n.unop)
  exact NatIso.ofComponents (fun n => asIso (moduleBidualEvaluation H
    ((adicQuotientDiagram J M).obj n))) (fun f => moduleBidualEvaluation_naturality H _)

/-- Dualizing the original annihilator diagram and then applying original
finite-quotient reflexivity gives the original quotient diagram itself. -/
def annihilatorDualQuotientDiagramIso (hbid : SupportedModuleBiduality J H) :
    (annihilatorFiltration J ((moduleHomDual H).obj (op M))).op ⋙ moduleHomDual H ≅
      adicQuotientDiagram J M :=
  Functor.isoWhiskerRight (NatIso.op (dualQuotientAnnihilatorDiagramIso J H M)) (moduleHomDual H) ≪≫
    (adicQuotientBidualEvaluationIso J H M hbid).symm

/-- The bidual with its actual restriction-and-evaluation projections is a
cone on the original quotient diagram. -/
def finiteBidualQuotientCone (hbid : SupportedModuleBiduality J H) :
    Cone (adicQuotientDiagram J M) :=
  (Cone.postcompose (annihilatorDualQuotientDiagramIso J H M hbid).hom).obj
    ((moduleHomDual H).mapCone
      (annihilatorFiltrationCocone J ((moduleHomDual H).obj (op M))).op)

/-- Original Hom sends the actual annihilator colimit to this actual limit. -/
def finiteBidualQuotientConeIsLimit (hH : supportedModuleProperty J H)
    (hbid : SupportedModuleBiduality J H) : IsLimit (finiteBidualQuotientCone J H M hbid) :=
  (IsLimit.postcomposeHomEquiv (annihilatorDualQuotientDiagramIso J H M hbid) _).symm
    (annihilatorHomIsLimit J ((moduleHomDual H).obj (op M)) H
      ((powerTorsion_eq_top_iff_support_of_fg J J.fg_of_isNoetherianRing _).mpr
        (finiteSource_moduleHomDual_supported J H M hH)))

/-- The actual Hom bidual of a finite module is its actual adic completion. -/
def finiteBidualCompletionIso (hH : supportedModuleProperty J H)
    (hbid : SupportedModuleBiduality J H) :
    (moduleHomBidual H).obj M ≅ ModuleCat.of R (AdicCompletion J M) :=
  (finiteBidualQuotientConeIsLimit J H M hH hbid).conePointUniqueUpToIso
    (adicCompletionConeIsLimit J M)

omit [IsNoetherianRing R] in
/-- The actual cone projection recovers the original quotient map when
composed with canonical bidual evaluation. -/
@[reassoc] theorem finiteBidualQuotientCone_evaluation
    (hbid : SupportedModuleBiduality J H) (n : ℕᵒᵖ) :
    moduleBidualEvaluation H M ≫ (finiteBidualQuotientCone J H M hbid).π.app n =
      (adicQuotientProjection J M).app n := by
  let Q := (adicQuotientDiagram J M).obj n
  have : IsIso (moduleBidualEvaluation H Q) :=
    hbid Q inferInstance (finiteSource_powerQuotient_supported J M n.unop)
  let A := Submodule.torsionBySet R ((moduleHomDual H).obj (op M)) (J ^ n.unop : Ideal R)
  let j : ModuleCat.of R A ⟶ (moduleHomDual H).obj (op M) := ModuleCat.ofHom A.subtype
  let e := quotientHomIdealAnnihilatorIso (J ^ n.unop) H M
  have hc : moduleBidualEvaluation H M ≫
        ((moduleHomDual H).map j.op ≫ (moduleHomDual H).map e.hom.op) =
      (adicQuotientProjection J M).app n ≫ moduleBidualEvaluation H Q := by
    apply ModuleCat.hom_ext
    ext x
    apply ModuleCat.hom_ext
    ext g
    rfl
  change moduleBidualEvaluation H M ≫
    ((moduleHomDual H).map j.op ≫
      ((moduleHomDual H).map e.hom.op ≫ inv (moduleBidualEvaluation H Q))) = _
  rw [← Category.assoc ((moduleHomDual H).map j.op), ← Category.assoc, hc,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Canonical comparison:** the original double-Hom evaluation becomes
the original adic completion map under the specified isomorphism. -/
@[reassoc] theorem finiteBidualCompletionIso_evaluation
    (hH : supportedModuleProperty J H) (hbid : SupportedModuleBiduality J H) :
    moduleBidualEvaluation H M ≫ (finiteBidualCompletionIso J H M hH hbid).hom =
      ModuleCat.ofHom (AdicCompletion.of J M) := by
  apply (adicCompletionConeIsLimit J M).hom_ext
  intro n
  rw [Category.assoc, finiteBidualCompletionIso,
    IsLimit.conePointUniqueUpToIso_hom_comp, finiteBidualQuotientCone_evaluation]
  rfl

/-- Original finite-module canonical reflexivity is exactly actual adic completeness. -/
theorem finiteBidualEvaluation_isIso_iff_isAdicComplete
    (hH : supportedModuleProperty J H) (hbid : SupportedModuleBiduality J H) :
    IsIso (moduleBidualEvaluation H M) ↔ IsAdicComplete J M := by
  have hcomp := finiteBidualCompletionIso_evaluation J H M hH hbid
  constructor
  · intro h
    have : IsIso (ModuleCat.ofHom (AdicCompletion.of J M)) := by
      rw [← hcomp]
      infer_instance
    exact AdicCompletion.of_bijective_iff.mp
      ((ConcreteCategory.isIso_iff_bijective _).mp this)
  · intro h
    have : IsIso (ModuleCat.ofHom (AdicCompletion.of J M)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (AdicCompletion.of_bijective J M)
    have : IsIso (moduleBidualEvaluation H M ≫ (finiteBidualCompletionIso J H M hH hbid).hom) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (finiteBidualCompletionIso J H M hH hbid).hom

end SGA.SGA2.ExposeIV
