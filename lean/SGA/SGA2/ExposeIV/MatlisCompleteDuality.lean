/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisCategories
import SGA.SGA2.ExposeIV.MatlisBidualCompletion
import SGA.SGA2.ExposeIV.MatlisDualComplete
import SGA.SGA2.ExposeIV.SupportedHomCogenerator

/-!
# IV.5.1 over a complete noetherian local base

The actual Hom functor exchanges finite modules with locally Artinian
modules of finite socle. Both canonical original bidual evaluations are
natural isomorphisms. They yield the genuine anti-equivalence, retaining
the actual Hom module and precomposition maps in both directions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

/-- Actual Hom sends every finite module into the literal category `CA`. -/
def matlisFiniteHom : (FGModuleCat.{u} R)ᵒᵖ ⥤ MatlisArtinianModuleCat R where
  obj M := ⟨(moduleHomDual H).obj (op M.unop.obj),
    hH.finiteSource_dual_locallyArtinian_finiteSocle M.unop.obj⟩
  map f := ObjectProperty.homMk ((moduleHomDual H).map f.unop.hom.op)
  map_id M := by apply ObjectProperty.hom_ext; exact (moduleHomDual H).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; ext x; rfl

instance : (matlisFiniteHom H hH).Additive where
  map_add {X Y f g} := by
    apply ObjectProperty.hom_ext
    exact (moduleHomDual H).map_add (f := f.unop.hom.op) (g := g.unop.hom.op)

instance : (matlisFiniteHom H hH).Linear R where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul r (f.unop.hom.hom x)

/-- Forgetting the target property leaves the original Hom functor exactly. -/
theorem matlisFiniteHom_forget :
    matlisFiniteHom H hH ⋙ (matlisArtinianModuleProperty R).ι =
      (ModuleCat.isFG R).ι.op ⋙ moduleHomDual H := rfl

include hH in
/-- Over the original possibly noncomplete ring, the actual dual of every
`CA` object satisfies both defining conditions of `DA`. -/
theorem matlisArtinianHom_completeProperty (X : MatlisArtinianModuleCat R) :
    matlisCompleteModuleProperty R ((moduleHomDual H).obj (op X.obj)) := by
  have := X.property.2
  refine ⟨fun n => ?_, hH.supported_dual_isAdicComplete X.obj X.supported⟩
  have := hH.finiteSocle_dual_powerQuotient_finite X.obj X.supported (n + 1)
  exact finite_supported_isFiniteLength_of_fg
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing _
    (finiteSource_powerQuotient_supported (IsLocalRing.maximalIdeal R)
      ((moduleHomDual H).obj (op X.obj)) (n + 1))

/-- The first original Hom functor of IV.5.1, over any noetherian local ring. -/
def matlisHomToComplete : (MatlisArtinianModuleCat R)ᵒᵖ ⥤ MatlisCompleteModuleCat R where
  obj X := ⟨(moduleHomDual H).obj (op X.unop.obj),
    matlisArtinianHom_completeProperty H hH X.unop⟩
  map f := ObjectProperty.homMk ((moduleHomDual H).map f.unop.hom.op)
  map_id X := by apply ObjectProperty.hom_ext; exact (moduleHomDual H).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; ext x; rfl

theorem matlisHomToComplete_forget :
    matlisHomToComplete H hH ⋙ (matlisCompleteModuleProperty R).ι =
      (matlisArtinianModuleProperty R).ι.op ⋙ moduleHomDual H := rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

include hH in
/-- Canonical finite-module reflexivity follows from completeness, not from
an additional hypothesis of reflexivity of finite non-supported modules. -/
theorem SupportedDualizingModule.finite_moduleBidualEvaluation_isIso
    (M : ModuleCat.{u} R) [Module.Finite R M] : IsIso (moduleBidualEvaluation H M) :=
  (finiteBidualEvaluation_isIso_iff_isAdicComplete
    (IsLocalRing.maximalIdeal R) H M hH.1 hH.2.2).mpr
      (isAdicComplete_of_finite (IsLocalRing.maximalIdeal R) M)

include hH in
/-- Canonical reflexivity on `CA` follows from finite reflexivity of its
actual dual and the proved all-module Hom cogenerator property. -/
theorem SupportedDualizingModule.matlisArtinian_moduleBidualEvaluation_isIso
    (X : MatlisArtinianModuleCat R) : IsIso (moduleBidualEvaluation H X.obj) := by
  have := X.property.2
  have := hH.supported_finiteSocle_dual_finite X.obj X.supported
  have := hH.finite_moduleBidualEvaluation_isIso H ((moduleHomDual H).obj (op X.obj))
  exact hH.moduleBidualEvaluation_isIso_of_dual X.obj

/-- Actual Hom from `CA` to finite modules over the complete base. -/
def matlisArtinianHom : (MatlisArtinianModuleCat R)ᵒᵖ ⥤ FGModuleCat.{u} R where
  obj X := by
    have := X.unop.property.2
    have := hH.supported_finiteSocle_dual_finite X.unop.obj X.unop.supported
    exact FGModuleCat.of R ((moduleHomDual H).obj (op X.unop.obj))
  map f := ObjectProperty.homMk ((moduleHomDual H).map f.unop.hom.op)
  map_id X := by apply ObjectProperty.hom_ext; exact (moduleHomDual H).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; ext x; rfl

instance : (matlisArtinianHom H hH).Additive where
  map_add {X Y f g} := by
    apply ObjectProperty.hom_ext
    exact (moduleHomDual H).map_add (f := f.unop.hom.op) (g := g.unop.hom.op)

instance : (matlisArtinianHom H hH).Linear R where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul r (f.unop.hom.hom x)

/-- The other inclusion square also commutes on the original modules and maps. -/
theorem matlisArtinianHom_forget :
    matlisArtinianHom H hH ⋙ (ModuleCat.isFG R).ι =
      (matlisArtinianModuleProperty R).ι.op ⋙ moduleHomDual H := rfl

/-- The original finite-module evaluation as a natural isomorphism. -/
def matlisFiniteEvaluationIso :
    𝟭 (FGModuleCat.{u} R) ≅ (matlisFiniteHom H hH).rightOp ⋙ matlisArtinianHom H hH := by
  have (M : FGModuleCat.{u} R) : IsIso (moduleBidualEvaluation H M.obj) :=
    hH.finite_moduleBidualEvaluation_isIso H M.obj
  exact NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ (asIso (moduleBidualEvaluation H M.obj)))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact moduleBidualEvaluation_naturality H f.hom)

/-- The original `CA`-module evaluation as a natural isomorphism. -/
def matlisArtinianEvaluationIso :
    𝟭 (MatlisArtinianModuleCat R) ≅
      (matlisArtinianHom H hH).rightOp ⋙ matlisFiniteHom H hH := by
  have (X : MatlisArtinianModuleCat R) : IsIso (moduleBidualEvaluation H X.obj) :=
    hH.matlisArtinian_moduleBidualEvaluation_isIso H X
  exact NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (asIso (moduleBidualEvaluation H X.obj)))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact moduleBidualEvaluation_naturality H f.hom)

@[simp] theorem matlisFiniteEvaluationIso_hom (M : FGModuleCat.{u} R) :
    ((matlisFiniteEvaluationIso H hH).hom.app M).hom = moduleBidualEvaluation H M.obj := rfl

@[simp] theorem matlisArtinianEvaluationIso_hom (X : MatlisArtinianModuleCat R) :
    ((matlisArtinianEvaluationIso H hH).hom.app X).hom = moduleBidualEvaluation H X.obj := rfl

/-- **IV.5.1, complete-base formulation.** The two actual linear Hom
functors are quasi-inverse. Standard adjointification keeps both functors
and the inverse canonical finite-module evaluation counit unchanged. -/
def matlisCompleteAntiEquivalence : (MatlisArtinianModuleCat R)ᵒᵖ ≌ FGModuleCat.{u} R :=
  CategoryTheory.Equivalence.mk (matlisArtinianHom H hH) (matlisFiniteHom H hH).rightOp
    (NatIso.op (matlisArtinianEvaluationIso H hH)).symm
    (matlisFiniteEvaluationIso H hH).symm

/-- The same actual duality with the literal complete category `DA`. -/
def matlisCompleteCategoryAntiEquivalence :
    (MatlisArtinianModuleCat R)ᵒᵖ ≌ MatlisCompleteModuleCat R :=
  (matlisCompleteAntiEquivalence H hH).trans matlisCompleteFiniteEquivalence.symm

/-- Even after identifying finite modules with `DA`, the forward functor
is precisely the original Hom functor constructed over the original ring. -/
@[simp] theorem matlisCompleteCategoryAntiEquivalence_functor :
    (matlisCompleteCategoryAntiEquivalence H hH).functor = matlisHomToComplete H hH := rfl

/-- Adjointification leaves inverse canonical evaluation as the counit. -/
@[simp] theorem matlisCompleteAntiEquivalence_counitInv (M : FGModuleCat.{u} R) :
    ((matlisCompleteAntiEquivalence H hH).counitIso.inv.app M).hom =
      moduleBidualEvaluation H M.obj := rfl

instance : PreservesFiniteLimits (matlisArtinianHom H hH) := by
  change PreservesFiniteLimits (matlisCompleteAntiEquivalence H hH).functor
  infer_instance

instance : PreservesFiniteColimits (matlisArtinianHom H hH) := by
  change PreservesFiniteColimits (matlisCompleteAntiEquivalence H hH).functor
  infer_instance

end SGA.SGA2.ExposeIV
