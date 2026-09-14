/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisCompletedRingDuality

/-!
# The completed-ring Matlis equivalence retains the original Hom functor

Restriction of completed-ring Hom, precomposition with the original source
tensor unit, and postcomposition with the inverse coefficient tensor unit
give the comparison with the original base-ring Hom module. Its inverse is
the actual tensor-extension map on morphisms. Both source and coefficient
naturality are retained, and the final natural isomorphism compares the
actual forward equivalence functor with original Hom on `CA`.
-/

noncomputable section
universe u
open CategoryTheory Opposite ModuleCat TensorProduct

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

/-- The original completed-ring Hom comparison for an arbitrary supported
source, assembled entirely from actual scalar-change maps. -/
def matlisCompletedHomObjectIso (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X) :
    (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj
      ((moduleHomDual (matlisCompletedCoefficient H)).obj
        (op ((extendScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X))) ≅
      (moduleHomDual H).obj (op X) := by
  let m := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion m R)
  letI := completion_unit_isIso m X hX
  exact completionHomDualIso m ((extendScalars f).obj H) ((extendScalars f).obj X)
      (supported_extendScalars f m m.fg_of_isNoetherianRing H hH.1)
      (supported_extendScalars f m m.fg_of_isNoetherianRing X hX) ≪≫
    (moduleHomDual ((restrictScalars f).obj ((extendScalars f).obj H))).mapIso
      (asIso ((extendRestrictScalarsAdj f).unit.app X)).op ≪≫
    moduleHomCoefficientIso hH.completionUnitIso.symm X

/-- The comparison's actual formula is evaluation on `1 ⊗ x`, followed
by the inverse of the original coefficient tensor unit. -/
@[simp]
theorem matlisCompletedHomObjectIso_hom_apply (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X)
    (g : (extendScalars
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X ⟶
        matlisCompletedCoefficient H) (x : X) :
    ModuleCat.Hom.hom ((matlisCompletedHomObjectIso H hH X hX).hom g) x =
      hH.completionUnitIso.inv
        (g ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x)) := rfl

/-- Tensor extension followed by the comparison recovers the original morphism. -/
@[simp]
theorem matlisCompletedHomObjectIso_hom_extend (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X) (g : X ⟶ H) :
    (matlisCompletedHomObjectIso H hH X hX).hom
      ((extendScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map g) = g := by
  apply ModuleCat.hom_ext
  ext x
  rw [matlisCompletedHomObjectIso_hom_apply, ExtendScalars.map_tmul]
  exact ConcreteCategory.congr_hom hH.completionUnitIso.hom_inv_id (g x)

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- An abstract inverse identity avoids unfolding the concrete comparison. -/
private theorem moduleIso_inv_apply_eq {A B : ModuleCat.{u} R} (e : A ≅ B)
    (x : A) (y : B) (h : e.hom x = y) : e.inv y = x :=
  (congrArg (fun z => e.inv z) h).symm.trans (ConcreteCategory.congr_hom e.hom_inv_id x)

/-- The inverse comparison is the actual tensor extension of morphisms. -/
@[simp]
theorem matlisCompletedHomObjectIso_inv_apply (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X) (g : X ⟶ H) :
    (matlisCompletedHomObjectIso H hH X hX).inv g =
      (extendScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map g := by
  exact moduleIso_inv_apply_eq (matlisCompletedHomObjectIso H hH X hX) _ g
    (matlisCompletedHomObjectIso_hom_extend H hH X hX g)

/-- Naturality compares actual precomposition before and after scalar change. -/
@[reassoc]
theorem matlisCompletedHomObjectIso_naturality
    (X Y : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X)
    (hY : supportedModuleProperty (IsLocalRing.maximalIdeal R) Y) (f : X ⟶ Y) :
    (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map
      ((moduleHomDual (matlisCompletedCoefficient H)).map
        ((extendScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map f).op) ≫
        (matlisCompletedHomObjectIso H hH X hX).hom =
      (matlisCompletedHomObjectIso H hH Y hY).hom ≫ (moduleHomDual H).map f.op := by
  apply ModuleCat.hom_ext
  ext g
  apply ModuleCat.hom_ext
  ext x
  change hH.completionUnitIso.inv
      (ModuleCat.Hom.hom g ((extendScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map f
          ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x))) =
    hH.completionUnitIso.inv
      (ModuleCat.Hom.hom g ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] f x))
  rw [ExtendScalars.map_tmul]

/-- The inverse coefficient tensor units intertwine every actual original
coefficient morphism, by naturality of the original scalar-change adjunction. -/
theorem matlisCompletionUnitIso_inv_naturality
    (K : ModuleCat.{u} R) (hK : SupportedDualizingModule K) (f : H ⟶ K) :
    (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map
      ((extendScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map f) ≫
        hK.completionUnitIso.inv = hH.completionUnitIso.inv ≫ f := by
  apply (cancel_epi hH.completionUnitIso.hom).mp
  rw [← Category.assoc, ← Category.assoc, hH.completionUnitIso.hom_inv_id, Category.id_comp]
  have h := (extendRestrictScalarsAdj
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).unit.naturality f
  change f ≫ hK.completionUnitIso.hom =
    hH.completionUnitIso.hom ≫
      (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map
        ((extendScalars
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map f) at h
  rw [← h, Category.assoc, hK.completionUnitIso.hom_inv_id, Category.comp_id]

/-- Coefficient naturality is actual postcomposition on both Hom modules. -/
@[reassoc]
theorem matlisCompletedHomObjectIso_coefficient_naturality
    (K : ModuleCat.{u} R) (hK : SupportedDualizingModule K) (f : H ⟶ K)
    (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X) :
    (restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map
      (((linearYoneda (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (ModuleCat (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map
          ((extendScalars
            (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map f)).app
              (op ((extendScalars
                (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X))) ≫
        (matlisCompletedHomObjectIso K hK X hX).hom =
      (matlisCompletedHomObjectIso H hH X hX).hom ≫
        (((linearYoneda R (ModuleCat R)).map f).app (op X)) := by
  apply ModuleCat.hom_ext
  ext g
  apply ModuleCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom (matlisCompletionUnitIso_inv_naturality H hH K hK f)
    (ModuleCat.Hom.hom g ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x))

/-- **IV.5.1, original Hom identification.** Forgetting finite generation and
restricting scalars in the actual completed-ring anti-equivalence yields
the original base-ring Hom functor on the original category `CA`. -/
def matlisCompletedRingHomIso :
    (matlisCompletedRingAntiEquivalence H hH).functor ⋙
        (ModuleCat.isFG (AdicCompletion (IsLocalRing.maximalIdeal R) R)).ι ⋙
          restrictScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ≅
      (matlisArtinianModuleProperty R).ι.op ⋙ moduleHomDual H :=
  NatIso.ofComponents
    (fun X => matlisCompletedHomObjectIso H hH X.unop.obj X.unop.supported)
    (fun f => matlisCompletedHomObjectIso_naturality H hH _ _ _ _ f.unop.hom)

/-- The final functor comparison has the same literal original pointwise formula. -/
@[simp]
theorem matlisCompletedRingHomIso_hom_app_apply (X : MatlisArtinianModuleCat R)
    (g : (extendScalars
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj X.obj ⟶
        matlisCompletedCoefficient H) (x : X.obj) :
    ModuleCat.Hom.hom ((matlisCompletedRingHomIso H hH).hom.app (op X) g) x =
      hH.completionUnitIso.inv
        (g ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] x)) := rfl

/-- The inverse final functor comparison is exactly tensor extension of the
original morphism, even though its target lies in the completed Hom module. -/
@[simp]
theorem matlisCompletedRingHomIso_inv_app_apply (X : MatlisArtinianModuleCat R)
    (g : X.obj ⟶ H) :
    (matlisCompletedRingHomIso H hH).inv.app (op X) g =
      (extendScalars
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).map g :=
  matlisCompletedHomObjectIso_inv_apply H hH X.obj X.supported g

end SGA.SGA2.ExposeIV
