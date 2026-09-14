/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.TorsionColimit
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# SGA 2, Exposé II, (7.5): local cohomology in degree zero

The degree-zero Ext functor appearing in mathlib's definition of local
cohomology is identified with Hom. Taking its colimit over ideal powers
identifies degree-zero local cohomology with ideal-power torsion.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

section DerivedNaturality

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [EnoughProjectives C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

private theorem fromLeftDerivedZero_naturality (α : F ⟶ G) (X : C) :
    (α.leftDerived 0).app X ≫ G.fromLeftDerivedZero.app X =
      F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P := projectiveResolution X
  rw [P.leftDerived_app_eq, P.fromLeftDerivedZero_eq, P.fromLeftDerivedZero_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (P.isoLeftDerivedObj F 0).hom).mpr
  change (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex α _).app P.complex) 0 ≫
        HomologicalComplex.homologyι _ 0 ≫ P.fromLeftDerivedZero' G) =
      (HomologicalComplex.homologyι _ 0 ≫ P.fromLeftDerivedZero' F) ≫ α.app X
  rw [Category.assoc]
  rw [HomologicalComplex.homologyι_naturality_assoc]
  congr 1
  apply (cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex _).obj P.complex) 0)).mp
  simp only [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (α.naturality (P.π.f 0)).symm

end DerivedNaturality

variable {R : Type u} [CommRing R]

private theorem linearYoneda_preservesLimits (M : ModuleCat.{u} R) :
    PreservesLimits ((linearYoneda R (ModuleCat.{u} R)).obj M) := by
  have : PreservesLimits
      (((linearYoneda R (ModuleCat.{u} R)).obj M) ⋙ forget (ModuleCat.{u} R)) :=
    inferInstanceAs (PreservesLimits (yoneda.obj M))
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- The Ext functor used to define local cohomology agrees in degree zero
with Hom, naturally in the first argument. -/
def extZeroIsoHom (M : ModuleCat.{u} R) :
    (Ext R (ModuleCat.{u} R) 0).flip.obj M ≅
      (linearYoneda R (ModuleCat.{u} R)).obj M := by
  have := linearYoneda_preservesLimits M
  have := preservesFiniteColimits_rightOp ((linearYoneda R (ModuleCat.{u} R)).obj M)
  let α := (((linearYoneda R (ModuleCat.{u} R)).obj M).rightOp).fromLeftDerivedZero
  have (X : (ModuleCat.{u} R)ᵒᵖ) : IsIso (α.leftOp.app X) := by
    change IsIso (α.app X.unop).unop
    infer_instance
  have : IsIso α.leftOp := NatIso.isIso_of_isIso_app _
  exact (asIso α.leftOp).symm

/-- The canonical degree-zero comparison, natural in both Hom arguments. -/
def homToExtZero : linearCoyoneda R (ModuleCat.{u} R) ⟶ Ext R (ModuleCat.{u} R) 0 where
  app X :=
    { app := fun M =>
        ((((linearYoneda R (ModuleCat.{u} R)).obj M).rightOp).fromLeftDerivedZero.app
          X.unop).unop
      naturality := by
        intro M N f
        apply Quiver.Hom.op_inj
        exact (fromLeftDerivedZero_naturality
          (((linearYoneda R (ModuleCat.{u} R)).map f).rightOp) X.unop).symm }
  naturality := by
    intro X Y f
    apply NatTrans.ext
    funext M
    apply Quiver.Hom.op_inj
    exact ((((linearYoneda R (ModuleCat.{u} R)).obj M).rightOp).fromLeftDerivedZero.naturality
      f.unop).symm

instance homToExtZero_app_app_isIso (X : (ModuleCat.{u} R)ᵒᵖ) (M : ModuleCat.{u} R) :
    IsIso (((homToExtZero (R := R)).app X).app M) := by
  have := linearYoneda_preservesLimits M
  have := preservesFiniteColimits_rightOp ((linearYoneda R (ModuleCat.{u} R)).obj M)
  change IsIso
    ((((linearYoneda R (ModuleCat.{u} R)).obj M).rightOp).fromLeftDerivedZero.app X.unop).unop
  infer_instance

instance homToExtZero_app_isIso (X : (ModuleCat.{u} R)ᵒᵖ) :
    IsIso ((homToExtZero (R := R)).app X) := NatIso.isIso_of_isIso_app _

instance homToExtZero_isIso : IsIso (homToExtZero (R := R)) := NatIso.isIso_of_isIso_app _

/-- Degree-zero Ext agrees with Hom as a bifunctor. -/
def extZeroIsoHomFunctor :
    Ext R (ModuleCat.{u} R) 0 ≅ linearCoyoneda R (ModuleCat.{u} R) :=
  (asIso homToExtZero).symm

/-- II.(7.5): degree-zero local cohomology agrees naturally with
ideal-power torsion. -/
def localCohomologyZeroIsoPowerTorsionFunctor (I : Ideal R) :
    _root_.localCohomology I 0 ≅ powerTorsionFunctor I :=
  HasColimit.isoOfNatIso
    (Functor.isoWhiskerLeft (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram I)).op extZeroIsoHomFunctor) ≪≫
    quotientHomColimitIso I

/-- II.(7.5): degree-zero local cohomology is the submodule of elements
annihilated by an ideal power. -/
def localCohomologyZeroIsoPowerTorsion (I : Ideal R) (M : ModuleCat.{u} R) :
    (_root_.localCohomology I 0).obj M ≅ ModuleCat.of R (powerTorsion I M) :=
  (localCohomologyZeroIsoPowerTorsionFunctor I).app M

end SGA.SGA2.ExposeII
