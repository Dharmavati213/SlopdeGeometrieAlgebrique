/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleAdditiveNaturality

/-!
# Actual global scalar actions on underlying additive sheaves and complexes

Even for a noncommutative structure ring, global scalars act by additive-sheaf
endomorphisms, natural with respect to module-linear maps. They therefore act
on the underlying additive complex of every module complex and on its image
in the derived category. This retains scalar data in the derived truncation
approach to V.3.2 without assuming that forgetting scalars preserves injectivity.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

/-- An additive functor carries the full endomorphism ring, not just its multiplication. -/
def additiveEndRingHom {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (T : C ⥤ D) [T.Additive] (K : C) :
    End K →+* End (T.obj K) where
  toFun := T.map
  map_one' := T.map_id K
  map_mul' a b := T.map_comp b a
  map_zero' := T.map_zero K K
  map_add' _ _ := T.map_add

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

local instance (M : SheafOfModules.{u} R) (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) (((SheafOfModules.toSheaf R).obj M).obj.obj U) :=
  inferInstanceAs (Module (R.obj.obj U) (M.val.obj U))

/-- Multiplication by a global scalar on the underlying additive sheaf. -/
def moduleUnderlyingGlobalScalarHom (M : SheafOfModules.{u} R)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj M :=
  ⟨{ app U := ModuleCat.smul (M.val.obj U)
        (R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op r)
     naturality {U V} i := by
       ext x
       change R.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op r • M.val.map i x =
         M.val.map i (R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op r • x)
       rw [M.val.map_smul]
       congr 1
       exact (ConcreteCategory.congr_hom
         (R.obj.map_comp (homOfLE (le_top : U.unop ≤ ⊤)).op i) r) }⟩

/-- Module-linear maps commute with the actual additive global scalar action. -/
@[reassoc]
theorem moduleUnderlyingGlobalScalarHom_naturality
    {M N : SheafOfModules.{u} R} (a : M ⟶ N)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    (SheafOfModules.toSheaf R).map a ≫ moduleUnderlyingGlobalScalarHom R N r =
      moduleUnderlyingGlobalScalarHom R M r ≫ (SheafOfModules.toSheaf R).map a := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U x
  exact ((a.val.app U).hom.map_smul _ x).symm

/-- The scalar action as an endomorphism of the actual forgetful functor. -/
def moduleUnderlyingGlobalScalar (r : R.obj.obj (op (⊤ : Opens X))) :
    SheafOfModules.toSheaf R ⟶ SheafOfModules.toSheaf R where
  app M := moduleUnderlyingGlobalScalarHom R M r
  naturality {_ _} a := moduleUnderlyingGlobalScalarHom_naturality R a r

/-- The full ring laws hold for the natural global scalar endomorphisms. -/
def moduleUnderlyingGlobalScalarRingHom :
    R.obj.obj (op (⊤ : Opens X)) →+* End (SheafOfModules.toSheaf R) where
  toFun := moduleUnderlyingGlobalScalar R
  map_one' := by
    apply NatTrans.ext
    funext M
    apply CategoryTheory.Sheaf.hom_ext
    ext U x
    change R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op 1 • x = x
    simp
  map_mul' r s := by
    apply NatTrans.ext
    funext M
    apply CategoryTheory.Sheaf.hom_ext
    ext U x
    change R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op (r * s) • x =
      R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op r •
        (R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op s • x)
    simp [mul_smul]
  map_zero' := by
    apply NatTrans.ext
    funext M
    apply CategoryTheory.Sheaf.hom_ext
    ext U x
    change R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op 0 • x = 0
    simp
  map_add' r s := by
    apply NatTrans.ext
    funext M
    apply CategoryTheory.Sheaf.hom_ext
    ext U x
    change R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op (r + s) • x =
      R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op r • x +
        R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op s • x
    simp [add_smul]

/-- Global scalars act on the entire original additive complex of a module complex. -/
def moduleUnderlyingComplexGlobalScalar
    (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    End (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  ((moduleUnderlyingGlobalScalar R r).mapHomologicalComplex (ComplexShape.up ℤ)).app K

/-- The action on a module complex is a genuine ring homomorphism. -/
def moduleUnderlyingComplexGlobalScalarRingHom
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    R.obj.obj (op (⊤ : Opens X)) →+*
      End (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  toFun := moduleUnderlyingComplexGlobalScalar R K
  map_one' := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun a : End (SheafOfModules.toSheaf R) ↦ a.app (K.X n))
      (moduleUnderlyingGlobalScalarRingHom R).map_one
  map_mul' r s := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun a : End (SheafOfModules.toSheaf R) ↦ a.app (K.X n))
      ((moduleUnderlyingGlobalScalarRingHom R).map_mul r s)
  map_zero' := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun a : End (SheafOfModules.toSheaf R) ↦ a.app (K.X n))
      (moduleUnderlyingGlobalScalarRingHom R).map_zero
  map_add' r s := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun a : End (SheafOfModules.toSheaf R) ↦ a.app (K.X n))
      ((moduleUnderlyingGlobalScalarRingHom R).map_add r s)

/-- Actual coefficient cochain maps commute with the scalar action on complexes. -/
@[reassoc]
theorem moduleUnderlyingComplexGlobalScalar_naturality
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (a : K ⟶ L)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫
        moduleUnderlyingComplexGlobalScalar R L r =
      moduleUnderlyingComplexGlobalScalar R K r ≫
        ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map a :=
  ((moduleUnderlyingGlobalScalar R r).mapHomologicalComplex (ComplexShape.up ℤ)).naturality a

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

/-- Localization carries the original global scalar action to the actual derived object. -/
def moduleUnderlyingDerivedGlobalScalarRingHom
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    R.obj.obj (op (⊤ : Opens X)) →+*
      End ((DerivedCategory.Q (C := Sheaf AddCommGrpCat.{u} X)).obj
        (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  (additiveEndRingHom (DerivedCategory.Q (C := Sheaf AddCommGrpCat.{u} X)) _).comp
    (moduleUnderlyingComplexGlobalScalarRingHom R K)

/-- Original cochain coefficient maps remain equivariant after localization. -/
@[reassoc]
theorem moduleUnderlyingDerivedGlobalScalar_naturality
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (a : K ⟶ L)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    (DerivedCategory.Q (C := Sheaf AddCommGrpCat.{u} X)).map
        (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map a) ≫
          moduleUnderlyingDerivedGlobalScalarRingHom R L r =
      moduleUnderlyingDerivedGlobalScalarRingHom R K r ≫
        (DerivedCategory.Q (C := Sheaf AddCommGrpCat.{u} X)).map
          (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  have h := congrArg (DerivedCategory.Q (C := Sheaf AddCommGrpCat.{u} X)).map
    (moduleUnderlyingComplexGlobalScalar_naturality R a r)
  simp only [Functor.map_comp] at h
  exact h

end SGA.SGA2.ExposeV
