/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHomFunctor

/-! # Global sections of local linear Hom are the original module-sheaf morphisms -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- A global local-linear map gives its actual module-sheaf morphism. -/
def moduleGlobalHomToMorphism (F G : SheafOfModules.{u} R)
    (φ : moduleLocalHom F.val G.val (⊤ : Opens X)) : F ⟶ G :=
  ⟨PresheafOfModules.homMk
    { app U := φ.val.app (op (Over.mk (homOfLE (le_top : U.unop ≤ ⊤))))
      naturality {U V} i :=
        φ.val.naturality
          (Over.homMk i.unop :
            Over.mk (homOfLE (le_top : V.unop ≤ ⊤)) ⟶
              Over.mk (homOfLE (le_top : U.unop ≤ ⊤))).op }
    (fun U r x ↦ φ.property (Over.mk (homOfLE le_top)) r x)⟩

/-- Every original module-sheaf morphism gives a global section of the actual Hom sheaf. -/
def moduleMorphismToGlobalHom {F G : SheafOfModules.{u} R} (a : F ⟶ G) :
    moduleLocalHom F.val G.val (⊤ : Opens X) :=
  ⟨Functor.whiskerLeft (Over.forget (⊤ : Opens X)).op
    ((PresheafOfModules.toPresheaf R.obj).map a.val),
    fun V r x ↦ (a.val.app (op V.left)).hom.map_smul r x⟩

/-- The global Hom identification uses the original maps, with their addition. -/
def moduleSheafHomAbGlobalEquiv (F G : SheafOfModules.{u} R) :
    ((moduleSheafHomAb (Opens.grothendieckTopology X) F G).obj.obj (op (⊤ : Opens X))) ≃+
      (F ⟶ G) where
  toFun := moduleGlobalHomToMorphism R F G
  invFun := moduleMorphismToGlobalHom R
  left_inv φ := by
    apply moduleLocalHom_ext
    intro V x
    rfl
  right_inv a := by ext U x; rfl
  map_add' _ _ := by ext U x; rfl

/-- The global identification respects the original coefficient postcomposition. -/
theorem moduleSheafHomAbGlobalEquiv_naturality (F : SheafOfModules.{u} R)
    {G H : SheafOfModules.{u} R} (a : G ⟶ H)
    (φ : ((moduleSheafHomAb (Opens.grothendieckTopology X) F G).obj.obj
      (op (⊤ : Opens X)))) :
    moduleSheafHomAbGlobalEquiv R F H
        (((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).map a).hom.app
          (op (⊤ : Opens X)) φ) =
      moduleSheafHomAbGlobalEquiv R F G φ ≫ a := by ext U x; rfl

/-- Global sections of the actual Hom sheaf are naturally the original additive Hom functor. -/
def moduleSheafHomAbGlobalFunctorIso (F : SheafOfModules.{u} R) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op (⊤ : Opens X)) ≅ preadditiveCoyoneda.obj (op F) :=
  NatIso.ofComponents (fun G ↦ (moduleSheafHomAbGlobalEquiv R F G).toAddCommGrpIso)
    (fun a ↦ by ext φ; exact moduleSheafHomAbGlobalEquiv_naturality R F a φ)

end SGA.SGA2.ExposeVI
