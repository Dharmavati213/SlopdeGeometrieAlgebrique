/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralAbutment
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralNaturality
import SGA.SGA2.ExposeI.HomComplexNaturality

/-!
# Naturality of the actual module-endofunctor spectral abutment

The original Hom-complex comparison and the K-injective localization map
intertwine every resolution map. The integer-resolution comparison then
identifies the actual total-interval map with the original right-derived
composite map.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R) [T.Additive]
  (F : SheafOfModules.{u} R)

local instance moduleEndofunctorTotalNaturalityHasDerivedCategory :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable {G H : SheafOfModules.{u} R} {I : InjectiveResolution G} {J : InjectiveResolution H}

/-- The actual single-source Hom-complex comparison on homology. -/
def moduleEndofunctorHomComplexHomologyIso (I : InjectiveResolution G) (n : ℤ) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj F)
      (moduleEndofunctorResolutionInt R T I)).homology n ≅
        (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (moduleEndofunctorResolutionInt R T I)).homology n :=
  (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
    (ExposeI.homComplexFromSingleIso F (moduleEndofunctorResolutionInt R T I))

/-- The comparison retains the original module coefficient cochain maps. -/
@[reassoc]
theorem moduleEndofunctorHomComplexHomologyIso_naturality
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :
    homologyMap (ExposeI.homComplexPostcomp
        ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj F)
        (moduleEndofunctorResolutionIntMap R T α)) n ≫
        (moduleEndofunctorHomComplexHomologyIso R T F J n).hom =
      (moduleEndofunctorHomComplexHomologyIso R T F I n).hom ≫
        homologyMap (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (moduleEndofunctorResolutionIntMap R T α)) n := by
  have h := congrArg (fun f ↦ homologyMap f n)
    (ExposeI.homComplexFromSingleIso_naturality F (moduleEndofunctorResolutionIntMap R T α))
  simp only [homologyMap_comp] at h
  exact h

variable [T.PreservesInjectiveObjects]

/-- The actual Hom-complex total comparison is natural in every resolution map. -/
theorem moduleEndofunctorHomComplexTotalEquiv_naturality
    (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ)
    (x : (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (moduleEndofunctorResolutionInt R T I)).homology n) :
    moduleEndofunctorHomComplexTotalEquiv R T F J n
        (homologyMap (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (moduleEndofunctorResolutionIntMap R T α)) n x) =
      moduleEndofunctorSpectralTotalMap R T F α n
        (moduleEndofunctorHomComplexTotalEquiv R T F I n x) := by
  let A := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj F
  let eI := moduleEndofunctorHomComplexHomologyIso R T F I n
  let eJ := moduleEndofunctorHomComplexHomologyIso R T F J n
  have hm : homologyMap (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (moduleEndofunctorResolutionIntMap R T α)) n ≫ eJ.inv =
      eI.inv ≫ homologyMap
        (ExposeI.homComplexPostcomp A (moduleEndofunctorResolutionIntMap R T α)) n := by
    rw [← cancel_epi eI.hom, ← Category.assoc,
      ← moduleEndofunctorHomComplexHomologyIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change ExposeI.homComplexHomologyDerivedHomEquiv A (moduleEndofunctorResolutionInt R T J) n
      (eJ.inv (homologyMap (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (moduleEndofunctorResolutionIntMap R T α)) n x)) =
    ExposeI.homComplexHomologyDerivedHomEquiv A (moduleEndofunctorResolutionInt R T I) n
      (eI.inv x) ≫ (moduleEndofunctorDerivedObjectMap R T α)⟦n⟧'
  have hx := ConcreteCategory.congr_hom hm x
  simp only [ConcreteCategory.comp_apply] at hx
  rw [hx]
  exact ExposeI.homComplexHomologyDerivedHomEquiv_naturality A
    (moduleEndofunctorResolutionIntMap R T α) n _

/-- The actual total-interval map is the original right-derived composite coefficient map. -/
theorem moduleEndofunctorSpectralDerivedCompositeEquiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ)
    (x : moduleEndofunctorSpectralTotal R T F I n) :
    moduleEndofunctorSpectralDerivedCompositeEquiv R T F J n
        (moduleEndofunctorSpectralTotalMap R T F α n x) =
      ((T ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n).map a
        (moduleEndofunctorSpectralDerivedCompositeEquiv R T F I n x) := by
  let eI := moduleEndofunctorHomComplexTotalEquiv R T F I n
  let eJ := moduleEndofunctorHomComplexTotalEquiv R T F J n
  let z := eI.symm x
  have he := moduleEndofunctorHomComplexTotalEquiv_naturality R T F α n z
  change eJ _ = moduleEndofunctorSpectralTotalMap R T F α n (eI z) at he
  rw [AddEquiv.apply_symm_apply] at he
  change (ExposeI.injectiveResolutionIntHomologyIso
      (T ⋙ preadditiveCoyoneda.obj (op F)) J n).hom
      (eJ.symm (moduleEndofunctorSpectralTotalMap R T F α n x)) = _
  rw [← he, AddEquiv.symm_apply_apply]
  exact ConcreteCategory.congr_hom
    (ExposeI.injectiveResolutionIntHomologyIso_naturality
      (T ⋙ preadditiveCoyoneda.obj (op F)) a I J α hα n) z

/-- A proved natural identification of the composite retains the actual total coefficient map. -/
theorem moduleEndofunctorSpectralComparedAbutmentEquiv_naturality
    (U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (e : (T ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n ≅ U)
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0)
    (x : moduleEndofunctorSpectralTotal R T F I n) :
    moduleEndofunctorSpectralComparedAbutmentEquiv R T F U n e J
        (moduleEndofunctorSpectralTotalMap R T F α n x) =
      U.map a (moduleEndofunctorSpectralComparedAbutmentEquiv R T F U n e I x) := by
  change e.hom.app H (moduleEndofunctorSpectralDerivedCompositeEquiv R T F J n
      (moduleEndofunctorSpectralTotalMap R T F α n x)) =
    U.map a (e.hom.app G (moduleEndofunctorSpectralDerivedCompositeEquiv R T F I n x))
  rw [moduleEndofunctorSpectralDerivedCompositeEquiv_naturality R T F a α hα]
  generalize moduleEndofunctorSpectralDerivedCompositeEquiv R T F I n x = y
  have h := ConcreteCategory.congr_hom (e.hom.naturality a) y
  simpa only [ConcreteCategory.comp_apply] using h

end SGA.SGA2.ExposeVI
