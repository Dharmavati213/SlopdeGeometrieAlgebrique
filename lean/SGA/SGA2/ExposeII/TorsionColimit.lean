/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.Torsion
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# SGA 2, Exposé II, (7.5): the colimit of quotient Hom modules

The direct system of `Hom_R(R/I^n, M)` has colimit `powerTorsion I M`, naturally
in `M`. The indexing and quotient maps are those used by mathlib's definition
of local cohomology. The comparison proved here concerns degree zero Hom;
it does not assert a sheaf cohomology or higher Ext comparison.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The ideal-power torsion submodule, regarded as a functor on modules. -/
def powerTorsionFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (powerTorsion I M)
  map f := ModuleCat.ofHom (powerTorsionMap I f.hom)

/-- The quotient-Hom direct system, with the same indexing as mathlib's
`localCohomology.diagram (idealPowersDiagram I) 0`. -/
def quotientHomDiagram : (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).op ⋙
    linearCoyoneda R (ModuleCat.{u} R)

/-- Evaluation at `1` gives a cocone from the quotient-Hom system to ideal-power torsion. -/
def quotientHomTorsionCocone : Cocone (quotientHomDiagram I) where
  pt := powerTorsionFunctor I
  ι :=
    { app := fun n =>
        { app := fun M => ModuleCat.ofHom
            ((quotientHomToPowerTorsion I M n.unop.unop).comp
              ModuleCat.homLinearEquiv.toLinearMap)
          naturality := by intros; rfl }
      naturality := by intros; rfl }

/-- The canonical comparison from the categorical Hom colimit to ideal-power torsion. -/
def quotientHomColimitToTorsion : colimit (quotientHomDiagram I) ⟶ powerTorsionFunctor I :=
  colimit.desc _ (quotientHomTorsionCocone I)

@[simp]
theorem quotientHomColimitToTorsion_ι (n : (ℕᵒᵖ)ᵒᵖ) (M : ModuleCat.{u} R)
    (f : ModuleCat.of R (R ⧸ I ^ n.unop.unop) ⟶ M) :
    Subtype.val (p := fun x : M => x ∈ powerTorsion I M)
      ((quotientHomColimitToTorsion I).app M
        ((colimit.ι (quotientHomDiagram I) n).app M f)) = f.hom 1 := by
  have h := NatTrans.congr_app (colimit.ι_desc (quotientHomTorsionCocone I) n) M
  exact congrArg Subtype.val (ConcreteCategory.congr_hom h f)

/-- Every element of the categorical colimit has a representative in one Hom module. -/
theorem quotientHomColimit_exists_rep (M : ModuleCat.{u} R)
    (x : (colimit (quotientHomDiagram I)).obj M) :
    ∃ (n : (ℕᵒᵖ)ᵒᵖ) (f : ModuleCat.of R (R ⧸ I ^ n.unop.unop) ⟶ M),
      (colimit.ι (quotientHomDiagram I) n).app M f = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  exact Concrete.isColimit_exists_rep
    (quotientHomDiagram I ⋙ (evaluation _ _).obj M)
    (isColimitOfPreserves ((evaluation _ _).obj M) (colimit.isColimit _)) x

/-- Distinct elements in the Hom colimit give distinct ideal-power torsion elements. -/
theorem quotientHomColimitToTorsion_injective (M : ModuleCat.{u} R) :
    Function.Injective ((quotientHomColimitToTorsion I).app M) := by
  intro x y h
  obtain ⟨i, f, rfl⟩ := quotientHomColimit_exists_rep I M x
  obtain ⟨j, g, rfl⟩ := quotientHomColimit_exists_rep I M y
  have hfg : f.hom 1 = g.hom 1 := by
    have hh := congrArg (Subtype.val (p := fun x : M => x ∈ powerTorsion I M)) h
    simpa only [quotientHomColimitToTorsion_ι] using hh
  apply Concrete.isColimit_rep_eq_of_exists
    (quotientHomDiagram I ⋙ (evaluation _ _).obj M)
    (D := ((evaluation _ _).obj M).mapCocone (colimit.cocone (quotientHomDiagram I))) f g
  refine ⟨op (op (max i.unop.unop j.unop.unop)),
    (homOfLE (le_max_left _ _)).op.op, (homOfLE (le_max_right _ _)).op.op, ?_⟩
  apply ModuleCat.hom_ext
  apply (quotientHomEquivTorsionBySet (I ^ max i.unop.unop j.unop.unop) M).injective
  apply Subtype.ext
  exact hfg

/-- Every ideal-power torsion element is the image of the corresponding quotient Hom class. -/
theorem quotientHomColimitToTorsion_surjective (M : ModuleCat.{u} R) :
    Function.Surjective ((quotientHomColimitToTorsion I).app M) := by
  intro x
  obtain ⟨n, f, hf⟩ := (mem_powerTorsion_iff_exists_quotientHom I M x.val).mp x.property
  refine ⟨(colimit.ι (quotientHomDiagram I) (op (op n))).app M (ModuleCat.ofHom f), ?_⟩
  apply Subtype.ext
  exact (quotientHomColimitToTorsion_ι I (op (op n)) M (ModuleCat.ofHom f)).trans hf

/-- The canonical Hom-colimit comparison is an isomorphism at every module. -/
instance quotientHomColimitToTorsion_app_isIso (M : ModuleCat.{u} R) :
    IsIso ((quotientHomColimitToTorsion I).app M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨quotientHomColimitToTorsion_injective I M, quotientHomColimitToTorsion_surjective I M⟩

instance quotientHomColimitToTorsion_isIso : IsIso (quotientHomColimitToTorsion I) :=
  NatIso.isIso_of_isIso_app _

/-- II.(7.5), degree-zero algebraic comparison: the colimit of
`Hom_R(R/I^n, -)` is naturally isomorphic to ideal-power torsion. -/
def quotientHomColimitIso : colimit (quotientHomDiagram I) ≅ powerTorsionFunctor I :=
  asIso (quotientHomColimitToTorsion I)

/-- Evaluation at `1` exhibits ideal-power torsion itself as a categorical colimit. -/
def quotientHomTorsionCoconeIsColimit : IsColimit (quotientHomTorsionCocone I) := by
  have : IsIso ((colimit.isColimit (quotientHomDiagram I)).desc
      (quotientHomTorsionCocone I)) := quotientHomColimitToTorsion_isIso I
  exact (colimit.isColimit (quotientHomDiagram I)).ofPointIso

end SGA.SGA2.ExposeII
