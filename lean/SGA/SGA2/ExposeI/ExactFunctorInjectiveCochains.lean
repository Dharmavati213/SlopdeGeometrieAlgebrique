/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ExtRightDerivedExactFunctor

/-!
# Exact functors on the integer-indexed injective-resolution complex

Mapping an injective resolution and then extending it by zero to integer
degrees agrees canonically with first extending and then applying the
exact functor. The comparison retains the actual augmentation.
-/

noncomputable section

universe v u u'

open CategoryTheory Limits Opposite HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] (G : C ⥤ D)
    [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
    {B : C} (I : InjectiveResolution B)

/-- The degreewise comparison for mapping the integer-indexed resolution. -/
def mapInjectiveResolutionCochainXIso (i : ℤ) :
    G.obj (I.cochainComplex.X i) ≅ (mapInjectiveResolution G I).cochainComplex.X i :=
  if hi : 0 ≤ i then
    G.mapIso (I.cochainComplexXIso i i.toNat (Int.toNat_of_nonneg hi)) ≪≫
      ((mapInjectiveResolution G I).cochainComplexXIso i i.toNat
        (Int.toNat_of_nonneg hi)).symm
  else
    (G.map_isZero (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 i
      (lt_of_not_ge hi))).iso
        (CochainComplex.isZero_of_isStrictlyGE (mapInjectiveResolution G I).cochainComplex
          0 i (lt_of_not_ge hi))

@[simp]
theorem mapInjectiveResolutionCochainXIso_ofNat (i : ℕ) :
    mapInjectiveResolutionCochainXIso G I (i : ℤ) =
      G.mapIso (I.cochainComplexXIso i i rfl) ≪≫
        ((mapInjectiveResolution G I).cochainComplexXIso i i rfl).symm := by
  simp [mapInjectiveResolutionCochainXIso]

/-- The degreewise comparison respects the canonical transports between equal degrees. -/
@[reassoc]
theorem mapInjectiveResolutionCochainXIso_inv_naturality {i j : ℤ} (h : i = j) :
    G.map (I.cochainComplex.XIsoOfEq h).inv ≫ (mapInjectiveResolutionCochainXIso G I i).hom =
      (mapInjectiveResolutionCochainXIso G I j).hom ≫
        ((mapInjectiveResolution G I).cochainComplex.XIsoOfEq h).inv := by
  subst j
  simp

/-- Exact functors commute with extension by zero of the resolution complex. -/
def mapInjectiveResolutionCochainIso :
    (G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ≅
      (mapInjectiveResolution G I).cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (mapInjectiveResolutionCochainXIso G I)
    (fun i j hij => by
      by_cases hi : 0 ≤ i
      · have hj : 0 ≤ j := by change i + 1 = j at hij; omega
        change (mapInjectiveResolutionCochainXIso G I i).hom ≫
          (mapInjectiveResolution G I).cochainComplex.d i j =
          G.map (I.cochainComplex.d i j) ≫ (mapInjectiveResolutionCochainXIso G I j).hom
        rw [I.cochainComplex_d i j i.toNat j.toNat
          (Int.toNat_of_nonneg hi) (Int.toNat_of_nonneg hj)]
        rw [(mapInjectiveResolution G I).cochainComplex_d i j i.toNat j.toNat
          (Int.toNat_of_nonneg hi) (Int.toNat_of_nonneg hj)]
        simp [mapInjectiveResolutionCochainXIso, hi, hj, Functor.map_comp,
          Category.assoc, mapInjectiveResolution]
      · exact (G.map_isZero (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex
          0 i (lt_of_not_ge hi))).eq_of_src _ _)

/-- The actual augmentation is preserved by the integer-complex comparison. -/
theorem mapInjectiveResolutionCochainIso_ι :
    (G.mapCochainComplexSingleFunctor 0).inv.app B ≫
        (G.mapHomologicalComplex (.up ℤ)).map I.ι' ≫
          (mapInjectiveResolutionCochainIso G I).hom = (mapInjectiveResolution G I).ι' := by
  apply HomologicalComplex.from_single_hom_ext
  simp [mapInjectiveResolutionCochainIso, mapInjectiveResolutionCochainXIso,
    InjectiveResolution.ι'_f_zero,
    mapInjectiveResolution_ι_f_zero, Functor.mapCochainComplexSingleFunctor,
    singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq,
    Functor.map_comp, Category.assoc]

end SGA.SGA2.ExposeI
