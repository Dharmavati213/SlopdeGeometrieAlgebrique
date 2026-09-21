/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.ExactFunctorInjectiveCochains

/-!
# Mapping the actual cocycles representing Ext classes

The cocycle defining an Ext class is sent to the cocycle obtained by applying
the exact functor to its component in the injective resolution.
-/

noncomputable section

universe v u u'

open CategoryTheory Limits Opposite Abelian HomologicalComplex CochainComplex HomComplex
open CategoryTheory.Localization

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} (I : InjectiveResolution B)

/-- The original cocycle used by `InjectiveResolution.extMk`. -/
def injectiveResolutionExtCocycle {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    Cocycle ((singleFunctor C 0).obj A) I.cochainComplex (n : ℤ) :=
  Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)
    m (by omega) (by simp [I.cochainComplex_d n m n m rfl rfl, reassoc_of% hf])

/-- The corresponding actual morphism from a single complex to a shifted resolution. -/
def injectiveResolutionExtCocycleHom {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    (singleFunctor C 0).obj A ⟶ I.cochainComplex⟦(n : ℤ)⟧ :=
  Cocycle.equivHomShift.symm (injectiveResolutionExtCocycle I f m hm hf)

/-- The degree-zero component of the actual shifted cocycle map. -/
theorem injectiveResolutionExtCocycleHom_f_zero {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    (injectiveResolutionExtCocycleHom I f m hm hf).f 0 =
      (singleObjXSelf (.up ℤ) 0 A).hom ≫ f ≫ (I.cochainComplexXIso n n rfl).inv ≫
        (I.cochainComplex.shiftFunctorObjXIso (n : ℤ) 0 n (zero_add _)).inv := by
  change ((Cochain.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)).rightShift
    (n : ℤ) 0 (zero_add _)).v 0 0 (add_zero _) = _
  rw [Cochain.rightShift_v _ (n : ℤ) 0 (zero_add _) 0 0 (add_zero _) n (zero_add _),
    Cochain.fromSingleMk_v]
  simp only [Category.assoc]

variable [HasExt.{v} C]

/-- Postcomposing `extMk` by the augmentation gives the original cocycle. -/
theorem extMk_postcomp_augmentation {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    (SmallShiftedHom.postcompEquiv I.ι'
      (by rw [mem_quasiIso_iff]; infer_instance)) (I.extMk f m hm hf) =
      SmallShiftedHom.mk (quasiIso C (.up ℤ)) (injectiveResolutionExtCocycleHom I f m hm hf) := by
  change (SmallShiftedHom.postcompEquiv I.ι' _)
    ((SmallShiftedHom.postcompEquiv I.ι' _).symm
      (CohomologyClass.equivOfIsKInjective
        (.mk (injectiveResolutionExtCocycle I f m hm hf)))) = _
  rw [Equiv.apply_symm_apply]
  exact CohomologyClass.toSmallShiftedHom_mk _

variable {D : Type u'} [Category.{v} D] [Abelian D] (G : C ⥤ D)
    [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]

/-- The shifted cocycle map commutes with the exact functor and the actual
integer-complex comparison of mapped resolutions. -/
theorem injectiveResolutionExtCocycleHom_map {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    (G.mapCochainComplexSingleFunctor 0).inv.app A ≫
        ShiftedHom.map (injectiveResolutionExtCocycleHom I f m hm hf)
          (G.mapHomologicalComplex (.up ℤ)) ≫
            (mapInjectiveResolutionCochainIso G I).hom⟦(n : ℤ)⟧' =
      injectiveResolutionExtCocycleHom (mapInjectiveResolution G I) (G.map f) m hm
        (by change G.map f ≫ G.map (I.cocomplex.d n m) = 0; rw [← G.map_comp, hf, G.map_zero]) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [ShiftedHom.map, Functor.mapCochainComplexSingleFunctor, singleMapHomologicalComplex,
    singleObjXSelf, singleObjXIsoOfEq, injectiveResolutionExtCocycleHom_f_zero,
    mapInjectiveResolutionCochainIso, mapInjectiveResolutionCochainXIso_ofNat,
    shiftFunctor_map_f', Functor.map_comp, Category.assoc, shiftFunctorObjXIso]

end SGA.SGA2.ExposeI
