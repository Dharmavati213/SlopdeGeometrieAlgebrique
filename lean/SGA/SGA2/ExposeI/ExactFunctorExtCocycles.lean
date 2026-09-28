/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
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
        (I.cochainComplex.shiftFunctorObjXIso (n : ℤ) 0 n (zero_add _).symm).inv := by
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

omit [HasExt.{v} C] in
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
  simp only [ShiftedHom.map, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f',
    Functor.mapCochainComplexSingleFunctor, singleMapHomologicalComplex,
    NatIso.ofComponents_inv_app]
  simp only [shiftFunctor_obj_X', Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
    ↓reduceDIte, eqToHom_refl, injectiveResolutionExtCocycleHom_f_zero, singleObjXSelf,
    singleObjXIsoOfEq, eqToIso_refl, Iso.refl_hom, shiftFunctorObjXIso, Category.id_comp,
    Functor.map_comp, Category.comp_id, mapInjectiveResolutionCochainIso,
    Hom.isoOfComponents_hom_f, Category.assoc]
  rw [mapInjectiveResolutionCochainXIso_inv_naturality]
  simp [mapInjectiveResolutionCochainXIso_ofNat, Category.assoc]

variable [HasExt.{v} D] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Applying the exact functor to an Ext class represented by an actual
resolution cocycle is the Ext class of the mapped cocycle. -/
theorem extMk_mapExactFunctor {n : ℕ} (f : A ⟶ I.cocomplex.X n)
    (m : ℕ) (hm : n + 1 = m) (hf : f ≫ I.cocomplex.d n m = 0) :
    (I.extMk f m hm hf).mapExactFunctor G =
      (mapInjectiveResolution G I).extMk (G.map f) m hm
        (by change G.map f ≫ G.map (I.cocomplex.d n m) = 0; rw [← G.map_comp, hf, G.map_zero]) := by
  let J := mapInjectiveResolution G I
  let Φ := G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let eA : (G.mapHomologicalComplex (.up ℤ)).obj ((singleFunctor C 0).obj A) ≅
      (singleFunctor D 0).obj (G.obj A) := (G.mapCochainComplexSingleFunctor 0).app A
  let eB : (G.mapHomologicalComplex (.up ℤ)).obj ((singleFunctor C 0).obj B) ≅
      (singleFunctor D 0).obj (G.obj B) := (G.mapCochainComplexSingleFunctor 0).app B
  let eI : (G.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ≅ J.cochainComplex :=
    mapInjectiveResolutionCochainIso G I
  have haug : Φ.smallShiftedHomMap eB eI
      (SmallShiftedHom.mk₀ (quasiIso C (.up ℤ)) (0 : ℤ) rfl I.ι') =
        SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) (0 : ℤ) rfl J.ι' := by
    rw [LocalizerMorphism.smallShiftedHomMap_mk₀]
    congr 1
    exact mapInjectiveResolutionCochainIso_ι G I
  have hcoc : Φ.smallShiftedHomMap eA eI
      (SmallShiftedHom.mk (quasiIso C (.up ℤ)) (injectiveResolutionExtCocycleHom I f m hm hf)) =
        SmallShiftedHom.mk (quasiIso D (.up ℤ))
          (injectiveResolutionExtCocycleHom J (G.map f) m hm
            (by change G.map f ≫ G.map (I.cocomplex.d n m) = 0
                rw [← G.map_comp, hf, G.map_zero])) := by
    rw [LocalizerMorphism.smallShiftedHomMap_mk]
    congr 1
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Φ, eA, eI, J,
      Functor.comp_obj, Iso.app_inv,
      Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism] using
      injectiveResolutionExtCocycleHom_map I G f m hm hf
  apply (SmallShiftedHom.postcompEquiv J.ι'
    (by rw [mem_quasiIso_iff]; infer_instance)).injective
  rw [extMk_postcomp_augmentation]
  change (Φ.smallShiftedHomMap eA eB (I.extMk f m hm hf)).comp
    (SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) (0 : ℤ) rfl J.ι') (zero_add _) = _
  rw [← haug, ← LocalizerMorphism.smallShiftedHomMap_comp]
  change Φ.smallShiftedHomMap eA eI
    ((SmallShiftedHom.postcompEquiv I.ι' (by rw [mem_quasiIso_iff]; infer_instance))
      (I.extMk f m hm hf)) = _
  rw [extMk_postcomp_augmentation, hcoc]

end SGA.SGA2.ExposeI
