/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.Fibers
import SGA.SGA1.ExposeVI.BasedEquivalences
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# SGA 1, Exposé VI, VI.6.10: fiberwise faithfulness for cartesian functors
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

set_option linter.style.haveILetI false

theorem fiberMap_faithful_of_faithful (F : BasedFunctor X Y) [F.toFunctor.Faithful]
    (S : E) : (fiberMap F S).Faithful :=
  inferInstance

theorem fiberMap_full_of_full (F : BasedFunctor X Y) [F.toFunctor.Full]
    (S : E) : (fiberMap F S).Full :=
  inferInstance

/-- VI.6.10 (faithful, ⇐). -/
theorem faithful_of_fiberwise [IsPreFibered X.p] (F : BasedFunctor X Y)
    [IsCartesianFunctor F] (h : ∀ S, (fiberMap F S).Faithful) :
    F.toFunctor.Faithful where
  map_injective {a b} {u v} huv := by
    have hbase : X.p.map u = X.p.map v := by
      have h : (F.toFunctor ⋙ Y.p).map u = (F.toFunctor ⋙ Y.p).map v :=
        congrArg Y.p.map huv
      rwa [F.w] at h
    let f : X.p.obj a ⟶ X.p.obj b := X.p.map u
    haveI : IsHomLift X.p f u := IsHomLift.map X.p u
    haveI : IsHomLift X.p f v := by
      haveI := IsHomLift.map X.p v
      convert ‹IsHomLift X.p (X.p.map v) v›
    let β := IsPreFibered.pullbackMap (p := X.p) (show X.p.obj b = X.p.obj b from rfl) f
    haveI : IsCartesian X.p f β :=
      IsPreFibered.pullbackMap.IsCartesian (p := X.p)
        (show X.p.obj b = X.p.obj b from rfl) f
    let u' := IsCartesian.map X.p f β u
    let v' := IsCartesian.map X.p f β v
    haveI : IsHomLift X.p (𝟙 (X.p.obj a)) u' := inferInstance
    haveI : IsHomLift X.p (𝟙 (X.p.obj a)) v' := inferInstance
    have hu : u' ≫ β = u := IsCartesian.fac X.p f β u
    have hv : v' ≫ β = v := IsCartesian.fac X.p f β v
    haveI : IsCartesian Y.p f (F.map β) :=
      IsCartesianFunctor.map_isCartesian (F := F) f β
    haveI : IsHomLift Y.p (𝟙 (X.p.obj a)) (F.map u') :=
      BasedFunctor.preserves_isHomLift F (𝟙 (X.p.obj a)) u'
    haveI : IsHomLift Y.p (𝟙 (X.p.obj a)) (F.map v') :=
      BasedFunctor.preserves_isHomLift F (𝟙 (X.p.obj a)) v'
    have hFuv : F.map u' = F.map v' :=
      IsCartesian.ext (p := Y.p) (f := f) (φ := F.map β) (F.map u') (F.map v') (by
        calc
          F.map u' ≫ F.map β = F.map (u' ≫ β) := (F.map_comp _ _).symm
          _ = F.map u := by rw [hu]
          _ = F.map v := huv
          _ = F.map (v' ≫ β) := by rw [hv]
          _ = F.map v' ≫ F.map β := F.map_comp _ _)
    have hproj : X.p.obj (IsPreFibered.pullbackObj (p := X.p)
        (show X.p.obj b = X.p.obj b from rfl) f) = X.p.obj a :=
      IsPreFibered.pullbackObj_proj (p := X.p)
        (show X.p.obj b = X.p.obj b from rfl) f
    let src : Fiber X.p (X.p.obj a) := ⟨a, rfl⟩
    let tgt : Fiber X.p (X.p.obj a) := ⟨_, hproj⟩
    let uFib : src ⟶ tgt := ⟨u', inferInstance⟩
    let vFib : src ⟶ tgt := ⟨v', inferInstance⟩
    have : uFib = vFib := (h (X.p.obj a)).map_injective (Subtype.ext hFuv)
    have huv' : u' = v' := congrArg Subtype.val this
    calc
      u = u' ≫ β := hu.symm
      _ = v' ≫ β := by rw [huv']
      _ = v := hv

/-- VI.6.10 (faithful). -/
theorem isCartesianFunctor_faithful_iff [IsPreFibered X.p]
    (F : BasedFunctor X Y) [IsCartesianFunctor F] :
    F.toFunctor.Faithful ↔ ∀ S, (fiberMap F S).Faithful :=
  ⟨fun _ S => fiberMap_faithful_of_faithful F S, fun h => faithful_of_fiberwise F h⟩

theorem fiberMap_isEquivalence_of_isBasedEquivalence (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) (S : E) : (fiberMap F S).IsEquivalence := by
  obtain ⟨Q⟩ := hF
  exact (Q.fiberEquivalence S).isEquivalence_functor

theorem isBasedEquivalence_iff_fiberwise_equivalences (F : BasedFunctor X Y) :
    IsBasedEquivalence F ↔
      F.toFunctor.IsEquivalence ∧ ∀ S, (fiberMap F S).IsEquivalence :=
  isBasedEquivalence_iff_fiberwise F

end SGA.SGA1.ExposeVI
