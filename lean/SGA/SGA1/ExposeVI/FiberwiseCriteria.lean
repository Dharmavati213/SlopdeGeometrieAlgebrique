/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered

/-!
# SGA 1, Exposé VI, VI.6.10: fiberwise criteria for cartesian functors

A cartesian `E`-functor `F : 𝒳 ⥤ 𝒴` out of a prefibered category is faithful (resp. fully
faithful, resp. an `E`-equivalence) iff every functor `F_S : 𝒳_S ⥤ 𝒴_S` between fibers is
faithful (resp. fully faithful, resp. an equivalence). SGA assumes both `𝒳` and `𝒴`
prefibered; only the source needs to be.
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- The base arrow of an arrow of `𝒴` between images of `F`, read in `𝒳`'s base objects. -/
private def baseArrow (F : BasedFunctor X Y) {a b : X.obj} (w : F.obj a ⟶ F.obj b) :
    X.p.obj a ⟶ X.p.obj b :=
  eqToHom (F.w_obj a).symm ≫ Y.p.map w ≫ eqToHom (F.w_obj b)

private instance (F : BasedFunctor X Y) {a b : X.obj} (w : F.obj a ⟶ F.obj b) :
    IsHomLift Y.p (baseArrow F w) w :=
  IsHomLift.of_fac _ _ _ (F.w_obj a) (F.w_obj b) rfl

variable [IsPreFibered X.p] (F : BasedFunctor X Y) [hF : IsCartesianFunctor F]
include hF

/-- VI.6.10 (faithful, ⇐): if every `F_S` is faithful, so is `F`. -/
theorem faithful_of_fiberwise (h : ∀ S, (fiberMap F S).Faithful) : F.toFunctor.Faithful where
  map_injective {a b} {u v} huv := by
    have hbase : X.p.map u = X.p.map v := by
      have h₁ := Functor.congr_hom F.w u
      have h₂ := Functor.congr_hom F.w v
      rw [Functor.comp_map, huv] at h₁
      rw [Functor.comp_map, h₁] at h₂
      exact (cancel_mono _).mp ((cancel_epi _).mp h₂)
    let f := X.p.map u
    have : IsHomLift X.p f v := by
      rw [show f = X.p.map v from hbase]
      infer_instance
    obtain ⟨c, β, hβ⟩ := IsPreFibered.exists_isCartesian X.p (rfl : X.p.obj b = _) f
    have hc : X.p.obj c = X.p.obj a := IsHomLift.domain_eq X.p f β
    let u' := IsCartesian.map X.p f β u
    let v' := IsCartesian.map X.p f β v
    have hFβ : IsCartesian Y.p f (F.map β) := hF.map_isCartesian f β
    have hFuv : F.map u' = F.map v' := by
      apply IsCartesian.ext Y.p f (F.map β)
      rw [← F.map_comp, ← F.map_comp, IsCartesian.fac, IsCartesian.fac, huv]
    let A : Fiber X.p (X.p.obj a) := ⟨a, rfl⟩
    let B : Fiber X.p (X.p.obj a) := ⟨c, hc⟩
    have : (⟨u', inferInstance⟩ : A ⟶ B) = ⟨v', inferInstance⟩ :=
      (h (X.p.obj a)).map_injective (Subtype.ext hFuv)
    rw [← IsCartesian.fac X.p f β u, ← IsCartesian.fac X.p f β v]
    exact congrArg (· ≫ β) (congrArg Subtype.val this)

/-- VI.6.10 (full, ⇐): if every `F_S` is full, so is `F`. -/
theorem full_of_fiberwise (h : ∀ S, (fiberMap F S).Full) : F.toFunctor.Full where
  map_surjective {a b} w := by
    let f := baseArrow F w
    obtain ⟨c, β, hβ⟩ := IsPreFibered.exists_isCartesian X.p (rfl : X.p.obj b = _) f
    have hc : X.p.obj c = X.p.obj a := IsHomLift.domain_eq X.p f β
    have : IsCartesian Y.p f (F.map β) := hF.map_isCartesian f β
    let w' := IsCartesian.map Y.p f (F.map β) w
    let A : Fiber X.p (X.p.obj a) := ⟨a, rfl⟩
    let B : Fiber X.p (X.p.obj a) := ⟨c, hc⟩
    obtain ⟨u', hu'⟩ := (h (X.p.obj a)).map_surjective (X := A) (Y := B)
      ⟨w', IsCartesian.map_isHomLift Y.p f (F.map β) w⟩
    refine ⟨u'.val ≫ β, ?_⟩
    have hu'' : F.map u'.val = w' := congrArg Subtype.val hu'
    rw [F.map_comp, hu'']
    exact IsCartesian.fac Y.p f (F.map β) w

/-- VI.6.10 (faithful): for a cartesian functor out of a prefibered category, `F` is
faithful iff every `F_S` is. -/
theorem faithful_iff_fiberwise :
    F.toFunctor.Faithful ↔ ∀ S, (fiberMap F S).Faithful :=
  ⟨fun _ _ ↦ inferInstance, faithful_of_fiberwise F⟩

/-- VI.6.10 (fully faithful): for a cartesian functor out of a prefibered category, `F` is
fully faithful iff every `F_S` is. -/
theorem fullyFaithful_iff_fiberwise :
    (F.toFunctor.Full ∧ F.toFunctor.Faithful) ↔
      ∀ S, (fiberMap F S).Full ∧ (fiberMap F S).Faithful := by
  constructor
  · rintro ⟨_, _⟩ S
    exact ⟨inferInstance, inferInstance⟩
  · intro h
    exact ⟨full_of_fiberwise F (fun S ↦ (h S).1), faithful_of_fiberwise F (fun S ↦ (h S).2)⟩

/-- VI.6.10 (`E`-equivalence): a cartesian functor out of a prefibered category is an
`E`-equivalence iff every `F_S` is an equivalence of categories. -/
theorem isBasedEquivalence_iff_fiberwise_isEquivalence :
    IsBasedEquivalence F ↔ ∀ S, (fiberMap F S).IsEquivalence := by
  constructor
  · intro hF S
    exact ((isBasedEquivalence_iff_fiberwise F).mp hF).2 S
  · intro h
    apply (isBasedEquivalence_iff F).mpr
    refine ⟨full_of_fiberwise F (fun S ↦ inferInstance),
      faithful_of_fiberwise F (fun S ↦ inferInstance), fun y ↦ ?_⟩
    let b : Fiber Y.p (Y.p.obj y) := ⟨y, rfl⟩
    let e := (fiberMap F (Y.p.obj y)).objObjPreimageIso b
    exact ⟨((fiberMap F (Y.p.obj y)).objPreimage b).val, Fiber.fiberInclusion.mapIso e,
      e.hom.property⟩

end SGA.SGA1.ExposeVI
