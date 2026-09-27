/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import SGA.Foundations.Fields.GeometricallyReduced

/-!
# Geometrically reduced schemes over a field

We compare mathlib's `AlgebraicGeometry.GeometricallyReduced` (all base changes to fields are
reduced) with `Algebra.IsGeometricallyReduced` for affine schemes over a field.

## Main results

- `AlgebraicGeometry.geometricallyReduced_spec_iff`: `Spec A → Spec k` is geometrically reduced
  iff `A` is a geometrically reduced `k`-algebra.
- `AlgebraicGeometry.geometricallyReduced_iff_of_openCover`: geometric reducedness is local on
  the source.
- `AlgebraicGeometry.GeometricallyReduced.of_perfectField`: over a perfect field, every reduced
  scheme is geometrically reduced.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- `Spec A → Spec k` is geometrically reduced iff `A` is a geometrically reduced `k`-algebra
(EGA IV 4.6.2). -/
theorem geometricallyReduced_spec_iff :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
      Algebra.IsGeometricallyReduced k A := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms,
    Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  refine forall_congr' fun K ↦ ⟨fun h _ _ ↦ ?_, fun h _ _ ↦ ?_⟩
  · have := h
    have : IsReduced (Spec (.of (A ⊗[k] K))) :=
      (ObjectProperty.prop_of_iso _ (pullbackSpecIso k A K) this)
    have := (affine_isReduced_iff _).mp this
    exact isReduced_of_injective (Algebra.TensorProduct.comm k K A).toAlgHom
      (Algebra.TensorProduct.comm k K A).injective
  · have := h
    have : _root_.IsReduced (A ⊗[k] K) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k A K).toAlgHom
        (Algebra.TensorProduct.comm k A K).injective
    exact ObjectProperty.prop_of_iso _ (pullbackSpecIso k A K).symm
      ((affine_isReduced_iff (.of (A ⊗[k] K))).mpr this)

/-- Over a perfect field, the spectrum of a reduced algebra is geometrically reduced. -/
theorem geometricallyReduced_spec_of_perfectField [PerfectField k] [_root_.IsReduced A] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  geometricallyReduced_spec_iff.mpr (.of_perfectField k A)

section Cover

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Geometric reducedness can be checked on an open cover of the source. -/
theorem GeometricallyReduced.of_openCover (𝒰 : X.OpenCover)
    (h : ∀ i, GeometricallyReduced (𝒰.f i ≫ f)) : GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have (i : (Scheme.Pullback.openCoverOfLeft 𝒰 f y).I₀) :
      IsReduced ((Scheme.Pullback.openCoverOfLeft 𝒰 f y).X i) :=
    pullback_of_geometrically (h i).geometrically_isReduced K y
  exact IsReduced.of_openCover (𝒰 := Scheme.Pullback.openCoverOfLeft 𝒰 f y)

/-- Geometric reducedness is inherited by open subschemes of the source. -/
theorem GeometricallyReduced.comp_of_isOpenImmersion {U : Scheme.{u}} (g : U ⟶ X)
    [IsOpenImmersion g] [GeometricallyReduced f] : GeometricallyReduced (g ≫ f) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : IsReduced (pullback f y) :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K y
  exact isReduced_of_isOpenImmersion
    (pullback.map (g ≫ f) y f y g (𝟙 _) (𝟙 _) (by simp) (by simp))

/-- Geometric reducedness is local on the source. -/
theorem geometricallyReduced_iff_of_openCover (𝒰 : X.OpenCover) :
    GeometricallyReduced f ↔ ∀ i, GeometricallyReduced (𝒰.f i ≫ f) :=
  ⟨fun _ _ ↦ GeometricallyReduced.comp_of_isOpenImmersion f _,
    GeometricallyReduced.of_openCover f 𝒰⟩

/-- Over a perfect field, every reduced scheme is geometrically reduced (EGA IV 4.6.1). -/
theorem GeometricallyReduced.of_perfectField {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [IsReduced X] : GeometricallyReduced f := by
  refine GeometricallyReduced.of_openCover f X.affineOpenCover.openCover fun i ↦ ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
  have : IsOpenImmersion (X.affineOpenCover.f i) := X.affineOpenCover.map_prop i
  have : IsReduced (Spec (X.affineOpenCover.X i)) :=
    isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
  have := (affine_isReduced_iff _).mp this
  algebraize [φ.hom]
  change GeometricallyReduced (X.affineOpenCover.f i ≫ f)
  rw [← hφ]
  exact geometricallyReduced_spec_of_perfectField
    (k := k) (A := X.affineOpenCover.X i)

end Cover

end AlgebraicGeometry
