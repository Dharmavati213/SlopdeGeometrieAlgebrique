/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric connectedness descends along surjective base change

* `AlgebraicGeometry.GeometricallyConnected.of_pullback_snd`: let `f : X ⟶ S` and `φ : T ⟶ S`
  surjective. If the base change `X ×_S T ⟶ T` is geometrically connected, so is `f`. For a field
  `K` and `Spec K ⟶ S`, a point of `T ×_S Spec K` gives a field `Ω ⊇ K` with `Spec Ω ⟶ T`; then
  `X ×_S Spec Ω` is connected and maps onto `X ×_S Spec K`. In particular geometric connectedness
  over a field `k` can be checked after any field extension `K ⊇ k` (EGA IV 4.5.1).
* `AlgebraicGeometry.GeometricallyConnected.of_isPullback`: the same for any cartesian square.
* `AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback`: geometric
  connectedness of the fibres is invariant under base change, `X_t = X_{g t} ⊗_{κ(g t)} κ(t)`.

## References

* [EGA IV₂, 4.5.1][EGA4]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Geometric connectedness descends along a surjective base change: if `φ : T ⟶ S` is surjective
and `X ×_S T ⟶ T` is geometrically connected, then `f : X ⟶ S` is geometrically connected
(EGA IV 4.5.1 for `S` the spectrum of a field). -/
theorem GeometricallyConnected.of_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (φ : T ⟶ S)
    [Surjective φ] [GeometricallyConnected (pullback.snd f φ)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  -- a field `Ω` with `Spec Ω ⟶ T` and `Spec Ω ⟶ Spec K` over `S`
  obtain ⟨y₀⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨t, ht⟩ := φ.surjective (y y₀)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := y) t y₀ ht
  let w := (pullback φ y).fromSpecResidueField z
  let a := w ≫ pullback.snd φ y
  let b := w ≫ pullback.fst φ y
  have hab : b ≫ φ = a ≫ y := by simp only [a, b, Category.assoc, pullback.condition]
  -- `X ×_S Spec Ω` is connected
  have h₁ : IsPullback (pullback.fst (pullback.snd f y) a ≫ pullback.fst f y)
      (pullback.snd (pullback.snd f y) a) f (a ≫ y) :=
    (IsPullback.of_hasPullback (pullback.snd f y) a).paste_horiz (IsPullback.of_hasPullback f y)
  let ℓ : pullback (pullback.snd f y) a ⟶ pullback f φ :=
    pullback.lift (pullback.fst (pullback.snd f y) a ≫ pullback.fst f y)
      (pullback.snd (pullback.snd f y) a ≫ b) (by simpa only [Category.assoc, hab] using h₁.w)
  have h₂ : IsPullback ℓ (pullback.snd (pullback.snd f y) a) (pullback.snd f φ) b := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f φ)
    rw [pullback.lift_fst, hab]
    exact h₁
  have : ConnectedSpace ↥(pullback (pullback.snd f y) a) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h₂
  -- it maps onto `X ×_S Spec K`
  have : Surjective a := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.fst (pullback.snd f y) a) := inferInstance
  exact (pullback.fst (pullback.snd f y) a).surjective.connectedSpace
    (pullback.fst (pullback.snd f y) a).continuous

/-- Geometric connectedness descends along a surjective base change, for any cartesian square
`P = X ×_S T`: if `P ⟶ T` is geometrically connected and `φ : T ⟶ S` surjective, then `f` is
geometrically connected. -/
theorem GeometricallyConnected.of_isPullback {X S T P : Scheme.{u}} {f : X ⟶ S} {φ : T ⟶ S}
    {e : P ⟶ X} {q : P ⟶ T} (h : IsPullback e q f φ) [Surjective φ] [GeometricallyConnected q] :
    GeometricallyConnected f := by
  have : GeometricallyConnected (pullback.snd f φ) :=
    MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso (fst := h.isoPullback.inv)
      (g := 𝟙 T) ⟨by rw [h.isoPullback_inv_snd, Category.comp_id]⟩) ‹GeometricallyConnected q›
  exact GeometricallyConnected.of_pullback_snd f φ

/-- Geometric connectedness of a fibre is invariant under extension of the residue field: for a
cartesian square `P = X ×_S T` and `t ∈ T`, the fibre of `P ⟶ T` at `t` is geometrically connected
iff the fibre of `X ⟶ S` at the image of `t` is. -/
theorem geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback {X S T P : Scheme.{u}}
    {f : X ⟶ S} {g : T ⟶ S} {e : P ⟶ X} {q : P ⟶ T} (h : IsPullback e q f g) (t : T) :
    GeometricallyConnected (q.fiberToSpecResidueField t) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (g t)) := by
  have sq := isPullback_fiberToSpecResidueField_of_isPullback h t
  refine ⟨fun h₁ ↦ ?_, fun h₂ ↦ MorphismProperty.of_isPullback sq h₂⟩
  have : Surjective (Spec.map (g.residueFieldMap t)) :=
    ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact @GeometricallyConnected.of_isPullback _ _ _ _ _ _ _ _ sq _ h₁

end AlgebraicGeometry
