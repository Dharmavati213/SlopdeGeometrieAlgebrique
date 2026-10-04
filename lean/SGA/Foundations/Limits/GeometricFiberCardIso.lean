/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import SGA.Foundations.Limits.GeometricFiberCard

/-!
# Étale morphisms with one geometric point in each fibre

* `AlgebraicGeometry.Scheme.Hom.geometricFiberCard_eq_one_of_isIso`: an isomorphism has one
  geometric point in each fibre.
* `AlgebraicGeometry.Scheme.Hom.isIso_of_forall_geometricFiberCard_eq_one`: conversely, an étale
  morphism with finite fibres and exactly one geometric point in each fibre is an isomorphism. It
  is surjective and universally injective (its diagonal is surjective), hence an open immersion
  (EGA IV 17.9.1) which is surjective.
* `AlgebraicGeometry.Scheme.Hom.isIso_of_geometricFiberCard_eq_one_of_connectedSpace`: a finite
  étale morphism onto a connected scheme with one geometric point in a single fibre is an
  isomorphism, since the geometric number of points of a finite étale morphism is locally
  constant (`Scheme.Hom.isLocallyConstant_geometricFiberCard`).

## References

* [EGA IV, 17.9.1][ega-iv-4]
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
-/

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- An isomorphism has exactly one geometric point in each fibre. -/
lemma geometricFiberCard_eq_one_of_isIso [IsIso g] (y : Y) : g.geometricFiberCard y = 1 := by
  let t := Y.fromSpecAlgClosure y
  have hfin : (g ⁻¹' {t (closedPoint _)}).Finite := by
    refine Set.Subsingleton.finite fun a ha b hb ↦ ?_
    have : Function.Injective g := (asIso g).hom.homeomorph.injective
    exact this (ha.trans hb.symm)
  have h := g.natCard_pointsOver' t hfin
  rw [Scheme.fromSpecAlgClosure_apply] at h
  rw [← h, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩, ⟨⟨t ≫ inv g, by simp⟩⟩⟩
  rw [← cancel_mono g, a.2, b.2]

-- Without this option, rewriting with `Scheme.Hom.comp_apply` below fails to find the pattern
-- `?g (?f ?x)` in the points of the pullback `X ×_Y X` (the types of the points do not unify at
-- reducible transparency).
set_option backward.isDefEq.respectTransparency.types false in
/-- An étale morphism with finite fibres and exactly one geometric point in each fibre is an
isomorphism. (The hypothesis `LocallyQuasiFinite g` holds for every étale `g`; the instance is
`SGA.SGA1.ExposeI.locallyQuasiFinite_of_formallyUnramified`, which Foundations cannot import.) -/
lemma isIso_of_forall_geometricFiberCard_eq_one [Etale g] [LocallyQuasiFinite g]
    (hfin : ∀ y, (g ⁻¹' {y}).Finite) (h : ∀ y, g.geometricFiberCard y = 1) : IsIso g := by
  have : UniversallyInjective g := by
    rw [UniversallyInjective.iff_diagonal]
    refine ⟨fun w ↦ ?_⟩
    let w' := (pullback g g).fromSpecAlgClosure w
    let t := w' ≫ pullback.fst g g ≫ g
    have hcard := g.natCard_pointsOver' t (hfin _)
    rw [h, Nat.card_eq_one_iff_unique] at hcard
    have hab : (⟨w' ≫ pullback.fst g g, rfl⟩ : g.PointsOver t) =
        ⟨w' ≫ pullback.snd g g, by simp [t, pullback.condition]⟩ := hcard.1.elim _ _
    have hab' : w' ≫ pullback.fst g g = w' ≫ pullback.snd g g := congrArg Subtype.val hab
    have : w' = (w' ≫ pullback.fst g g) ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · simp
      · simp [hab']
    refine ⟨(w' ≫ pullback.fst g g) (closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← this, Scheme.fromSpecAlgClosure_apply]
  -- étale and universally injective: the diagonal is a surjective open immersion
  have : IsIso (pullback.diagonal g) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, (UniversallyInjective.iff_diagonal g).mp inferInstance⟩
  have : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  have : IsOpenImmersion g := IsOpenImmersion.of_flat_of_mono g
  refine (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨x, hx⟩ := g.nonempty_preimage_of_geometricFiberCard_ne_zero y (by rw [h y]; simp)
  exact ⟨x, hx⟩

/-- A finite étale morphism onto a connected scheme with exactly one geometric point in one fibre
is an isomorphism. -/
lemma isIso_of_geometricFiberCard_eq_one_of_connectedSpace [ConnectedSpace Y] [IsFinite g]
    [Etale g] (y₀ : Y) (h : g.geometricFiberCard y₀ = 1) : IsIso g :=
  isIso_of_forall_geometricFiberCard_eq_one g g.finite_preimage_singleton fun y ↦
    (g.isLocallyConstant_geometricFiberCard.apply_eq_of_isPreconnected
      isPreconnected_univ (Set.mem_univ y) (Set.mem_univ y₀)).trans h

end AlgebraicGeometry.Scheme.Hom
