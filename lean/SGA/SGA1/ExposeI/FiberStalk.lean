/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Stalk

/-!
# The local rings of a fibre

Let `f : X ⟶ Y`, `y ∈ Y`, and let `z` be a point of the fibre `X_y = X ×_Y Spec κ(y)`, with image
`x` in `X`. The stalk map `𝒪_{X,x} → 𝒪_{X_y,z}` of `X_y ⟶ X` is surjective with kernel
`𝔪_y 𝒪_{X,x}` (`ker_stalkMap_fiberι`, EGA I 3.6.5): the local ring of the fibre is
`𝒪_{X,x} / 𝔪_y 𝒪_{X,x}`. This is used for the fibrewise criteria I.5.7–I.5.9.

The kernel contains `𝔪_y 𝒪_{X,x}` because `X_y ⟶ Y` factors through `Spec κ(y)`, whose local
rings are fields. Conversely the morphism `Spec (𝒪_{X,x} / 𝔪_y 𝒪_{X,x}) ⟶ X_y` given by the
universal property of the fibre product sends the closed point to `z`, and the reduction map
`𝒪_{X,x} → 𝒪_{X,x} / 𝔪_y 𝒪_{X,x}` factors through `𝒪_{X_y,z}`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace SGA.SGA1.ExposeI

variable {X Y : Scheme.{u}}

lemma apply_fiberι (f : X ⟶ Y) (y : Y) (z : f.fiber y) : f (f.fiberι y z) = y := by
  have : f.fiberι y z ∈ f ⁻¹' {y} := f.range_fiberι y ▸ Set.mem_range_self z
  exact this

lemma stalkClosedPointTo_congr {R : CommRingCat.{u}} [IsLocalRing R] {g₁ g₂ : Spec R ⟶ X}
    (e : g₁ = g₂) :
    Scheme.stalkClosedPointTo g₁ =
      (X.presheaf.stalkCongr (.of_eq (by rw [e]))).hom ≫ Scheme.stalkClosedPointTo g₂ := by
  subst e
  simp [TopCat.Presheaf.stalkCongr_hom]

set_option backward.isDefEq.respectTransparency false in
lemma stalkClosedPointTo_SpecMap_fromSpecStalk {R : CommRingCat.{u}} [IsLocalRing R] {x : X}
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (.of_eq (by
        rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]))).hom ≫
        φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  rw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- If `ι ∘ h' = Spec φ ∘ (Spec 𝒪_{ι z} → X)` with `h'` sending the closed point to `z`, then `φ`
kills the kernel of the stalk map of `ι` at `z`. -/
lemma apply_eq_zero_of_stalkMap_eq_zero {T : Scheme.{u}} (ι : T ⟶ X) {R : CommRingCat.{u}}
    [IsLocalRing R] (h' : Spec R ⟶ T) (z : T) (φ : X.presheaf.stalk (ι z) ⟶ R)
    [IsLocalHom φ.hom] (hz : h' (closedPoint R) = z)
    (hh' : h' ≫ ι = Spec.map φ ≫ X.fromSpecStalk (ι z)) (a : X.presheaf.stalk (ι z))
    (ha : (ι.stalkMap z).hom a = 0) : φ.hom a = 0 := by
  subst hz
  have key := Scheme.stalkClosedPointTo_comp h' ι
  rw [stalkClosedPointTo_congr hh', stalkClosedPointTo_SpecMap_fromSpecStalk] at key
  have := congr(($key).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero] at this
  convert this using 2
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `f.fiberι y` at `z` factors the reduction modulo `𝔪_y`. -/
lemma ker_stalkMap_fiberι_le (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    RingHom.ker ((f.fiberι y).stalkMap z).hom ≤
      (maximalIdeal (Y.presheaf.stalk (f (f.fiberι y z)))).map (f.stalkMap (f.fiberι y z)).hom := by
  set x := f.fiberι y z
  have hy : f x = y := apply_fiberι f y z
  set J := (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom
  have hJ : J ≤ maximalIdeal (X.presheaf.stalk x) := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ map_nonunit _ a ha
  have : Nontrivial (X.presheaf.stalk x ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJ)
  have : IsLocalRing (X.presheaf.stalk x ⧸ J) :=
    .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{u} := .of (X.presheaf.stalk x ⧸ J)
  let mk : X.presheaf.stalk x ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hsp : f x ⤳ y := hy ▸ specializes_rfl
  let φ : Y.presheaf.stalk y ⟶ Q := Y.presheaf.stalkSpecializes hsp ≫ f.stalkMap x ≫ mk
  have hφ : ∀ a ∈ maximalIdeal (Y.presheaf.stalk y), φ.hom a = 0 := by
    intro a ha
    have : IsLocalHom (Y.presheaf.stalkSpecializes hsp).hom :=
      inferInstanceAs (IsLocalHom (Y.presheaf.stalkCongr (.of_eq hy.symm)).hom.hom)
    change Ideal.Quotient.mk J _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ (map_nonunit _ _ ha)
  let θ : Y.residueField y ⟶ Q := CommRingCat.ofHom
    (Ideal.Quotient.lift (maximalIdeal (Y.presheaf.stalk y)) φ.hom hφ)
  have hθ : Y.residue y ≫ θ = φ := by
    ext a
    rfl
  let h₁ : Spec Q ⟶ X := Spec.map mk ≫ X.fromSpecStalk x
  have w : h₁ ≫ f = Spec.map θ ≫ Y.fromSpecResidueField y := by
    simp only [h₁, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hθ]
  let h' : Spec Q ⟶ f.fiber y := pullback.lift h₁ (Spec.map θ) w
  have hh' : h' ≫ f.fiberι y = h₁ := pullback.lift_fst _ _ _
  have : IsLocalHom mk.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcp : h₁ (closedPoint Q) = x := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hz : h' (closedPoint Q) = z := (f.fiberι y).isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hh', hcp])
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact apply_eq_zero_of_stalkMap_eq_zero (f.fiberι y) h' z mk hz hh' a ha

/-- The stalks of `Spec κ(y)` are fields. -/
lemma maximalIdeal_stalk_spec_residueField (y : Y) (p : Spec (Y.residueField y)) :
    maximalIdeal ((Spec (Y.residueField y)).presheaf.stalk p) = ⊥ := by
  have hsub (q r : Spec (Y.residueField y)) : q = r := by
    have := q.isPrime
    have := r.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans
      (Ideal.eq_bot_of_prime r.asIdeal).symm)
  have hp : closure {p} ∈ irreducibleComponents (Spec (Y.residueField y)) := by
    have : closure ({p} : Set (Spec (Y.residueField y))) = Set.univ :=
      Set.eq_univ_of_forall fun q ↦ subset_closure (hsub q p)
    rw [this, irreducibleComponents_eq_singleton]
    rfl
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp
    (isField_stalk_of_closure_mem_irreducibleComponents _ p hp)

/-- A morphism which factors through `Spec κ(y)` kills the maximal ideals of the stalks of `Y`. -/
lemma map_maximalIdeal_stalkMap_eq_bot {T : Scheme.{u}} (φ : T ⟶ Y) (y : Y)
    (g : T ⟶ Spec (Y.residueField y)) (e : φ = g ≫ Y.fromSpecResidueField y) (z : T) :
    (maximalIdeal (Y.presheaf.stalk (φ z))).map (φ.stalkMap z).hom = ⊥ := by
  subst e
  rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_bot,
    show (g ≫ Y.fromSpecResidueField y).stalkMap z =
      (Y.fromSpecResidueField y).stalkMap (g z) ≫ g.stalkMap z from Scheme.Hom.stalkMap_comp _ _ _]
  have hb := map_nonunit ((Y.fromSpecResidueField y).stalkMap (g z)).hom a ha
  rw [maximalIdeal_stalk_spec_residueField, Ideal.mem_bot] at hb
  change (g.stalkMap z).hom (((Y.fromSpecResidueField y).stalkMap (g z)).hom a) = 0
  rw [hb, map_zero]

/-- The stalk of a fibre: the stalk map `𝒪_{X,x} → 𝒪_{X_y,z}` of `f.fiberι y` at a point `z` of
the fibre (with `x` its image in `X`) is surjective with kernel `𝔪_y 𝒪_{X,x}`
(EGA I 3.6.5). -/
theorem ker_stalkMap_fiberι (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    RingHom.ker ((f.fiberι y).stalkMap z).hom =
      (maximalIdeal (Y.presheaf.stalk (f (f.fiberι y z)))).map (f.stalkMap (f.fiberι y z)).hom := by
  refine le_antisymm (ker_stalkMap_fiberι_le f y z) fun a ha ↦ ?_
  have h := map_maximalIdeal_stalkMap_eq_bot (f.fiberι y ≫ f) y _ (f.fiber_fac y) z
  have hcomp : ((f.fiberι y ≫ f).stalkMap z).hom =
      ((f.fiberι y).stalkMap z).hom.comp (f.stalkMap (f.fiberι y z)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp _ _ _)
  have h2 : ((maximalIdeal (Y.presheaf.stalk (f (f.fiberι y z)))).map
      (f.stalkMap (f.fiberι y z)).hom).map ((f.fiberι y).stalkMap z).hom = ⊥ := by
    rw [Ideal.map_map, ← hcomp]
    exact h
  rw [RingHom.mem_ker, ← Ideal.mem_bot, ← h2]
  exact Ideal.mem_map_of_mem _ ha

/-- The stalk map of `f.fiberι y` at `z` is surjective. -/
lemma stalkMap_fiberι_surjective (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    Function.Surjective ((f.fiberι y).stalkMap z) :=
  (f.fiberι y).stalkMap_surjective z

/-- The local ring of the fibre `X_y` at `z` is `𝒪_{X,x} / 𝔪_y 𝒪_{X,x}`, `x` the image of `z`. -/
noncomputable def stalkFiberEquiv (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    X.presheaf.stalk (f.fiberι y z) ⧸
        (maximalIdeal (Y.presheaf.stalk (f (f.fiberι y z)))).map (f.stalkMap (f.fiberι y z)).hom ≃+*
      (f.fiber y).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (ker_stalkMap_fiberι f y z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (stalkMap_fiberι_surjective f y z))

lemma stalkFiberEquiv_mk (f : X ⟶ Y) (y : Y) (z : f.fiber y) (a : X.presheaf.stalk (f.fiberι y z)) :
    stalkFiberEquiv f y z (Ideal.Quotient.mk _ a) = ((f.fiberι y).stalkMap z).hom a :=
  rfl

end SGA.SGA1.ExposeI
