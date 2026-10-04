/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Sections of a product of schemes over a field over a product of affine opens

Let `k` be a field and `P`, `Q` schemes over `Spec k`. The sections of `P ×ₖ Q` over the
"box" `V ⊠ V' = pr₁⁻¹ V ∩ pr₂⁻¹ V'` of affine opens `V ⊆ P`, `V' ⊆ Q` are the tensor product
`Γ(P, V) ⊗ₖ Γ(Q, V')`: the multiplication map `a ⊗ b ↦ pr₁^* a · pr₂^* b`
(`AlgebraicGeometry.OverField.mulTensor`) is bijective (`OverField.bijective_mulTensor`; this is
mathlib's `isIso_pushoutSection_of_isAffineOpen`, rewritten over `k`). The box of two affine opens
is affine (`OverField.isAffineOpen_box`).

The `k`-algebra structure on `Γ(X, V)` for `X` over `Spec k` is the scoped instance
`OverField.sectionsAlgebra` (`open scoped AlgebraicGeometry.OverField`); the maps induced by
morphisms over `Spec k` and the restriction maps are `k`-algebra maps (`OverField.appLEAlgHom`,
`OverField.resAlgHom`).

## References

* [A. Grothendieck, J. Dieudonné, *EGA* I 3.2.6][EGA]
* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR)
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open TensorProduct

namespace AlgebraicGeometry.OverField

variable {k : Type u} [Field k]

lemma le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens) : V ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ ↦ trivial

/-- The `k`-algebra structure on the sections of a scheme over `Spec k`. -/
noncomputable scoped instance sectionsAlgebra (X : Over (Spec (.of k))) (V : X.left.Opens) :
    Algebra k Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ V (le_preimage_top _ _)).hom.toAlgebra

lemma algebraMap_eq (X : Over (Spec (.of k))) (V : X.left.Opens) :
    algebraMap k Γ(X.left, V) = ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ V (le_preimage_top _ _)).hom :=
  rfl

/-- The map on sections induced by a morphism over `Spec k`, as a `k`-algebra map. -/
noncomputable def appLEAlgHom {X Y : Over (Spec (.of k))} (g : X ⟶ Y) (V : Y.left.Opens)
    (V' : X.left.Opens) (h : V' ≤ g.left ⁻¹ᵁ V) : Γ(Y.left, V) →ₐ[k] Γ(X.left, V') where
  __ := (g.left.appLE V V' h).hom
  commutes' a := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appLE ⊤ V (le_preimage_top _ _)) ≫ g.left.appLE V V' h) a =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ V' (le_preimage_top _ _)) a
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, Over.w]

@[simp]
lemma appLEAlgHom_apply {X Y : Over (Spec (.of k))} (g : X ⟶ Y) (V : Y.left.Opens)
    (V' : X.left.Opens) (h : V' ≤ g.left ⁻¹ᵁ V) (a : Γ(Y.left, V)) :
    appLEAlgHom g V V' h a = g.left.appLE V V' h a :=
  rfl

/-- Restriction of sections, as a `k`-algebra map. -/
noncomputable def resAlgHom (X : Over (Spec (.of k))) {V V' : X.left.Opens} (h : V' ≤ V) :
    Γ(X.left, V) →ₐ[k] Γ(X.left, V') where
  __ := (X.left.presheaf.map (homOfLE h).op).hom
  commutes' a := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ V (le_preimage_top _ _)) ≫
      X.left.presheaf.map (homOfLE h).op) a =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appLE ⊤ V' (le_preimage_top _ _)) a
    rw [Category.assoc, Scheme.Hom.appLE_map]

@[simp]
lemma resAlgHom_apply (X : Over (Spec (.of k))) {V V' : X.left.Opens} (h : V' ≤ V)
    (a : Γ(X.left, V)) : resAlgHom X h a = X.left.presheaf.map (homOfLE h).op a :=
  rfl

variable (P Q : Over (Spec (.of k)))

/-- The box `V ⊠ V' = pr₁⁻¹ V ∩ pr₂⁻¹ V'` in `P ×ₖ Q`. -/
noncomputable def box (V : P.left.Opens) (V' : Q.left.Opens) : (P ⊗ Q).left.Opens :=
  (fst P Q).left ⁻¹ᵁ V ⊓ (snd P Q).left ⁻¹ᵁ V'

variable {P Q}

lemma box_mono {V₁ V₂ : P.left.Opens} {V₁' V₂' : Q.left.Opens} (h : V₂ ≤ V₁) (h' : V₂' ≤ V₁') :
    box P Q V₂ V₂' ≤ box P Q V₁ V₁' :=
  inf_le_inf ((fst P Q).left.preimage_mono h) ((snd P Q).left.preimage_mono h')

lemma box_le_fst (V : P.left.Opens) (V' : Q.left.Opens) :
    box P Q V V' ≤ (fst P Q).left ⁻¹ᵁ V :=
  inf_le_left

lemma box_le_snd (V : P.left.Opens) (V' : Q.left.Opens) :
    box P Q V V' ≤ (snd P Q).left ⁻¹ᵁ V' :=
  inf_le_right

/-- The multiplication map `Γ(P, V) ⊗ₖ Γ(Q, V') → Γ(P ×ₖ Q, V ⊠ V')`, `a ⊗ b ↦ pr₁^* a · pr₂^* b`. -/
noncomputable def mulTensor (V : P.left.Opens) (V' : Q.left.Opens) :
    Γ(P.left, V) ⊗[k] Γ(Q.left, V') →ₐ[k] Γ((P ⊗ Q).left, box P Q V V') :=
  Algebra.TensorProduct.productMap (appLEAlgHom (fst P Q) V _ (box_le_fst V V'))
    (appLEAlgHom (snd P Q) V' _ (box_le_snd V V'))

lemma mulTensor_tmul (V : P.left.Opens) (V' : Q.left.Opens) (a : Γ(P.left, V))
    (b : Γ(Q.left, V')) :
    mulTensor V V' (a ⊗ₜ b) = (fst P Q).left.appLE V _ (box_le_fst V V') a *
      (snd P Q).left.appLE V' _ (box_le_snd V V') b :=
  rfl

lemma isPullback_fst_snd (P Q : Over (Spec (.of k))) :
    IsPullback (fst P Q).left (snd P Q).left P.hom Q.hom :=
  IsPullback.of_hasPullback P.hom Q.hom

/-- The box of two affine opens is affine. -/
lemma isAffineOpen_box {V : P.left.Opens} {V' : Q.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') : IsAffineOpen (box P Q V V') := by
  have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top (Spec (.of k))
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  exact .of_isIso (Scheme.Hom.isPullback_resLE (isPullback_fst_snd P Q)
    (US := ⊤) (UT := V') (UX := V) (UY := box P Q V V') (le_preimage_top _ _) (le_preimage_top _ _) rfl).isoPullback.hom

/-- **Sections over a box of affine opens** (EGA I 3.2.6): for `V ⊆ P`, `V' ⊆ Q` affine, the
multiplication map `Γ(P, V) ⊗ₖ Γ(Q, V') → Γ(P ×ₖ Q, V ⊠ V')` is bijective. -/
theorem bijective_mulTensor {V : P.left.Opens} {V' : Q.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') : Function.Bijective (mulTensor V V') := by
  have H0 := (isIso_pushoutSection_iff (isPullback_fst_snd P Q) (US := ⊤) (UT := V') (UX := V)
    (UY := box P Q V V') (le_preimage_top _ _) (le_preimage_top _ _) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen _ _ _ _ (isAffineOpen_top _) hV' hV)
  have H : IsPushout (CommRingCat.ofHom (algebraMap k Γ(P.left, V)))
      (CommRingCat.ofHom (algebraMap k Γ(Q.left, V')))
      ((fst P Q).left.appLE V (box P Q V V') (box_le_fst V V'))
      ((snd P Q).left.appLE V' (box P Q V V') (box_le_snd V V')) :=
    H0.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [algebraMap_eq]; simp) (by rw [algebraMap_eq]; simp) (by simp) (by simp)
  let e := IsPushout.isoIsPushout _ _
    (CommRingCat.isPushout_tensorProduct k Γ(P.left, V) Γ(Q.left, V')) H
  have he : ∀ x, e.hom x = mulTensor V V' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h1 := ConcreteCategory.congr_hom (IsPushout.inl_isoIsPushout_hom _ _
        (CommRingCat.isPushout_tensorProduct k Γ(P.left, V) Γ(Q.left, V')) H) a
      have h2 := ConcreteCategory.congr_hom (IsPushout.inr_isoIsPushout_hom _ _
        (CommRingCat.isPushout_tensorProduct k Γ(P.left, V) Γ(Q.left, V')) H) b
      simp only [CommRingCat.comp_apply] at h1 h2
      have : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : Γ(Q.left, V'))) * ((1 : Γ(P.left, V)) ⊗ₜ[k] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul]
      erw [h1, h2]
      rw [← this, mulTensor_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hb : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  exact (funext he : (e.hom : _ → _) = mulTensor V V') ▸ hb

end AlgebraicGeometry.OverField
