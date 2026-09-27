/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Flat base change of scheme-theoretic images

For a quasi-compact morphism `f : X ⟶ S`, the kernel `f.ker` is the ideal sheaf of the
scheme-theoretic image of `f`. We show that `X ⟶ f.image` is scheme-theoretically dominant and
that the scheme-theoretic image commutes with flat base change: for `g : S' ⟶ S` flat,
`f.ker.comap g = (pullback.fst g f).ker` ([Stacks, Tag 081I]).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y S S' : Scheme.{u}}

/-- A quasi-compact morphism is scheme-theoretically dominant onto its scheme-theoretic image. -/
instance Scheme.Hom.isSchemeTheoreticallyDominant_toImage (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U, U.2.preimage _⟩) ?_ fun U ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

/-- The scheme-theoretic image of a quasi-compact morphism commutes with flat base change:
the inverse image of `f.ker` along a flat `g : S' ⟶ S` is the kernel of the base change
`S' ×_S X ⟶ S'`. -/
@[stacks 081I]
lemma Scheme.Hom.ker_comap_of_flat (f : X ⟶ S) [QuasiCompact f] (g : S' ⟶ S) [Flat g] :
    f.ker.comap g = (pullback.fst g f).ker := by
  let a : pullback g f ⟶ pullback g f.imageι :=
    pullback.map g f g f.imageι (𝟙 _) f.toImage (𝟙 _) (by simp) (by simp [f.toImage_imageι])
  have ha : a ≫ pullback.fst g f.imageι = pullback.fst g f := pullback.lift_fst _ _ _
  have H : IsPullback (pullback.snd g f) a f.toImage (pullback.snd g f.imageι) := by
    refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback g f.imageι)).flip
    rw [ha, f.toImage_imageι]
    exact .of_hasPullback g f
  have : IsSchemeTheoreticallyDominant a := .of_isPullback H
  rw [← ha, Scheme.Hom.ker_comp, a.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rfl

end AlgebraicGeometry
