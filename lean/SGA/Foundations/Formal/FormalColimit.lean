/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# Colimits of thickenings of schemes

A *thickening sequence* is a sequence of schemes `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` whose transition maps are
closed immersions which are homeomorphisms, for instance `Xₙ = Spec (A ⧸ I ^ (n + 1))`, or the
infinitesimal neighbourhoods of a closed subscheme. Its colimit in the category of locally
ringed spaces is the formal scheme `𝔛 = lim→ Xₙ` (EGA I, §10.6): the underlying space is
that of `X₀` and the structure sheaf is `lim← 𝒪_{Xₙ}`.

Mathlib's `LocallyRingedSpace` has all colimits, computed in `SheafedSpace`
(`LocallyRingedSpace.preservesColimits_forgetToSheafedSpace`), so the colimit is automatically a
locally ringed space and the maps `Xₙ ⟶ 𝔛` are morphisms of locally ringed spaces.

## Main definitions and results

* `AlgebraicGeometry.Scheme.IsThickeningSequence F`: the transition maps of `F : ℕ ⥤ Scheme` are
  surjective closed immersions.
* `AlgebraicGeometry.Scheme.formalColimit F`: the colimit of `F` in `LocallyRingedSpace`.
* `AlgebraicGeometry.Scheme.formalColimit.homeomorph`: `Xₙ ≃ₜ 𝔛` for every `n`.
* `AlgebraicGeometry.Scheme.formalColimit.isLimitΓ`: `Γ(𝔛) = lim← Γ(Xₙ)`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

instance : PreservesColimitsOfSize.{0, 0} LocallyRingedSpace.forgetToSheafedSpace.{u} :=
  preservesSmallestColimits_of_preservesColimits _

instance : PreservesColimitsOfSize.{0, 0} (SheafedSpace.forget.{_, _, u} CommRingCat.{u}) :=
  preservesSmallestColimits_of_preservesColimits _

instance : PreservesColimitsOfShape ℕ LocallyRingedSpace.forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape ℕ
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _))

/-- `Γ` turns colimits of locally ringed spaces into limits of rings, being a left adjoint
`LocallyRingedSpace ⥤ CommRingCatᵒᵖ`. -/
instance : PreservesColimitsOfSize.{0, 0} LocallyRingedSpace.Γ.{u}.rightOp :=
  have : PreservesColimits LocallyRingedSpace.Γ.{u}.rightOp :=
    ΓSpec.locallyRingedSpaceAdjunction.{u}.leftAdjoint_preservesColimits
  preservesSmallestColimits_of_preservesColimits _

namespace Scheme

/-- A sequence `X₀ ⟶ X₁ ⟶ ⋯` of schemes is a *thickening sequence* if every transition map
`Xₙ ⟶ Xₙ₊₁` is a surjective closed immersion, i.e. identifies `Xₙ` with a closed subscheme of
`Xₙ₊₁` with the same underlying space. -/
class IsThickeningSequence (F : ℕ ⥤ Scheme.{u}) : Prop where
  isClosedImmersion (n : ℕ) : IsClosedImmersion (F.map (homOfLE n.le_succ))
  surjective (n : ℕ) : Surjective (F.map (homOfLE n.le_succ))

namespace IsThickeningSequence

variable (F : ℕ ⥤ Scheme.{u}) [IsThickeningSequence F]

lemma isClosedImmersion_and_surjective {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (F.map (homOfLE h)) ∧ Surjective (F.map (homOfLE h)) := by
  induction n, h using Nat.le_induction with
  | base => simp only [homOfLE_refl, F.map_id]; exact ⟨inferInstance, inferInstance⟩
  | succ n hmn ih =>
    obtain ⟨h₁, h₂⟩ := ih
    have := IsThickeningSequence.isClosedImmersion (F := F) n
    have := IsThickeningSequence.surjective (F := F) n
    rw [← homOfLE_comp hmn n.le_succ, F.map_comp]
    exact ⟨inferInstance, inferInstance⟩

instance {m n : ℕ} (f : m ⟶ n) : IsClosedImmersion (F.map f) :=
  (isClosedImmersion_and_surjective F (leOfHom f)).1

instance {m n : ℕ} (f : m ⟶ n) : Surjective (F.map f) :=
  (isClosedImmersion_and_surjective F (leOfHom f)).2

/-- The transition maps of a thickening sequence are homeomorphisms. -/
instance isIso_forgetToTop_map {m n : ℕ} (f : m ⟶ n) :
    IsIso (Scheme.forgetToTop.map (F.map f)) :=
  TopCat.isIso_of_bijective_of_isClosedMap _
    ⟨(F.map f).isClosedEmbedding.injective, (F.map f).surjective⟩
    (F.map f).isClosedEmbedding.isClosedMap

end IsThickeningSequence

variable (F : ℕ ⥤ Scheme.{u})

/-- The colimit `𝔛 = lim→ Xₙ` of a sequence of schemes, in locally ringed spaces. For a
thickening sequence this is the formal scheme defined by the `Xₙ` (EGA I, §10.6). -/
noncomputable def formalColimit : LocallyRingedSpace.{u} :=
  colimit (F ⋙ Scheme.forgetToLocallyRingedSpace)

namespace formalColimit

/-- The canonical morphism `Xₙ ⟶ 𝔛`. -/
noncomputable def ι (n : ℕ) : (F.obj n).toLocallyRingedSpace ⟶ formalColimit F :=
  colimit.ι (F ⋙ Scheme.forgetToLocallyRingedSpace) n

@[reassoc (attr := simp)]
lemma w {m n : ℕ} (f : m ⟶ n) : (F.map f).toLRSHom ≫ ι F n = ι F m :=
  colimit.w (F ⋙ Scheme.forgetToLocallyRingedSpace) f

/-- Morphisms out of `𝔛 = lim→ Xₙ` are compatible families of morphisms out of the `Xₙ`. -/
noncomputable def desc {Y : LocallyRingedSpace.{u}}
    (f : ∀ n, (F.obj n).toLocallyRingedSpace ⟶ Y)
    (hf : ∀ n, (F.map (homOfLE n.le_succ)).toLRSHom ≫ f (n + 1) = f n) :
    formalColimit F ⟶ Y :=
  colimit.desc (F ⋙ Scheme.forgetToLocallyRingedSpace)
    { pt := Y
      ι := NatTrans.ofSequence (F := F ⋙ Scheme.forgetToLocallyRingedSpace)
        (G := (Functor.const ℕ).obj Y) f fun n ↦ (hf n).trans (Category.comp_id (f n)).symm }

@[reassoc (attr := simp)]
lemma ι_desc {Y : LocallyRingedSpace.{u}} (f : ∀ n, (F.obj n).toLocallyRingedSpace ⟶ Y)
    (hf : ∀ n, (F.map (homOfLE n.le_succ)).toLRSHom ≫ f (n + 1) = f n) (n : ℕ) :
    ι F n ≫ desc F f hf = f n :=
  colimit.ι_desc _ n

@[ext]
lemma hom_ext {Y : LocallyRingedSpace.{u}} {g g' : formalColimit F ⟶ Y}
    (h : ∀ n, ι F n ≫ g = ι F n ≫ g') : g = g' :=
  colimit.hom_ext h

/-- The cone `Γ(𝔛) ⟶ Γ(Xₙ)` of restriction maps. -/
noncomputable def Γcone : Cone (F.op ⋙ Scheme.Γ) :=
  LocallyRingedSpace.Γ.mapCone (colimit.cocone (F ⋙ Scheme.forgetToLocallyRingedSpace)).op

/-- `Γ(𝔛) = lim← Γ(Xₙ)`: global sections turn the colimit `𝔛 = lim→ Xₙ` into a limit, since
`Γ` is left adjoint to `Spec` (as functors `LocallyRingedSpace ⥤ CommRingCatᵒᵖ`). -/
noncomputable def isLimitΓcone : IsLimit (Γcone F) :=
  isLimitConeOfCoconeRightOp ((F ⋙ Scheme.forgetToLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ)
    (isColimitOfPreserves LocallyRingedSpace.Γ.rightOp
      (colimit.isColimit (F ⋙ Scheme.forgetToLocallyRingedSpace)))

variable [IsThickeningSequence F]

/-- The maps `Xₙ ⟶ 𝔛` are homeomorphisms. -/
instance isIso_forgetToTop_map_ι (n : ℕ) :
    IsIso (LocallyRingedSpace.forgetToTop.map (ι F n)) := by
  let G := F ⋙ Scheme.forgetToLocallyRingedSpace
  let H := LocallyRingedSpace.forgetToTop.{u}
  have hG {i j : ℕ} (f : i ⟶ j) : IsIso ((G ⋙ H).map f) :=
    IsThickeningSequence.isIso_forgetToTop_map F f
  have h₀ : IsIso (colimit.ι (G ⋙ H) 0) := isIso_ι_of_isInitial isInitialBot _
  have hn : IsIso (colimit.ι (G ⋙ H) n) := by
    rw [← colimit.w (G ⋙ H) (homOfLE (Nat.zero_le n))] at h₀
    exact IsIso.of_isIso_comp_left ((G ⋙ H).map (homOfLE (Nat.zero_le n))) _
  change IsIso (H.map (colimit.ι G n))
  rw [← ι_preservesColimitIso_inv H G n]
  infer_instance

/-- The underlying space of `𝔛 = lim→ Xₙ` is that of any `Xₙ`. -/
noncomputable def homeomorph (n : ℕ) : F.obj n ≃ₜ formalColimit F :=
  TopCat.homeoOfIso (@asIso _ _ _ _ (LocallyRingedSpace.forgetToTop.map (ι F n))
    (isIso_forgetToTop_map_ι F n))

end formalColimit

end Scheme

end AlgebraicGeometry
