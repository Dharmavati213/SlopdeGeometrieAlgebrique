/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatDepth
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Dimension.Scheme
import SGA.SGA1.ExposeI.FiberStalk
import SGA.SGA1.ExposeII.Criteria
import SGA.SGA1.ExposeII.PermanenceSmooth

/-!
# SGA 1, Exposé II, formulas (3.1)–(3.2): depth and codepth

After II.3.1, SGA notes that if `f : X ⟶ Y` is smooth at `x` and `y = f(x)`, then
`dim 𝒪_x = dim 𝒪_y + n - d` and `prof 𝒪_x = prof 𝒪_y + n - d` (3.1), where `n` is the dimension
of the fibre at `x` and `d = trdeg_{κ(y)} κ(x)`. Hence `coprof 𝒪_x = coprof 𝒪_y` (3.2), and
`𝒪_x` is Cohen–Macaulay iff `𝒪_y` is. We prove:

* `depth_stalk_eq_add_of_flat`: if `f` is flat at `x`,
  `depth 𝒪_x = depth 𝒪_y + depth 𝒪_{f⁻¹(y),x}` (EGA IV 6.3.1), together with the dimension
  formula `dim 𝒪_x = dim 𝒪_y + dim 𝒪_{f⁻¹(y),x}` at a single flat point;
* for `f` smooth at `x`, the local ring of the fibre is regular, so
  `depth 𝒪_x = depth 𝒪_y + dim 𝒪_{f⁻¹(y),x}` and, in the form of (3.1),
  `depth 𝒪_x + d = depth 𝒪_y + n`;
* (3.2): `𝒪_x` and `𝒪_y` have the same codepth, and `𝒪_x` is Cohen–Macaulay iff `𝒪_y` is.

Depth is `Ideal.depth` of the maximal ideal. Cohen–Macaulay is written as
`depth = ringKrullDim`. Not formalized: the "without embedded components" clause of the remark.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace SGA.SGA1.ExposeII

variable {X Y : Scheme.{u}}

/-- II.2.1, necessity, pointwise: if `f` is smooth at `x`, then `𝒪_{f(x)} → 𝒪_x` is flat. -/
theorem flat_stalkMap_of_mem_smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] {x : X}
    (hx : x ∈ f.smoothLocus) : (f.stalkMap x).hom.Flat := by
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  obtain ⟨p, rfl⟩ : ∃ p : f.smoothLocus.toScheme, f.smoothLocus.ι p = x := ⟨⟨x, hx⟩, rfl⟩
  refine (RingHom.Flat.respectsIso.cancel_right_isIso (f.stalkMap (f.smoothLocus.ι p))
    (f.smoothLocus.ι.stalkMap p)).mp ?_
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact Flat.stalkMap (f.smoothLocus.ι ≫ f) p

private theorem depth_and_ringKrullDim_aux (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (y : Y) (z : f.fiber y) (x : X) (h : f.fiberι y z = x)
    (hf : (f.stalkMap x).hom.Flat) :
    (maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) =
        (maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) +
          (maximalIdeal ((f.fiber y).presheaf.stalk z)).depth ((f.fiber y).presheaf.stalk z) ∧
      ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim ((f.fiber y).presheaf.stalk z) := by
  subst h
  algebraize [(f.stalkMap (f.fiberι y z)).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f (f.fiberι y z)))
      (X.presheaf.stalk (f.fiberι y z))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap _).hom)
  exact ⟨depth_eq_add_of_flat (ExposeI.stalkMap_fiberι_surjective f y z)
      (ExposeI.ker_stalkMap_fiberι f y z),
    ringKrullDim_eq_add_of_flat (ExposeI.stalkMap_fiberι_surjective f y z)
      (ExposeI.ker_stalkMap_fiberι f y z)⟩

/-- II, formula (3.1), depth part, for `f` flat at `x` (EGA IV 6.3.1): with `y = f(x)`,
`depth 𝒪_x = depth 𝒪_y + depth 𝒪_{f⁻¹(y),x}`. -/
theorem depth_stalk_eq_add_of_flat (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (x : X) (hf : (f.stalkMap x).hom.Flat) :
    (maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) =
      (maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) +
        (maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x))).depth
          ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  (depth_and_ringKrullDim_aux f (f x) (f.asFiber x) x (Scheme.Hom.fiberι_asFiber f x) hf).1

/-- II, formula (3.1), dimension part, for `f` flat at the single point `x` (EGA IV 6.1.1): with
`y = f(x)`, `dim 𝒪_x = dim 𝒪_y + dim 𝒪_{f⁻¹(y),x}`. (For `f` flat everywhere this is
`Scheme.Hom.ringKrullDim_stalk_eq_add_of_flat`.) -/
theorem ringKrullDim_stalk_eq_add_of_flat_at (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (x : X) (hf : (f.stalkMap x).hom.Flat) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) +
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  (depth_and_ringKrullDim_aux f (f x) (f.asFiber x) x (Scheme.Hom.fiberι_asFiber f x) hf).2

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` is smooth at `x`, the local ring of `x` in its fibre is regular (II.2.1 and II.3.1
over the field `κ(f(x))`). -/
theorem isRegularLocalRing_stalk_fiber_of_mem_smoothLocus (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {x : X} (hx : x ∈ f.smoothLocus) :
    IsRegularLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  refine ((permanence_of_mem_smoothLocus (f.fiberToSpecResidueField (f x)) (f.asFiber x)
    (asFiber_mem_smoothLocus f hx)).2.1).mpr ?_
  refine .of_spanFinrank_maximalIdeal_le _ ?_
  rw [ExposeI.maximalIdeal_stalk_spec_residueField, Submodule.spanFinrank_bot]
  exact_mod_cast ringKrullDim_nonneg_of_nontrivial

section Smooth

variable (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsLocallyNoetherian Y] {x : X}
  (hx : x ∈ f.smoothLocus)

include hx

/-- II, formula (3.1), depth part, for `f` smooth at `x`: with `y = f(x)`,
`depth 𝒪_x = depth 𝒪_y + dim 𝒪_{f⁻¹(y),x}`. -/
theorem depth_stalk_eq_add_ringKrullDim_of_mem_smoothLocus :
    ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) =
      ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isRegularLocalRing_stalk_fiber_of_mem_smoothLocus f hx
  rw [depth_stalk_eq_add_of_flat f x (flat_stalkMap_of_mem_smoothLocus f hx), WithBot.coe_add,
    IsRegularLocalRing.depth_eq_ringKrullDim (R := (f.fiber (f x)).presheaf.stalk (f.asFiber x))]

/-- II, formula (3.1), depth part, as stated in SGA: if `f` is smooth at `x`, `y = f(x)`, `n` is
the dimension of the fibre `f⁻¹(y)` at `x` and `d = trdeg_{κ(y)} κ(x)`, then
`prof 𝒪_x = prof 𝒪_y + n - d`, i.e. `depth 𝒪_x + d = depth 𝒪_y + n`. -/
theorem depth_stalk_add_residueFieldTrdeg_eq_of_mem_smoothLocus :
    ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) +
        (f.residueFieldTrdeg x).toENat =
      ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) +
        f.fiberDimAt x := by
  rw [depth_stalk_eq_add_ringKrullDim_of_mem_smoothLocus f hx, add_assoc,
    Scheme.Hom.fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg f x]

/-- II, formula (3.1), dimension part, for `f` smooth at `x` (pointwise; for `f` smooth everywhere
see `ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_smooth`): `dim 𝒪_x + d = dim 𝒪_y + n`. -/
theorem ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_mem_smoothLocus :
    ringKrullDim (X.presheaf.stalk x) + (f.residueFieldTrdeg x).toENat =
      ringKrullDim (Y.presheaf.stalk (f x)) + f.fiberDimAt x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [ringKrullDim_stalk_eq_add_of_flat_at f x (flat_stalkMap_of_mem_smoothLocus f hx), add_assoc,
    Scheme.Hom.fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg f x]

private theorem codepth_aux (c : ℕ) :
    (ringKrullDim (X.presheaf.stalk x) =
        ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) +
          ((c : ℕ∞) : WithBot ℕ∞) ↔
      ringKrullDim (Y.presheaf.stalk (f x)) =
        ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) +
          ((c : ℕ∞) : WithBot ℕ∞)) ∧
    (((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) ↔
      ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) =
        ringKrullDim (Y.presheaf.stalk (f x))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hreg := isRegularLocalRing_stalk_fiber_of_mem_smoothLocus f hx
  suffices ∀ (y : Y) (z : f.fiber y) (x : X) (_ : f.fiberι y z = x)
      (_ : (f.stalkMap x).hom.Flat) (_ : IsRegularLocalRing ((f.fiber y).presheaf.stalk z)),
      (ringKrullDim (X.presheaf.stalk x) =
          ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) +
            ((c : ℕ∞) : WithBot ℕ∞) ↔
        ringKrullDim (Y.presheaf.stalk (f x)) =
          ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) +
            ((c : ℕ∞) : WithBot ℕ∞)) ∧
      (((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk x) ↔
        ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) =
          ringKrullDim (Y.presheaf.stalk (f x))) from
    this (f x) (f.asFiber x) x (Scheme.Hom.fiberι_asFiber f x)
      (flat_stalkMap_of_mem_smoothLocus f hx) hreg
  intro y z x h hf _
  subst h
  algebraize [(f.stalkMap (f.fiberι y z)).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f (f.fiberι y z)))
      (X.presheaf.stalk (f.fiberι y z))) :=
    inferInstanceAs (IsLocalHom (f.stalkMap _).hom)
  have hs := ExposeI.stalkMap_fiberι_surjective f y z
  have hk := ExposeI.ker_stalkMap_fiberι f y z
  refine ⟨ringKrullDim_eq_depth_add_iff_of_flat hs hk
    IsRegularLocalRing.depth_eq_ringKrullDim c, ?_⟩
  rw [depth_eq_ringKrullDim_iff_of_flat hs hk]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, IsRegularLocalRing.depth_eq_ringKrullDim⟩⟩

/-- II, formula (3.2): if `f` is smooth at `x` and `y = f(x)`, then `coprof 𝒪_x = coprof 𝒪_y`:
for every `c : ℕ`, `dim 𝒪_x = depth 𝒪_x + c` iff `dim 𝒪_y = depth 𝒪_y + c`. -/
theorem ringKrullDim_stalk_eq_depth_add_iff_of_mem_smoothLocus (c : ℕ) :
    ringKrullDim (X.presheaf.stalk x) =
        ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) +
          ((c : ℕ∞) : WithBot ℕ∞) ↔
      ringKrullDim (Y.presheaf.stalk (f x)) =
        ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) +
          ((c : ℕ∞) : WithBot ℕ∞) :=
  (codepth_aux f hx c).1

/-- Consequence of (3.2): if `f` is smooth at `x`, then `𝒪_x` is Cohen–Macaulay iff `𝒪_{f(x)}`
is. -/
theorem depth_eq_ringKrullDim_stalk_iff_of_mem_smoothLocus :
    ((maximalIdeal (X.presheaf.stalk x)).depth (X.presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) ↔
      ((maximalIdeal (Y.presheaf.stalk (f x))).depth (Y.presheaf.stalk (f x)) : WithBot ℕ∞) =
        ringKrullDim (Y.presheaf.stalk (f x)) :=
  (codepth_aux f hx 0).2

end Smooth

end SGA.SGA1.ExposeII
