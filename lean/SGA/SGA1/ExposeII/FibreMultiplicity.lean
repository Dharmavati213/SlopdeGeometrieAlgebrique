/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.Depth

/-!
# SGA 1, Exposé II, II.2.4–II.2.6: components of multiplicity one

SGA calls an irreducible component `Z` of a fibre `f⁻¹(y)`, with generic point `x`, *of
multiplicity 1* if (i) `dim 𝒪_x = dim 𝒪_y` and (ii) `𝔪_y 𝒪_x = 𝔪_x`. II.2.6 says that for `f`
dominant of finite type between reduced schemes and `𝒪_y` regular, `f` is smooth at the points
over `y` iff the components of `f⁻¹(y)` have multiplicity 1 and `f⁻¹(y)_red` is smooth over `κ(y)`.

We prove the necessity at the generic points of the fibre, without the hypotheses on `Y`
(`ringKrullDim_stalk_eq_and_map_maximalIdeal_eq_of_mem_smoothLocus`): it follows from the
dimension formula for flat morphisms and the regularity of the fibre.

Not formalized: the sufficiency, which rests on Hironaka's II.2.5 (EGA IV 5.12.10: a fibre
whose components have multiplicity 1 and whose reduction is normal is reduced, and `X` is normal
and flat over `Y` along it), and the remarks II.2.4 on geometrically unibranch points.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace SGA.SGA1.ExposeII

variable {X Y : Scheme.{u}}

/-- A regular local ring of dimension `0` is a field: its maximal ideal is zero. -/
lemma maximalIdeal_eq_bot_of_ringKrullDim_eq_zero {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R = 0) : maximalIdeal R = ⊥ := by
  have h' := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [h] at h'
  have : (maximalIdeal R).spanFinrank = 0 := by exact_mod_cast h'
  exact (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp this

private lemma map_maximalIdeal_aux (f : X ⟶ Y) (y : Y) (z : f.fiber y) (x : X)
    (h : f.fiberι y z = x) (hF : maximalIdeal ((f.fiber y).presheaf.stalk z) = ⊥) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) := by
  subst h
  refine le_antisymm ?_ fun a ha ↦ ?_
  · rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  · rw [← ExposeI.ker_stalkMap_fiberι, RingHom.mem_ker, ← Ideal.mem_bot, ← hF]
    have hs := ExposeI.stalkMap_fiberι_surjective f y z
    have := map_maximalIdeal_of_surjective ((f.fiberι y).stalkMap z).hom hs
    rw [← this]
    exact Ideal.mem_map_of_mem _ ha

/-- **II.2.6, necessity**: let `f : X ⟶ Y` be locally of finite presentation, `Y` locally
noetherian, and `x` a point where `f` is smooth which is the generic point of an irreducible
component of its fibre `f⁻¹(y)`, `y = f(x)` (i.e. `dim 𝒪_{f⁻¹(y),x} = 0`). Then this component has
multiplicity `1` in the sense of SGA: (i) `dim 𝒪_x = dim 𝒪_y`, and (ii) `𝔪_y 𝒪_x = 𝔪_x`. (The
fibre is moreover smooth over `κ(y)` at `x`, `Scheme.asFiber_mem_smoothLocus`, hence reduced
there.) -/
theorem ringKrullDim_stalk_eq_and_map_maximalIdeal_eq_of_mem_smoothLocus (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian Y] {x : X} (hx : x ∈ f.smoothLocus)
    (h0 : ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = 0) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) ∧
      (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
        maximalIdeal (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isRegularLocalRing_stalk_fiber_of_mem_smoothLocus f hx
  refine ⟨?_, map_maximalIdeal_aux f (f x) (f.asFiber x) x (Scheme.Hom.fiberι_asFiber f x)
    (maximalIdeal_eq_bot_of_ringKrullDim_eq_zero h0)⟩
  rw [ringKrullDim_stalk_eq_add_of_flat_at f x (flat_stalkMap_of_mem_smoothLocus f hx), h0,
    add_zero]

end SGA.SGA1.ExposeII
