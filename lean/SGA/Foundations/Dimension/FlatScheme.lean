/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import SGA.Foundations.Dimension.FlatFiber
import SGA.Foundations.Dimension.Scheme

/-!
# The dimension formula for flat morphisms of schemes

Let `f : X ⟶ Y` be flat and locally of finite type, with `Y` locally noetherian, `x ∈ X` and
`y = f(x)`. Then (EGA IV §6.1; SGA 1 II (3.1))

* `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_add_of_flat`:
  `dim 𝒪_{X,x} = dim 𝒪_{Y,y} + dim 𝒪_{f⁻¹(y),x}` (and
  `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_add_of_flat_appLE`, assuming flatness only
  on an affine open containing `x`);
* `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_flat`:
  `dim 𝒪_{X,x} + trdeg_{κ(y)} κ(x) = dim 𝒪_{Y,y} + dim_x f⁻¹(y)`, i.e.
  `dim 𝒪_x = dim 𝒪_y + n - d` with `n` the dimension of the fibre at `x` and `d` the
  transcendence degree of `κ(x)` over `κ(y)`.

The proof computes all three dimensions as heights of points for the specialization order, and
reduces to the algebraic formula `PrimeSpectrum.height_eq_height_comap_add_height_fiber` on
affine opens.
-/

universe u

open Order Topology CategoryTheory

/-- The coheight of `a` in a subset `s` containing every element above `a` is its coheight. -/
theorem Order.coheight_subtype_of_forall_le_mem {α : Type*} [Preorder α] {s : Set α} {a : α}
    (ha : a ∈ s) (hs : ∀ b, a ≤ b → b ∈ s) : coheight (⟨a, ha⟩ : s) = coheight a := by
  refine le_antisymm (coheight_le_coheight_apply_of_strictMono Subtype.val (fun _ _ h ↦ h) _)
    (coheight_le fun l hl ↦ ?_)
  have hmem : ∀ i, l i ∈ s := fun i ↦ hs _ (hl ▸ l.monotone (Fin.zero_le i))
  let l' : LTSeries s := LTSeries.mk l.length (fun i ↦ ⟨l i, hmem i⟩) (fun _ _ h ↦ l.strictMono h)
  exact length_le_coheight (p := l') (x := ⟨a, ha⟩) (le_of_eq (Subtype.ext hl.symm))

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The fibre scheme of `f` over `y` is order-isomorphic (for the specialization orders) to the
fibre `f⁻¹(y) ⊆ X`. -/
noncomputable def Scheme.Hom.fiberOrderIso (f : X ⟶ Y) (y : Y) : f.fiber y ≃o f ⁻¹' {y} where
  toEquiv := (f.fiberHomeo y).toEquiv
  map_rel_iff' {a b} := by
    change f.fiberι y b ⤳ f.fiberι y a ↔ b ⤳ a
    exact (f.fiberι y).isEmbedding.isInducing.specializes_iff

/-- For an affine open `V` of `X`, the height of a point `x ∈ V` in `X` is the height of its
prime ideal in `Γ(X, V)`. -/
theorem IsAffineOpen.coheight_eq_height_primeIdealOf {V : X.Opens} (hV : IsAffineOpen V)
    {x : X} (hx : x ∈ V) : coheight x = height (hV.primeIdealOf ⟨x, hx⟩) := by
  have h := coheight_eq_of_isOpenImmersion (x := hV.primeIdealOf ⟨x, hx⟩) hV.fromSpec
  rw [hV.fromSpec_primeIdealOf] at h
  rw [h]
  exact (idealHeight_eq_coheight Γ(X, V) (hV.primeIdealOf ⟨x, hx⟩)).symm.trans
    (PrimeSpectrum.height_eq_orderHeight _)

namespace Scheme.Hom

/-- Heights in the fibre of `f` agree with heights in the fibres of `Spec Γ(X, V) → Spec Γ(Y, U)`
for affine opens `U` and `V ≤ f⁻¹(U)`. -/
theorem coheight_asFiber_eq_height_fiber (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) :
    letI := (f.appLE U V e).hom.toAlgebra
    coheight (f.asFiber x) = height (⟨hV.primeIdealOf ⟨x, hx⟩, rfl⟩ :
      PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) ⁻¹'
        {PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) (hV.primeIdealOf ⟨x, hx⟩)}) := by
  let := (f.appLE U V e).hom.toAlgebra
  set φ := PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V))
  set z := hV.primeIdealOf ⟨x, hx⟩
  have hz : hV.fromSpec z = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  have key : ∀ w, f (hV.fromSpec w) = hU.fromSpec (φ w) := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    rfl
  -- the fibre scheme and the set-theoretic fibre
  have h₁ : coheight (f.asFiber x) = coheight (⟨x, rfl⟩ : f ⁻¹' {f x}) := by
    rw [← coheight_orderIso (f.fiberOrderIso (f x))]
    congr 1
    exact (f.fiberHomeo (f x)).apply_symm_apply _
  -- generalizations of `x` lie in `V`
  set s : Set (f ⁻¹' {f x}) := {t | t.1 ∈ V}
  have h₂ : coheight (⟨⟨x, rfl⟩, hx⟩ : s) = coheight (⟨x, rfl⟩ : f ⁻¹' {f x}) :=
    coheight_subtype_of_forall_le_mem (s := s) hx fun b hb ↦ (show b.1 ⤳ x from hb).mem_open V.2 hx
  -- the part of the fibre in `V` is the fibre of `Spec Γ(X, V) → Spec Γ(Y, U)`
  set G := φ ⁻¹' {φ z}
  have hmem : ∀ g : G, f (hV.fromSpec g.1) = f x := fun g ↦
    (key g.1).trans ((congrArg hU.fromSpec (show φ g.1 = φ z from g.2)).trans
      ((key z).symm.trans (congrArg f hz)))
  have hrange : ∀ w, hV.fromSpec w ∈ V := fun w ↦ by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact Set.mem_range_self w
  let Ψ₀ : Gᵒᵈ → s := fun g ↦ ⟨⟨hV.fromSpec (OrderDual.ofDual g).1, hmem _⟩, hrange _⟩
  have hΨ : ∀ a b, Ψ₀ a ≤ Ψ₀ b ↔ a ≤ b := by
    intro a b
    change hV.fromSpec (OrderDual.ofDual b).1 ⤳ hV.fromSpec (OrderDual.ofDual a).1 ↔
      (OrderDual.ofDual b).1 ≤ (OrderDual.ofDual a).1
    exact hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.trans
      (PrimeSpectrum.le_iff_specializes _ _).symm
  let Ψ := OrderEmbedding.ofMapLEIff Ψ₀ hΨ
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨⟨t, ht⟩, htV⟩
    obtain ⟨g, rfl⟩ : t ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact htV
    have hg : φ g = φ z := by
      apply hU.fromSpec.isOpenEmbedding.injective
      exact (key g).symm.trans (ht.trans ((congrArg f hz).symm.trans (key z)))
    exact ⟨OrderDual.toDual ⟨g, hg⟩, rfl⟩
  have h₃ : coheight (⟨⟨x, rfl⟩, hx⟩ : s) = height (⟨z, rfl⟩ : G) := by
    rw [← coheight_toDual, ← coheight_orderIso (OrderIso.ofSurjective Ψ hsurj)]
    congr 1
    exact Subtype.ext (Subtype.ext hz.symm)
  rw [h₁, ← h₂, h₃]

/-- **Dimension formula for flat morphisms**, local form: let `U ⊆ Y` and `V ⊆ f⁻¹(U)` be affine
opens with noetherian rings of sections such that `Γ(Y, U) → Γ(X, V)` is flat (i.e. `f` is flat
on `V`). Then for `x ∈ V`, `dim 𝒪_{X,x} = dim 𝒪_{Y,f(x)} + dim 𝒪_{f⁻¹(f(x)),x}`. -/
theorem ringKrullDim_stalk_eq_add_of_flat_appLE (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    [IsNoetherianRing Γ(Y, U)] [IsNoetherianRing Γ(X, V)]
    (hflat : (f.appLE U V e).hom.Flat) {x : X} (hxV : x ∈ V) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) +
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let := (f.appLE U V e).hom.toAlgebra
  have : Module.Flat Γ(Y, U) Γ(X, V) := hflat
  set z := hV.primeIdealOf ⟨x, hxV⟩
  have hfx : hU.primeIdealOf ⟨f x, e hxV⟩ = PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) z :=
    (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hxV).symm
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
    ringKrullDim_stalk_eq_coheight, ← WithBot.coe_add, WithBot.coe_inj,
    hV.coheight_eq_height_primeIdealOf hxV, hU.coheight_eq_height_primeIdealOf (e hxV), hfx,
    coheight_asFiber_eq_height_fiber f hU hV e hxV]
  exact PrimeSpectrum.height_eq_height_comap_add_height_fiber z

/-- **Dimension formula for flat morphisms** (EGA IV §6.1; SGA 1 II (3.1)): if `f` is flat and
locally of finite type and `Y` is locally noetherian, then
`dim 𝒪_{X,x} = dim 𝒪_{Y,f(x)} + dim 𝒪_{f⁻¹(f(x)),x}`. -/
theorem ringKrullDim_stalk_eq_add_of_flat (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) +
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).2
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian (X := Y) ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian (X := X) ⟨V, hV⟩
  exact ringKrullDim_stalk_eq_add_of_flat_appLE f hU hV hVU
    (HasRingHomProperty.appLE @Flat f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ hVU) hxV

/-- **The dimension formula (3.1) of SGA 1 II** (EGA IV §6.1): if `f` is flat and locally of
finite type and `Y` is locally noetherian, then for `x ∈ X`,
`dim 𝒪_{X,x} + trdeg_{κ(f(x))} κ(x) = dim 𝒪_{Y,f(x)} + dim_x f⁻¹(f(x))`. -/
theorem ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_flat (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + (f.residueFieldTrdeg x).toENat =
      ringKrullDim (Y.presheaf.stalk (f x)) + f.fiberDimAt x := by
  rw [ringKrullDim_stalk_eq_add_of_flat f x, add_assoc,
    fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg f x]

end Scheme.Hom

end AlgebraicGeometry
