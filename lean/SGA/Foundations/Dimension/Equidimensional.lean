/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import SGA.Foundations.Dimension.FiberDimension

/-!
# Equidimensionality of smooth morphisms

A generalizing map (e.g. a flat morphism of schemes) sends the generic point of every
irreducible component to the generic point of an irreducible component, so every irreducible
component dominates an irreducible component of the target
(`GeneralizingMap.closure_image_mem_irreducibleComponents`,
`AlgebraicGeometry.Scheme.Hom.closure_image_mem_irreducibleComponents_of_flat`).

Consequently a morphism smooth of relative dimension `n` over a locally noetherian scheme is
equidimensional in the sense of SGA 1 II.2 at every point: every point has an open
neighbourhood `U` all of whose irreducible components dominate irreducible components of `Y`,
and such that all irreducible components of all the fibres `f⁻¹(y) ∩ U` have dimension `n`
(`AlgebraicGeometry.Scheme.Hom.exists_equidimensional_nhds_of_smoothOfRelativeDimension`); the
same holds on every affine open `V` on which `f` is standard smooth of relative dimension `n`
over an affine open of `Y`
(`AlgebraicGeometry.Scheme.Hom.equidimensional_of_isStandardSmoothOfRelativeDimension_appLE`).
-/

universe u

open Topology TopologicalSpace

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous generalizing map from a quasi-sober `T₀` space to a quasi-sober space maps
every irreducible component into an irreducible component, densely. -/
theorem GeneralizingMap.closure_image_mem_irreducibleComponents [QuasiSober X] [T0Space X]
    [QuasiSober Y] {f : X → Y} (hc : Continuous f) (hf : GeneralizingMap f) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) : closure (f '' Z) ∈ irreducibleComponents Y := by
  set ζ := hZ.1.genericPoint
  have hζ : closure {ζ} = Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  -- `f ζ` has no proper generalization
  have hmax : ∀ y, y ⤳ f ζ → y = f ζ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hf hy
    have h₁ : Z ⊆ closure {x} := hζ ▸ specializes_iff_closure_subset.mp hx
    have h₂ : closure {x} ⊆ Z := hZ.2 isIrreducible_singleton.closure h₁
    have hxζ : ζ ⤳ x := by
      rw [specializes_iff_mem_closure, hζ]
      exact h₂ (subset_closure rfl)
    rw [(hx.antisymm hxζ).eq]
  have hcl : closure (f '' Z) = closure {f ζ} := by
    refine le_antisymm ?_ (closure_mono (Set.singleton_subset_iff.mpr ⟨ζ, hζ ▸ subset_closure rfl,
      rfl⟩))
    rw [← hζ]
    refine (closure_mono (image_closure_subset_closure_image hc)).trans ?_
    rw [Set.image_singleton, closure_closure]
  rw [hcl]
  refine ⟨isIrreducible_singleton.closure, fun W hW hsub ↦ ?_⟩
  set w := hW.closure.genericPoint
  have hw : closure {w} = closure W := hW.closure.isGenericPoint_genericPoint isClosed_closure
  have hwζ : w ⤳ f ζ := by
    rw [specializes_iff_mem_closure, hw]
    exact subset_closure (hsub (subset_closure rfl))
  rw [← hmax w hwζ, hw]
  exact subset_closure

end Topology

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a flat morphism `f : X ⟶ Y` and an open `U ⊆ X`, every irreducible component of `U`
dominates an irreducible component of `Y`. -/
theorem closure_image_mem_irreducibleComponents_of_flat [Flat f] (U : X.Opens) {Z : Set U}
    (hZ : Z ∈ irreducibleComponents U) :
    closure (f '' (Subtype.val '' Z)) ∈ irreducibleComponents Y := by
  have hg : GeneralizingMap (f ∘ Subtype.val : ↥(U : Set X) → Y) := by
    intro u y hy
    obtain ⟨x', hx', rfl⟩ := Flat.generalizingMap f hy
    exact ⟨⟨x', hx'.mem_open U.2 u.2⟩, IsInducing.subtypeVal.specializes_iff.mp hx', rfl⟩
  have : QuasiSober {x // x ∈ (U : Set X)} := inferInstanceAs (QuasiSober U.toScheme)
  have : T0Space {x // x ∈ (U : Set X)} := inferInstanceAs (T0Space U.toScheme)
  convert hg.closure_image_mem_irreducibleComponents
    (f.continuous.comp continuous_subtype_val) hZ using 2
  exact (Set.image_comp _ _ _).symm

/-- A morphism smooth of relative dimension `n` over a locally noetherian scheme is
equidimensional at every point in the sense of SGA 1 II.2: every point has an open
neighbourhood `U` whose irreducible components dominate irreducible components of `Y`, and such
that every irreducible component of every fibre `f⁻¹(y) ∩ U` has dimension `n`. -/
theorem exists_equidimensional_nhds_of_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian Y] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      (∀ Z ∈ irreducibleComponents U,
        closure (f '' (Subtype.val '' Z)) ∈ irreducibleComponents Y) ∧
      ∀ y : Y, ∀ C ∈ irreducibleComponents ↥(f ⁻¹' {y} ∩ (U : Set X)),
        topologicalKrullDim C = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, hxU, fun Z hZ ↦ closure_image_mem_irreducibleComponents_of_flat f U hZ,
    fun y C hC ↦ ?_⟩
  have : NoetherianSpace (U : Set X) := ‹NoetherianSpace U›
  have : NoetherianSpace ↥(f ⁻¹' {y} ∩ (U : Set X)) :=
    NoetherianSpace.of_subset (W := (U : Set X)) Set.inter_subset_right
  exact topologicalKrullDim_eq_of_mem_irreducibleComponents_preimage_singleton_inter f n U.2 hC

/-- **Equidimensionality of smooth morphisms, pointwise form** (SGA 1 II.2.3, necessity): let
`U ⊆ Y` and `V ⊆ f⁻¹(U)` be affine opens such that `Γ(Y, U) → Γ(X, V)` is standard smooth of
relative dimension `n` (i.e. `f` is smooth of relative dimension `n` on `V`), with `Y` locally
noetherian. Then every irreducible component of `V` dominates an irreducible component of `Y`,
and every irreducible component of every fibre `f⁻¹(y) ∩ V` has dimension `n`. -/
theorem equidimensional_of_isStandardSmoothOfRelativeDimension_appLE [IsLocallyNoetherian Y]
    {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    (∀ Z ∈ irreducibleComponents V,
        closure (f '' (Subtype.val '' Z)) ∈ irreducibleComponents Y) ∧
      ∀ y : Y, ∀ C ∈ irreducibleComponents ↥(f ⁻¹' {y} ∩ (V : Set X)),
        topologicalKrullDim C = n := by
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(X, V) := h
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := Γ(Y, U))
    (S := Γ(X, V)) n
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian (X := Y) ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing Γ(Y, U) Γ(X, V)
  have key : ∀ w, f (hV.fromSpec w) =
      hU.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) w) := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    rfl
  refine ⟨fun Z hZ ↦ ?_, fun y C hC ↦ ?_⟩
  · -- `f` restricted to `V` lifts generalizations, by going down for the flat map `Γ(U) → Γ(V)`
    have hgd : GeneralizingMap (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V))) :=
      Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance
    have hg : GeneralizingMap (f ∘ Subtype.val : ↥(V : Set X) → Y) := by
      rintro ⟨v, hv⟩ y' hy'
      obtain ⟨w, rfl⟩ : v ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
      have hy'U : y' ∈ U := hy'.mem_open U.2 (e hv)
      obtain ⟨p', rfl⟩ : y' ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
      simp only [Function.comp_apply] at hy'
      rw [key] at hy'
      have hy'' : p' ⤳ PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) w :=
        hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hy'
      obtain ⟨w', hw', hw'p⟩ := hgd hy''
      have hw'V : hV.fromSpec w' ∈ (V : Set X) := by
        rw [← hV.range_fromSpec]
        exact Set.mem_range_self _
      refine ⟨⟨hV.fromSpec w', hw'V⟩, ?_, ?_⟩
      · exact IsInducing.subtypeVal.specializes_iff.mp
          (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mpr hw')
      · exact (key w').trans (congrArg hU.fromSpec hw'p)
    have : QuasiSober {x // x ∈ (V : Set X)} := inferInstanceAs (QuasiSober V.toScheme)
    have : T0Space {x // x ∈ (V : Set X)} := inferInstanceAs (T0Space V.toScheme)
    convert hg.closure_image_mem_irreducibleComponents
      (f.continuous.comp continuous_subtype_val) hZ using 2
    exact (Set.image_comp _ _ _).symm
  · have : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
    have : NoetherianSpace (V : Set X) := ‹NoetherianSpace V›
    have : NoetherianSpace ↥(f ⁻¹' {y} ∩ (V : Set X)) :=
      NoetherianSpace.of_subset (W := (V : Set X)) Set.inter_subset_right
    refine topologicalKrullDim_eq_of_mem_irreducibleComponents (fun z ↦ ?_) hC
    obtain ⟨z, hzy, hzV⟩ := z
    rw [topologicalKrullDimAt_inter_of_isOpen (s := f ⁻¹' {y}) V.isOpen ⟨z, hzy, hzV⟩]
    obtain rfl : f z = y := hzy
    exact (fiberDimAt_eq f z).symm.trans
      (fiberDimAt_eq_of_isStandardSmoothOfRelativeDimension_appLE f hU hV e n h hzV)

end AlgebraicGeometry.Scheme.Hom
