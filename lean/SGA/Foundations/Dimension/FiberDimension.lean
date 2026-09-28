/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Dimension.Scheme
import SGA.Foundations.Dimension.Semicontinuity

/-!
# Upper semicontinuity of the dimension of the fibres

For a morphism of schemes `f : X ⟶ Y` locally of finite type, the function
`x ↦ dim_x (f⁻¹(f(x)))` is upper semicontinuous (Chevalley; EGA IV 13.1.3, Stacks Project,
Tag 02FZ): `AlgebraicGeometry.Scheme.Hom.isOpen_setOf_fiberDimAt_le`. The proof reduces to the
affine case `PrimeSpectrum.isOpen_setOf_fiberDimAt_le`, through
`AlgebraicGeometry.Scheme.Hom.fiberDimAt_fromSpec`.
-/

universe u

open CategoryTheory Topology

/-- **SGA 1 II.1.5**, algebraic form: if `B` is standard smooth of relative dimension `n` over
`A`, all fibres of `Spec B → Spec A` have dimension `n` at every point. -/
theorem Algebra.IsStandardSmoothOfRelativeDimension.fiberDimAt_eq {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (n : ℕ) [IsStandardSmoothOfRelativeDimension n A B]
    (z : PrimeSpectrum B) : PrimeSpectrum.fiberDimAt A z = n := by
  set p := PrimeSpectrum.comap (algebraMap A B) z
  rw [PrimeSpectrum.fiberDimAt,
    ← (PrimeSpectrum.preimageHomeomorphFiber A B p).topologicalKrullDimAt_eq]
  exact IsStandardSmoothOfRelativeDimension.topologicalKrullDimAt_eq p.asIdeal.ResidueField n _

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- On affine opens `U ⊆ Y`, `V ⊆ f⁻¹(U)`, the dimension of the fibres of `f` agrees with the
dimension of the fibres of `Spec Γ(X, V) → Spec Γ(Y, U)`. -/
theorem fiberDimAt_fromSpec (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) (z : PrimeSpectrum Γ(X, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    f.fiberDimAt (hV.fromSpec z) = PrimeSpectrum.fiberDimAt Γ(Y, U) z := by
  let := (f.appLE U V e).hom.toAlgebra
  have key : ∀ z, f (hV.fromSpec z) =
      hU.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    rfl
  rw [fiberDimAt_eq, PrimeSpectrum.fiberDimAt]
  refine (hV.fromSpec.isOpenEmbedding.topologicalKrullDimAt_preimage_singleton
    (φ := PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V))) (f := f) (fun z₁ z₂ ↦ ?_) z).symm
  rw [key, key]
  exact hU.fromSpec.isOpenEmbedding.injective.eq_iff.symm

/-- **SGA 1 II.1.5**, pointwise form: if on affine opens `U ⊆ Y`, `V ⊆ f⁻¹(U)` the ring map
`Γ(Y, U) → Γ(X, V)` is standard smooth of relative dimension `n` (i.e. `f` is smooth of relative
dimension `n` on `V`), then the fibres of `f` have dimension `n` at every point of `V`. -/
theorem fiberDimAt_eq_of_isStandardSmoothOfRelativeDimension_appLE (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) {z : X} (hz : z ∈ V) :
    f.fiberDimAt z = n := by
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(X, V) := h
  have h₁ := fiberDimAt_fromSpec f hU hV e (hV.primeIdealOf ⟨z, hz⟩)
  rw [hV.fromSpec_primeIdealOf] at h₁
  rw [h₁]
  exact Algebra.IsStandardSmoothOfRelativeDimension.fiberDimAt_eq n _

/-- **Chevalley's semicontinuity theorem** (EGA IV 13.1.3; Stacks Project, Tag 02FZ): for a
morphism `f` locally of finite type, `x ↦ dim_x (f⁻¹(f(x)))` is upper semicontinuous. -/
theorem isOpen_setOf_fiberDimAt_le (f : X ⟶ Y) [LocallyOfFiniteType f] (n : WithBot ℕ∞) :
    IsOpen {x : X | f.fiberDimAt x ≤ n} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).2
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  have e : V ≤ f ⁻¹ᵁ U := hVU
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  refine ⟨hV.fromSpec '' {z | PrimeSpectrum.fiberDimAt Γ(Y, U) z ≤ n}, ?_,
    hV.fromSpec.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.isOpen_setOf_fiberDimAt_le n), ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change f.fiberDimAt (hV.fromSpec z) ≤ n
    rw [fiberDimAt_fromSpec f hU hV e z]
    exact hz
  · refine ⟨hV.primeIdealOf ⟨x, hxV⟩, ?_, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
    change PrimeSpectrum.fiberDimAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩) ≤ n
    rw [← fiberDimAt_fromSpec f hU hV e, hV.fromSpec_primeIdealOf]
    exact hx

end AlgebraicGeometry.Scheme.Hom
