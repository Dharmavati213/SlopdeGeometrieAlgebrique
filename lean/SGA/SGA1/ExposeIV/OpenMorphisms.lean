/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import SGA.SGA1.ExposeIV.Constructible
import SGA.SGA1.ExposeIV.FaithfullyFlat

/-!
# SGA 1, Exposé IV, §6: flat morphisms are open

* IV.6.5: a morphism of finite type over a noetherian base maps the neighbourhoods of `x` to
  neighbourhoods of `f x` iff every generization of `f x` lifts to a generization of `x`. We prove
  it for affine schemes, i.e. for `Spec B → Spec A` with `B` of finite type over `A` noetherian;
  the scheme form is `image_mem_nhds_iff_forall_specializes_of_locallyOfFiniteType` in `Schemes`.
* IV.6.6: if `F` is a coherent sheaf on `X` with support `X`, flat over `Y`, then `f` is open.
  We prove the affine statement for a finite `B`-module `M` flat over `A` with support
  `Spec B`, and the scheme statement for `F = 𝒪_X`, where mathlib gives the stronger conclusion
  (remark after IV.6.6) that `f` is universally open. The scheme statement for a coherent `F` is
  `isOpenMap_of_flatAt` in `CoherentModules`.
-/

universe u

namespace SGA.SGA1.ExposeIV

open Topology Set TopologicalSpace PrimeSpectrum

section Affine

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- IV.6.5 (affine case): let `A` be noetherian and `B` a finitely generated `A`-algebra. The
map `f : Spec B → Spec A` sends every neighbourhood of `x` to a neighbourhood of `f x` if and only
if every generization of `f x` is the image of a generization of `x`. -/
theorem image_mem_nhds_iff_forall_specializes [IsNoetherianRing A] [Algebra.FiniteType A B]
    (x : PrimeSpectrum B) :
    (∀ V ∈ 𝓝 x, comap (algebraMap A B) '' V ∈ 𝓝 (comap (algebraMap A B) x)) ↔
      ∀ y', y' ⤳ comap (algebraMap A B) x → ∃ x', x' ⤳ x ∧ comap (algebraMap A B) x' = y' := by
  have hfp : (algebraMap A B).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finiteType.1 ‹_›)
  set f := comap (algebraMap A B)
  have hcont : Continuous f := continuous_comap _
  constructor
  · intro h y' hy'
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    -- decompose `f⁻¹(closure {y'})` into finitely many irreducible closed sets
    obtain ⟨S, hSf, hSc, hSi, hZ⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure.preimage hcont : IsClosed (f ⁻¹' closure {y'}))
    let F := ⋃₀ {T ∈ S | x ∉ T}
    have hF : IsClosed F := by
      simp only [F]
      rw [sUnion_eq_biUnion]
      exact (hSf.subset fun _ h ↦ h.1).isClosed_biUnion fun T hT ↦ hSc T hT.1
    have hxF : x ∉ F := fun ⟨T, ⟨_, hxT⟩, hx⟩ ↦ hxT hx
    obtain ⟨x₁, hx₁F, hx₁⟩ := mem_of_mem_nhds (hy' (h _ (hF.isOpen_compl.mem_nhds hxF)))
    have : x₁ ∈ f ⁻¹' closure {y'} := by
      rw [mem_preimage, hx₁]
      exact subset_closure rfl
    rw [hZ] at this
    obtain ⟨T, hTS, hx₁T⟩ := this
    have hxT : x ∈ T := by
      by_contra hxT
      exact hx₁F ⟨T, ⟨hTS, hxT⟩, hx₁T⟩
    -- the generic point of the component `T` works
    obtain ⟨x', hx'⟩ := QuasiSober.sober (hSi T hTS) (hSc T hTS)
    refine ⟨x', hx'.specializes hxT, ?_⟩
    have h₁ : f x' ⤳ y' := hx₁ ▸ (hx'.specializes hx₁T).map hcont
    have h₂ : y' ⤳ f x' := by
      have : x' ∈ f ⁻¹' closure {y'} := by rw [hZ]; exact ⟨T, hTS, hx'.mem⟩
      exact specializes_iff_mem_closure.2 this
    exact (h₁.antisymm h₂).eq
  · intro h V hV
    -- a basic open neighbourhood of `x` inside `V`
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgV⟩ := isBasis_basic_opens.mem_nhds_iff.1 hV
    refine Filter.mem_of_superset ?_ (image_mono hgV)
    have hC : IsConstructible (f '' (basicOpen g : Set (PrimeSpectrum B))) :=
      isConstructible_comap_image hfp isConstructible_basicOpen
    refine (mem_nhds_iff_of_isConstructible hC _).2 fun y' hy' ↦ ?_
    obtain ⟨x', hx', rfl⟩ := h y' hy'
    exact ⟨x', hx'.mem_open (basicOpen g).isOpen hxg, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- IV.6.6 (affine case): if `A` is noetherian, `B` a finitely generated `A`-algebra and `M` a
finite `B`-module, flat over `A`, whose support is all of `Spec B`, then `Spec B → Spec A` is
open. -/
theorem isOpenMap_comap_of_flat [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Finite B M] [Module.Flat A M] (hM : Module.support B M = Set.univ) :
    IsOpenMap (comap (algebraMap A B)) := by
  have := hasGoingDown_of_flat_of_support_eq_univ A B M hM
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-- IV.6.6 (affine case, `M = B`): a flat algebra of finite type over a noetherian ring gives an
open map on spectra. -/
theorem isOpenMap_comap_of_flat_algebra [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Flat A B] : IsOpenMap (comap (algebraMap A B)) := by
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end Affine

section Schemes

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- IV.6.6 for `F = 𝒪_X`: a flat morphism locally of finite type over a locally noetherian
scheme is open. -/
theorem isOpenMap_of_flat [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Flat f] :
    IsOpenMap f :=
  f.isOpenMap

/-- Remark after IV.6.6, for `F = 𝒪_X`: such a morphism is even universally open. -/
theorem universallyOpen_of_flat [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Flat f] :
    UniversallyOpen f :=
  inferInstance

end Schemes

end SGA.SGA1.ExposeIV
