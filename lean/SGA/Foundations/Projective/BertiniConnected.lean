/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Cohomology.SteinFactorization

/-!
# Geometric connectedness from a separably closed field of functions

Let `K₀` be a field and `W` a nonempty proper `K₀`-scheme whose ring of global sections embeds,
over `K₀`, into a field `M` in which `K₀` is separably closed (every element of `M` separable
over `K₀` lies in `K₀`). Then `W` is geometrically connected: `W ×_{K₀} K` is connected for every
field `K ⊇ K₀` (`AlgebraicGeometry.connectedSpace_pullback_of_injective`,
`AlgebraicGeometry.geometricallyConnected_of_injective`). Two ways to get the embedding:

* `W` reduced with a dense open `V` whose ring of sections embeds into `M`
  (`AlgebraicGeometry.connectedSpace_pullback_of_forall_isSeparable`);
* `W` reduced with a `K₀`-morphism `τ : Spec M ⟶ W` with dense image
  (`AlgebraicGeometry.injective_appTop_of_isDominant`,
  `AlgebraicGeometry.geometricallyConnected_of_isDominant`).

This is the form in which Bertini's theorem enters SGA 1 X.2.10/X.2.11: for the generic hyperplane
section `W` of a variety, `M` is the function field of `W`, and `K₀` (the field of the
hyperplane's coefficients) is separably closed in `M` by the Matsusaka–Zariski lemma
(`Bertini.mem_of_isAlgebraic`).

Proof: `B = Γ(W, 𝒪_W)` is a finite `K₀`-algebra (`W` proper,
`CohomologyAux.finite_app_of_isProper`) which embeds into `M`; so `B` is a field, purely
inseparable over `K₀`. Then `B ⊗_{K₀} K` has only trivial idempotents
(`CohomologyAux.trivialIdempotents_tensor_of_isPurelyInseparable`), and it is `Γ(W_K, 𝒪)` (flat
base change, `CohomologyAux.trivialIdempotents_pullback_iff`).

## References

* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [EGA IV₂, 4.5.13 and 4.5.15]
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry

open CohomologyAux

variable {K₀ : Type u} [Field K₀] {W : Scheme.{u}} (q : W ⟶ Spec (.of K₀)) [IsProper q]

omit [IsProper q] in
/-- On a reduced scheme, restriction of global sections to a dense open is injective. -/
lemma injective_presheaf_map_of_dense [IsReduced W] {V : W.Opens} (hV : Dense (V : Set W)) :
    Function.Injective (W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine (basicOpen_eq_bot_iff s).mp ?_
  have h : W.basicOpen (W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) = V ⊓ W.basicOpen s :=
    Scheme.basicOpen_res W s _
  rw [hs, Scheme.basicOpen_zero] at h
  refine TopologicalSpace.Opens.ext (Set.eq_empty_of_forall_notMem fun x hx ↦ ?_)
  obtain ⟨y, hy, hyV⟩ := hV.inter_open_nonempty _ (W.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ (V ⊓ W.basicOpen s : W.Opens) := ⟨hyV, hy⟩
  rw [← h] at this
  exact this

/-- **Geometric connectedness from a separably closed field of functions**, core form: let `W`
be a proper `K₀`-scheme (`q : W ⟶ Spec K₀`), nonempty, and `φ : Γ(W, 𝒪_W) → M` an injective ring
map into a field `M` which is a `K₀`-algebra, compatibly with `q` (`hcomp`), such that every
element of `M` separable over `K₀` lies in `K₀`. Then `W ×_{K₀} K` is connected for every field
`K ⊇ K₀`. -/
theorem connectedSpace_pullback_of_injective [Nonempty W] {M : Type u} [Field M] [Algebra K₀ M]
    (φ : Γ(W, ⊤) →+* M) (hφ : Function.Injective φ)
    (hcomp : ∀ a : K₀, φ (q.specStructureRingHom a) = algebraMap K₀ M a)
    (hsep : ∀ θ : M, IsSeparable K₀ θ → θ ∈ Set.range (algebraMap K₀ M))
    (K : Type u) [Field K] [Algebra K₀ K] :
    ConnectedSpace ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))) := by
  let _ : Algebra K₀ Γ(W, ⊤) := q.specStructureRingHom.toAlgebra
  -- `Γ(W, ⊤)` embeds into `M` over `K₀`
  let φ : Γ(W, ⊤) →ₐ[K₀] M := { φ with commutes' := hcomp }
  -- `Γ(W, ⊤)` is finite over `K₀`
  have hfin : Module.Finite K₀ Γ(W, ⊤) := by
    have h := finite_app_of_isProper q (isAffineOpen_top (Spec (.of K₀)))
    let _ := (q.app ⊤).hom.toAlgebra
    have : Module.Finite Γ(Spec (.of K₀), ⊤) Γ(W, q ⁻¹ᵁ ⊤) := h
    have e : (Scheme.ΓSpecIso (.of K₀)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    have h' : (q.specStructureRingHom).Finite := by
      rw [Scheme.Hom.specStructureRingHom, CommRingCat.hom_comp]
      exact RingHom.Finite.comp h e
    exact h'
  -- its image is a subfield of `M`, purely inseparable over `K₀`
  have hrfin : Module.Finite K₀ φ.range :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hfield : IsField φ.range :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap K₀ φ.range).injective).mp
      (Field.toIsField K₀)
  let B : IntermediateField K₀ M := φ.range.toIntermediateField' hfield
  have hBfin : Module.Finite K₀ B := hrfin
  have : IsPurelyInseparable K₀ B := by
    refine ⟨inferInstance, fun x hx ↦ ?_⟩
    obtain ⟨a, ha⟩ := hsep x (IsSeparable.map (IsScalarTower.toAlgHom K₀ B M)
      (algebraMap B M).injective hx)
    exact ⟨a, Subtype.ext ha⟩
  -- transport to `Γ(W, ⊤)`
  let e : Γ(W, ⊤) ≃ₐ[K₀] B :=
    (AlgEquiv.ofInjective φ hφ).trans
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
  have h₁ := trivialIdempotents_tensor_of_isPurelyInseparable K₀ B K
  have h₂ : TrivialIdempotents (Γ(W, ⊤) ⊗[K₀] K) :=
    h₁.of_ringEquiv (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toRingEquiv
  have h₃ := (trivialIdempotents_pullback_iff q K).mpr h₂
  have : Nonempty ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))) := by
    obtain ⟨w⟩ := ‹Nonempty W›
    obtain ⟨z, -⟩ := (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))).surjective w
    exact ⟨z⟩
  exact connectedSpace_of_trivialIdempotents _ h₃

/-- `connectedSpace_pullback_of_injective` in the language of `GeometricallyConnected`. -/
theorem geometricallyConnected_of_injective [Nonempty W] {M : Type u} [Field M] [Algebra K₀ M]
    (φ : Γ(W, ⊤) →+* M) (hφ : Function.Injective φ)
    (hcomp : ∀ a : K₀, φ (q.specStructureRingHom a) = algebraMap K₀ M a)
    (hsep : ∀ θ : M, IsSeparable K₀ θ → θ ∈ Set.range (algebraMap K₀ M)) :
    GeometricallyConnected q := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact connectedSpace_pullback_of_injective q φ hφ hcomp hsep K

/-- **Geometric connectedness from a separably closed field of functions**: let `W` be a reduced
proper `K₀`-scheme (`q : W ⟶ Spec K₀`), nonempty, `V ⊆ W` a dense open and `ι : Γ(W, V) → M` an
injective ring map into a field `M` which is a `K₀`-algebra, compatibly with `q`
(`hcomp`), such that every element of `M` separable over `K₀` lies in `K₀`. Then `W ×_{K₀} K` is
connected for every field `K ⊇ K₀`. -/
theorem connectedSpace_pullback_of_forall_isSeparable [IsReduced W] [Nonempty W] {V : W.Opens}
    (hV : Dense (V : Set W)) {M : Type u} [Field M] [Algebra K₀ M] (ι : Γ(W, V) →+* M)
    (hι : Function.Injective ι)
    (hcomp : ∀ a : K₀,
      ι ((W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (q.specStructureRingHom a)) =
        algebraMap K₀ M a)
    (hsep : ∀ θ : M, IsSeparable K₀ θ → θ ∈ Set.range (algebraMap K₀ M))
    (K : Type u) [Field K] [Algebra K₀ K] :
    ConnectedSpace ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))) :=
  connectedSpace_pullback_of_injective q (ι.comp (W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom)
    (hι.comp (injective_presheaf_map_of_dense hV)) hcomp hsep K

omit [IsProper q] in
/-- On a reduced scheme, global sections are detected by a morphism `τ : Spec M ⟶ W` with dense
image (`M` a field): `Γ(W, 𝒪_W) → M` is injective. -/
lemma injective_appTop_of_isDominant [IsReduced W] {M : Type u} [Field M] (τ : Spec (.of M) ⟶ W)
    [IsDominant τ] : Function.Injective (τ.appTop ≫ (Scheme.ΓSpecIso (.of M)).hom).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hs' : τ.appTop s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (.of M)).inv.hom hs
    rwa [map_zero, ← CommRingCat.comp_apply, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] at this
  refine (basicOpen_eq_bot_iff s).mp ?_
  refine TopologicalSpace.Opens.ext (Set.eq_empty_of_forall_notMem fun x hx ↦ ?_)
  obtain ⟨_, hp, ⟨p, rfl⟩⟩ := τ.denseRange.inter_open_nonempty _ (W.basicOpen s).isOpen ⟨x, hx⟩
  have : p ∈ τ ⁻¹ᵁ W.basicOpen s := hp
  rw [Scheme.preimage_basicOpen] at this
  change p ∈ (Spec (.of M)).basicOpen (τ.appTop s) at this
  rw [hs', Scheme.basicOpen_zero] at this
  exact this

/-- **Geometric connectedness from a dense generic point**: let `W` be a reduced proper
`K₀`-scheme (`q : W ⟶ Spec K₀`) and `τ : Spec M ⟶ W` a `K₀`-morphism with dense image from the
spectrum of a field `M` in which `K₀` is separably closed (every element of `M` separable over
`K₀` lies in `K₀`). Then `W` is geometrically connected over `K₀`. -/
theorem geometricallyConnected_of_isDominant [IsReduced W] {M : Type u} [Field M] [Algebra K₀ M]
    (τ : Spec (.of M) ⟶ W) [IsDominant τ]
    (hτ : τ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ M)))
    (hsep : ∀ θ : M, IsSeparable K₀ θ → θ ∈ Set.range (algebraMap K₀ M)) :
    GeometricallyConnected q := by
  have : Nonempty W := ⟨τ (IsLocalRing.closedPoint M)⟩
  refine geometricallyConnected_of_injective q _ (injective_appTop_of_isDominant τ) (fun a ↦ ?_)
    hsep
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K₀ M))
  have e : (Scheme.ΓSpecIso (.of K₀)).inv ≫ q.appTop ≫ τ.appTop ≫
      (Scheme.ΓSpecIso (.of M)).hom = CommRingCat.ofHom (algebraMap K₀ M) := by
    rw [← Scheme.Hom.comp_appTop_assoc, hτ, h, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ : CommRingCat.of K₀ ⟶ CommRingCat.of M ↦ φ.hom a) e

end AlgebraicGeometry
