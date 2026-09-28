/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Field
import SGA.Foundations.HenselianFiniteLocal
import SGA.Foundations.StrictLocalizationLift

/-!
# Étale morphisms over the spectrum of a strictly henselian local ring

* `AlgHom.mem_range_algebraMap_of_etale_of_isSepClosed`: an algebra map from an étale algebra over
  a separably closed field `K` to a field extension of `K` takes values in `K`.
* `AlgebraicGeometry.Scheme.exists_lift_of_isStrictlyHenselian`: let `A` be a strictly henselian
  local ring with a geometric point `Spec Ω ⟶ Spec A` at the closed point (a local map `A → Ω`).
  For every étale morphism `W ⟶ X` and `Spec A ⟶ X`, every lift `Spec Ω ⟶ W` of the geometric
  point extends to an `X`-morphism `Spec A ⟶ W` (Stacks 04GG (10), EGA IV 18.5.11): étale
  morphisms have sections through the points of the closed fibre over strictly henselian local
  rings. The proof reduces to affine charts, where it is the lifting property of henselian local
  rings (`HenselianLocalRing.exists_algHom_lift`).
-/

universe u

open CategoryTheory Limits IsLocalRing TensorProduct

/-- An algebra map from an étale algebra over a separably closed field `K` to a field extension
of `K` takes values in `K`: the étale algebra is a product of copies of `K`, whose idempotents are
sent to `0` or `1`. -/
lemma AlgHom.mem_range_algebraMap_of_etale_of_isSepClosed {K D L : Type*} [Field K]
    [IsSepClosed K] [CommRing D] [Algebra K D] [Algebra.Etale K D] [Field L] [Algebra K L]
    (χ : D →ₐ[K] L) (d : D) : χ d ∈ (algebraMap K L).range := by
  classical
  have := Algebra.FormallyUnramified.finite_of_free K D
  have : IsArtinianRing D := isArtinian_of_tower K inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K D
  let _ : Fintype (PrimeSpectrum D) := Fintype.ofFinite _
  have hd : d = ∑ i, e d i • e.symm (Pi.single i 1) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, AlgEquiv.apply_symm_apply]
    ext j
    simp [Pi.single_apply]
  rw [hd, map_sum]
  refine Subring.sum_mem _ fun i _ ↦ ?_
  rw [map_smul, Algebra.smul_def]
  have h₁ : IsIdempotentElem (Pi.single i (1 : K) : PrimeSpectrum D → K) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have hid : IsIdempotentElem (χ (e.symm (Pi.single i 1))) := (h₁.map e.symm).map χ
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h | h
  · rw [h, mul_zero]
    exact Subring.zero_mem _
  · rw [h, mul_one]
    exact ⟨_, rfl⟩

noncomputable section

-- As in `SGA.Foundations.StrictLocalizationLift`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

variable {Ω : Type u} [Field Ω]

/-- **Étale morphisms over a strictly henselian local ring have sections through the closed
fibre** (Stacks 04GG (10), EGA IV 18.5.11, 18.8.1). Let `A` be a strictly henselian local ring and
`α : A → Ω` a local homomorphism to a field, i.e. a geometric point of `Spec A` at the closed
point. Let `h : Spec A ⟶ X`, `p : W ⟶ X` étale and `w : Spec Ω ⟶ W` a lift of the geometric point
`Spec α ≫ h`. Then there is `g : Spec A ⟶ W` with `g ≫ p = h` and `Spec α ≫ g = w`. -/
theorem Scheme.exists_lift_of_isStrictlyHenselian {A : CommRingCat.{u}} [IsStrictlyHenselian A]
    (α : A ⟶ .of Ω) [IsLocalHom α.hom] {X W : Scheme.{u}} (h : Spec A ⟶ X) (p : W ⟶ X)
    [Etale p] (w : Spec (.of Ω) ⟶ W) (hw : w ≫ p = Spec.map α ≫ h) :
    ∃ g : Spec A ⟶ W, g ≫ p = h ∧ Spec.map α ≫ g = w := by
  have hα₀ : Spec.map α (closedPoint Ω) = closedPoint A := Spec_closedPoint
  have hpw₀ : p (w (closedPoint Ω)) = h (closedPoint A) := by
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hα₀]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (h (closedPoint A))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (show w (closedPoint Ω) ∈ p ⁻¹ᵁ U by simpa [hpw₀] using hxU) (p ⁻¹ᵁ U).isOpen
  have e : V ≤ p ⁻¹ᵁ U := hVU
  have hwV' : ⊤ ≤ w ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem w hwV).ge
  have hhU : ⊤ ≤ h ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem h hxU).ge
  let γ : Γ(X, U) ⟶ A := h.appLE U ⊤ hhU ≫ (Scheme.ΓSpecIso A).hom
  have hhγ : Spec.map γ ≫ hU.fromSpec = h := Scheme.Hom.SpecMap_appLE_ΓSpecIso_fromSpec h hU hhU
  let τ : Γ(W, V) ⟶ CommRingCat.of Ω := w.appLE V ⊤ hwV' ≫ (Scheme.ΓSpecIso _).hom
  have hwτ : Spec.map τ ≫ hV.fromSpec = w := Scheme.Hom.SpecMap_appLE_ΓSpecIso_fromSpec w hV hwV'
  have hτ : p.appLE U V e ≫ τ = γ ≫ α := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec p hU hV e, reassoc_of% hwτ, hw, Spec.map_comp,
      Category.assoc, hhγ]
  -- the algebra structures
  have hét := HasRingHomProperty.appLE @Etale p ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e
  let _ : Algebra Γ(X, U) Γ(W, V) := (p.appLE U V e).hom.toAlgebra
  let _ : Algebra Γ(X, U) A := γ.hom.toAlgebra
  have : Algebra.Etale Γ(X, U) Γ(W, V) := hét
  -- the residue field of `A` inside `Ω`
  let ᾱ : ResidueField A →+* Ω := ResidueField.lift α.hom
  have hᾱ (a : A) : ᾱ (IsLocalRing.residue A a) = α a := ResidueField.lift_residue_apply α.hom a
  -- `τ` takes values in the residue field of `A`
  have hrange (d : Γ(W, V)) : τ d ∈ ᾱ.range := by
    let K := ResidueField A
    let _ : Algebra K Ω := ᾱ.toAlgebra
    let _ : Algebra Γ(X, U) Ω := ((algebraMap K Ω).comp (algebraMap Γ(X, U) K)).toAlgebra
    have : IsScalarTower Γ(X, U) K Ω := .of_algebraMap_eq' rfl
    let τA : Γ(W, V) →ₐ[Γ(X, U)] Ω :=
      { τ.hom with
        commutes' := fun r ↦ by
          change (p.appLE U V e ≫ τ) r = ᾱ (IsLocalRing.residue A (γ r))
          rw [hτ, hᾱ]
          rfl }
    let χ : K ⊗[Γ(X, U)] Γ(W, V) →ₐ[K] Ω :=
      Algebra.TensorProduct.lift (Algebra.ofId K Ω) τA fun _ _ ↦ .all _ _
    obtain ⟨x, hx⟩ := χ.mem_range_algebraMap_of_etale_of_isSepClosed (1 ⊗ₜ d)
    refine ⟨x, ?_⟩
    change algebraMap K Ω x = τ d
    rw [hx]
    simp [χ, τA]
  -- the point `Γ(W, V) → κ(A)`
  let ᾱe : ResidueField A ≃+* ᾱ.range :=
    RingEquiv.ofBijective ᾱ.rangeRestrict
      ⟨fun a b hab ↦ ᾱ.injective (congrArg Subtype.val hab), ᾱ.rangeRestrict_surjective⟩
  let τ' : Γ(W, V) →ₐ[Γ(X, U)] ResidueField A :=
    { (ᾱe.symm : ᾱ.range →+* ResidueField A).comp (τ.hom.codRestrict ᾱ.range hrange) with
      commutes' := fun r ↦ by
        apply ᾱ.injective
        change ((ᾱe (ᾱe.symm _) : ᾱ.range) : Ω) = _
        rw [RingEquiv.apply_symm_apply]
        change (p.appLE U V e ≫ τ) r = ᾱ (IsLocalRing.residue A (γ r))
        rw [hτ, hᾱ]
        rfl }
  have hτ' (d : Γ(W, V)) : ᾱ (τ' d) = τ d := by
    change ((ᾱe (ᾱe.symm _) : ᾱ.range) : Ω) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  obtain ⟨φ, hφ⟩ := HenselianLocalRing.exists_algHom_lift (A := A) τ'
  have hφ' (d : Γ(W, V)) : IsLocalRing.residue A (φ d) = τ' d := DFunLike.congr_fun hφ d
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hV e, ← Category.assoc,
      ← Spec.map_comp, ← hhγ]
    congr 2
    ext r
    exact φ.commutes r
  · rw [← Category.assoc, ← Spec.map_comp, ← hwτ]
    congr 2
    ext d
    change α (φ d) = τ d
    rw [← hᾱ, hφ', hτ']

end AlgebraicGeometry
