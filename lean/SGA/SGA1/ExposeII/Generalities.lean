/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# SGA 1, Exposé II, §1: smooth morphisms, generalities

SGA calls `f : X ⟶ Y` smooth at `x` when some open neighbourhood of `x` has an étale
`Y`-morphism to an affine space `Y[t₁,…,tₙ]` (II.1.1). The affine space is mathlib's
`𝔸(n; Y)`. Mathlib defines smoothness by formal smoothness plus finite presentation
(`AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus`).

This file records SGA's definition as `LocallyEtaleOverAffineSpaceAt` and proves that it agrees
with mathlib's notion, pointwise (`locallyEtaleOverAffineSpaceAt_iff_mem_smoothLocus`) and
globally (`smooth_iff_forall_locallyEtaleOverAffineSpaceAt`). It also covers the affine
version of the definition, the openness of the smooth locus (II.1.1), stability under
generization (II.1.2), the permanence properties II.1.3, and the uniqueness of the relative
dimension (II.1.5) through the rank of `Ω¹`.

The identification of the relative dimension with the dimension of the fibre (II.1.5) is in
`SGA.SGA1.ExposeII.RelativeDimension`. The formulas (1.2) and (1.3) for affine spaces are
`isPullback_affineSpace` and `affineSpaceAffineSpaceIso`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeII

section AffineSpace

variable (n : Type u) (S : Scheme.{u})

set_option backward.isDefEq.respectTransparency.types false in
/-- II.1: `Y[t₁,…,tₙ]` is smooth over `Y`. (SGA states finite type and flat; smoothness is
the étale-over-itself case of II.1.1.) -/
instance smooth_affineSpace [Finite n] : Smooth (𝔸(n; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ <| by
    have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @Smooth),
      HasRingHomProperty.Spec_iff (P := @Smooth)]
    have : Algebra.Smooth (ULift ℤ) (MvPolynomial n (ULift ℤ)) := ⟨inferInstance, inferInstance⟩
    exact RingHom.smooth_algebraMap.mpr this

set_option backward.isDefEq.respectTransparency.types false in
/-- II.1: `Y[t₁,…,tₙ]` is flat over `Y` (for any set of variables). -/
instance flat_affineSpace : Flat (𝔸(n; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ <| by
    have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
      HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- II.1, formula (1.2): `Y[t₁,…,tₙ] ×_Y Y' = Y'[t₁,…,tₙ]`. -/
theorem isPullback_affineSpace {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (AffineSpace.map n f) (𝔸(n; S) ↘ S) (𝔸(n; T) ↘ T) f :=
  AffineSpace.isPullback_map f

/-- II.1: a `Y`-morphism `X ⟶ Y[t₁,…,tₙ]` is the same as `n` global sections of `𝒪_X`. -/
noncomputable abbrev affineSpaceHomOverEquiv {X : Scheme.{u}} [X.Over S] :
    { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤)) :=
  AffineSpace.homOverEquiv S

variable (τ σ : Type u)

set_option backward.isDefEq.respectTransparency.types false in
/-- II.1, formula (1.3): `(Y[t₁,…,tₙ])[tₙ₊₁,…,tₘ] = Y[t₁,…,tₘ]`, i.e. `𝔸(σ; 𝔸(τ; S)) ≅ 𝔸(τ ⊕ σ; S)`,
the coordinates `tᵢ` of `𝔸(τ; S)` becoming the coordinates indexed by `τ`. -/
noncomputable def affineSpaceAffineSpaceIso : 𝔸(σ; 𝔸(τ; S)) ≅ 𝔸(τ ⊕ σ; S) where
  hom := AffineSpace.homOfVector (𝔸(σ; 𝔸(τ; S)) ↘ 𝔸(τ; S) ≫ 𝔸(τ; S) ↘ S)
    (Sum.elim (fun i ↦ (𝔸(σ; 𝔸(τ; S)) ↘ 𝔸(τ; S)).appTop (AffineSpace.coord S i))
      (fun j ↦ AffineSpace.coord (𝔸(τ; S)) j))
  inv := AffineSpace.homOfVector
    (AffineSpace.homOfVector (𝔸(τ ⊕ σ; S) ↘ S) fun i ↦ AffineSpace.coord S (Sum.inl i))
    fun j ↦ AffineSpace.coord S (Sum.inr j)
  hom_inv_id := by
    ext1
    · simp only [Category.assoc, AffineSpace.homOfVector_over, Category.id_comp]
      rw [AffineSpace.comp_homOfVector]
      ext1 <;> simp
    · simp
  inv_hom_id := by
    ext1
    · rw [Category.assoc, AffineSpace.homOfVector_over, Category.id_comp, ← Category.assoc,
        AffineSpace.homOfVector_over, AffineSpace.homOfVector_over]
    · rename_i i
      rcases i with i | j
      · have := congr(Scheme.Hom.appTop $(AffineSpace.homOfVector_over
          (AffineSpace.homOfVector (𝔸(τ ⊕ σ; S) ↘ S) fun i ↦ AffineSpace.coord S (Sum.inl i))
          fun j ↦ AffineSpace.coord S (Sum.inr j)) (AffineSpace.coord S i))
        rw [Scheme.Hom.comp_appTop, AffineSpace.homOfVector_appTop_coord] at this
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.id_appTop,
          CommRingCat.id_apply, AffineSpace.homOfVector_appTop_coord, Sum.elim_inl]
        exact this
      · simp

/-- The isomorphism of formula (1.3) is an isomorphism over `S`. -/
@[reassoc (attr := simp)]
lemma affineSpaceAffineSpaceIso_hom_over :
    (affineSpaceAffineSpaceIso S τ σ).hom ≫ 𝔸(τ ⊕ σ; S) ↘ S =
      𝔸(σ; 𝔸(τ; S)) ↘ 𝔸(τ; S) ≫ 𝔸(τ; S) ↘ S :=
  AffineSpace.homOfVector_over _ _

end AffineSpace

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- II.1.1 (SGA's definition of "smooth at `x`"): there are an integer `n`, an open
neighbourhood `U` of `x` and an étale `Y`-morphism `U ⟶ Y[t₁,…,tₙ]`. By
`locallyEtaleOverAffineSpaceAt_iff_mem_smoothLocus` this is mathlib's pointwise smoothness. -/
def LocallyEtaleOverAffineSpaceAt (x : X) : Prop :=
  ∃ (n : ℕ) (U : X.Opens) (_ : x ∈ U) (g : U.toScheme ⟶ 𝔸(ULift.{u} (Fin n); Y)),
    Etale g ∧ g ≫ 𝔸(ULift.{u} (Fin n); Y) ↘ Y = U.ι ≫ f

variable {f}

/-- II.1.1: the definition may be checked on an open immersion instead of an open subset. -/
lemma LocallyEtaleOverAffineSpaceAt.of_isOpenImmersion {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {x : X} (hx : x ∈ Set.range j) (n : ℕ)
    (g : W ⟶ 𝔸(ULift.{u} (Fin n); Y)) [Etale g]
    (hg : g ≫ 𝔸(ULift.{u} (Fin n); Y) ↘ Y = j ≫ f) : LocallyEtaleOverAffineSpaceAt f x := by
  refine ⟨n, j.opensRange, hx, j.isoOpensRange.inv ≫ g, inferInstance, ?_⟩
  rw [Category.assoc, hg, j.isoOpensRange_inv_comp_assoc]

/-- II.1.1: the notion is local on `X`. -/
lemma LocallyEtaleOverAffineSpaceAt.of_comp {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    {w : W} (h : LocallyEtaleOverAffineSpaceAt (j ≫ f) w) :
    LocallyEtaleOverAffineSpaceAt f (j w) := by
  obtain ⟨n, U, hw, g, hg, e⟩ := h
  exact .of_isOpenImmersion (U.ι ≫ j) ⟨⟨w, hw⟩, rfl⟩ n g (by simpa using e)

/-- II.1.1: a morphism which is smooth at `x` in SGA's sense is smooth on a neighbourhood
of `x` in mathlib's sense. -/
lemma LocallyEtaleOverAffineSpaceAt.exists_smooth {x : X}
    (h : LocallyEtaleOverAffineSpaceAt f x) : ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  obtain ⟨n, U, hx, g, hg, e⟩ := h
  exact ⟨U, hx, e ▸ inferInstance⟩

variable (f) in
/-- II.1.1: a smooth morphism is, near every point, étale over an affine space. This is the
local structure theorem of mathlib (`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`)
transported to schemes. -/
theorem locallyEtaleOverAffineSpaceAt_of_smooth [Smooth f] (x : X) :
    LocallyEtaleOverAffineSpaceAt f x := by
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨m, φ, hφC, hφ⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hstd
  let e₁ : MvPolynomial (ULift.{u} (Fin m)) Γ(Y, U) ≃ₐ[Γ(Y, U)] MvPolynomial (Fin m) Γ(Y, U) :=
    MvPolynomial.renameEquiv _ Equiv.ulift
  let ψ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) Γ(Y, U)) ⟶ Γ(X, V) :=
    CommRingCat.ofHom (φ.comp e₁.toRingEquiv.toRingHom)
  have : Etale (Spec.map ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective e₁.toRingEquiv.bijective) hφ
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin m)) hU.fromSpec) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map _).flip inferInstance
  refine .of_isOpenImmersion hV.fromSpec (by rwa [hV.range_fromSpec]) m
    (Spec.map ψ ≫ (AffineSpace.SpecIso _ Γ(Y, U)).inv ≫ AffineSpace.map _ hU.fromSpec) ?_
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc,
    ← Spec.map_comp_assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
  congr 2
  ext1
  simp only [ψ, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← hφC]
  ext r
  simp [e₁]

/-- II.1.1, comparison with mathlib: smooth at `x` in SGA's sense implies that `x` lies in the
smooth locus. -/
theorem LocallyEtaleOverAffineSpaceAt.mem_smoothLocus [LocallyOfFinitePresentation f] {x : X}
    (h : LocallyEtaleOverAffineSpaceAt f x) : x ∈ f.smoothLocus := by
  obtain ⟨U, hx, hU⟩ := h.exists_smooth
  have : (⟨x, hx⟩ : U) ∈ U.ι ⁻¹ᵁ f.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq, (U.ι ≫ f).smoothLocus_eq_top]
    trivial
  exact this

/-- II.1.1: SGA's pointwise definition of smoothness agrees with mathlib's smooth locus. -/
theorem locallyEtaleOverAffineSpaceAt_iff_mem_smoothLocus [LocallyOfFinitePresentation f]
    {x : X} : LocallyEtaleOverAffineSpaceAt f x ↔ x ∈ f.smoothLocus := by
  refine ⟨LocallyEtaleOverAffineSpaceAt.mem_smoothLocus, fun hx ↦ ?_⟩
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext y
    simp
  exact .of_comp f.smoothLocus.ι
    (locallyEtaleOverAffineSpaceAt_of_smooth (f.smoothLocus.ι ≫ f) (⟨x, hx⟩ : f.smoothLocus))

set_option backward.isDefEq.respectTransparency.types false in
/-- II.1.1: `f` is smooth in SGA's sense (smooth at every point) iff it is smooth in mathlib's
sense. No finiteness hypothesis is needed. -/
theorem smooth_iff_forall_locallyEtaleOverAffineSpaceAt :
    Smooth f ↔ ∀ x, LocallyEtaleOverAffineSpaceAt f x := by
  refine ⟨fun _ ↦ locallyEtaleOverAffineSpaceAt_of_smooth f, fun H ↦ ?_⟩
  choose U hxU hU using fun x ↦ (H x).exists_smooth
  refine IsZariskiLocalAtSource.of_iSup_eq_top U ?_ hU
  exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- II.1.1 (proposition): the set of points where `f` is smooth is open ("trivial from the
definition"). -/
theorem isOpen_setOf_locallyEtaleOverAffineSpaceAt :
    IsOpen {x | LocallyEtaleOverAffineSpaceAt f x} :=
  isOpen_iff_forall_mem_open.mpr fun _ ⟨m, U, hx, g, hg, e⟩ ↦
    ⟨U, fun _ hy ↦ ⟨m, U, hy, g, hg, e⟩, U.2, hx⟩

variable (f) in
/-- II.1.1 (proposition), in mathlib's language: the smooth locus is open. -/
theorem smoothLocus_isOpen [LocallyOfFinitePresentation f] : IsOpen (f.smoothLocus : Set X) :=
  f.smoothLocus.2

/-- II.1.2, geometric form: if `f` is smooth at `x` then it is smooth at every generization
of `x`. -/
theorem LocallyEtaleOverAffineSpaceAt.of_specializes {x x' : X} (hx : x' ⤳ x)
    (h : LocallyEtaleOverAffineSpaceAt f x) : LocallyEtaleOverAffineSpaceAt f x' :=
  hx.mem_open isOpen_setOf_locallyEtaleOverAffineSpaceAt h

/-- II.1.3 (i): an étale morphism is smooth, with relative dimension `0`: `f` itself is the
required étale morphism to `Y[∅] = Y`. -/
theorem locallyEtaleOverAffineSpaceAt_of_etale [Etale f] (x : X) :
    LocallyEtaleOverAffineSpaceAt f x := by
  refine ⟨0, ⊤, trivial, (⊤ : X.Opens).ι ≫ f ≫ inv (𝔸(ULift.{u} (Fin 0); Y) ↘ Y),
    inferInstance, ?_⟩
  simp

/-- II.1.3 (i): an étale morphism is smooth (mathlib). -/
theorem smooth_of_etale [Etale f] : Smooth f := inferInstance

/-- II.1.3 (ii): smoothness is stable under base change (mathlib). -/
theorem smooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Smooth :=
  AlgebraicGeometry.smooth_isStableUnderBaseChange

/-- II.1.3 (iii): a composite of smooth morphisms is smooth (mathlib). -/
theorem smooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g] : Smooth (f ≫ g) :=
  inferInstance

/-- II.1.5: the relative dimension is additive under composition (mathlib, for the standard
smooth presentations defining `SmoothOfRelativeDimension`). -/
theorem smoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (f ≫ g) :=
  inferInstance

/-! ### The affine case -/

section Algebra

open Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- II.1.1, affine version: a finitely presented algebra `S` is smooth over `R` at the prime
`p` iff some `S_f`, `f ∉ p`, is étale over a polynomial ring `R[t₁,…,tₙ]`. -/
theorem isSmoothAt_iff_exists_etale_mvPolynomial [FinitePresentation R S] (p : Ideal S)
    [p.IsPrime] :
    IsSmoothAt R p ↔ ∃ f ∉ p, ∃ (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away f),
      φ.toRingHom.Etale := by
  constructor
  · intro _
    obtain ⟨f, hf, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
    exact ⟨f, hf, n, IsScalarTower.toAlgHom _ _ _, RingHom.etale_algebraMap.mpr inferInstance⟩
  · rintro ⟨f, hf, n, φ, hφ⟩
    have : (algebraMap R (Localization.Away f)).Smooth := by
      have : Smooth R (MvPolynomial (Fin n) R) := ⟨inferInstance, inferInstance⟩
      have h := (RingHom.smooth_algebraMap.mpr this).comp
        ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp hφ).2
      rwa [show φ.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) =
        algebraMap R (Localization.Away f) from φ.comp_algebraMap] at h
    have : Smooth R (Localization.Away f) := RingHom.smooth_algebraMap.mp this
    exact (basicOpen_subset_smoothLocus_iff_smooth (R := R)).mpr this
      (show (⟨p, ‹_›⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen f from hf)

/-- II.1.2: if `B` is smooth over `A` at `p`, it is smooth over `A` at every `q ≤ p`. -/
theorem IsSmoothAt.of_le [FinitePresentation R S] {p q : Ideal S} [p.IsPrime] [q.IsPrime]
    (hqp : q ≤ p) [IsSmoothAt R p] : IsSmoothAt R q := by
  have hsp : (⟨q, ‹_›⟩ : PrimeSpectrum S) ⤳ ⟨p, ‹_›⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hqp
  exact hsp.mem_open (Algebra.isOpen_smoothLocus (R := R)) (show IsSmoothAt R p from ‹_›)

/-- II.1.5, affine version: if `S` is formally étale over `R[t₁,…,tₙ]`, then `Ω¹_{S/R}` is free
with basis the `dtᵢ`. -/
noncomputable def basisKaehlerOfFormallyEtale (ι : Type*) [Algebra (MvPolynomial ι R) S]
    [IsScalarTower R (MvPolynomial ι R) S] [FormallyEtale (MvPolynomial ι R) S] :
    Module.Basis ι S Ω[S⁄R] :=
  ((KaehlerDifferential.mvPolynomialBasis R ι).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial ι R) S)

theorem basisKaehlerOfFormallyEtale_apply (ι : Type*) [Algebra (MvPolynomial ι R) S]
    [IsScalarTower R (MvPolynomial ι R) S] [FormallyEtale (MvPolynomial ι R) S] (i : ι) :
    basisKaehlerOfFormallyEtale ι i =
      KaehlerDifferential.D R S (algebraMap (MvPolynomial ι R) S (.X i)) := by
  simp [basisKaehlerOfFormallyEtale, KaehlerDifferential.mapBaseChange_tmul]

/-- II.1.5, affine version: if `S` is nonzero and étale over `R[t₁,…,tₙ]`, then `Ω¹_{S/R}` has
rank `n`. -/
theorem finrank_kaehler_of_formallyEtale [Nontrivial S] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [FormallyEtale (MvPolynomial (Fin n) R) S] : Module.finrank S Ω[S⁄R] = n := by
  simp [Module.finrank_eq_card_basis (basisKaehlerOfFormallyEtale (Fin n))]

/-- II.1.5, affine version: the integer `n` of II.1.1 is well determined, being the rank of
`Ω¹_{S/R}`. -/
theorem eq_of_formallyEtale_mvPolynomial [Nontrivial S] {n m : ℕ}
    (φ : MvPolynomial (Fin n) R →ₐ[R] S) (ψ : MvPolynomial (Fin m) R →ₐ[R] S)
    (hφ : φ.toRingHom.FormallyEtale) (hψ : ψ.toRingHom.FormallyEtale) : n = m := by
  have hn : Module.finrank S Ω[S⁄R] = n := by
    algebraize [φ.toRingHom]
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algHom φ
    exact finrank_kaehler_of_formallyEtale n
  have hm : Module.finrank S Ω[S⁄R] = m := by
    algebraize [ψ.toRingHom]
    have : IsScalarTower R (MvPolynomial (Fin m) R) S := .of_algHom ψ
    exact finrank_kaehler_of_formallyEtale m
  rw [← hn, hm]

end Algebra

end SGA.SGA1.ExposeII
