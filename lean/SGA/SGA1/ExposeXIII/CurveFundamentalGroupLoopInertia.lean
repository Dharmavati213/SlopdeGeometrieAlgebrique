/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaChart
import Mathlib.RingTheory.Etale.Field

/-!
# Orbits of the Galois group on the geometric points of an étale algebra

For a field `K` and a finite étale `K`-algebra `D`, the fundamental group of `Spec K` (the
automorphism group of the fibre functor `D ↦ Hom_K(D, Ω)`, `Ω` separably closed) acts on the
geometric points `Hom_K(D, Ω)`, and two of them lie in the same orbit iff they have the same
kernel: the orbits are the points of `Spec D` (a consequence of V.8.1: the connected components of
`Spec D` are the `Spec (D ⧸ Q)`).

In XIII.2.12 over `ℂ` (registry row C32), `K` is the fraction field of the strict henselization
of a curve at a point `a`, the inertia group at `a` is the image of `π₁(Spec K)`, and this says
that the orbits of the inertia group on the fibre of a covering `E` are the points of
`E ×_U Spec K`.

* `exists_smul_eq_iff_ker_eq`: the statement above, for the fibre functor
  `ExposeV.fiberFunctor (.of K) Ω` of the Galois category of finite étale `K`-algebras;
* the local scheme `U ×_X X̃` at a point `a` of a curve: if `V` is an affine open containing `a`
  with `U ∩ V = D(h)`, then `U ×_X X̃ ≅ Spec 𝒪^{sh}[1/h]` (`pullbackIsoOfInfEq`), `𝒪^{sh}` is a
  discrete valuation ring when `𝒪_{X,a}` is one
  (`isDiscreteValuationRing_strictLocalization_of_isDiscreteValuationRing`, in
  `SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaChart`),
  and `𝒪^{sh}[1/h]` is its fraction field when `h` vanishes at `a` but not near it
  (`isFractionRing_strictLocalizationAway`).
-/

universe u

open CategoryTheory PreGaloisCategory Opposite

namespace SGA.SGA1.ExposeXIII.LoopInertia

open ExposeV

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- A point of the fibre of the finite étale `K`-algebra `D`, as a `K`-algebra map `D → Ω`. -/
def toAlgHom {D : CommAlgCat.FiniteEtale.{u} (CommRingCat.of K)}
    (x : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D)) : D.obj →ₐ[K] Ω :=
  x

/-- A `K`-algebra map `D → Ω`, as a point of the fibre of `D`. -/
def ofAlgHom {D : CommAlgCat.FiniteEtale.{u} (CommRingCat.of K)} (ψ : D.obj →ₐ[K] Ω) :
    (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D) :=
  ψ

/-- **Orbits of `π₁(Spec K)` on geometric points are kernels** (a consequence of V.8.1 and its
proof: the connected components of `Spec D` are the `Spec (D ⧸ Q)`, and `π₁` acts transitively on
the fibre of a connected object). For a finite étale `K`-algebra
`D` and two points `x₁, x₂` of its fibre (`K`-algebra maps `D → Ω`, `Ω` separably closed), some
element of the fundamental group `Aut (ExposeV.fiberFunctor K Ω)` maps `x₁` to `x₂` iff the two maps
have the same kernel. -/
theorem exists_smul_eq_iff_ker_eq (D : CommAlgCat.FiniteEtale.{u} (CommRingCat.of K))
    (x₁ x₂ : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D)) :
    (∃ τ : Aut (ExposeV.fiberFunctor (CommRingCat.of K) Ω), τ • x₁ = x₂) ↔
      RingHom.ker (toAlgHom K Ω x₁) = RingHom.ker (toAlgHom K Ω x₂) := by
  classical
  -- the point `Q = ker x₁` and the component `Spec (D ⧸ Q)`
  set Q : Ideal D.obj := RingHom.ker (toAlgHom K Ω x₁)
  have hQprime : Q.IsPrime := RingHom.ker_isPrime _
  have hQ : Q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q
  let := Ideal.Quotient.field Q
  have : Module.Finite K (D.obj ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K Q)
  have : Algebra.FormallyUnramified K (D.obj ⧸ Q) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K Q)
      (Ideal.Quotient.mkₐ_surjective K Q)
  have : Algebra.IsSeparable K (D.obj ⧸ Q) := Algebra.FormallyUnramified.isSeparable K (D.obj ⧸ Q)
  have : Algebra.FormallyEtale K (D.obj ⧸ Q) := Algebra.FormallyEtale.of_isSeparable K (D.obj ⧸ Q)
  have : Algebra.FinitePresentation K (D.obj ⧸ Q) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K (D.obj ⧸ Q) := ⟨inferInstance, inferInstance⟩
  let D' : CommAlgCat.FiniteEtale.{u} (CommRingCat.of K) := CommAlgCat.FiniteEtale.of _ (D.obj ⧸ Q)
  let f : op D' ⟶ op D := (CommAlgCat.FiniteEtale.ofHom (Ideal.Quotient.mkₐ K Q) : D ⟶ D').op
  have hF (y : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D')) :
      toAlgHom K Ω ((ExposeV.fiberFunctor (CommRingCat.of K) Ω).map f y) =
        (toAlgHom K Ω y).comp (Ideal.Quotient.mkₐ K Q) :=
    rfl
  have hconn : IsConnected (op D') := by
    rw [isConnected_op_iff_connectedSpace]
    infer_instance
  -- the points with kernel `Q` are those coming from `D ⧸ Q`
  have hker (y : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D')) :
      RingHom.ker (toAlgHom K Ω ((ExposeV.fiberFunctor (CommRingCat.of K) Ω).map f y)) = Q := by
    rw [hF]
    ext a
    simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply]
    rw [map_eq_zero_iff (toAlgHom K Ω y)
      (RingHom.injective (toAlgHom K Ω y : (D.obj ⧸ Q) →+* Ω)), Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  have hfac (x : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D))
      (hx : RingHom.ker (toAlgHom K Ω x) = Q) :
      ∃ y : (ExposeV.fiberFunctor (CommRingCat.of K) Ω).obj (op D'),
        (ExposeV.fiberFunctor (CommRingCat.of K) Ω).map f y = x := by
    refine ⟨ofAlgHom K Ω (Ideal.Quotient.liftₐ Q (toAlgHom K Ω x) fun a ha ↦ by
      rw [← hx] at ha; exact ha), ?_⟩
    apply_fun toAlgHom K Ω using fun _ _ h ↦ h
    rw [hF]
    ext a
    rfl
  obtain ⟨y₁, hy₁⟩ := hfac x₁ rfl
  constructor
  · rintro ⟨τ, rfl⟩
    rw [← hy₁, mulAction_naturality, hker]
  · intro h
    obtain ⟨y₂, hy₂⟩ := hfac x₂ h.symm
    obtain ⟨τ, hτ⟩ :=
      MulAction.exists_smul_eq (Aut (ExposeV.fiberFunctor (CommRingCat.of K) Ω)) y₁ y₂
    exact ⟨τ, by rw [← hy₁, ← hy₂, mulAction_naturality, hτ]⟩

section StrictLocalization

open AlgebraicGeometry Limits IsLocalRing AffineLineChart

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V) {Ω₀ : Type u} [Field Ω₀]
  {xb : Spec (.of Ω₀) ⟶ X} (hxV : xb.imagePoint ∈ V) (h : Γ(X, V))

include hV hxV in
/-- The strict localization `X̃ → X` at a geometric point of the affine open `V` lands in `V`. -/
lemma preimage_eq_top : xb.fromSpecStrictLocalization ⁻¹ᵁ V = ⊤ := by
  rw [fromSpecStrictLocalization_eq hxV hV, Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self,
    Scheme.Hom.preimage_top]

include hV hxV in
lemma preimage_eq_basicOpen (U : X.Opens) (hUV : U ⊓ V = X.basicOpen h) :
    xb.fromSpecStrictLocalization ⁻¹ᵁ U =
      PrimeSpectrum.basicOpen (toStrictLocalization hxV h) := by
  rw [← preimage_basicOpen hxV h hV, ← hUV, Scheme.Hom.preimage_inf, preimage_eq_top hV hxV,
    inf_top_eq]

/-- **`U ×_X X̃ ≅ Spec 𝒪^{sh}[1/h]`** when `U ∩ V = D(h)` for an affine open `V` containing the
image of the geometric point. -/
noncomputable def pullbackIsoOfInfEq (U : X.Opens) (hUV : U ⊓ V = X.basicOpen h) :
    pullback U.ι xb.fromSpecStrictLocalization ≅
      Spec (.of (StrictLocalizationAway hxV h)) :=
  pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict xb.fromSpecStrictLocalization U ≪≫
    Scheme.isoOfEq _ (preimage_eq_basicOpen hV hxV h U hUV) ≪≫
    basicOpenIsoSpecAway (toStrictLocalization hxV h)

attribute [local instance] Scheme.Hom.residueFieldAlgebra Scheme.Hom.stalkAlgebra
  Scheme.Hom.isScalarTower_stalkAlgebra isLocalHom_algebraMap_of_isScalarTower

variable [IsDomain (X.presheaf.stalk xb.imagePoint)]
  [IsDiscreteValuationRing (X.presheaf.stalk xb.imagePoint)]

/-- `𝒪^{sh}[1/h]` is the fraction field of the discrete valuation ring `𝒪^{sh}` when the image of
`h` is a nonzero nonunit (`h` vanishes at the point but not identically near it). -/
lemma isFractionRing_strictLocalizationAway (hh0 : toStrictLocalization hxV h ≠ 0)
    (hhu : ¬ IsUnit (toStrictLocalization hxV h)) :
    haveI := isDomain_strictLocalization_of_isDiscreteValuationRing xb
    IsFractionRing xb.strictLocalization (StrictLocalizationAway hxV h) := by
  have := isDomain_strictLocalization_of_isDiscreteValuationRing xb
  have := isDiscreteValuationRing_strictLocalization_of_isDiscreteValuationRing xb
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible xb.strictLocalization
  obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh0 hπ
  have hk : k ≠ 0 := by
    rintro rfl
    exact hhu (by rw [hw, pow_zero, mul_one]; exact w.isUnit)
  refine IsLocalization.isLocalization_of_is_exists_mul_mem _
    (Submonoid.powers (toStrictLocalization hxV h)) (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh0) ?_
  rintro ⟨y, hy⟩
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hy) hπ
  obtain ⟨d, hd⟩ : ∃ d, n * k = n + d :=
    ⟨n * k - n, by have := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hk); omega⟩
  refine ⟨↑v⁻¹ * ↑w ^ n * π ^ d, n, ?_⟩
  change toStrictLocalization hxV h ^ n = _
  rw [hw, mul_pow, ← pow_mul, mul_comm k n, hd, pow_add]
  calc (↑w : xb.strictLocalization) ^ n * (π ^ n * π ^ d) =
        (↑v * ↑v⁻¹) * (↑w ^ n * (π ^ n * π ^ d)) := by rw [Units.mul_inv, one_mul]
    _ = ↑v⁻¹ * ↑w ^ n * π ^ d * (↑v * π ^ n) := by ring

end StrictLocalization

end SGA.SGA1.ExposeXIII.LoopInertia
