/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.PolynomialAlgebra
import SGA.SGA1.ExposeXIII.KunnethMain

/-!
# SGA 1, XIII.4.6 in characteristic `0`: invariance for the affine line

The resolution-free proof of XIII.4.6 in characteristic `0` starts from the invariance of `π₁`
under algebraically closed base change for the open subschemes of the affine line (the milestone
C1 of the triage). This file treats the affine line itself: in characteristic `0`,
`π₁(𝔸¹_k) = 1` for every algebraically closed `k` (XIII.2.12 for `g = 0`, `n = 1`, proved without
Riemann's existence theorem, `affineLinePrimeToPTrivialStatement 0`), so base change of étale
coverings along `𝔸¹_{k'} → 𝔸¹_k` is an equivalence (`hasAlgClosedBaseChangeInvariance_affineLine`).

* `eq_one_of_proLKernel_eq_top`: a fundamental group (of a Galois category) whose maximal
  pro-`L` quotient is trivial for `L` the set of all primes is trivial.
* `bijective_map_prod_affineLine_of_isNormalScheme`: with the main lemma
  (`bijective_map_prod_of_isNormalScheme_of_invariance`), XIII.4.6 for `X × 𝔸¹` with `X` normal:
  `π₁(X ×ₖ 𝔸¹) → π₁(X) × π₁(𝔸¹)` is bijective, i.e. `π₁(X ×ₖ 𝔸¹) ≅ π₁(X)`.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory Polynomial
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII

section Galois

variable {C : Type*} [Category* C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- If every open normal subgroup of `Aut F` (of finite index) is the whole group, i.e. the
maximal profinite quotient of `Aut F` for the set of all primes is trivial, then `Aut F` is
trivial: the stabilizers of the points of Galois objects form a basis of neighbourhoods of `1`. -/
theorem eq_one_of_proLKernel_eq_top (h : proLKernel {ℓ | ℓ.Prime} (Aut F) = ⊤) (σ : Aut F) :
    σ = 1 := by
  have hmem (X : PointedGaloisObject F) : σ ∈ MulAction.stabilizer (Aut F) X.pt := by
    have := X.isGalois
    let N := MulAction.stabilizer (Aut F) X.pt
    have hN : N.Normal := stabilizer_normal_of_isGalois F X.obj X.pt
    have ho : IsOpen (N : Set (Aut F)) := stabilizer_isOpen _ _
    have : Finite (Aut F ⧸ N) := N.quotient_finite_of_isOpen ho
    have hL : IsLIndex {ℓ | ℓ.Prime} N := ⟨Subgroup.index_ne_zero_of_finite, fun p hp _ ↦ hp⟩
    exact mem_proLKernel.mp (h ▸ Subgroup.mem_top σ) N hN ho hL
  have hspec : σ ⤳ 1 := by
    rw [specializes_iff_pure, Filter.le_def]
    intro s hs
    obtain ⟨X, -, hX⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.mp hs
    exact hX (hmem X)
  exact hspec.eq

end Galois

section AffineLine

/-- XIII.2.12 (`g = 0`, `n = 1`, `p = 0`): `π₁(𝔸¹_k) = 1` for `k` algebraically closed of
characteristic `0`, for any fibre functor (from `affineLinePrimeToPTrivialStatement 0`). -/
theorem aut_eq_one_affineLine (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (G : ExposeV.FEt (Spec (.of k[X])) ⥤ FintypeCat.{u}) [FiberFunctor G] (σ : Aut G) :
    σ = 1 := by
  have : ConnectedSpace (Spec (.of k[X])) := inferInstance
  let Ω := AlgebraicClosure k
  let y : Spec (.of Ω) ⟶ Spec (.of k[X]) :=
    Spec.map (CommRingCat.ofHom ((Polynomial.aeval (0 : Ω)).toRingHom))
  have : CharP k 0 := CharP.ofCharZero k
  have hk := affineLinePrimeToPTrivialStatement 0 k Ω y
  have hL : primesDifferentFrom 0 = {ℓ | ℓ.Prime} := by
    ext ℓ
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.ne_zero⟩⟩
  rw [hL] at hk
  have h1 : ∀ τ : FundamentalGroup y, τ = 1 := eq_one_of_proLKernel_eq_top _ hk
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor G (ExposeV.FEt.fiber Ω y)
  apply φ.conjAut.injective
  rw [map_one]
  exact h1 _

set_option backward.isDefEq.respectTransparency false in
/-- XIII.4.6, case `X = 𝔸¹`, `Y = Spec k'`, in characteristic `0`: the étale coverings of the
affine line over an algebraically closed field `k` of characteristic `0` are invariant under
algebraically closed base change (both fundamental groups are trivial). -/
theorem hasAlgClosedBaseChangeInvariance_affineLine (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] :
    HasAlgClosedBaseChangeInvariance (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  intro k' _ _ _
  let sA := Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst sA ρ
  have : CharZero k' := charZero_of_injective_algebraMap (algebraMap k k').injective
  -- `𝔸¹_k ⊗ₖ k' ≅ 𝔸¹_{k'}`
  let ψ : k[X] ⊗[k] k' ≃ₐ[k] k'[X] :=
    (Algebra.TensorProduct.comm k k[X] k').trans (polyEquivTensor k k').symm
  let g : pullback sA ρ ⟶ Spec (.of k'[X]) :=
    (pullbackSpecIso k k[X] k').hom ≫ Spec.map (CommRingCat.ofHom ψ.symm.toRingHom)
  have : IsIso (Spec.map (CommRingCat.ofHom ψ.symm.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom ψ.symm.toRingHom) :=
      (ψ.symm.toRingEquiv.toCommRingCatIso).isIso_hom
    infer_instance
  have : IsIso g := by infer_instance
  have : ConnectedSpace (Spec (.of k'[X])) := inferInstance
  have : ConnectedSpace ↥(pullback sA ρ) :=
    (Scheme.homeoOfIso (asIso g)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso g)).symm.continuous
  obtain ⟨z⟩ : Nonempty ↥(pullback sA ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback sA ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback sA ρ := ExposeX.geometricPoint _ z
  let F' := ExposeV.FEt.fiber Ω x
  have : FiberFunctor (ExposeV.FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback π) F']
  -- `π₁(𝔸¹_k ⊗ₖ k')` is trivial, being isomorphic to `π₁(𝔸¹_{k'})`
  have h₁ : ∀ τ : Aut F', τ = 1 := by
    intro τ
    have hb := ExposeV.autMap_bijective (ExposeV.FEt.pullback g)
      (ExposeV.FEt.pullbackFiberIso Ω g x)
    apply hb.1
    rw [map_one]
    exact aut_eq_one_affineLine k' _ _
  refine ⟨fun a b _ ↦ (h₁ a).trans (h₁ b).symm, fun τ ↦ ⟨1, ?_⟩⟩
  rw [map_one, aut_eq_one_affineLine k _ τ]

/-- The affine line is smooth. -/
instance smooth_specMap_polynomial (k : Type u) [Field k] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.Smooth k k[X] := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.mpr this

/-- XIII.4.6 in characteristic `0` for `Y = 𝔸¹` and `X` connected, normal and locally of finite
type over `k` (algebraically closed; special case): `π₁(X ×ₖ 𝔸¹) → π₁(X) × π₁(𝔸¹)` is bijective,
at every geometric point. As `π₁(𝔸¹) = 1` (`aut_eq_one_affineLine`), this says
`π₁(X ×ₖ 𝔸¹) ≅ π₁(X)`. -/
theorem bijective_map_prod_affineLine_of_isNormalScheme (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : Spec (.of Ω) ⟶ pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst _ _) c).prod
      (FundamentalGroup.map (pullback.snd _ _) c)) := by
  have : ConnectedSpace (Spec (.of k[X])) := inferInstance
  exact bijective_map_prod_of_isNormalScheme_of_invariance sX _ hX
    (hasAlgClosedBaseChangeInvariance_affineLine k) Ω c

end AffineLine

end SGA.SGA1.ExposeXIII
