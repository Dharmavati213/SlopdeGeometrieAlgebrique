/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.BaseChange
import SGA.Foundations.Fields.GeometricallyIntegral
import SGA.Foundations.CommAlg.PurityScheme
import SGA.Foundations.Smooth.GenericSmoothness
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeII.PermanenceSmooth
import SGA.SGA1.ExposeV.QuotientComponents

/-!
# Normality of products over an algebraically closed field of characteristic `0`

For the Künneth formula XIII.4.6 with two normal factors (resolution-free route, characteristic
`0`) we need `X ×ₖ Y` normal when `X` and `Y` are normal of finite type over the algebraically
closed field `k`. On rings: if `A`, `B` are integrally closed domains of finite type over `k`, then
`A ⊗ₖ B` is an integrally closed domain (`isIntegrallyClosed_tensorProduct`). The proof:

* `A ⊗ₖ B` is a domain (`Algebra.TensorProduct.isDomain_of_isAlgClosed`);
* `B ⊗ₖ Frac A` is integrally closed (`isIntegrallyClosed_tensorProduct_fractionRing`): by
  generic smoothness `A_f` is smooth over `k` for some `f ≠ 0`, so `B ⊗ₖ A_f` is smooth over `B`,
  hence normal (II.3.1, normal ascent,
  `ExposeII.isDomain_and_isIntegrallyClosed_localization_of_smooth`), and `B ⊗ₖ Frac A` is a
  localization of it;
* inside `Frac A ⊗ₖ Frac B`, an element integral over `A ⊗ₖ B` lies in `Frac A ⊗ₖ B` and in
  `A ⊗ₖ Frac B`, whose intersection is `A ⊗ₖ B`
  (`TensorProduct.mem_range_map_of_mem_range_lTensor_of_mem_range_rTensor`).

On schemes (`isNormalScheme_pullback`): if `X` and `Y` are normal and locally of finite type over
`k`, then `X ×ₖ Y` is normal; it is covered by the `Spec (A ⊗ₖ B)` for open subschemes `Spec A`,
`Spec B` of `X`, `Y` with `A`, `B` integrally closed domains
(`exists_isOpenImmersion_spec_of_isNormalScheme`).

## References

* [EGA IV₂, 6.14.1] (geometric normality), [Stacks, Tag 06DF]
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeXIII

/-- An integrally closed domain is integrally closed in each of its localizations at
submonoids of non-zero-divisors. -/
lemma isIntegrallyClosedIn_of_isLocalization {R S : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) [IsLocalization M S] : IsIntegrallyClosedIn R S := by
  let g : S →ₐ[R] FractionRing R :=
    IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId R (FractionRing R)) fun y ↦
      IsLocalization.map_units (FractionRing R) ⟨y.1, hM y.2⟩
  refine g.isIntegrallyClosedIn ?_ ‹IsIntegrallyClosed R›
  refine (IsLocalization.lift_injective_iff _).mpr fun x y ↦ ?_
  rw [(IsLocalization.injective S hM).eq_iff]
  exact (IsFractionRing.injective R (FractionRing R)).eq_iff.symm

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- `B ⊗ₖ Frac A` is an integrally closed domain, for `A` a domain of finite type and `B` an
integrally closed domain over an algebraically closed field `k` of characteristic `0`. -/
theorem isIntegrallyClosed_tensorProduct_fractionRing {A B K : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra k B] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K]
    [IsScalarTower k A K] : IsIntegrallyClosed (B ⊗[k] K) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.exists_ne_zero_smooth_localization_away k A
  let Af := Localization.Away f
  have hfA : Submonoid.powers f ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain Af := IsLocalization.isDomain_localization hfA
  -- `K` is a fraction field of `A_f`
  have hfu : IsUnit (algebraMap A K f) :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hf |>.isUnit
  let _ : Algebra Af K := (IsLocalization.Away.lift f hfu).toAlgebra
  have : IsScalarTower A Af K := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq f hfu a).symm
  have : IsScalarTower k Af K := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k A Af, ← IsScalarTower.algebraMap_apply A Af K,
      ← IsScalarTower.algebraMap_apply]
  have : IsFractionRing Af K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) Af K
  -- `C = B ⊗ₖ A_f` is smooth over `B`, a domain, hence integrally closed (II.3.1)
  let C := B ⊗[k] Af
  have : IsDomain C := Algebra.TensorProduct.isDomain_of_isAlgClosed
  have : IsIntegrallyClosed C := IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
    (ExposeII.isDomain_and_isIntegrallyClosed_localization_of_smooth (A := B) p).2
  -- `B ⊗ₖ K` is a localization of `C`
  let _ : Algebra C (B ⊗[k] K) :=
    (Algebra.TensorProduct.map (AlgHom.id k B) (IsScalarTower.toAlgHom k Af K)).toRingHom.toAlgebra
  have : IsScalarTower B C (B ⊗[k] K) := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change b ⊗ₜ 1 = Algebra.TensorProduct.map _ _ (b ⊗ₜ 1)
    simp
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k B (nonZeroDivisors Af) K
    (by ext a; simp [RingHom.algebraMap_toAlgebra])
  refine isIntegrallyClosed_of_isLocalization (R := C) (B ⊗[k] K)
    ((nonZeroDivisors Af).map (Algebra.TensorProduct.includeRight (R := k) (A := B))) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero ha ?_
  exact Algebra.TensorProduct.includeRight_injective (algebraMap k B).injective
    (h.trans (map_zero _).symm)

omit [IsAlgClosed k] [CharZero k] in
private lemma algebraTensorProductMap_apply {A B C D : Type u} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] C) (g : B →ₐ[k] D) (x : A ⊗[k] B) :
    Algebra.TensorProduct.map f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Products of normal varieties over an algebraically closed field of characteristic `0` are
normal**: if `A` and `B` are integrally closed domains of finite type over an algebraically
closed field `k` of characteristic `0`, then `A ⊗ₖ B` is an integrally closed domain. -/
theorem isIntegrallyClosed_tensorProduct {A B : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra k B] [Algebra.FiniteType k B] :
    IsIntegrallyClosed (A ⊗[k] B) := by
  let K := FractionRing A
  let L := FractionRing B
  let i := IsScalarTower.toAlgHom k A K
  let j := IsScalarTower.toAlgHom k B L
  have hi : Function.Injective i := IsFractionRing.injective A K
  have hj : Function.Injective j := IsFractionRing.injective B L
  have : IsDomain (A ⊗[k] B) := Algebra.TensorProduct.isDomain_of_isAlgClosed
  have : IsDomain (K ⊗[k] L) := Algebra.TensorProduct.isDomain_of_isAlgClosed
  -- `Q = K ⊗ L` is integrally closed
  have : IsIntegrallyClosed (L ⊗[k] K) := isIntegrallyClosed_tensorProduct_fractionRing (A := A)
  have : IsIntegrallyClosed (K ⊗[k] L) :=
    IsIntegrallyClosed.of_equiv (Algebra.TensorProduct.comm k L K).toRingEquiv
  -- `P = A ⊗ B ⊆ Q`
  let _ : Algebra (A ⊗[k] B) (K ⊗[k] L) := (Algebra.TensorProduct.map i j).toRingHom.toAlgebra
  have hι : Function.Injective (algebraMap (A ⊗[k] B) (K ⊗[k] L)) := by
    change Function.Injective (Algebra.TensorProduct.map i j)
    have : Module.Flat k K := Module.Flat.of_free
    have : Module.Flat k B := Module.Flat.of_free
    intro x y hxy
    rw [algebraTensorProductMap_apply, algebraTensorProductMap_apply] at hxy
    exact TensorProduct.map_injective_of_flat_flat i.toLinearMap j.toLinearMap hi hj hxy
  have : FaithfulSMul (A ⊗[k] B) (K ⊗[k] L) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hι
  have : IsIntegrallyClosedIn (A ⊗[k] B) (K ⊗[k] L) := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨hι, fun {x} hx ↦ ?_⟩
    -- `x` lies in `K ⊗ B`, which is integrally closed with `K ⊗ L` as a localization
    obtain ⟨u, hu⟩ : ∃ u : K ⊗[k] B, Algebra.TensorProduct.map (AlgHom.id k K) j u = x := by
      let _ : Algebra (K ⊗[k] B) (K ⊗[k] L) :=
        (Algebra.TensorProduct.map (AlgHom.id k K) j).toRingHom.toAlgebra
      let _ : Algebra (A ⊗[k] B) (K ⊗[k] B) :=
        (Algebra.TensorProduct.map i (AlgHom.id k B)).toRingHom.toAlgebra
      have : IsScalarTower (A ⊗[k] B) (K ⊗[k] B) (K ⊗[k] L) :=
        IsScalarTower.of_algebraMap_eq fun y ↦ by
          change Algebra.TensorProduct.map i j y = Algebra.TensorProduct.map (AlgHom.id k K) j
            (Algebra.TensorProduct.map i (AlgHom.id k B) y)
          rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
          rfl
      have : IsIntegrallyClosed (B ⊗[k] K) := isIntegrallyClosed_tensorProduct_fractionRing (A := A)
      have : IsIntegrallyClosed (K ⊗[k] B) :=
        .of_equiv (Algebra.TensorProduct.comm k B K).toRingEquiv
      have : IsDomain (K ⊗[k] B) := Algebra.TensorProduct.isDomain_of_isAlgClosed
      have : IsScalarTower K (K ⊗[k] B) (K ⊗[k] L) := IsScalarTower.of_algebraMap_eq fun c ↦ by
        change c ⊗ₜ 1 = Algebra.TensorProduct.map (AlgHom.id k K) j (c ⊗ₜ 1)
        simp
      have := IsLocalization.tensorProduct_tensorProduct_right k K (nonZeroDivisors B) L
        (by ext b; simp [RingHom.algebraMap_toAlgebra, j])
      have hM : (nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := k) (A := K)) ≤
          nonZeroDivisors (K ⊗[k] B) := by
        rintro _ ⟨b, hb, rfl⟩
        refine mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero hb ?_
        exact Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
          (h.trans (map_zero _).symm)
      have := isIntegrallyClosedIn_of_isLocalization (S := K ⊗[k] L) _ hM
      exact (IsIntegralClosure.isIntegral_iff (A := K ⊗[k] B)).mp
        (IsIntegral.tower_top (A := K ⊗[k] B) hx)
    -- `x` lies in `A ⊗ L`, which is integrally closed with `K ⊗ L` as a localization
    obtain ⟨v, hv⟩ : ∃ v : A ⊗[k] L, Algebra.TensorProduct.map i (AlgHom.id k L) v = x := by
      let _ : Algebra (A ⊗[k] L) (K ⊗[k] L) :=
        (Algebra.TensorProduct.map i (AlgHom.id k L)).toRingHom.toAlgebra
      let _ : Algebra (A ⊗[k] B) (A ⊗[k] L) :=
        (Algebra.TensorProduct.map (AlgHom.id k A) j).toRingHom.toAlgebra
      have : IsScalarTower (A ⊗[k] B) (A ⊗[k] L) (K ⊗[k] L) :=
        IsScalarTower.of_algebraMap_eq fun y ↦ by
          change Algebra.TensorProduct.map i j y = Algebra.TensorProduct.map i (AlgHom.id k L)
            (Algebra.TensorProduct.map (AlgHom.id k A) j y)
          rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
          rfl
      have : IsIntegrallyClosed (A ⊗[k] L) := isIntegrallyClosed_tensorProduct_fractionRing (A := B)
      have : IsDomain (A ⊗[k] L) := Algebra.TensorProduct.isDomain_of_isAlgClosed
      have : IsScalarTower A (A ⊗[k] L) (K ⊗[k] L) := IsScalarTower.of_algebraMap_eq fun a ↦ by
        change algebraMap A K a ⊗ₜ 1 = Algebra.TensorProduct.map i (AlgHom.id k L) (a ⊗ₜ 1)
        simp [i]
      have := IsLocalization.tensorProduct_tensorProduct k L (nonZeroDivisors A) K
        (by ext l; simp [RingHom.algebraMap_toAlgebra, i])
      have hM : Algebra.algebraMapSubmonoid (A ⊗[k] L) (nonZeroDivisors A) ≤
          nonZeroDivisors (A ⊗[k] L) := by
        rintro _ ⟨a, ha, rfl⟩
        refine mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero ha ?_
        exact Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective
          (h.trans (map_zero _).symm)
      have := isIntegrallyClosedIn_of_isLocalization (S := K ⊗[k] L) _ hM
      exact (IsIntegralClosure.isIntegral_iff (A := A ⊗[k] L)).mp
        (IsIntegral.tower_top (A := A ⊗[k] L) hx)
    -- hence `x ∈ A ⊗ B`
    rw [algebraTensorProductMap_apply] at hu hv
    obtain ⟨w, hw⟩ := TensorProduct.mem_range_map_of_mem_range_lTensor_of_mem_range_rTensor
      i.toLinearMap j.toLinearMap hj ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨w, (algebraTensorProductMap_apply i j w).trans hw⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (A ⊗[k] B) (K ⊗[k] L)

section Scheme

open CategoryTheory Limits AlgebraicGeometry

omit [IsAlgClosed k] [CharZero k] in
/-- Normality of a local ring is transported along the stalk isomorphisms of an open
immersion. -/
lemma isDomain_and_isIntegrallyClosed_stalk_of_isOpenImmersion {W Z : Scheme.{u}} (j : W ⟶ Z)
    [IsOpenImmersion j] (w : W)
    (h : IsDomain (W.presheaf.stalk w) ∧ IsIntegrallyClosed (W.presheaf.stalk w)) :
    IsDomain (Z.presheaf.stalk (j w)) ∧ IsIntegrallyClosed (Z.presheaf.stalk (j w)) :=
  ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
    (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.symm h

omit [IsAlgClosed k] [CharZero k] in
/-- The spectrum of an integrally closed domain is a normal scheme. -/
lemma isNormalScheme_spec {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ExposeI.IsNormalScheme (Spec (.of R)) := by
  intro x
  let e : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have : IsDomain Γ(Spec (.of R), ⊤) := e.symm.injective.isDomain _
  have : IsIntegrallyClosed Γ(Spec (.of R), ⊤) := IsIntegrallyClosed.of_equiv e
  have hU := isAffineOpen_top (Spec (.of R))
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; trivial
  have := p.isPrime
  refine ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv (hU.localizationAtPrimeEquivStalk p)
    ⟨IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors, ?_⟩
  exact isIntegrallyClosed_of_isLocalization _ _ p.asIdeal.primeCompl_le_nonZeroDivisors

omit [IsAlgClosed k] [CharZero k] in
/-- A normal scheme locally of finite type over a field `k` is covered by open subschemes
`Spec A`, `A` an integrally closed domain of finite type over `k`. -/
theorem exists_isOpenImmersion_spec_of_isNormalScheme {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (hX : ExposeI.IsNormalScheme X) (x : X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (f : Spec (.of A) ⟶ X),
      IsOpenImmersion f ∧ x ∈ Set.range f ∧
        f ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ IsDomain A ∧
          IsIntegrallyClosed A ∧ Algebra.FiniteType k A := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- the connected component `C` of `x` is open and irreducible
  have hC := ExposeV.isClopen_connectedComponent_of_isLocallyNoetherian x
  let C : X.Opens := ⟨connectedComponent x, hC.isOpen⟩
  have : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hCn := ExposeI.isNormalScheme_of_etale C.ι hX
  have : IrreducibleSpace C := ExposeI.irreducibleSpace_of_isDomain_stalk fun y ↦ (hCn y).1
  have hCirr : IsIrreducible (connectedComponent x) :=
    isIrreducible_iff_irreducibleSpace.mpr ‹IrreducibleSpace C›
  -- an affine open `x ∈ U ⊆ C`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUC⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open mem_connectedComponent hC.isOpen
  have hUirr : IsIrreducible (U : Set X) := ⟨⟨x, hxU⟩, hCirr.2.open_subset U.isOpen hUC⟩
  -- `Γ(X, U)` is a domain: `U ≅ Spec Γ(X, U)` is irreducible and reduced
  have : ∀ y : X, _root_.IsReduced (X.presheaf.stalk y) := fun y ↦ by
    have := (hX y).1
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have hdom : IsDomain Γ(X, U) := by
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUirr
    have : IrreducibleSpace (Spec Γ(X, U)) :=
      (Scheme.homeoOfIso hU.isoSpec).surjective.irreducibleSpace
        (Scheme.homeoOfIso hU.isoSpec).continuous
    have hprime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp this
    rw [nilradical_eq_zero] at hprime
    exact IsDomain.of_bot_isPrime _
  -- `Γ(X, U)` is integrally closed: its local rings are stalks of `X`
  have hint : IsIntegrallyClosed Γ(X, U) :=
    IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
      (ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
        (hU.localizationAtPrimeEquivStalk ⟨p, inferInstance⟩).symm
        (hX (hU.fromSpec ⟨p, inferInstance⟩))).2
  -- the `k`-algebra structure and finite type
  let f := hU.fromSpec
  have : IsOpenImmersion f := hU.isOpenImmersion_fromSpec
  let _ : Algebra k Γ(X, U) := (Spec.preimage (f ≫ sX)).hom.toAlgebra
  have hf : f ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) :=
    (Spec.map_preimage _).symm
  have hft : Algebra.FiniteType k Γ(X, U) := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
      rw [← hf]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.mp this
  refine ⟨Γ(X, U), inferInstance, inferInstance, f, inferInstance, ?_, hf, hdom, hint, hft⟩
  rw [hU.range_fromSpec]
  exact hxU

/-- **The product of normal schemes of finite type over an algebraically closed field of
characteristic `0` is normal**: if `X`, `Y` are normal and locally of finite type over `k`, then
`X ×ₖ Y` is normal (EGA IV 6.14.1 for `k` algebraically closed of characteristic `0`). -/
theorem isNormalScheme_pullback {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (hX : ExposeI.IsNormalScheme X) (hY : ExposeI.IsNormalScheme Y) :
    ExposeI.IsNormalScheme (pullback sX sY) := by
  intro z
  obtain ⟨A, _, _, f, _, ⟨a, ha⟩, hf, _, _, _⟩ :=
    exists_isOpenImmersion_spec_of_isNormalScheme sX hX (pullback.fst sX sY z)
  obtain ⟨B, _, _, g, _, ⟨b, hb⟩, hg, _, _, _⟩ :=
    exists_isOpenImmersion_spec_of_isNormalScheme sY hY (pullback.snd sX sY z)
  let ι := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (Spec.map (CommRingCat.ofHom (algebraMap k B))) sX sY f g (𝟙 _)
    (by rw [Category.comp_id, hf]) (by rw [Category.comp_id, hg])
  have hz : z ∈ Set.range ι := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  obtain ⟨w, rfl⟩ := hz
  refine isDomain_and_isIntegrallyClosed_stalk_of_isOpenImmersion ι w ?_
  -- the source of `ι` is `Spec (A ⊗ₖ B)`
  have : IsDomain (A ⊗[k] B) := Algebra.TensorProduct.isDomain_of_isAlgClosed
  have : IsIntegrallyClosed (A ⊗[k] B) := isIntegrallyClosed_tensorProduct
  have h := isDomain_and_isIntegrallyClosed_stalk_of_isOpenImmersion
    (pullbackSpecIso k A B).inv ((pullbackSpecIso k A B).hom w) (isNormalScheme_spec _)
  have hw : (pullbackSpecIso k A B).inv ((pullbackSpecIso k A B).hom w) = w := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rwa [hw] at h

end Scheme

end SGA.SGA1.ExposeXIII
