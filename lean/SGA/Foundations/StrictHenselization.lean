/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Henselization
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure

/-!
# Strictly henselian local rings and the strict henselization

A local ring is *strictly henselian* if it is henselian and its residue field is separably
closed (Stacks, Section 04GE; EGA IV 18.8). Let `R` be a local ring with residue field `k` and
`K` a field extension of `k`. The residue field of `IsLocalRing.StrictHenselization R K` is the
separable closure of `k` in `K` (`StrictHenselization.residueFieldEquivSeparableClosure`): the
points of the standard étale neighbourhoods are the simple roots in `K` of monic polynomials
over `R`, i.e. the elements of `K` separable over `k`. Hence, if `K` is separably closed,
`StrictHenselization R K` is strictly henselian: it is the strict henselization of `R` with
respect to the separable closure of `k` in `K` (Stacks 0BSK; EGA IV 18.8). If `K` is itself a
separable closure of `k`, its residue field is `K` and its universal property reads: for a
henselian local ring `A` under `R` (with local structure map), the `R`-algebra maps to `A`
correspond to the `k`-embeddings of `K` into the residue field of `A`
(`StrictHenselization.liftEquivOfIsSeparable`; Stacks 0BSK, EGA IV 18.8).
-/

universe u

open Polynomial IsLocalRing

noncomputable section

/-- A local ring is *strictly henselian* if it is henselian and its residue field is separably
closed (Stacks, Section 04GE; EGA IV 18.8). -/
class IsStrictlyHenselian (R : Type*) [CommRing R] : Prop extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (ResidueField R)

attribute [instance] IsStrictlyHenselian.isSepClosed_residueField

lemma isStrictlyHenselian_iff (R : Type*) [CommRing R] :
    IsStrictlyHenselian R ↔ ∃ _ : HenselianLocalRing R, IsSepClosed (ResidueField R) :=
  ⟨fun h ↦ ⟨h.toHenselianLocalRing, h.isSepClosed_residueField⟩, fun ⟨_, h'⟩ ↦ ⟨h'⟩⟩

/-- A field is separably closed if it is isomorphic to a separably closed field. -/
lemma IsSepClosed.of_ringEquiv {k k' : Type*} [Field k] [Field k'] [IsSepClosed k]
    (e : k ≃+* k') : IsSepClosed k' := by
  refine IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_
  have hsep' : (p.map (e.symm : k' →+* k)).Separable := hsep.map
  have hdeg : (p.map (e.symm : k' →+* k)).degree ≠ 0 := by
    rw [degree_map]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep'
  have hp : p = (p.map (e.symm : k' →+* k)).map (e : k →+* k') := by
    rw [Polynomial.map_map]
    ext
    simp
  refine ⟨e x, ?_⟩
  rw [hp, eval_map]
  change eval₂ (e : k →+* k') ((e : k →+* k') x) _ = 0
  rw [eval₂_hom, hx.eq_zero, map_zero]

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K] [Algebra R K]
  [Algebra (ResidueField R) K] [IsScalarTower R (ResidueField R) K]

/-- A ring map `R → K` factoring through the residue field of the local ring `R` is local. -/
lemma isLocalHom_algebraMap_of_isScalarTower : IsLocalHom (algebraMap R K) where
  map_nonunit r hr := by
    rw [IsScalarTower.algebraMap_apply R (ResidueField R) K, ResidueField.algebraMap_eq] at hr
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, map_zero] at hr
    exact not_isUnit_zero hr

attribute [local instance] isLocalHom_algebraMap_of_isScalarTower

namespace EtaleNbhd

variable (N : EtaleNbhd R K)

/-- The point of a standard étale neighbourhood is separable over the residue field of `R`: it is
a simple root of the reduction of a monic polynomial over `R`. -/
theorem isSeparable_point : IsSeparable (ResidueField R) N.point := by
  set k := ResidueField R
  set F : k[X] := N.pair.f.map (algebraMap R k)
  have hF : aeval N.point F = 0 := by
    rw [aeval_map_algebraMap]
    exact N.hasMap.1
  have hF' : aeval N.point (derivative F) ≠ 0 := by
    rw [derivative_map, aeval_map_algebraMap]
    exact N.hasMap.isUnit_derivative_f.ne_zero
  have hint : IsIntegral k N.point := ⟨F, N.pair.monic_f.map _, hF⟩
  obtain ⟨q, hq⟩ := minpoly.dvd k N.point hF
  rw [IsSeparable, separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro h
  apply hF'
  rw [hq, derivative_mul, h, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]

variable {N} in
/-- The values of the point on the local ring of a neighbourhood are separable over the residue
field of `R`. -/
theorem pointHom_mem_separableClosure (x : N.Stalk) :
    N.pointHom x ∈ separableClosure (ResidueField R) K := by
  set E := separableClosure (ResidueField R) K
  have hpt : N.point ∈ E := (mem_separableClosure_iff).mpr N.isSeparable_point
  have haeval (p : R[X]) : aeval N.point p ∈ E := by
    rw [← aeval_map_algebraMap (ResidueField R)]
    have := aeval_algebraMap_apply K (⟨N.point, hpt⟩ : E) (p.map (algebraMap R (ResidueField R)))
    rw [show algebraMap E K ⟨N.point, hpt⟩ = N.point from rfl] at this
    rw [this]
    exact (aeval _ _ : E).2
  have htoField (a : N.pair.Ring) : N.toField a ∈ E := by
    let P : StandardEtalePresentation R N.pair.Ring :=
      ⟨N.pair, N.pair.X, StandardEtalePair.hasMap_X, by
        simpa using Function.bijective_id⟩
    obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x a
    have hg : aeval N.point N.pair.g ≠ 0 := N.hasMap.2.ne_zero
    have := congrArg N.toField hp
    rw [map_mul, map_pow, ← aeval_algHom_apply, ← aeval_algHom_apply] at this
    change N.toField a * aeval (N.toField N.pair.X) N.pair.g ^ n =
      aeval (N.toField N.pair.X) p at this
    rw [toField_X] at this
    rw [eq_div_of_mul_eq (pow_ne_zero n hg) this]
    exact div_mem (haeval p) (pow_mem (haeval _) n)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq N.prime.primeCompl x
  have hs : N.toField s ≠ 0 := fun h ↦ s.2 (N.mem_prime.mpr h)
  have h := congrArg N.pointHom (IsLocalization.mk'_spec N.Stalk a s)
  rw [map_mul, pointHom_algebraMap, pointHom_algebraMap] at h
  rw [eq_div_of_mul_eq hs h]
  exact div_mem (htoField a) (htoField s)

end EtaleNbhd

namespace StrictHenselization

variable (R K)

theorem pointHom_mem_separableClosure (z : StrictHenselization R K) :
    pointHom z ∈ separableClosure (ResidueField R) K := by
  obtain ⟨N, x, rfl⟩ := exists_of z
  exact EtaleNbhd.pointHom_mem_separableClosure x

/-- Every element of `K` separable over the residue field of `R` is a value of the point of the
strict henselization: it is a simple root of a monic lift of its minimal polynomial. -/
theorem exists_pointHom_eq {y : K} (hy : IsSeparable (ResidueField R) y) :
    ∃ z : StrictHenselization R K, pointHom z = y := by
  set k := ResidueField R
  have hint : IsIntegral k y := hy.isIntegral
  obtain ⟨F, hFμ, -, hF⟩ := lifts_and_degree_eq_and_monic
    (map_surjective (algebraMap R k) residue_surjective (minpoly k y)) (minpoly.monic hint)
  have haeval (p : R[X]) : aeval y p = aeval y (p.map (algebraMap R k)) :=
    (aeval_map_algebraMap k y p).symm
  let N : EtaleNbhd R K := ⟨⟨F, hF, derivative F, 1, 0, 1, by ring⟩, y, by
    refine ⟨?_, ?_⟩
    · change aeval y F = 0
      rw [haeval, hFμ, minpoly.aeval]
    · change IsUnit (aeval y (derivative F))
      rw [haeval, ← derivative_map, hFμ, isUnit_iff_ne_zero]
      exact hy.aeval_derivative_ne_zero (minpoly.aeval k y)⟩
  refine ⟨of N (algebraMap N.pair.Ring N.Stalk N.pair.X), ?_⟩
  rw [pointHom_of, EtaleNbhd.pointHom_algebraMap, EtaleNbhd.toField_X]

/-- The values of the point of the strict henselization are the elements of `K` separable over
the residue field of `R`. -/
theorem range_pointHom :
    Set.range (pointHom : StrictHenselization R K →ₐ[R] K) =
      separableClosure (ResidueField R) K := by
  ext y
  refine ⟨?_, fun hy ↦ exists_pointHom_eq R K (mem_separableClosure_iff.mp hy)⟩
  rintro ⟨z, rfl⟩
  exact pointHom_mem_separableClosure R K z

/-- The residue field of the strict henselization with respect to `K` is the separable closure
of the residue field of `R` in `K` (Stacks 0BSK). -/
def residueFieldEquivSeparableClosure :
    ResidueField (StrictHenselization R K) ≃+* separableClosure (ResidueField R) K :=
  RingEquiv.ofBijective
    ((residueFieldHom : ResidueField (StrictHenselization R K) →ₐ[R] K).toRingHom.codRestrict
      (separableClosure (ResidueField R) K) fun z ↦ by
        obtain ⟨z, rfl⟩ := residue_surjective z
        exact pointHom_mem_separableClosure R K z)
    ⟨fun a b h ↦ residueFieldHom_injective (congrArg Subtype.val h), fun ⟨y, hy⟩ ↦ by
      obtain ⟨z, hz⟩ := exists_pointHom_eq R K (mem_separableClosure_iff.mp hy)
      exact ⟨residue _ z, Subtype.ext hz⟩⟩

@[simp]
lemma coe_residueFieldEquivSeparableClosure_residue (z : StrictHenselization R K) :
    (residueFieldEquivSeparableClosure R K (residue _ z) : K) = pointHom z := rfl

/-- If `K` is separably closed, the strict henselization with respect to `K` is strictly
henselian (Stacks 0BSK; EGA IV 18.8). -/
instance isStrictlyHenselian [IsSepClosed K] : IsStrictlyHenselian (StrictHenselization R K) where
  isSepClosed_residueField :=
    haveI := IsSepClosure.sep_closed (ResidueField R) (K := separableClosure (ResidueField R) K)
    IsSepClosed.of_ringEquiv (residueFieldEquivSeparableClosure R K).symm

section IsSeparable

variable [Algebra.IsSeparable (ResidueField R) K]

lemma pointHom_surjective_of_isSeparable :
    Function.Surjective (pointHom : StrictHenselization R K →ₐ[R] K) := fun y ↦
  exists_pointHom_eq R K (Algebra.IsSeparable.isSeparable _ y)

/-- If `K` is separable over the residue field `k` of `R` (e.g. a separable closure of `k`), the
residue field of the strict henselization with respect to `K` is `K`. -/
def residueFieldEquiv : ResidueField (StrictHenselization R K) ≃ₐ[R] K :=
  AlgEquiv.ofBijective residueFieldHom ⟨residueFieldHom_injective, fun y ↦ by
    obtain ⟨z, rfl⟩ := pointHom_surjective_of_isSeparable R K y
    exact ⟨residue _ z, rfl⟩⟩

@[simp]
lemma residueFieldEquiv_residue (z : StrictHenselization R K) :
    residueFieldEquiv R K (residue _ z) = pointHom z := rfl

variable {A : Type*} [CommRing A] [HenselianLocalRing A] [Algebra R A]
  [IsLocalHom (algebraMap R A)]

/-- The universal property of the strict henselization with respect to a separable closure `K`
of the residue field `k` of `R` (Stacks 0BSK; EGA IV 18.8): for a henselian (e.g. strictly
henselian) local ring `A` with a local homomorphism `R → A`, the `R`-algebra maps from the strict
henselization to `A` correspond to the embeddings of `K` into the residue field of `A` over `R`
(equivalently over `k`), via the induced map of residue fields. -/
def liftEquivOfIsSeparable : (StrictHenselization R K →ₐ[R] A) ≃ (K →ₐ[R] ResidueField A) :=
  liftEquivResidueField.trans
    { toFun σ := σ.comp (residueFieldEquiv R K).symm.toAlgHom
      invFun τ := τ.comp (residueFieldEquiv R K).toAlgHom
      left_inv σ := by ext; simp
      right_inv τ := by ext; simp }

lemma liftEquivOfIsSeparable_apply_pointHom (φ : StrictHenselization R K →ₐ[R] A)
    (z : StrictHenselization R K) :
    liftEquivOfIsSeparable R K φ (pointHom z) = residue A (φ z) := by
  rw [← liftEquivResidueField_apply_residue]
  simp only [liftEquivOfIsSeparable, Equiv.trans_apply, Equiv.coe_fn_mk, AlgHom.comp_apply]
  congr 1
  exact (residueFieldEquiv R K).symm_apply_eq.mpr rfl

end IsSeparable

/-- Stacks 06LJ: the strict henselization of a noetherian local ring (with respect to a separable
closure of its residue field) is noetherian. Proved as
`IsLocalRing.StrictHenselization.isNoetherianStatement` in
`SGA.Foundations.HenselizationNoetherian`. -/
def IsNoetherianStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [Algebra (ResidueField R) K] [IsScalarTower R (ResidueField R) K]
    [IsSepClosure (ResidueField R) K],
    IsNoetherianRing (StrictHenselization R K)

end StrictHenselization

/-- The canonical map from the henselization to the strict henselization with respect to a field
extension `K` of the residue field (EGA IV 18.8). -/
def Henselization.toStrictHenselization :
    Henselization R →ₐ[R] StrictHenselization R K :=
  Henselization.lift

end IsLocalRing
