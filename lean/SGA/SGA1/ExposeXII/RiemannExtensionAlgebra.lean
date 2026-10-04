/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Smooth.Fiber
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeV.NormalBase

/-!
# SGA 1, Exposé XII, 5.1 for curves: counting points to prove étaleness

Algebraic part of the extension of the Riemann existence theorem across finitely many points of a
normal curve. Let `C` be a finite flat algebra over a domain `B`, of rank `n`, and `p` a prime of
`B` with perfect residue field. By `∑_{q | p} e(q) f(q) = n` (mathlib's
`Ideal.sum_ramification_inertia_eq_finrank`):

* `isUnramifiedAt_of_finrank_le_card`: if there are at least `n` primes of `C` over `p`, then `C`
  is unramified over `B` at each of them;
* `card_primesOver_eq_finrank`: if `C` is unramified over `B` at the primes over `p` and their
  residue fields are those of `p`, there are exactly `n` of them.

Over `ℂ`, the primes of `C` over the kernel of `x ∈ X(ℂ)` are the points of `Y(ℂ)` over `x`,
`X = Spec B`, `Y = Spec C` (`Points.card_fiber_eq_card_primesOver`, through
`Points.fiberEquivPrimesOver`), all with residue field `ℂ` (`Points.inertiaDeg_ker_eq_one`), so
over a point where `C` is unramified there are exactly `n` of them
(`Points.card_fiber_eq_finrank`). Hence (`Points.etale_of_forall_card_fiber`): a finite flat
`B`-algebra `C`, unramified over the complement of `{h = 0}`, is étale over `B` as soon as, over
every point of `{h = 0}`, `Y(ℂ)` has at least `n` points. This is how the topological extension
of a covering across a puncture (`SGA.SGA1.ExposeXII.RiemannExtensionTopology`) is turned into
étaleness of the integral closure. Also `isLocalization_away_integralClosure` (an algebra
integral over `R[1/h]` is the localization away from `h` of the integral closure of `R` in it)
and `isDomain_of_connectedSpace_of_etale`: a connected finite étale algebra over a normal domain
is a domain (the affine finite case of the first assertion of I.10.1, through V.8.2's
`ExposeV.isConnected_baseChange`). Reference: the formula `∑ e f = n` (Serre, *Corps locaux*,
I §4, Prop. 10, for Dedekind rings; here for finite flat algebras over a domain).
-/

noncomputable section

open Module TensorProduct

universe u

namespace SGA.SGA1.ExposeXII

namespace RiemannExtension

section Counting

variable {B C : Type*} [CommRing B] [IsDomain B] [CommRing C] [Algebra B C] [Module.Finite B C]
  [Module.Flat B C] (p : Ideal B) [p.IsPrime]

/-- **Many primes over `p` force unramifiedness**: if `C` is finite flat of rank `n` over the
domain `B` and has at least `n` primes over `p` (whose residue field is perfect), then `C` is
unramified over `B` at every prime over `p`. -/
theorem isUnramifiedAt_of_finrank_le_card [PerfectField p.ResidueField]
    (h : finrank B C ≤ Nat.card (p.primesOver C)) (q : Ideal C) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsUnramifiedAt B q := by
  classical
  have : Fintype (p.primesOver C) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p C
  set f : p.primesOver C → ℕ := fun q' ↦ q'.1.ramificationIdx B * q'.1.inertiaDeg B
  have hf1 (q' : p.primesOver C) : 1 ≤ f q' := by
    have : q'.1.IsPrime := q'.2.1
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q'.1 B).ne'
      (Ideal.inertiaDeg_pos q'.1 B).ne')
  let q₀ : p.primesOver C := ⟨q, inferInstance, inferInstance⟩
  have hq₀ : f q₀ = 1 := by
    by_contra hne
    have h2 : 2 ≤ f q₀ := by have := hf1 q₀; omega
    have hrest : (Finset.univ.erase q₀).card • 1 ≤ ∑ q' ∈ Finset.univ.erase q₀, f q' :=
      Finset.card_nsmul_le_sum _ _ _ fun q' _ ↦ hf1 q'
    have hsum' : f q₀ + ∑ q' ∈ Finset.univ.erase q₀, f q' = finrank B C := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ q₀)]
      exact hsum
    rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ, smul_eq_mul,
      mul_one] at hrest
    rw [Nat.card_eq_fintype_card] at h
    have hpos : 0 < Fintype.card (p.primesOver C) := Fintype.card_pos_iff.mpr ⟨q₀⟩
    omega
  have he : q.ramificationIdx B = 1 := Nat.eq_one_of_mul_eq_one_right hq₀
  obtain rfl : p = q.under B := Ideal.LiesOver.over
  exact (Ideal.ramificationIdx_eq_one_iff).mp he

/-- **Unramified primes with trivial residue extensions are counted by the rank**: if `C` is
finite flat of rank `n` over the domain `B` and, at every prime `q` over `p`, unramified with
inertia degree `1`, then there are exactly `n` primes of `C` over `p`. -/
theorem card_primesOver_eq_finrank [Algebra.EssFiniteType B C]
    (hq : ∀ (q : Ideal C) [q.IsPrime] [q.LiesOver p],
      Algebra.IsUnramifiedAt B q ∧ q.inertiaDeg B = 1) :
    Nat.card (p.primesOver C) = finrank B C := by
  classical
  have : Fintype (p.primesOver C) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank p C, Nat.card_eq_fintype_card,
    Fintype.card, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  have : q'.1.IsPrime := q'.2.1
  have : q'.1.LiesOver p := q'.2.2
  obtain ⟨hu, hf⟩ := hq q'.1
  rw [Ideal.ramificationIdx_eq_one, hf]

end Counting

/-- **The integral closure localizes back**: if `S` is integral over `R[1/h]`, then `S` is the
localization of the integral closure of `R` in `S` away from `h` (clear denominators in an
integral equation). This is the case `S_f = S` of mathlib's `IsLocalization.Away.integralClosure`
(integral closure commutes with localization), proved directly here to avoid setting up the
algebra `integralClosure R S → integralClosure R[1/h] S`. -/
theorem isLocalization_away_integralClosure {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : R) [Algebra (Localization.Away h) S] [IsScalarTower R (Localization.Away h) S]
    [Algebra.IsIntegral (Localization.Away h) S] :
    IsLocalization.Away (algebraMap R (integralClosure R S) h) S := by
  have hunit : IsUnit (algebraMap R S h) := by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away h) S]
    exact (IsLocalization.Away.algebraMap_isUnit h).map _
  refine
    { map_units := ?_
      surj := fun s ↦ ?_
      exists_of_eq := fun {a b} hab ↦ ⟨1, by rw [Subtype.ext hab]⟩ }
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact hunit.pow n
  · obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Submonoid.powers h) s (Algebra.IsIntegral.isIntegral (R := Localization.Away h) s)
    refine ⟨⟨⟨h ^ N • s, hN⟩, ⟨algebraMap R (integralClosure R S) h ^ N, N, rfl⟩⟩, ?_⟩
    change s * algebraMap R S h ^ N = h ^ N • s
    rw [Algebra.smul_def, map_pow, mul_comm]

/-- I.10.1, first assertion, affine finite case: a finite étale algebra `C'` over a normal domain
`A` with `Spec C'` connected is a domain. (SGA's statement is for `X` étale and separated over a
normal connected `Y`, and also describes the components through the fields `K_i` and the
normalization; only this special case is proved here.) Proof: the generic fibre `K ⊗_A C'` is
connected (V.8.2's `isConnected_baseChange`), reduced and artinian, hence a field, and `C'` embeds
in it. -/
theorem isDomain_of_connectedSpace_of_etale {A C' : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing C'] [Algebra A C'] [Algebra.Etale A C'] [Module.Finite A C']
    [ConnectedSpace (PrimeSpectrum C')] : IsDomain C' := by
  let K := FractionRing A
  let T : CommAlgCat.FiniteEtale.{u} A := CommAlgCat.FiniteEtale.of A C'
  have hT : CategoryTheory.PreGaloisCategory.IsConnected (Opposite.op T) :=
    (ExposeV.isConnected_op_iff_connectedSpace A T).mpr ‹_›
  obtain ⟨hnt, hid⟩ := (ExposeV.isConnected_op_iff K _).mp
    (ExposeV.isConnected_baseChange A K T hT)
  change Nontrivial (K ⊗[A] C') at hnt
  change ∀ e : K ⊗[A] C', IsIdempotentElem e → e = 0 ∨ e = 1 at hid
  have : IsReduced (K ⊗[A] C') := Algebra.FormallyUnramified.isReduced_of_field K _
  have : IsArtinianRing (K ⊗[A] C') := IsArtinianRing.of_finite K _
  have hfield := ExposeI.isField_of_isArtinianRing_of_isReduced (K ⊗[A] C') hid
  let := hfield.toField
  have hinj : Function.Injective (algebraMap C' (C' ⊗[A] K)) :=
    ExposeI.injective_algebraMap_tensor_fractionRing K
  have hinj' : Function.Injective
      (Algebra.TensorProduct.includeRight : C' →ₐ[A] K ⊗[A] C') := by
    have : (Algebra.TensorProduct.includeRight : C' →ₐ[A] K ⊗[A] C') =
        (Algebra.TensorProduct.comm A C' K).toAlgHom.comp
          (IsScalarTower.toAlgHom A C' (C' ⊗[A] K)) := by
      ext c; simp
    rw [this]
    exact (Algebra.TensorProduct.comm A C' K).injective.comp hinj
  exact hinj'.isDomain _

end RiemannExtension

/-! ### Points over `ℂ` -/

namespace Points

variable {B C : Type*} [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] [CommRing C]
  [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C] [Module.Finite B C]

/-- The fibre of `Y(ℂ) → X(ℂ)` over `x` is the set of primes of `C` over the kernel of `x`
(`C` finite over `B` of finite type over `ℂ`). -/
def fiberEquivPrimesOver (x : Points ℂ B) :
    {ψ : Points ℂ C // proj B C ψ = x} ≃ (ker x).primesOver C where
  toFun ψ := ⟨ker ψ.1, inferInstance, ⟨by
    have h := ker_proj (A := B) ψ.1
    rw [ψ.2] at h
    exact h⟩⟩
  invFun q :=
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver (ker x) := q.2.2
    have : Algebra.FiniteType ℂ C := .trans (S := B) inferInstance inferInstance
    have : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := ker x) (P := q.1)
    ⟨(exists_ker_eq (K := ℂ) q.1).choose, eq_of_ker_eq <| by
      rw [ker_proj, (exists_ker_eq (K := ℂ) q.1).choose_spec]
      exact (Ideal.LiesOver.over (P := q.1) (p := ker x)).symm⟩
  left_inv ψ := by
    have : Algebra.FiniteType ℂ C := .trans (S := B) inferInstance inferInstance
    refine Subtype.ext (eq_of_ker_eq ?_)
    have : (ker ψ.1).IsMaximal := inferInstance
    exact (exists_ker_eq (K := ℂ) (ker ψ.1)).choose_spec
  right_inv q := by
    have : Algebra.FiniteType ℂ C := .trans (S := B) inferInstance inferInstance
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver (ker x) := q.2.2
    have : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := ker x) (P := q.1)
    exact Subtype.ext (exists_ker_eq (K := ℂ) q.1).choose_spec

lemma card_fiber_eq_card_primesOver (x : Points ℂ B) :
    Nat.card {ψ : Points ℂ C // proj B C ψ = x} = Nat.card ((ker x).primesOver C) :=
  Nat.card_congr (fiberEquivPrimesOver x)

/-- The primes of `C` over the kernel of a `ℂ`-point of `B` have inertia degree `1`. -/
lemma inertiaDeg_ker_eq_one (x : Points ℂ B) (q : Ideal C) [q.IsPrime] [q.LiesOver (ker x)] :
    q.inertiaDeg B = 1 := by
  have : Algebra.FiniteType ℂ C := .trans (S := B) inferInstance inferInstance
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := ker x) (P := q)
  obtain ⟨ψ, hψ⟩ := exists_ker_eq (K := ℂ) q
  rw [Ideal.inertiaDeg_eq_of_isMaximal (ker x) q]
  let := Ideal.Quotient.field (ker x)
  have hbij : Function.Bijective (algebraMap (B ⧸ ker x) (C ⧸ q)) := by
    refine ⟨RingHom.injective _, fun c ↦ ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨Ideal.Quotient.mk _ (algebraMap ℂ B (ψ c)), ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq,
      ← IsScalarTower.algebraMap_apply, ← neg_sub]
    refine q.neg_mem_iff.mpr ?_
    rw [← hψ]
    exact sub_algebraMap_mem_ker ψ c
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap (B ⧸ ker x) (C ⧸ q)) hbij).finrank_eq,
    Module.finrank_self]

section Etale

variable [IsDomain B] [Module.Flat B C]

omit [Algebra.FiniteType ℂ B] [IsDomain B] in
lemma perfectField_residueField_ker (x : Points ℂ B) : PerfectField (ker x).ResidueField :=
  have : CharZero (ker x).ResidueField := charZero_of_injective_ringHom
    (f := (algebraMap B (ker x).ResidueField).comp (algebraMap ℂ B)) (RingHom.injective _)
  inferInstance

/-- Over a point `x ∈ X(ℂ)` at which `C` is unramified over `B`, the fibre of `Y(ℂ) → X(ℂ)` has
exactly `n` points, `n` the rank of `C` over `B`. -/
theorem card_fiber_eq_finrank (x : Points ℂ B)
    (hx : ∀ (q : Ideal C) [q.IsPrime] [q.LiesOver (ker x)], Algebra.IsUnramifiedAt B q) :
    Nat.card {ψ : Points ℂ C // proj B C ψ = x} = finrank B C := by
  rw [card_fiber_eq_card_primesOver]
  exact RiemannExtension.card_primesOver_eq_finrank (ker x) fun q _ _ ↦
    ⟨hx q, inertiaDeg_ker_eq_one x q⟩

/-- **Étaleness by counting points**: let `B` be a domain of finite type over `ℂ` in which every
nonzero prime is maximal, `C` a finite flat `B`-algebra of rank `n`, and `h ≠ 0` in `B` such that
`C[1/h]` is unramified over `B`. If over every `x ∈ X(ℂ)` with `h(x) = 0` the fibre of
`Y(ℂ) → X(ℂ)` has at least `n` points, then `C` is étale over `B`. -/
theorem etale_of_forall_card_fiber (hmax : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    {h : B} (hh : h ≠ 0)
    (hunr : Algebra.FormallyUnramified B (Localization.Away (algebraMap B C h)))
    (hcard : ∀ x : Points ℂ B, x h = 0 →
      finrank B C ≤ Nat.card {ψ : Points ℂ C // proj B C ψ = x}) :
    Algebra.Etale B C := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  have : Algebra.FinitePresentation B C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyUnramified B C := by
    rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro Q
    by_cases hQ : algebraMap B C h ∈ Q.asIdeal
    · set p := Q.asIdeal.under B
      have hp : p ≠ ⊥ := fun h0 ↦ hh (by
        have : h ∈ p := hQ
        rwa [h0, Ideal.mem_bot] at this)
      have : p.IsMaximal := hmax p inferInstance hp
      obtain ⟨x, hx⟩ := exists_ker_eq (K := ℂ) p
      have hxh : x h = 0 := mem_ker.mp (by rw [hx]; exact hQ)
      have : Q.asIdeal.LiesOver (ker x) := ⟨by rw [hx]⟩
      have := perfectField_residueField_ker x
      exact RiemannExtension.isUnramifiedAt_of_finrank_le_card (ker x)
        (by rw [← card_fiber_eq_card_primesOver]; exact hcard x hxh) Q.asIdeal
    · exact (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hunr) hQ
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Etale

end Points

end SGA.SGA1.ExposeXII
