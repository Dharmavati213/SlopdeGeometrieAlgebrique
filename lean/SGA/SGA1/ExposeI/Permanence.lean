/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import SGA.SGA1.ExposeI.TraceFormulas

/-!
# SGA 1, Exposé I, §9: permanence properties

Proved here:

* reducedness (I.9.2–I.9.3): over a reduced noetherian ring, a flat, formally unramified,
  essentially finite type algebra is reduced, with SGA's proof through the minimal
  primes; the scheme version for étale morphisms, and descent along surjective ones;
* normality (I.9.5(i), I.9.10): SGA's second proof. Smooth base change commutes with integral
  closure (mathlib), so an étale `B` over an integrally closed domain `A` is integrally
  closed in `B ⊗_A K`; each local ring `B_q` is then an integrally closed domain, since
  the idempotents of the artinian ring `B_q ⊗_A K` are integral over `B_q`. Conversely
  normality descends along faithfully flat maps of domains. For schemes (all local rings
  integrally closed domains, `IsNormalScheme`) this gives I.9.10 in both directions;
* I.9.5(ii): an injective unramified local algebra `B`, essentially of finite type over an
  integrally closed domain `A`, is flat. By I.7.6 `B` is a quotient of a local ring `C_P`
  of a standard étale algebra; the generic fibre of `C_P` is a field (as in I.9.5(i)),
  so the kernel is `A`-torsion, hence zero;
* the integral closure bound I.9.9 (`F'(u) A' ⊆ A[u]`), and the trace formulas I.9.6–I.9.8
  when `L` is a field (from mathlib's trace dual of a power basis); over an arbitrary base ring
  they are in `TraceFormulas`;
* regularity (I.9.1 and its corollary in I.9.2): for a flat local `A → B` with
  `m_A B = m_B`, `dim B = dim A` (going down and Krull's height theorem give
  `dim B = dim A + dim B/m_A B`), and `m_A`, `m_B` need the same number of generators
  (a basis of `m_B/m_B²` can be lifted to `m_A`, and ideals of `A` are contracted from `B`);
* I.9.12, pointwise: for `f` dominant, locally of finite type, `Y` normal and `X`
  irreducible, the stalk maps are injective, so `f` is flat wherever it is unramified.

I.9.4 (completions) is in `CompletionCriteria`, I.9.11 in `DominantUnramified`.
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra IsLocalRing TensorProduct Polynomial

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

section Reduced

/-- In a reduced ring, the localization at a minimal prime is a field. -/
theorem isField_localization_atPrime_of_mem_minimalPrimes [IsReduced A] {p : Ideal A}
    [p.IsPrime] (hp : p ∈ minimalPrimes A) : IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime p) p ⊥ hp
  rw [Ideal.map_bot, Localization.AtPrime.map_eq_maximalIdeal] at h
  rw [← h]
  exact nilradical_eq_zero _

/-- In a reduced ring, an element outside all minimal primes is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes [IsReduced A] {a : A}
    (ha : ∀ p ∈ minimalPrimes A, a ∉ p) : a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  by_contra hy0
  have : a ∈ ⋃ p ∈ minimalPrimes A, (p : Set A) := by
    rw [minimalPrimes, Ideal.iUnion_minimalPrimes]
    have hr : (⊥ : Ideal A).radical = ⊥ := nilradical_eq_zero A
    refine ⟨y, ?_, ?_⟩
    · rwa [hr, Ideal.mem_bot]
    · rw [hr, Ideal.mem_bot, mul_comm]
      exact hy
  simp only [Set.mem_iUnion, SetLike.mem_coe] at this
  obtain ⟨p, hp, hap⟩ := this
  exact ha p hp hap


/-- I.9.3, necessity of reducedness transferring upwards, in global form: over a reduced
noetherian ring `A`, a flat, formally unramified, essentially finite type algebra `B`
(e.g. an étale algebra, or a local ring of one) is reduced. As in SGA, `B ⊗_A A_p` is
étale over the field `A_p` for each minimal prime `p`, hence reduced, and flatness
lets one conclude. -/
theorem isReduced_of_flat_of_formallyUnramified [IsNoetherianRing A] [IsReduced A]
    [Module.Flat A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    IsReduced B := by
  refine ⟨fun x hx ↦ ?_⟩
  -- for each minimal prime `p`, some `a ∉ p` kills `x`
  have key : ∀ p ∈ minimalPrimes A, ∃ a ∉ p, a • x = 0 := by
    intro p hp
    have := hp.isPrime
    let : Field (Localization.AtPrime p) :=
      (isField_localization_atPrime_of_mem_minimalPrimes hp).toField
    have hred := FormallyUnramified.isReduced_of_field (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] B)
    have h0 : (1 : Localization.AtPrime p) ⊗ₜ[A] x = 0 :=
      (hx.map (Algebra.TensorProduct.includeRight (R := A) (A := Localization.AtPrime p))).eq_zero
    have : IsLocalizedModule p.primeCompl (TensorProduct.mk A (Localization.AtPrime p) B 1) :=
      (isLocalizedModule_iff_isBaseChange p.primeCompl (Localization.AtPrime p) _).mpr
        (TensorProduct.isBaseChange A B (Localization.AtPrime p))
    obtain ⟨⟨a, ha⟩, hax⟩ :=
      (IsLocalizedModule.eq_zero_iff p.primeCompl
        (TensorProduct.mk A (Localization.AtPrime p) B 1)).mp h0
    exact ⟨a, ha, hax⟩
  -- by prime avoidance, the annihilator of `x` contains a non-zero-divisor
  let J : Ideal A := (Submodule.span A {x}).annihilator
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hJ : ¬ (J : Set A) ⊆ ⋃ p ∈ (↑hfin.toFinset : Set (Ideal A)), ((id p : Ideal A) : Set A) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
      fun p hp _ _ ↦ ((hfin.mem_toFinset.mp hp).isPrime)]
    rintro ⟨p, hp, hJp⟩
    obtain ⟨a, ha, hax⟩ := key p (hfin.mem_toFinset.mp hp)
    exact ha (hJp ((Submodule.mem_annihilator_span_singleton x a).mpr hax))
  obtain ⟨a, haJ, hanot⟩ := Set.not_subset.mp hJ
  have hreg : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_forall_notMem_minimalPrimes
    fun p hp hap ↦ hanot (Set.mem_biUnion (by simpa using hp) hap)
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors hreg).right_eq_zero_of_smul
    ((Submodule.mem_annihilator_span_singleton x a).mp haJ)

/-- I.9.3, sufficiency: if `A → B` is faithfully flat (e.g. a local étale homomorphism)
and `B` is reduced, so is `A`. -/
theorem isReduced_of_faithfullyFlat [Module.FaithfullyFlat A B] [IsReduced B] : IsReduced A :=
  isReduced_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

/-- I.9.3 for local rings: a local étale homomorphism `A → B` (flat, formally unramified,
essentially of finite type) of noetherian local rings: `A` is reduced iff `B` is. -/
theorem isReduced_iff_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType A B] : IsReduced A ↔ IsReduced B := by
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact ⟨fun _ ↦ isReduced_of_flat_of_formallyUnramified (A := A) (B := B),
    fun _ ↦ isReduced_of_faithfullyFlat (B := B)⟩

open AlgebraicGeometry in
/-- I.9.2 (the proposition): if `f : X ⟶ Y` is étale and `Y` is reduced (and locally
noetherian, the exposé's standing hypothesis), then `X` is reduced. -/
theorem isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsReduced Y] [Etale f] : AlgebraicGeometry.IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have h₁ := Flat.stalkMap f x
    have h₂ := FormallyUnramified.stalkMap f x
    have h₃ := LocallyOfFiniteType.stalkMap f x
    algebraize [(f.stalkMap x).hom]
    exact isReduced_of_flat_of_formallyUnramified (A := Y.presheaf.stalk (f x))
  exact isReduced_of_isReduced_stalk X

open AlgebraicGeometry in
/-- I.9.2 (the proposition), converse: if `f : X ⟶ Y` is flat and surjective (e.g.
étale and surjective) and `X` is reduced, then `Y` is reduced. -/
theorem isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Surjective f] [AlgebraicGeometry.IsReduced X] : AlgebraicGeometry.IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    have h₁ := Flat.stalkMap f x
    algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x))
      (B := X.presheaf.stalk x)
    exact isReduced_of_faithfullyFlat (B := X.presheaf.stalk x)
  exact isReduced_of_isReduced_stalk Y

end Reduced

section Normal

variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]

/-- For `B` flat over a domain `A` with fraction field `K`, the map `B → B ⊗_A K` is
injective (a localization at non-zero-divisors). -/
theorem injective_algebraMap_tensor_fractionRing [Module.Flat A B] :
    Function.Injective (algebraMap B (B ⊗[A] K)) := by
  refine IsLocalization.injective (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) _ ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha)
  exact this.right_eq_zero_of_smul (by rwa [Algebra.smul_def, mul_comm])

/-- If `A` is integrally closed with fraction field `K`, `B` is flat over `A`, and base
change `B ⊗_A -` commutes with integral closure in `K`, then `B` is integrally closed
in `B ⊗_A K`. -/
theorem isIntegrallyClosedIn_tensor_fractionRing_of_bijective [IsIntegrallyClosed A]
    [Module.Flat A B] (hbij : Function.Bijective (TensorProduct.toIntegralClosure A B K)) :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  refine ⟨injective_algebraMap_tensor_fractionRing K, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := hbij.2 ⟨x, hx⟩
    have hbot := IsIntegrallyClosed.integralClosure_eq_bot A K
    suffices H : ∀ t, ∃ y, algebraMap B (B ⊗[A] K) y =
        (TensorProduct.toIntegralClosure A B K t : B ⊗[A] K) by
      obtain ⟨y, hy⟩ := H t
      exact ⟨y, hy.trans (congrArg Subtype.val ht)⟩
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | add s t hs ht =>
      obtain ⟨a, ha⟩ := hs
      obtain ⟨b, hb⟩ := ht
      exact ⟨a + b, by rw [map_add, map_add, Subalgebra.coe_add, ha, hb]⟩
    | tmul b c =>
      have : (c : K) ∈ (⊥ : Subalgebra A K) := hbot ▸ c.2
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp this
      refine ⟨a • b, ?_⟩
      change algebraMap B (B ⊗[A] K) (a • b) = b ⊗ₜ[A] (c : K)
      rw [← ha, Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
  · rintro ⟨y, rfl⟩
    exact isIntegral_algebraMap

/-- I.9.5(i), the key step (second proof in SGA): if `A` is an integrally closed domain
with fraction field `K` and `B` is smooth (e.g. étale) over `A`, then `B` is integrally
closed in `B ⊗_A K`. This is smooth base change of integral closures (I.10.5). -/
theorem isIntegrallyClosedIn_tensor_fractionRing [IsIntegrallyClosed A] [Algebra.Smooth A B] :
    IsIntegrallyClosedIn B (B ⊗[A] K) :=
  isIntegrallyClosedIn_tensor_fractionRing_of_bijective K
    TensorProduct.toIntegralClosure_bijective_of_smooth

/-- I.9.5(i), sufficiency, when `B` is a domain: an étale domain over an integrally
closed domain is integrally closed. (`B ⊗_A K` is then the fraction field of `B`.) -/
theorem isIntegrallyClosed_of_etale [IsDomain A] [IsIntegrallyClosed A] [Algebra.Etale A B]
    [IsDomain B] : IsIntegrallyClosed B := by
  let K := FractionRing A
  let L := B ⊗[A] K
  have hinj : Function.Injective (algebraMap B L) := injective_algebraMap_tensor_fractionRing K
  -- the submonoid `A \ {0}` consists of non-zero-divisors of `B`
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha).right_eq_zero_of_smul
      (x := (1 : B)) (by rw [Algebra.smul_def, mul_one, h0])
    exact one_ne_zero this
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L
    (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) hM
  -- `L ≅ K ⊗_A B` is finite over the field `K`, hence a field
  let e : L ≃ₐ[A] K ⊗[A] B := Algebra.TensorProduct.comm A B K
  have : IsDomain (K ⊗[A] B) := e.toMulEquiv.isDomain_iff.mp inferInstance
  have : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K _
  have hL : IsField L := MulEquiv.isField
    (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)) e.toMulEquiv
  let : Field L := hL.toField
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr hinj
  have : IsFractionRing B L := IsFractionRing.of_field B L fun z ↦ by
    obtain ⟨⟨b, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) z
    refine ⟨b, s, ?_⟩
    have hs := IsLocalization.map_units L s
    rw [eq_div_iff hs.ne_zero]
    exact IsLocalization.mk'_spec L b s
  exact (isIntegrallyClosed_iff L).mpr fun hx ↦
    (isIntegrallyClosedIn_tensor_fractionRing (A := A) K).isIntegral_iff.mp hx

/-- I.9.5(i), necessity (first part of the second proof in SGA): if `A → B` is faithfully
flat (e.g. a local étale homomorphism) of domains and `B` is integrally closed, then so
is `A`, because `B ∩ K = A` inside the fraction field of `B`. -/
theorem isIntegrallyClosed_of_faithfullyFlat [IsDomain A] [IsDomain B]
    [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  let K := FractionRing A
  let L := FractionRing B
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hg : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
    (IsFractionRing.injective B L).comp hAB
  let φ : K →+* L := IsFractionRing.lift hg
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hφ : (algebraMap B L).comp (algebraMap A B) = φ.comp (algebraMap A K) := by
    ext a; simp [φ, IsFractionRing.lift_algebraMap]
  have hx' : IsIntegral B (φ (algebraMap A K a / algebraMap A K s)) :=
    IsIntegral.map_of_comp_eq (algebraMap A B) φ hφ hx
  obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff L).mp inferInstance hx'
  have hs0 : algebraMap A B s ≠ 0 := by
    rw [← map_zero (algebraMap A B)]
    exact hAB.ne (nonZeroDivisors.ne_zero hs)
  have hbs : b * algebraMap A B s = algebraMap A B a := by
    apply IsFractionRing.injective B L
    rw [map_mul, hb, map_div₀]
    have h1 := congr($hφ a)
    have h2 := congr($hφ s)
    simp only [RingHom.comp_apply] at h1 h2
    rw [← h1, ← h2, div_mul_cancel₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hs0
  have ha : a ∈ Ideal.span {s} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {s}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨b, hbs⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨c, ?_⟩
  rw [map_mul, mul_div_assoc, div_self, mul_one]
  exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hs)

/-- A reduced artinian ring without non-trivial idempotents is a field. -/
theorem isField_of_isArtinianRing_of_isReduced (L : Type*) [CommRing L] [IsArtinianRing L]
    [IsReduced L] [Nontrivial L] (h : ∀ e : L, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField L := by
  classical
  have : IsLocalRing L := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨m, hm⟩ := Ideal.exists_maximal L
    refine ⟨m, hm, fun m' hm' ↦ ?_⟩
    by_contra hne
    let e : L := (IsArtinianRing.equivPi L).symm (Pi.single ⟨m, hm⟩ 1)
    have he : IsIdempotentElem e := by
      rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
    have hne' : (⟨m', hm'⟩ : MaximalSpectrum L) ≠ ⟨m, hm⟩ := fun h ↦ hne (by
      simpa using congrArg MaximalSpectrum.asIdeal h)
    rcases h e he with h0 | h1
    · have := congr($(h0) |> IsArtinianRing.equivPi L)
      simp only [e, AlgEquiv.apply_symm_apply, map_zero] at this
      have := congr_fun this ⟨m, hm⟩
      simp only [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero (α := L ⧸ m) this
    · have := congr($(h1) |> IsArtinianRing.equivPi L)
      simp only [e, AlgEquiv.apply_symm_apply, map_one] at this
      have := congr_fun this ⟨m', hm'⟩
      simp only [Pi.single_eq_of_ne hne', Pi.one_apply] at this
      exact zero_ne_one (α := L ⧸ m') this
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing L

omit [Algebra A B] in
/-- An idempotent in a local ring is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing [IsLocalRing B] {b : B}
    (hb : IsIdempotentElem b) : b = 0 ∨ b = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp hb)
  · exact Or.inl (by simpa using (IsIdempotentElem.iff_eq_one_of_isUnit h).mp hb.one_sub)

/-- The generic fibre `B_q ⊗_A K` of a local ring `B_q` of an étale algebra `B` over an
integrally closed domain `A` is a field: it is a reduced artinian ring whose idempotents are
integral over the local ring `B_q`. -/
theorem isField_localization_tensor_fractionRing_of_etale [IsDomain A] [IsIntegrallyClosed A]
    [Algebra.Etale A B] (q : Ideal B) [q.IsPrime] :
    IsField (Localization.AtPrime q ⊗[A] FractionRing A) := by
  let K := FractionRing A
  let Bq := Localization.AtPrime q
  let L := Bq ⊗[A] K
  have : Module.Flat A Bq := Module.Flat.trans A B Bq
  have hbij : Function.Bijective (TensorProduct.toIntegralClosure A Bq K) :=
    TensorProduct.toIntegralClosure_bijective_of_tower
      TensorProduct.toIntegralClosure_bijective_of_smooth
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization q.primeCompl)
  have hIC : IsIntegrallyClosedIn Bq L :=
    isIntegrallyClosedIn_tensor_fractionRing_of_bijective K hbij
  have hinj : Function.Injective (algebraMap Bq L) := injective_algebraMap_tensor_fractionRing K
  -- `L ≅ K ⊗_A B_q` is a reduced artinian `K`-algebra
  let e : L ≃ₐ[A] K ⊗[A] Bq := Algebra.TensorProduct.comm A Bq K
  have : Nontrivial L := hinj.nontrivial
  have : Module.Finite K (K ⊗[A] Bq) := Algebra.FormallyUnramified.finite_of_free K _
  have : IsArtinianRing (K ⊗[A] Bq) := isArtinian_of_tower K inferInstance
  have : IsReduced (K ⊗[A] Bq) := FormallyUnramified.isReduced_of_field K _
  have : IsArtinianRing L := e.symm.toRingEquiv.isArtinianRing
  have : IsReduced L := isReduced_of_injective e.toRingHom e.injective
  -- its idempotents are integral over the local ring `B_q`, hence trivial
  exact isField_of_isArtinianRing_of_isReduced L fun x hx ↦ by
    have : IsIntegral Bq x := ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (by simp), by simp [sq, hx.eq]⟩
    obtain ⟨b, rfl⟩ := hIC.isIntegral_iff.mp this
    have hb : IsIdempotentElem b := hinj (by rw [map_mul, hx.eq])
    rcases IsIdempotentElem.eq_zero_or_one_of_isLocalRing hb with rfl | rfl
    · exact Or.inl (map_zero _)
    · exact Or.inr (map_one _)

/-- I.9.5(i), sufficiency: let `A` be an integrally closed domain and `B` an étale
`A`-algebra. Then every local ring `B_q` of `B` is an integrally closed domain.
(SGA's `B` is a local ring essentially of finite type and étale over `A`, i.e. such a
`B_q`.) -/
theorem isDomain_and_isIntegrallyClosed_localization_of_etale [IsDomain A]
    [IsIntegrallyClosed A] [Algebra.Etale A B] (q : Ideal B) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let K := FractionRing A
  let Bq := Localization.AtPrime q
  let L := Bq ⊗[A] K
  have : Module.Flat A Bq := Module.Flat.trans A B Bq
  have hbij : Function.Bijective (TensorProduct.toIntegralClosure A Bq K) :=
    TensorProduct.toIntegralClosure_bijective_of_tower
      TensorProduct.toIntegralClosure_bijective_of_smooth
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization q.primeCompl)
  have hIC : IsIntegrallyClosedIn Bq L :=
    isIntegrallyClosedIn_tensor_fractionRing_of_bijective K hbij
  have hinj : Function.Injective (algebraMap Bq L) := injective_algebraMap_tensor_fractionRing K
  let : Field L := (isField_localization_tensor_fractionRing_of_etale q).toField
  have : IsDomain Bq := hinj.isDomain _
  refine ⟨this, ?_⟩
  have : FaithfulSMul Bq L := (faithfulSMul_iff_algebraMap_injective Bq L).mpr hinj
  have : IsFractionRing Bq L := IsFractionRing.of_field Bq L fun z ↦ by
    obtain ⟨⟨b, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid Bq (nonZeroDivisors A)) z
    refine ⟨b, s, ?_⟩
    have hs := IsLocalization.map_units L s
    rw [eq_div_iff hs.ne_zero]
    exact IsLocalization.mk'_spec L b s
  exact (isIntegrallyClosed_iff L).mpr fun hx ↦ hIC.isIntegral_iff.mp hx

end Normal


attribute [local instance] Polynomial.algebra in
/-- I.9.9: let `A` be an integrally closed domain with fraction field `K`, `F` a monic
polynomial over `A`, `L = K[t]/(F)` and `u` the class of `t`. Then every element `y` of
`L` integral over `A` satisfies `F'(u) y ∈ A[u]`: the integral closure of `A` in `L` lies
in `A[u] / F'(u)`. (SGA assumes `F` separable over `K`; this is not needed.) -/
theorem exists_derivative_mul_eq_of_isIntegral [IsDomain A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] {F : A[X]} (hF : F.Monic)
    {y : AdjoinRoot (F.map (algebraMap A K))} (hy : IsIntegral A y) :
    ∃ G : A[X], aeval (AdjoinRoot.root (F.map (algebraMap A K))) (derivative F) * y =
      aeval (AdjoinRoot.root (F.map (algebraMap A K))) G := by
  set f := F.map (algebraMap A K)
  let φ : K[X] →ₐ[A] AdjoinRoot f := (Ideal.Quotient.mkₐ K (Ideal.span {f})).restrictScalars A
  obtain ⟨g, hg, hgi⟩ := exists_derivative_mul_eq_and_isIntegral_coeff (R := A) (φ := φ)
    (Ideal.Quotient.mkₐ_surjective K _) (hF.map _) (fun i ↦ by
      rw [coeff_map]; exact isIntegral_algebraMap) (Ideal.Quotient.mkₐ_ker K _) hy
  have hlift : g ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact (isIntegrallyClosed_iff K).mp inferInstance (hgi i)
  obtain ⟨G, rfl⟩ := hlift
  refine ⟨G, ?_⟩
  have hφ (P : A[X]) : φ (P.map (algebraMap A K)) = aeval (AdjoinRoot.root f) P := by
    rw [AdjoinRoot.aeval_eq_of_algebra]; rfl
  rw [← hφ, ← hφ, ← derivative_map]
  exact hg

/-- I.9.6 and I.9.8, over a field: for a power basis `1, u, …, u^(n-1)` of a finite
separable extension `L/K`, the trace dual basis is `aᵢ / F'(u)`, where `F` is the minimal
polynomial of `u` and `F / (t - u) = ∑ aᵢ tⁱ` (mathlib). Since `aᵢ` is monic of degree
`n - 1 - i` in `u`, this is SGA's statement that the dual of `A[u]` is spanned by the
`uⁱ / F'(u)`. -/
theorem traceDual_powerBasis_eq {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (pb : PowerBasis K L) (i : Fin pb.dim) :
    pb.basis.traceDual i =
      (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)) :=
  Module.Basis.traceDual_powerBasis_eq pb i

section TraceFormulas

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- I.9.6, over a field: let `u` generate the finite separable extension `L/K`, with
minimal polynomial `F` of degree `n`. Then `Tr_{L/K}(uⁱ / F'(u)) = 0` for `0 ≤ i < n - 1`
and `Tr_{L/K}(u^(n-1) / F'(u)) = 1`. -/
theorem trace_pow_div_aeval_derivative (pb : PowerBasis K L) {i : ℕ} (hi : i < pb.dim) :
    trace K L (pb.gen ^ i / aeval pb.gen (derivative (minpoly K pb.gen))) =
      if i = pb.dim - 1 then 1 else 0 := by
  have hn := pb.dim_pos
  let j : Fin pb.dim := ⟨pb.dim - 1, by omega⟩
  have hdeg : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by
    rw [natDegree_minpolyDiv, pb.natDegree_minpoly]
  have hj : pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
    rw [traceDual_powerBasis_eq]
    congr 1
    rw [show ((j : ℕ)) = (minpolyDiv K pb.gen).natDegree from hdeg.symm]
    exact (minpolyDiv_monic (R := K) (x := pb.gen) (pb.isIntegral_gen)).coeff_natDegree
  have := pb.basis.trace_traceDual_mul j ⟨i, hi⟩
  rw [hj, pb.coe_basis, one_div, inv_mul_eq_div] at this
  rw [this]
  simp [j, Fin.ext_iff]

/-- I.9.7, over a field: the matrix `(Tr_{L/K}(uʲ uⁱ / F'(u)))_{0 ≤ i, j < n}` has
determinant `(-1)^(n(n-1)/2)`; in particular it is invertible in every subring of `K`. -/
theorem det_trace_pow_mul_pow_div_aeval_derivative (pb : PowerBasis K L) :
    (Matrix.of fun i j : Fin pb.dim ↦ trace K L
      (pb.gen ^ (j : ℕ) * pb.gen ^ (i : ℕ) / aeval pb.gen (derivative (minpoly K pb.gen)))).det =
      (-1) ^ (pb.dim * (pb.dim - 1) / 2) := by
  set d := aeval pb.gen (derivative (minpoly K pb.gen))
  set M := Matrix.of fun i j : Fin pb.dim ↦ trace K L (pb.gen ^ (j : ℕ) * pb.gen ^ (i : ℕ) / d)
  have hM' : (M.submatrix id Fin.revPerm).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ ?_]
    · refine Finset.prod_eq_one fun i _ ↦ ?_
      have := i.isLt
      simp only [Matrix.submatrix_apply, _root_.id, M, Matrix.of_apply, Fin.revPerm_apply,
        Fin.val_rev, ← pow_add]
      rw [trace_pow_div_aeval_derivative pb (by omega), ite_eq_left (by omega)]
    · intro i j hij
      have := j.isLt
      simp only [Matrix.submatrix_apply, _root_.id, M, Matrix.of_apply, Fin.revPerm_apply,
        Fin.val_rev, ← pow_add]
      have : (i : ℕ) < j := hij
      rw [trace_pow_div_aeval_derivative pb (by omega), ite_eq_right (by omega)]
  rw [Matrix.det_permute', sign_revPerm] at hM'
  push_cast at hM'
  calc M.det = (-1) ^ (pb.dim * (pb.dim - 1) / 2) *
        ((-1) ^ (pb.dim * (pb.dim - 1) / 2) * M.det) := by
        rw [← mul_assoc, ← mul_pow]; simp
    _ = (-1) ^ (pb.dim * (pb.dim - 1) / 2) := by rw [hM', mul_one]

end TraceFormulas

section Unramified

/-- The generic-fibre argument of I.9.5(ii): let `A` be a domain with fraction field `K`,
`D` a flat `A`-algebra whose generic fibre `D ⊗_A K` is a field, and `ψ : D → B` a map of
`A`-algebras, `A → B` injective. Then `ψ` is injective. -/
theorem injective_of_isField_tensor_fractionRing [IsDomain A] {D : Type u} [CommRing D]
    [Algebra A D] [Module.Flat A D] (hD : IsField (D ⊗[A] FractionRing A)) (ψ : D →ₐ[A] B)
    (hA : Function.Injective (algebraMap A B)) : Function.Injective ψ := by
  let K := FractionRing A
  let M := nonZeroDivisors A
  rw [injective_iff_map_eq_zero]
  intro x hx
  have : Nontrivial (B ⊗[A] K) := by
    refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨⟨_, a, ha, rfl⟩, h1⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid B M) (B ⊗[A] K) 1).mp (by rw [map_one]; exact h)
    rw [mul_one] at h1
    exact nonZeroDivisors.ne_zero ha (hA (by simpa using h1))
  let := hD.toField
  let Ψ := Algebra.TensorProduct.map ψ (AlgHom.id A K)
  have h0 : algebraMap D (D ⊗[A] K) x = 0 := by
    apply Ψ.toRingHom.injective
    rw [map_zero]
    change Ψ (x ⊗ₜ 1) = 0
    simp [Ψ, hx]
  obtain ⟨⟨_, a, ha, rfl⟩, h1⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid D M) _ x).mp h0
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors ha).right_eq_zero_of_smul
    (by rwa [Algebra.smul_def])

/-- I.7.6 in the form used for I.9.5(ii): a local algebra `B`, unramified and essentially of
finite type over `A`, is a quotient of a local ring `C_P` of an étale `A`-algebra `C`, with `P`
the inverse image of `𝔪_B`. -/
theorem exists_etale_localization_surjective [IsLocalRing B] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType A B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (P : Ideal C)
      (_ : P.IsPrime) (ψ : Localization.AtPrime P →ₐ[A] B), Function.Surjective ψ ∧
      P.comap (algebraMap A C) = (maximalIdeal B).comap (algebraMap A B) := by
  -- `B` is a localization of a finite type `A`-algebra `B'` at a prime `Q`
  let B' := EssFiniteType.subalgebra A B
  let M' := EssFiniteType.submonoid A B
  let Q := (maximalIdeal B).comap (algebraMap B' B)
  have : IsLocalization.AtPrime B (maximalIdeal B) :=
    IsLocalization.of_le_isUnit fun x hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx
  have : IsLocalization.AtPrime B Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M' B (maximalIdeal B)
  let e : Localization.AtPrime Q ≃ₐ[A] B :=
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) B).restrictScalars A
  have : IsUnramifiedAt A Q := FormallyUnramified.of_equiv e.symm
  -- I.7.6: near `Q`, `B'` is a quotient of a standard étale algebra `C`
  obtain ⟨f, hfQ, P₀, φ, hφ⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) Q
  have hunit (y : B') (hy : y ∉ Q) : IsUnit (algebraMap B' B y) :=
    IsLocalRing.notMem_maximalIdeal.mp hy
  let g : Localization.Away f →ₐ[A] B := IsLocalization.liftAlgHom
    (M := Submonoid.powers f) (f := IsScalarTower.toAlgHom A B' B) fun y ↦ by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      change IsUnit (algebraMap B' B y)
      rw [← hn, map_pow]
      exact (hunit f hfQ).pow n
  have hg (x : B') : g (algebraMap B' _ x) = algebraMap B' B x :=
    IsLocalization.lift_eq _ x
  -- the local ring `C_P` of `C` at the preimage of `m_B` maps onto `B`
  let ψ₀ := g.comp φ
  let P := (maximalIdeal B).comap ψ₀
  let D := Localization.AtPrime P
  let ψ : D →ₐ[A] B := IsLocalization.liftAlgHom (M := P.primeCompl) (f := ψ₀)
    fun y ↦ IsLocalRing.notMem_maximalIdeal.mp y.2
  have hsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M' b
    obtain ⟨c₁, hc₁⟩ := hφ (algebraMap B' _ x)
    obtain ⟨c₂, hc₂⟩ := hφ (algebraMap B' _ (s : B'))
    have h₁ : ψ₀ c₁ = algebraMap B' B x := by simp [ψ₀, hc₁, hg]
    have h₂ : ψ₀ c₂ = algebraMap B' B s := by simp [ψ₀, hc₂, hg]
    have hc₂P : c₂ ∈ P.primeCompl := by
      change ψ₀ c₂ ∉ maximalIdeal B
      rw [h₂]
      exact IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units B s)
    refine ⟨IsLocalization.mk' D c₁ ⟨c₂, hc₂P⟩, ?_⟩
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h₁, h₂]
    exact (IsLocalization.mk'_spec' B x s).symm
  refine ⟨P₀.Ring, inferInstance, inferInstance, inferInstance, P, inferInstance, ψ, hsurj, ?_⟩
  ext a
  simp [P, Ideal.mem_comap]

/-- The generic fibre `C_P ⊗_A K` of a local ring `C_P` of an étale algebra `C` over a domain `A`
is a field if `C_P` is a domain (a reduced artinian localization of `C_P`). -/
theorem isField_localization_tensor_fractionRing_of_isDomain [IsDomain A] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] [IsDomain (Localization.AtPrime q)] :
    IsField (Localization.AtPrime q ⊗[A] FractionRing A) := by
  let K := FractionRing A
  let Bq := Localization.AtPrime q
  let L := Bq ⊗[A] K
  have : Module.Flat A Bq := Module.Flat.trans A B Bq
  let e : L ≃ₐ[A] K ⊗[A] Bq := Algebra.TensorProduct.comm A Bq K
  have : Module.Finite K (K ⊗[A] Bq) := Algebra.FormallyUnramified.finite_of_free K _
  have : IsArtinianRing (K ⊗[A] Bq) := isArtinian_of_tower K inferInstance
  have : IsArtinianRing L := e.symm.toRingEquiv.isArtinianRing
  have : IsDomain L := by
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid Bq
      (nonZeroDivisors A)) _ ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Bq) ha)
    exact this.right_eq_zero_of_smul (by rwa [Algebra.smul_def, mul_comm])
  exact IsArtinianRing.isField_of_isDomain L

/-- I.9.5(ii): let `A` be an integrally closed domain and `B` a local `A`-algebra,
essentially of finite type and unramified over `A`, with `A → B` injective. Then `B` is
flat over `A` (so `A → B` is étale). This is the direction ⇐ of SGA's equivalence; ⇒ holds
because a flat local homomorphism is faithfully flat, hence injective. By I.7.6, `B` is a
quotient of a local ring `C_P` of an étale `A`-algebra `C` (`exists_etale_localization_surjective`);
`C_P` has a field as generic fibre (I.9.5(i)), so the kernel is `A`-torsion, hence zero. -/
theorem flat_of_injective_of_formallyUnramified [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalRing B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (hA : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  obtain ⟨C, _, _, _, P, _, ψ, hsurj, -⟩ := exists_etale_localization_surjective (A := A) (B := B)
  have : Module.Flat A (Localization.AtPrime P) := Module.Flat.trans A C _
  have hinj : Function.Injective ψ := injective_of_isField_tensor_fractionRing
    (isField_localization_tensor_fractionRing_of_etale P) ψ hA
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.toLinearEquiv

end Unramified

section NormalSchemes

/-- `IsDomain ∧ IsIntegrallyClosed` transfers along ring isomorphisms. -/
lemma isDomain_and_isIntegrallyClosed_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsDomain R ∧ IsIntegrallyClosed R) : IsDomain S ∧ IsIntegrallyClosed S := by
  obtain ⟨_, _⟩ := h
  have : IsDomain S := e.symm.injective.isDomain _
  exact ⟨this, IsIntegrallyClosed.of_equiv e⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- I.9.5(i) in the form used for I.9.10: let `R → S` be étale, `q` a prime of `S` over
`p`. If `R_p` is an integrally closed domain, so is `S_q`. -/
theorem isDomain_and_isIntegrallyClosed_localization_of_etale_of_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime]
    (hp : IsDomain (Localization.AtPrime (q.comap (algebraMap R S))) ∧
      IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap R S)))) :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  set p := q.comap (algebraMap R S)
  let A := Localization.AtPrime p
  obtain ⟨_, _⟩ := hp
  let B := A ⊗[R] S
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have : IsLocalization M B := IsLocalization.tensorRight (A := A) p.primeCompl
  have hdisj : Disjoint (M : Set S) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hq
    exact ha hq
  let Q : Ideal B := q.map (algebraMap S B)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B q ‹_› hdisj
  have hQc : Q.comap (algebraMap S B) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B ‹_› hdisj
  have H := isDomain_and_isIntegrallyClosed_localization_of_etale (A := A) (B := B) Q
  have : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap S B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ Q
  have : IsLocalization q.primeCompl (Localization.AtPrime Q) := by
    convert this; exact hQc.symm
  exact isDomain_and_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime q)).toRingEquiv H


lemma isDomain_and_isIntegrallyClosed_localization_congr {R : Type u} [CommRing R]
    {P₁ P₂ : Ideal R} [P₁.IsPrime] [P₂.IsPrime] (h : P₁ = P₂)
    (H : IsDomain (Localization.AtPrime P₁) ∧ IsIntegrallyClosed (Localization.AtPrime P₁)) :
    IsDomain (Localization.AtPrime P₂) ∧ IsIntegrallyClosed (Localization.AtPrime P₂) := by
  subst h; exact H

open AlgebraicGeometry in
/-- A scheme is normal if all its local rings are integrally closed domains. -/
def IsNormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

open AlgebraicGeometry in
/-- The local ring of a scheme at a point of an affine open `V` is the localization of
`Γ(X, V)` at the corresponding prime. -/
noncomputable def stalkEquivLocalization {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hx : x ∈ V) :
    X.presheaf.stalk x ≃+* Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _).toRingEquiv

open AlgebraicGeometry in
/-- I.9.10: if `f : X ⟶ Y` is étale and `Y` is normal, then `X` is normal. -/
theorem isNormalScheme_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (hY : IsNormalScheme Y) :
    IsNormalScheme X := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have h := HasRingHomProperty.appLE @Etale f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hpq : q.comap (algebraMap Γ(Y, U) Γ(X, V)) = (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1)
  have hp := isDomain_and_isIntegrallyClosed_of_ringEquiv
    (stalkEquivLocalization hU (f x) (hVU hxV)) (hY (f x))
  replace hp := isDomain_and_isIntegrallyClosed_localization_congr hpq.symm hp
  exact isDomain_and_isIntegrallyClosed_of_ringEquiv (stalkEquivLocalization hV x hxV).symm
    (isDomain_and_isIntegrallyClosed_localization_of_etale_of_localization q hp)


open AlgebraicGeometry in
/-- I.9.10, converse: if `f : X ⟶ Y` is flat and surjective (e.g. étale and surjective)
and `X` is normal, then `Y` is normal. -/
theorem isNormalScheme_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Surjective f] (hX : IsNormalScheme X) : IsNormalScheme Y := by
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨_, _⟩ := hX x
  have h₁ := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x))
    (B := X.presheaf.stalk x)
  have : IsDomain (Y.presheaf.stalk (f x)) :=
    (FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)).isDomain _
  exact ⟨this, isIntegrallyClosed_of_faithfullyFlat (B := X.presheaf.stalk x)⟩

end NormalSchemes

section UnramifiedSchemes

open AlgebraicGeometry in
/-- The local homomorphism `O_{Y, f x} → O_{X, x}` is injective if `O_{Y, f x}` is a domain
and some generization `ξ` of `x` maps to a maximal point of `Y` (a generic point of an
irreducible component). -/
theorem injective_stalkMap_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x ξ : X}
    [IsDomain (Y.presheaf.stalk (f x))] (hξ : ξ ⤳ x) (hmax : ∀ z, z ⤳ f ξ → f ξ ⤳ z) :
    Function.Injective (f.stalkMap x) := by
  obtain ⟨q, hq⟩ : ξ ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hξ
  set p := Spec.map (f.stalkMap x) q
  have hp : Y.fromSpecStalk (f x) p = f ξ := by
    rw [← hq, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Hom.comp_apply]
  let p₀ : Spec (Y.presheaf.stalk (f x)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Y.presheaf.stalk (f x)))
  have h₁ : p ⤳ p₀ := by
    rw [← (Y.fromSpecStalk (f x)).isEmbedding.specializes_iff, hp]
    apply hmax
    rw [← hp]
    exact ((PrimeSpectrum.le_iff_specializes p₀ p).mp bot_le).map
      (Y.fromSpecStalk (f x)).continuous
  have hp₀ : p.asIdeal = ⊥ := le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr h₁)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ p.asIdeal := by
    change (f.stalkMap x).hom a ∈ q.asIdeal
    rw [ha]
    exact zero_mem _
  rwa [hp₀, Ideal.mem_bot] at this

open AlgebraicGeometry in
/-- I.9.12: let `f : X ⟶ Y` be dominant, locally of finite type, with `Y` normal and `X`
irreducible. Then `f` is étale at every point where it is unramified: there the stalk
map is flat. (Étale at `x` means flat and unramified at `x`, I.4.1; so the étale locus is
the unramified locus, the complement of the support of `Ω¹_{X/Y}`.) -/
theorem flat_stalkMap_of_formallyUnramified_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDominant f] [IrreducibleSpace X] (hY : IsNormalScheme Y)
    (x : X) (hx : (f.stalkMap x).hom.FormallyUnramified) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, _⟩ := hY (f x)
  have hgen : IsGenericPoint (f (genericPoint X)) Set.univ := by
    have := (genericPoint_spec X).image f.continuous
    rwa [Set.image_univ, f.denseRange.closure_range] at this
  have hinj := injective_stalkMap_of_specializes f (genericPoint_specializes x)
    fun z _ ↦ hgen.specializes (Set.mem_univ z)
  have h₃ := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  exact flat_of_injective_of_formallyUnramified hinj

end UnramifiedSchemes

section Regular

variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]

/-- I.9, recalled fact (EGA IV 6.1.2): for a flat local homomorphism `A → B` of noetherian
local rings, `dim B = dim A + dim (B ⧸ m_A B)`. -/
theorem ringKrullDim_eq_add_of_flat [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] :
    ringKrullDim B =
      ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  set J := (maximalIdeal A).map (algebraMap A B)
  have hJ : J ≤ maximalIdeal B := map_maximalIdeal_le _
  have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ)
  have : IsLocalRing (B ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h]
  rfl

/-- I.9, recalled fact: a flat local homomorphism `A → B` of noetherian local rings with
`m_A B = m_B` (e.g. a local étale homomorphism) preserves Krull dimension. -/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  rw [ringKrullDim_eq_add_of_flat (A := A) (B := B), h, ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (maximalIdeal.isMaximal B)),
    add_zero]

/-- If `A → B` is flat and local and `m_A B = m_B`, the maximal ideals of `A` and `B`
need the same number of generators. -/
theorem spanFinrank_maximalIdeal_eq_of_flat [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
  refine le_antisymm ?_
    (h ▸ Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  have hmem (x : maximalIdeal A) : algebraMap A B x ∈ maximalIdeal B :=
    h ▸ Ideal.mem_map_of_mem _ x.2
  let w : maximalIdeal A → maximalIdeal B := fun x ↦ ⟨algebraMap A B x, hmem x⟩
  -- a family of elements of `m_A` generates `m_A` as soon as its image generates `m_B`
  have key {ι : Type u} (a : ι → maximalIdeal A)
      (ha : Submodule.span B (Set.range (w ∘ a)) = ⊤) :
      Ideal.span (Set.range fun i ↦ (a i : A)) = maximalIdeal A := by
    have hmap : (Ideal.span (Set.range fun i ↦ (a i : A))).map (algebraMap A B) =
        maximalIdeal B := by
      rw [Ideal.map_span, ← Set.range_comp]
      have := congr(Submodule.map (maximalIdeal B).subtype $ha)
      rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
        at this
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span _), hmap,
      Ideal.LiesOver.over (P := maximalIdeal B) (p := maximalIdeal A), Ideal.under_def]
  have hw : Submodule.span B (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal B).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    conv_rhs => rw [← h, Ideal.map]
    congr 1
    ext y
    simp [w]
  -- the images of `m_A` span the cotangent space of `B`; extract a basis
  let v := (maximalIdeal B).toCotangent ∘ w
  have hspan : Submodule.span (ResidueField B) (Set.range v) = ⊤ := by
    rw [Set.range_comp]
    exact CotangentSpace.span_image_eq_top_iff.mpr hw
  obtain ⟨κ, a, ha, hsa, hli⟩ := exists_linearIndependent' (ResidueField B) v
  have : Finite κ := hli.finite_of_isNoetherian
  let b := Module.Basis.mk hli (by rw [hsa, hspan])
  have hY := key a (by
    rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
    exact hsa.trans hspan)
  have hinj : Function.Injective fun i ↦ (a i : A) := Subtype.val_injective.comp ha
  rw [← hY, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, Module.finrank_eq_nat_card_basis b,
    ← Set.ncard_range_of_injective hinj]
  exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)

/-- I.9.1, in the generality of the proof: if `A → B` is a flat local homomorphism of
noetherian local rings with `m_A B = m_B`, then `A` is regular iff `B` is. -/
theorem isRegularLocalRing_iff_of_flat [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ↔ IsRegularLocalRing B := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff, spanFinrank_maximalIdeal_eq_of_flat h,
    ringKrullDim_eq_of_flat_of_map_maximalIdeal h]

/-- I.9.1: for a local étale homomorphism `A → B` of noetherian local rings (flat, formally
unramified, essentially of finite type), `A` is regular iff `B` is. -/
theorem isRegularLocalRing_iff_of_etale [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    IsRegularLocalRing A ↔ IsRegularLocalRing B :=
  isRegularLocalRing_iff_of_flat FormallyUnramified.map_maximalIdeal

end Regular

open AlgebraicGeometry in
/-- The local rings of `X` and `Y` at `x` and `f x` are simultaneously regular when `f` is
étale and `Y` locally noetherian (I.9.1 applied to the stalk map). -/
theorem isRegularLocalRing_stalk_iff_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [Etale f] (x : X) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) ↔ IsRegularLocalRing (X.presheaf.stalk x) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h₁ := Flat.stalkMap f x
  have h₂ := FormallyUnramified.stalkMap f x
  have h₃ := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact isRegularLocalRing_iff_of_etale

open AlgebraicGeometry in
/-- I.9.2, the corollary: if `f : X ⟶ Y` is étale and `Y` is regular (locally noetherian
with regular local rings), so is `X`; the converse holds if `f` is surjective. -/
theorem isRegular_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [Etale f] :
    ((∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) →
      ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ∧
    (Surjective f → (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
      ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) := by
  refine ⟨fun hY x ↦ (isRegularLocalRing_stalk_iff_of_etale f x).mp (hY (f x)),
    fun _ hX y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective y
  exact (isRegularLocalRing_stalk_iff_of_etale f x).mpr (hX x)

end SGA.SGA1.ExposeI
