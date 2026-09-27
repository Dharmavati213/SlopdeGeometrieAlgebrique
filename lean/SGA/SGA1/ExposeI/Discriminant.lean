/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# SGA 1, Exposé I, I.4.10: the discriminant criterion

A finite free algebra `B` over `A` (an étale covering of `Spec A` which is locally free)
is étale iff the trace form `(x, y) ↦ Tr_{B/A}(xy)` identifies `B` with its dual, i.e.
iff the discriminant of a basis is a unit (`etale_iff_isUnit_discr`). As in SGA one
reduces to the fibres over the residue fields; over a field the criterion is proved by
decomposing a reduced finite algebra into a product of fields
(`etale_iff_traceForm_nondegenerate`).
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra
open scoped TensorProduct

variable {K : Type u} [CommRing K]

/-- The trace of a finite product of free finite algebras is the sum of the traces. -/
theorem trace_pi_apply {ι : Type*} [Fintype ι] (L : ι → Type*) [∀ i, CommRing (L i)]
    [∀ i, Algebra K (L i)] [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]
    (x : ∀ i, L i) : Algebra.trace K (∀ i, L i) x = ∑ i, Algebra.trace K (L i) (x i) := by
  classical
  let b := fun i ↦ Module.Free.chooseBasis K (L i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b)]
  simp_rw [Algebra.trace_eq_matrix_trace (b _)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply,
    Pi.basis_repr]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  change ((b i).repr ((x * Pi.single i ((b i) a)) i)) a = _
  rw [Pi.mul_apply, Pi.single_eq_same]


lemma trace_pi_single_mul {ι : Type*} [Finite ι] [DecidableEq ι] (L : ι → Type*)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)] [∀ i, Module.Free K (L i)]
    [∀ i, Module.Finite K (L i)] (i : ι) (z : L i) (y : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) (Pi.single i z * y) = Algebra.trace K (L i) (z * y i) := by
  have := Fintype.ofFinite ι
  rw [trace_pi_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The trace form is nondegenerate iff `x ↦ (y ↦ Tr(xy))` is injective. -/
lemma traceForm_nondegenerate_iff (L : Type*) [CommRing L] [Algebra K L] :
    (traceForm K L).Nondegenerate ↔ ∀ x : L, (∀ y, Algebra.trace K L (x * y) = 0) → x = 0 :=
  ⟨fun h x hx ↦ h.1 x (by simpa using hx), fun h ↦ ⟨fun x hx ↦ h x (by simpa using hx),
    fun y hy ↦ h y fun x ↦ by rw [mul_comm]; simpa using hy x⟩⟩

/-- The trace form of a finite product is nondegenerate iff each factor's is. -/
theorem traceForm_pi_nondegenerate_iff {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)] [∀ i, Module.Free K (L i)]
    [∀ i, Module.Finite K (L i)] :
    (traceForm K (∀ i, L i)).Nondegenerate ↔ ∀ i, (traceForm K (L i)).Nondegenerate := by
  classical
  simp_rw [traceForm_nondegenerate_iff]
  constructor
  · intro h i z hz
    have := h (Pi.single i z) fun y ↦ by rw [trace_pi_single_mul]; exact hz (y i)
    simpa using congr_fun this i
  · intro h x hx
    funext i
    refine h i (x i) fun z ↦ ?_
    have := hx (Pi.single i z)
    rwa [mul_comm, trace_pi_single_mul, mul_comm] at this


lemma traceForm_nondegenerate_iff_of_algEquiv {L L' : Type*} [CommRing L] [CommRing L']
    [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    (traceForm K L).Nondegenerate ↔ (traceForm K L').Nondegenerate := by
  simp_rw [traceForm_nondegenerate_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · refine e.symm.injective ((h (e.symm x) fun y ↦ ?_).trans (map_zero e.symm).symm)
    rw [← Algebra.trace_eq_of_algEquiv e, map_mul, e.apply_symm_apply]
    exact hx _
  · refine e.injective ((h (e x) fun y ↦ ?_).trans (map_zero e).symm)
    rw [← e.apply_symm_apply y, ← map_mul, Algebra.trace_eq_of_algEquiv]
    exact hx _

/-- I.4.10 over a field: a finite algebra `L` over a field `K` is étale (a product of
finite separable extensions) iff its trace form `(x, y) ↦ Tr_{L/K}(xy)` is
nondegenerate. -/
theorem etale_iff_traceForm_nondegenerate {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    [FiniteDimensional K L] :
    Algebra.Etale K L ↔ (traceForm K L).Nondegenerate := by
  constructor
  · intro _
    obtain ⟨I, _, Li, _, _, e, h⟩ := (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := L)).mp
      inferInstance
    have := Fintype.ofFinite I
    have := fun i ↦ (h i).1
    have := fun i ↦ (h i).2
    rw [traceForm_nondegenerate_iff_of_algEquiv e, traceForm_pi_nondegenerate_iff]
    exact fun i ↦ traceForm_nondegenerate K (Li i)
  · intro h
    -- `L` is reduced: nilpotents lie in the kernel of the trace form
    have : IsReduced L := ⟨fun x hx ↦ (traceForm_nondegenerate_iff L).mp h x fun y ↦
      (Algebra.isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_right
        (Commute.all x y) hx)).eq_zero⟩
    have : IsArtinianRing L := isArtinian_of_tower K inferInstance
    have := Fintype.ofFinite (MaximalSpectrum L)
    let e : L ≃ₐ[K] ∀ I : MaximalSpectrum L, L ⧸ I.asIdeal :=
      (IsArtinianRing.equivPi L).restrictScalars K
    rw [traceForm_nondegenerate_iff_of_algEquiv e, traceForm_pi_nondegenerate_iff] at h
    have H (I : MaximalSpectrum L) : Algebra.Etale K (L ⧸ I.asIdeal) := by
      have := I.isMaximal
      let := Ideal.Quotient.field I.asIdeal
      have : Algebra.IsSeparable K (L ⧸ I.asIdeal) :=
        ((traceForm_nondegenerate_tfae K (L ⧸ I.asIdeal)).out 3 1).mp (h I)
      have : Algebra.FormallyEtale K (L ⧸ I.asIdeal) := Algebra.FormallyEtale.of_isSeparable _ _
      have : Algebra.FinitePresentation K (L ⧸ I.asIdeal) :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact ⟨inferInstance, inferInstance⟩
    exact Algebra.Etale.of_equiv e.symm


section General

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
  [Module.Finite A B]

/-- The trace commutes with base change. -/
lemma trace_baseChange (T : Type u) [CommRing T] [Algebra A T] (x : B) :
    Algebra.trace T (T ⊗[A] B) (1 ⊗ₜ x) = algebraMap A T (Algebra.trace A B x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

/-- The discriminant commutes with base change. -/
lemma discr_baseChange (T : Type u) [CommRing T] [Algebra A T] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι A B) :
    Algebra.discr T (Algebra.TensorProduct.basis T b) = algebraMap A T (Algebra.discr A b) := by
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.TensorProduct.basis_apply, trace_baseChange]

/-- A finite module whose reductions modulo all maximal ideals vanish is zero. -/
lemma subsingleton_of_forall_subsingleton_quotient_tensor (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Finite A M]
    (h : ∀ m : Ideal A, m.IsMaximal → Subsingleton ((A ⧸ m) ⊗[A] M)) : Subsingleton M := by
  suffices Module.annihilator A M = ⊤ by
    rwa [Module.annihilator_eq_top_iff] at this
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have := h m hm
  have := (TensorProduct.quotTensorEquivQuotSMul M m).symm.subsingleton
  rw [Submodule.Quotient.subsingleton_iff] at this
  obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
    Module.Finite.fg_top this.ge
  have : r ∈ m := hle (Module.mem_annihilator.mpr fun x ↦ hr' x trivial)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem this hr))

/-- The discriminant of a basis of a finite free algebra over a field is nonzero iff the
algebra is étale. -/
lemma discr_ne_zero_iff_etale {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) :
    Algebra.discr K b ≠ 0 ↔ Algebra.Etale K L := by
  rw [etale_iff_traceForm_nondegenerate, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b,
    Algebra.discr_def]
  congr! 3
  ext i j
  rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- I.4.10: a finite free algebra `B` over `A` is étale iff its discriminant (with respect
to any basis) is a unit, i.e. iff the trace form `(x, y) ↦ Tr_{B/A}(xy)` identifies `B`
with its dual. As in SGA, one reduces to the fibres over the residue fields. -/
theorem etale_iff_isUnit_discr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) : Algebra.Etale A B ↔ IsUnit (Algebra.discr A b) := by
  -- étaleness of the fibre over a maximal ideal is the non-vanishing of the discriminant there
  have key (m : Ideal A) [m.IsMaximal] :
      Algebra.Etale (A ⧸ m) ((A ⧸ m) ⊗[A] B) ↔ Algebra.discr A b ∉ m := by
    let := Ideal.Quotient.field m
    rw [← discr_ne_zero_iff_etale (Algebra.TensorProduct.basis (A ⧸ m) b), discr_baseChange,
      Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro _
    by_contra hu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {Algebra.discr A b})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact (key m).mp inferInstance (hle (Ideal.mem_span_singleton_self _))
  · intro hu
    have : Module.Finite A Ω[B⁄A] := Module.Finite.trans B _
    have hΩ : Subsingleton Ω[B⁄A] := by
      refine subsingleton_of_forall_subsingleton_quotient_tensor (A := A) _ fun m hm ↦ ?_
      have := (key m).mpr fun h ↦ hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
      have : Subsingleton Ω[(A ⧸ m) ⊗[A] B⁄A ⧸ m] :=
        (Algebra.formallyUnramified_iff _ _).mp inferInstance
      exact (KaehlerDifferential.tensorKaehlerEquivBase A (A ⧸ m) B ((A ⧸ m) ⊗[A] B)).subsingleton
    have : Algebra.FormallyUnramified A B := (Algebra.formallyUnramified_iff _ _).mpr hΩ
    have : Module.FinitePresentation A B := Module.finitePresentation_of_projective _ _
    exact Algebra.Etale.of_formallyUnramified_of_flat

end General

end SGA.SGA1.ExposeI
