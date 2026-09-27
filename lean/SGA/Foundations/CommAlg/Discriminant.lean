/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Finite

/-!
# The discriminant criterion for étaleness

Let `B` be a finite free `A`-algebra with basis `b`. Then `B` is étale over `A` iff the
discriminant `disc(b) = det (Tr(bᵢ bⱼ))` is a unit, i.e. iff the trace form of `B` over `A` is
perfect (Stacks 0BVH; SGA 1, I.4.10).

* Over a field `K`, a finite étale algebra is a product of finite separable extensions, whose trace
  forms are nondegenerate, so the trace form is nondegenerate
  (`Algebra.traceForm_nondegenerate_of_formallyEtale`).
* The discriminant commutes with base change (`Algebra.discr_tensorProduct_basis`); applied to the
  residue fields at maximal ideals this gives `Algebra.isUnit_discr_of_formallyEtale`.
* Conversely, if `disc(b)` is a unit, the trace-dual basis `b^∨` exists and
  `∑ bᵢ ⊗ b^∨ᵢ ∈ B ⊗_A B` is a separability idempotent, so `B` is unramified, hence étale since it
  is flat (`Algebra.etale_of_isUnit_discr`).
* For a finite locally free `B`, étaleness is the invertibility of the discriminants of the
  localizations at the maximal ideals (`Algebra.etale_iff_forall_isUnit_discr_localization`).
-/

universe u v

open Module TensorProduct

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

section BaseChange

variable (A' : Type*) [CommRing A'] [Algebra A A']

/-- The trace of `1 ⊗ x` in `A' ⊗_A B` over `A'` is the image of the trace of `x`. -/
theorem trace_one_tmul [Module.Free A B] [Module.Finite A B] (x : B) :
    trace A' (A' ⊗[A] B) (1 ⊗ₜ x) = algebraMap A A' (trace A B x) := by
  rw [trace_apply, trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The discriminant commutes with base change. -/
theorem discr_tensorProduct_basis (b : Basis ι A B) :
    discr A' (Algebra.TensorProduct.basis A' b) = algebraMap A A' (discr A b) := by
  have : Module.Free A B := Module.Free.of_basis b
  have : Module.Finite A B := Module.Finite.of_basis b
  rw [discr_def, discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [traceMatrix_apply, traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_one_tmul]

end BaseChange

section Field

variable (K : Type u) [Field K]

/-- The trace of `Pi.single i w` in a finite product of finite free algebras is the trace of `w`
in the `i`-th factor. -/
theorem trace_pi_single {I : Type*} [Finite I] [DecidableEq I] (C : I → Type v)
    [∀ i, CommRing (C i)] [∀ i, Algebra K (C i)] [∀ i, Module.Finite K (C i)] (i : I) (w : C i) :
    trace K (Π j, C j) (Pi.single i w) = trace K (C i) w := by
  have h : lmul K (Π j, C j) (Pi.single i w) =
      (LinearMap.single K C i ∘ₗ lmul K (C i) w) ∘ₗ LinearMap.proj i := by
    refine LinearMap.ext fun y ↦ funext fun j ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [trace_apply, h, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc,
    LinearMap.proj_comp_single_same, LinearMap.id_comp, trace_apply]

/-- The trace form of a finite étale algebra over a field is nondegenerate. -/
theorem traceForm_nondegenerate_of_formallyEtale (C : Type v) [CommRing C] [Algebra K C]
    [Module.Finite K C] [FormallyEtale K C] : (traceForm K C).Nondegenerate := by
  classical
  have : EssFiniteType K C := inferInstance
  obtain ⟨I, _, L, _, _, e, hsep⟩ := (FormallyEtale.iff_exists_algEquiv_prod K C).mp inferInstance
  have := Fintype.ofFinite I
  have hfin : ∀ i, Module.Finite K (L i) := fun i ↦
    Module.Finite.of_surjective ((LinearMap.proj i).comp e.toLinearMap)
      (fun y ↦ ⟨e.symm (Pi.single i y), by simp⟩)
  refine (traceForm_isSymm (R := K) (S := C)).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  apply e.injective
  rw [map_zero]
  ext i
  have hdeg : ∀ z : L i, traceForm K (L i) (e x i) z = 0 := by
    intro z
    have := hx (e.symm (Pi.single i z))
    rw [traceForm_apply, ← trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply] at this
    rw [traceForm_apply, ← trace_pi_single K L i, ← this]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  exact (traceForm_nondegenerate K (L i)).1 _ hdeg

/-- The discriminant of a basis of a finite étale algebra over a field is nonzero. -/
theorem discr_ne_zero_of_formallyEtale {C : Type v} [CommRing C] [Algebra K C]
    [FormallyEtale K C] (b : Basis ι K C) : discr K b ≠ 0 := by
  have : Module.Finite K C := Module.Finite.of_basis b
  rw [discr_def, traceMatrix_of_basis]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (traceForm_nondegenerate_of_formallyEtale K C)

end Field

/-- SGA 1, I.4.10, necessity: the discriminant of a basis of a finite free formally étale algebra
is a unit. -/
theorem isUnit_discr_of_formallyEtale [FormallyEtale A B] (b : Basis ι A B) :
    IsUnit (discr A b) := by
  by_contra h
  obtain ⟨M, hM, hdM⟩ := exists_max_ideal_of_mem_nonunits h
  let k := A ⧸ M
  let : Field k := Ideal.Quotient.field M
  have := discr_ne_zero_of_formallyEtale k (Algebra.TensorProduct.basis k b)
  rw [discr_tensorProduct_basis, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hdM] at this
  exact this rfl

section Converse

variable (b : Basis ι A B) (hb : IsUnit (discr A b))

/-- The trace-dual basis of `b`, when the discriminant is a unit. -/
noncomputable def traceDualOfIsUnitDiscr (j : ι) : B :=
  ∑ l, ((traceMatrix A b)⁻¹ l j) • b l

variable {b}

include hb in
theorem trace_mul_traceDualOfIsUnitDiscr (i j : ι) :
    trace A B (b i * traceDualOfIsUnitDiscr b j) = if i = j then 1 else 0 := by
  have hM : IsUnit (traceMatrix A b).det := hb
  have := congrFun (congrFun (Matrix.mul_nonsing_inv _ hM) i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [← this, traceDualOfIsUnitDiscr, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm, traceMatrix_apply, traceForm_apply]

include hb in
theorem trace_mul_traceDualOfIsUnitDiscr_eq_repr (y : B) (k : ι) :
    trace A B (y * traceDualOfIsUnitDiscr b k) = b.repr y k := by
  conv_lhs => rw [← b.sum_repr y]
  simp_rw [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul,
    trace_mul_traceDualOfIsUnitDiscr hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hb in
theorem eq_sum_trace_mul_traceDualOfIsUnitDiscr_smul (z : B) :
    z = ∑ j, trace A B (z * traceDualOfIsUnitDiscr b j) • b j := by
  simp_rw [trace_mul_traceDualOfIsUnitDiscr_eq_repr hb]
  exact (b.sum_repr z).symm

include hb in
/-- The trace form is nondegenerate when the discriminant is a unit. -/
theorem eq_zero_of_forall_trace_mul_eq_zero {w : B} (hw : ∀ z, trace A B (z * w) = 0) :
    w = 0 := by
  rw [eq_sum_trace_mul_traceDualOfIsUnitDiscr_smul hb w]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [mul_comm, hw, zero_smul]

include hb in
theorem eq_sum_trace_mul_smul_traceDualOfIsUnitDiscr (w : B) :
    w = ∑ i, trace A B (w * b i) • traceDualOfIsUnitDiscr b i := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_trace_mul_eq_zero hb
  intro z
  conv_lhs => rw [← b.sum_repr z]
  simp_rw [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [mul_sub, map_sub, Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, trace_mul_traceDualOfIsUnitDiscr hb, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [mul_comm (b k) w, sub_self, mul_zero]

include hb in
theorem sum_mul_traceDualOfIsUnitDiscr : ∑ i, b i * traceDualOfIsUnitDiscr b i = 1 := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_trace_mul_eq_zero hb
  intro z
  rw [mul_sub, map_sub, mul_one, Finset.mul_sum, map_sum, sub_eq_zero,
    trace_eq_matrix_trace b z, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_assoc, trace_mul_traceDualOfIsUnitDiscr_eq_repr hb, Matrix.diag,
    leftMulMatrix_eq_repr_mul]

include hb in
/-- SGA 1, I.4.10, sufficiency: a finite free algebra whose discriminant is a unit is formally
unramified. -/
theorem formallyUnramified_of_isUnit_discr : FormallyUnramified A B := by
  have : Module.Finite A B := Module.Finite.of_basis b
  rw [FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, b i ⊗ₜ traceDualOfIsUnitDiscr b i, fun s ↦ ?_, ?_⟩
  · rw [sub_mul, sub_eq_zero, Finset.mul_sum, Finset.mul_sum]
    simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e1 : ∀ i, b i ⊗ₜ[A] (s * traceDualOfIsUnitDiscr b i) =
        ∑ j, trace A B (s * traceDualOfIsUnitDiscr b i * b j) •
          (b i ⊗ₜ[A] traceDualOfIsUnitDiscr b j) := fun i ↦ by
      conv_lhs => rw [eq_sum_trace_mul_smul_traceDualOfIsUnitDiscr hb
        (s * traceDualOfIsUnitDiscr b i)]
      simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    have e2 : ∀ i, (s * b i) ⊗ₜ[A] traceDualOfIsUnitDiscr b i =
        ∑ j, trace A B (s * b i * traceDualOfIsUnitDiscr b j) •
          (b j ⊗ₜ[A] traceDualOfIsUnitDiscr b i) := fun i ↦ by
      conv_lhs => rw [eq_sum_trace_mul_traceDualOfIsUnitDiscr_smul hb (s * b i)]
      simp_rw [TensorProduct.sum_tmul, TensorProduct.smul_tmul']
    simp_rw [e1, e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show s * traceDualOfIsUnitDiscr b j * b i = s * b i * traceDualOfIsUnitDiscr b j by ring]
  · simp_rw [map_sum, TensorProduct.lmul'_apply_tmul]
    exact sum_mul_traceDualOfIsUnitDiscr hb

include hb in
/-- SGA 1, I.4.10, sufficiency: a finite free algebra whose discriminant is a unit is étale. -/
theorem etale_of_isUnit_discr : Etale A B := by
  have : Module.Free A B := Module.Free.of_basis b
  have : Module.Finite A B := Module.Finite.of_basis b
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have := formallyUnramified_of_isUnit_discr hb
  exact Etale.of_formallyUnramified_of_flat

end Converse

/-- SGA 1, I.4.10 (Stacks 0BVH): a finite free algebra is étale iff the discriminant of a basis
is a unit, i.e. iff its trace form is perfect. -/
theorem etale_iff_isUnit_discr (b : Basis ι A B) : Etale A B ↔ IsUnit (discr A b) :=
  ⟨fun _ ↦ isUnit_discr_of_formallyEtale b, etale_of_isUnit_discr⟩

/-- SGA 1, I.4.10 (Stacks 0BVH), for formally étale algebras. -/
theorem formallyEtale_iff_isUnit_discr (b : Basis ι A B) :
    FormallyEtale A B ↔ IsUnit (discr A b) :=
  ⟨fun _ ↦ isUnit_discr_of_formallyEtale b,
    fun h ↦ have := etale_of_isUnit_discr h; inferInstance⟩

section LocallyFree

variable (A B) in
/-- SGA 1, I.4.10 for locally free algebras (Stacks 0BVH): a finite projective (i.e. finite
locally free) `A`-algebra `B` is étale iff at every maximal ideal `m` of `A` the discriminant of a
basis of the free `A_m`-algebra `B_m` is a unit. (The trace of a projective module which is not
free is not defined in mathlib, so the discriminant is taken locally.) -/
theorem etale_iff_forall_isUnit_discr_localization [Module.Finite A B] [Module.Projective A B] :
    Etale A B ↔ ∀ (m : Ideal A) [m.IsMaximal] {κ : Type v} [Fintype κ] [DecidableEq κ]
      (b : Basis κ (Localization.AtPrime m) (Localization (algebraMapSubmonoid B m.primeCompl))),
      IsUnit (discr (Localization.AtPrime m) b) := by
  constructor
  · intro _ m _ κ _ _ b
    have : IsLocalization (m.primeCompl.map (algebraMap A B))
        (Localization (algebraMapSubmonoid B m.primeCompl)) := Localization.isLocalization
    have : FormallyEtale (Localization.AtPrime m)
        (Localization (algebraMapSubmonoid B m.primeCompl)) :=
      FormallyEtale.localization_map (S := B) m.primeCompl
    exact isUnit_discr_of_formallyEtale b
  · intro h
    have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
    refine ⟨?_, inferInstance⟩
    rw [← etaleLocus_eq_univ_iff]
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal (q.asIdeal.comap (algebraMap A B))
      (Ideal.IsPrime.comap _).ne_top
    let M := m.primeCompl
    let Am := Localization.AtPrime m
    let Bm := Localization (algebraMapSubmonoid B M)
    have : Module.Free Am Bm := Module.free_of_flat_of_isLocalRing
    have : FormallyEtale Am Bm :=
      (formallyEtale_iff_isUnit_discr (Module.Free.chooseBasis Am Bm)).mpr (h m _)
    -- `B_q` is a localization of `B_m`
    have hdisj : Disjoint (algebraMapSubmonoid B M : Set B) q.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hsq
      exact hs (hqm hsq)
    let Q := q.asIdeal.map (algebraMap B Bm)
    have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Bm q.asIdeal q.2 hdisj
    have hQq : Q.comap (algebraMap B Bm) = q.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint _ Bm q.2 hdisj
    have : FormallyEtale A Am := FormallyEtale.of_isLocalization M
    have : FormallyEtale A (Localization.AtPrime Q) := FormallyEtale.comp A Am _
    have hL : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap B Bm)) :=
      inferInstance
    have : IsLocalization.AtPrime (Localization.AtPrime Q) q.asIdeal := by
      convert hL using 2; exact hQq.symm
    let e : Localization.AtPrime q.asIdeal ≃ₐ[B] Localization.AtPrime Q :=
      IsLocalization.algEquiv q.asIdeal.primeCompl _ _
    exact FormallyEtale.of_equiv (e.restrictScalars A).symm

end LocallyFree

end Algebra
