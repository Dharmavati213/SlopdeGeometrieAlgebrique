/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RegularElementProjectiveDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The residue field as a summand of the reduced maximal ideal

If `x` has nonzero cotangent class, a cotangent functional taking that class
to one splits the map `k → m/xm` sending one to `x`. The splitting is linear
over the actual quotient ring. If `x` is also regular on the ring, this
lowers the residue field's projective-dimension bound by one over `R/(x)`.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open scoped Pointwise

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The actual residue fields before and after a proper quotient agree
linearly over the original ring, through their original scalar maps. -/
def quotientResidueFieldLinearEquiv (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    ResidueField R ≃ₗ[R] ResidueField (R ⧸ I) := by
  have : IsLocalHom (algebraMap R (R ⧸ I)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let f := (Algebra.linearMap (ResidueField R) (ResidueField (R ⧸ I))).restrictScalars R
  apply LinearEquiv.ofBijective f
  refine ⟨(algebraMap (ResidueField R) (ResidueField (R ⧸ I))).injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := residue_surjective a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨residue R r, rfl⟩

/-- An actual linear splitting of `k → m/xm`, obtained from a cotangent
functional taking the specified original parameter to one. -/
theorem exists_residue_retract_reduced_maximalIdeal (x : R)
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ (i : ResidueField R →ₗ[R] QuotSMulTop x (maximalIdeal R))
      (p : QuotSMulTop x (maximalIdeal R) →ₗ[R] ResidueField R), p.comp i = .id := by
  let m := maximalIdeal R
  let v : m := ⟨x, hx⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ResidueField R)
    (show m.toCotangent v ≠ 0 from fun h ↦ hx2 ((Ideal.toCotangent_eq_zero m v).mp h))
  let l : m →ₗ[R] ResidueField R := (φ.restrictScalars R).comp m.toCotangent
  have hl : l v = 1 := hφ
  let q : m →ₗ[R] QuotSMulTop x m := (x • (⊤ : Submodule R m)).mkQ
  let f : R →ₗ[R] QuotSMulTop x m := LinearMap.toSpanSingleton R _ (q v)
  have hfi : m ≤ LinearMap.ker f := by
    intro a ha
    change a • q v = 0
    rw [← q.map_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨⟨a, ha⟩, trivial, Subtype.ext (mul_comm x a)⟩
  let i : ResidueField R →ₗ[R] QuotSMulTop x m := m.liftQ f hfi
  have hpl : x • (⊤ : Submodule R m) ≤ LinearMap.ker l := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha
    change l (x • b) = 0
    rw [l.map_smul, Algebra.smul_def, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff x).mpr hx, zero_mul]
  let p : QuotSMulTop x m →ₗ[R] ResidueField R := (x • (⊤ : Submodule R m)).liftQ l hpl
  refine ⟨i, p, ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change p (r • q v) = residue R r
  rw [p.map_smul]
  change r • l v = residue R r
  rw [hl, Algebra.smul_def, ResidueField.algebraMap_eq, mul_one]

/-- The splitting is over the quotient ring and its own actual residue
field, not merely over the original ring. -/
theorem nonempty_residue_retract_reduced_maximalIdeal (x : R)
    [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    Nonempty (Retract (ModuleCat.of (R ⧸ Ideal.span {x})
      (ResidueField (R ⧸ Ideal.span {x})))
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (maximalIdeal R)))) := by
  obtain ⟨i, p, hpi⟩ := exists_residue_retract_reduced_maximalIdeal x hx hx2
  let e := quotientResidueFieldLinearEquiv (Ideal.span {x})
  let i' := (i.comp e.symm.toLinearMap).extendScalarsOfSurjective
    (S := R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective
  let p' := (e.toLinearMap.comp p).extendScalarsOfSurjective
    (S := R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective
  refine ⟨⟨ModuleCat.ofHom i', ModuleCat.ofHom p', ?_⟩⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change e (p (i (e.symm a))) = a
  have h := DFunLike.congr_fun hpi (e.symm a)
  exact (congrArg e h).trans (e.apply_symm_apply a)

variable [IsNoetherianRing R]

/-- Killing a regular element outside `m²` lowers the residue field's
projective-dimension bound by one over the actual quotient ring. -/
theorem quotient_residueField_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) (n + 1)]
    (x : R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxR : IsSMulRegular R x) :
    HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x})
      (ResidueField (R ⧸ Ideal.span {x}))) n := by
  let m := maximalIdeal R
  let S := ModuleCat.shortComplexOfCompEqZero m.subtype m.mkQ (by
    ext a
    exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr
        (m.range_subtype.trans m.ker_mkQ.symm)
      mono_f := (ModuleCat.mono_iff_injective _).mpr m.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).mpr m.mkQ_surjective }
  have hres : HasProjectiveDimensionLT S.X₃ (n + 2) :=
    inferInstanceAs (HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) (n + 1))
  have hm : HasProjectiveDimensionLE S.X₁ n :=
    (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hres
  have hqm := quotient_hasProjectiveDimensionLE_of_regularElement n S.X₁ x hxR
    (hxR.submodule m x)
  exact (nonempty_residue_retract_reduced_maximalIdeal x hx hx2).some.hasProjectiveDimensionLT
    (n + 1)

end SGA.SGA2.ExposeV
