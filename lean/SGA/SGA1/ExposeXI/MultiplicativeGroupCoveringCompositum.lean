/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.MultiplicativeGroupCoveringField

/-!
# The Kummer pullback of a covering of `𝔾_m` (for XIII.2.12)

Let `L/k(T)` be the function field of a connected Galois covering of `𝔾_{m,k}` of degree `d`
prime to the characteristic, and `K' = k(T)[z]/(z^d - T)` the function field of the Kummer
covering `z ↦ z^d` (`kummerField`). A composite `F` of `L` and `K'` (`compositum`, a quotient of
`K' ⊗_{k(T)} L` by a maximal ideal) is Galois over `K'` of degree dividing `d`
(`isGalois_compositum`, `finrank_compositum_dvd`), and by Abhyankar's lemma (X.3.6, XIII.5.2) its
normalization over every local ring `k[T]_(T - a)` of `𝔸¹` is finite étale over the
normalization in `K'` (`etale_integralClosure_compositum`): at `a = 0` because the ramification
indices of `L` divide `d`, the ramification index of `K'`; at `a ≠ 0` because `L` is unramified
there.
-/

universe u

open Polynomial Module IsLocalRing
open scoped LaurentPolynomial KummerExtension

namespace SGA.SGA1.ExposeXI.MultiplicativeGroupCovering

section KummerField

variable (k : Type u) [Field k] (d : ℕ) [NeZero d]

/-- `T ∈ k(T)`, the image of the uniformizer of `k[T]_(T)`. -/
noncomputable abbrev coordT : FractionRing k[X] :=
  algebraMap (localRingAt k 0) (FractionRing k[X]) (uniformizer 0)

/-- The function field `k(T)[z]/(z^d - T) = k(z)` of the Kummer covering of degree `d` of
`𝔾_m`. -/
abbrev KummerField : Type u := AdjoinRoot (X ^ d - C (coordT k))

variable {k d}

lemma primitiveRoots_nonempty [IsSepClosed k] (hd : (d : k) ≠ 0) :
    (primitiveRoots d (FractionRing k[X])).Nonempty := by
  have : NeZero (d : k) := ⟨hd⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k d
  refine ⟨algebraMap k (FractionRing k[X]) ζ, ?_⟩
  rw [mem_primitiveRoots (NeZero.pos d)]
  exact hζ.map_of_injective (algebraMap k (FractionRing k[X])).injective

lemma irreducible_kummer : Irreducible (X ^ d - C (coordT k)) :=
  (ExposeXIII.fact_irreducible_X_pow_sub_C_algebraMap (localRingAt k 0) (K := FractionRing k[X])
    (uniformizer 0) d).out

instance fact_irreducible_kummer : Fact (Irreducible (X ^ d - C (coordT k))) :=
  ⟨irreducible_kummer⟩

variable (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
include hζ

lemma isSplittingField_kummerField :
    IsSplittingField (FractionRing k[X]) (KummerField k d) (X ^ d - C (coordT k)) :=
  isSplittingField_AdjoinRoot_X_pow_sub_C hζ irreducible_kummer

lemma isGalois_kummerField : IsGalois (FractionRing k[X]) (KummerField k d) :=
  have := isSplittingField_kummerField hζ
  isGalois_of_isSplittingField_X_pow_sub_C hζ irreducible_kummer _

lemma finrank_kummerField : finrank (FractionRing k[X]) (KummerField k d) = d :=
  have := isSplittingField_kummerField hζ
  finrank_of_isSplittingField_X_pow_sub_C hζ irreducible_kummer _

lemma isCyclic_kummerField : IsCyclic Gal(KummerField k d/FractionRing k[X]) :=
  have := isSplittingField_kummerField hζ
  isCyclic_of_isSplittingField_X_pow_sub_C hζ irreducible_kummer _

end KummerField

section Compositum

open scoped TensorProduct

variable (k : Type u) [Field k] (d : ℕ) [NeZero d] (L : Type u) [Field L]
  [Algebra (FractionRing k[X]) L] [FiniteDimensional (FractionRing k[X]) L]

instance nontrivial_kummerField_tensor :
    Nontrivial (KummerField k d ⊗[FractionRing k[X]] L) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
    (algebraMap (FractionRing k[X]) (KummerField k d)).injective
    (algebraMap (FractionRing k[X]) L).injective

/-- A maximal ideal of `K' ⊗_{k(T)} L`. -/
noncomputable def compositumIdeal : Ideal (KummerField k d ⊗[FractionRing k[X]] L) :=
  Classical.choose (Ideal.exists_maximal (KummerField k d ⊗[FractionRing k[X]] L))

instance isMaximal_compositumIdeal : (compositumIdeal k d L).IsMaximal :=
  Classical.choose_spec (Ideal.exists_maximal (KummerField k d ⊗[FractionRing k[X]] L))

/-- A composite `F` of `L` and `K' = k(T)[z]/(z^d - T)` over `k(T)`. -/
abbrev Compositum : Type u :=
  (KummerField k d ⊗[FractionRing k[X]] L) ⧸ compositumIdeal k d L

noncomputable instance : Field (Compositum k d L) := Ideal.Quotient.field _

/-- The embedding `L → F`. -/
noncomputable def toCompositum : L →ₐ[FractionRing k[X]] Compositum k d L :=
  (Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight

instance finiteDimensional_compositum :
    FiniteDimensional (FractionRing k[X]) (Compositum k d L) :=
  Module.Finite.trans (KummerField k d ⊗[FractionRing k[X]] L) _

omit [FiniteDimensional (FractionRing k[X]) L] in
lemma adjoin_compositum :
    Algebra.adjoin (FractionRing k[X]) (Set.range (toCompositum k d L) ∪
      Set.range (algebraMap (KummerField k d) (Compositum k d L))) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  clear ‹_ ∈ ⊤›
  induction t using TensorProduct.induction_on with
  | zero => rw [(Ideal.Quotient.mk _).map_zero]; exact Subalgebra.zero_mem _
  | tmul a b =>
    have h : a ⊗ₜ[FractionRing k[X]] b = algebraMap (KummerField k d) _ a *
        Algebra.TensorProduct.includeRight b := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    have : Ideal.Quotient.mk (compositumIdeal k d L) (a ⊗ₜ b) =
        algebraMap (KummerField k d) (Compositum k d L) a * toCompositum k d L b := by
      rw [h, (Ideal.Quotient.mk _).map_mul]
      rfl
    rw [this]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩))
      (Algebra.subset_adjoin (Or.inl ⟨b, rfl⟩))
  | add x y hx hy => rw [(Ideal.Quotient.mk _).map_add]; exact Subalgebra.add_mem _ hx hy

variable {k d L}
variable (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
include hζ

lemma isSeparable_compositum [Algebra.IsSeparable (FractionRing k[X]) L] :
    Algebra.IsSeparable (FractionRing k[X]) (Compositum k d L) := by
  have := isGalois_kummerField hζ
  have : FiniteDimensional (FractionRing k[X]) (KummerField k d) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_kummerField hζ]; exact NeZero.pos d)
  have : Algebra.FormallyEtale (FractionRing k[X]) L := Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FinitePresentation (FractionRing k[X]) L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (FractionRing k[X]) L := ⟨inferInstance, inferInstance⟩
  have : Algebra.FormallyEtale (FractionRing k[X]) (KummerField k d) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FinitePresentation (FractionRing k[X]) (KummerField k d) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (FractionRing k[X]) (KummerField k d) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale (KummerField k d) (KummerField k d ⊗[FractionRing k[X]] L) :=
    inferInstance
  have : Algebra.Etale (FractionRing k[X]) (KummerField k d ⊗[FractionRing k[X]] L) :=
    Algebra.Etale.comp _ (KummerField k d) _
  have : Algebra.FormallyUnramified (FractionRing k[X]) (Compositum k d L) := inferInstance
  have : Algebra.EssFiniteType (FractionRing k[X]) (Compositum k d L) := inferInstance
  exact Algebra.FormallyUnramified.isSeparable _ _

omit [FiniteDimensional (FractionRing k[X]) L] in
/-- The composite `F` is Galois over `K'` (it is the composite of the Galois extensions `L` and
`K'` of `k(T)`). -/
lemma isGalois_compositum [IsGalois (FractionRing k[X]) L] :
    IsGalois (KummerField k d) (Compositum k d L) := by
  have := isGalois_kummerField hζ
  set K := FractionRing k[X]
  set F := Compositum k d L
  let E₁ : IntermediateField K F := (toCompositum k d L).fieldRange
  let E₂ : IntermediateField K F := (IsScalarTower.toAlgHom K (KummerField k d) F).fieldRange
  have : IsGalois K E₁ := IsGalois.of_algEquiv (toCompositum k d L).equivFieldRange
  have : IsGalois K E₂ :=
    IsGalois.of_algEquiv (IsScalarTower.toAlgHom K (KummerField k d) F).equivFieldRange
  have htop : E₁ ⊔ E₂ = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : x ∈ Algebra.adjoin K (Set.range (toCompositum k d L) ∪
        Set.range (algebraMap (KummerField k d) F)) := by
      rw [adjoin_compositum]; trivial
    refine Algebra.adjoin_le (S := (E₁ ⊔ E₂).toSubalgebra) ?_ hx
    rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact (le_sup_left : E₁ ≤ E₁ ⊔ E₂) ⟨y, rfl⟩
    · exact (le_sup_right : E₂ ≤ E₁ ⊔ E₂) ⟨y, rfl⟩
  have : IsGalois K (⊤ : IntermediateField K F) := htop ▸ inferInstance
  have : IsGalois K F := IsGalois.of_algEquiv IntermediateField.topEquiv
  exact IsGalois.tower_top_of_isGalois K (KummerField k d) F

/-- `[F : K']` divides `[L : k(T)]`: restriction to `L` embeds `Gal(F/K')` into `Gal(L/k(T))`. -/
lemma finrank_compositum_dvd [IsGalois (FractionRing k[X]) L] :
    finrank (KummerField k d) (Compositum k d L) ∣ finrank (FractionRing k[X]) L := by
  have := isGalois_compositum hζ (L := L)
  set K := FractionRing k[X]
  set F := Compositum k d L
  let E₁ : IntermediateField K F := (toCompositum k d L).fieldRange
  let E₂ : IntermediateField K F := (IsScalarTower.toAlgHom K (KummerField k d) F).fieldRange
  have : Normal K E₁ := Normal.of_algEquiv (toCompositum k d L).equivFieldRange
  let ρ : Gal(F/KummerField k d) →* Gal(E₁/K) :=
    (AlgEquiv.restrictNormalHom E₁).comp (AlgEquiv.restrictScalarsHom K)
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    have h₁ : AlgEquiv.restrictScalars K σ ∈ E₁.fixingSubgroup := by
      have hk := AlgEquiv.ker_restrictNormalHom (F := K) (K₁ := F) E₁
      have he : (IsScalarTower.toAlgHom K E₁ F).fieldRange = E₁ := E₁.fieldRange_val
      rw [he] at hk
      rw [← hk]
      exact hσ
    have h₂ : AlgEquiv.restrictScalars K σ ∈ E₂.fixingSubgroup := by
      rintro ⟨_, y, rfl⟩
      exact σ.commutes y
    have htop : E₁ ⊔ E₂ = ⊤ := by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      have hx : x ∈ Algebra.adjoin K (Set.range (toCompositum k d L) ∪
          Set.range (algebraMap (KummerField k d) F)) := by
        rw [adjoin_compositum]; trivial
      refine Algebra.adjoin_le (S := (E₁ ⊔ E₂).toSubalgebra) ?_ hx
      rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · exact (le_sup_left : E₁ ≤ E₁ ⊔ E₂) ⟨y, rfl⟩
      · exact (le_sup_right : E₂ ≤ E₁ ⊔ E₂) ⟨y, rfl⟩
    have h₃ : AlgEquiv.restrictScalars K σ ∈ (E₁ ⊔ E₂).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨h₁, h₂⟩
    rw [htop, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at h₃
    rw [Subgroup.mem_bot]
    ext x
    exact AlgEquiv.congr_fun h₃ x
  have hdvd := Subgroup.card_dvd_of_injective ρ hρ
  have : IsGalois K E₁ := IsGalois.of_algEquiv (toCompositum k d L).equivFieldRange
  have hE : Nat.card Gal(E₁/K) = finrank K L := by
    rw [IsGalois.card_aut_eq_finrank]
    exact (toCompositum k d L).equivFieldRange.toLinearEquiv.finrank_eq.symm
  have hF : Nat.card Gal(F/KummerField k d) = finrank (KummerField k d) F :=
    IsGalois.card_aut_eq_finrank _ _
  rw [← hE, ← hF]
  exact hdvd

end Compositum


end SGA.SGA1.ExposeXI.MultiplicativeGroupCovering
