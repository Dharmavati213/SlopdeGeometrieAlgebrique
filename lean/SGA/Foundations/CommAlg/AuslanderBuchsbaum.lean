/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import SGA.Foundations.CommAlg.RegularLocalRing

/-!
# The Auslander–Buchsbaum formula

* `IsLocalRing.projectiveDimension_add_depth`: if a nonzero finite module `M` over a noetherian
  local ring `R` has finite projective dimension, then `pd M + depth M = depth R` (Stacks 090V).
* `IsRegularLocalRing.free_of_isWeaklyRegular`: a finite module over a regular local ring `A`
  admitting a regular sequence of length `dim A` in the maximal ideal (a maximal Cohen–Macaulay
  module) is free (Stacks 00NT; EGA 0_IV 17.3.4). This is the case used in SGA 1, X.3.2 in
  dimension `2`; it is proved directly from `pd (M/(x)M) = pd M + #x` and Serre's bound
  `pd ≤ dim A`.

The proof of the formula is by induction on `pd M`, through a minimal presentation
`0 → K → R^t → M → 0` (with `K ⊆ 𝔪 R^t`) and the long exact sequence of `Ext(R/𝔪, -)`; depth is
read off from the vanishing of `Ext^i(R/𝔪, -)` (`depth_eq_iff_ext`). The minimality of the
presentation makes `Ext(R/𝔪, K) → Ext(R/𝔪, R^t)` vanish when `K` is free
(`ext_comp_mk₀_eq_zero_of_range_le`), which handles `pd M = 1`.
-/

universe u

open IsLocalRing RingTheory.Sequence CategoryTheory

/-- A finite module over a regular local ring `A` with a regular sequence of length `dim A` in the
maximal ideal is free (Stacks 090V, 00NT; EGA 0_IV 17.3.4). -/
theorem IsRegularLocalRing.free_of_isWeaklyRegular {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    {rs : List A} (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A) (hreg : IsWeaklyRegular M rs)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim A) : Module.Free A M := by
  cases subsingleton_or_nontrivial M
  · exact Module.Free.of_subsingleton A M
  have h1 := ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
    (ModuleCat.of A M) rs hreg hmem
  have h2 := IsRegularLocalRing.hasProjectiveDimensionLE hlen.symm
    (ModuleCat.of A (M ⧸ Ideal.ofList rs • (⊤ : Submodule A M)))
  rw [← projectiveDimension_le_iff, h1] at h2
  have h3 : projectiveDimension (ModuleCat.of A M) ≤ (0 : ℕ) := by
    rw [← ENat.WithBot.add_le_add_natCast_right_iff (c := rs.length)]
    simpa using h2
  rw [projectiveDimension_le_iff, ← projective_iff_hasProjectiveDimensionLE_zero,
    ← IsProjective.iff_projective] at h3
  exact Module.free_of_flat_of_isLocalRing

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M]
  [Module R M]

/-- A regular sequence on a module is regular on its retracts. -/
theorem IsWeaklyRegular.of_retract (i : N →ₗ[R] M) (p : M →ₗ[R] N) (hpi : p ∘ₗ i = .id)
    {rs : List R} (h : IsWeaklyRegular M rs) : IsWeaklyRegular N rs := by
  induction rs generalizing N M with
  | nil => exact IsWeaklyRegular.nil R N
  | cons r rs ih =>
    rw [isWeaklyRegular_cons_iff] at h ⊢
    refine ⟨fun a b hab ↦ ?_, ih (QuotSMulTop.map r i) (QuotSMulTop.map r p)
      (by rw [← QuotSMulTop.map_comp, hpi, QuotSMulTop.map_id]) h.2⟩
    have := h.1 (show r • i a = r • i b by rw [← map_smul, ← map_smul]; exact congrArg i hab)
    simpa [← LinearMap.comp_apply, hpi] using congrArg p this

end RingTheory.Sequence

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A nonzero free module has the same depth as the ring. -/
theorem depth_of_free (F : Type*) [AddCommGroup F] [Module R F] [Module.Free R F] [Nontrivial F] :
    I.depth F = I.depth R := by
  apply le_antisymm
  · -- `R` is a retract of `F`
    let b := Module.Free.chooseBasis R F
    obtain ⟨j⟩ := b.index_nonempty
    refine iSup_mono fun rs ↦ iSup_mono fun _ ↦ iSup_mono' fun hrs ↦ ⟨?_, le_rfl⟩
    refine IsWeaklyRegular.of_retract (LinearMap.toSpanSingleton R F (b j)) (b.coord j) ?_ hrs
    ext
    simp
  · refine iSup_mono fun rs ↦ iSup_mono fun _ ↦ iSup_mono' fun hrs ↦ ⟨?_, le_rfl⟩
    exact (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R F) rs).mp
      (hrs.isWeaklyRegular_lTensor (M₂ := F))

end Ideal

section AuslanderBuchsbaum

open Abelian

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The residue field `R/𝔪` as an object of `ModuleCat R`. -/
local notation "𝕜" => ModuleCat.of R (R ⧸ maximalIdeal R)

/-- `Ext^n(R/𝔪, N)` is killed by `𝔪`. -/
theorem ext_residueField_smul_eq_zero {N : ModuleCat.{u} R} {n : ℕ} {r : R}
    (hr : r ∈ maximalIdeal R) (e : Ext 𝕜 N n) : r • e = 0 := by
  have h0 : (r • 𝟙 𝕜 : 𝕜 ⟶ 𝕜) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (r * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr
  calc r • e = r • (Ext.mk₀ (𝟙 𝕜)).comp e (zero_add n) := by rw [Ext.mk₀_id_comp]
    _ = (Ext.mk₀ (r • 𝟙 𝕜)).comp e (zero_add n) := by rw [Ext.mk₀_smul, Ext.smul_comp]
    _ = 0 := by rw [h0, Ext.mk₀_zero, Ext.zero_comp]

/-- If `ι : K → F` is a linear map from a finite free module with image in `𝔪 F`, then the induced
map `Ext^n(R/𝔪, K) → Ext^n(R/𝔪, F)` vanishes. -/
theorem ext_comp_mk₀_eq_zero_of_range_le [IsNoetherianRing R] {K F : Type u} [AddCommGroup K]
    [Module R K] [AddCommGroup F] [Module R F] [Module.Free R K] [Module.Finite R K]
    (ι : K →ₗ[R] F) (hι : ∀ z, ι z ∈ maximalIdeal R • (⊤ : Submodule R F)) {n : ℕ}
    (e : Ext 𝕜 (ModuleCat.of R K) n) : e.comp (Ext.mk₀ (ModuleCat.ofHom ι)) (add_zero n) = 0 := by
  classical
  obtain ⟨s, hs⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  -- every element of `𝔪 F` is a combination `∑ g • w g` of the generators `g ∈ s`
  have hdec : ∀ v ∈ maximalIdeal R • (⊤ : Submodule R F), ∃ w : R → F, v = ∑ g ∈ s, g • w g := by
    intro v hv
    refine Submodule.smul_induction_on (p := fun v ↦ ∃ w : R → F, v = ∑ g ∈ s, g • w g) hv
      (fun a ha w _ ↦ ?_) (fun v₁ v₂ h₁ h₂ ↦ ?_)
    · rw [← hs] at ha
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.mp ha
      exact ⟨fun g ↦ c g • w, by simp [Finset.sum_smul, smul_smul, mul_comm]⟩
    · obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      exact ⟨w₁ + w₂, by simp [smul_add, Finset.sum_add_distrib]⟩
  let b := Module.Free.chooseBasis R K
  choose w hw using fun l ↦ hdec _ (hι (b l))
  let ιg : R → K →ₗ[R] F := fun g ↦ b.constr R fun l ↦ w l g
  have hsum : ι = ∑ g ∈ s, g • ιg g := b.ext fun l ↦ by
    simp [ιg, hw l]
  let Φ : (K →ₗ[R] F) →ₗ[R] Ext 𝕜 (ModuleCat.of R F) n :=
    { toFun f := e.comp (Ext.mk₀ (ModuleCat.ofHom f)) (add_zero n)
      map_add' f g := by rw [ModuleCat.ofHom_add, Ext.mk₀_add, Ext.comp_add]
      map_smul' r f := by
        rw [show ModuleCat.ofHom (r • f) = r • ModuleCat.ofHom f from rfl, Ext.mk₀_smul,
          Ext.comp_smul]
        rfl }
  change Φ ι = 0
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun g hg ↦ ?_
  rw [map_smul]
  exact ext_residueField_smul_eq_zero (hs ▸ Submodule.subset_span hg) _

variable [IsNoetherianRing R]

/-- The depth of a nonzero finite module is the first degree in which `Ext^i(R/𝔪, M)` does not
vanish. -/
theorem depth_eq_iff_ext (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (d : ℕ) : (maximalIdeal R).depth M = d ↔
      (∀ i < d, Subsingleton (Ext 𝕜 (ModuleCat.of R M) i)) ∧
        ¬ Subsingleton (Ext 𝕜 (ModuleCat.of R M) d) := by
  rw [← Ideal.le_depth_iff_ext_quotient]
  constructor
  · intro h
    refine ⟨h.ge, fun hd ↦ ?_⟩
    have : ((d + 1 : ℕ) : ℕ∞) ≤ (maximalIdeal R).depth M := by
      rw [Ideal.le_depth_iff_ext_quotient]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact (Ideal.le_depth_iff_ext_quotient d).mp h.ge i hi
      · exact hd
    rw [h] at this
    exact absurd (ENat.natCast_le_natCast.mp this) (by omega)
  · rintro ⟨h1, h2⟩
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (IsLocalRing.depth_ne_top (R := R) (M := M))
    rw [← he] at h1 ⊢
    congr 1
    refine le_antisymm (Nat.le_of_lt_succ ?_) (ENat.natCast_le_natCast.mp h1)
    by_contra hlt
    exact h2 ((Ideal.le_depth_iff_ext_quotient (e : ℕ)).mp (he ▸ le_refl _) d (by omega))

section ShortExact

omit [IsNoetherianRing R]

variable {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
include hS

theorem subsingleton_ext_X₃ {i : ℕ} (h₂ : Subsingleton (Ext 𝕜 S.X₂ i))
    (h₁ : Subsingleton (Ext 𝕜 S.X₁ (i + 1))) : Subsingleton (Ext 𝕜 S.X₃ i) := by
  refine subsingleton_of_forall_eq 0 fun x₃ ↦ ?_
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ 𝕜 hS x₃ rfl (Subsingleton.elim _ 0)
  rw [Subsingleton.elim x₂ 0, Ext.zero_comp]

theorem subsingleton_ext_X₁_succ {i : ℕ}
    (hf : ∀ x₁ : Ext 𝕜 S.X₁ (i + 1), x₁.comp (Ext.mk₀ S.f) (add_zero _) = 0)
    (h₃ : Subsingleton (Ext 𝕜 S.X₃ i)) : Subsingleton (Ext 𝕜 S.X₁ (i + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x₁ ↦ ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ 𝕜 hS x₁ (hf x₁) rfl
  rw [Subsingleton.elim x₃ 0, Ext.zero_comp]

theorem subsingleton_ext_X₁_zero
    (hf : ∀ x₁ : Ext 𝕜 S.X₁ 0, x₁.comp (Ext.mk₀ S.f) (add_zero _) = 0) :
    Subsingleton (Ext 𝕜 S.X₁ 0) := by
  have := hS.mono_f
  refine subsingleton_of_forall_eq 0 fun x₁ ↦ ?_
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective (X := 𝕜) (Y := S.X₁)).2 x₁
  have h := hf (Ext.mk₀ φ)
  rw [Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff] at h
  rw [(cancel_mono S.f).mp (h.trans (Limits.zero_comp).symm), Ext.mk₀_zero]

end ShortExact

variable (R) in
/-- Auslander–Buchsbaum, the inductive statement: if a nonzero finite module `M` over a noetherian
local ring has projective dimension `n`, then `n + depth M = depth R`. -/
theorem natCast_add_depth_eq_depth_of_projectiveDimension_eq (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
      projectiveDimension (ModuleCat.of R M) = n →
        (n : ℕ∞) + (maximalIdeal R).depth M = (maximalIdeal R).depth R := by
  induction n with
  | zero =>
    intro M _ _ _ _ h
    have : HasProjectiveDimensionLE (ModuleCat.of R M) 0 :=
      (projectiveDimension_le_iff _ 0).mp h.le
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at this
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    rw [Nat.cast_zero, zero_add, Ideal.depth_of_free]
  | succ n ih =>
    intro M _ _ _ _ h
    classical
    -- a minimal presentation `0 → K → R^t → M → 0`
    obtain ⟨t, htcard, htspan⟩ :=
      Submodule.FG.exists_span_finset_card_eq_spanFinrank (R := R) (p := (⊤ : Submodule R M))
        (Module.Finite.fg_top)
    let v : t → M := fun i ↦ (i : M)
    let f : (t → R) →ₗ[R] M := Fintype.linearCombination R v
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
        Finset.setOfPred_mem, htspan]
    have hmin : ∀ w ∈ LinearMap.ker f, ∀ i, w i ∈ maximalIdeal R := by
      intro w hw i
      by_contra hwi
      have hu : IsUnit (w i) := by rwa [← IsLocalRing.notMem_maximalIdeal]
      have hmem : (i : M) ∈ Submodule.span R ((t.erase i : Finset M) : Set M) := by
        have hsum : ∑ j, w j • v j = 0 := by
          rw [← Fintype.linearCombination_apply]
          exact hw
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
        have h' := eq_neg_of_add_eq_zero_left hsum
        have hi : (i : M) = (↑hu.unit⁻¹ : R) • (w i • v i) := by
          rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        have key : (↑hu.unit⁻¹ : R) • (w i • v i) ∈
            Submodule.span R ((t.erase i : Finset M) : Set M) := by
          rw [h']
          refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj ↦
            Submodule.smul_mem _ _ (Submodule.subset_span ?_)))
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff, v]
          exact ⟨j.2, fun h ↦ (Finset.mem_erase.mp hj).1 (Subtype.ext h)⟩
        rwa [← hi] at key
      have htop : Submodule.span R ((t.erase i : Finset M) : Set M) = ⊤ := by
        rw [eq_top_iff, ← htspan, Submodule.span_le]
        intro z hz
        by_cases hzi : z = i
        · rw [hzi]; exact hmem
        · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hzi, hz⟩)
      have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
        (t.erase (i : M)).finite_toSet
      rw [htop, Set.ncard_coe_finset, Finset.card_erase_of_mem i.2, ← htcard] at hle
      have : 0 < t.card := Finset.card_pos.mpr ⟨i, i.2⟩
      omega
    let K := LinearMap.ker f
    have hS := LinearMap.shortExact_shortComplexKer hf
    set S := f.shortComplexKer
    have : Projective S.X₂ := by
      rw [← IsProjective.iff_projective]
      infer_instance
    -- the projective dimension of `K` is `n`
    have hM1 : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1) :=
      (projectiveDimension_le_iff _ (n + 1)).mp (by rw [h])
    have hM2 : ¬ HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) :=
      (projectiveDimension_ge_iff _ (n + 1)).mp (by rw [h])
    have hK1 : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n this).mp hM1
    have hK2 : ¬ HasProjectiveDimensionLT (ModuleCat.of R K) n := by
      intro hK
      apply hM2
      cases n with
      | zero =>
        have hz : Limits.IsZero S.X₁ := (hasProjectiveDimensionLT_zero_iff_isZero _).mp hK
        have : IsIso S.g := hS.isIso_g_iff.mpr hz
        have : Projective S.X₃ := Projective.of_iso (asIso S.g) inferInstance
        exact projective_iff_hasProjectiveDimensionLT_one.mp this
      | succ n => exact (hS.hasProjectiveDimensionLT_X₃_iff n ‹_›).mpr hK
    have hKn : projectiveDimension (ModuleCat.of R K) = n :=
      le_antisymm ((projectiveDimension_le_iff _ n).mpr hK1)
        ((projectiveDimension_ge_iff _ n).mpr hK2)
    have : Nontrivial K := by
      by_contra hK
      rw [not_nontrivial_iff_subsingleton] at hK
      have : HasProjectiveDimensionLT (ModuleCat.of R K) 0 :=
        (hasProjectiveDimensionLT_zero_iff_isZero _).mpr (ModuleCat.isZero_of_subsingleton _)
      exact hK2 (hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le n))
    have ihK := ih K hKn
    -- depths
    have : Nonempty t := by
      by_contra ht
      rw [not_nonempty_iff] at ht
      have : (t : Set M) = ∅ := by
        ext z; simp only [Finset.mem_coe, Set.mem_empty_iff_false, iff_false]
        exact fun hz ↦ ht.elim ⟨z, hz⟩
      rw [this, Submodule.span_empty] at htspan
      refine not_subsingleton M (subsingleton_of_forall_eq 0 fun z ↦ ?_)
      have : z ∈ (⊤ : Submodule R M) := trivial
      rwa [← htspan, Submodule.mem_bot] at this
    have hdF := Ideal.depth_of_free (maximalIdeal R) (t → R)
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp (IsLocalRing.depth_ne_top (R := R) (M := R))
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (IsLocalRing.depth_ne_top (R := R) (M := K))
    rw [← hd, ← he] at ihK
    have hed : n + e = d := by exact_mod_cast ihK
    rw [← hd] at hdF
    obtain ⟨hF1, hF2⟩ := (depth_eq_iff_ext (t → R) d).mp hdF
    obtain ⟨hK1', hK2'⟩ := (depth_eq_iff_ext K e).mp he.symm
    -- the map `Ext^i(R/𝔪, K) → Ext^i(R/𝔪, R^t)` vanishes when `n = 0` (minimality)
    have hzero : n = 0 → ∀ (i : ℕ) (x₁ : Ext 𝕜 S.X₁ i),
        x₁.comp (Ext.mk₀ S.f) (add_zero _) = 0 := by
      rintro rfl i x₁
      have : Module.Free R K := by
        have : Projective (ModuleCat.of R K) := (projective_iff_hasProjectiveDimensionLE_zero _).mpr
          hK1
        rw [← IsProjective.iff_projective] at this
        exact Module.free_of_flat_of_isLocalRing
      refine ext_comp_mk₀_eq_zero_of_range_le K.subtype (fun z ↦ ?_) x₁
      rw [Submodule.subtype_apply, pi_eq_sum_univ (z : t → R)]
      refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hmin z z.2 i) trivial
    -- `e ≥ 1`
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun he0 ↦ hK2' ?_)
      subst he0
      apply subsingleton_ext_X₁_zero hS
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact hzero hn 0
      · intro x₁
        have : Subsingleton (Ext 𝕜 S.X₂ 0) := hF1 0 (by omega)
        exact Subsingleton.elim _ _
    -- `depth M = e`
    have hM : (maximalIdeal R).depth M = e := by
      rw [depth_eq_iff_ext]
      refine ⟨fun i hi ↦ subsingleton_ext_X₃ hS (hF1 i (by omega)) (hK1' (i + 1) (by omega)),
        fun hMe ↦ hK2' (subsingleton_ext_X₁_succ hS ?_ hMe)⟩
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact hzero hn (e + 1)
      · intro x₁
        have : Subsingleton (Ext 𝕜 S.X₂ (e + 1)) := hF1 (e + 1) (by omega)
        exact Subsingleton.elim _ _
    rw [hM, ← hd, ← hed]
    push_cast
    ring

/-- The Auslander–Buchsbaum formula (Stacks 090V): if a nonzero finite module `M` over a noetherian
local ring `R` has finite projective dimension, then `pd M + depth M = depth R`. -/
@[stacks 090V]
theorem IsLocalRing.projectiveDimension_add_depth (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (h : projectiveDimension (ModuleCat.of R M) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R M) + ((maximalIdeal R).depth M : WithBot ℕ∞) =
      (maximalIdeal R).depth R := by
  have hbot : projectiveDimension (ModuleCat.of R M) ≠ ⊥ := by
    rw [Ne, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    exact not_subsingleton M
  obtain ⟨n, hn⟩ : ∃ n : ℕ, projectiveDimension (ModuleCat.of R M) = n := by
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
    rw [← he] at h
    have he' : e ≠ ⊤ := fun h' ↦ h (by rw [h']; rfl)
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp he'
    exact ⟨n, he.symm⟩
  rw [hn, ← natCast_add_depth_eq_depth_of_projectiveDimension_eq R n M hn]
  rfl

/-- A consequence of Auslander–Buchsbaum: a finite module of finite projective dimension over a
noetherian local ring has projective dimension at most `depth R`. -/
theorem IsLocalRing.projectiveDimension_le_depth (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (h : projectiveDimension (ModuleCat.of R M) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R M) ≤ (maximalIdeal R).depth R := by
  rw [← IsLocalRing.projectiveDimension_add_depth M h]
  exact le_add_of_nonneg_right (WithBot.coe_nonneg.mpr zero_le)

end AuslanderBuchsbaum
