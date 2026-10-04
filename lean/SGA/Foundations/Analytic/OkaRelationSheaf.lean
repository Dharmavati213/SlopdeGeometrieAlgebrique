/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaRelations
import SGA.Foundations.Analytic.OkaSpreading
import SGA.Foundations.Analytic.LocalModelHom
import SGA.Foundations.Analytic.Noetherian
import SGA.Foundations.Analytic.Stalk

/-!
# Relation sheaves of matrices of analytic functions

Let `A = (A_{k i})` be a finite matrix of analytic functions near a point `x₀` of a normed space
`E`. Its *relation sheaf* has as stalk at `y` the module of germs `(a_i) ∈ 𝒪_y^ι` with
`∑ᵢ aᵢ A_{k i} = 0` for all `k` (`matrixRelationModule`). The relation sheaf is *of finite type
near `x₀`* (`HasFiniteRelationsNear A x₀`) if finitely many analytic relations defined on one
open neighbourhood `V` of `x₀` generate it at every point of `V`. Oka's coherence theorem says
that this always holds on `𝕜ⁿ` ([Grauert–Remmert, *Coherent analytic sheaves*, 2.5];
[Demailly, *Complex analytic and differential geometry*, II.3.19]); it is proved in
`SGA.Foundations.Analytic.OkaInduction`.

This file contains the formal parts of the proof:

* `HasFiniteRelationsNear.of_eventuallyEq`: the property only depends on the germs at `x₀`;
* `HasFiniteRelationsNear.comp_analyticEquiv`: invariance under analytic changes of coordinates
  with analytic inverse;
* `HasFiniteRelationsNear.of_mul`: multiplying the columns by functions which do not vanish
  at `x₀` does not change the property;
* `HasFiniteRelationsNear.of_rows`: the case of one row implies the case of a matrix (adding the
  rows one at a time);
* `HasFiniteRelationsNear.of_isEmpty`: the case of a point (the stalk is noetherian).
-/

noncomputable section

universe u

open TopologicalSpace Filter Set
open scoped Topology

namespace AnalyticGeometry

/-! ### Relations of a matrix over a ring -/

section Algebra

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι]

/-- The module of relations `a` with `∑ᵢ aᵢ A_{k i} = 0` for every row `k` of a matrix. -/
def matrixRelationModule (A : κ → ι → R) : Submodule R (ι → R) :=
  ⨅ k, relationModule (A k)

lemma mem_matrixRelationModule {A : κ → ι → R} {a : ι → R} :
    a ∈ matrixRelationModule A ↔ ∀ k, ∑ i, a i * A k i = 0 := by
  simp [matrixRelationModule, Submodule.mem_iInf]

/-- A ring isomorphism carries relations to relations. -/
lemma map_mem_matrixRelationModule_iff {S : Type*} [CommRing S] (e : R ≃+* S)
    (A : κ → ι → R) (a : ι → R) :
    (fun i ↦ e (a i)) ∈ matrixRelationModule (fun k i ↦ e (A k i)) ↔
      a ∈ matrixRelationModule A := by
  simp only [mem_matrixRelationModule, ← map_mul, ← map_sum, map_eq_zero_iff _ e.injective]

omit [Fintype ι] in
/-- A ring isomorphism carries spans of finite families to spans. -/
lemma map_mem_span_range_iff {S : Type*} [CommRing S] (e : R ≃+* S) {μ : Type*} [Finite μ]
    (g : μ → ι → R) (a : ι → R) :
    (fun i ↦ e (a i)) ∈ Submodule.span S (Set.range fun m i ↦ e (g m i)) ↔
      a ∈ Submodule.span R (Set.range g) := by
  have := Fintype.ofFinite μ
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun m ↦ e.symm (c m), funext fun i ↦ e.injective ?_⟩
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [map_sum, ← this]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [map_mul, RingEquiv.apply_symm_apply]
  · rintro ⟨c, hc⟩
    refine ⟨fun m ↦ e (c m), funext fun i ↦ ?_⟩
    have := congrArg e (congrFun hc i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this ⊢
    exact this

/-- Transport of a presentation of the relation module along a ring isomorphism. -/
lemma matrixRelationModule_map_eq_span {S : Type*} [CommRing S] (e : R ≃+* S) {μ : Type*}
    [Finite μ] {A : κ → ι → R} {g : μ → ι → R}
    (h : matrixRelationModule A = Submodule.span R (Set.range g)) :
    matrixRelationModule (fun k i ↦ e (A k i)) =
      Submodule.span S (Set.range fun m i ↦ e (g m i)) := by
  have := Fintype.ofFinite μ
  ext a
  have ha : a = fun i ↦ e (e.symm (a i)) := funext fun i ↦ (e.apply_symm_apply _).symm
  rw [ha, map_mem_matrixRelationModule_iff, map_mem_span_range_iff, h]

/-- Multiplying the columns of a matrix by units: if the relations of `(A_{k i} wᵢ)` are spanned
by the `g_m`, those of `A` are spanned by the `(g_{m i} wᵢ)`. -/
lemma matrixRelationModule_eq_span_of_mul_units {μ : Type*} [Finite μ] {A : κ → ι → R}
    (w : ι → Rˣ) {g : μ → ι → R}
    (h : matrixRelationModule (fun k i ↦ A k i * w i) = Submodule.span R (Set.range g)) :
    matrixRelationModule A = Submodule.span R (Set.range fun m i ↦ g m i * w i) := by
  have := Fintype.ofFinite μ
  ext a
  have key : a ∈ matrixRelationModule A ↔
      (fun i ↦ a i * ↑(w i)⁻¹) ∈ matrixRelationModule (fun k i ↦ A k i * w i) := by
    simp only [mem_matrixRelationModule]
    refine forall_congr' fun k ↦ ?_
    rw [iff_eq_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc a i * A k i = a i * A k i * (↑(w i)⁻¹ * w i) := by rw [Units.inv_mul, mul_one]
      _ = _ := by ring
  rw [key, h, Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun i ↦ ?_⟩
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    calc ∑ m, c m * (g m i * w i) = (∑ m, c m * g m i) * w i := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ ↦ by ring
      _ = a i := by rw [this, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun i ↦ ?_⟩
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    calc c m * g m i = c m * (g m i * (w i * ↑(w i)⁻¹)) := by rw [Units.mul_inv, mul_one]
      _ = _ := by ring

/-- Adding one row to a matrix (Oka's argument for the passage from one row to several rows):
if the relations of the rows `A` are spanned by the `G m`, and the relations of the row
`h_m = ∑ᵢ G_{m i} bᵢ` are spanned by the `H t`, then the relations of `A` together with the new
row `b` are spanned by the `∑ₘ H_{t m} G_m`. -/
lemma matrixRelationModule_option_eq_span {μ ν : Type*} [Fintype μ] [Finite ν]
    {A : κ → ι → R} (b : ι → R) {G : μ → ι → R}
    (hG : matrixRelationModule A = Submodule.span R (Set.range G)) {H : ν → μ → R}
    (hH : relationModule (fun m ↦ ∑ i, G m i * b i) = Submodule.span R (Set.range H)) :
    matrixRelationModule (fun k : Option κ ↦ k.elim b A) =
      Submodule.span R (Set.range fun t i ↦ ∑ m, H t m * G m i) := by
  have := Fintype.ofFinite ν
  have hGmem (m : μ) : G m ∈ matrixRelationModule A := hG ▸ Submodule.subset_span ⟨m, rfl⟩
  apply le_antisymm
  · intro a ha
    rw [mem_matrixRelationModule] at ha
    have haA : a ∈ matrixRelationModule A := mem_matrixRelationModule.mpr fun k ↦ ha (some k)
    rw [hG, Submodule.mem_span_range_iff_exists_fun] at haA
    obtain ⟨c, rfl⟩ := haA
    have hc : c ∈ relationModule (fun m ↦ ∑ i, G m i * b i) := by
      rw [mem_relationModule]
      have := ha none
      simp only [Option.elim_none, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hH, Submodule.mem_span_range_iff_exists_fun] at hc
    obtain ⟨d, rfl⟩ := hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨d, funext fun i ↦ ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun m _ ↦ by ring
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, mem_matrixRelationModule]
    have hHt : H t ∈ relationModule (fun m ↦ ∑ i, G m i * b i) :=
      hH ▸ Submodule.subset_span ⟨t, rfl⟩
    rw [mem_relationModule] at hHt
    rintro (_ | k)
    · simp only [Option.elim_none]
      rw [← hHt]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    · simp only [Option.elim_some]
      have hk (m : μ) : ∑ i, G m i * A k i = 0 := mem_matrixRelationModule.mp (hGmem m) k
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      rw [← mul_zero (H t m), ← hk m, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Reindexing the rows does not change the relations. -/
lemma matrixRelationModule_comp_equiv {κ' : Type*} (e : κ' ≃ κ) (A : κ → ι → R) :
    matrixRelationModule (fun k ↦ A (e k)) = matrixRelationModule A := by
  ext a
  simp only [mem_matrixRelationModule]
  exact ⟨fun h k ↦ by simpa using h (e.symm k), fun h k ↦ h (e k)⟩

omit [Fintype ι] in
/-- Reindexing the generators does not change their span. -/
lemma span_range_comp_equiv {μ μ' : Type*} (e : μ' ≃ μ) (g : μ → ι → R) :
    Submodule.span R (Set.range fun m ↦ g (e m)) = Submodule.span R (Set.range g) := by
  congr 1
  exact e.surjective.range_comp g

/-- A matrix with no rows: every vector is a relation. -/
lemma matrixRelationModule_of_isEmpty [IsEmpty κ] [DecidableEq ι] (A : κ → ι → R) :
    matrixRelationModule A = Submodule.span R (Set.range fun i : ι ↦ Pi.single i 1) := by
  have htop : matrixRelationModule A = ⊤ :=
    Submodule.eq_top_iff'.mpr fun a ↦ by simp [mem_matrixRelationModule]
  rw [htop, ← (Pi.basisFun R ι).span_eq]
  congr 2
  funext i
  exact Pi.basisFun_apply R ι i

end Algebra

/-! ### Germs of finite families of functions -/

section Germs

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma germOf_sum_mul {y : E} {μ : Type*} [Fintype μ] {f g : μ → E → 𝕜}
    (hf : ∀ m, AnalyticAt 𝕜 (f m) y) (hg : ∀ m, AnalyticAt 𝕜 (g m) y)
    (h : AnalyticAt 𝕜 (fun z ↦ ∑ m, f m z * g m z) y) :
    germOf (fun z ↦ ∑ m, f m z * g m z) h = ∑ m, germOf (f m) (hf m) * germOf (g m) (hg m) := by
  rw [germOf_sum Finset.univ (g := fun m z ↦ f m z * g m z) (fun m ↦ (hf m).mul (hg m)) h]
  exact Finset.sum_congr rfl fun m _ ↦ germOf_mul (hf m) (hg m)

omit [CompleteSpace 𝕜] in
lemma analyticAt_sum_mul {y : E} {μ : Type*} [Fintype μ] {f g : μ → E → 𝕜}
    (hf : ∀ m, AnalyticAt 𝕜 (f m) y) (hg : ∀ m, AnalyticAt 𝕜 (g m) y) :
    AnalyticAt 𝕜 (fun z ↦ ∑ m, f m z * g m z) y :=
  (Finset.univ.analyticAt_sum fun m _ ↦ (hf m).mul (hg m)).congr
    (Eventually.of_forall fun z ↦ by simp)

lemma germOf_eq_zero_iff {y : E} {f : E → 𝕜} (hf : AnalyticAt 𝕜 f y) :
    germOf f hf = 0 ↔ f =ᶠ[𝓝 y] 0 := by
  rw [← germOf_zero (x := y), germOf_eq_germOf_iff]
  rfl

end Germs

/-! ### Relation sheaves of finite type -/

section RelationSheaf

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ι κ : Type} [Fintype ι]

/-- The relation sheaf of a matrix `A` of functions is *of finite type near `x₀`*: on some open
neighbourhood `V` of `x₀` the entries of `A` are analytic, and finitely many analytic relations
`g_m` on `V` generate the module of relations between the germs of the columns of `A` at every
point of `V`. -/
def HasFiniteRelationsNear (A : κ → ι → E → 𝕜) (x₀ : E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ (hA : ∀ k i, ∀ y ∈ V, AnalyticAt 𝕜 (A k i) y) (n : ℕ)
    (g : Fin n → ι → E → 𝕜) (hg : ∀ m i, ∀ y ∈ V, AnalyticAt 𝕜 (g m i) y),
    ∀ y (hy : y ∈ V), matrixRelationModule (fun k i ↦ germOf (A k i) (hA k i y hy)) =
      Submodule.span _ (Set.range fun m i ↦ germOf (g m i) (hg m i y hy))

namespace HasFiniteRelationsNear

/-- A variant of the definition with generators indexed by any finite type. -/
lemma of_fintype {A : κ → ι → E → 𝕜} {x₀ : E} {V : Set E} (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (hA : ∀ k i, ∀ y ∈ V, AnalyticAt 𝕜 (A k i) y) {μ : Type*} [Finite μ]
    (g : μ → ι → E → 𝕜) (hg : ∀ m i, ∀ y ∈ V, AnalyticAt 𝕜 (g m i) y)
    (h : ∀ y (hy : y ∈ V), matrixRelationModule (fun k i ↦ germOf (A k i) (hA k i y hy)) =
      Submodule.span _ (Set.range fun m i ↦ germOf (g m i) (hg m i y hy))) :
    HasFiniteRelationsNear A x₀ := by
  have := Fintype.ofFinite μ
  let e := Fintype.equivFin μ
  refine ⟨V, hV, hx₀, hA, Fintype.card μ, fun m ↦ g (e.symm m), fun m ↦ hg (e.symm m),
    fun y hy ↦ ?_⟩
  rw [h y hy]
  exact (span_range_comp_equiv e.symm (fun m i ↦ germOf (g m i) (hg m i y hy))).symm

/-- Shrinking the neighbourhood. -/
lemma mono {A : κ → ι → E → 𝕜} {x₀ : E} {V : Set E} (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (hA : ∀ k i, ∀ y ∈ V, AnalyticAt 𝕜 (A k i) y) {n : ℕ}
    (g : Fin n → ι → E → 𝕜) (hg : ∀ m i, ∀ y ∈ V, AnalyticAt 𝕜 (g m i) y)
    (h : ∀ y (hy : y ∈ V), matrixRelationModule (fun k i ↦ germOf (A k i) (hA k i y hy)) =
      Submodule.span _ (Set.range fun m i ↦ germOf (g m i) (hg m i y hy)))
    {W : Set E} (hW : IsOpen W) (hx₀W : x₀ ∈ W) :
    ∃ V' ⊆ W, IsOpen V' ∧ x₀ ∈ V' ∧ ∃ (hA' : ∀ k i, ∀ y ∈ V', AnalyticAt 𝕜 (A k i) y)
      (hg' : ∀ m i, ∀ y ∈ V', AnalyticAt 𝕜 (g m i) y),
      ∀ y (hy : y ∈ V'), matrixRelationModule (fun k i ↦ germOf (A k i) (hA' k i y hy)) =
        Submodule.span _ (Set.range fun m i ↦ germOf (g m i) (hg' m i y hy)) :=
  ⟨V ∩ W, inter_subset_right, hV.inter hW, ⟨hx₀, hx₀W⟩, fun k i y hy ↦ hA k i y hy.1,
    fun m i y hy ↦ hg m i y hy.1, fun y hy ↦ h y hy.1⟩

/-- The property only depends on the germs of the entries at `x₀`. -/
lemma of_eventuallyEq {A A' : κ → ι → E → 𝕜} {x₀ : E} (h : HasFiniteRelationsNear A x₀)
    (hAA' : ∀ k i, A k i =ᶠ[𝓝 x₀] A' k i) [Finite κ] : HasFiniteRelationsNear A' x₀ := by
  obtain ⟨V, hV, hx₀, hA, n, g, hg, hgen⟩ := h
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ k i, A k i y = A' k i y :=
    eventually_all.mpr fun k ↦ eventually_all.mpr fun i ↦ hAA' k i
  obtain ⟨W, hWsub, hW, hx₀W⟩ := mem_nhds_iff.mp hev
  have heq (k i) (y) (hy : y ∈ W) : A k i =ᶠ[𝓝 y] A' k i :=
    Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz ↦ hWsub hz k i
  refine ⟨V ∩ W, hV.inter hW, ⟨hx₀, hx₀W⟩,
    fun k i y hy ↦ (hA k i y hy.1).congr (heq k i y hy.2), n, g,
    fun m i y hy ↦ hg m i y hy.1, fun y hy ↦ ?_⟩
  rw [← hgen y hy.1]
  congr 1
  funext k i
  exact (germOf_congr _ (heq k i y hy.2)).symm

/-- Invariance under an analytic isomorphism `Ψ` (with analytic inverse `Φ`): if the relations
of `B` are of finite type near `Ψ z₀`, those of `B ∘ Ψ` are of finite type near `z₀`. -/
lemma comp_analyticEquiv {E' : Type u} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {B : κ → ι → E' → 𝕜} {Ψ : E → E'} {Φ : E' → E} (hΨ : ∀ z, AnalyticAt 𝕜 Ψ z)
    (hΦ : ∀ w, AnalyticAt 𝕜 Φ w) (hΦΨ : ∀ z, Φ (Ψ z) = z) (hΨΦ : ∀ w, Ψ (Φ w) = w) {z₀ : E}
    (h : HasFiniteRelationsNear B (Ψ z₀)) :
    HasFiniteRelationsNear (fun k i z ↦ B k i (Ψ z)) z₀ := by
  obtain ⟨V, hV, hx₀, hB, n, g, hg, hgen⟩ := h
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun z ↦ (hΨ z).continuousAt
  -- the pullback of germs along `Ψ` is bijective at every point
  have hbij (y : E) : Function.Bijective (stalkPullback Ψ (hΨ y)) := by
    constructor
    · intro s t hst
      induction s using germOf_induction with
      | h G hG =>
      induction t using germOf_induction with
      | h G' hG' =>
      rw [stalkPullback_germOf, stalkPullback_germOf, germOf_eq_germOf_iff] at hst
      rw [germOf_eq_germOf_iff]
      have hΦc : Tendsto Φ (𝓝 (Ψ y)) (𝓝 y) := by
        have := (hΦ (Ψ y)).continuousAt.tendsto
        rwa [hΦΨ] at this
      filter_upwards [hΦc.eventually hst] with w hw
      simpa only [hΨΦ] using hw
    · intro s
      induction s using germOf_induction with
      | h G hG =>
      have hG' : AnalyticAt 𝕜 (fun w ↦ G (Φ w)) (Ψ y) :=
        AnalyticAt.comp (g := G) (by rwa [hΦΨ]) (hΦ (Ψ y))
      refine ⟨germOf (fun w ↦ G (Φ w)) hG', ?_⟩
      rw [stalkPullback_germOf]
      exact germOf_congr _ (Eventually.of_forall fun z ↦ by simp only [hΦΨ])
  let e (y : E) := RingEquiv.ofBijective (stalkPullback Ψ (hΨ y)) (hbij y)
  refine ⟨Ψ ⁻¹' V, hV.preimage hΨc, hx₀, fun k i y hy ↦ (hB k i (Ψ y) hy).comp (hΨ y), n,
    fun m i z ↦ g m i (Ψ z), fun m i y hy ↦ (hg m i (Ψ y) hy).comp (hΨ y), fun y hy ↦ ?_⟩
  have := matrixRelationModule_map_eq_span (e y) (hgen (Ψ y) hy)
  refine (?_ : _ = _).trans (this.trans ?_)
  · congr 1
    funext k i
    exact (stalkPullback_germOf Ψ (hΨ y) (B k i) _).symm
  · congr 2
    funext m i
    exact stalkPullback_germOf Ψ (hΨ y) (g m i) _

/-- Multiplying the columns by functions not vanishing at `x₀`. -/
lemma of_mul {A : κ → ι → E → 𝕜} {w : ι → E → 𝕜} {x₀ : E} (hw : ∀ i, AnalyticAt 𝕜 (w i) x₀)
    (hw₀ : ∀ i, w i x₀ ≠ 0) (h : HasFiniteRelationsNear (fun k i z ↦ A k i z * w i z) x₀)
    (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀) [Finite κ] :
    HasFiniteRelationsNear A x₀ := by
  obtain ⟨V, hV, hx₀, hAw, n, g, hg, hgen⟩ := h
  have hev : ∀ᶠ y in 𝓝 x₀, (∀ i, AnalyticAt 𝕜 (w i) y ∧ w i y ≠ 0) ∧
      ∀ k i, AnalyticAt 𝕜 (A k i) y := by
    refine (eventually_all.mpr fun i ↦ ?_).and (eventually_all.mpr fun k ↦
      eventually_all.mpr fun i ↦ (hA k i).eventually_analyticAt)
    exact (hw i).eventually_analyticAt.and ((hw i).continuousAt.eventually_ne (hw₀ i))
  obtain ⟨W, hWsub, hW, hx₀W⟩ := mem_nhds_iff.mp hev
  have hwW (i) (y) (hy : y ∈ W) : AnalyticAt 𝕜 (w i) y := ((hWsub hy).1 i).1
  have hunit (i) (y) (hy : y ∈ W) : IsUnit (germOf (w i) (hwW i y hy)) := by
    rw [isUnit_stalk_iff, evalStalk_germOf]
    exact ((hWsub hy).1 i).2
  refine of_fintype (hV.inter hW) ⟨hx₀, hx₀W⟩ (fun k i y hy ↦ (hWsub hy.2).2 k i)
    (fun m i z ↦ g m i z * w i z)
    (fun m i y hy ↦ (hg m i y hy.1).mul (hwW i y hy.2)) fun y hy ↦ ?_
  let u : ι → (analyticPresheaf 𝕜 E).stalk y := fun i ↦ germOf (w i) (hwW i y hy.2)
  have hu (i : ι) : IsUnit (u i) := hunit i y hy.2
  have key := matrixRelationModule_eq_span_of_mul_units (fun i ↦ (hu i).unit)
    (A := fun k i ↦ germOf (A k i) ((hWsub hy.2).2 k i)) (g := fun m i ↦ germOf (g m i)
      (hg m i y hy.1)) (by
      rw [← hgen y hy.1]
      congr 1
      funext k i
      rw [IsUnit.unit_spec, ← germOf_mul]
      rfl)
  rw [key]
  refine congrArg (Submodule.span _) (congrArg Set.range (funext fun m ↦ funext fun i ↦ ?_))
  rw [IsUnit.unit_spec, ← germOf_mul]
  rfl

/-- A row of functions vanishing near `x₀`: every vector is a relation. -/
lemma of_eventually_eq_zero {f : κ → ι → E → 𝕜} {x₀ : E} [Finite κ]
    (hf : ∀ k i, f k i =ᶠ[𝓝 x₀] 0) : HasFiniteRelationsNear f x₀ := by
  classical
  refine of_eventuallyEq (A := fun _ _ _ ↦ 0) ?_ fun k i ↦ (hf k i).symm
  refine of_fintype isOpen_univ (mem_univ x₀) (fun _ _ _ _ ↦ analyticAt_const)
    (fun (j : ι) i (_ : E) ↦ if i = j then (1 : 𝕜) else 0) (fun _ _ _ _ ↦ analyticAt_const)
    fun y hy ↦ ?_
  have hzero : (fun (_ : κ) (_ : ι) ↦ germOf (fun _ : E ↦ (0 : 𝕜)) (analyticAt_const (x := y))) =
      fun _ _ ↦ 0 := by
    funext k i
    exact germOf_zero
  rw [hzero]
  apply le_antisymm
  · intro a _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, funext fun i ↦ ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)]
    · convert mul_one (a i) using 2
      rw [← germOf_one (x := y)]
      exact germOf_congr _ (Eventually.of_forall fun _ ↦ by simp)
    · convert mul_zero (a j) using 2
      rw [← germOf_zero (x := y)]
      exact germOf_congr _ (Eventually.of_forall fun _ ↦ by simp [Ne.symm hj])
  · intro a _
    simp [mem_matrixRelationModule]

/-- Reindexing the rows. -/
lemma of_comp_equiv {κ' : Type} (e : κ' ≃ κ) {A : κ → ι → E → 𝕜} {x₀ : E}
    (h : HasFiniteRelationsNear (fun k ↦ A (e k)) x₀) : HasFiniteRelationsNear A x₀ := by
  obtain ⟨V, hV, hx₀, hA, n, g, hg, hgen⟩ := h
  have hA' (k i) (y) (hy : y ∈ V) : AnalyticAt 𝕜 (A k i) y := by
    simpa using hA (e.symm k) i y hy
  refine ⟨V, hV, hx₀, hA', n, g, hg, fun y hy ↦ ?_⟩
  rw [← hgen y hy]
  exact (matrixRelationModule_comp_equiv e _).symm

/-- One row: the relation module of a row is `relationModule`. -/
lemma matrixRelationModule_unit {R : Type*} [CommRing R] (f : ι → R) :
    matrixRelationModule (fun _ : Unit ↦ f) = relationModule f := by
  ext a
  simp [mem_matrixRelationModule]

/-- **Oka's reduction from matrices to rows**: if the relations of every finite row of functions
analytic at `x₀` are of finite type near `x₀`, so are those of every finite matrix. -/
lemma of_rows {x₀ : E}
    (hrow : ∀ (ι : Type) [Fintype ι] (f : ι → E → 𝕜), (∀ i, AnalyticAt 𝕜 (f i) x₀) →
      HasFiniteRelationsNear (fun (_ : Unit) ↦ f) x₀)
    (κ : Type) [Finite κ] (A : κ → ι → E → 𝕜) (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀) :
    HasFiniteRelationsNear A x₀ := by
  have := Fintype.ofFinite κ
  classical
  revert A
  refine Fintype.induction_empty_option (P := fun κ _ ↦ ∀ A : κ → ι → E → 𝕜,
    (∀ k i, AnalyticAt 𝕜 (A k i) x₀) → HasFiniteRelationsNear A x₀) ?_ ?_ ?_ κ
  · intro α β _ e hα A hA
    exact of_comp_equiv e (hα _ fun k i ↦ hA (e k) i)
  · intro A _
    exact of_eventually_eq_zero fun k ↦ PEmpty.elim k
  · intro α _ hα A hA
    have hev : ∀ᶠ y in 𝓝 x₀, ∀ k i, AnalyticAt 𝕜 (A k i) y :=
      eventually_all.mpr fun k ↦ eventually_all.mpr fun i ↦ (hA k i).eventually_analyticAt
    obtain ⟨W, hWsub, hW, hx₀W⟩ := mem_nhds_iff.mp hev
    obtain ⟨V₁, hV₁, hx₁, hA₁, n, G, hG, hgen₁⟩ := hα (fun k ↦ A (some k)) fun k ↦ hA (some k)
    have hAW (k i) (y) (hy : y ∈ W) : AnalyticAt 𝕜 (A k i) y := hWsub hy k i
    -- the new row, restricted to the relations of the old rows
    let h : Fin n → E → 𝕜 := fun m z ↦ ∑ i, G m i z * A none i z
    have hh (y) (hy : y ∈ V₁ ∩ W) (m) : AnalyticAt 𝕜 (h m) y :=
      analyticAt_sum_mul (fun i ↦ hG m i y hy.1) fun i ↦ hAW none i y hy.2
    obtain ⟨V₂, hV₂, hx₂, hh₂, n', H, hH, hgen₂⟩ := hrow (Fin n) h (hh x₀ ⟨hx₁, hx₀W⟩)
    refine of_fintype ((hV₁.inter hW).inter hV₂) ⟨⟨hx₁, hx₀W⟩, hx₂⟩
      (fun k i y hy ↦ hAW k i y hy.1.2)
      (fun t i z ↦ ∑ m, H t m z * G m i z)
      (fun t i y hy ↦ analyticAt_sum_mul (fun m ↦ hH t m y hy.2) fun m ↦ hG m i y hy.1.1)
      fun y hy ↦ ?_
    have hA_eq : (fun k i ↦ germOf (A k i) (hAW k i y hy.1.2)) =
        fun k : Option α ↦ k.elim (fun i ↦ germOf (A none i) (hAW none i y hy.1.2))
          (fun k i ↦ germOf (A (some k) i) (hAW (some k) i y hy.1.2)) := by
      funext k i
      cases k <;> rfl
    have hrow_eq : (fun m ↦ germOf (h m) (hh y hy.1 m)) = fun m ↦
        ∑ i, germOf (G m i) (hG m i y hy.1.1) * germOf (A none i) (hAW none i y hy.1.2) := by
      funext m
      exact germOf_sum_mul _ _ _
    have h₂ : relationModule (fun m ↦
        ∑ i, germOf (G m i) (hG m i y hy.1.1) * germOf (A none i) (hAW none i y hy.1.2)) =
        Submodule.span _ (Set.range fun t m ↦ germOf (H t m) (hH t m y hy.2)) := by
      rw [← hrow_eq, ← matrixRelationModule_unit]
      exact hgen₂ y hy.2
    rw [hA_eq, matrixRelationModule_option_eq_span _ (hgen₁ y hy.1.1) h₂]
    refine congrArg (Submodule.span _) (congrArg Set.range (funext fun t ↦ funext fun i ↦ ?_))
    exact (germOf_sum_mul _ _ _).symm

/-- On a space with one point, the relations of every matrix are of finite type: the stalk is
the noetherian ring `𝕜{X_σ}` with `σ` empty. -/
lemma of_isEmpty {σ : Type u} [Fintype σ] [IsEmpty σ] {A : κ → ι → (σ → 𝕜) → 𝕜} {x₀ : σ → 𝕜}
    (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀) : HasFiniteRelationsNear A x₀ := by
  classical
  have : IsNoetherianRing ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀) :=
    isNoetherianRing_of_ringEquiv _ (convergentStalkEquiv x₀)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian
    (matrixRelationModule fun k i ↦ germOf (A k i) (hA k i))
  have hpt (y : σ → 𝕜) : y = x₀ := Subsingleton.elim _ _
  refine of_fintype isOpen_univ (mem_univ x₀) (fun k i y _ ↦ hpt y ▸ hA k i)
    (fun (v : s) i ↦ germRep (v.1 i))
    (fun v i y _ ↦ hpt y ▸ analyticAt_germRep (v.1 i)) fun y hy ↦ ?_
  obtain rfl := hpt y
  rw [← hs]
  have hfun : (fun (v : s) i ↦ germOf (germRep (v.1 i)) (analyticAt_germRep (v.1 i))) =
      fun v ↦ v.1 := funext fun v ↦ funext fun i ↦ germOf_germRep _
  rw [hfun, Subtype.range_coe_subtype]
  rfl

end HasFiniteRelationsNear

end RelationSheaf

end AnalyticGeometry
