/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.NoetherianSpace
import SGA.Foundations.Dimension.FiniteType

/-!
# The dimension of a space at a point

For a topological space `X` and `x ∈ X`, the *dimension of `X` at `x`*,
`topologicalKrullDimAt X x`, is the infimum of the Krull dimensions of the open neighbourhoods
of `x` (EGA 0_IV §14.1). It only depends on a neighbourhood of `x`
(`Topology.IsOpenEmbedding.topologicalKrullDimAt_eq`), and may be computed on a basis of open
sets.

For `Spec A` it is the infimum of `dim A_f` over `f ∉ q`. When `A` is of finite type over a field
`k` we prove (EGA IV §5.2; Stacks Project, section "Dimension of finite type algebras over fields"):

* `Algebra.FiniteType.topologicalKrullDimAt_eq`: `dim_q (Spec A) = ht q + dim A/q`;
* `Algebra.FiniteType.topologicalKrullDimAt_eq_iSup`: `dim_q (Spec A)` is the maximal dimension of
  an irreducible component of `Spec A` through `q`;
* `Algebra.FiniteType.topologicalKrullDimAt_eq_height_add_trdeg`:
  `dim_q (Spec A) = dim A_q + trdeg_k κ(q)`.

The key algebraic input is that for `A` of finite type over `k`, localizing at an element does
not change the dimension `dim A/P` of the quotients by primes
(`Algebra.FiniteType.coheight_comap_localization_away`), since it does not change transcendence
degrees.
-/

open Order Cardinal PrimeSpectrum TopologicalSpace Topology

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable (X) in
/-- The dimension of a topological space `X` at a point `x`: the infimum of the Krull dimensions
of the open neighbourhoods of `x` (EGA 0_IV §14.1). -/
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U

theorem topologicalKrullDim_mono {s t : Set X} (h : s ⊆ t) :
    topologicalKrullDim s ≤ topologicalKrullDim t :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- An embedding identifies a subspace with its image, so they have the same dimension. -/
theorem Topology.IsEmbedding.topologicalKrullDim_image {f : Y → X} (hf : IsEmbedding f)
    (s : Set Y) : topologicalKrullDim (f '' s) = topologicalKrullDim s := by
  have h : Set.range (f ∘ Subtype.val : s → X) = f '' s := by
    rw [Set.range_comp, Subtype.range_coe]
  rw [← h]
  exact ((hf.comp IsEmbedding.subtypeVal).toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm

theorem topologicalKrullDimAt_le {x : X} {U : Opens X} (hx : x ∈ U) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim U :=
  iInf₂_le U hx

theorem le_topologicalKrullDimAt_iff {x : X} {d : WithBot ℕ∞} :
    d ≤ topologicalKrullDimAt X x ↔ ∀ U : Opens X, x ∈ U → d ≤ topologicalKrullDim U :=
  le_iInf₂_iff

theorem topologicalKrullDimAt_le_topologicalKrullDim (x : X) :
    topologicalKrullDimAt X x ≤ topologicalKrullDim X :=
  (topologicalKrullDimAt_le (U := ⊤) trivial).trans (topologicalKrullDim_subspace_le X _)

/-- The dimension at a point can be computed on the members of a basis of open sets. -/
theorem topologicalKrullDimAt_eq_iInf_of_isBasis {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (x : X) : topologicalKrullDimAt X x = ⨅ U ∈ B, ⨅ (_ : x ∈ U), topologicalKrullDim U := by
  refine le_antisymm (le_iInf₂ fun U _ ↦ le_iInf fun hx ↦ topologicalKrullDimAt_le hx) ?_
  rw [le_topologicalKrullDimAt_iff]
  intro U hU
  obtain ⟨V, hVB, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hU
  exact ((iInf₂_le V hVB).trans (iInf_le _ hxV)).trans (topologicalKrullDim_mono hVU)

/-- The dimension at a point only depends on an open neighbourhood of the point. -/
theorem Topology.IsOpenEmbedding.topologicalKrullDimAt_eq {f : Y → X} (hf : IsOpenEmbedding f)
    (y : Y) : topologicalKrullDimAt X (f y) = topologicalKrullDimAt Y y := by
  refine le_antisymm (le_iInf₂ fun U hU ↦ ?_) (le_iInf₂ fun W hW ↦ ?_)
  · refine (topologicalKrullDimAt_le (U := ⟨f '' U, hf.isOpenMap _ U.2⟩)
      ⟨y, hU, rfl⟩).trans_eq ?_
    exact hf.isEmbedding.topologicalKrullDim_image (U : Set Y)
  · refine (topologicalKrullDimAt_le (U := ⟨f ⁻¹' W, W.2.preimage hf.continuous⟩) hW).trans ?_
    change topologicalKrullDim (f ⁻¹' (W : Set X)) ≤ topologicalKrullDim (W : Set X)
    rw [← hf.isEmbedding.topologicalKrullDim_image]
    exact topologicalKrullDim_mono (Set.image_preimage_subset f _)

theorem Homeomorph.topologicalKrullDimAt_eq (e : Y ≃ₜ X) (y : Y) :
    topologicalKrullDimAt X (e y) = topologicalKrullDimAt Y y :=
  e.isOpenEmbedding.topologicalKrullDimAt_eq y

/-- The dimension of an open subset at a point is the dimension of the space at that point. -/
theorem IsOpen.topologicalKrullDimAt_eq {s : Set X} (hs : IsOpen s) (x : s) :
    topologicalKrullDimAt s x = topologicalKrullDimAt X x :=
  (hs.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq x).symm

/-- Fibres and open embeddings: let `ι : Z → X` be an open embedding and `φ : Z → W`,
`f : X → V` maps with the same fibres along `ι`. Then the fibre of `φ` through `z` and the fibre
of `f` through `ι z` have the same dimension at these points. -/
theorem Topology.IsOpenEmbedding.topologicalKrullDimAt_preimage_singleton {Z W V : Type*}
    [TopologicalSpace Z] {ι : Z → X} (hι : IsOpenEmbedding ι) {φ : Z → W} {f : X → V}
    (h : ∀ z₁ z₂, φ z₁ = φ z₂ ↔ f (ι z₁) = f (ι z₂)) (z : Z) :
    topologicalKrullDimAt (φ ⁻¹' {φ z}) ⟨z, rfl⟩ =
      topologicalKrullDimAt (f ⁻¹' {f (ι z)}) ⟨ι z, rfl⟩ := by
  set F := f ⁻¹' {f (ι z)}
  have hset : φ ⁻¹' {φ z} = ι ⁻¹' F := by
    ext w
    simp [F, h w z]
  let j := (F.restrictPreimage ι) ∘ (Homeomorph.setCongr hset)
  have hj : IsOpenEmbedding j :=
    (Set.restrictPreimage_isOpenEmbedding F hι).comp (Homeomorph.setCongr hset).isOpenEmbedding
  exact (hj.topologicalKrullDimAt_eq ⟨z, rfl⟩).symm

/-- The dimension of `s ∩ t` at a point, for `t` open, is the dimension of `s` there. -/
theorem topologicalKrullDimAt_inter_of_isOpen {s t : Set X} (ht : IsOpen t) (x : ↥(s ∩ t)) :
    topologicalKrullDimAt ↥(s ∩ t) x = topologicalKrullDimAt s ⟨x.1, x.2.1⟩ := by
  have h : IsOpen (Subtype.val ⁻¹' (s ∩ t) : Set s) := by
    have : (Subtype.val ⁻¹' (s ∩ t) : Set s) = Subtype.val ⁻¹' t := by
      ext a
      simp
    rw [this]
    exact ht.preimage continuous_subtype_val
  exact ((IsOpenEmbedding.inclusion Set.inter_subset_left h).topologicalKrullDimAt_eq x).symm

/-- The dimension of a subspace at a point is at most the dimension of the space there. -/
theorem topologicalKrullDimAt_subtype_le (s : Set X) (x : s) :
    topologicalKrullDimAt s x ≤ topologicalKrullDimAt X x := by
  refine le_iInf₂ fun U hU ↦ (topologicalKrullDimAt_le (U := ⟨Subtype.val ⁻¹' (U : Set X),
    U.2.preimage continuous_subtype_val⟩) hU).trans ?_
  change topologicalKrullDim (Subtype.val ⁻¹' (U : Set X) : Set s) ≤ topologicalKrullDim (U : Set X)
  rw [← IsEmbedding.subtypeVal.topologicalKrullDim_image]
  exact topologicalKrullDim_mono (Set.image_preimage_subset _ _)

/-- The Krull dimension of a space is the supremum of its dimensions at its points: a chain of
irreducible closed subsets `Z₀ ⊊ ⋯ ⊊ Zᵣ` induces a chain of the same length in every open
neighbourhood of a point of `Z₀`. -/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt :
    topologicalKrullDim X = ⨆ x, topologicalKrullDimAt X x := by
  refine le_antisymm (iSup_le fun l ↦ ?_)
    (iSup_le fun x ↦ topologicalKrullDimAt_le_topologicalKrullDim x)
  obtain ⟨z, hz⟩ := l.head.2.nonempty
  refine le_iSup_of_le z (le_iInf₂ fun U hU ↦ ?_)
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (Subtype.val : U → X) U.isOpenEmbedding'
  have hmem : ∀ i, (Subtype.val ⁻¹' (l i : Set X) : Set U).Nonempty := fun i ↦
    ⟨⟨z, hU⟩, l.monotone (Fin.zero_le i) hz⟩
  let l' : LTSeries {V : IrreducibleCloseds X | (Subtype.val ⁻¹' (V : Set X) : Set U).Nonempty} :=
    LTSeries.mk l.length (fun i ↦ ⟨l i, hmem i⟩) (fun _ _ h ↦ l.strictMono h)
  exact (l'.map e.symm e.symm.strictMono).length_le_krullDim

/-- If `X` has dimension `n` at every point of a subspace `s`, then `dim s ≤ n`. -/
theorem topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le {s : Set X} {n : WithBot ℕ∞}
    (h : ∀ x ∈ s, topologicalKrullDimAt X x ≤ n) : topologicalKrullDim s ≤ n := by
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  exact iSup_le fun x ↦ (topologicalKrullDimAt_subtype_le s x).trans (h x x.2)

/-- In a noetherian space of dimension `n` at every point, every irreducible component has
dimension `n`. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents [NoetherianSpace X]
    {n : WithBot ℕ∞} (h : ∀ x, topologicalKrullDimAt X x = n) {C : Set X}
    (hC : C ∈ irreducibleComponents X) : topologicalKrullDim C = n := by
  refine le_antisymm (topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le fun x _ ↦
    (h x).le) ?_
  obtain ⟨o, ho, ⟨x, hx⟩, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  rw [← h x]
  exact (topologicalKrullDimAt_le (U := ⟨o, ho⟩) hx).trans (topologicalKrullDim_mono hoC)

end Topology

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The basic open set `D(f)` of `Spec R` has dimension `dim R_f`. -/
theorem topologicalKrullDim_basicOpen (f : R) :
    topologicalKrullDim (basicOpen f) = ringKrullDim (Localization.Away f) := by
  have h := (localization_away_isOpenEmbedding (Localization.Away f) f).isEmbedding
  rw [← topologicalKrullDim_eq_ringKrullDim, h.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    localization_away_comap_range (Localization.Away f) f]
  rfl

/-- The dimension of `Spec R` at `q` is the infimum of `dim R_f` over `f ∉ q`. -/
theorem topologicalKrullDimAt_eq_iInf (q : PrimeSpectrum R) :
    topologicalKrullDimAt (PrimeSpectrum R) q =
      ⨅ (f : R) (_ : f ∉ q.asIdeal), ringKrullDim (Localization.Away f) := by
  rw [topologicalKrullDimAt_eq_iInf_of_isBasis isBasis_basic_opens, iInf_range]
  simp_rw [mem_basicOpen, topologicalKrullDim_basicOpen]

end PrimeSpectrum

namespace Algebra.FiniteType

variable (k : Type*) [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- For an algebra of finite type over a field, localizing at an element does not change
`dim A/P`: if `P` is a prime of `A_f`, then `dim A_f/P = dim A/(P ∩ A)`. -/
theorem coheight_comap_localization_away [Algebra.FiniteType k A] (f : A)
    (P : PrimeSpectrum (Localization.Away f)) :
    coheight (comap (algebraMap A (Localization.Away f)) P) = coheight P := by
  set S := Localization.Away f
  set P₀ := comap (algebraMap A S) P
  let φ : (A ⧸ P₀.asIdeal) →ₐ[k] (S ⧸ P.asIdeal) :=
    Ideal.quotientMapₐ P.asIdeal (IsScalarTower.toAlgHom k A S) le_rfl
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' (H := le_rfl) le_rfl
  have hf : Ideal.Quotient.mk P₀.asIdeal f ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h ↦ P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit f))
  have : IsScalarTower k (A ⧸ P₀.asIdeal) (S ⧸ P.asIdeal) :=
    .of_algebraMap_eq' φ.comp_algebraMap.symm
  have : FaithfulSMul (A ⧸ P₀.asIdeal) (S ⧸ P.asIdeal) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ
  have : Algebra.IsAlgebraic (A ⧸ P₀.asIdeal) (S ⧸ P.asIdeal) := by
    constructor
    intro c
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
    refine ⟨Polynomial.C (Ideal.Quotient.mk _ f ^ n) * Polynomial.X -
      Polynomial.C (Ideal.Quotient.mk _ a), fun h ↦ pow_ne_zero n hf ?_, ?_⟩
    · have h1 := congrArg (Polynomial.coeff · 1) h
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
        Polynomial.coeff_C, one_ne_zero, ite_false, sub_zero, Polynomial.coeff_zero] using h1
    · have : algebraMap (A ⧸ P₀.asIdeal) (S ⧸ P.asIdeal) = φ.toRingHom := rfl
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, this, map_pow]
      change Ideal.Quotient.mk _ (algebraMap A S f) ^ n * Ideal.Quotient.mk _ x -
        Ideal.Quotient.mk _ (algebraMap A S a) = 0
      rw [← map_pow, ← map_mul, ← map_sub, mul_comm, ha, sub_self, map_zero]
  have h := lift_trdeg_add_eq k (A ⧸ P₀.asIdeal) (S ⧸ P.asIdeal)
  rw [trdeg_eq_zero (R := A ⧸ P₀.asIdeal), lift_zero, add_zero, lift_id, lift_id] at h
  rw [← WithBot.coe_inj, coheight_eq_ringKrullDim_quotient, coheight_eq_ringKrullDim_quotient,
    ringKrullDim_eq_trdeg k, ringKrullDim_eq_trdeg k, h]

/-- For an algebra of finite type over a field, `ht P + dim A/P` is unchanged by localizing at
an element. -/
theorem height_add_coheight_comap_localization_away [Algebra.FiniteType k A] (f : A)
    (P : PrimeSpectrum (Localization.Away f)) :
    height (comap (algebraMap A (Localization.Away f)) P) +
      coheight (comap (algebraMap A (Localization.Away f)) P) = height P + coheight P := by
  rw [coheight_comap_localization_away k]
  congr 1
  rw [← height_eq_orderHeight, ← height_eq_orderHeight]
  exact IsLocalization.height_under (Submonoid.powers f) P.asIdeal

/-- In a noetherian ring, given a prime `q` and a submonoid `M` which meets every minimal prime
`p ⊄ q` outside `q`, there is `f ∈ M`, `f ∉ q`, lying in every minimal prime `p ⊄ q`. -/
theorem _root_.Ideal.exists_mem_submonoid_notMem_forall_minimalPrimes [IsNoetherianRing A]
    (q : Ideal A) [q.IsPrime] (M : Submonoid A)
    (hM : ∀ p ∈ minimalPrimes A, ¬ p ≤ q → ∃ a ∈ M, a ∈ p ∧ a ∉ q) :
    ∃ f ∈ M, f ∉ q ∧ ∀ p ∈ minimalPrimes A, ¬ p ≤ q → f ∈ p := by
  classical
  set T := {p ∈ minimalPrimes A | ¬ p ≤ q}
  have hT : T.Finite := (minimalPrimes.finite_of_isNoetherianRing A).subset fun _ h ↦ h.1
  choose! a haM haT haq using fun p (hp : p ∈ T) ↦ hM p hp.1 hp.2
  refine ⟨∏ p ∈ hT.toFinset, a p, Submonoid.prod_mem _ fun p hp ↦ haM p (hT.mem_toFinset.mp hp),
    ?_, fun p hp hpq ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpq⟩
    exact haq p (hT.mem_toFinset.mp hp) hpq
  · exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (hT.mem_toFinset.mpr ⟨hp, hpq⟩))
      (haT p ⟨hp, hpq⟩)

/-- For `A` of finite type over a field and `f ∉ q`, `ht q + dim A/q ≤ dim A_f`. -/
theorem height_add_coheight_le_ringKrullDim_localization_away [Algebra.FiniteType k A]
    (q : PrimeSpectrum A) {f : A} (hf : f ∉ q.asIdeal) :
    ((height q + coheight q : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (Localization.Away f) := by
  obtain ⟨P, hP⟩ : q ∈ Set.range (comap (algebraMap A (Localization.Away f))) := by
    rw [localization_away_comap_range (Localization.Away f) f]
    exact hf
  rw [← hP, height_add_coheight_comap_localization_away k]
  exact Order.height_add_coheight_le_krullDim P

/-- For `A` of finite type over a field, if `f ∉ q` lies in every minimal prime not contained in
`q`, then `dim A_f ≤ ht q + dim A/q`. -/
theorem ringKrullDim_localization_away_le [Algebra.FiniteType k A] (q : PrimeSpectrum A) {f : A}
    (hfq : f ∉ q.asIdeal) (hf : ∀ p ∈ minimalPrimes A, ¬ p ≤ q.asIdeal → f ∈ p) :
    ringKrullDim (Localization.Away f) ≤ ((height q + coheight q : ℕ∞) : WithBot ℕ∞) := by
  have hmin : ∀ p : PrimeSpectrum A, IsMin p → p.asIdeal ∈ minimalPrimes A := fun p hp ↦
    ⟨⟨p.2, bot_le⟩, fun J hJ hJp ↦ hp (show (⟨J, hJ.1⟩ : PrimeSpectrum A) ≤ p from hJp)⟩
  obtain ⟨P₁, -⟩ : q ∈ Set.range (comap (algebraMap A (Localization.Away f))) := by
    rw [localization_away_comap_range (Localization.Away f) f]
    exact hfq
  have : Nonempty (PrimeSpectrum (Localization.Away f)) := ⟨P₁⟩
  rw [ringKrullDim, krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  refine iSup_le fun P ↦ ?_
  rw [← height_add_coheight_comap_localization_away k,
    height_add_coheight_eq_iSup k (comap (algebraMap A (Localization.Away f)) P),
    height_add_coheight_eq_iSup k q]
  refine iSup₂_le fun p hp ↦ iSup_le fun hpP ↦ le_iSup₂_of_le p hp (le_iSup_of_le ?_ le_rfl)
  by_contra hpq
  have hfP : f ∉ (comap (algebraMap A (Localization.Away f)) P).asIdeal := fun h ↦
    P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit f))
  exact hfP (hpP (hf _ (hmin p hp) hpq))

/-- For `A` of finite type over a field and a prime `q`, and a submonoid `M` of `A` meeting every
minimal prime `p ⊄ q` outside `q`, there is `f ∈ M`, `f ∉ q`, with `dim A_f = ht q + dim A/q`. -/
theorem exists_mem_ringKrullDim_localization_away_eq [Algebra.FiniteType k A]
    (q : PrimeSpectrum A) (M : Submonoid A)
    (hM : ∀ p ∈ minimalPrimes A, ¬ p ≤ q.asIdeal → ∃ a ∈ M, a ∈ p ∧ a ∉ q.asIdeal) :
    ∃ f ∈ M, f ∉ q.asIdeal ∧
      ringKrullDim (Localization.Away f) = ((height q + coheight q : ℕ∞) : WithBot ℕ∞) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨f, hfM, hfq, hf⟩ := q.asIdeal.exists_mem_submonoid_notMem_forall_minimalPrimes M hM
  exact ⟨f, hfM, hfq, le_antisymm (ringKrullDim_localization_away_le k q hfq hf)
    (height_add_coheight_le_ringKrullDim_localization_away k q hfq)⟩

/-- For `A` of finite type over a field and a prime `q`, the infimum of `dim A_f` over `f ∉ q`
is `ht q + dim A/q`. -/
theorem iInf_ringKrullDim_localization_away [Algebra.FiniteType k A] (q : PrimeSpectrum A) :
    ⨅ (f : A) (_ : f ∉ q.asIdeal), ringKrullDim (Localization.Away f) =
      ((height q + coheight q : ℕ∞) : WithBot ℕ∞) := by
  refine le_antisymm ?_ (le_iInf₂ fun f hf ↦
    height_add_coheight_le_ringKrullDim_localization_away k q hf)
  obtain ⟨f, -, hfq, hf⟩ := exists_mem_ringKrullDim_localization_away_eq k q ⊤
    fun p _ hpq ↦ (SetLike.not_le_iff_exists.mp hpq).imp fun a ha ↦ ⟨trivial, ha⟩
  exact (iInf₂_le f hfq).trans hf.le

/-- For `A` of finite type over a field, the dimension of `Spec A` at `q` is `ht q + dim A/q`
(EGA IV §5.2). -/
theorem topologicalKrullDimAt_eq [Algebra.FiniteType k A] (q : PrimeSpectrum A) :
    topologicalKrullDimAt (PrimeSpectrum A) q = ((height q + coheight q : ℕ∞) : WithBot ℕ∞) := by
  rw [topologicalKrullDimAt_eq_iInf, iInf_ringKrullDim_localization_away k]

/-- For `A` of finite type over a field, the dimension of `Spec A` at `q` is the maximal
dimension of an irreducible component `V(p)` (`p` a minimal prime) through `q`
(EGA IV §5.2). -/
theorem topologicalKrullDimAt_eq_iSup [Algebra.FiniteType k A] (q : PrimeSpectrum A) :
    topologicalKrullDimAt (PrimeSpectrum A) q =
      ((⨆ (p : PrimeSpectrum A) (_ : IsMin p) (_ : p ≤ q), coheight p : ℕ∞) : WithBot ℕ∞) := by
  rw [topologicalKrullDimAt_eq k, height_add_coheight_eq_iSup k]

/-- **`dim_x X = dim 𝒪_x + trdeg_k κ(x)`** (EGA IV §5.2), affine form:
for a prime `q` of an algebra `A` of finite type over a field `k`,
`dim_q (Spec A) = ht q + trdeg_k κ(q)`. -/
theorem topologicalKrullDimAt_eq_height_add_trdeg [Algebra.FiniteType k A] (q : Ideal A)
    [q.IsPrime] : topologicalKrullDimAt (PrimeSpectrum A) ⟨q, ‹_›⟩ =
      ((q.height + (trdeg k q.ResidueField).toENat : ℕ∞) : WithBot ℕ∞) := by
  rw [topologicalKrullDimAt_eq_iSup k, height_add_trdeg_residueField_eq_iSup k]
  rfl

/-- **`dim_x X = dim 𝒪_x + trdeg_k κ(x)`**, with the local ring `A_q`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_add_trdeg [Algebra.FiniteType k A] (q : Ideal A)
    [q.IsPrime] : topologicalKrullDimAt (PrimeSpectrum A) ⟨q, ‹_›⟩ =
      ringKrullDim (Localization.AtPrime q) + (trdeg k q.ResidueField).toENat := by
  rw [topologicalKrullDimAt_eq_height_add_trdeg k,
    IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), WithBot.coe_add]

/-- The spectrum of a domain of finite type over a field has the same dimension `dim A` at every
point. -/
theorem topologicalKrullDimAt_eq_ringKrullDim [IsDomain A] [Algebra.FiniteType k A]
    (q : PrimeSpectrum A) : topologicalKrullDimAt (PrimeSpectrum A) q = ringKrullDim A := by
  rw [topologicalKrullDimAt_eq k, height_add_coheight_eq k]

end Algebra.FiniteType
