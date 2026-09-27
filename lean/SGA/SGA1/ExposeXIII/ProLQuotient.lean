/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# SGA 1, Exposé XIII, 2.10 and §4: maximal pro-`L` quotients and the groups `π'₁`

For a set `L` of primes, XIII.2.10 defines `π₁^L(U, a)` as the projective limit of the finite
quotients of `π₁(U, a)` whose orders have all their prime factors in `L`. Here this is
`ProLQuotient L G = G ⧸ proLKernel L G`, where `proLKernel L G` is the intersection of the open
normal subgroups with such quotients.

XIII.4.0 considers `h' : π₁(X_s̄) → π₁(X)` and `h : π₁(X) → π₁(S)`, the kernel `K` of `h`, the
kernel `N` of `K → K^L`, and `π'₁(X) = π₁(X) ⧸ N`. We prove that `N` is normal, construct
`u : π₁^L(X_s̄) → π'₁(X)` and `v : π'₁(X) → π₁(S)` with `vu = 1`, and prove the group-theoretic
part of XIII.4.1–4.6:

* exactness of `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` in terms of `h`, `h'` (the first step of the
  proof of XIII.4.1), and the fact that it follows from the exactness of
  `π₁(X_s̄) → π₁(X) → π₁(S) → 1` (so the first part of XIII.4.4 follows from X.1.4);
* the covering criterion of the proof of XIII.4.1 (`ker_le_range_sup_primeKernel_iff`): the
  exactness holds iff every Galois covering with `L`-group of some `X ×_S S'` which is
  connected over `X̃` stays connected over `X_s̄`; this uses a compactness argument;
* injectivity of `u` (the first step of the proof of XIII.4.3) and its covering criterion
  (`injective_proLToPrimeQuotient_iff_exists_openSubgroup`);
* the semidirect product decomposition XIII.4.5 given a section, and the algebraic content of
  XIII.4.5.1 (crossed homomorphisms trivial on `π₁(S)` are `π₁(S)`-equivariant homomorphisms);
* the last step of the proof of the Künneth formula XIII.4.6.

The groups are topological groups (profinite where compactness is needed); the corresponding
statements for fundamental groups of Galois categories are in
`SGA.SGA1.ExposeXIII.HomotopySequence`, and for schemes in
`SGA.SGA1.ExposeXIII.SchemeFundamentalGroup`.
-/

namespace SGA.SGA1.ExposeXIII

open scoped Pointwise

section LGroup

variable (L : Set ℕ)

/-- XIII.2.10: a finite group is an `L`-group if every prime dividing its order lies in `L`. -/
def IsLGroup (G : Type*) [Group G] : Prop :=
  Finite G ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ∈ L

/-- A subgroup has *`L`-index* if its index is finite with all prime factors in `L`; for a
normal subgroup this says that the quotient is an `L`-group (`isLGroup_quotient_iff`). -/
def IsLIndex {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  N.index ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ N.index → p ∈ L

variable {L} {G H : Type*} [Group G] [Group H]

lemma isLGroup_quotient_iff (N : Subgroup G) [N.Normal] :
    IsLGroup L (G ⧸ N) ↔ IsLIndex L N := by
  rw [IsLGroup, IsLIndex, Subgroup.index_ne_zero_iff_finite, Subgroup.index_eq_card]

lemma IsLGroup.of_injective (hH : IsLGroup L H) (f : G →* H) (hf : Function.Injective f) :
    IsLGroup L G := by
  have := hH.1
  exact ⟨Finite.of_injective f hf, fun p hp hdvd ↦
    hH.2 p hp (hdvd.trans (Subgroup.card_dvd_of_injective f hf))⟩

lemma IsLGroup.of_surjective (hG : IsLGroup L G) (f : G →* H) (hf : Function.Surjective f) :
    IsLGroup L H := by
  have := hG.1
  exact ⟨Finite.of_surjective f hf, fun p hp hdvd ↦
    hG.2 p hp (hdvd.trans (Subgroup.card_dvd_of_surjective f hf))⟩

lemma IsLGroup.prod (hG : IsLGroup L G) (hH : IsLGroup L H) : IsLGroup L (G × H) := by
  have := hG.1
  have := hH.1
  refine ⟨inferInstance, fun p hp hdvd ↦ ?_⟩
  rw [Nat.card_prod] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  exacts [hG.2 p hp h, hH.2 p hp h]

lemma IsLIndex.of_dvd {N : Subgroup G} {M : Subgroup H} (hN : IsLIndex L N) (hM : M.index ≠ 0)
    (hd : M.index ∣ N.index) : IsLIndex L M :=
  ⟨hM, fun p hp hpM ↦ hN.2 p hp (hpM.trans hd)⟩

lemma IsLIndex.comap {N : Subgroup G} [N.Normal] (hN : IsLIndex L N) (f : H →* G) :
    IsLIndex L (N.comap f) := by
  have hd : (N.comap f).index ∣ N.index := by
    rw [Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal N f.range
  exact hN.of_dvd (fun h0 ↦ hN.1 (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))) hd

lemma IsLIndex.inf {N₁ N₂ : Subgroup G} [N₂.Normal] (h₁ : IsLIndex L N₁) (h₂ : IsLIndex L N₂) :
    IsLIndex L (N₁ ⊓ N₂) := by
  have heq : (N₁ ⊓ N₂).index = N₂.relIndex N₁ * N₁.index := by
    rw [← Subgroup.relIndex_mul_index inf_le_left, inf_comm, Subgroup.inf_relIndex_right]
  have hd : N₂.relIndex N₁ ∣ N₂.index := Subgroup.relIndex_dvd_index_of_normal N₂ N₁
  refine ⟨?_, fun p hp hdvd ↦ ?_⟩
  · rw [heq]
    exact mul_ne_zero (fun h0 ↦ h₂.1 (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))) h₁.1
  · rw [heq] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    exacts [h₂.2 p hp (h.trans hd), h₁.2 p hp h]

end LGroup

section ProL

variable (L : Set ℕ) (G : Type*) [Group G] [TopologicalSpace G]

/-- The kernel of the maximal pro-`L` quotient of a topological group: the intersection of the
open normal subgroups `N` such that `G ⧸ N` is a finite `L`-group. -/
def proLKernel : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N.Normal ∧ IsOpen (N : Set G) ∧ IsLIndex L N), N

/-- XIII.2.10: `π₁^L`, the maximal pro-`L` quotient of `G`, the projective limit of the finite
quotients of `G` whose orders have all their prime factors in `L`. -/
abbrev ProLQuotient := G ⧸ proLKernel L G

instance : (proLKernel L G).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ Subgroup.normal_iInf_normal fun h ↦ h.1

variable {L G}

lemma mem_proLKernel {g : G} :
    g ∈ proLKernel L G ↔
      ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → IsLIndex L N → g ∈ N := by
  simp only [proLKernel, Subgroup.mem_iInf]
  exact ⟨fun h N hN ho hL ↦ h N ⟨hN, ho, hL⟩, fun h N hN ↦ h N hN.1 hN.2.1 hN.2.2⟩

lemma proLKernel_le {N : Subgroup G} (hN : N.Normal) (ho : IsOpen (N : Set G))
    (hL : IsLIndex L N) : proLKernel L G ≤ N :=
  fun _ hg ↦ mem_proLKernel.mp hg N hN ho hL

lemma isClosed_proLKernel [IsTopologicalGroup G] : IsClosed (proLKernel L G : Set G) := by
  simp only [proLKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun N ↦ isClosed_iInter fun h ↦ Subgroup.isClosed_of_isOpen N h.2.1

/-- Continuous homomorphisms to finite discrete `L`-groups factor through the maximal pro-`L`
quotient. -/
theorem proLKernel_le_ker {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (hQ : IsLGroup L Q) (φ : G →* Q) (hφ : Continuous φ) : proLKernel L G ≤ φ.ker := by
  have := hQ.1
  refine proLKernel_le (MonoidHom.normal_ker φ) ?_ ⟨?_, fun p hp hdvd ↦ hQ.2 p hp ?_⟩
  · change IsOpen (φ ⁻¹' {1})
    exact (isOpen_discrete _).preimage hφ
  · rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · rw [Subgroup.index_ker] at hdvd
    exact hdvd.trans (Subgroup.card_subgroup_dvd_card _)

variable (L) {H : Type*} [Group H] [TopologicalSpace H]

/-- Functoriality of the maximal pro-`L` quotient. -/
theorem proLKernel_le_comap (φ : G →* H) (hφ : Continuous φ) :
    proLKernel L G ≤ (proLKernel L H).comap φ := fun _ hg ↦
  mem_proLKernel.mpr fun N hN ho hL ↦
    mem_proLKernel.mp hg (N.comap φ) (hN.comap φ) (ho.preimage hφ) (hL.comap φ)

/-- The homomorphism of maximal pro-`L` quotients induced by a continuous homomorphism. -/
def proLMap (φ : G →* H) (hφ : Continuous φ) : ProLQuotient L G →* ProLQuotient L H :=
  QuotientGroup.map _ _ φ (proLKernel_le_comap L φ hφ)

/-- XIII.4.0: if `K` is a normal subgroup of `G`, the kernel of `K → K^L` is normal in `G`
(it is invariant under the continuous automorphisms of `K`). -/
theorem normal_map_proLKernel [IsTopologicalGroup G] (K : Subgroup G) [K.Normal] :
    ((proLKernel L K).map K.subtype).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ g
  let c : K →* K := (MulAut.conjNormal g).toMonoidHom
  have hc : Continuous c := by
    apply continuous_induced_rng.2
    have : (Subtype.val ∘ c) = fun k : K ↦ g * k * g⁻¹ := by
      funext k
      exact MulAut.conjNormal_apply g k
    rw [this]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact ⟨c k, proLKernel_le_comap L c hc hk, MulAut.conjNormal_apply g k⟩

/-- The kernel of the maximal pro-`L` quotient of a product contains the product of the kernels. -/
theorem prod_proLKernel_le {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] :
    (proLKernel L G).prod (proLKernel L H) ≤ proLKernel L (G × H) := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  refine mem_proLKernel.mpr fun N hN ho hL ↦ ?_
  have hinl : IsOpen ((N.comap (MonoidHom.inl G H) : Subgroup G) : Set G) :=
    ho.preimage (continuous_id.prodMk continuous_const : Continuous fun a : G ↦ (a, (1 : H)))
  have hinr : IsOpen ((N.comap (MonoidHom.inr G H) : Subgroup H) : Set H) :=
    ho.preimage (continuous_const.prodMk continuous_id : Continuous fun b : H ↦ ((1 : G), b))
  have h₁ : a ∈ N.comap (MonoidHom.inl G H) :=
    proLKernel_le (hN.comap _) hinl (hL.comap _) ha
  have h₂ : b ∈ N.comap (MonoidHom.inr G H) :=
    proLKernel_le (hN.comap _) hinr (hL.comap _) hb
  have : ((a, b) : G × H) = (a, 1) * (1, b) := by simp
  rw [this]
  exact N.mul_mem h₁ h₂

/-- A continuous bijective homomorphism which is an open map identifies the kernels of the
maximal pro-`L` quotients. -/
theorem comap_proLKernel_le_of_isOpenMap {H : Type*} [Group H] [TopologicalSpace H]
    (φ : G →* H) (hφ : Function.Bijective φ) (ho : IsOpenMap φ) :
    (proLKernel L H).comap φ ≤ proLKernel L G := by
  intro x hx
  refine mem_proLKernel.mpr fun N hN hNo hL ↦ ?_
  have hN' : (N.map φ).Normal := hN.map φ hφ.2
  have hLN : IsLIndex L (N.map φ) := by
    rw [IsLIndex, Subgroup.index_map_of_bijective hφ]
    exact hL
  have := proLKernel_le hN' (ho _ hNo) hLN hx
  obtain ⟨y, hy, hyx⟩ := this
  rwa [hφ.1 hyx] at hy

/-- XIII.4.6, last step, for maximal pro-`L` quotients: if `(p, q) : Z → X × Y` is a continuous
bijection of compact groups (`X`, `Y` Hausdorff), then the induced map
`Z^L → X^L × Y^L` is bijective. -/
theorem bijective_proLMap_prod {Z X Y : Type*} [Group Z] [Group X] [Group Y]
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X]
    [IsTopologicalGroup Y] [CompactSpace Z] [T2Space X] [T2Space Y] (p : Z →* X) (q : Z →* Y)
    (hp : Continuous p) (hq : Continuous q) (hpq : Function.Bijective (p.prod q)) :
    Function.Bijective ((proLMap L p hp).prod (proLMap L q hq)) := by
  have hc : Continuous (p.prod q) := hp.prodMk hq
  have hopen : IsOpenMap (p.prod q) := by
    intro U hU
    have hcl : IsClosed ((p.prod q) '' Uᶜ) := hc.isClosedMap _ hU.isClosed_compl
    have : (p.prod q) '' U = ((p.prod q) '' Uᶜ)ᶜ := by
      rw [Set.image_compl_eq hpq]
      simp
    rw [this]
    exact hcl.isOpen_compl
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hz
    obtain ⟨h₁, h₂⟩ := hz
    have h₁ : p z ∈ proLKernel L X := (QuotientGroup.eq_one_iff _).mp h₁
    have h₂ : q z ∈ proLKernel L Y := (QuotientGroup.eq_one_iff _).mp h₂
    have : z ∈ proLKernel L Z :=
      comap_proLKernel_le_of_isOpenMap L (p.prod q) hpq hopen
        (prod_proLKernel_le L ⟨h₁, h₂⟩)
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact this
  · rintro ⟨x, y⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨z, hz⟩ := hpq.2 (x, y)
    refine ⟨z, ?_⟩
    simp only [MonoidHom.prod_apply, Prod.mk.injEq] at hz ⊢
    exact ⟨congrArg QuotientGroup.mk hz.1, congrArg QuotientGroup.mk hz.2⟩

end ProL

section PrimeQuotient

variable (L : Set ℕ) {G'' G' G : Type*} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- XIII.4.0: for `h : π₁(X) → π₁(S)` with kernel `K`, the subgroup `N` of `π₁(X)`, the kernel
of `K → K^L`. -/
def primeKernel (h : G' →* G) : Subgroup G' :=
  (proLKernel L h.ker).map h.ker.subtype

instance (h : G' →* G) : (primeKernel L h).Normal :=
  normal_map_proLKernel L h.ker

omit [IsTopologicalGroup G'] in
lemma primeKernel_le_ker (h : G' →* G) : primeKernel L h ≤ h.ker :=
  Subgroup.map_subtype_le _

/-- XIII.4.0: `π'₁(X) = π₁(X) ⧸ N`. -/
abbrev PrimeQuotient (h : G' →* G) := G' ⧸ primeKernel L h

/-- XIII.4.0: the morphism `v : π'₁(X) → π₁(S)`. -/
def primeQuotientLift (h : G' →* G) : PrimeQuotient L h →* G :=
  QuotientGroup.lift _ h (primeKernel_le_ker L h)

variable (h' : G'' →* G') (h : G' →* G) (hh' : Continuous h') (hcomp : h.comp h' = 1)

omit [IsTopologicalGroup G'] in
include hh' hcomp in
lemma proLKernel_le_comap_primeKernel :
    proLKernel L G'' ≤ (primeKernel L h).comap h' := by
  have hmem (x : G'') : h' x ∈ h.ker := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp, MonoidHom.one_apply]
  let k : G'' →* h.ker := h'.codRestrict h.ker hmem
  have hk : Continuous k := hh'.subtype_mk _
  exact fun x hx ↦ ⟨k x, proLKernel_le_comap L k hk hx, rfl⟩

/-- XIII.4.0: the morphism `u : π₁^L(X_s̄) → π'₁(X)`. -/
def proLToPrimeQuotient : ProLQuotient L G'' →* PrimeQuotient L h :=
  QuotientGroup.map _ _ h' (proLKernel_le_comap_primeKernel L h' h hh' hcomp)

/-- XIII.4.0: `vu = 1`. -/
theorem primeQuotientLift_comp_proLToPrimeQuotient :
    (primeQuotientLift L h).comp (proLToPrimeQuotient L h' h hh' hcomp) = 1 := by
  ext x
  change h (h' x) = 1
  rw [← MonoidHom.comp_apply, hcomp, MonoidHom.one_apply]

lemma range_proLToPrimeQuotient :
    (proLToPrimeQuotient L h' h hh' hcomp).range =
      h'.range.map (QuotientGroup.mk' (primeKernel L h)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨h' x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

lemma surjective_primeQuotientLift_iff :
    Function.Surjective (primeQuotientLift L h) ↔ Function.Surjective h := by
  refine ⟨fun hs g ↦ ?_, fun hs g ↦ ?_⟩
  · obtain ⟨q, rfl⟩ := hs g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  · obtain ⟨x, rfl⟩ := hs g
    exact ⟨x, rfl⟩

/-- XIII.4.1, formal part: the sequence `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact iff
`π₁(X) → π₁(S)` is surjective and `K = ker(π₁(X) → π₁(S))` is generated by the image of
`π₁(X_s̄)` and `N`, i.e. `π₁^L(X_s̄) → K^L` is surjective. -/
theorem exact_primeQuotient_iff :
    (Function.Surjective (primeQuotientLift L h) ∧
        (proLToPrimeQuotient L h' h hh' hcomp).range = (primeQuotientLift L h).ker) ↔
      (Function.Surjective h ∧ h.ker ≤ h'.range ⊔ primeKernel L h) := by
  rw [surjective_primeQuotientLift_iff, range_proLToPrimeQuotient, primeQuotientLift,
    QuotientGroup.ker_lift]
  refine and_congr Iff.rfl ⟨fun heq ↦ ?_, fun hle ↦ ?_⟩
  · have := congrArg (Subgroup.comap (QuotientGroup.mk' (primeKernel L h))) heq
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [this]
    exact le_sup_left
  · have hrange : h'.range ≤ h.ker := (MonoidHom.range_le_ker_iff _ _).mpr hcomp
    have heq : h'.range ⊔ primeKernel L h = h.ker ⊔ primeKernel L h :=
      le_antisymm (sup_le_sup_right hrange _)
        (sup_le hle le_sup_right)
    rw [← QuotientGroup.ker_mk' (primeKernel L h), ← Subgroup.comap_map_eq,
      ← Subgroup.comap_map_eq] at heq
    exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _) heq

/-- XIII.4.1 and XIII.4.4 (group-theoretic part): the exactness of
`π₁(X_s̄) → π₁(X) → π₁(S) → 1` (X.1.4) implies that of `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1`. -/
theorem exact_primeQuotient_of_exact (hs : Function.Surjective h) (hex : h'.range = h.ker) :
    Function.Surjective (primeQuotientLift L h) ∧
      (proLToPrimeQuotient L h' h hh' hcomp).range = (primeQuotientLift L h).ker :=
  (exact_primeQuotient_iff L h' h hh' hcomp).mpr ⟨hs, hex ▸ le_sup_left⟩

/-- XIII.4.3, formal part: `u : π₁^L(X_s̄) → π'₁(X)` is injective iff the preimage of `N` in
`π₁(X_s̄)` is contained in the kernel of `π₁(X_s̄) → π₁^L(X_s̄)`. -/
theorem injective_proLToPrimeQuotient_iff :
    Function.Injective (proLToPrimeQuotient L h' h hh' hcomp) ↔
      (primeKernel L h).comap h' ≤ proLKernel L G'' := by
  rw [← MonoidHom.ker_eq_bot_iff, proLToPrimeQuotient, QuotientGroup.ker_map,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

end PrimeQuotient

section Criteria

lemma mem_sup_normal_iff {G' : Type*} [Group G'] (H N : Subgroup G') [N.Normal] {x : G'} :
    x ∈ H ⊔ N ↔ ∃ y ∈ H, ∃ z ∈ N, y * z = x := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  rfl

/-- The second isomorphism theorem in terms of indices: if `W` is normal in `V`, `K ≤ V` and
`K W = V`, then `W ∩ K` has the same index in `K` as `W` in `V`. -/
lemma relIndex_map_subtype_eq_index {G' : Type*} [Group G'] {V K : Subgroup G'} (hKV : K ≤ V)
    (W : Subgroup V) [W.Normal] (hsup : K.subgroupOf V ⊔ W = ⊤) :
    (W.map V.subtype).relIndex K = W.index := by
  have hW : (W.map V.subtype).subgroupOf V = W := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← Subgroup.relIndex_subgroupOf hKV, hW, ← Subgroup.relIndex_sup_right, hsup,
    Subgroup.relIndex_top_right]

variable (L : Set ℕ) {G'' G' G : Type*} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [TopologicalSpace G]
  [IsTopologicalGroup G'] [CompactSpace G''] [CompactSpace G'] [TotallyDisconnectedSpace G']
  [T2Space G'] [T1Space G]
  (h' : G'' →* G') (h : G' →* G) (hh' : Continuous h') (hh : Continuous h) (hcomp : h.comp h' = 1)

omit [CompactSpace G'] [TotallyDisconnectedSpace G'] [T2Space G'] in
include hh in
lemma isClosed_primeKernel : IsClosed (primeKernel L h : Set G') := by
  have hKc : IsClosed (h.ker : Set G') := isClosed_singleton.preimage hh
  rw [primeKernel, Subgroup.coe_map]
  have := isClosed_proLKernel (L := L) (G := h.ker)
  exact hKc.isClosedEmbedding_subtypeVal.isClosedMap _ this

omit [TopologicalSpace G''] [TopologicalSpace G'] [TopologicalSpace G] [IsTopologicalGroup G']
  [CompactSpace G''] [CompactSpace G'] [TotallyDisconnectedSpace G'] [T2Space G'] [T1Space G] in
include hcomp in
lemma range_le_ker_of_comp_eq_one : h'.range ≤ h.ker :=
  (MonoidHom.range_le_ker_iff _ _).mpr hcomp

include hh hh' in
/-- XIII.4.1, the criterion of its proof: `π₁^L(X_s̄) → K^L` is surjective (i.e. `K` lies in the
subgroup generated by the image of `π₁(X_s̄)` and `N`) iff, for every open subgroup `V ⊇ K` of
`π₁(X)` (an étale covering `X' = X ×_S S'` with `S'` an étale covering of `S`) and every open
normal subgroup `W` of `V` with `V ⧸ W` an `L`-group (a Galois covering `Q` of `X'` with group an
`L`-group), if `K` maps onto `V ⧸ W` (`Q ×_{X'} X̃` is connected) then so does `π₁(X_s̄)`
(`Q|X_s̄` is connected). -/
theorem ker_le_range_sup_primeKernel_iff :
    h.ker ≤ h'.range ⊔ primeKernel L h ↔
      ∀ (V : Subgroup G') (_ : IsOpen (V : Set G')) (hK : h.ker ≤ V) (W : Subgroup V) [W.Normal],
        IsOpen (W : Set V) → IsLIndex L W →
        Function.Surjective ((QuotientGroup.mk' W).comp (Subgroup.inclusion hK)) →
        Function.Surjective ((QuotientGroup.mk' W).comp
          (h'.codRestrict V fun x ↦ hK (range_le_ker_of_comp_eq_one h' h hcomp ⟨x, rfl⟩))) := by
  constructor
  · intro hle V hV hK W _ hWo hWL hsK q
    have hsup : h.ker.subgroupOf V ⊔ W = ⊤ := by
      rw [eq_top_iff]
      intro v _
      obtain ⟨k, hk⟩ := hsK (v : V ⧸ W)
      have hw : (Subgroup.inclusion hK k)⁻¹ * v ∈ W := QuotientGroup.eq.mp hk
      have hv : v = Subgroup.inclusion hK k * ((Subgroup.inclusion hK k)⁻¹ * v) := by group
      rw [hv]
      exact Subgroup.mul_mem_sup (by simp [Subgroup.mem_subgroupOf]) hw
    let M : Subgroup h.ker := (W.map V.subtype).subgroupOf h.ker
    have hMn : M.Normal := ⟨fun m hm k ↦ by
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨w, hw, hwm⟩ := hm
      have hwm' : (w : G') = m := hwm
      refine ⟨Subgroup.inclusion hK k * w * (Subgroup.inclusion hK k)⁻¹,
        ‹W.Normal›.conj_mem w hw _, ?_⟩
      simp [hwm']⟩
    have hMo : IsOpen (M : Set h.ker) := by
      have : IsOpen ((W.map V.subtype : Subgroup G') : Set G') := by
        rw [Subgroup.coe_map]
        exact hV.isOpenEmbedding_subtypeVal.isOpenMap _ hWo
      exact this.preimage continuous_subtype_val
    have hML : IsLIndex L M := by
      have : M.index = W.index := relIndex_map_subtype_eq_index hK W hsup
      rw [IsLIndex, this]
      exact hWL
    have hNW : primeKernel L h ≤ W.map V.subtype := by
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (proLKernel_le hMn hMo hML hm)
    obtain ⟨k, rfl⟩ := hsK q
    obtain ⟨_, ⟨x, rfl⟩, n, hn, hxn⟩ := (mem_sup_normal_iff _ _).mp (hle k.2)
    obtain ⟨w, hw, rfl⟩ := hNW hn
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hkw : Subgroup.inclusion hK k =
        h'.codRestrict V (fun x ↦ hK (range_le_ker_of_comp_eq_one h' h hcomp ⟨x, rfl⟩)) x * w :=
      Subtype.ext (by simp [← hxn])
    rw [hkw, inv_mul_cancel_left]
    exact hw
  · intro hcrit
    -- Step 1: for each open normal `M ⊴ K` with `K ⧸ M` an `L`-group, `K ⊆ h'(G'') M`.
    have step1 : ∀ M : Subgroup h.ker, M.Normal → IsOpen (M : Set h.ker) → IsLIndex L M →
        ∀ k : h.ker, ∃ x : G'', (h' x)⁻¹ * k ∈ M.map h.ker.subtype := by
      intro M hMn hMo hML k
      obtain ⟨O, hOo, hOM⟩ := isOpen_induced_iff.mp hMo
      have h1O : (1 : G') ∈ O := by
        have : (1 : h.ker) ∈ (M : Set h.ker) := M.one_mem
        rw [← hOM] at this
        exact this
      obtain ⟨U₀, hU₀⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
      have hU₀n : (U₀ : Subgroup G').Normal := U₀.isNormal'
      set M' : Subgroup G' := M.map h.ker.subtype with hM'
      have hU₀K : ∀ u ∈ (U₀ : Subgroup G'), u ∈ h.ker → u ∈ M' := by
        intro u hu huK
        have : (⟨u, huK⟩ : h.ker) ∈ (M : Set h.ker) := by
          rw [← hOM]
          exact hU₀ hu
        exact ⟨_, this, rfl⟩
      set V : Subgroup G' := h.ker ⊔ U₀ with hVdef
      have hVo : IsOpen (V : Set G') := Subgroup.isOpen_mono le_sup_right U₀.isOpen'
      have hK : h.ker ≤ V := le_sup_left
      set Wg : Subgroup G' := M' ⊔ U₀ with hWgdef
      have hWgV : Wg ≤ V := sup_le_sup_right (Subgroup.map_subtype_le M) _
      let W : Subgroup V := Wg.subgroupOf V
      have hWn : W.Normal := by
        rw [Subgroup.normal_subgroupOf_iff hWgV]
        intro w v hw hv
        obtain ⟨m, hm, u, hu, rfl⟩ := (mem_sup_normal_iff _ _).mp hw
        obtain ⟨k₀, hk₀, u₀, hu₀, rfl⟩ := (mem_sup_normal_iff _ _).mp hv
        obtain ⟨m₁, hm₁, rfl⟩ := hm
        have e : k₀ * u₀ * (h.ker.subtype m₁ * u) * (k₀ * u₀)⁻¹ =
            (k₀ * m₁ * k₀⁻¹) * (k₀ * ((m₁ : G')⁻¹ * u₀ * m₁ * u₀⁻¹) * k₀⁻¹) *
              (k₀ * (u₀ * u * u₀⁻¹) * k₀⁻¹) := by
          simp only [Subgroup.coe_subtype]
          group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
          (Subgroup.mem_sup_right ?_)) (Subgroup.mem_sup_right ?_)
        · exact ⟨⟨k₀, hk₀⟩ * m₁ * ⟨k₀, hk₀⟩⁻¹, hMn.conj_mem m₁ hm₁ ⟨k₀, hk₀⟩, rfl⟩
        · have h₁ : (m₁ : G')⁻¹ * u₀ * m₁ ∈ (U₀ : Subgroup G') := by
            simpa using hU₀n.conj_mem u₀ hu₀ (m₁⁻¹ : G')
          exact hU₀n.conj_mem _ (Subgroup.mul_mem _ h₁ (Subgroup.inv_mem _ hu₀)) k₀
        · exact hU₀n.conj_mem _ (hU₀n.conj_mem u hu u₀) k₀
      have hWo : IsOpen (W : Set V) :=
        (Subgroup.isOpen_mono (le_sup_right : (U₀ : Subgroup G') ≤ Wg)
          U₀.isOpen').preimage continuous_subtype_val
      have hsup : h.ker.subgroupOf V ⊔ W = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨v, hv⟩ -
        obtain ⟨k₀, hk₀, u₀, hu₀, rfl⟩ := (mem_sup_normal_iff _ _).mp hv
        have : (⟨k₀ * u₀, hv⟩ : V) = ⟨k₀, hK hk₀⟩ * ⟨u₀, le_sup_right (a := h.ker) hu₀⟩ := rfl
        rw [this]
        exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk₀)
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hu₀))
      have hMeq : Wg.subgroupOf h.ker = M := by
        ext k
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hk
          obtain ⟨m, hm, u, hu, hmu⟩ := (mem_sup_normal_iff _ _).mp hk
          have huK : u ∈ h.ker := by
            have hu' : u = m⁻¹ * k := by rw [← hmu]; group
            rw [hu']
            exact h.ker.mul_mem (h.ker.inv_mem (Subgroup.map_subtype_le M hm)) k.2
          have hmem := M'.mul_mem hm (hU₀K u hu huK)
          rw [hmu] at hmem
          obtain ⟨k', hk', hk'k⟩ := hmem
          rwa [← Subtype.ext hk'k]
        · intro hk
          exact Subgroup.mem_sup_left ⟨k, hk, rfl⟩
      have hWL : IsLIndex L W := by
        have h1 : (W.map V.subtype).relIndex h.ker = W.index :=
          relIndex_map_subtype_eq_index hK W hsup
        have h2 : W.map V.subtype = Wg := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hWgV]
        rw [h2, Subgroup.relIndex, hMeq] at h1
        rw [IsLIndex, ← h1]
        exact hML
      have hsK : Function.Surjective ((QuotientGroup.mk' W).comp (Subgroup.inclusion hK)) := by
        intro q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : v ∈ h.ker.subgroupOf V ⊔ W := by
          rw [hsup]
          trivial
        obtain ⟨k', hk', w, hw, rfl⟩ := (mem_sup_normal_iff _ _).mp hv
        refine ⟨⟨k', hk'⟩, ?_⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have : Subgroup.inclusion hK ⟨(k' : G'), hk'⟩ = k' := rfl
        rw [this, inv_mul_cancel_left]
        exact hw
      obtain ⟨x, hx⟩ := hcrit V hVo hK W hWo hWL hsK
        (QuotientGroup.mk (Subgroup.inclusion hK k))
      have hw := QuotientGroup.eq.mp hx
      rw [Subgroup.mem_subgroupOf] at hw
      refine ⟨x, ?_⟩
      have hmemK : (h' x)⁻¹ * (k : G') ∈ h.ker :=
        h.ker.mul_mem (h.ker.inv_mem (range_le_ker_of_comp_eq_one h' h hcomp ⟨x, rfl⟩)) k.2
      have : (⟨_, hmemK⟩ : h.ker) ∈ M := by
        rw [← hMeq, Subgroup.mem_subgroupOf]
        simpa using hw
      exact ⟨_, this, rfl⟩
    -- Step 2: compactness.
    intro k hk
    let ι := {M : Subgroup h.ker // M.Normal ∧ IsOpen (M : Set h.ker) ∧ IsLIndex L M}
    have hne : Nonempty ι := ⟨⟨⊤, inferInstance, isOpen_univ,
      ⟨by simp, fun p hp hdvd ↦ absurd (Nat.le_of_dvd one_pos (by simpa using hdvd))
        (by simpa using hp.one_lt)⟩⟩⟩
    have hKc : IsClosed (h.ker : Set G') := isClosed_singleton.preimage hh
    have hMc : ∀ M : ι, IsClosed ((M.1.map h.ker.subtype : Subgroup G') : Set G') := by
      intro M
      rw [Subgroup.coe_map]
      have := Subgroup.isClosed_of_isOpen (G := h.ker) M.1 M.2.2.1
      exact hKc.isClosedEmbedding_subtypeVal.isClosedMap _ this
    let t : ι → Set G' := fun M ↦
      (h'.range : Set G') ∩ (fun a ↦ a⁻¹ * k) ⁻¹' (M.1.map h.ker.subtype : Set G')
    have hrc : IsCompact (h'.range : Set G') := by
      rw [MonoidHom.coe_range]
      exact isCompact_range hh'
    have hcont : Continuous fun a : G' ↦ a⁻¹ * k := continuous_inv.mul continuous_const
    have ht : (⋂ M, t M).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro M₁ M₂
        have := M₁.2.1
        have := M₂.2.1
        refine ⟨⟨M₁.1 ⊓ M₂.1, inferInstance, M₁.2.2.1.inter M₂.2.2.1, M₁.2.2.2.inf M₂.2.2.2⟩,
          Set.inter_subset_inter_right _ (Set.preimage_mono fun x hx ↦ ?_),
          Set.inter_subset_inter_right _ (Set.preimage_mono fun x hx ↦ ?_)⟩
        · exact Subgroup.map_mono inf_le_left hx
        · exact Subgroup.map_mono inf_le_right hx
      · intro M
        obtain ⟨x, hx⟩ := step1 M.1 M.2.1 M.2.2.1 M.2.2.2 ⟨k, hk⟩
        exact ⟨h' x, ⟨x, rfl⟩, hx⟩
      · intro M
        exact hrc.inter_right ((hMc M).preimage hcont)
      · intro M
        exact hrc.isClosed.inter ((hMc M).preimage hcont)
    obtain ⟨a, ha⟩ := ht
    rw [Set.mem_iInter] at ha
    obtain ⟨⟨x, rfl⟩, -⟩ := ha (Classical.arbitrary ι)
    have hmemK : (h' x)⁻¹ * k ∈ h.ker :=
      h.ker.mul_mem (h.ker.inv_mem (range_le_ker_of_comp_eq_one h' h hcomp ⟨x, rfl⟩)) hk
    have hN : (⟨_, hmemK⟩ : h.ker) ∈ proLKernel L h.ker :=
      mem_proLKernel.mpr fun M hMn hMo hML ↦ by
        obtain ⟨-, m, hm, hmeq⟩ := ha ⟨M, hMn, hMo, hML⟩
        rwa [show (⟨_, hmemK⟩ : h.ker) = m from Subtype.ext hmeq.symm]
    have hk' : k = h' x * ((h' x)⁻¹ * k) := by group
    rw [hk']
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨_, hN, rfl⟩

omit [T2Space G'] in
include hh in
/-- XIII.4.3, the criterion of its proof (V.6.8 for `π'₁`): `u : π₁^L(X_s̄) → π'₁(X)` is injective
iff for every open normal subgroup `W` of `π₁(X_s̄)` with `L`-group quotient (a principal
covering `Z̄` of `X_s̄` with group an `L`-group) there is an open subgroup `U ⊇ N` of `π₁(X)` (a
covering `Z` of `X` which is a `π'₁`-covering) whose preimage lies in `W` (a connected component
of `Z|X_s̄` maps to `Z̄`). -/
theorem injective_proLToPrimeQuotient_iff_exists_openSubgroup :
    Function.Injective (proLToPrimeQuotient L h' h hh' hcomp) ↔
      ∀ W : Subgroup G'', W.Normal → IsOpen (W : Set G'') → IsLIndex L W →
        ∃ U : Subgroup G', IsOpen (U : Set G') ∧ primeKernel L h ≤ U ∧ U.comap h' ≤ W := by
  rw [injective_proLToPrimeQuotient_iff]
  constructor
  · intro hle W hWn hWo hWL
    by_contra hcon
    push Not at hcon
    let Nc : ClosedSubgroup G' := ⟨primeKernel L h, isClosed_primeKernel L h hh⟩
    have hsInf := ProfiniteGrp.closedSubgroup_eq_sInf_open Nc
    let ι := {U : Subgroup G' // IsOpen (U : Set G') ∧ primeKernel L h ≤ U}
    have hne : Nonempty ι := ⟨⟨⊤, isOpen_univ, le_top⟩⟩
    let c : ι → Set G'' := fun U ↦ (U.1.comap h' : Set G'') ∩ (W : Set G'')ᶜ
    have hclosed : ∀ U : ι, IsClosed (c U) := fun U ↦
      ((Subgroup.isClosed_of_isOpen U.1 U.2.1).preimage hh').inter hWo.isClosed_compl
    have hc : (⋂ U, c U).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U₁ U₂
        refine ⟨⟨U₁.1 ⊓ U₂.1, U₁.2.1.inter U₂.2.1, le_inf U₁.2.2 U₂.2.2⟩,
          Set.inter_subset_inter_left _ fun x hx ↦ ?_,
          Set.inter_subset_inter_left _ fun x hx ↦ ?_⟩
        · exact (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
        · exact (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
      · intro U
        obtain ⟨x, hx, hxW⟩ := SetLike.not_le_iff_exists.mp (hcon U.1 U.2.1 U.2.2)
        exact ⟨x, hx, hxW⟩
      · exact fun U ↦ (hclosed U).isCompact
      · exact hclosed
    obtain ⟨x, hx⟩ := hc
    rw [Set.mem_iInter] at hx
    have hxN : h' x ∈ primeKernel L h := by
      have : h' x ∈ (Nc : Subgroup G') := by
        rw [hsInf, Subgroup.mem_sInf]
        rintro U ⟨hUo, hNU⟩
        exact (hx ⟨U, hUo, hNU⟩).1
      exact this
    exact (hx (Classical.arbitrary ι)).2 (proLKernel_le hWn hWo hWL (hle hxN))
  · intro hcrit x hx
    rw [mem_proLKernel]
    intro W hWn hWo hWL
    obtain ⟨U, -, hNU, hUW⟩ := hcrit W hWn hWo hWL
    exact hUW (hNU hx)

end Criteria

section Semidirect

variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- XIII.4.5: a short exact sequence `1 → A → B → C → 1` with a section `w` of `B → C` (in SGA:
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` with the section induced by `g : S → X`) identifies `B`
with a semidirect product of `C` by `A`, `C` acting on `A` by conjugation through `w`. This is
mathlib's `GroupExtension.Splitting.semidirectProductMulEquiv`. -/
theorem exists_semidirectProduct_mulEquiv (u : A →* B) (v : B →* C)
    (hu : Function.Injective u) (hv : Function.Surjective v) (hex : u.range = v.ker)
    (w : C →* B) (hw : v.comp w = MonoidHom.id C) :
    ∃ (φ : C →* MulAut A) (e : A ⋊[φ] C ≃* B),
      (∀ a, e (SemidirectProduct.inl a) = u a) ∧ (∀ c, e (SemidirectProduct.inr c) = w c) ∧
      ∀ c a, u (φ c a) = w c * u a * (w c)⁻¹ := by
  let S : GroupExtension A B C := ⟨u, v, hu, hex, hv⟩
  let s : S.Splitting := ⟨w, fun c ↦ DFunLike.congr_fun hw c⟩
  refine ⟨s.conjAct, s.semidirectProductMulEquiv, fun a ↦ ?_, fun c ↦ ?_, fun c a ↦ ?_⟩
  · change u a * w 1 = u a
    rw [map_one, mul_one]
  · change u 1 * w c = w c
    rw [map_one, one_mul]
  · exact S.inl_conjAct_comm

variable {G : Type*} [Group G] (φ : C →* MulAut A) (ψ : C →* MulAut G)

/-- Crossed homomorphisms `A ⋊ C → G`, for the action of `A ⋊ C` on `G` through `C`, which are
trivial on `C`. In XIII.4.5.1 they classify the torsors under `G_X` trivialized along the
section `g`. -/
abbrev NormalizedCrossedHom : Type _ :=
  { f : A ⋊[φ] C → G //
    (∀ b₁ b₂, f (b₁ * b₂) = f b₁ * ψ b₁.right (f b₂)) ∧ ∀ c, f (SemidirectProduct.inr c) = 1 }

/-- `C`-equivariant homomorphisms `A → G`; in XIII.4.5.1, the homomorphisms of group schemes
`π₁^L(X/S, g) → G` over `S`. -/
abbrev EquivariantHom : Type _ :=
  { f : A →* G // ∀ c a, f (φ c a) = ψ c (f a) }

variable {φ ψ} in
lemma NormalizedCrossedHom.apply_one (f : NormalizedCrossedHom φ ψ) : f.1 1 = 1 := by
  have h : (1 : A ⋊[φ] C) = SemidirectProduct.inr 1 :=
    (map_one (SemidirectProduct.inr : C →* A ⋊[φ] C)).symm
  rw [h, f.2.2]

variable {φ ψ} in
lemma NormalizedCrossedHom.map_inl_mul (f : NormalizedCrossedHom φ ψ) (a₁ a₂ : A) :
    f.1 (SemidirectProduct.inl (a₁ * a₂)) =
      f.1 (SemidirectProduct.inl a₁) * f.1 (SemidirectProduct.inl a₂) := by
  rw [map_mul, f.2.1, SemidirectProduct.right_inl, map_one ψ, MulAut.one_apply]

variable {φ ψ} in
lemma NormalizedCrossedHom.map_inl_aut (f : NormalizedCrossedHom φ ψ) (c : C) (a : A) :
    f.1 (SemidirectProduct.inl (φ c a)) = ψ c (f.1 (SemidirectProduct.inl a)) := by
  rw [SemidirectProduct.inl_aut, f.2.1, f.2.1, f.2.2, f.2.2, SemidirectProduct.right_inr]
  simp

variable {φ ψ} in
lemma NormalizedCrossedHom.apply_eq (f : NormalizedCrossedHom φ ψ) (b : A ⋊[φ] C) :
    f.1 b = f.1 (SemidirectProduct.inl b.left) := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right b]
  rw [f.2.1, f.2.2, map_one (ψ _), mul_one]

/-- XIII.4.5.1, algebraic part: crossed homomorphisms of `A ⋊ C` trivial on `C` are the same as
`C`-equivariant homomorphisms `A → G` (by restriction to `A`). -/
def normalizedCrossedHomEquiv : NormalizedCrossedHom φ ψ ≃ EquivariantHom φ ψ where
  toFun f :=
    ⟨{ toFun := fun a ↦ f.1 (SemidirectProduct.inl a)
       map_one' := by rw [_root_.map_one, f.apply_one]
       map_mul' := f.map_inl_mul },
      f.map_inl_aut⟩
  invFun f :=
    ⟨fun b ↦ f.1 b.left,
      fun b₁ b₂ ↦ by
        change f.1 (b₁ * b₂).left = f.1 b₁.left * ψ b₁.right (f.1 b₂.left)
        rw [SemidirectProduct.mul_left, map_mul, f.2],
      fun c ↦ by
        change f.1 (SemidirectProduct.inr c : A ⋊[φ] C).left = 1
        rw [SemidirectProduct.left_inr, _root_.map_one]⟩
  left_inv f := by
    apply Subtype.ext
    funext b
    exact (f.apply_eq b).symm
  right_inv f := by
    apply Subtype.ext
    ext a
    rfl

variable {φ ψ} in
/-- Changing the trivialization along the section by a `C`-invariant element `γ` of `G`
conjugates a normalized crossed homomorphism by `γ`. -/
def NormalizedCrossedHom.conj (f : NormalizedCrossedHom φ ψ) (γ : G) (hγ : ∀ c, ψ c γ = γ) :
    NormalizedCrossedHom φ ψ :=
  ⟨fun b ↦ γ⁻¹ * f.1 b * γ, fun b₁ b₂ ↦ by
      beta_reduce
      rw [f.2.1, map_mul, map_mul, map_inv, hγ]
      group,
    fun c ↦ by
      beta_reduce
      rw [f.2.2, mul_one, inv_mul_cancel]⟩

/-- XIII.4.5.1, "mod inner automorphisms": `normalizedCrossedHomEquiv` transforms the conjugation
of crossed homomorphisms by a `C`-invariant element `γ` of `G` into the conjugation of
equivariant homomorphisms by `γ`. -/
lemma normalizedCrossedHomEquiv_conj (f : NormalizedCrossedHom φ ψ) (γ : G)
    (hγ : ∀ c, ψ c γ = γ) (a : A) :
    (normalizedCrossedHomEquiv φ ψ (f.conj γ hγ)).1 a =
      γ⁻¹ * (normalizedCrossedHomEquiv φ ψ f).1 a * γ :=
  rfl

end Semidirect

/-- XIII.4.6, last step of the proof: let `1 → A → Z → Y → 1` be exact (`A = π₁^{p'}(X_b)`,
`Z = π₁^{p'}(X ×_k Y)`) and suppose the composite of `A → Z` with `p : Z → X` is bijective. Then
`(p, q) : Z → X × Y` is bijective. -/
theorem bijective_prod_of_exact {A Z X Y : Type*} [Group A] [Group Z] [Group X] [Group Y]
    (i : A →* Z) (p : Z →* X) (q : Z →* Y) (hq : Function.Surjective q) (hex : i.range = q.ker)
    (hpi : Function.Bijective (p.comp i)) : Function.Bijective (p.prod q) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hz
    obtain ⟨a, rfl⟩ : z ∈ i.range := hex ▸ hz.2
    have : a = 1 := hpi.1 (by simpa using hz.1)
    simp [this]
  · rintro ⟨x, y⟩
    obtain ⟨z₁, rfl⟩ := hq y
    obtain ⟨a, ha⟩ := hpi.2 (x * (p z₁)⁻¹)
    have hqa : q (i a) = 1 := by
      rw [← MonoidHom.mem_ker, ← hex]
      exact ⟨a, rfl⟩
    refine ⟨i a * z₁, Prod.ext ?_ ?_⟩
    · change p (i a * z₁) = x
      rw [map_mul, ← MonoidHom.comp_apply, ha, inv_mul_cancel_right]
    · change q (i a * z₁) = q z₁
      rw [map_mul, hqa, one_mul]

end SGA.SGA1.ExposeXIII
