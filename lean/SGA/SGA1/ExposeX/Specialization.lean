/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# SGA 1, Exposé X: the group theory of the specialization homomorphism

Several results of Exposé X are deduced from geometric input by arguments on (profinite)
groups alone. This file proves these arguments; the geometric input appears as hypotheses.

* X.1.7: a split exact sequence `e → π₁(X) → π₁(X ×ₖ Y) → π₁(Y) → e` gives
  `π₁(X ×ₖ Y) ≅ π₁(X) × π₁(Y)` (`bijective_prod_of_retraction`).
* X.2.2: transporting the exact sequence IX.6.1 along the isomorphisms X.2.1
  (`exact_of_bijective`).
* The specialization homomorphism (between X.2.2 and X.2.3) and its surjectivity X.2.3
  (`SpecializationDiagram.specializationHom`,
  `SpecializationDiagram.specializationHom_surjective`).
* X.2.12: a topologically finitely generated group has only finitely many continuous
  homomorphisms to a finite group (`finite_setOf_continuous_monoidHom`).
* X.3.6: the group-theoretic core of Abhyankar's lemma (`injective_snd_of_isCyclic`).
* X.3.9 from X.3.8: the specialization homomorphism induces an isomorphism on the largest
  quotients of order prime to `p`, and is an isomorphism in characteristic zero
  (`primeToQuotientEquiv`, `bijective_of_forall_factor`).
-/

universe u

namespace SGA.SGA1.ExposeX

section Product

variable {A B C : Type*} [Group A] [Group B] [Group C]

/-- X.1.7 (group-theoretic part). Let `i : A → B`, `p : B → C` with `p` surjective and
`Im i = Ker p`, and let `r : B → A` be a retraction of `i`. Then `(r, p) : B → A × C` is an
isomorphism. In X.1.7, `A = π₁(X)`, `B = π₁(X ×ₖ Y)`, `C = π₁(Y)`, `p` and `r` come from the
projections and `i` from the fibre `X ≅ X ×ₖ {b}`; exactness is X.1.4. -/
theorem bijective_prod_of_retraction (i : A →* B) (p : B →* C) (r : B →* A)
    (hri : r.comp i = MonoidHom.id A) (hex : i.range = p.ker) (hp : Function.Surjective p) :
    Function.Bijective (r.prod p) := by
  have hri' (a : A) : r (i a) = a := DFunLike.congr_fun hri a
  have hpi (a : A) : p (i a) = 1 := by
    rw [← MonoidHom.mem_ker, ← hex]
    exact ⟨a, rfl⟩
  constructor
  · rw [injective_iff_map_eq_one]
    intro b hb
    simp only [MonoidHom.prod_apply, Prod.mk_eq_one] at hb
    obtain ⟨a, rfl⟩ : b ∈ i.range := hex ▸ hb.2
    rw [hri'] at hb
    rw [hb.1, map_one]
  · rintro ⟨a, c⟩
    obtain ⟨b, rfl⟩ := hp c
    refine ⟨b * i ((r b)⁻¹ * a), ?_⟩
    simp [hri', hpi]

end Product

section Exact

variable {A B C B' C' : Type*} [Group A] [Group B] [Group C] [Group B'] [Group C']

/-- X.2.2 (group-theoretic part): an exact sequence `e → A → B → C → e` stays exact after
replacing `B` and `C` by isomorphic groups compatibly. In X.2.2 the sequence is IX.6.1 for the
closed fibre `X₀`, and the isomorphisms are `π₁(X₀) ≅ π₁(X)` (X.2.1) and
`π₁(k) ≅ π₁(Y)`. -/
theorem exact_of_bijective (i : A →* B) (p : B →* C) (β : B →* B') (γ : C →* C')
    (p' : B' →* C') (hcomm : p'.comp β = γ.comp p) (hβ : Function.Bijective β)
    (hγ : Function.Bijective γ) (hi : Function.Injective i) (hex : i.range = p.ker)
    (hp : Function.Surjective p) :
    Function.Injective (β.comp i) ∧ (β.comp i).range = p'.ker ∧ Function.Surjective p' := by
  have hc (b : B) : p' (β b) = γ (p b) := DFunLike.congr_fun hcomm b
  refine ⟨hβ.injective.comp hi, ?_, fun c' ↦ ?_⟩
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      have : i a ∈ p.ker := hex ▸ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hc, (MonoidHom.mem_ker).mp this, map_one]
    · intro hx
      obtain ⟨b, rfl⟩ := hβ.surjective x
      rw [MonoidHom.mem_ker, hc, ← map_one γ] at hx
      obtain ⟨a, rfl⟩ : b ∈ i.range := hex ▸ hγ.injective hx
      exact ⟨a, rfl⟩
  · obtain ⟨c, rfl⟩ := hγ.surjective c'
    obtain ⟨b, rfl⟩ := hp c
    exact ⟨β b, hc b⟩

end Exact

section Specialization

variable {A₀ B₀ C₀ A₁ B₁ C₁ : Type*} [Group A₀] [Group B₀] [Group C₀] [Group A₁] [Group B₁]
  [Group C₁] {i₀ : A₀ →* B₀} {p₀ : B₀ →* C₀} {i₁ : A₁ →* B₁} {p₁ : B₁ →* C₁}
  {β : B₁ →* B₀} {γ : C₁ →* C₀}

/-- The data of the commutative diagram of X.2.2–X.2.3: a row
`A₁ → B₁ → C₁` whose composite is trivial (the geometric fibre `X̄₁`, `X`, `Y`, based at `a₁`),
an exact row `e → A₀ → B₀ → C₀` (X.2.2, based at `a₀`) and vertical maps `β`, `γ` (a class of
paths from `a₁` to `a₀`) making the square commute. -/
structure SpecializationDiagram (i₀ : A₀ →* B₀) (p₀ : B₀ →* C₀) (i₁ : A₁ →* B₁)
    (p₁ : B₁ →* C₁) (β : B₁ →* B₀) (γ : C₁ →* C₀) : Prop where
  injective_i₀ : Function.Injective i₀
  range_i₀ : i₀.range = p₀.ker
  comm : p₀.comp β = γ.comp p₁
  comp_eq_one : p₁.comp i₁ = 1

namespace SpecializationDiagram

variable (h : SpecializationDiagram i₀ p₀ i₁ p₁ β γ)
include h

lemma mem_range (a : A₁) : β (i₁ a) ∈ i₀.range := by
  rw [h.range_i₀, MonoidHom.mem_ker, ← MonoidHom.comp_apply, h.comm, MonoidHom.comp_apply,
    ← MonoidHom.comp_apply p₁, h.comp_eq_one, MonoidHom.one_apply, map_one]

/-- The specialization homomorphism `π₁(X̄₁, ā₁) → π₁(X̄₀, ā₀)` (defined after X.2.2): the unique
homomorphism `A₁ → A₀` through which `β ∘ i₁` factors, `i₀` being injective. -/
noncomputable def specializationHom : A₁ →* A₀ :=
  (MonoidHom.ofInjective h.injective_i₀).symm.toMonoidHom.comp
    ((β.comp i₁).codRestrict i₀.range h.mem_range)

lemma i₀_specializationHom (a : A₁) : i₀ (specializationHom h a) = β (i₁ a) := by
  have := congrArg Subtype.val ((MonoidHom.ofInjective h.injective_i₀).apply_symm_apply
    ((β.comp i₁).codRestrict i₀.range h.mem_range a))
  rw [MonoidHom.ofInjective_apply] at this
  exact this

/-- Uniqueness of the specialization homomorphism. -/
lemma eq_specializationHom (s : A₁ →* A₀) (hs : i₀.comp s = β.comp i₁) :
    s = specializationHom h := by
  ext a
  apply h.injective_i₀
  rw [h.i₀_specializationHom, ← MonoidHom.comp_apply, hs, MonoidHom.comp_apply]

/-- X.2.3 (group-theoretic part): if the vertical maps are isomorphisms (X.2.1) and the first
row is exact at `B₁` (X.1.4), the specialization homomorphism is surjective. -/
theorem specializationHom_surjective (hβ : Function.Surjective β) (hγ : Function.Injective γ)
    (hex₁ : p₁.ker ≤ i₁.range) : Function.Surjective (specializationHom h) := by
  intro a₀
  obtain ⟨b₁, hb₁⟩ := hβ (i₀ a₀)
  have hk : p₁ b₁ = 1 := by
    apply hγ
    rw [map_one, ← MonoidHom.comp_apply, ← h.comm, MonoidHom.comp_apply, hb₁,
      ← MonoidHom.mem_ker, ← h.range_i₀]
    exact ⟨a₀, rfl⟩
  obtain ⟨a₁, rfl⟩ := hex₁ hk
  exact ⟨a₁, h.injective_i₀ (by rw [h.i₀_specializationHom, hb₁])⟩

/-- The specialization homomorphism is continuous when `i₀` is a topological embedding (for
instance a continuous injection from a compact group to a Hausdorff group). -/
theorem continuous_specializationHom [TopologicalSpace A₀] [TopologicalSpace B₀]
    [TopologicalSpace A₁] [TopologicalSpace B₁] (hi₀ : Topology.IsEmbedding i₀)
    (hi₁ : Continuous i₁) (hβ : Continuous β) : Continuous (specializationHom h) := by
  rw [hi₀.continuous_iff]
  have : (i₀ ∘ specializationHom h) = β ∘ i₁ := funext h.i₀_specializationHom
  rw [this]
  exact hβ.comp hi₁

end SpecializationDiagram

end Specialization

section FiniteGeneration

/-- X.2.12 (group-theoretic part): if `G` is topologically generated by a finite set `S`
(X.2.9), there are only finitely many continuous homomorphisms from `G` to a finite group `Q`.
In X.2.12, `G = π₁(X)` and these homomorphisms classify the principal coverings with group `Q`
(up to isomorphism, the classes being the orbits under conjugation). -/
theorem finite_setOf_continuous_monoidHom {G Q : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {S : Set G} (hS : S.Finite) (hdense : (Subgroup.closure S).topologicalClosure = ⊤) :
    {f : G →* Q | Continuous f}.Finite := by
  have : Finite S := hS.to_subtype
  let Φ : {f : G →* Q | Continuous f} → S → Q := fun f s ↦ f.1 s
  have hΦ : Function.Injective Φ := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ hfg
    have hcl : Subgroup.closure S ≤ f.eqLocus g :=
      (Subgroup.closure_le _).mpr fun s hs ↦ congrFun hfg ⟨s, hs⟩
    have htop : (Subgroup.closure S).topologicalClosure ≤ f.eqLocus g :=
      Subgroup.topologicalClosure_minimal _ hcl (isClosed_eq hf hg)
    rw [hdense] at htop
    exact Subtype.ext (MonoidHom.ext fun x ↦ htop (Subgroup.mem_top x))
  exact Set.finite_coe_iff.mp (Finite.of_injective Φ hΦ)

end FiniteGeneration

section Abhyankar

/-- X.3.6 (group-theoretic core of Abhyankar's lemma). Let `M` be a cyclic subgroup of `G × H`,
where `H` is finite and the exponent of `G` divides the order of `H`. If `M → H` is surjective,
it is injective. In X.3.6, `G` and `H` are the inertia groups of `L` and `K'` (cyclic of orders
`n ∣ m`, tame ramification), `M` is the inertia group of the composite `L'` (cyclic, of order
prime to `p`), and injectivity of `M → H` says that `L'` is unramified over `K'`. -/
theorem injective_snd_of_isCyclic {G H : Type*} [Group G] [Group H] [Finite H]
    (M : Subgroup (G × H)) [IsCyclic M] (hG : Monoid.exponent G ∣ Nat.card H)
    (hsurj : Function.Surjective ((MonoidHom.snd G H).comp M.subtype)) :
    Function.Injective ((MonoidHom.snd G H).comp M.subtype) := by
  have hpow (x : M) : x ^ Nat.card H = 1 := by
    obtain ⟨⟨g, h⟩, hx⟩ := x
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, Prod.pow_mk, OneMemClass.coe_one, Prod.mk_eq_one]
    obtain ⟨k, hk⟩ := hG
    exact ⟨by rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow], pow_card_eq_one'⟩
  have hdvd : Nat.card M ∣ Nat.card H := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have hpos : 0 < Nat.card H := Nat.card_pos
  have : Finite M := Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero hpos.ne' hdvd)
  exact (hsurj.bijective_of_nat_card_le (Nat.le_of_dvd hpos hdvd)).injective

end Abhyankar

section PrimeTo

variable (q : ℕ) (G : Type*) [Group G] [TopologicalSpace G]

/-- X.3.9: the intersection of the open normal subgroups of `G` whose index is prime to `q`,
i.e. of the kernels of the continuous homomorphisms of `G` onto finite groups of order prime to
`q`. For `q = p` the characteristic exponent, `G ⧸ primeToKernel q G` is the group `G^(p)` of
X.3.9 (for `q = 1`, characteristic zero, every open normal subgroup occurs). -/
def primeToKernel : Subgroup G :=
  ⨅ (N : OpenNormalSubgroup G) (_ : N.toSubgroup.index.Coprime q), N.toSubgroup

instance : (primeToKernel q G).Normal := by
  unfold primeToKernel
  refine Subgroup.normal_iInf_normal fun N ↦ Subgroup.normal_iInf_normal fun _ ↦ N.isNormal'

variable {q G}

lemma primeToKernel_le (N : OpenNormalSubgroup G) (hN : N.toSubgroup.index.Coprime q) :
    primeToKernel q G ≤ N.toSubgroup :=
  iInf₂_le N hN

lemma le_primeToKernel {K : Subgroup G}
    (h : ∀ N : OpenNormalSubgroup G, N.toSubgroup.index.Coprime q → K ≤ N.toSubgroup) :
    K ≤ primeToKernel q G :=
  le_iInf₂ h

/-- In a profinite group, the open normal subgroups meet in the trivial subgroup; hence so does
`primeToKernel 1 G` (characteristic zero). -/
lemma primeToKernel_one_eq_bot [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] : primeToKernel 1 G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := x)) (Ne.symm hne)
  exact hN (primeToKernel_le N (Nat.coprime_one_right _) hx) rfl

variable {G₁ : Type u} {G₀ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [CompactSpace G₁] [Group G₀] [TopologicalSpace G₀]
  (sp : G₁ →* G₀)

/-- X.3.8, as a hypothesis on a homomorphism `sp : G₁ → G₀`: every continuous homomorphism of
`G₁` into a finite group of order prime to `q` comes from a continuous homomorphism of `G₀`. -/
def FactorsPrimeTo (q : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
    (Nat.card Q).Coprime q → ∀ f : G₁ →* Q, Continuous f →
      ∃ g : G₀ →* Q, Continuous g ∧ g.comp sp = f

variable {sp}

/-- X.3.9 (from X.3.8 and the surjectivity X.2.4): the inverse image of `N_q(G₀)` under the
specialization homomorphism is `N_q(G₁)`. -/
theorem comap_primeToKernel (hsp : Continuous sp) (hsurj : Function.Surjective sp)
    (hfac : FactorsPrimeTo sp q) :
    (primeToKernel q G₀).comap sp = primeToKernel q G₁ := by
  apply le_antisymm
  · refine le_primeToKernel fun N hN x hx ↦ ?_
    have : DiscreteTopology (G₁ ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
    have : Finite (G₁ ⧸ N.toSubgroup) := N.toSubgroup.quotient_finite_of_isOpen N.isOpen
    obtain ⟨g, hg, hgsp⟩ := hfac (G₁ ⧸ N.toSubgroup) hN (QuotientGroup.mk' N.toSubgroup)
      QuotientGroup.continuous_mk
    have hgsurj : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup y
      exact ⟨sp x, DFunLike.congr_fun hgsp x⟩
    let N₀ : OpenNormalSubgroup G₀ :=
      { toSubgroup := g.ker
        isOpen' := (isOpen_discrete ({1} : Set (G₁ ⧸ N.toSubgroup))).preimage hg
        isNormal' := g.normal_ker }
    have hN₀ : N₀.toSubgroup.index.Coprime q := by
      change g.ker.index.Coprime q
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hgsurj, Subgroup.card_top]
      exact hN
    have h1 : g (sp x) = 1 := primeToKernel_le N₀ hN₀ hx
    rw [← MonoidHom.comp_apply, hgsp, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  · intro x hx
    rw [Subgroup.mem_comap, primeToKernel, Subgroup.mem_iInf]
    intro N₀
    rw [Subgroup.mem_iInf]
    intro hN₀
    let N : OpenNormalSubgroup G₁ :=
      { toSubgroup := N₀.toSubgroup.comap sp
        isOpen' := N₀.isOpen.preimage hsp
        isNormal' := N₀.isNormal'.comap sp }
    have hN : N.toSubgroup.index.Coprime q := by
      change (N₀.toSubgroup.comap sp).index.Coprime q
      rwa [Subgroup.index_comap_of_surjective _ hsurj]
    exact primeToKernel_le N hN hx

/-- X.3.9, first assertion: the kernel of the specialization homomorphism is contained in
`N_q(G₁)`, the intersection of the kernels of the continuous homomorphisms of `G₁` to finite
groups of order prime to `q`. -/
theorem ker_le_primeToKernel (hsp : Continuous sp) (hsurj : Function.Surjective sp)
    (hfac : FactorsPrimeTo sp q) : sp.ker ≤ primeToKernel q G₁ := by
  rw [← comap_primeToKernel hsp hsurj hfac]
  intro x hx
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hx]
  exact one_mem _

/-- X.3.9, second assertion: the specialization homomorphism induces an isomorphism
`G₁^(p) ≅ G₀^(p)` of the largest quotients of order prime to `p` (with `q = p`). -/
noncomputable def primeToQuotientEquiv (hsp : Continuous sp) (hsurj : Function.Surjective sp)
    (hfac : FactorsPrimeTo sp q) :
    G₁ ⧸ primeToKernel q G₁ ≃* G₀ ⧸ primeToKernel q G₀ :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_primeToKernel hsp hsurj hfac])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' _).comp sp)
      ((QuotientGroup.mk'_surjective _).comp hsurj))

lemma primeToQuotientEquiv_mk (hsp : Continuous sp) (hsurj : Function.Surjective sp)
    (hfac : FactorsPrimeTo sp q) (x : G₁) :
    primeToQuotientEquiv hsp hsurj hfac (x : G₁ ⧸ primeToKernel q G₁) = (sp x : G₀ ⧸ _) :=
  rfl

/-- X.3.9, characteristic zero: if every continuous homomorphism of the profinite group `G₁` to a
finite group factors through the surjection `sp` (X.3.8 with `p = 1`), then `sp` is an
isomorphism. -/
theorem bijective_of_forall_factor [T2Space G₁] [TotallyDisconnectedSpace G₁]
    (hsp : Continuous sp) (hsurj : Function.Surjective sp)
    (hfac : FactorsPrimeTo sp 1) : Function.Bijective sp := by
  refine ⟨?_, hsurj⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← primeToKernel_one_eq_bot]
  exact ker_le_primeToKernel hsp hsurj hfac

end PrimeTo

end SGA.SGA1.ExposeX
