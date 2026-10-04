/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Group

/-!
# XIII.2.13: the group theory of Harbater–Stevenson's node lemma

In Harbater–Stevenson's proof of Raynaud's patching theorem (*Patching and thickening problems*,
J. Algebra 212 (1999), 272–304, proof of Theorem 6), the local Galois data at the node of a nodal
curve over `k⟦t⟧` are produced by a lemma: for a `p`-group `P`, `P`-Galois covers of the two
punctured branches `Spec k((u))` and `Spec k((v))` at the node extend to a `P`-Galois cover of the
punctured node. Its proof is an induction along a central series of `P`, which only uses two
properties of the fundamental groups involved. This file proves that induction abstractly.

Let `Γ` and `Γᵢ` (`i ∈ ι`) be topological groups with continuous homomorphisms `ρᵢ : Γᵢ → Γ`
(for the node: `Γ = π₁` of the punctured node, `Γᵢ = π₁` of the punctured branches, `ρᵢ` induced
by the reductions to the branches). Assume

* (weak lifting) every central embedding problem of order `p` for `Γ` with a surjective
  homomorphism has a weak solution (`HasCentralLifts`; for `Γ = π₁(Spec R)`, `R` of
  characteristic `p` with connected spectrum, this is
  `SGA.SGA1.ExposeXIII.exists_lift_of_central_ker`);
* (Artin–Schreier surjectivity) every family of continuous homomorphisms `δᵢ : Γᵢ → D` to a group
  `D` of order `p` is the restriction `χ ∘ ρᵢ` of one continuous `χ : Γ → D` (for the node this
  is Artin–Schreier theory together with
  `PatchingProjectiveLine.exists_nodePunctured_reduce_eq`).

Then (`AffineLinePGroups.exists_continuousMonoidHom_conj`) for every finite `p`-group `P` and every
family of continuous homomorphisms `φᵢ : Γᵢ → P` there is a continuous `ψ : Γ → P` such that each
`ψ ∘ ρᵢ` is conjugate to `φᵢ`. The weak lifting hypothesis is only needed for surjective
homomorphisms: the general case follows by restricting the extension to the preimage of the image
(`HasCentralLifts.exists_lift`).
-/

universe u v w

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

section CentralLifts

variable (p : ℕ) (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

/-- Weak solvability of the central embedding problems of order `p` for `Γ`, for surjective
homomorphisms: if `ψ : Γ → H` is a continuous surjection onto a finite group and `π : G → H` is a
surjection whose kernel is central of order `p`, then `ψ` lifts to a continuous `Γ → G`.
The groups `H` and `G` are taken in the universe `u`. -/
def HasCentralLifts : Prop :=
  ∀ (H G : Type u) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G]
    [TopologicalSpace G] [DiscreteTopology G] (ψ : ContinuousMonoidHom Γ H),
    Function.Surjective ψ → ∀ π : G →* H, Function.Surjective π → π.ker ≤ Subgroup.center G →
      Nat.card π.ker = p → ∃ ψ' : ContinuousMonoidHom Γ G, π.comp ψ'.toMonoidHom = ψ.toMonoidHom

variable {p Γ}

/-- Weak solutions of central embedding problems of order `p` exist for all continuous
homomorphisms `ψ : Γ → H`, not only for the surjective ones: restrict the extension `G → H` to the
preimage of the image of `ψ`. -/
theorem HasCentralLifts.exists_lift (h : HasCentralLifts.{u} p Γ) {H G : Type u} [Group H]
    [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (ψ : ContinuousMonoidHom Γ H) (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hcard : Nat.card π.ker = p) :
    ∃ ψ' : ContinuousMonoidHom Γ G, π.comp ψ'.toMonoidHom = ψ.toMonoidHom := by
  classical
  set H' : Subgroup H := ψ.toMonoidHom.range
  set G' : Subgroup G := H'.comap π
  let π' : G' →* H' := (π.comp G'.subtype).codRestrict H' fun g ↦ g.2
  have hπ'apply (g : G') : (π' g : H) = π g := rfl
  have hπ' : Function.Surjective π' := by
    rintro ⟨h', hh'⟩
    obtain ⟨g, rfl⟩ := hπ h'
    exact ⟨⟨g, hh'⟩, rfl⟩
  have hmem_ker (z : G') (hz : z ∈ π'.ker) : (z : G) ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hz ⊢
    rw [← hπ'apply, hz, OneMemClass.coe_one]
  have hker' : π'.ker ≤ Subgroup.center G' := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker (hmem_ker z hz))) g)
  have hcard' : Nat.card π'.ker = p := by
    rw [← hcard]
    refine Nat.card_congr
      { toFun := fun z ↦ ⟨z.1.1, hmem_ker z.1 z.2⟩
        invFun := fun z ↦ ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun z ↦ rfl
        right_inv := fun z ↦ rfl }
    · change π z.1 ∈ H'
      rw [MonoidHom.mem_ker.mp z.2]
      exact H'.one_mem
    · rw [MonoidHom.mem_ker]
      exact Subtype.ext (MonoidHom.mem_ker.mp z.2)
  let ψ₀ : ContinuousMonoidHom Γ H' :=
    ⟨ψ.toMonoidHom.rangeRestrict, continuous_induced_rng.2 ψ.continuous⟩
  have hψ₀ : Function.Surjective ψ₀ := ψ.toMonoidHom.rangeRestrict_surjective
  obtain ⟨ψ₁, hψ₁⟩ := h H' G' ψ₀ hψ₀ π' hπ' hker' hcard'
  refine ⟨⟨G'.subtype.comp ψ₁.toMonoidHom, continuous_subtype_val.comp ψ₁.continuous⟩, ?_⟩
  ext γ
  have := congrArg (fun f : Γ →* H' ↦ (f γ : H)) hψ₁
  exact this

end CentralLifts

section Node

variable {p : ℕ} [hp : Fact p.Prime] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]

omit hp in
lemma mul_comm_of_mem_center {P : Type*} [Group P] {z : P} (hz : z ∈ Subgroup.center P)
    (x : P) : z * x = x * z :=
  (Subgroup.mem_center_iff.mp hz x).symm

/-- The group theory of Harbater–Stevenson's node lemma (proof of Theorem 6 of *Patching and
thickening problems*, J. Algebra 212 (1999)): let `ρᵢ : Γᵢ → Γ` be continuous homomorphisms such
that

* `Γ` has weak solutions of central embedding problems of order `p` (`HasCentralLifts`), and
* every family of continuous homomorphisms `δᵢ : Γᵢ → D` to a discrete group of order `p` is the
  family of restrictions `χ ∘ ρᵢ` of a single continuous `χ : Γ → D`.

Then for every finite `p`-group `P` and continuous homomorphisms `φᵢ : Γᵢ → P` there is a continuous
`ψ : Γ → P` with `ψ ∘ ρᵢ` conjugate to `φᵢ` for each `i`. The proof is an induction on `|P|`
along a central subgroup `Z` of order `p`: lift a solution for `P/Z` (weak lifting), then correct
the lift by a homomorphism `Γ → Z` whose restrictions are the differences on the `Γᵢ`. -/
theorem exists_continuousMonoidHom_conj (hlift : HasCentralLifts.{u} p Γ) {ι : Type w}
    {Γi : ι → Type*} [∀ i, Group (Γi i)] [∀ i, TopologicalSpace (Γi i)]
    (ρ : ∀ i, ContinuousMonoidHom (Γi i) Γ)
    (hAS : ∀ (D : Type u) [Group D] [TopologicalSpace D] [DiscreteTopology D], Nat.card D = p →
      ∀ δ : ∀ i, ContinuousMonoidHom (Γi i) D,
        ∃ χ : ContinuousMonoidHom Γ D, ∀ i σ, χ (ρ i σ) = δ i σ)
    (P : Type u) [Group P] [Finite P] [TopologicalSpace P] [DiscreteTopology P]
    (hP : IsPGroup p P) (φ : ∀ i, ContinuousMonoidHom (Γi i) P) :
    ∃ ψ : ContinuousMonoidHom Γ P, ∀ i, ∃ c : P, ∀ σ, ψ (ρ i σ) = c * φ i σ * c⁻¹ := by
  classical
  suffices H : ∀ n (P : Type u) [Group P] [Finite P] [TopologicalSpace P] [DiscreteTopology P],
      Nat.card P = n → IsPGroup p P → ∀ φ : ∀ i, ContinuousMonoidHom (Γi i) P,
        ∃ ψ : ContinuousMonoidHom Γ P, ∀ i, ∃ c : P, ∀ σ, ψ (ρ i σ) = c * φ i σ * c⁻¹ from
    H _ P rfl hP φ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ _ _ hn hP φ
  rcases subsingleton_or_nontrivial P with hs | hnt
  · exact ⟨1, fun i ↦ ⟨1, fun σ ↦ Subsingleton.elim _ _⟩⟩
  -- a central subgroup `Z` of order `p`
  have hZc := hP.center_nontrivial
  obtain ⟨z, hz⟩ : ∃ z : Subgroup.center P, orderOf z = p := by
    apply exists_prime_orderOf_dvd_card' p
    obtain ⟨m, hm, hcard⟩ := (hP.to_subgroup _).nontrivial_iff_card.mp hZc
    rw [hcard]
    exact dvd_pow_self p hm.ne'
  set Z : Subgroup P := Subgroup.zpowers (z : P) with hZdef
  have hZcenter : Z ≤ Subgroup.center P := (Subgroup.zpowers_le).mpr z.2
  have hZcard : Nat.card Z = p := by
    rw [hZdef, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have : Z.Normal := ⟨fun x hx g ↦ by
    rw [← mul_comm_of_mem_center (hZcenter hx) g, mul_inv_cancel_right]
    exact hx⟩
  -- the quotient `P/Z`
  let _ : TopologicalSpace (P ⧸ Z) := ⊥
  have : DiscreteTopology (P ⧸ Z) := ⟨rfl⟩
  have hlt : Nat.card (P ⧸ Z) < n := by
    rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZcard]
    exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt
  let q : P →* (P ⧸ Z) := QuotientGroup.mk' Z
  let φbar : ∀ i, ContinuousMonoidHom (Γi i) (P ⧸ Z) := fun i ↦
    ⟨q.comp (φ i).toMonoidHom, (continuous_of_discreteTopology (f := q)).comp (φ i).continuous⟩
  obtain ⟨ψbar, hψbar⟩ := ih _ hlt (P ⧸ Z) rfl (hP.to_quotient Z) φbar
  -- lift the solution for `P/Z` to `P`
  obtain ⟨ψ', hψ'⟩ := hlift.exists_lift ψbar q (QuotientGroup.mk'_surjective Z)
    (by rw [QuotientGroup.ker_mk']; exact hZcenter) (by rw [QuotientGroup.ker_mk']; exact hZcard)
  have hψ'q (γ : Γ) : q (ψ' γ) = ψbar γ := congrArg (fun f : Γ →* P ⧸ Z ↦ f γ) hψ'
  choose cbar hcbar using hψbar
  choose c hc using fun i ↦ QuotientGroup.mk'_surjective Z (cbar i)
  -- the differences `δᵢ : Γᵢ → Z`
  have hdiff (i : ι) (σ : Γi i) : ψ' (ρ i σ) * (c i * φ i σ * (c i)⁻¹)⁻¹ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    change q (ψ' (ρ i σ) * (c i * φ i σ * (c i)⁻¹)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hψ'q, hcbar i σ, hc i]
    change _ * (_ * q (φ i σ) * _)⁻¹ = 1
    exact mul_inv_cancel _
  let δ : ∀ i, ContinuousMonoidHom (Γi i) Z := fun i ↦
    { toFun := fun σ ↦ ⟨_, hdiff i σ⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun σ τ ↦ by
        apply Subtype.ext
        change ψ' (ρ i (σ * τ)) * (c i * φ i (σ * τ) * (c i)⁻¹)⁻¹ =
          (ψ' (ρ i σ) * (c i * φ i σ * (c i)⁻¹)⁻¹) * (ψ' (ρ i τ) * (c i * φ i τ * (c i)⁻¹)⁻¹)
        have hτ := mul_comm_of_mem_center (hZcenter (hdiff i τ)) ((c i * φ i σ * (c i)⁻¹)⁻¹)
        rw [map_mul, map_mul, map_mul]
        calc ψ' (ρ i σ) * ψ' (ρ i τ) * (c i * (φ i σ * φ i τ) * (c i)⁻¹)⁻¹
            = ψ' (ρ i σ) * ((ψ' (ρ i τ) * (c i * φ i τ * (c i)⁻¹)⁻¹) *
                (c i * φ i σ * (c i)⁻¹)⁻¹) := by group
          _ = _ := by rw [hτ]; group
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_of_discreteTopology
          (f := fun x : P × P ↦ x.1 * (c i * x.2 * (c i)⁻¹)⁻¹)).comp
            ((ψ'.continuous.comp (ρ i).continuous).prodMk (φ i).continuous) }
  obtain ⟨χ, hχ⟩ := hAS Z hZcard δ
  -- correct the lift by `χ`
  have hχc (γ : Γ) : ((χ γ : Z) : P) ∈ Subgroup.center P := hZcenter (χ γ).2
  let ψ : ContinuousMonoidHom Γ P :=
    { toFun := fun γ ↦ ψ' γ * ((χ γ : Z) : P)⁻¹
      map_one' := by simp
      map_mul' := fun γ γ' ↦ by
        have h1 := mul_comm_of_mem_center (Subgroup.inv_mem _ (hχc γ)) (ψ' γ')
        have h2 := mul_comm_of_mem_center (hχc γ) ((χ γ' : Z) : P)
        change ψ' (γ * γ') * ((χ (γ * γ') : Z) : P)⁻¹ =
          ψ' γ * ((χ γ : Z) : P)⁻¹ * (ψ' γ' * ((χ γ' : Z) : P)⁻¹)
        rw [map_mul, map_mul, Subgroup.coe_mul, h2,
          show ψ' γ * ((χ γ : Z) : P)⁻¹ * (ψ' γ' * ((χ γ' : Z) : P)⁻¹) =
            ψ' γ * (((χ γ : Z) : P)⁻¹ * ψ' γ') * ((χ γ' : Z) : P)⁻¹ by group, h1]
        group
      continuous_toFun :=
        (continuous_of_discreteTopology (f := fun x : P × Z ↦ x.1 * (x.2 : P)⁻¹)).comp
          (ψ'.continuous.prodMk χ.continuous) }
  refine ⟨ψ, fun i ↦ ⟨c i, fun σ ↦ ?_⟩⟩
  change ψ' (ρ i σ) * ((χ (ρ i σ) : Z) : P)⁻¹ = _
  rw [hχ i σ]
  change ψ' (ρ i σ) * (ψ' (ρ i σ) * (c i * φ i σ * (c i)⁻¹)⁻¹)⁻¹ = _
  rw [← mul_comm_of_mem_center (Subgroup.inv_mem _ (hZcenter (hdiff i σ))) (ψ' (ρ i σ))]
  group

end Node

end SGA.SGA1.ExposeXIII.AffineLinePGroups
