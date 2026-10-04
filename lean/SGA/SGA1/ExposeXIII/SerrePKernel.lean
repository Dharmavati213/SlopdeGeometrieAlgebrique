/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import SGA.SGA1.ExposeXIII.AbhyankarAffineLine
import SGA.SGA1.ExposeXIII.SerrePKernelProper

/-!
# Serre's theorem on `p`-group kernels for the affine line

Serre (C. R. Acad. Sci. Paris 311 (1990), 341–346): over an algebraically closed field `k` of
characteristic `p`, if `H` is a continuous quotient of `π₁(𝔸¹_k)` and `G → H` is onto with kernel a
`p`-group, then `G` is a continuous quotient of `π₁(𝔸¹_k)` (`affineLinePExtension`, which proves
`AffineLinePExtensionStatement`). This is the first case of Raynaud's proof of XIII.2.13, so
Abhyankar's conjecture for the affine line now follows from the other two cases alone
(`abhyankarAffineLine_of_patching_of_caseB`).

The proof is by induction on `|G|`. A minimal normal subgroup `M` of `G` inside the kernel is
elementary abelian (`exists_minimal_normal_elementary`). The vector Artin–Schreier covering gives
a lift through `G → G/M` (`exists_lift_of_elementary_ker`); if it is not onto, its image is a
complement of `M` (`ker_le_of_not_surjective`, `exists_section_of_inf_eq_bot`), and in this split
case the covering of an invariant class `a` that is not a coboundary
(`exists_invariant_forall_not_root`) gives a lift which is onto, since otherwise the covering would
be dominated by the Galois covering of `G/M` and `a` would be a coboundary
(`exists_lift_of_split`, `exists_surjective_of_minimal_ker`).
-/

universe u

namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

section GroupTheory

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

omit [Group G] [Finite G] in
lemma exists_addEquiv_of_zmodModule {A : Type*} [AddCommGroup A] [Finite A]
    [Module (ZMod p) A] [Nontrivial A] :
    ∃ r, 0 < r ∧ Nonempty ((Fin r → ZMod p) ≃+ A) := by
  have : Module.Finite (ZMod p) A := Module.Finite.of_finite
  exact ⟨_, Module.finrank_pos, ⟨(Module.finBasis (ZMod p) A).equivFun.symm.toAddEquiv⟩⟩

/-- A minimal non-trivial normal subgroup contained in a normal `p`-subgroup `N` exists, and it
is elementary abelian: `≅ (ℤ/p)ʳ`. -/
theorem exists_minimal_normal_elementary (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hne : N ≠ ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ M ≤ N ∧ M ≠ ⊥ ∧
      (∀ L : Subgroup G, L.Normal → L ≤ M → L = ⊥ ∨ L = M) ∧
      ∃ r, 0 < r ∧ Nonempty (Multiplicative (Fin r → ZMod p) ≃* M) := by
  classical
  obtain ⟨M, ⟨hMn, hMN, hMne⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {L : Subgroup G | L.Normal ∧ L ≤ N ∧ L ≠ ⊥} ⟨N, inferInstance, le_rfl, hne⟩
  have hMmin : ∀ L : Subgroup G, L.Normal → L ≤ M → L = ⊥ ∨ L = M := by
    intro L hL hLM
    by_contra h
    push Not at h
    exact hmin L ⟨hL, hLM.trans hMN, h.1⟩ (lt_of_le_of_ne hLM h.2)
  have hMp : IsPGroup p M := hN.to_le hMN
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have : M.Normal := hMn
  -- `M` is abelian: its centre is a non-trivial normal subgroup of `G`
  have hcomm : ∀ x y : M, x * y = y * x := by
    let K := (Subgroup.center M).map M.subtype
    have hKM : K ≤ M := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hKne : K ≠ ⊥ := by
      have := hMp.center_nontrivial
      intro hK
      rw [Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective] at hK
      obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center M)
      exact hz (Subtype.ext (by simpa [hK] using z.2))
    rcases hMmin K inferInstance hKM with h | h
    · exact absurd h hKne
    · intro x y
      have hx : (x : G) ∈ K := by rw [h]; exact x.2
      obtain ⟨x', hx', hxx'⟩ := hx
      have : x' = x := Subtype.ext hxx'
      rw [← this]
      exact (Subgroup.mem_center_iff.mp hx' y).symm
  -- `M` has exponent `p`: its `p`-torsion is a non-trivial normal subgroup of `G`
  have hexp : ∀ x : M, x ^ p = 1 := by
    let K : Subgroup M :=
      { carrier := {x | x ^ p = 1}
        mul_mem' := fun {x y} hx hy ↦ by
          change (x * y) ^ p = 1
          rw [(Commute.mul_pow (hcomm x y) p), hx, hy, one_mul]
        one_mem' := one_pow p
        inv_mem' := fun {x} hx ↦ by
          change x⁻¹ ^ p = 1
          rw [inv_pow, hx, inv_one] }
    have : K.Characteristic := ⟨fun φ ↦ by
      ext x
      change (φ x) ^ p = 1 ↔ x ^ p = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff]⟩
    let K' := K.map M.subtype
    have hK'M : K' ≤ M := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hK'ne : K' ≠ ⊥ := by
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) p (by
        obtain ⟨n, hn⟩ := hMp.exists_card_eq
        have : n ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hn
          exact (Finite.one_lt_card (α := M)).ne' hn
        rw [hn]
        exact dvd_pow_self p this)
      intro hK'
      rw [Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective] at hK'
      have hxK : x ∈ K := by
        change x ^ p = 1
        rw [← hx, pow_orderOf_eq_one]
      rw [hK', Subgroup.mem_bot] at hxK
      rw [hxK, orderOf_one] at hx
      exact hp.out.one_lt.ne hx
    rcases hMmin K' inferInstance hK'M with h | h
    · exact absurd h hK'ne
    · intro x
      have hx : (x : G) ∈ K' := by rw [h]; exact x.2
      obtain ⟨x', hx', hxx'⟩ := hx
      have : x' = x := Subtype.ext hxx'
      rw [← this]
      exact hx'
  -- coordinates
  let : CommGroup M := { (inferInstance : Group M) with mul_comm := hcomm }
  let : Module (ZMod p) (Additive M) := AddCommGroup.zmodModule (n := p) fun x ↦ by
    change Additive.ofMul ((Additive.toMul x) ^ p) = 0
    rw [hexp]
    rfl
  have : Finite (Additive M) := inferInstanceAs (Finite M)
  have : Nontrivial (Additive M) := inferInstanceAs (Nontrivial M)
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_addEquiv_of_zmodModule (p := p) (A := Additive M)
  exact ⟨M, hMn, hMN, hMne, hMmin, r, hr, ⟨AddEquiv.toMultiplicativeLeft e⟩⟩

end GroupTheory

section Lifts

variable {Γ G Q : Type*} [Group Γ] [Group G] [Group Q]

/-- A lift `φ` of a surjection `ψ` through `π : G → Q` whose kernel is abelian and minimal normal
is either surjective or meets the kernel trivially; in the second case `ker ψ ⊆ ker φ`. -/
lemma ker_le_of_not_surjective (π : G →* Q) (φ : Γ →* G) (ψ : Γ →* Q) (hφ : π.comp φ = ψ)
    (hψ : Function.Surjective ψ) (hcomm : ∀ x ∈ π.ker, ∀ y ∈ π.ker, x * y = y * x)
    (hmin : ∀ L : Subgroup G, L.Normal → L ≤ π.ker → L = ⊥ ∨ L = π.ker)
    (hns : ¬ Function.Surjective φ) : φ.range ⊓ π.ker = ⊥ ∧ ψ.ker ≤ φ.ker := by
  have hπφ : ∀ γ, π (φ γ) = ψ γ := fun γ ↦ by rw [← MonoidHom.comp_apply, hφ]
  have hK : φ.range ⊓ π.ker = ⊥ := by
    have hnormal : (φ.range ⊓ π.ker).Normal := ⟨fun x hx g ↦ by
      obtain ⟨γ, hγ⟩ := hψ (π g)
      set i := φ γ
      have hm : i⁻¹ * g ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπφ, hγ, inv_mul_cancel]
      have hxm : (i⁻¹ * g) * x * (i⁻¹ * g)⁻¹ = x := by
        rw [hcomm _ hm x hx.2, mul_inv_cancel_right]
      have : g * x * g⁻¹ = i * x * i⁻¹ := by
        calc g * x * g⁻¹ = i * ((i⁻¹ * g) * x * (i⁻¹ * g)⁻¹) * i⁻¹ := by group
          _ = i * x * i⁻¹ := by rw [hxm]
      have hi : i ∈ φ.range := ⟨γ, rfl⟩
      rw [this]
      exact ⟨φ.range.mul_mem (φ.range.mul_mem hi hx.1) (φ.range.inv_mem hi),
        (MonoidHom.normal_ker π).conj_mem x hx.2 i⟩⟩
    rcases hmin _ hnormal inf_le_right with h | h
    · exact h
    · exfalso
      refine hns fun g ↦ ?_
      obtain ⟨γ, hγ⟩ := hψ (π g)
      have hm : (φ γ)⁻¹ * g ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπφ, hγ, inv_mul_cancel]
      have : (φ γ)⁻¹ * g ∈ φ.range := (h ▸ inf_le_left : π.ker ≤ φ.range) hm
      obtain ⟨δ, hδ⟩ := this
      exact ⟨γ * δ, by rw [map_mul, hδ, mul_inv_cancel_left]⟩
  refine ⟨hK, fun γ hγ ↦ ?_⟩
  have : φ γ ∈ φ.range ⊓ π.ker := ⟨⟨γ, rfl⟩, (MonoidHom.mem_ker).mpr (by
    rw [hπφ]
    exact hγ)⟩
  rw [hK, Subgroup.mem_bot] at this
  exact this

/-- If a lift `φ` of a surjection `ψ` through `π` meets `ker π` trivially, its image is a
complement: `π` has a homomorphic section. -/
lemma exists_section_of_inf_eq_bot (π : G →* Q) (φ : Γ →* G) (ψ : Γ →* Q)
    (hφ : π.comp φ = ψ) (hψ : Function.Surjective ψ) (hK : φ.range ⊓ π.ker = ⊥) :
    ∃ s₀ : Q →* G, ∀ σ, π (s₀ σ) = σ := by
  let π' : φ.range →* Q := π.comp φ.range.subtype
  have hinj : Function.Injective π' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have : (x : G) ∈ φ.range ⊓ π.ker := ⟨x.2, hx⟩
    rw [hK, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hsurj : Function.Surjective π' := fun σ ↦ by
    obtain ⟨γ, rfl⟩ := hψ σ
    exact ⟨⟨φ γ, γ, rfl⟩, by simp [π', ← hφ]⟩
  let e := MulEquiv.ofBijective π' ⟨hinj, hsurj⟩
  exact ⟨φ.range.subtype.comp e.symm.toMonoidHom, fun σ ↦ e.apply_symm_apply σ⟩

end Lifts

section Step

open CategoryTheory PreGaloisCategory CommAlgCat AffineLinePGroups Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-- Serre's theorem, one step: over `𝔸¹_k` (`k` algebraically closed of characteristic `p`), a
continuous surjection `ψ : π₁ → Q` lifts to a continuous surjection onto `G`, for any `G → Q`
whose kernel is a minimal normal subgroup `≅ (ℤ/p)ʳ`. -/
theorem exists_surjective_of_minimal_ker (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k[X] Ω] {Q G : Type u} [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) Q) (hψ : Function.Surjective ψ)
    (π : G →* Q) (hπ : Function.Surjective π) {r : ℕ} (hr : 0 < r)
    (e : Multiplicative (Fin r → ZMod p) ≃* π.ker)
    (hmin : ∀ L : Subgroup G, L.Normal → L ≤ π.ker → L = ⊥ ∨ L = π.ker) :
    ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) G, Function.Surjective φ := by
  classical
  have hcomm : ∀ x ∈ π.ker, ∀ y ∈ π.ker, x * y = y * x := by
    intro x hx y hy
    have := congrArg Subtype.val (congrArg e (mul_comm (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩)))
    simpa using this
  obtain ⟨ψ', hψ'⟩ := exists_lift_of_elementary_ker p k[X] Ω ψ hψ π hπ e
  by_cases hs : Function.Surjective ψ'
  · exact ⟨ψ', hs⟩
  obtain ⟨hK, -⟩ := ker_le_of_not_surjective π ψ'.toMonoidHom ψ.toMonoidHom hψ' hψ hcomm hmin hs
  obtain ⟨s₀, hs₀⟩ := exists_section_of_inf_eq_bot π ψ'.toMonoidHom ψ.toMonoidHom hψ' hψ hK
  -- the Galois algebra of `ψ`
  obtain ⟨P, α, hα, x₀, hx₀⟩ := ExposeV.exists_torsorHom_eq
    (F := ExposeV.fiberFunctor k[X] Ω) ψ.toMonoidHom ψ.continuous
  let A := P.unop
  let ρH : Q →* (A.obj ≃ₐ[k[X]] A.obj) := (autOpMulEquivAlgEquiv A).toMonoidHom.comp α
  have hH : ∀ x y : A.obj →ₐ[k[X]] Ω, ∃! σ : Q, x.comp (ρH σ).toAlgHom = y := hα
  let x₀a : A.obj →ₐ[k[X]] Ω := x₀
  have hconn := isConnected_of_torsorHom k[X] Ω ψ hψ hα x₀ hx₀
  obtain ⟨hnt, hidem⟩ := (ExposeV.isConnected_op_iff k[X] A).mp hconn
  have : ConnectedSpace (PrimeSpectrum A.obj) :=
    (ExposeV.isConnected_op_iff_connectedSpace k[X] A).mp hconn
  have : IsDomain A.obj := isDomain_of_etale_of_connectedSpace (R := k[X])
  have : CharP A.obj p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap k[X] A.obj), CharP.cast_eq_zero, map_zero])
  have : Fintype Q := Fintype.ofFinite Q
  -- Chase–Harrison–Rosenberg elements for the Galois action
  have hCHR := galoisAlgebra_exists_galois_elements k[X] Ω A ρH x₀a hH hidem
  -- the conjugation matrices
  obtain ⟨CmH, hCmH⟩ := exists_comp_eq_of_ker π hπ (conjMat p e)
    fun z hz ↦ conjMat_eq_one_of_mem p e hz
  -- an invariant class which is not a coboundary
  obtain ⟨a, ha, hroot⟩ := exists_invariant_forall_not_root p ρH CmH hr hCHR
  obtain ⟨ψa, hψa, hdom⟩ := exists_lift_of_split p k[X] Ω ψ hψ π e s₀ hs₀ hα x₀ hx₀ CmH hCmH a ha
  by_contra hno
  push Not at hno
  have hnsa : ¬ Function.Surjective ψa := fun h ↦ hno ψa h
  obtain ⟨-, hker⟩ := ker_le_of_not_surjective π ψa.toMonoidHom ψ.toMonoidHom hψa hψ hcomm hmin
    hnsa
  obtain ⟨b, hb⟩ := hdom hker
  exact hroot b hb

end Step

section Induction

open CategoryTheory PreGaloisCategory CommAlgCat AffineLinePGroups Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-- Serre's theorem for `p`-group kernels, in terms of the fibre functor of finite étale
`k[T]`-algebras (`k` algebraically closed of characteristic `p`). -/
theorem exists_surjective_of_isPGroup_ker (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k[X] Ω] {Q : Type u} [Group Q] [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q]
    (hQ : ∃ ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) Q, Function.Surjective ψ)
    (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] (π : G →* Q)
    (hπ : Function.Surjective π) (hpk : IsPGroup p π.ker) :
    ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) G, Function.Surjective φ := by
  suffices h : ∀ n (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
      (π : G →* Q), Nat.card G = n → Function.Surjective π → IsPGroup p π.ker →
      ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) G, Function.Surjective φ from
    h _ G π rfl hπ hpk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ _ π hn hπ hpk
  by_cases hN : π.ker = ⊥
  · let eπ := MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hN, hπ⟩
    obtain ⟨ψ, hψ⟩ := hQ
    exact ⟨⟨eπ.symm.toMonoidHom.comp ψ.toMonoidHom,
      (continuous_of_discreteTopology (f := eπ.symm)).comp ψ.continuous⟩,
      eπ.symm.surjective.comp hψ⟩
  obtain ⟨M, hMn, hMN, hMne, hMmin, r, hr, ⟨eM⟩⟩ :=
    exists_minimal_normal_elementary π.ker hpk hN
  let : TopologicalSpace (G ⧸ M) := ⊥
  have : DiscreteTopology (G ⧸ M) := ⟨rfl⟩
  let π' : G ⧸ M →* Q := QuotientGroup.lift M π hMN
  have hπ' : Function.Surjective π' := by
    intro σ
    obtain ⟨g, rfl⟩ := hπ σ
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hmem : ∀ g : G, (g : G ⧸ M) ∈ π'.ker ↔ g ∈ π.ker := fun g ↦ Iff.rfl
  have hpk' : IsPGroup p π'.ker := by
    intro ⟨q, hq⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨j, hj⟩ := hpk ⟨g, (hmem g).mp hq⟩
    refine ⟨j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hlt : Nat.card (G ⧸ M) < n := by
    rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup M]
    have : 0 < Nat.card (G ⧸ M) := Nat.card_pos
    have : 1 < Nat.card M := by
      have := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
      exact Finite.one_lt_card
    nlinarith
  obtain ⟨ψ', hψ'⟩ := ih _ hlt (G ⧸ M) π' rfl hπ' hpk'
  have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
  exact exists_surjective_of_minimal_ker p k Ω ψ' hψ' (QuotientGroup.mk' M)
    (QuotientGroup.mk'_surjective M) hr (eM.trans (MulEquiv.subgroupCongr hker.symm))
    (fun L hL hLM ↦ by rw [hker] at hLM ⊢; exact hMmin L hL hLM)

end Induction

section Statement

open AlgebraicGeometry Polynomial AffineLinePGroups

variable (p : ℕ) [hp : Fact p.Prime]

/-- Serre's theorem on `p`-group kernels for the affine line (C. R. Acad. Sci. Paris 311 (1990);
the first step of Raynaud's proof of XIII.2.13): over an algebraically closed field `k` of
characteristic `p`, the finite continuous quotients of `π₁(𝔸¹_k)` are closed under extensions by
`p`-groups. -/
theorem affineLinePExtension : AffineLinePExtensionStatement.{u} p := by
  intro k _ _ _ Ω _ _ x G H _ _ _ _ _ _ _ _ π hπ hpk hH
  let := ExposeV.algebraOfPoint (CommRingCat.of k[X]) Ω x
  exact exists_surjective_of_continuousMulEquiv (fundamentalGroupSpecContinuousMulEquiv k[X] Ω x)
    (exists_surjective_of_isPGroup_ker p k Ω (exists_surjective_of_continuousMulEquiv
      (fundamentalGroupSpecContinuousMulEquiv k[X] Ω x).symm hH) G π hπ hpk)

/-- XIII.2.13 (Abhyankar's conjecture for the affine line) follows from the patching step
(`AffineLinePatchingStatement`) and the degeneration step (`AffineLineCaseBStatement`) of
Raynaud's proof, Serre's theorem being proved (`affineLinePExtension`). -/
theorem abhyankarAffineLine_of_patching_of_caseB (h₂ : AffineLinePatchingStatement.{u} p)
    (h₃ : AffineLineCaseBStatement.{u} p) : AbhyankarAffineLineStatement.{u} p :=
  abhyankarAffineLine_of_cases p (affineLinePExtension p) h₂ h₃

end Statement

end SerrePKernel

end SGA.SGA1.ExposeXIII
