/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupPresentation
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupCompletion

/-!
# SGA 1, XIII.2.12: inertia subgroups, change of base point and finite levels

In SGA the inertia group at a point is defined up to conjugation (XIII.2.11, proof), and the
condition "`σⱼ` generates an inertia group at `aⱼ`" of XIII.2.12 is read in a quotient of
`π₁(U)`. This file collects the formal facts used to verify it.

* `IsInertiaSubgroupAt.map_path`: transported along a path `ξ → ξ'` (V.7), an inertia subgroup at
  `x̄` of `π₁(U, ξ)` becomes one of `π₁(U, ξ')`; `IsInertiaSubgroupAt.conj`: conjugates of inertia
  subgroups are inertia subgroups.
* `tameCurvePrimeToPConclusion_of_path`: the conclusion of XIII.2.12 ("in other words" form)
  at one geometric point of `U` implies it at every other one.
* `topologicalClosure_sup_proLKernel_eq_iInf`: in a compact group, the closure of `B · Γ^L-kernel`
  is the intersection of the `B · N`, `N` open normal of `L`-index.
* `exists_conj_topologicalClosure_sup_proLKernel_eq`: if for each open normal `N` of `L`-index
  the images of `H` and `A` in `Γ / N` are conjugate, then some conjugate of `H` has the same
  image as `A` in `Γ^L` (a compactness argument). This is how an identification of inertia
  groups made in each finite quotient of `π₁(U)` (where the choices of paths are not compatible)
  gives the condition of XIII.2.12.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry
open scoped Pointwise

namespace SGA.SGA1.ExposeXIII

section Paths

open ExposeV

variable {S : Scheme.{u}}

/-- The isomorphism of fundamental groups induced by a composite of paths is the composite. -/
lemma continuousMulEquivOfPath_trans_apply {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω']
    [Field Ω''] {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S} {s'' : Spec (.of Ω'') ⟶ S}
    (γ : etalePaths Ω Ω' s s') (γ' : etalePaths Ω' Ω'' s' s'')
    (σ : etaleFundamentalGroup Ω s) :
    etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω'' (γ ≪≫ γ') σ =
      etaleFundamentalGroup.continuousMulEquivOfPath Ω' Ω'' γ'
        (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω' γ σ) :=
  Iso.trans_conjAut γ γ' σ

/-- An element `g` of `π₁(S, s)` is a path from `s` to itself, and the induced automorphism of
`π₁(S, s)` is the conjugation by `g`. -/
lemma continuousMulEquivOfPath_self_apply {Ω : Type u} [Field Ω] {s : Spec (.of Ω) ⟶ S}
    (g σ : etaleFundamentalGroup Ω s) :
    etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω g σ = g * σ * g⁻¹ := by
  exact Iso.ext rfl

lemma map_continuousMulEquivOfPath_trans {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω']
    [Field Ω''] {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S} {s'' : Spec (.of Ω'') ⟶ S}
    (γ : etalePaths Ω Ω' s s') (γ' : etalePaths Ω' Ω'' s' s'')
    (K : Subgroup (etaleFundamentalGroup Ω s)) :
    (K.map (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω' γ).toMonoidHom).map
        (etaleFundamentalGroup.continuousMulEquivOfPath Ω' Ω'' γ').toMonoidHom =
      K.map (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω'' (γ ≪≫ γ')).toMonoidHom := by
  rw [Subgroup.map_map]
  exact congrArg (fun φ ↦ K.map φ) (MonoidHom.ext fun σ ↦
    (continuousMulEquivOfPath_trans_apply γ γ' σ).symm)

variable {X : Scheme.{u}} {U : X.Opens} {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
  {xb : Spec (.of Ω₀) ⟶ X} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] {ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})}
  {ξ' : Spec (.of Ω') ⟶ (U : Scheme.{u})} {H : Subgroup (etaleFundamentalGroup Ω ξ)}

/-- V.7, XIII.2.11: an inertia subgroup at `x̄` of `π₁(U, ξ)`, transported along a path from `ξ`
to `ξ'`, is an inertia subgroup at `x̄` of `π₁(U, ξ')`. -/
theorem IsInertiaSubgroupAt.map_path (hH : IsInertiaSubgroupAt U xb ξ H)
    (γ : etalePaths Ω Ω' ξ ξ') :
    IsInertiaSubgroupAt U xb ξ'
      (H.map (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω' γ).toMonoidHom) := by
  obtain ⟨Ω'', i₁, i₂, η, γ₀, hH⟩ := hH
  unfold IsInertiaSubgroupAt
  refine ⟨Ω'', i₁, i₂, η, γ₀ ≪≫ γ, ?_⟩
  rw [hH]
  exact map_continuousMulEquivOfPath_trans γ₀ γ _

/-- XIII.2.11: the conjugates of an inertia subgroup at `x̄` are inertia subgroups at `x̄` (the
inertia group at a point is defined up to conjugation). -/
theorem IsInertiaSubgroupAt.conj (hH : IsInertiaSubgroupAt U xb ξ H)
    (g : etaleFundamentalGroup Ω ξ) : IsInertiaSubgroupAt U xb ξ (MulAut.conj g • H) := by
  have h := hH.map_path g
  convert h using 1
  rw [Subgroup.pointwise_smul_def]
  exact congrArg (fun φ ↦ H.map φ) (MonoidHom.ext fun σ ↦
    (continuousMulEquivOfPath_self_apply g σ).symm)

end Paths

section ProLKernel

variable {L : Set ℕ} {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ']

/-- An isomorphism of topological groups maps the kernel of `Γ → Γ^L` onto that of
`Γ' → Γ'^L`. -/
lemma map_proLKernel_of_continuousMulEquiv (ψ : Γ ≃ₜ* Γ') :
    (proLKernel L Γ).map (ψ : Γ →* Γ') = proLKernel L Γ' := by
  refine le_antisymm ?_ fun γ' hγ' ↦ ⟨ψ.symm γ', ?_, ψ.apply_symm_apply γ'⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact proLKernel_le_comap L (ψ : Γ →* Γ') ψ.continuous hγ
  · exact proLKernel_le_comap L (ψ.symm : Γ' →* Γ) ψ.symm.continuous hγ'

/-- The closure of a subgroup is transported by isomorphisms of topological groups. -/
lemma map_topologicalClosure_of_continuousMulEquiv [IsTopologicalGroup Γ]
    [IsTopologicalGroup Γ'] (ψ : Γ ≃ₜ* Γ')
    (B : Subgroup Γ) :
    B.topologicalClosure.map (ψ : Γ →* Γ') = (B.map (ψ : Γ →* Γ')).topologicalClosure := by
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe,
    Subgroup.coe_map]
  exact ψ.toHomeomorph.image_closure _

end ProLKernel

section Transport

open ExposeV

variable {k : Type u} [Field k] {X : Scheme.{u}} {g n : ℕ} {a : Fin n → X} {U : X.Opens}
  {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  {ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})} {ξ' : Spec (.of Ω') ⟶ (U : Scheme.{u})}

/-- XIII.2.12, change of base point: the conclusion of XIII.2.12 ("in other words" form,
`TameCurvePrimeToPConclusion`) at the geometric point `ξ` of `U` implies it at `ξ'`, given a
path from `ξ` to `ξ'` (one exists when `U` is connected, V.7). -/
theorem tameCurvePrimeToPConclusion_of_path
    (h : TameCurvePrimeToPConclusion k X g n a U Ω ξ) (γ : etalePaths Ω Ω' ξ ξ') :
    TameCurvePrimeToPConclusion k X g n a U Ω' ξ' := by
  obtain ⟨x, y, σ, hpres, hin⟩ := h
  set ψ := etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω' γ
  refine ⟨ψ ∘ x, ψ ∘ y, ψ ∘ σ, hpres.map ψ, fun j ↦ ?_⟩
  obtain ⟨Ω₀, _, _, xb, H, hxb, hH, hHσ⟩ := hin j
  refine ⟨Ω₀, _, _, xb, H.map (ψ : _ →* _), hxb, hH.map_path γ, ?_⟩
  have hK := map_proLKernel_of_continuousMulEquiv (L := primesDifferentFrom (ringChar k)) ψ
  have e₁ := map_topologicalClosure_of_continuousMulEquiv ψ
    (H ⊔ proLKernel (primesDifferentFrom (ringChar k)) _)
  have e₂ := map_topologicalClosure_of_continuousMulEquiv ψ
    (Subgroup.zpowers (σ j) ⊔ proLKernel (primesDifferentFrom (ringChar k)) _)
  rw [Subgroup.map_sup, hK] at e₁ e₂
  rw [← e₁, hHσ, e₂, MonoidHom.map_zpowers]
  rfl

end Transport

section Compactness

variable {L : Set ℕ} {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The open normal subgroups of `L`-index, as a type. -/
private abbrev LOpenNormal (L : Set ℕ) (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :=
  {N : Subgroup Γ // N.Normal ∧ IsOpen (N : Set Γ) ∧ IsLIndex L N}

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
private lemma isLIndex_top : IsLIndex L (⊤ : Subgroup Γ) :=
  ⟨by simp, fun p hp h1 ↦ absurd (Nat.dvd_one.mp (by simpa using h1)) hp.ne_one⟩

omit [IsTopologicalGroup Γ] in
private def LOpenNormal.top : LOpenNormal L Γ :=
  ⟨⊤, inferInstance, isOpen_univ, isLIndex_top⟩

omit [IsTopologicalGroup Γ] in
private def LOpenNormal.inf (N₁ N₂ : LOpenNormal L Γ) : LOpenNormal L Γ :=
  have := N₁.2.1
  have := N₂.2.1
  ⟨N₁.1 ⊓ N₂.1, inferInstance, N₁.2.2.1.inter N₂.2.2.1, N₁.2.2.2.inf N₂.2.2.2⟩

/-- In a compact group, the closure of `B ⊔ proLKernel L Γ` is the intersection of the subgroups
`B ⊔ N`, `N` open normal of `L`-index. -/
theorem topologicalClosure_sup_proLKernel_eq_iInf [CompactSpace Γ] (B : Subgroup Γ) :
    (B ⊔ proLKernel L Γ).topologicalClosure =
      ⨅ (N : Subgroup Γ) (_ : N.Normal ∧ IsOpen (N : Set Γ) ∧ IsLIndex L N), B ⊔ N := by
  refine le_antisymm (le_iInf₂ fun N hN ↦ ?_) fun y hy ↦ ?_
  · refine Subgroup.topologicalClosure_minimal _ (sup_le_sup_left (proLKernel_le hN.1 hN.2.1
      hN.2.2) B) ?_
    exact Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right hN.2.1)
  · -- `y ∈ M N` for all `N`, where `M` is the (compact) closure; Cantor's intersection theorem
    set M := (B ⊔ proLKernel L Γ).topologicalClosure
    have hMc : IsClosed (M : Set Γ) := Subgroup.isClosed_topologicalClosure _
    have hyN (N : LOpenNormal L Γ) : y ∈ B ⊔ N.1 :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hy N.1) N.2
    let t : LOpenNormal L Γ → Set Γ := fun N ↦ (M : Set Γ) ∩ y • (N.1 : Set Γ)
    have : Nonempty (LOpenNormal L Γ) := ⟨LOpenNormal.top⟩
    have hne : (⋂ N, t N).Nonempty := by
      refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t ?_ ?_ ?_ ?_
      · intro N₁ N₂
        refine ⟨N₁.inf N₂, ?_, ?_⟩
        · exact Set.inter_subset_inter_right _ (Set.smul_set_mono inf_le_left)
        · exact Set.inter_subset_inter_right _ (Set.smul_set_mono inf_le_right)
      · intro N
        have := N.2.1
        obtain ⟨b, hb, m, hm, hbm⟩ := (mem_sup_normal_iff B N.1).mp (hyN N)
        refine ⟨b, Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left hb), m⁻¹, inv_mem hm,
          ?_⟩
        rw [← hbm]
        simp
      · intro N
        exact (hMc.inter ((Subgroup.isClosed_of_isOpen _ N.2.2.1).smul y)).isCompact
      · intro N
        exact hMc.inter ((Subgroup.isClosed_of_isOpen _ N.2.2.1).smul y)
    obtain ⟨m, hm⟩ := hne
    rw [Set.mem_iInter] at hm
    have hmM : m ∈ M := (hm LOpenNormal.top).1
    have hK : y⁻¹ * m ∈ proLKernel L Γ := by
      rw [mem_proLKernel]
      intro N hN ho hL
      obtain ⟨n, hn, hnm⟩ := (hm ⟨N, hN, ho, hL⟩).2
      simp only [smul_eq_mul] at hnm
      rw [← hnm, inv_mul_cancel_left]
      exact hn
    have : y = m * (y⁻¹ * m)⁻¹ := by group
    rw [this]
    exact M.mul_mem hmM (inv_mem (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hK)))

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- Conjugating by an element of a subgroup `M` preserves `M`. -/
private lemma conj_smul_eq_self_of_mem {M : Subgroup Γ} {n : Γ} (hn : n ∈ M) :
    MulAut.conj n • M = M := by
  refine le_antisymm ?_ fun m hm ↦ ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact M.mul_mem (M.mul_mem hn hm) (inv_mem hn)
  · refine ⟨n⁻¹ * m * n, M.mul_mem (M.mul_mem (inv_mem hn) hm) hn, ?_⟩
    simp [mul_assoc]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
private lemma conj_mul_smul_sup {H N : Subgroup Γ} [hN : N.Normal] (g : Γ) {n : Γ} (hn : n ∈ N) :
    MulAut.conj (g * n) • H ⊔ N = MulAut.conj g • H ⊔ N := by
  have hNg : MulAut.conj g • N = N := Subgroup.Normal.conj_smul_eq_self g N
  have hNn : MulAut.conj n • N = N := Subgroup.Normal.conj_smul_eq_self n N
  rw [map_mul, mul_smul]
  calc MulAut.conj g • MulAut.conj n • H ⊔ N
      = MulAut.conj g • (MulAut.conj n • H ⊔ MulAut.conj n • N) := by
        rw [Subgroup.smul_sup, hNn, hNg]
    _ = MulAut.conj g • (H ⊔ N) := by
        rw [← Subgroup.smul_sup, conj_smul_eq_self_of_mem (Subgroup.mem_sup_right hn)]
    _ = MulAut.conj g • H ⊔ N := by rw [Subgroup.smul_sup, hNg]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
private lemma sup_eq_sup_of_le {M A N' N : Subgroup Γ} (h : M ⊔ N' = A ⊔ N') (hN : N' ≤ N) :
    M ⊔ N = A ⊔ N := by
  rw [← sup_eq_right.mpr hN, ← sup_assoc, h, sup_assoc]

/-- **Finite levels to `Γ^L`, up to conjugation.** In a compact group `Γ`, let `H` and `A` be
subgroups whose images in `Γ / N` are conjugate for every open normal subgroup `N` of `L`-index
(`(g H g⁻¹) N = A N` for some `g`, depending on `N`). Then a single conjugate `g H g⁻¹` has the
same image as `A` in `Γ^L`: `closure (g H g⁻¹ · proLKernel) = closure (A · proLKernel)`. -/
theorem exists_conj_topologicalClosure_sup_proLKernel_eq [CompactSpace Γ] (H A : Subgroup Γ)
    (h : ∀ N : Subgroup Γ, N.Normal → IsOpen (N : Set Γ) → IsLIndex L N →
      ∃ g : Γ, MulAut.conj g • H ⊔ N = A ⊔ N) :
    ∃ g : Γ, (MulAut.conj g • H ⊔ proLKernel L Γ).topologicalClosure =
      (A ⊔ proLKernel L Γ).topologicalClosure := by
  -- `C N`: the conjugating elements at level `N`; a nonempty union of cosets of `N`
  let C : LOpenNormal L Γ → Set Γ := fun N ↦ {g | MulAut.conj g • H ⊔ N.1 = A ⊔ N.1}
  have hCN (N : LOpenNormal L Γ) {g n : Γ} (hn : n ∈ N.1) : g * n ∈ C N ↔ g ∈ C N := by
    have := N.2.1
    change MulAut.conj (g * n) • H ⊔ N.1 = A ⊔ N.1 ↔ MulAut.conj g • H ⊔ N.1 = A ⊔ N.1
    rw [conj_mul_smul_sup g hn]
  have hopen (N : LOpenNormal L Γ) {D : Set Γ} (hD : ∀ g n, n ∈ N.1 → (g * n ∈ D ↔ g ∈ D)) :
      IsOpen D := by
    refine isOpen_iff_forall_mem_open.mpr fun g hg ↦ ⟨g • (N.1 : Set Γ), ?_, N.2.2.1.smul g,
      ⟨1, one_mem _, by simp⟩⟩
    rintro _ ⟨n, hn, rfl⟩
    exact (hD g n hn).mpr hg
  have hclosed (N : LOpenNormal L Γ) : IsClosed (C N) := by
    rw [← isOpen_compl_iff]
    exact hopen N fun g n hn ↦ not_congr (hCN N hn)
  have : Nonempty (LOpenNormal L Γ) := ⟨LOpenNormal.top⟩
  have hne : (⋂ N, C N).Nonempty := by
    refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C ?_ ?_
      (fun N ↦ (hclosed N).isCompact) hclosed
    · intro N₁ N₂
      exact ⟨N₁.inf N₂, fun g hg ↦ sup_eq_sup_of_le hg inf_le_left,
        fun g hg ↦ sup_eq_sup_of_le hg inf_le_right⟩
    · exact fun N ↦ h N.1 N.2.1 N.2.2.1 N.2.2.2
  obtain ⟨g, hg⟩ := hne
  rw [Set.mem_iInter] at hg
  refine ⟨g, ?_⟩
  rw [topologicalClosure_sup_proLKernel_eq_iInf, topologicalClosure_sup_proLKernel_eq_iInf]
  exact iInf_congr fun N ↦ iInf_congr fun hN ↦ hg ⟨N, hN⟩

end Compactness

section GaloisCategory

open PreGaloisCategory

variable {C : Type*} [Category C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

omit [GaloisCategory C] [FiberFunctor F] in
/-- For `x₀` with stabilizer `N` (normal), `k • (g • x₀) = g • h • x₀` for some `k ∈ K` iff
`h ∈ (g⁻¹ K g) N`. -/
private lemma exists_smul_eq_iff_mem {X : C} {x₀ : F.obj X} {N : Subgroup (Aut F)} [N.Normal]
    (hx₀ : MulAction.stabilizer (Aut F) x₀ = N) (K : Subgroup (Aut F)) (g h : Aut F) :
    (∃ k ∈ K, k • g • x₀ = g • h • x₀) ↔ h ∈ MulAut.conj g⁻¹ • K ⊔ N := by
  rw [mem_sup_normal_iff]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨g⁻¹ * k * g, ⟨k, hk, by simp⟩, (g⁻¹ * k * g)⁻¹ * h, ?_, by group⟩
    rw [← hx₀, MulAction.mem_stabilizer_iff, mul_smul]
    have e : h • x₀ = (g⁻¹ * k * g) • x₀ := by rw [mul_smul, mul_smul, hkx, inv_smul_smul]
    rw [e, inv_smul_smul]
  · rintro ⟨_, ⟨k, hk, rfl⟩, n, hn, rfl⟩
    refine ⟨k, hk, ?_⟩
    rw [← hx₀, MulAction.mem_stabilizer_iff] at hn
    rw [mul_smul, hn]
    change k • g • x₀ = g • (g⁻¹ * k * g⁻¹⁻¹) • x₀
    rw [inv_inv, mul_smul, mul_smul, smul_inv_smul]

/-- **Finite levels of the inertia condition, in a Galois category.** Let `H`, `A` be subgroups
of `π = Aut F` and `N` an open normal subgroup. Suppose that for every Galois object `X` there
are points `x`, `y` of `F X` such that an automorphism `φ` of `X` maps `x` into its `H`-orbit
iff it maps `y` into its `A`-orbit (the `Aut X`-sets of `H`-orbits and of `A`-orbits of `F X`
have conjugate stabilizers). Then the images of `H` and `A` in `π / N` are conjugate:
`(g H g⁻¹) N = A N` for some `g`. -/
theorem exists_conj_sup_eq_of_forall_isGalois (H A N : Subgroup (Aut F)) [hN : N.Normal]
    (ho : IsOpen (N : Set (Aut F)))
    (h : ∀ (X : C) [IsGalois X], ∃ x y : F.obj X, ∀ φ : Aut X,
      (∃ k ∈ H, k • x = F.map φ.hom x) ↔ (∃ k ∈ A, k • y = F.map φ.hom y)) :
    ∃ g : Aut F, MulAut.conj g • H ⊔ N = A ⊔ N := by
  obtain ⟨X, x₀, hX, hx₀⟩ := ExposeV.exists_isGalois_stabilizer_eq F ⟨N, ho⟩ hN
  change MulAction.stabilizer (Aut F) x₀ = N at hx₀
  obtain ⟨x, y, hxy⟩ := h X
  obtain ⟨g₁, rfl⟩ := MulAction.exists_smul_eq (Aut F) x₀ x
  obtain ⟨g₂, rfl⟩ := MulAction.exists_smul_eq (Aut F) x₀ y
  have heq : MulAut.conj g₁⁻¹ • H ⊔ N = MulAut.conj g₂⁻¹ • A ⊔ N := by
    ext h
    obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Aut X) x₀ (h • x₀)
    change F.map φ.hom x₀ = h • x₀ at hφ
    have e₁ : F.map φ.hom (g₁ • x₀) = g₁ • h • x₀ := by
      rw [← hφ]
      exact (mulAction_naturality F g₁ φ.hom x₀).symm
    have e₂ : F.map φ.hom (g₂ • x₀) = g₂ • h • x₀ := by
      rw [← hφ]
      exact (mulAction_naturality F g₂ φ.hom x₀).symm
    have := hxy φ
    rw [e₁, e₂] at this
    rw [← exists_smul_eq_iff_mem F hx₀, ← exists_smul_eq_iff_mem F hx₀]
    exact this
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have hNg (g : Aut F) : MulAut.conj g • N = N := Subgroup.Normal.conj_smul_eq_self g N
  have := congrArg (fun K ↦ MulAut.conj g₂ • K) heq
  simp only [Subgroup.smul_sup, hNg, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    at this
  exact this

end GaloisCategory

end SGA.SGA1.ExposeXIII
