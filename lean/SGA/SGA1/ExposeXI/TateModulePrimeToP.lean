/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.TateModulePrimary

/-!
# SGA 1, Exposé XI.2.1: the `ℓ`-primary component of `π₁(A)` for `ℓ` invertible in `k`

For a prime `ℓ` invertible in `k`, the last clause of XI.2.1 (the `ℓ`-primary component of
`π₁(A)` is canonically `T_ℓ(A)`) holds with no input on `p_A`
(`abelianVarietyPrimaryComponent_of_natCast_ne_zero`): only the étale coverings `(ℓ^r)_A` are
used. The isomorphism is `T_ℓ(A) → T(A) → π₁(A, 0)` (`tateModuleOfAt` followed by the canonical
map `tateModuleToFundamentalGroup`), which is the only possible one
(`eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt`).

* injective (`injective_tateModuleToFundamentalGroup_comp_tateModuleOfAt`), since `(ℓ^r)_A` is an
  étale covering on whose fibre `K_{ℓ^r}` acts faithfully; a closed embedding since `T_ℓ(A)` is
  compact (`K_{ℓ^r}` is finite);
* onto the `ℓ`-primary component: its range is closed, and an `ℓ`-primary `σ` is matched on every
  point `y` of the fibre of an étale covering (`exists_tateModuleAt_smul_eq`). By
  `exists_primePow_lift` (Serre–Lang), `y` is reached from a lift `g'` of some `(ℓ^a)_A` through
  the pull-back `Y'` of `Y` along `m_A`, `ℓ ∤ m`, where `π₁` acts through `τ ↦ τ^m`. Since
  `(ℓ^a)_A` is an étale covering, `K_{ℓ^a}` acts transitively on the connected component of
  `g'(0)` (`exists_torsionPoints_of_lift`), which gives `z ∈ T_ℓ(A)` matching `σ` on `Y'`
  (`exists_tateModuleAt_apply_eq`). Commutativity of `π₁(A)` and `ℓ ∤ m` then remove the `m`-th
  power (`smul_eq_of_pow_smul_eq`).

With `TateModuleProduct`, this reduces the first part of XI.2.1 in characteristic `p > 0` to its
`p`-primary clause (`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] [IsReduced A.left]

/-- The key step for `ℓ` invertible in `k`: every `ℓ`-primary element `σ` of `π₁(A, 0)` agrees at
any given point `y` of the fibre of an étale covering `Y` with the image of some `z ∈ T_ℓ(A)`. -/
theorem exists_tateModuleAt_smul_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0)
    (σ : ExposeV.etaleFundamentalGroup k (unitSection A))
    (hσ : σ ∈ primaryComponent (ExposeV.etaleFundamentalGroup k (unitSection A)) ℓ)
    (Y : ExposeV.FEt A.left) (y : (originFiber A).obj Y) :
    ∃ z : tateModuleAt A ℓ, tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) • y = σ • y := by
  let F := originFiber A
  -- Serre–Lang: `y` comes from a lift `g'` of `(ℓ^a)_A` through `Y' = m_A^* Y`, `ℓ ∤ m`
  obtain ⟨a, m, Y', g', y', e, hm, hg', hy', rfl, he⟩ := exists_primePow_lift hℓ Y y
  have ha0 : unitSection A ≫ (mulN A (ℓ ^ a)).left = unitSection A := unit_comp_mulN_left A _
  -- the connected component `W` of `y'`, through which `(ℓ^a)_A` lifts
  obtain ⟨W, i, w, hiw, hW, hi⟩ := fiber_in_connected_component F Y' y'
  have hinj : Function.Injective (F.map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
  have hfixW (τ : ExposeV.etaleFundamentalGroup k (unitSection A)) :
      pointedMap k (mulN A (ℓ ^ a)).left _ _ ha0 τ • w = w := by
    apply hinj
    rw [← mulAction_naturality, hiw]
    exact pointedMap_smul_eq_of_lift _ _ _ ha0 Y' y' g' hg' hy'.symm τ
  obtain ⟨h, hh, hh0⟩ :=
    exists_lift_of_forall_smul_eq_of_apply (mulN A (ℓ ^ a)).left _ _ ha0 W w hfixW
  have hℓa : ((ℓ ^ a : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero a hℓk
  have : Surjective (mulN A (ℓ ^ a)).left := (mulNIsogeny_of_ne_zero A hℓa).2
  -- `K_{ℓ^a}` acts transitively on the fibre of `W`: `σ w = h(c)`
  obtain ⟨c, hc⟩ := exists_torsionPoints_of_lift A W h hh _
    (ExposeV.FEt.fiberPoint_comp k (σ • w))
  have hhi : h ≫ i.left = g' := by
    refine eq_of_comp_eq_of_unitSection A (Y := Y') ?_ ?_
    · rw [Category.assoc, MorphismProperty.Over.w i, hh, hg']
    · rw [← Category.assoc, hh0, ← ExposeV.FEt.fiberPoint_map, hiw, hy']
  have hσy : ExposeV.FEt.fiberPoint k (σ • y') = pointLeft A c ≫ g' := by
    rw [← hiw, mulAction_naturality, ExposeV.FEt.fiberPoint_map, hc, Category.assoc, hhi]
  -- lift `c` to `z ∈ T_ℓ(A)`; then `z` and `σ` agree at `y'`
  have hdiv (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ b', b' ^ ℓ = b := by
    have := (mulNIsogeny_of_ne_zero A hℓk).2
    exact exists_pow_eq_of_surjective A b
  obtain ⟨z, hz⟩ := exists_tateModuleAt_apply_eq hdiv a c
  refine ⟨z, ?_⟩
  have hψ : tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) • y' = σ • y' := by
    apply ExposeV.FEt.fiber_ext_point
    rw [hσy, fiberPoint_tateModuleToFundamentalGroup_tateModuleOfAt_smul hℓ z y' a hg' hy'.symm,
      hz]
  -- hence their `m`-th powers agree at `y = e(y')`; remove the `m`-th power
  exact smul_eq_of_pow_smul_eq (mul_comm_of_monObj A) (stabilizer_isOpen _ _) hm
    (tateModuleToFundamentalGroup_tateModuleOfAt_mem hℓ z) hσ (by rw [← he, ← he, hψ])

/-- The map `T_ℓ(A) → π₁(A, 0)` is injective for `ℓ` invertible in `k`: on the fibre of the étale
covering `(ℓ^r)_A`, `K_{ℓ^r}` acts faithfully. -/
theorem injective_tateModuleToFundamentalGroup_comp_tateModuleOfAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓk : (ℓ : k) ≠ 0) :
    Function.Injective ((tateModuleToFundamentalGroup A).comp (tateModuleOfAt hℓ)) := by
  refine (injective_iff_map_eq_one _).mpr fun z hz ↦ Subtype.ext (funext fun r ↦ ?_)
  have hℓr : ((ℓ ^ r : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero r hℓk
  obtain ⟨Y, g, hg, hginj⟩ := exists_lift_mulN_injective_of_ne_zero A hℓr
  have hy : (unitSection A ≫ g) ≫ Y.hom = unitSection A := by
    rw [Category.assoc, hg, unit_comp_mulN_left]
  let y := fiberMk Y (unitSection A ≫ g) hy
  have h := fiberPoint_tateModuleToFundamentalGroup_tateModuleOfAt_smul hℓ z y r hg
    (fiberPoint_fiberMk _ _ _).symm
  have hz' : tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) = 1 := hz
  rw [hz', one_smul, fiberPoint_fiberMk] at h
  have h1 : z.1 r = 1 := by
    refine hginj _ _ ?_
    change pointLeft A (z.1 r : 𝟙_ (Over (Spec (.of k))) ⟶ A) ≫ g =
      pointLeft A (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) ≫ g
    rw [pointLeft_one]
    exact h.symm
  rw [h1]
  rfl

end Main

/-- XI.2.1, last clause, for every prime `ℓ` different from the characteristic, with no
hypothesis on `p_A`: for an abelian variety `A` over an algebraically closed field `k` and a
prime `ℓ` with `(ℓ : k) ≠ 0`, the `ℓ`-primary component of `π₁(A, 0)` is canonically isomorphic
to `T_ℓ(A)`, through `T_ℓ(A) → T(A) → π₁(A, 0)`. -/
theorem abelianVarietyPrimaryComponent_of_natCast_ne_zero (k : Type u) [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyPrimaryComponentConclusion k A ℓ := by
  have := isCommMonObj_of_smooth A
  have : IsReduced A.left := ExposeII.isReduced_of_smooth_of_isReduced A.hom
  set ψ := (tateModuleToFundamentalGroup A).comp (tateModuleOfAt hℓ)
  have hcont : Continuous ψ :=
    (continuous_tateModuleToFundamentalGroup A).comp (continuous_tateModuleOfAt hℓ)
  have hfin (r : ℕ) : Finite (torsionPoints A (ℓ ^ r)) := by
    have hℓr : ((ℓ ^ r : ℕ) : k) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero r hℓk
    have := (mulNIsogeny_of_ne_zero A hℓr).1
    exact finite_torsionPoints A
  have := compactSpace_tateModuleAt hfin
  have hinj := injective_tateModuleToFundamentalGroup_comp_tateModuleOfAt A hℓ hℓk
  refine ⟨ψ, (hcont.isClosedEmbedding hinj).isEmbedding, ?_, fun Y r g hg y hy z ↦
    fiberPoint_tateModuleToFundamentalGroup_tateModuleOfAt_smul hℓ z y r hg hy.symm⟩
  refine (Set.range_subset_iff.mpr (tateModuleToFundamentalGroup_tateModuleOfAt_mem hℓ)).antisymm
    fun σ hσ ↦ ?_
  -- the range is closed; an `ℓ`-primary `σ` is in its closure
  have hcl : IsClosed (Set.range ψ) := (isCompact_range hcont).isClosed
  change σ ∈ Set.range ψ
  rw [← hcl.closure_eq, mem_closure_iff_nhds]
  intro t ht
  have ht1 : (fun τ ↦ σ * τ) ⁻¹' t ∈ nhds (1 : ExposeV.etaleFundamentalGroup k (unitSection A)) :=
    (continuous_const_mul σ).continuousAt.preimage_mem_nhds (by rwa [_root_.mul_one])
  obtain ⟨X, -, hsub⟩ := (nhds_one_has_basis_stabilizers (originFiber A)).mem_iff.mp ht1
  obtain ⟨z, hz⟩ := exists_tateModuleAt_smul_eq A hℓ hℓk σ hσ X.obj X.pt
  refine ⟨ψ z, ?_, z, rfl⟩
  have hmem : σ⁻¹ * ψ z ∈ MulAction.stabilizer _ X.pt := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    change σ⁻¹ • tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) • X.pt = X.pt
    rw [hz, inv_smul_smul]
  have := hsub hmem
  simpa using this

end SGA.SGA1.ExposeXI
