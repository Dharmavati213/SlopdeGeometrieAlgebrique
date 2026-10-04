/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.TateModulePrimeToP

/-!
# SGA 1, Exposé XI.2.1: `T(A) = ∏_ℓ T_ℓ(A)`, and the two parts of XI.2.1 are equivalent

XI.2.1 displays `T.(A) = ∏_ℓ T_ℓ(A) = lim K_n`: `tateModuleEquivPi` is the isomorphism of
topological groups `T(G) ≃ ∏_ℓ T_ℓ(G)`, `x ↦ (x_{ℓ^r})_{ℓ, r}`, for any commutative group object
`G` (the `n`-th component of the inverse is the product over the primes `ℓ ∣ n` of the `n`-th
components of the sections `tateModuleOfAt`).

With it, the first part of XI.2.1 (`AbelianVarietyFundamentalGroupConclusion`) follows from its
`ℓ`-primary clauses for all primes `ℓ`
(`abelianVarietyFundamentalGroupConclusion_of_forall_primaryComponent`), the converse of
`abelianVarietyPrimaryComponent_of_conclusion`. The canonical map `T(A) → π₁(A, 0)` is then an
isomorphism:

* the isomorphisms of the `ℓ`-primary clauses are the canonical ones
  (`eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt`);
* `T(A)` is compact, since each `T_ℓ(A)` is homeomorphic to the `ℓ`-primary component of
  `π₁(A, 0)`, which is closed (`isClosed_primaryComponent`);
* `T(A)` acts faithfully: if `x` acts trivially, so do its `ℓ`-primary parts, whose components
  are powers of those of `x` (`exists_coe_tateModuleOfAt_tateModuleToAt_apply_eq_pow`);
* `T(A)` acts transitively on the fibres of connected coverings: the `ℓ`-primary components
  generate a dense subgroup of the profinite abelian group `π₁(A, 0)`
  (`exists_mem_inv_mul_mem_of_primaryComponent_subset`).

So the two parts of XI.2.1 are equivalent
(`abelianVarietyFundamentalGroupStatement_iff_primaryComponentStatement`). Since the `ℓ`-primary
clauses for `ℓ` invertible in `k` are proved (`TateModulePrimeToP`), in characteristic `p > 0`
the first part is equivalent to the `p`-primary clause alone
(`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`). That clause, or
`MulNIsogenyStatement` for `n = p`, is what remains open.
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Product

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G : C} [GrpObj G] [IsCommMonObj G]

/-- An element `x ∈ T(G)` whose components `x_{ℓ^r}` are all trivial is trivial: for every
prime `ℓ`, `x_n^m = x_{ℓ^v} = 1` where `n = ℓ^v m`, `ℓ ∤ m`, so the order of `x_n` has no prime
factor. -/
lemma eq_one_of_forall_tateModuleToAt_eq_one {x : tateModule G}
    (h : ∀ ℓ : Nat.Primes, tateModuleToAt ℓ.2.pos x = 1) : x = 1 := by
  refine Subtype.ext (funext fun n ↦ Subtype.ext ?_)
  change (x.1 n : 𝟙_ C ⟶ G) = 1
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  have hdvd (ℓ : ℕ) (hℓ : ℓ.Prime) : orderOf (x.1 n : 𝟙_ C ⟶ G) ∣ ordCompl[ℓ] (n : ℕ) := by
    apply orderOf_dvd_of_pow_eq_one
    let m : ℕ+ := ⟨ordCompl[ℓ] (n : ℕ), Nat.ordCompl_pos ℓ hn⟩
    have hnm : ℓ.toPNat hℓ.pos ^ ((n : ℕ).factorization ℓ) * m = n :=
      PNat.eq (Nat.ordProj_mul_ordCompl_eq_self (n : ℕ) ℓ)
    have h1 := pow_tateModule x (ℓ.toPNat hℓ.pos ^ ((n : ℕ).factorization ℓ)) m
    rw [tateModule_apply_congr x hnm] at h1
    have h2 := congrArg (fun z : tateModuleAt G ℓ ↦ (z.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G))
      (h ⟨ℓ, hℓ⟩)
    simp only [tateModuleToAt_apply] at h2
    exact h1.trans h2
  rw [← orderOf_eq_one_iff]
  by_contra hne
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
  exact Nat.not_dvd_ordCompl hℓ hn (hℓd.trans (hdvd ℓ hℓ))

/-- The `n`-th component of the element of `T(G)` with `ℓ`-primary parts `z_ℓ`: the product over
the primes `ℓ ∣ n` of the `n`-th components of the `tateModuleOfAt (z_ℓ)`. -/
noncomputable def tateModuleOfPiFun (z : (ℓ : Nat.Primes) → tateModuleAt G ℓ) (n : ℕ+) :
    torsionPoints G n :=
  ∏ ℓ ∈ ((n : ℕ).primeFactors.subtype Nat.Prime : Finset Nat.Primes),
    (tateModuleOfAt ℓ.2 (z ℓ)).1 n

/-- The product defining `tateModuleOfPiFun` can be taken over any finite set of primes
containing the prime factors of `n`. -/
lemma coe_tateModuleOfPiFun_eq_prod (z : (ℓ : Nat.Primes) → tateModuleAt G ℓ) (n : ℕ+)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ n → ℓ ∈ S) :
    (tateModuleOfPiFun z n : 𝟙_ C ⟶ G) =
      ∏ ℓ ∈ S, ((tateModuleOfAt ℓ.2 (z ℓ)).1 n : 𝟙_ C ⟶ G) := by
  rw [tateModuleOfPiFun, SubmonoidClass.coe_finsetProd]
  refine Finset.prod_subset (fun ℓ hℓ ↦ hS ℓ ?_) fun ℓ _ hℓ ↦ ?_
  · exact Nat.dvd_of_mem_primeFactors (Finset.mem_subtype.mp hℓ)
  · refine coe_tateModuleOfAt_apply_of_not_dvd ℓ.2 _ fun hdvd ↦ hℓ ?_
    exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨ℓ.2, hdvd, n.ne_zero⟩)

/-- The inverse of `tateModuleEquivPi`: the element of `T(G)` with `ℓ`-primary parts `z_ℓ`. -/
noncomputable def tateModuleOfPi (z : (ℓ : Nat.Primes) → tateModuleAt G ℓ) : tateModule G :=
  ⟨tateModuleOfPiFun z, fun n s ↦ by
    let S : Finset Nat.Primes := ((n * s : ℕ+) : ℕ).primeFactors.subtype Nat.Prime
    have hS (m : ℕ+) (hm : (m : ℕ) ∣ (n * s : ℕ+)) (ℓ : Nat.Primes) (h : (ℓ : ℕ) ∣ m) : ℓ ∈ S :=
      Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨ℓ.2, h.trans hm, (n * s).ne_zero⟩)
    rw [coe_tateModuleOfPiFun_eq_prod z (n * s) S (hS _ dvd_rfl),
      coe_tateModuleOfPiFun_eq_prod z n S (hS n (Dvd.intro _ rfl)), ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun ℓ _ ↦ pow_tateModule _ n s⟩

lemma tateModuleToAt_tateModuleOfPi (z : (ℓ : Nat.Primes) → tateModuleAt G ℓ)
    (ℓ : Nat.Primes) : tateModuleToAt ℓ.2.pos (tateModuleOfPi z) = z ℓ := by
  refine Subtype.ext (funext fun r ↦ Subtype.ext ?_)
  rw [tateModuleToAt_apply]
  change (tateModuleOfPiFun z ((ℓ : ℕ).toPNat ℓ.2.pos ^ r) : 𝟙_ C ⟶ G) = (z ℓ).1 r
  rw [coe_tateModuleOfPiFun_eq_prod z _ {ℓ} fun ℓ' h ↦ Finset.mem_singleton.mpr
      (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ'.2 ℓ.2).mp (ℓ'.2.dvd_of_dvd_pow h))),
    Finset.prod_singleton, coe_tateModuleOfAt_apply_toPNat_pow]

lemma continuous_tateModuleOfPi :
    Continuous (tateModuleOfPi : ((ℓ : Nat.Primes) → tateModuleAt G ℓ) → tateModule G) := by
  refine continuous_induced_rng.mpr (continuous_pi fun n ↦ ?_)
  change Continuous fun z ↦ tateModuleOfPiFun z n
  refine continuous_finsetProd _ fun ℓ _ ↦ ?_
  exact (continuous_apply (A := fun n : ℕ+ ↦ torsionPoints G n) n).comp
    (continuous_subtype_val.comp ((continuous_tateModuleOfAt ℓ.2).comp (continuous_apply ℓ)))

variable (G) in
/-- XI.2.1: `T(G) = ∏_ℓ T_ℓ(G)` as topological groups, `x ↦ (x_{ℓ^r})_{ℓ, r}`
(`tateModuleToAt`). The inverse maps `(z_ℓ)` to the family whose `n`-th component is the product
over the primes `ℓ ∣ n` of the `n`-th components of the `tateModuleOfAt (z_ℓ)`. -/
noncomputable def tateModuleEquivPi : tateModule G ≃ₜ* ((ℓ : Nat.Primes) → tateModuleAt G ℓ) where
  toFun x ℓ := tateModuleToAt ℓ.2.pos x
  invFun := tateModuleOfPi
  left_inv x := by
    refine (mul_inv_eq_one.mp (eq_one_of_forall_tateModuleToAt_eq_one fun ℓ ↦ ?_)).symm
    rw [map_mul, map_inv, tateModuleToAt_tateModuleOfPi, mul_inv_cancel]
  right_inv z := funext fun ℓ ↦ tateModuleToAt_tateModuleOfPi z ℓ
  map_mul' x y := funext fun ℓ ↦ map_mul (tateModuleToAt ℓ.2.pos) x y
  continuous_toFun := continuous_pi fun ℓ ↦ continuous_tateModuleToAt ℓ.2.pos
  continuous_invFun := continuous_tateModuleOfPi

lemma tateModuleEquivPi_apply (x : tateModule G) (ℓ : Nat.Primes) :
    tateModuleEquivPi G x ℓ = tateModuleToAt ℓ.2.pos x :=
  rfl

/-- `T(G)` is compact as soon as every `T_ℓ(G)` is. -/
lemma compactSpace_tateModule_of_forall_compactSpace
    (h : ∀ ℓ : Nat.Primes, CompactSpace (tateModuleAt G ℓ)) : CompactSpace (tateModule G) :=
  (tateModuleEquivPi G).toHomeomorph.symm.compactSpace

end Product

section AbelianVariety

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A]
  [IsCommMonObj A] [IsProper A.hom] [IsReduced A.left] [ConnectedSpace A.left]

/-- If `x ∈ T(A)` acts trivially on the fibres of all étale coverings, so does its `ℓ`-primary
part: its components are powers of those of `x`. -/
lemma tateModuleOfAt_tateModuleToAt_smul_eq {ℓ : ℕ} (hℓ : ℓ.Prime) {x : tateModule A}
    (hx : ∀ (Y : ExposeV.FEt A.left) (y : (originFiber A).obj Y), x • y = y)
    (Y : ExposeV.FEt A.left) (y : (originFiber A).obj Y) :
    tateModuleOfAt hℓ (tateModuleToAt hℓ.pos x) • y = y := by
  obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
  obtain ⟨e, he⟩ := exists_coe_tateModuleOfAt_tateModuleToAt_apply_eq_pow hℓ x (liftDegree Y)
  have hxe : x ^ e • y = y := (MulAction.stabilizer (tateModule A) y).pow_mem (hx Y y) e
  have h1 := fiberPoint_tateModule_smul (x ^ e) y _ hg hg0
  rw [hxe, coe_tateModule_pow_apply] at h1
  apply ExposeV.FEt.fiber_ext_point
  rw [fiberPoint_tateModule_smul _ y _ hg hg0, he]
  exact h1.symm

/-- XI.2.1: the first part follows from the `ℓ`-primary clauses for all primes `ℓ` (the converse
of `abelianVarietyPrimaryComponent_of_conclusion`). The isomorphisms of the `ℓ`-primary clauses
being the canonical ones, the canonical map `T(A) → π₁(A, 0)` is an isomorphism: `T(A)` is compact
(each `T_ℓ(A)` is homeomorphic to the closed `ℓ`-primary component of `π₁(A, 0)`), acts
faithfully (as its `ℓ`-primary parts do) and transitively on the fibres of connected coverings
(the `ℓ`-primary components generate a dense subgroup of `π₁(A, 0)`). -/
theorem abelianVarietyFundamentalGroupConclusion_of_forall_primaryComponent
    (h : ∀ ℓ : ℕ, ℓ.Prime → AbelianVarietyPrimaryComponentConclusion k A ℓ) :
    AbelianVarietyFundamentalGroupConclusion k A := by
  have hcomm := mul_comm_of_monObj A
  -- the isomorphisms of the `ℓ`-primary clauses are the canonical ones
  have hψ (ℓ : ℕ) (hℓ : ℓ.Prime) :
      Topology.IsEmbedding ((tateModuleToFundamentalGroup A).comp (tateModuleOfAt hℓ)) ∧
        Set.range ((tateModuleToFundamentalGroup A).comp (tateModuleOfAt hℓ)) =
          primaryComponent _ ℓ := by
    obtain ⟨ψ, hemb, hrange, hpin⟩ := h ℓ hℓ
    have he := eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt hℓ ψ
      (fun z ↦ hrange ▸ Set.mem_range_self z) hpin
    rw [← he]
    exact ⟨hemb, hrange⟩
  -- `T(A) = ∏_ℓ T_ℓ(A)` is compact
  have hcpt (ℓ : Nat.Primes) : CompactSpace (tateModuleAt A ℓ) := by
    obtain ⟨hemb, hrange⟩ := hψ ℓ ℓ.2
    have hcl : IsClosed (Set.range ((tateModuleToFundamentalGroup A).comp (tateModuleOfAt ℓ.2))) :=
      hrange ▸ isClosed_primaryComponent hcomm ℓ.2
    exact (Topology.IsClosedEmbedding.mk hemb hcl).compactSpace
  have := compactSpace_tateModule_of_forall_compactSpace hcpt
  refine exists_tateModule_equiv_of_isPretransitive A (fun Y hY ↦ ⟨fun y y' ↦ ?_⟩) fun x hx ↦ ?_
  · -- transitivity: the image of `T(A)` meets every coset of the stabilizer of `y`
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut (originFiber A)) y y'
    obtain ⟨_, ⟨x, rfl⟩, hρ⟩ := exists_mem_inv_mul_mem_of_primaryComponent_subset hcomm
      (tateModuleToFundamentalGroup A).range (fun ℓ hℓ ↦ by
        rw [← (hψ ℓ hℓ).2]
        rintro _ ⟨z, rfl⟩
        exact ⟨tateModuleOfAt hℓ z, rfl⟩) σ ⟨MulAction.stabilizer _ y, stabilizer_isOpen _ y⟩
    refine ⟨x, ?_⟩
    rw [← tateModuleToFundamentalGroup_smul]
    have : (σ⁻¹ * tateModuleToFundamentalGroup A x) • y = y := hρ
    rwa [mul_smul, inv_smul_eq_iff] at this
  · -- faithfulness: the `ℓ`-primary parts of `x` act trivially, hence are trivial
    refine eq_one_of_forall_tateModuleToAt_eq_one fun ℓ ↦ (hψ ℓ ℓ.2).1.injective ?_
    rw [map_one]
    ext Y y
    exact ((tateModuleToFundamentalGroup_smul _ y).trans
      (tateModuleOfAt_tateModuleToAt_smul_eq ℓ.2 hx Y y)).trans
      (one_smul (Aut (originFiber A)) y).symm

/-- XI.2.1: the first part and the `ℓ`-primary clauses for all primes `ℓ` are equivalent. -/
theorem abelianVarietyFundamentalGroupConclusion_iff_forall_primaryComponent :
    AbelianVarietyFundamentalGroupConclusion k A ↔
      ∀ ℓ : ℕ, ℓ.Prime → AbelianVarietyPrimaryComponentConclusion k A ℓ :=
  ⟨fun h _ hℓ ↦ abelianVarietyPrimaryComponent_of_conclusion h hℓ,
    abelianVarietyFundamentalGroupConclusion_of_forall_primaryComponent⟩

end AbelianVariety

/-- XI.2.1: its two parts are equivalent: `π₁(A) ≅ T(A)` for every abelian variety `A` over an
algebraically closed field iff the `ℓ`-primary component of `π₁(A)` is `T_ℓ(A)` for every such
`A` and every prime `ℓ`. -/
theorem abelianVarietyFundamentalGroupStatement_iff_primaryComponentStatement :
    AbelianVarietyFundamentalGroupStatement.{u} ↔ AbelianVarietyPrimaryComponentStatement.{u} := by
  refine ⟨abelianVarietyPrimaryComponentStatement_of_fundamentalGroup, fun h k _ _ A _ _ _ _ ↦ ?_⟩
  have := isCommMonObj_of_smooth A
  have : IsReduced A.left := ExposeII.isReduced_of_smooth_of_isReduced A.hom
  exact abelianVarietyFundamentalGroupConclusion_of_forall_primaryComponent fun ℓ hℓ ↦ h k A ℓ hℓ

/-- XI.2.1 in characteristic `p > 0`: the first part holds for an abelian variety `A` iff its
`p`-primary clause does (the `ℓ`-primary clauses for `ℓ ≠ p` are
`abelianVarietyPrimaryComponent_of_natCast_ne_zero`). -/
theorem abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP (k : Type u)
    [Field k] [IsAlgClosed k] {p : ℕ} (hp : p.Prime) [CharP k p] (A : Over (Spec (.of k)))
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyFundamentalGroupConclusion k A ↔
      AbelianVarietyPrimaryComponentConclusion k A p := by
  have := isCommMonObj_of_smooth A
  have : IsReduced A.left := ExposeII.isReduced_of_smooth_of_isReduced A.hom
  refine ⟨fun h ↦ abelianVarietyPrimaryComponent_of_conclusion h hp, fun h ↦ ?_⟩
  refine abelianVarietyFundamentalGroupConclusion_of_forall_primaryComponent fun ℓ hℓ ↦ ?_
  by_cases hℓp : ℓ = p
  · subst hℓp
    exact h
  · refine abelianVarietyPrimaryComponent_of_natCast_ne_zero k A hℓ ?_
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact fun hdvd ↦ hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hdvd).symm

end SGA.SGA1.ExposeXI
