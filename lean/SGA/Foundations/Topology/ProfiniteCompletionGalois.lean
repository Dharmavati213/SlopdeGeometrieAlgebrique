/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-!
# The fundamental group of finite `G`-sets is the profinite completion of `G`

For a group `G` (without topology), the category `Action FintypeCat G` of finite `G`-sets is a
Galois category and the forgetful functor is a fibre functor (mathlib,
`CategoryTheory/Galois/Examples.lean`). We show that its fundamental group is the profinite
completion `Ĝ = ProfiniteGrp.ProfiniteCompletion.completion G`:

* `Ĝ` acts on every finite `G`-set `X` through the finite quotient of `G` by the kernel of the
  action (`ProfiniteCompletion.mulActionAction`), extending the action of `G` along
  `G → Ĝ` (`ProfiniteCompletion.etaFn_smul`);
* with these actions, `Ĝ` is a fundamental group of the forgetful functor in the sense of
  `PreGaloisCategory.IsFundamentalGroup` (`ProfiniteCompletion.isFundamentalGroup`);
* hence `Aut (Action.forget FintypeCat G) ≃ₜ* Ĝ` (`ProfiniteCompletion.autForgetEquiv`).

## References

* [SGA 1, Exposé V, §4–§5][sga1]
-/

universe u

open CategoryTheory PreGaloisCategory

namespace ProfiniteGrp.ProfiniteCompletion

variable {G : Type u} [Group G]

/-- The projection from the profinite completion of `G` onto the finite quotient `G ⧸ N`. -/
def projQuotient (N : FiniteIndexNormalSubgroup G) :
    completion (GrpCat.of G) →* G ⧸ N.toSubgroup where
  toFun σ := σ.1 N
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma projQuotient_etaFn (N : FiniteIndexNormalSubgroup G) (g : G) :
    projQuotient N (etaFn (GrpCat.of G) g) = (g : G ⧸ N.toSubgroup) :=
  rfl

/-- The projections to the finite quotients are compatible. -/
lemma projQuotient_of_le (σ : completion (GrpCat.of G)) {N M : FiniteIndexNormalSubgroup G}
    (h : N ≤ M) :
    projQuotient M σ = QuotientGroup.map _ _ (MonoidHom.id G) h (projQuotient N σ) :=
  (σ.2 h.hom).symm

lemma projQuotient_eq_mk_of_le {σ : completion (GrpCat.of G)} {N M : FiniteIndexNormalSubgroup G}
    (h : N ≤ M) {g : G} (hg : projQuotient N σ = g) : projQuotient M σ = g := by
  rw [projQuotient_of_le σ h, hg]
  rfl

/-- An element of the profinite completion is trivial if all its projections are trivial. -/
lemma eq_one_of_projQuotient {σ : completion (GrpCat.of G)}
    (h : ∀ N, projQuotient N σ = 1) : σ = 1 :=
  Subtype.ext (funext h)

lemma isOpen_setOf_projQuotient_eq (N : FiniteIndexNormalSubgroup G) (q : G ⧸ N.toSubgroup) :
    IsOpen {σ : completion (GrpCat.of G) | projQuotient N σ = q} := by
  have : DiscreteTopology ((diagram (GrpCat.of G)).obj N) := ⟨rfl⟩
  have hc : Continuous fun σ : completion (GrpCat.of G) ↦ σ.1 N :=
    (continuous_apply N).comp continuous_subtype_val
  exact hc.isOpen_preimage {q} (isOpen_discrete _)

/-! ### The action on finite `G`-sets -/

/-- The kernel of the action of `G` on a finite `G`-set, a normal subgroup of finite index. -/
def kerAction (X : Action FintypeCat.{u} G) : FiniteIndexNormalSubgroup G :=
  haveI : Finite (MulAction.toPermHom G X.V).range := inferInstance
  FiniteIndexNormalSubgroup.ofSubgroup (MulAction.toPermHom G X.V).ker

lemma mem_kerAction {X : Action FintypeCat.{u} G} {g : G} :
    g ∈ (kerAction X).toSubgroup ↔ ∀ x : X.V, g • x = x := by
  change MulAction.toPermHom G X.V g = 1 ↔ _
  rw [Equiv.ext_iff]
  rfl

/-- The action of `G ⧸ N` on a finite `G`-set `X`, for `N` contained in the kernel of the
action. -/
def quotientPerm (X : Action FintypeCat.{u} G) :
    G ⧸ (kerAction X).toSubgroup →* Equiv.Perm X.V :=
  QuotientGroup.lift _ (MulAction.toPermHom G X.V) le_rfl

/-- The action of the profinite completion `Ĝ` on a finite `G`-set, through the finite quotient
of `G` by the kernel of the action. -/
instance mulActionAction (X : Action FintypeCat.{u} G) :
    MulAction (completion (GrpCat.of G)) X.V :=
  MulAction.compHom _ ((quotientPerm X).comp (projQuotient (kerAction X)))

lemma smul_def (X : Action FintypeCat.{u} G) (σ : completion (GrpCat.of G)) (x : X.V) :
    σ • x = quotientPerm X (projQuotient (kerAction X) σ) x :=
  rfl

/-- The action of `σ ∈ Ĝ` on `X` is the action of any `g ∈ G` with the same image in a finite
quotient `G ⧸ N` with `N` acting trivially on `X`. -/
lemma smul_eq_of_projQuotient_eq {X : Action FintypeCat.{u} G} {σ : completion (GrpCat.of G)}
    {N : FiniteIndexNormalSubgroup G} (hN : N ≤ kerAction X) {g : G}
    (hg : projQuotient N σ = g) (x : X.V) : σ • x = g • x := by
  rw [smul_def, projQuotient_eq_mk_of_le hN hg]
  rfl

@[simp]
lemma etaFn_smul (X : Action FintypeCat.{u} G) (g : G) (x : X.V) :
    etaFn (GrpCat.of G) g • x = g • x :=
  smul_eq_of_projQuotient_eq le_rfl rfl x

lemma exists_smul_eq_smul (X Y : Action FintypeCat.{u} G) (σ : completion (GrpCat.of G)) :
    ∃ g : G, (∀ x : X.V, σ • x = g • x) ∧ ∀ y : Y.V, σ • y = g • y := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (projQuotient (kerAction X ⊓ kerAction Y) σ)
  exact ⟨g, smul_eq_of_projQuotient_eq inf_le_left hg.symm,
    smul_eq_of_projQuotient_eq inf_le_right hg.symm⟩

lemma isOpen_stabilizer (X : Action FintypeCat.{u} G) (x : X.V) :
    IsOpen (MulAction.stabilizer (completion (GrpCat.of G)) x :
      Set (completion (GrpCat.of G))) := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  exact ⟨_, fun τ (hτ : projQuotient (kerAction X) τ = projQuotient (kerAction X) σ) ↦ by
    change τ • x = x
    rwa [smul_def, hτ, ← smul_def], isOpen_setOf_projQuotient_eq _ _, rfl⟩

variable (G) in
instance (X : Action FintypeCat.{u} G) :
    MulAction (completion (GrpCat.of G)) ((Action.forget FintypeCat G).obj X) :=
  mulActionAction X

variable (G) in
/-- The profinite completion of `G` is a fundamental group of the forgetful functor from finite
`G`-sets to finite sets. -/
instance isFundamentalGroup :
    IsFundamentalGroup (Action.forget FintypeCat.{u} G) (completion (GrpCat.of G)) where
  naturality σ X Y f x := by
    obtain ⟨g, hX, hY⟩ := exists_smul_eq_smul X Y σ
    exact (congrArg f.hom (hX x)).trans (congr($(f.comm g) x).trans (hY _).symm)
  transitive_of_isGalois X _ := by
    have := FintypeCat.Action.pretransitive_of_isConnected G X
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (show X.V from x) y
    exact ⟨etaFn (GrpCat.of G) g, (etaFn_smul X g x).trans hg⟩
  continuous_smul X := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    exact isOpen_stabilizer X
  non_trivial' σ h := by
    refine eq_one_of_projQuotient fun N ↦ ?_
    have : Fintype (G ⧸ N.toSubgroup) := Fintype.ofFinite _
    let X : Action FintypeCat.{u} G := G ⧸ₐ N.toSubgroup
    have hN : N ≤ kerAction X := fun g hg ↦ mem_kerAction.mpr fun x ↦ by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      change ((g * a : G) : G ⧸ N.toSubgroup) = a
      rw [QuotientGroup.eq, mul_inv_rev]
      simpa using N.isNormal'.conj_mem _ (inv_mem hg) a⁻¹
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (projQuotient N σ)
    have h1 : σ • (show X.V from ((1 : G) : G ⧸ N.toSubgroup)) =
        (show X.V from ((1 : G) : G ⧸ N.toSubgroup)) := h X _
    rw [smul_eq_of_projQuotient_eq hN hg.symm] at h1
    change ((g * 1 : G) : G ⧸ N.toSubgroup) = (1 : G) at h1
    rw [← hg, ← QuotientGroup.mk_one, ← h1, mul_one]

variable (G) in
/-- The automorphism group of the forgetful functor on finite `G`-sets is the profinite
completion of `G`, as a topological group. -/
noncomputable def autForgetEquiv :
    Aut (Action.forget FintypeCat.{u} G) ≃ₜ* completion (GrpCat.of G) :=
  let e := toAutMulEquiv (Action.forget FintypeCat.{u} G) (completion (GrpCat.of G))
  have he := toAutMulEquiv_isHomeomorph (Action.forget FintypeCat.{u} G)
    (completion (GrpCat.of G))
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := he.continuous
      continuous_invFun := he.homeomorph.symm.continuous }

variable (G) in
@[simp]
lemma autForgetEquiv_symm_apply_hom_app (σ : completion (GrpCat.of G))
    (X : Action FintypeCat.{u} G) (x : X.V) :
    ((autForgetEquiv G).symm σ).hom.app X x = σ • x :=
  rfl

end ProfiniteGrp.ProfiniteCompletion
