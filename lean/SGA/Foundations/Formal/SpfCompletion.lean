/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness
import SGA.Foundations.Formal.Spf

/-!
# `Spf` of a ring and of its completion

For a finitely generated ideal `I` of a ring `A`, with `I`-adic completion `Â`, the formal spectra
`Spf A` (for `I`) and `Spf Â` (for `I Â`) agree (EGA I, §10.1): they are the colimits of the same
thickening sequence `Spec (A ⧸ Iⁿ⁺¹) = Spec (Â ⧸ Iⁿ⁺¹ Â)`. In particular `Γ(Spf A, 𝒪) = Â`
(`Spf.ΓIsoAdicCompletion`), and the formal completion of an affine scheme `Spec A` along `V(I)` is
the formal spectrum of the complete ring `Â`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AdicCompletion

variable {A : Type u} [CommRing A] (I : Ideal A)

lemma factor_evalₐ {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h f =>
    rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    have := f.property h
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    simpa using neg_mem this

/-- The ideal `I Â` of the completion. -/
noncomputable abbrev completionIdeal : Ideal (AdicCompletion I A) :=
  I.map (algebraMap A (AdicCompletion I A))

lemma evalₐ_eq_zero_of_mem_pow {n : ℕ} {x : AdicCompletion I A}
    (hx : x ∈ completionIdeal I ^ n) : evalₐ I n x = 0 := by
  rw [← Ideal.map_pow] at hx
  have : (I ^ n).map (algebraMap A (AdicCompletion I A)) ≤ RingHom.ker (evalₐ I n) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  exact this hx

lemma pow_le_ker_evalₐ (n : ℕ) :
    completionIdeal I ^ n ≤ RingHom.ker (evalₐ I n).toRingHom :=
  fun _ hx ↦ RingHom.mem_ker.mpr (evalₐ_eq_zero_of_mem_pow I hx)

lemma mem_pow_of_evalₐ_eq_zero (hI : I.FG) {n : ℕ} {x : AdicCompletion I A}
    (hx : evalₐ I n x = 0) : x ∈ completionIdeal I ^ n := by
  have h₁ : eval I A n x = 0 := by
    rw [← factor_evalₐ_eq_eval I x (by simp), hx, _root_.map_zero]
  have h₂ : x ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) := by
    rw [pow_smul_top_eq_ker_eval hI]
    exact h₁
  rw [Ideal.smul_top_eq_map, Ideal.map_pow] at h₂
  exact h₂

/-- Two ring maps out of the completion which agree on `A` and kill `(I Â)ᵏ` are equal
(`I` finitely generated), since `Â = A + (I Â)ᵏ`. -/
lemma ringHom_ext_of_pow (hI : I.FG) {R : Type*} [CommRing R] {k : ℕ}
    {f g : AdicCompletion I A →+* R}
    (hfg : f.comp (algebraMap A _) = g.comp (algebraMap A _))
    (hf : completionIdeal I ^ k ≤ RingHom.ker f) (hg : completionIdeal I ^ k ≤ RingHom.ker g) :
    f = g := by
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I k x)
  have hmem : x - algebraMap A _ a ∈ completionIdeal I ^ k := by
    refine mem_pow_of_evalₐ_eq_zero I hI ?_
    rw [_root_.map_sub, ← ha, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, evalₐ_of, sub_self]
  rw [← sub_add_cancel x (algebraMap A _ a), _root_.map_add, _root_.map_add,
    RingHom.mem_ker.mp (hf hmem), RingHom.mem_ker.mp (hg hmem), zero_add, zero_add]
  exact congr($hfg a)

lemma pow_le_ker_lift_comp_evalₐ (n m : ℕ)
    (h : ∀ a ∈ I ^ (m + 1),
      ((Ideal.Quotient.mk (completionIdeal I ^ (n + 1))).comp (algebraMap A _)) a = 0) :
    completionIdeal I ^ (n + 1) ≤ RingHom.ker ((Ideal.Quotient.lift (I ^ (m + 1))
      ((Ideal.Quotient.mk (completionIdeal I ^ (n + 1))).comp (algebraMap A _)) h).comp
        (evalₐ I (m + 1)).toRingHom) := by
  refine (Ideal.map_pow _ I (n + 1)).ge.trans ?_
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, evalₐ_of, Ideal.Quotient.lift_mk, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

end AdicCompletion

namespace AlgebraicGeometry.Spf

open AdicCompletion

variable {A : Type u} [CommRing A] {I : Ideal A}

lemma fromSpec_congr {C : CommRingCat.{u}} {ψ ψ' : A →+* C} (e : ψ = ψ') (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) (h' : I ^ (n + 1) ≤ RingHom.ker ψ') :
    fromSpec ψ n h = fromSpec ψ' n h' := by
  subst e
  rfl

variable (A I)

/-- The morphism `Spf A ⟶ Spf Â`, given at level `n` by `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spf Â` induced by
`Â → A ⧸ Iⁿ⁺¹`. -/
noncomputable def toCompletion : Spf A I ⟶ Spf (AdicCompletion I A) (completionIdeal I) :=
  Scheme.formalColimit.desc (diagram A I)
    (fun n ↦ fromSpec (C := .of (A ⧸ I ^ (n + 1))) (evalₐ I (n + 1)).toRingHom n
      (pow_le_ker_evalₐ I (n + 1)))
    (fun n ↦ by
      rw [Spec_map_fromSpec]
      refine (fromSpec_congr ?_ _ _ ?_).trans (fromSpec_eq _ _ _ _ _)
      · ext x
        exact factor_evalₐ I (Nat.le_succ (n + 1)) x
      · exact (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))).trans (pow_le_ker_evalₐ I (n + 1)))

lemma ι_toCompletion (n : ℕ) :
    ι A I n ≫ toCompletion A I = fromSpec (C := .of (A ⧸ I ^ (n + 1)))
      (evalₐ I (n + 1)).toRingHom n (pow_le_ker_evalₐ I (n + 1)) :=
  Scheme.formalColimit.ι_desc (diagram A I) _ _ n

lemma fromSpec_toCompletion {C : CommRingCat.{u}} (ψ : A →+* C) (m : ℕ)
    (h : I ^ (m + 1) ≤ RingHom.ker ψ) :
    fromSpec ψ m h ≫ toCompletion A I = fromSpec
      ((Ideal.Quotient.lift _ ψ fun _ ha ↦ RingHom.mem_ker.mp (h ha)).comp
        (evalₐ I (m + 1)).toRingHom) m
      ((pow_le_ker_evalₐ I (m + 1)).trans fun x hx ↦ by
        rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp hx, _root_.map_zero]) := by
  rw [fromSpec, Category.assoc, ι_toCompletion, Spec_map_fromSpec]
  rfl

lemma completionIdeal_le_comap : I ^ 1 ≤ (completionIdeal I).comap (algebraMap A _) := by
  rw [pow_one]
  exact Ideal.le_comap_map

/-- For `I` finitely generated, `Spf A` computed with `I` and `Spf Â` computed with `I Â` agree
(EGA I, §10.1). -/
noncomputable def isoCompletion (hI : I.FG) :
    Spf A I ≅ Spf (AdicCompletion I A) (completionIdeal I) where
  hom := toCompletion A I
  inv := map (algebraMap A (AdicCompletion I A)) ⟨1, completionIdeal_le_comap A I⟩
  hom_inv_id := by
    refine hom_ext fun n ↦ ?_
    rw [← Category.assoc, ι_toCompletion, Category.comp_id, ι_eq_fromSpec]
    rw [fromSpec_map (m := n) (h' := ?_)]
    · refine fromSpec_congr ?_ _ _ _
      ext a
      exact evalₐ_of I (n + 1) a
    · intro a ha
      simpa [RingHom.mem_ker] using ha
  inv_hom_id := by
    refine hom_ext fun n ↦ ?_
    rw [← Category.assoc, ι_map, fromSpec_toCompletion, Category.comp_id, ι_eq_fromSpec]
    refine (fromSpec_eq _ _ n _ (pow_le_ker_lift_comp_evalₐ I n _ _)).trans
      (fromSpec_congr ?_ n (pow_le_ker_lift_comp_evalₐ I n _ _) _)
    refine ringHom_ext_of_pow I hI ?_ (pow_le_ker_lift_comp_evalₐ I n _ _) Ideal.mk_ker.symm.le
    ext a
    simp [AdicCompletion.algebraMap_apply]

/-- `Γ(Spf A, 𝒪) = Â` for `I` finitely generated (EGA I, §10.1): the global sections of the
formal spectrum are the `I`-adic completion. -/
noncomputable def ΓIsoAdicCompletion (hI : I.FG) :
    LocallyRingedSpace.Γ.obj (op (Spf A I)) ≅ .of (AdicCompletion I A) :=
  have : IsAdicComplete (completionIdeal I) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hI)
  (LocallyRingedSpace.Γ.mapIso (isoCompletion A I hI).op).symm ≪≫ ΓIso _ _

end AlgebraicGeometry.Spf
