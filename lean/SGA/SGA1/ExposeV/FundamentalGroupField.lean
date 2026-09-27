/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Algebra.CharP.IntermediateField
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé V, §8: the fundamental group of a field and the absolute Galois group

V.8.1 identifies `π₁(Spec k, a)` with the Galois group of the separable closure `k̄` of `k` in
`Ω` (`etaleFundamentalGroupContinuousMulEquivGal`). The proof of V.8.1 also uses that the natural
map from the group `π'` of `k`-automorphisms of the algebraic closure `k'` to `Gal(k̄/k)` is an
isomorphism ("it is well known"). We prove it: for a normal extension `K/k`, restriction to the
separable closure of `k` in `K` is an isomorphism of topological groups
`Gal(K/k) ≃ₜ* Gal(k̄/k)` (`galRestrictSeparableClosure`), since `K/k̄` is purely inseparable.

Consequently, for the geometric point `Spec k̄ᵃˡᵍ → Spec k` given by an algebraic closure,
`π₁(Spec k) ≅ Field.absoluteGaloisGroup k` (`etaleFundamentalGroupEquivAbsoluteGaloisGroup`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

section GaloisRestriction

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]

/-- A `k`-automorphism of an algebraic extension `K` which is the identity on the separable
closure of `k` in `K` is the identity (`K` is purely inseparable over it). -/
lemma eq_one_of_forall_mem_separableClosure [Algebra.IsAlgebraic k K] (σ : Gal(K/k))
    (hσ : ∀ x ∈ separableClosure k K, σ x = x) : σ = 1 := by
  let E := separableClosure k K
  let σ' : K →ₐ[E] K :=
    { (σ : K ≃ₐ[k] K).toRingEquiv.toRingHom with commutes' := fun e ↦ hσ e e.2 }
  have h := Subsingleton.elim σ' (AlgHom.id E K)
  ext x
  exact congr($h x)

variable [Normal k K]

/-- V.8.1 (proof): restriction of `k`-automorphisms of a normal extension `K` to the separable
closure of `k` in `K` is injective. -/
lemma restrictNormalHom_separableClosure_injective :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) (separableClosure k K)) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact eq_one_of_forall_mem_separableClosure k K σ
    ((AlgEquiv.restrictNormal_eq_one_iff _ σ).mp hσ)

lemma restrictNormalHom_separableClosure_bijective :
    Function.Bijective
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) (separableClosure k K)) :=
  ⟨restrictNormalHom_separableClosure_injective k K,
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := separableClosure k K) K⟩

/-- If `σ ∈ Gal(K/k)` restricts to an automorphism of the separable closure fixing the separable
part `M` of a subfield `L`, then `σ` fixes `L`. -/
lemma mem_fixingSubgroup_of_restrictNormal (L : IntermediateField k K) (σ : Gal(K/k))
    (hσ : ∀ e : separableClosure k K, (e : K) ∈ L →
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) (separableClosure k K) σ e = e) :
    σ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let q := ringExpChar K
  obtain ⟨n, e, he⟩ := IsPurelyInseparable.pow_mem (separableClosure k K) q x
  have heL : ((e : separableClosure k K) : K) ∈ L := by
    change algebraMap (separableClosure k K) K e ∈ L
    rw [he]
    exact pow_mem hx _
  have hfix : σ (x ^ q ^ n) = x ^ q ^ n := by
    rw [← he]
    have := congrArg (fun y : separableClosure k K ↦ (y : K)) (hσ e heL)
    simp only [AlgEquiv.restrictNormalHom_apply] at this
    exact this
  rw [map_pow] at hfix
  exact iterateFrobenius_inj K q n hfix

/-- V.8.1 (proof, "it is well known"): for a normal extension `K/k`, restriction to the separable
closure `k̄` of `k` in `K` is an isomorphism of topological groups `Gal(K/k) ≃ₜ* Gal(k̄/k)`. -/
noncomputable def galRestrictSeparableClosure : Gal(K/k) ≃ₜ* Gal(separableClosure k K/k) :=
  let f := AlgEquiv.restrictNormalHom (F := k) (K₁ := K) (separableClosure k K)
  let e := MulEquiv.ofBijective f (restrictNormalHom_separableClosure_bijective k K)
  { e with
    continuous_toFun := InfiniteGalois.restrictNormalHom_continuous (separableClosure k K)
    continuous_invFun := by
      change Continuous e.symm.toMonoidHom
      refine continuous_of_continuousAt_one _ ?_
      rw [ContinuousAt, map_one]
      intro A hA
      obtain ⟨L, hL, hLA⟩ := (krullTopology_mem_nhds_one_iff k K A).mp hA
      let M : IntermediateField k (separableClosure k K) :=
        IntermediateField.comap (separableClosure k K).val L
      have : FiniteDimensional k M := by
        let g : M →ₗ[k] L :=
          { toFun := fun x ↦ ⟨(x : separableClosure k K), x.2⟩
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        refine Module.Finite.of_injective g fun x y hxy ↦ ?_
        have := congrArg (fun z : L ↦ (z : K)) hxy
        exact Subtype.ext (Subtype.ext this)
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (M.fixingSubgroup_isOpen.mem_nhds M.fixingSubgroup.one_mem)
        fun τ hτ ↦ hLA ?_
      change e.symm τ ∈ L.fixingSubgroup
      refine mem_fixingSubgroup_of_restrictNormal k K L _ fun m hm ↦ ?_
      have hτ' : τ m = m := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ m hm
      exact (congrArg (fun ρ : Gal(separableClosure k K/k) ↦ ρ m) (e.apply_symm_apply τ)).trans
        hτ' }

lemma galRestrictSeparableClosure_apply (σ : Gal(K/k)) (x : separableClosure k K) :
    ((galRestrictSeparableClosure k K σ x : separableClosure k K) : K) = σ x :=
  AlgEquiv.restrictNormalHom_apply _ σ x

end GaloisRestriction

section SpecPoint

variable (R : CommRingCat.{u}) (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- For the geometric point `specPoint R Ω : Spec Ω → Spec R` of an `R`-algebra `Ω`, the fiber
functor of `FEt (Spec R)` is `A ↦ Hom_R(A, Ω)`. -/
noncomputable def FEt.fiberSpecPointIso [IsSepClosed Ω] [ConnectedSpace (PrimeSpectrum R)] :
    FEt.fiber Ω (specPoint R Ω) ≅ geometricFiber R Ω :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl
    (FEt.fiberInclIso Ω (specPoint R Ω) ≪≫ (geometricFiberInclIso R Ω).symm)

variable (k : Type u) [Field k] [Algebra k Ω] [IsSepClosed Ω]

/-- V.8.1: `π₁(Spec k, a) ≅ Gal(k̄/k)` at the geometric point `a : Spec Ω → Spec k` given by an
algebra structure on `Ω`, where `k̄` is the separable closure of `k` in `Ω`. -/
noncomputable def etaleFundamentalGroupSpecPointEquivGal :
    etaleFundamentalGroup Ω (specPoint (CommRingCat.of k) Ω) ≃ₜ*
      Gal(separableClosure k Ω/k) :=
  (autContinuousMulEquiv (specEquivalence (CommRingCat.of k)).inverse
    (FEt.fiberSpecPointIso (CommRingCat.of k) Ω).symm).symm.trans
    (fundamentalGroupContinuousMulEquivGal k Ω)

/-- V.8.1: for `Ω` separably closed and normal over `k` (e.g. algebraically closed), `π₁(Spec k, a)`
is the group of `k`-automorphisms of `Ω`. -/
noncomputable def etaleFundamentalGroupSpecPointEquivAut [Normal k Ω] :
    etaleFundamentalGroup Ω (specPoint (CommRingCat.of k) Ω) ≃ₜ* Gal(Ω/k) :=
  (etaleFundamentalGroupSpecPointEquivGal Ω k).trans (galRestrictSeparableClosure k Ω).symm

/-- V.8.1: the fundamental group of `Spec k` at the geometric point given by an algebraic closure
of `k` is the absolute Galois group of `k`. -/
noncomputable def etaleFundamentalGroupEquivAbsoluteGaloisGroup (k : Type u) [Field k] :
    etaleFundamentalGroup (AlgebraicClosure k) (specPoint (CommRingCat.of k) (AlgebraicClosure k))
      ≃ₜ* Field.absoluteGaloisGroup k :=
  etaleFundamentalGroupSpecPointEquivAut (AlgebraicClosure k) k

end SpecPoint

end SGA.SGA1.ExposeV
