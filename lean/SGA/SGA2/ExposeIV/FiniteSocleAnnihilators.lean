/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.LocalSocleDuality
import SGA.SGA2.ExposeIV.LocalArtinianFiniteIdeal
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite socles and finite maximal-ideal annihilator stages

Multiplication by actual generators of an ideal maps its `(n+1)`-st
annihilator into a finite product of its `n`-th annihilator. Its kernel is
the actual first annihilator. Over a local ring with finitely generated
maximal ideal, a finite socle therefore implies that every maximal-ideal
power annihilator has finite length.

Neither finite generation nor Artinianness of the whole coefficient module
is assumed. In particular this supplies the annihilator-stage finiteness
needed for the locally Artinian modules with finite socle in IV §5.
-/

noncomputable section

universe u

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (J : Ideal R) (X : Type u) [AddCommGroup X] [Module R X]
variable (s : Finset R) (hs : Submodule.span R (s : Set R) = J)

/-- The literal multiplication map on consecutive annihilator stages. -/
def annihilatorGeneratorMap (n : ℕ) :
    Submodule.torsionBySet R X ((J ^ (n + 1) : Ideal R) : Set R) →ₗ[R]
      ((r : (s : Set R)) → Submodule.torsionBySet R X ((J ^ n : Ideal R) : Set R)) where
  toFun x r := ⟨r.val • x.val, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have hr : r.val ∈ J := by
      rw [← hs]
      exact Submodule.subset_span r.property
    have har : a.val * r.val ∈ J ^ (n + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul a.property hr
    simpa only [mul_smul] using
      (Submodule.mem_torsionBySet_iff _ _).mp x.property ⟨a.val * r.val, har⟩⟩
  map_add' x y := by
    funext r
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' a x := by
    funext r
    apply Subtype.ext
    exact smul_comm _ _ _

@[simp]
theorem annihilatorGeneratorMap_apply (n : ℕ)
    (x : Submodule.torsionBySet R X ((J ^ (n + 1) : Ideal R) : Set R)) (r : (s : Set R)) :
    ((annihilatorGeneratorMap J X s hs n x r :
      Submodule.torsionBySet R X ((J ^ n : Ideal R) : Set R)) : X) = r.val • x.val := rfl

/-- Its kernel is precisely the actual first annihilator, viewed inside
the next stage. No finiteness assumption is used in this identification. -/
theorem mem_ker_annihilatorGeneratorMap (n : ℕ)
    (x : Submodule.torsionBySet R X ((J ^ (n + 1) : Ideal R) : Set R)) :
    x ∈ (annihilatorGeneratorMap J X s hs n).ker ↔
      x.val ∈ Submodule.torsionBySet R X (J : Set R) := by
  have hspan : Ideal.span (s : Set R) = J := hs
  have hmem (a : X) : a ∈ Submodule.torsionBySet R X (J : Set R) ↔
      ∀ r : (s : Set R), r.val • a = 0 := by
    rw [← hspan, ← Submodule.torsionBySet_eq_torsionBySet_span,
      Submodule.mem_torsionBySet_iff]
  rw [hmem, LinearMap.mem_ker]
  constructor
  · intro hx r
    exact congrArg Subtype.val (congrFun hx r)
  · intro hx
    funext r
    exact Subtype.ext (hx r)

/-- The canonical identification of the kernel with the first annihilator. -/
def annihilatorGeneratorKernelEquiv (n : ℕ) :
    (annihilatorGeneratorMap J X s hs n).ker ≃ₗ[R]
      Submodule.torsionBySet R X (J : Set R) :=
  LinearEquiv.ofBijective
    { toFun := fun x ↦ ⟨x.val.val,
        (mem_ker_annihilatorGeneratorMap J X s hs n x.val).mp x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Submodule.torsionBySet R X (J : Set R) ↦ z.val) h,
      by
      intro x
      have hle : Submodule.torsionBySet R X (J : Set R) ≤
          Submodule.torsionBySet R X ((J ^ (n + 1) : Ideal R) : Set R) := by
        simpa only [pow_one] using
          (Submodule.torsionBySet_le_torsionBySet_pow (R := R) (M := X)
            1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) J)
      let y : Submodule.torsionBySet R X ((J ^ (n + 1) : Ideal R) : Set R) :=
        ⟨x.val, hle x.property⟩
      refine ⟨⟨y, (mem_ker_annihilatorGeneratorMap J X s hs n y).mpr x.property⟩, rfl⟩⟩

@[simp]
theorem annihilatorGeneratorKernelEquiv_apply (n : ℕ)
    (x : (annihilatorGeneratorMap J X s hs n).ker) :
    ((annihilatorGeneratorKernelEquiv J X s hs n x :
      Submodule.torsionBySet R X (J : Set R)) : X) = x.val.val := rfl

omit s hs in
/-- The literal annihilator stage is killed by the indicated ideal power. -/
theorem ideal_pow_le_annihilator_torsionBySet (n : ℕ) :
    J ^ n ≤ Module.annihilator R (Submodule.torsionBySet R X ((J ^ n : Ideal R) : Set R)) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  exact Subtype.ext ((Submodule.mem_torsionBySet_iff _ _).mp x.property ⟨r, hr⟩)

section Local

variable [IsLocalRing R]
variable (hm : (IsLocalRing.maximalIdeal R).FG)
variable [Module.Finite R (localSocle (R := R) X)]

include hm in
/-- Finite socle implies finite generation of every maximal-ideal-power
annihilator. A finitely generated maximal ideal suffices; the ring and the
whole module need not be noetherian or Artinian. -/
theorem maximalIdealAnnihilator_finite_of_finite_socle (n : ℕ) :
    Module.Finite R
      (Submodule.torsionBySet R X ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
  let m := IsLocalRing.maximalIdeal R
  have hsocle : IsFiniteLength R (localSocle (R := R) X) :=
    isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg hm _ 1
      (by
        rw [pow_one]
        intro r hr
        apply Module.mem_annihilator.mpr
        intro x
        exact Subtype.ext ((mem_localSocle X x.val).mp x.property r hr))
  have : IsNoetherian R (localSocle (R := R) X) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hsocle).1
  have : IsNoetherian R (Submodule.torsionBySet R X (m : Set R)) :=
    (inferInstance : IsNoetherian R (localSocle (R := R) X))
  induction n with
  | zero =>
    have hz (x : Submodule.torsionBySet R X ((m ^ 0 : Ideal R) : Set R)) : x = 0 := by
      apply Subtype.ext
      change x.val = 0
      simpa only [one_smul] using
        (Submodule.mem_torsionBySet_iff _ _).mp x.property
          ⟨1, by simp⟩
    have : Subsingleton (Submodule.torsionBySet R X ((m ^ 0 : Ideal R) : Set R)) :=
      ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    infer_instance
  | succ n ih =>
    have : Module.Finite R (Submodule.torsionBySet R X ((m ^ n : Ideal R) : Set R)) := ih
    have hlen : IsFiniteLength R (Submodule.torsionBySet R X ((m ^ n : Ideal R) : Set R)) :=
      isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg hm _ n
        (ideal_pow_le_annihilator_torsionBySet m X n)
    have : IsNoetherian R (Submodule.torsionBySet R X ((m ^ n : Ideal R) : Set R)) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
    obtain ⟨s, hs⟩ := hm
    let f := annihilatorGeneratorMap m X s hs n
    have : Module.Finite R f.ker :=
      Module.Finite.of_injective
        (annihilatorGeneratorKernelEquiv m X s hs n).toLinearMap
        (annihilatorGeneratorKernelEquiv m X s hs n).injective
    have : Module.Finite R f.range := inferInstance
    exact Module.Finite.of_exact
      (show Function.Exact f.ker.subtype f.rangeRestrict by
        rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
      f.surjective_rangeRestrict

include hm in
/-- In fact all the actual annihilator stages have finite length. -/
theorem maximalIdealAnnihilator_isFiniteLength_of_finite_socle (n : ℕ) :
    IsFiniteLength R
      (Submodule.torsionBySet R X ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
  have := maximalIdealAnnihilator_finite_of_finite_socle X hm n
  exact isFiniteLength_of_maximalIdeal_pow_annihilator_of_fg hm _ n
    (ideal_pow_le_annihilator_torsionBySet (IsLocalRing.maximalIdeal R) X n)

end Local

end SGA.SGA2.ExposeIV
