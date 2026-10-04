/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Basic

/-!
# Coverings of a product with a contractible factor

Let `p : C → B × F` be a covering map, and `h : I × B → B` a contraction of `B` to `b₀`
(`h(0, b) = b₀`, `h(1, b) = b`). Then `C` is the product of `B` with the part `C₀` of `C` over the
slice `{b₀} × F` (`RiemannHigher.sliceHomeomorph`, with `proj_sliceHomeomorph`): the point over
`(b, f)` coming from `c ∈ C₀` over `(b₀, f)` is the end of the lift of the path
`t ↦ (h(t, b), f)` starting at `c`, and the inverse lifts the reversed path. Both are continuous by
the homotopy lifting property of covering maps (mathlib's `IsCoveringMap.liftHomotopy`), and they
are inverse by uniqueness of lifts (`IsCoveringMap.eq_of_comp_eq`).

This is the topological input of the parameter-space argument in the proof of XII.5.1 in higher
dimension (`SGA.SGA1.ExposeXII.RiemannHigher`): over a contractible piece of the base of a locally
trivial family of curves, coverings of the total space are constant along the base. General
topology; reference: Hatcher, *Algebraic topology*, Proposition 1.30 (homotopy lifting).
-/
noncomputable section

open Topology unitInterval

namespace SGA.SGA1.ExposeXII.RiemannHigher

section Contraction

variable {B F C : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace C]
  {p : C → B × F} (hp : IsCoveringMap p) {b₀ : B} (h : C(I × B, B))
  (h₀ : ∀ b, h (0, b) = b₀) (h₁ : ∀ b, h (1, b) = b)

/-- The part of a covering `C → B × F` lying over the slice `{b₀} × F`. -/
abbrev SliceSpace (p : C → B × F) (b₀ : B) : Type _ := {c : C // (p c).1 = b₀}

include hp in
/-- The homotopy `(t, (b, c)) ↦ (h(t, b), p_F(c))`, from the slice to `(b, p_F c)`. -/
def sliceHomotopy : C(I × (B × SliceSpace p b₀), B × F) where
  toFun x := (h (x.1, x.2.1), (p x.2.2.1).2)
  continuous_toFun := by
    have := hp.continuous
    fun_prop

include h₀ in
lemma sliceHomotopy_zero (x : B × SliceSpace p b₀) :
    sliceHomotopy hp h (0, x) = p (x.2 : C) := by
  change (h (0, x.1), (p x.2.1).2) = p x.2.1
  rw [h₀]
  exact Prod.ext x.2.2.symm rfl

/-- The lift of `sliceHomotopy`, starting on the slice. -/
def sliceLift : C(I × (B × SliceSpace p b₀), C) :=
  hp.liftHomotopy (sliceHomotopy hp h) ⟨fun x ↦ x.2.1, by fun_prop⟩ (sliceHomotopy_zero hp h h₀)

include hp in
/-- The reverse homotopy `(t, x) ↦ (h(1 - t, b_x), f_x)`, from `p x` to the slice. -/
def revHomotopy : C(I × C, B × F) where
  toFun x := (h (σ x.1, (p x.2).1), (p x.2).2)
  continuous_toFun := by
    have := hp.continuous
    fun_prop

include h₁ in
lemma revHomotopy_zero (x : C) : revHomotopy hp h (0, x) = p x := by
  change (h (σ 0, (p x).1), (p x).2) = p x
  rw [symm_zero, h₁]

/-- The lift of `revHomotopy`, starting at `x`. -/
def revLift : C(I × C, C) :=
  hp.liftHomotopy (revHomotopy hp h) (ContinuousMap.id C) (revHomotopy_zero hp h h₁)

lemma proj_sliceLift (t : I) (x : B × SliceSpace p b₀) :
    p (sliceLift hp h h₀ (t, x)) = (h (t, x.1), (p x.2.1).2) :=
  congr_fun (hp.liftHomotopy_lifts _ _ _) (t, x)

lemma proj_revLift (t : I) (x : C) :
    p (revLift hp h h₁ (t, x)) = (h (σ t, (p x).1), (p x).2) :=
  congr_fun (hp.liftHomotopy_lifts _ _ _) (t, x)

lemma sliceLift_zero (x : B × SliceSpace p b₀) : sliceLift hp h h₀ (0, x) = x.2.1 :=
  hp.liftHomotopy_zero _ _ _ x

lemma revLift_zero (x : C) : revLift hp h h₁ (0, x) = x :=
  hp.liftHomotopy_zero _ _ _ x

include h₁ in
/-- The trivialization of a covering of `B × F` along the contraction `h` of `B` to `b₀`: the
point over `(b, f)` reached from `c` (over `(b₀, f)`) by lifting `t ↦ (h(t, b), f)`. -/
def sliceHomeomorph : B × SliceSpace p b₀ ≃ₜ C where
  toFun x := sliceLift hp h h₀ (1, x)
  invFun x := ((p x).1, ⟨revLift hp h h₁ (1, x), by rw [proj_revLift hp h h₁, symm_one, h₀]⟩)
  left_inv a := by
    obtain ⟨b, c⟩ := a
    have hx : p (sliceLift hp h h₀ (1, (b, c))) = (b, (p c.1).2) := by
      rw [proj_sliceLift hp h h₀, h₁]
    have key := hp.eq_of_comp_eq (A := I)
      (g₁ := fun t ↦ revLift hp h h₁ (t, sliceLift hp h h₀ (1, (b, c))))
      (g₂ := fun t ↦ sliceLift hp h h₀ (σ t, (b, c))) (by fun_prop) (by fun_prop)
      (funext fun t ↦ by simp only [Function.comp_apply, proj_revLift hp h h₁,
        proj_sliceLift hp h h₀, h₁]) 0
      (by simp only [revLift_zero, symm_zero])
    have hpb : (p (sliceLift hp h h₀ (1, (b, c)))).1 = b := by rw [hx]
    ext
    · exact hpb
    · change revLift hp h h₁ (1, _) = c.1
      rw [congr_fun key 1, symm_one, sliceLift_zero]
  right_inv x := by
    have hc : p (revLift hp h h₁ (1, x)) = (b₀, (p x).2) := by
      rw [proj_revLift hp h h₁, symm_one, h₀]
    have key := hp.eq_of_comp_eq (A := I)
      (g₁ := fun t ↦ sliceLift hp h h₀ (t, ((p x).1, ⟨revLift hp h h₁ (1, x), by rw [hc]⟩)))
      (g₂ := fun t ↦ revLift hp h h₁ (σ t, x)) (by fun_prop) (by fun_prop)
      (funext fun t ↦ by simp only [Function.comp_apply, proj_revLift hp h h₁,
        proj_sliceLift hp h h₀, symm_symm])
      0 (by simp only [sliceLift_zero, symm_zero])
    change sliceLift hp h h₀ (1, _) = x
    rw [congr_fun key 1, symm_one, revLift_zero]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have := hp.continuous
    fun_prop

lemma proj_sliceHomeomorph (x : B × SliceSpace p b₀) :
    p (sliceHomeomorph hp h h₀ h₁ x) = (x.1, (p x.2.1).2) := by
  change p (sliceLift hp h h₀ (1, x)) = _
  rw [proj_sliceLift hp h h₀, h₁]

end Contraction

end SGA.SGA1.ExposeXII.RiemannHigher
