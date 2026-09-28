/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import SGA.SGA1.ExposeV.FiniteQuotient

/-!
# SGA 1, Exposé V, V.1.9: quotients commute with flat base change

Let `G` act on a `B`-algebra `A` with `A^G = B`, and let `B'` be a flat `B`-algebra. Then
`(B' ⊗_B A)^G = B'`, where `G` acts on the second factor. The proof is the one of SGA: the
exact sequence `0 → B → A → A^G`, `a ↦ (s • a - a)_s`, stays exact after `B' ⊗_B -`.
Conversely, for `B'` faithfully flat the equality `(B' ⊗_B A)^G = B'` implies `A^G = B`
(the converse used in the proof of V.2.6).

Geometrically: `Spec (B' ⊗_B A) ⟶ Spec B'` is the quotient of `Spec (B' ⊗_B A)` by `G`, i.e.
`(X/G) ×_Z Z' = (X ×_Z Z')/G` for `X` affine. The case of a non-affine `X` is
`QuotientBaseChange.lean`, and its faithfully flat converse `QuotientDescent.lean`.
-/

universe u

open TensorProduct AlgebraicGeometry

namespace SGA.SGA1.ExposeV

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] (B' : Type*) [CommRing B']
  [Algebra B B'] (G : Type*) [Group G] [MulSemiringAction G A] [SMulCommClass G B A]

/-- The action of `G` on `B' ⊗_B A` through the second factor. -/
@[instance_reducible]
noncomputable def tensorAction : MulSemiringAction G (B' ⊗[B] A) where
  smul g := Algebra.TensorProduct.map (AlgHom.id B B') (MulSemiringAction.toAlgHom B A g)
  one_smul x := by
    change Algebra.TensorProduct.map _ _ x = x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, MulSemiringAction.toAlgHom_apply,
        one_smul]
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h x := by
    change Algebra.TensorProduct.map _ _ x =
      Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ x)
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b a =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        MulSemiringAction.toAlgHom_apply, mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

lemma tensorAction_tmul (g : G) (b : B') (a : A) :
    letI := tensorAction (B := B) (A := A) B' G
    g • (b ⊗ₜ[B] a) = b ⊗ₜ (g • a) :=
  Algebra.TensorProduct.map_tmul _ _ b a

/-- The `B`-linear map `a ↦ (g • a - a)_g`, whose kernel is `A^G`. -/
noncomputable def invariantsDefect : A →ₗ[B] G → A :=
  LinearMap.pi fun g ↦ (MulSemiringAction.toAlgHom B A g).toLinearMap - LinearMap.id

variable {G} in
lemma invariantsDefect_apply (a : A) (g : G) : invariantsDefect (B := B) G a g = g • a - a := rfl

lemma invariantsDefect_comp :
    invariantsDefect (B := B) G ∘ₗ Algebra.linearMap B A = 0 := by
  refine LinearMap.ext fun b ↦ funext fun g ↦ ?_
  simp [invariantsDefect_apply]

variable {B'} in
/-- `A^G = B` (with `B → A` injective) is the exactness of `0 → B → A → A^G`. -/
lemma isInvariant_iff_exact :
    Algebra.IsInvariant B A G ↔
      Function.Exact (Algebra.linearMap B A) (invariantsDefect (B := B) G) := by
  refine ⟨fun h a ↦ ⟨fun ha ↦ ?_, ?_⟩, fun h ↦ ⟨fun a ha ↦ ?_⟩⟩
  · exact h.isInvariant a fun g ↦ sub_eq_zero.mp (congr_fun ha g)
  · rintro ⟨b, rfl⟩
    ext g
    simp [invariantsDefect_apply]
  · exact (h a).mp (funext fun g ↦ sub_eq_zero.mpr (ha g))

lemma lTensor_invariantsDefect_apply [Fintype G] [DecidableEq G] (x : B' ⊗[B] A) (g : G) :
    (piRight B B B' fun _ : G ↦ A) ((invariantsDefect (B := B) G).lTensor B' x) g =
      Algebra.TensorProduct.map (AlgHom.id B B') (MulSemiringAction.toAlgHom B A g) x - x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    simp only [LinearMap.lTensor_tmul, piRight_apply, piRightHom_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, MulSemiringAction.toAlgHom_apply,
      ← tmul_sub]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add]
    abel

lemma lTensor_algebraMap (y : B' ⊗[B] B) :
    (Algebra.linearMap B A).lTensor B' y =
      algebraMap B' (B' ⊗[B] A) (TensorProduct.rid B B' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b r =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one r, ← smul_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

lemma injective_algebraMap_tensorProduct_iff :
    Function.Injective (algebraMap B' (B' ⊗[B] A)) ↔
      Function.Injective ((Algebra.linearMap B A).lTensor B') := by
  have h : ⇑((Algebra.linearMap B A).lTensor B') =
      algebraMap B' (B' ⊗[B] A) ∘ TensorProduct.rid B B' := funext (lTensor_algebraMap B')
  rw [h]
  exact (EquivLike.injective_comp (TensorProduct.rid B B').toEquiv _).symm

lemma tensorAction_smulCommClass :
    letI := tensorAction (B := B) (A := A) B' G
    SMulCommClass G B' (B' ⊗[B] A) := by
  let _ := tensorAction (B := B) (A := A) B' G
  refine ⟨fun g b x ↦ ?_⟩
  change Algebra.TensorProduct.map _ _ (b • x) = b • Algebra.TensorProduct.map _ _ x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    rw [smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]


variable [Finite G]

/-- V.1.9: flat base change preserves `A^G = B`: for `B'` flat over `B`, `B' → B' ⊗_B A` is
injective with image the invariants `(B' ⊗_B A)^G`. -/
theorem isInvariant_tensorProduct [Module.Flat B B'] [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A)) :
    letI := tensorAction (B := B) (A := A) B' G
    Function.Injective (algebraMap B' (B' ⊗[B] A)) ∧ Algebra.IsInvariant B' (B' ⊗[B] A) G := by
  let _ := tensorAction (B := B) (A := A) B' G
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨(injective_algebraMap_tensorProduct_iff (A := A) B').mpr
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj), ⟨fun x hx ↦ ?_⟩⟩
  have hex := Module.Flat.lTensor_exact B' ((isInvariant_iff_exact (B := B) (A := A) G).mp ‹_›)
  have h0 : (invariantsDefect (B := B) G).lTensor B' x = 0 := by
    apply (piRight B B B' fun _ : G ↦ A).injective
    ext g
    rw [lTensor_invariantsDefect_apply, map_zero, Pi.zero_apply]
    exact sub_eq_zero.mpr (hx g)
  obtain ⟨y, rfl⟩ := (hex x).mp h0
  exact ⟨_, (lTensor_algebraMap B' y).symm⟩

/-- The converse of V.1.9 for a faithfully flat change of base (used in the proof of V.2.6):
if `(B' ⊗_B A)^G = B'` and `B'` is faithfully flat over `B`, then `A^G = B`. -/
theorem isInvariant_of_tensorProduct [Module.FaithfullyFlat B B'] :
    letI := tensorAction (B := B) (A := A) B' G
    Function.Injective (algebraMap B' (B' ⊗[B] A)) → Algebra.IsInvariant B' (B' ⊗[B] A) G →
      Function.Injective (algebraMap B A) ∧ Algebra.IsInvariant B A G := by
  let _ := tensorAction (B := B) (A := A) B' G
  intro hinj' hinv'
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨(Module.FaithfullyFlat.lTensor_injective_iff_injective B B' _).mp
    ((injective_algebraMap_tensorProduct_iff (A := A) B').mp hinj'),
    (isInvariant_iff_exact (B := B) (A := A) G).mpr ?_⟩
  rw [← Module.FaithfullyFlat.lTensor_exact_iff_exact B B']
  intro x
  constructor
  · intro hx
    have hfix : ∀ g : G, g • x = x := fun g ↦ by
      have := congr_fun (congr_arg (piRight B B B' fun _ : G ↦ A) hx) g
      rwa [lTensor_invariantsDefect_apply, map_zero, Pi.zero_apply, sub_eq_zero] at this
    obtain ⟨b, rfl⟩ := hinv'.isInvariant x hfix
    exact ⟨b ⊗ₜ 1, by rw [lTensor_algebraMap, TensorProduct.rid_tmul, one_smul]⟩
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, invariantsDefect_comp, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

/-- V.1.9, geometric form for affine schemes: `Spec (B' ⊗_B A) ⟶ Spec B'` is the quotient of
`Spec (B' ⊗_B A) = Spec A ×_{Spec B} Spec B'` by `G`, i.e. `(X/G) ×_Z Z' = (X ×_Z Z')/G` when
`Z' → Z` is flat. -/
theorem isQuotient_specMap_tensorProduct {B A B' : Type u} [CommRing B] [CommRing A]
    [Algebra B A] [CommRing B'] [Algebra B B'] [MulSemiringAction G A] [SMulCommClass G B A]
    [Module.Flat B B'] [Algebra.IsInvariant B A G] (hinj : Function.Injective (algebraMap B A)) :
    letI := tensorAction (B := B) (A := A) B' G
    IsQuotient (specAction (CommRingCat.of (B' ⊗[B] A)) G)
      (specMap (CommRingCat.of (B' ⊗[B] A)) (CommRingCat.of B')) := by
  let _ := tensorAction (B := B) (A := A) B' G
  have := tensorAction_smulCommClass (B := B) (A := A) B' G
  obtain ⟨hinj', hinv'⟩ := isInvariant_tensorProduct B' G hinj
  exact isQuotient_specMap hinj'

end SGA.SGA1.ExposeV
