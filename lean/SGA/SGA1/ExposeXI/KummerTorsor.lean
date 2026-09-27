/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import SGA.SGA1.ExposeXI.Kummer

/-!
# SGA 1, Exposé XI.4.2 and XI.6.2: Kummer coverings are torsors under `μ_n`

For an affine group scheme `G = Spec H` over `S = Spec R` (`H` a commutative Hopf algebra) and
an affine `P = Spec B`, a right action of `G` on `P` is a coaction `ρ : B → B ⊗_R H` (a comodule
algebra structure), and by XI.4.2 (ii), `P` is a principal homogeneous bundle under `G` if and only
if `B` is faithfully flat over `R` and `B ⊗_R B → B ⊗_R H`, `x ⊗ y ↦ (x ⊗ 1) ρ(y)` is bijective.
This is `IsHopfTorsor`.

The Kummer group is `μ_n = Spec R[ℤ/n]`, the group algebra of `ℤ/n` with its Hopf algebra
structure from mathlib (`muEquivGroupAlgebra` identifies it with `R[t]/(tⁿ - 1)`), and
`Kummer.isHopfTorsor` shows that the Kummer covering `R[T]/(Tⁿ - a)` of a unit `a` is a principal
homogeneous bundle under `μ_n` (XI.6.2), whatever `n` is.
-/

namespace SGA.SGA1.ExposeXI

open Polynomial TensorProduct

section HopfTorsor

variable {R : Type*} [CommRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
  {B : Type*} [CommRing B] [Algebra R B]

/-- The map `B ⊗_R B → B ⊗_R H`, `x ⊗ y ↦ (x ⊗ 1) ρ(y)`: the ring-theoretic form of
`P ×_S G → P ×_S P`, `(x, g) ↦ (x, x g)` (XI.4). -/
noncomputable def coactionTorsorMap (ρ : B →ₐ[R] B ⊗[R] H) : B ⊗[R] B →ₐ[B] B ⊗[R] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft ρ fun _ _ ↦ .all _ _

theorem coactionTorsorMap_tmul (ρ : B →ₐ[R] B ⊗[R] H) (x y : B) :
    coactionTorsorMap H ρ (x ⊗ₜ y) = (x ⊗ₜ[R] (1 : H)) * ρ y :=
  (Algebra.TensorProduct.lift_tmul _ _ _ x y).trans
    (by rw [Algebra.TensorProduct.includeLeft_apply])

/-- XI.4.1–XI.4.2 (affine case): `Spec B` is a principal homogeneous bundle under the affine group
scheme `Spec H`, acting through the coaction `ρ`: `ρ` is counital and coassociative, `B` is
faithfully flat over `R`, and `B ⊗_R B → B ⊗_R H` is bijective (XI.4.2 (ii)). -/
structure IsHopfTorsor (ρ : B →ₐ[R] B ⊗[R] H) : Prop where
  counit : (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R H)).comp ρ =
    Algebra.TensorProduct.includeLeft
  coassoc : (Algebra.TensorProduct.map ρ (AlgHom.id R H)).comp ρ =
    ((Algebra.TensorProduct.assoc R R R B H H).symm : _ →ₐ[R] _).comp
      ((Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R H)).comp ρ)
  faithfullyFlat : Module.FaithfullyFlat R B
  bijective : Function.Bijective (coactionTorsorMap H ρ)

end HopfTorsor

variable {A : Type*} [CommRing A] (n : ℕ) [NeZero n]

/-- The element `k ↦ tᵏ` of `μ_n(R[t]/(tⁿ - 1))`, as a homomorphism from `ℤ/n`. -/
noncomputable def muRootHom : Multiplicative (ZMod n) →* MuAlgebra A n where
  toFun k := AdjoinRoot.root _ ^ (Multiplicative.toAdd k).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' k l := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (Kummer.mu_root_pow n)]

theorem muRootHom_apply (k : Multiplicative (ZMod n)) :
    muRootHom (A := A) n k = AdjoinRoot.root _ ^ (Multiplicative.toAdd k).val := rfl

theorem single_one_pow_val (k : ZMod n) :
    (AddMonoidAlgebra.single (1 : ZMod n) (1 : A)) ^ k.val = AddMonoidAlgebra.single k 1 := by
  rw [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- The map `R[t]/(tⁿ - 1) → R[ℤ/n]`, `t ↦ [1]`. -/
noncomputable def muToGroupAlgebra : MuAlgebra A n →ₐ[A] AddMonoidAlgebra A (ZMod n) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AddMonoidAlgebra.single 1 1) (by
    change aeval _ (X ^ n - 1) = 0
    rw [map_sub, aeval_X_pow, map_one, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul,
      mul_one, ZMod.natCast_self, ← AddMonoidAlgebra.one_def, sub_self])

omit [NeZero n] in
theorem muToGroupAlgebra_root :
    muToGroupAlgebra (A := A) n (AdjoinRoot.root _) = AddMonoidAlgebra.single 1 1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- XI.6.1: `μ_n = Spec R[t]/(tⁿ - 1)` is the diagonalizable group scheme `Spec R[ℤ/n]`; the
right-hand side carries mathlib's Hopf algebra structure, making `μ_n` a group scheme. -/
noncomputable def muEquivGroupAlgebra : MuAlgebra A n ≃ₐ[A] AddMonoidAlgebra A (ZMod n) :=
  AlgEquiv.ofAlgHom (muToGroupAlgebra n)
    (AddMonoidAlgebra.lift A (MuAlgebra A n) (ZMod n) (muRootHom n))
    (AddMonoidAlgebra.algHom_ext (fun k ↦ by
      rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul, AlgHom.id_apply,
        muRootHom_apply, toAdd_ofAdd, map_pow, muToGroupAlgebra_root, single_one_pow_val])
      (Subsingleton.elim _ _))
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, muToGroupAlgebra_root, AddMonoidAlgebra.lift_single, one_smul,
        AlgHom.id_apply, muRootHom_apply, toAdd_ofAdd, ZMod.val_one_eq_one_mod,
        ← pow_eq_pow_mod _ (Kummer.mu_root_pow n), pow_one]))

theorem muEquivGroupAlgebra_root :
    muEquivGroupAlgebra (A := A) n (AdjoinRoot.root _) = AddMonoidAlgebra.single 1 1 :=
  show muToGroupAlgebra (A := A) n (AdjoinRoot.root _) = _ from muToGroupAlgebra_root n

namespace Kummer

variable {n} {a : A}

variable (n a) in
/-- XI.6.2: the coaction `K → K ⊗_R R[ℤ/n]`, `T ↦ T ⊗ [1]`, of `μ_n` on the Kummer covering. -/
noncomputable def groupCoaction :
    KummerAlgebra A n a →ₐ[A] KummerAlgebra A n a ⊗[A] AddMonoidAlgebra A (ZMod n) :=
  (Algebra.TensorProduct.map (AlgHom.id A _) (muToGroupAlgebra n)).comp (coaction n a)

omit [NeZero n] in
theorem groupCoaction_root :
    groupCoaction n a (AdjoinRoot.root _) =
      AdjoinRoot.root (X ^ n - C a) ⊗ₜ AddMonoidAlgebra.single (1 : ZMod n) (1 : A) := by
  rw [groupCoaction, AlgHom.comp_apply, coaction_root, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, muToGroupAlgebra_root]

/-- XI.6.2 (affine case): the Kummer covering `R[T]/(Tⁿ - a)` of a unit `a` is a principal
homogeneous bundle under the Kummer group `μ_n = Spec R[ℤ/n]`. -/
theorem isHopfTorsor (ha : IsUnit a) :
    IsHopfTorsor (AddMonoidAlgebra A (ZMod n)) (groupCoaction n a) where
  counit := AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, groupCoaction_root, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Bialgebra.counitAlgHom_apply,
      (AddMonoidAlgebra.isGroupLikeElem_single_one (R := A) (A := A) (1 : ZMod n)).counit_eq_one,
      Algebra.TensorProduct.includeLeft_apply])
  coassoc := AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, groupCoaction_root,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, groupCoaction_root,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply,
      (AddMonoidAlgebra.isGroupLikeElem_single_one (R := A) (A := A)
        (1 : ZMod n)).comul_eq_tmul_self]
    rfl)
  faithfullyFlat := inferInstance
  bijective := by
    let E := (torsorEquiv n ha).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl (muEquivGroupAlgebra (A := A) n))
    have : coactionTorsorMap _ (groupCoaction n a) = E.toAlgHom := by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AdjoinRoot.algHom_ext ?_)
      change coactionTorsorMap _ (groupCoaction n a) (1 ⊗ₜ AdjoinRoot.root _) =
        E (1 ⊗ₜ AdjoinRoot.root _)
      rw [coactionTorsorMap_tmul, ← Algebra.TensorProduct.one_def, one_mul, groupCoaction_root,
        AlgEquiv.trans_apply,
        torsorEquiv_tmul, coaction_root, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
        muEquivGroupAlgebra_root]
    rw [this]
    exact E.bijective

end Kummer

end SGA.SGA1.ExposeXI
