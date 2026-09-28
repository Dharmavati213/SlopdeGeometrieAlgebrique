/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVIII.ModuleDescent

/-!
# SGA 1, Exposé VIII, §1: descent data as isomorphisms `φ`

In SGA a descent datum on a `B`-module `N` relative to `A → B` is an isomorphism
`φ : N ⊗_A B ≅ B ⊗_A N` of `B ⊗_A B`-modules (the two inverse images of `N` on
`Spec (B ⊗_A B)`) satisfying the cocycle condition `φ₁₃ = φ₂₃ ∘ φ₁₂`. This is `DescentIso`.
We show that these are the same as the coactions `θ : N → B ⊗_A N` used in `ModuleDescent`
(`descentIsoEquiv`), via `θ n = φ (n ⊗ 1)` and `φ (n ⊗ c) = (1 ⊗ c) θ n`. In particular the
counit condition of `ModuleDescentDatum` is a consequence of the cocycle condition and the
invertibility of `φ` (`counit_of_surjective_isoOfCoaction`), and conversely `φ` is invertible
for every coaction (`ModuleDescentDatum.isoOfCoaction_bijective`).
-/

universe u v w

open TensorProduct

namespace SGA.SGA1.ExposeVIII

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

variable (A B N) in
/-- The action map `N ⊗_A B → N`, `n ⊗ c ↦ c • n`. -/
noncomputable def tensorActRight : N ⊗[A] B →ₗ[A] N :=
  (LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)).restrictScalars A ∘ₗ
    (TensorProduct.comm A N B).toLinearMap

@[simp]
lemma tensorActRight_tmul (n : N) (c : B) : tensorActRight A B N (n ⊗ₜ c) = c • n := by
  simp [tensorActRight]

variable (A B N) in
/-- Multiplication by `c` on the factor `N` of `B ⊗_A N`. -/
noncomputable def lTensorSMul (c : B) : B ⊗[A] N →ₗ[A] B ⊗[A] N :=
  LinearMap.lTensor B ((LinearMap.lsmul B N c).restrictScalars A)

@[simp]
lemma lTensorSMul_tmul (c b : B) (n : N) : lTensorSMul A B N c (b ⊗ₜ n) = b ⊗ₜ (c • n) := rfl

/-- SGA's isomorphism `φ : N ⊗_A B → B ⊗_A N` attached to a coaction `θ`:
`φ (n ⊗ c) = (1 ⊗ c) θ n`. -/
noncomputable def isoOfCoaction (θ : N →ₗ[B] B ⊗[A] N) : N ⊗[A] B →ₗ[B] B ⊗[A] N :=
  AlgebraTensorModule.lTensor B B (tensorActRight A B N) ∘ₗ
    (AlgebraTensorModule.assoc A A B B N B).toLinearMap ∘ₗ AlgebraTensorModule.rTensor A B θ

lemma lTensor_rightAct_assoc (y : B ⊗[A] N) (c : B) :
    LinearMap.lTensor B (tensorActRight A B N) (AlgebraTensorModule.assoc A A B B N B (y ⊗ₜ c)) =
      lTensorSMul A B N c y := by
  induction y with
  | zero => simp
  | add x y hx hy => rw [add_tmul, map_add, map_add, hx, hy, map_add]
  | tmul b n => simp

@[simp]
lemma isoOfCoaction_tmul (θ : N →ₗ[B] B ⊗[A] N) (n : N) (c : B) :
    isoOfCoaction θ (n ⊗ₜ c) = lTensorSMul A B N c (θ n) := by
  simp [isoOfCoaction, lTensor_rightAct_assoc]

/-- The candidate inverse `ψ (c ⊗ n) = c • τ (θ n)` of `isoOfCoaction θ`, where `τ` exchanges
the two factors. -/
noncomputable def invOfCoaction (θ : N →ₗ[B] B ⊗[A] N) : B ⊗[A] N →ₗ[B] N ⊗[A] B :=
  LinearMap.liftBaseChange B ((TensorProduct.comm A B N).toLinearMap ∘ₗ θ.restrictScalars A)

@[simp]
lemma invOfCoaction_tmul (θ : N →ₗ[B] B ⊗[A] N) (c : B) (n : N) :
    invOfCoaction θ (c ⊗ₜ n) = c • TensorProduct.comm A B N (θ n) := by
  simp [invOfCoaction]

variable (A B N) in
/-- Auxiliary map `x ⊗ y ⊗ n ↦ x n ⊗ c y`. -/
noncomputable def auxInvIso (c : B) : B ⊗[A] (B ⊗[A] N) →ₗ[A] N ⊗[A] B :=
  TensorProduct.map ((LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)).restrictScalars A)
      (LinearMap.mulLeft A c) ∘ₗ
    (TensorProduct.assoc A B N B).symm.toLinearMap ∘ₗ
    (TensorProduct.comm A B N).toLinearMap.lTensor B

@[simp]
lemma auxInvIso_tmul (c x y : B) (n : N) :
    auxInvIso A B N c (x ⊗ₜ (y ⊗ₜ n)) = (x • n) ⊗ₜ (c * y) := by
  simp [auxInvIso]

variable (A B N) in
/-- Auxiliary map `x ⊗ y ⊗ n ↦ c y ⊗ x n`. -/
noncomputable def auxIsoInv (c : B) : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] N :=
  (LinearMap.mulLeft A c).rTensor N ∘ₗ
    ((LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)).restrictScalars A).lTensor B ∘ₗ
    (TensorProduct.leftComm A B B N).toLinearMap

@[simp]
lemma auxIsoInv_tmul (c x y : B) (n : N) :
    auxIsoInv A B N c (x ⊗ₜ (y ⊗ₜ n)) = (c * y) ⊗ₜ (x • n) := by
  simp [auxIsoInv]

omit [Module B N] [IsScalarTower A B N] in
variable (A B N) in
/-- Auxiliary map `x ⊗ y ⊗ n ↦ x y ⊗ n`. -/
noncomputable def auxMul : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] N :=
  (LinearMap.mul' A B).rTensor N ∘ₗ (TensorProduct.assoc A B B N).symm.toLinearMap

omit [Module B N] [IsScalarTower A B N] in
@[simp]
lemma auxMul_tmul (x y : B) (n : N) : auxMul A B N (x ⊗ₜ (y ⊗ₜ n)) = (x * y) ⊗ₜ n := by
  simp [auxMul]

section

variable (θ : N →ₗ[B] B ⊗[A] N)

/-- The action map `B ⊗_A N → N`. -/
local notation "act" => LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

lemma invOfCoaction_isoOfCoaction_tmul (n : N) (c : B) :
    invOfCoaction θ (isoOfCoaction θ (n ⊗ₜ c)) =
      auxInvIso A B N c ((θ.restrictScalars A).lTensor B (θ n)) := by
  rw [isoOfCoaction_tmul]
  generalize θ n = y
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    rw [lTensorSMul_tmul, invOfCoaction_tmul, LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars,
      map_smul]
    generalize θ m = z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, tmul_add, hx, hy]
    | tmul x k => simp [smul_tmul']

lemma auxInvIso_lTensor_mk (c : B) (y : B ⊗[A] N) :
    auxInvIso A B N c ((TensorProduct.mk A B N 1).lTensor B y) = act y ⊗ₜ c := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
  | tmul b m => simp

lemma isoOfCoaction_invOfCoaction_tmul (c : B) (n : N) :
    isoOfCoaction θ (invOfCoaction θ (c ⊗ₜ n)) =
      auxIsoInv A B N c ((θ.restrictScalars A).lTensor B (θ n)) := by
  rw [invOfCoaction_tmul, map_smul]
  generalize θ n = y
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b m =>
    rw [TensorProduct.comm_tmul, isoOfCoaction_tmul, LinearMap.lTensor_tmul,
      LinearMap.coe_restrictScalars]
    generalize θ m = z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, tmul_add, hx, hy]
    | tmul x k => simp [smul_tmul']

lemma auxIsoInv_lTensor_mk (c : B) (y : B ⊗[A] N) :
    auxIsoInv A B N c ((TensorProduct.mk A B N 1).lTensor B y) = c ⊗ₜ act y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
  | tmul b m => simp

lemma auxMul_lTensor_coaction (y : B ⊗[A] N) :
    auxMul A B N ((θ.restrictScalars A).lTensor B y) = θ (act y) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    rw [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul,
      LinearMap.id_apply, map_smul]
    generalize θ m = z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, tmul_add, hx, hy]
    | tmul x k => simp [smul_tmul']

omit [Module B N] [IsScalarTower A B N] in
lemma auxMul_lTensor_mk (y : B ⊗[A] N) :
    auxMul A B N ((TensorProduct.mk A B N 1).lTensor B y) = y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

lemma act_lTensorSMul (c : B) (y : B ⊗[A] N) : act (lTensorSMul A B N c y) = c • act y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b m => simp [smul_comm b c m]

lemma act_isoOfCoaction (x : N ⊗[A] B) :
    act (isoOfCoaction θ x) = act (θ (tensorActRight A B N x)) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n c => rw [isoOfCoaction_tmul, act_lTensorSMul, tensorActRight_tmul, map_smul, map_smul]

theorem counit_of_surjective_isoOfCoaction
    (hcoassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) =
      (TensorProduct.mk A B N 1).lTensor B (θ n))
    (hsurj : Function.Surjective (isoOfCoaction θ)) (n : N) : act (θ n) = n := by
  have hidem (m : N) : act (θ (act (θ m))) = act (θ m) := by
    rw [← auxMul_lTensor_coaction, hcoassoc, auxMul_lTensor_mk]
  obtain ⟨x, hx⟩ := hsurj (1 ⊗ₜ n)
  have hn : n = act (θ (tensorActRight A B N x)) := by
    rw [← act_isoOfCoaction, hx, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.id_apply]
  rw [hn, hidem]

end

namespace ModuleDescentDatum

variable (D : ModuleDescentDatum A B N)

local notation "act" => LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

lemma invOfCoaction_isoOfCoaction (x : N ⊗[A] B) :
    invOfCoaction D.coaction (isoOfCoaction D.coaction x) = x := by
  suffices (invOfCoaction D.coaction).comp (isoOfCoaction D.coaction) = LinearMap.id from
    congr($this x)
  refine TensorProduct.AlgebraTensorModule.ext fun n c ↦ ?_
  rw [LinearMap.comp_apply, invOfCoaction_isoOfCoaction_tmul, D.coassoc, auxInvIso_lTensor_mk,
    D.counit, LinearMap.id_apply]

lemma isoOfCoaction_invOfCoaction (y : B ⊗[A] N) :
    isoOfCoaction D.coaction (invOfCoaction D.coaction y) = y := by
  suffices (isoOfCoaction D.coaction).comp (invOfCoaction D.coaction) = LinearMap.id from
    congr($this y)
  refine TensorProduct.AlgebraTensorModule.ext fun c n ↦ ?_
  rw [LinearMap.comp_apply, isoOfCoaction_invOfCoaction_tmul, D.coassoc, auxIsoInv_lTensor_mk,
    D.counit, LinearMap.id_apply]

/-- The isomorphism `φ` of a descent datum is bijective. -/
theorem isoOfCoaction_bijective : Function.Bijective (isoOfCoaction D.coaction) :=
  ⟨Function.LeftInverse.injective D.invOfCoaction_isoOfCoaction,
    Function.RightInverse.surjective D.isoOfCoaction_invOfCoaction⟩

end ModuleDescentDatum

variable (A B N) in
/-- VIII.1, SGA's definition: a descent datum on the `B`-module `N` relative to `A → B` is an
isomorphism `φ : N ⊗_A B ≅ B ⊗_A N` of `B ⊗_A B`-modules such that `φ₁₃ = φ₂₃ ∘ φ₁₂` on
`N ⊗_A B ⊗_A B`. Linearity over `B ⊗ 1` is the `B`-linearity of `toLinearEquiv` (for `B` acting
on `N`, resp. on the left factor); `map_smul_right` is linearity over `1 ⊗ B`. In `cocycle`,
the left side is `φ₂₃ (φ₁₂ (n ⊗ b ⊗ c))` and the right side is `φ₁₃ (n ⊗ b ⊗ c)`. -/
@[ext]
structure DescentIso where
  /-- The isomorphism `φ`. -/
  toLinearEquiv : N ⊗[A] B ≃ₗ[B] B ⊗[A] N
  map_smul_right (c : B) (x : N ⊗[A] B) :
    toLinearEquiv ((LinearMap.mulLeft A c).lTensor N x) = lTensorSMul A B N c (toLinearEquiv x)
  cocycle (n : N) (b c : B) :
    (toLinearEquiv.toLinearMap.restrictScalars A).lTensor B
        (TensorProduct.assoc A B N B (toLinearEquiv (n ⊗ₜ b) ⊗ₜ c)) =
      (TensorProduct.mk A B N b).lTensor B (toLinearEquiv (n ⊗ₜ c))

variable (A B N) in
/-- `n ↦ n ⊗ 1`, as a `B`-linear map `N → N ⊗_A B`. -/
noncomputable def tmulOne : N →ₗ[B] N ⊗[A] B where
  toFun n := n ⊗ₜ 1
  map_add' x y := add_tmul x y 1
  map_smul' b n := (smul_tmul' b n 1).symm

@[simp]
lemma tmulOne_apply (n : N) : tmulOne A B N n = n ⊗ₜ 1 := rfl

lemma lTensorSMul_lTensorSMul (c d : B) (y : B ⊗[A] N) :
    lTensorSMul A B N c (lTensorSMul A B N d y) = lTensorSMul A B N (c * d) y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mul_smul]

lemma lTensorSMul_one (y : B ⊗[A] N) : lTensorSMul A B N 1 y = y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp

lemma isoOfCoaction_comp_tmulOne (θ : N →ₗ[B] B ⊗[A] N) :
    isoOfCoaction θ ∘ₗ tmulOne A B N = θ := by
  ext n
  simp [lTensorSMul_one]

namespace DescentIso

variable (φ : DescentIso A B N)

/-- The coaction `θ n = φ (n ⊗ 1)` of SGA's descent datum `φ`. -/
noncomputable def coaction : N →ₗ[B] B ⊗[A] N := φ.toLinearEquiv.toLinearMap ∘ₗ tmulOne A B N

lemma isoOfCoaction_coaction : isoOfCoaction φ.coaction = φ.toLinearEquiv.toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun n c ↦ ?_
  have : n ⊗ₜ[A] c = (LinearMap.mulLeft A c).lTensor N (n ⊗ₜ 1) := by simp
  rw [isoOfCoaction_tmul, LinearEquiv.coe_coe, this, φ.map_smul_right]
  rfl

lemma assoc_tmul_one (y : B ⊗[A] N) :
    TensorProduct.assoc A B N B (y ⊗ₜ 1) = ((tmulOne A B N).restrictScalars A).lTensor B y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul b m => simp

/-- The coaction of SGA's descent datum `φ` is a descent datum. -/
noncomputable def toModuleDescentDatum : ModuleDescentDatum A B N where
  coaction := φ.coaction
  coassoc n := by
    have h := φ.cocycle n 1 1
    rw [assoc_tmul_one, ← LinearMap.lTensor_comp_apply] at h
    exact h
  counit := counit_of_surjective_isoOfCoaction φ.coaction
    (fun n ↦ by
      have h := φ.cocycle n 1 1
      rw [assoc_tmul_one, ← LinearMap.lTensor_comp_apply] at h
      exact h)
    (by rw [isoOfCoaction_coaction]; exact φ.toLinearEquiv.surjective)

end DescentIso

variable (A B N) in
/-- The map `x ⊗ y ⊗ k ↦ x ⊗ b y ⊗ c k` (action of `1 ⊗ b ⊗ c ∈ B ⊗ B ⊗ B`). -/
noncomputable def smulTwo (b c : B) : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] (B ⊗[A] N) :=
  LinearMap.lTensor B (TensorProduct.map (LinearMap.mulLeft A b)
    ((LinearMap.lsmul B N c).restrictScalars A))

@[simp]
lemma smulTwo_tmul (b c x y : B) (k : N) :
    smulTwo A B N b c (x ⊗ₜ (y ⊗ₜ k)) = x ⊗ₜ ((b * y) ⊗ₜ (c • k)) := rfl

lemma lTensorSMul_smul (b c : B) (w : B ⊗[A] N) :
    lTensorSMul A B N c (b • w) = TensorProduct.map (LinearMap.mulLeft A b)
      ((LinearMap.lsmul B N c).restrictScalars A) w := by
  induction w with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x k => simp [smul_tmul']

namespace ModuleDescentDatum

variable (D : ModuleDescentDatum A B N)

lemma cocycle_left (b c : B) (y : B ⊗[A] N) :
    ((isoOfCoaction D.coaction).restrictScalars A).lTensor B
        (TensorProduct.assoc A B N B (lTensorSMul A B N b y ⊗ₜ c)) =
      smulTwo A B N b c ((D.coaction.restrictScalars A).lTensor B y) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul x m =>
    simp only [lTensorSMul_tmul, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
      LinearMap.coe_restrictScalars, isoOfCoaction_tmul, map_smul, lTensorSMul_smul]
    generalize D.coaction m = w
    induction w with
    | zero => simp
    | add y z hy hz => simp only [map_add, tmul_add, hy, hz]
    | tmul y k => simp

lemma cocycle_right (b c : B) (y : B ⊗[A] N) :
    (TensorProduct.mk A B N b).lTensor B (lTensorSMul A B N c y) =
      smulTwo A B N b c ((TensorProduct.mk A B N 1).lTensor B y) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x m => simp

/-- SGA's form of a descent datum: the isomorphism `φ (n ⊗ c) = (1 ⊗ c) θ n`. -/
noncomputable def toDescentIso : DescentIso A B N where
  toLinearEquiv := LinearEquiv.ofBijective _ D.isoOfCoaction_bijective
  map_smul_right c x := by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul n d => simp [lTensorSMul_lTensorSMul]
  cocycle n b c := by
    simp only [LinearEquiv.ofBijective_apply, isoOfCoaction_tmul]
    change ((isoOfCoaction D.coaction).restrictScalars A).lTensor B _ = _
    rw [cocycle_left, D.coassoc, ← cocycle_right]

@[simp]
lemma toDescentIso_apply (x : N ⊗[A] B) :
    D.toDescentIso.toLinearEquiv x = isoOfCoaction D.coaction x := rfl

end ModuleDescentDatum

variable (A B N) in
/-- VIII.1: descent data in SGA's form (isomorphisms `φ` with the cocycle condition) are the
same as coactions `θ` (`ModuleDescentDatum`), via `θ n = φ (n ⊗ 1)` and
`φ (n ⊗ c) = (1 ⊗ c) θ n`. -/
noncomputable def descentIsoEquiv : ModuleDescentDatum A B N ≃ DescentIso A B N where
  toFun D := D.toDescentIso
  invFun φ := φ.toModuleDescentDatum
  left_inv D := by
    ext1
    exact isoOfCoaction_comp_tmulOne D.coaction
  right_inv φ := by
    ext1
    exact LinearEquiv.toLinearMap_injective φ.isoOfCoaction_coaction

end SGA.SGA1.ExposeVIII
