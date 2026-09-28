/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIV.Completion
import SGA.SGA1.ExposeIV.LocalCriterion
import SGA.SGA2.ExposeIV.NoetherianCompletion

/-!
# SGA 1, Exposé IV, IV.5.8: flatness and completion

Under the hypotheses of IV.5.6, let `J` be an ideal of `B` with `IB ⊆ J ⊆ rad B`. SGA states that
`M` is `A`-flat if and only if its `J`-adic completion `M̂` is flat over the `I`-adic completion
`Â`. The `Â`-module structure of `M̂` comes from the canonical map `Â → B̂`; we characterize it by
its compatibility with the evaluations `Â → A/Iⁿ` and `B̂ → B/Jⁿ` (such a map is unique).

The sufficiency, which SGA notes "already follows easily from IV.3.2", is proved by descent: `Â`
is flat over `A` and `B̂` is faithfully flat over `B`, so flatness of `M̂ = B̂ ⊗_B M` over `A`
descends to `M`. For the necessity we follow SGA and apply the local flatness criterion IV.5.6
to `Â → B̂` and `M̂`: `Â ⧸ (IÂ)ⁿ = A ⧸ Iⁿ` and `M̂ ⊗_Â (A ⧸ Iⁿ) = (A ⧸ Iⁿ) ⊗_A M̂`. The completions
of noetherian rings are noetherian by `SGA.SGA2.ExposeIV.adicCompletion_isNoetherianRing`.
-/

universe u

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

section

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The kernel of `Â → A/Iⁿ` is `(IÂ)ⁿ`, for `I` finitely generated. -/
lemma ker_evalₐ_eq_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n) = (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  ext x
  have hle : (I ^ n • ⊤ : Ideal A) ≤ I ^ n := by simp
  have hle' : I ^ n ≤ (I ^ n • ⊤ : Ideal A) := by simp
  have : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 :=
    ⟨fun h ↦ by rw [← AdicCompletion.factor_evalₐ_eq_eval I x hle', h, map_zero],
      fun h ↦ by rw [← AdicCompletion.factor_eval_eq_evalₐ I x hle, h, map_zero]⟩
  rw [RingHom.mem_ker, this, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hI,
    ← Ideal.map_pow, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

lemma algebraMap_quotient_pow_surjective (hI : I.FG) (n : ℕ) :
    Surjective (algebraMap A
      (AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ n)) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (AdicCompletion I A), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq, ← ker_evalₐ_eq_pow I hI, RingHom.mem_ker, map_sub, AlgHom.commutes, ← ha,
    Ideal.Quotient.algebraMap_eq, sub_self]

end

section BaseChange

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal A) (n : ℕ)
  {P : Type*} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower A R P]

local notation "S" => R ⧸ (I.map (algebraMap A R)) ^ n

/-- The key relation: in `(R ⧸ (IR)ⁿ) ⊗[A] P`, elements of `R` may be moved across the tensor
sign, as soon as `A → R ⧸ (IR)ⁿ` is surjective. -/
lemma tmul_smul_eq_smul_tmul (hsurj : Surjective (algebraMap A S)) (s : S) (r : R) (p : P) :
    s ⊗ₜ[A] (r • p) = (r • s) ⊗ₜ[A] p := by
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ r)
  have hk : r - algebraMap A R a ∈ (I ^ n).map (algebraMap A R) := by
    rw [Ideal.map_pow, ← Ideal.Quotient.eq, ← ha]
    rfl
  -- `(r - a) p` lies in `Iⁿ P`, which is killed in the tensor product
  have hmem : (r - algebraMap A R a) • p ∈ (I ^ n • ⊤ : Submodule A P) := by
    have := Submodule.smul_mem_smul (M := P) hk (Submodule.mem_top (x := p))
    rwa [← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top] at this
  have hkill : ∀ y ∈ (I ^ n • ⊤ : Submodule A P), s ⊗ₜ[A] y = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun a' ha' p' _ ↦ ?_) fun y y' h h' ↦ by
      rw [tmul_add, h, h', add_zero]
    have : algebraMap A S a' = 0 := by
      rw [IsScalarTower.algebraMap_apply A R S, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha'
    rw [← smul_tmul, Algebra.smul_def, this, zero_mul, zero_tmul]
  have hrp : r • p = a • p + (r - algebraMap A R a) • p := by
    rw [sub_smul, algebraMap_smul, add_sub_cancel]
  have hrs : r • s = a • s := by
    rw [Algebra.smul_def, Algebra.smul_def (A := S), Ideal.Quotient.algebraMap_eq, ← ha]
  rw [hrp, tmul_add, hkill _ hmem, add_zero, hrs, smul_tmul]

/-- For an `A`-algebra `R` and an ideal `I` of `A` such that `A → R ⧸ (IR)ⁿ` is surjective, the
canonical map `(R ⧸ (IR)ⁿ) ⊗[A] P → (R ⧸ (IR)ⁿ) ⊗[R] P` is an isomorphism. -/
noncomputable def tensorQuotientPowEquiv (hsurj : Surjective (algebraMap A S)) :
    S ⊗[A] P ≃ₗ[S] S ⊗[R] P :=
  let g : S ⊗[A] P →ₗ[S] S ⊗[R] P :=
    LinearMap.liftBaseChange S ((TensorProduct.mk R S P 1).restrictScalars A)
  let h : S ⊗[R] P →ₗ[R] S ⊗[A] P := TensorProduct.lift <| LinearMap.mk₂ R
    (fun s p ↦ s ⊗ₜ[A] p) (fun _ _ _ ↦ add_tmul _ _ _) (fun r s p ↦ (smul_tmul' r s p).symm)
    (fun _ _ _ ↦ tmul_add _ _ _) (fun r s p ↦ by
      rw [tmul_smul_eq_smul_tmul I n hsurj, smul_tmul'])
  have hg (s : S) (p : P) : g (s ⊗ₜ p) = s ⊗ₜ p := by
    simp [g, smul_tmul']
  { g with
    invFun := h
    left_inv := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s p => simp [hg, h]
      | add x y hx hy => simp only [AddHom.toFun_eq_coe, coe_toAddHom, map_add] at hx hy ⊢
                         rw [hx, hy]
    right_inv := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s p => simp [hg, h]
      | add x y hx hy => simp only [AddHom.toFun_eq_coe, coe_toAddHom, map_add] at hx hy ⊢
                         rw [hx, hy] }

end BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

lemma pow_le_comap_pow {I : Ideal A} {J : Ideal B} (h : I.map (algebraMap A B) ≤ J) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

/-- A ring map `Â → B̂` is *compatible* if it induces `A/Iⁿ → B/Jⁿ` on each quotient; the
canonical map of completions is the unique such map. -/
def IsCompletionMap {I : Ideal A} {J : Ideal B} (h : I.map (algebraMap A B) ≤ J)
    (φ : AdicCompletion I A →+* AdicCompletion J B) : Prop :=
  ∀ (n : ℕ) (x : AdicCompletion I A), AdicCompletion.evalₐ J n (φ x) =
    Ideal.quotientMap (J ^ n) (algebraMap A B) (pow_le_comap_pow h n) (AdicCompletion.evalₐ I n x)

/-- IV.5.8, as a proposition (proved below as `flatIffFlatCompletionStatement`): under the
conditions of IV.5.6, with `J` an ideal of `B` such that
`IB ⊆ J ⊆ rad B`, `M` is `A`-flat if and only if the `J`-adic completion `M̂` is flat over the
`I`-adic completion `Â` (acting through the canonical map `Â → B̂`). -/
def FlatIffFlatCompletionStatement : Prop :=
  ∀ (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J),
    J ≤ Ideal.jacobson ⊥ → ∀ φ : AdicCompletion I A →+* AdicCompletion J B, IsCompletionMap h φ →
      (Module.Flat A M ↔
        letI := Module.compHom (AdicCompletion J M) φ
        Module.Flat (AdicCompletion I A) (AdicCompletion J M))

variable {M : Type u} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- IV.5.8, sufficiency: under the conditions of IV.5.6 (`A`, `B` noetherian, `M` a finite
`B`-module) and `IB ⊆ J ⊆ rad B`, if `M̂` is flat over `Â` then `M` is flat over `A`. -/
theorem flat_of_flat_completion [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite B M]
    (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J) (hJ : J ≤ Ideal.jacobson ⊥)
    (φ : AdicCompletion I A →+* AdicCompletion J B) (hφ : IsCompletionMap h φ)
    (hflat : letI := Module.compHom (AdicCompletion J M) φ
      Module.Flat (AdicCompletion I A) (AdicCompletion J M)) : Module.Flat A M := by
  let Ahat := AdicCompletion I A
  let Bhat := AdicCompletion J B
  let Mhat := AdicCompletion J M
  let : Module Ahat Mhat := Module.compHom Mhat φ
  -- `φ` is compatible with the structure maps
  have hφa (a : A) : φ (algebraMap A Ahat a) = algebraMap A Bhat a := by
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [hφ, IsScalarTower.algebraMap_apply A B Bhat, AdicCompletion.algebraMap_apply,
      AdicCompletion.evalₐ_of, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Ideal.quotientMap_mk]
    simp
  have : IsScalarTower A Ahat Mhat := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change φ (algebraMap A Ahat a) • x = a • x
    rw [hφa, IsScalarTower.algebraMap_apply A B Bhat, algebraMap_smul, algebraMap_smul]
  have : Module.Flat A Ahat := flat_adicCompletion I
  have : Module.Flat A Mhat := Module.Flat.trans A Ahat Mhat
  -- `Mhat = Bhat ⊗_B M`, and `Bhat` is faithfully flat over `B` (IV.3.2)
  have : IsScalarTower A Bhat Mhat := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    rw [IsScalarTower.algebraMap_apply A B Bhat, algebraMap_smul, algebraMap_smul]
  let e : Bhat ⊗[B] M ≃ₗ[A] Mhat :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J M).restrictScalars A
  have : Module.Flat A (Bhat ⊗[B] M) := Module.Flat.of_linearEquiv e
  have : Module.FaithfullyFlat B Bhat := (faithfullyFlat_adicCompletion_iff J).2 hJ
  -- descend flatness along `B → Bhat`
  rw [Module.Flat.iff_lTensor_injective']
  intro I₀
  let g := AlgebraTensorModule.lTensor B M I₀.subtype
  rw [← AlgebraTensorModule.coe_lTensor (A := B),
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective B Bhat g]
  have key : ⇑(g.lTensor Bhat) =
      AlgebraTensorModule.assoc A B Bhat Bhat M A ∘ (I₀.subtype.lTensor (Bhat ⊗[B] M)) ∘
        (AlgebraTensorModule.assoc A B Bhat Bhat M I₀).symm := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul b y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        simp only [Function.comp_apply, tmul_add, map_add] at hy hz ⊢; rw [hy, hz]
      | tmul m i => simp [g]
  rw [key]
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective).comp
      (LinearEquiv.injective _))

/-- If `M` is `A`-flat and `B'` is flat over `B`, then `B' ⊗_B M` is `A`-flat. -/
lemma flat_tensorProduct_of_flat (B' : Type*) [CommRing B'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B'] [Module.Flat B B'] [Module.Flat A M] : Module.Flat A (B' ⊗[B] M) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I₀
  let g := AlgebraTensorModule.lTensor B M I₀.subtype
  have key : ⇑(I₀.subtype.lTensor (B' ⊗[B] M)) =
      (AlgebraTensorModule.assoc A B B' B' M A).symm ∘ (g.lTensor B') ∘
        AlgebraTensorModule.assoc A B B' B' M I₀ := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul y i =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        simp only [Function.comp_apply, add_tmul, map_add] at hy hz ⊢; rw [hy, hz]
      | tmul b m => simp [g]
  rw [key]
  have hg : Injective g := by
    rw [AlgebraTensorModule.coe_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap (M := B') _ hg).comp
      (LinearEquiv.injective _))

/-- IV.5.8, necessity: under the conditions of IV.5.6 (`A`, `B` noetherian, `M` a finite
`B`-module), with `J` an ideal of `B` containing `IB`, if `M` is `A`-flat then its `J`-adic
completion `M̂` is flat over `Â`. (The hypothesis `J ⊆ rad B` of SGA is only needed for the
converse.) As in SGA, one applies criterion (iv) of IV.5.6 to `Â → B̂` and `M̂`, using
`Â ⧸ (IÂ)ⁿ = A ⧸ Iⁿ` and `M̂ ⊗_Â (A ⧸ Iⁿ) = (A ⧸ Iⁿ) ⊗_A M̂`, which is flat over `A ⧸ Iⁿ` because
`M̂ = B̂ ⊗_B M` is `A`-flat. -/
theorem flat_completion_of_flat [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite B M]
    (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J)
    (φ : AdicCompletion I A →+* AdicCompletion J B) (hφ : IsCompletionMap h φ)
    [Module.Flat A M] :
    letI := Module.compHom (AdicCompletion J M) φ
    Module.Flat (AdicCompletion I A) (AdicCompletion J M) := by
  let Ahat := AdicCompletion I A
  let Bhat := AdicCompletion J B
  let Mhat := AdicCompletion J M
  let : Module Ahat Mhat := Module.compHom Mhat φ
  let : Algebra Ahat Bhat := φ.toAlgebra
  have : IsScalarTower Ahat Bhat Mhat := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- `φ` is compatible with the structure maps
  have hφa (a : A) : φ (algebraMap A Ahat a) = algebraMap A Bhat a := by
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [hφ, IsScalarTower.algebraMap_apply A B Bhat, AdicCompletion.algebraMap_apply,
      AdicCompletion.evalₐ_of, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Ideal.quotientMap_mk]
    simp
  have : IsScalarTower A Ahat Mhat := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change φ (algebraMap A Ahat a) • x = a • x
    rw [hφa, IsScalarTower.algebraMap_apply A B Bhat, algebraMap_smul, algebraMap_smul]
  -- `M̂ = B̂ ⊗_B M` is finite over `B̂` and flat over `A`
  have : Module.Finite Bhat Mhat :=
    Module.Finite.equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J M)
  have : Module.Flat B Bhat := flat_adicCompletion J
  have : Module.Flat A (Bhat ⊗[B] M) := flat_tensorProduct_of_flat Bhat
  have : IsScalarTower A Bhat Mhat := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    rw [IsScalarTower.algebraMap_apply A B Bhat, algebraMap_smul, algebraMap_smul]
  have : Module.Flat A Mhat := Module.Flat.of_linearEquiv
    ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J M).restrictScalars A).symm
  -- `IÂ B̂ ⊆ J B̂` lies in the radical of `B̂`
  have hK : (I.map (algebraMap A Ahat)).map (algebraMap Ahat Bhat) ≤
      J.map (algebraMap B Bhat) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply]
    change φ (algebraMap A Ahat a) ∈ _
    rw [hφa, IsScalarTower.algebraMap_apply A B Bhat]
    exact Ideal.mem_map_of_mem _ (h (Ideal.mem_map_of_mem _ ha))
  have : IsAdicComplete (J.map (algebraMap B Bhat)) Bhat :=
    AdicCompletion.isAdicComplete_self J (IsNoetherian.noetherian J)
  have hI := hK.trans (IsAdicComplete.le_jacobson_bot _)
  -- criterion (iv) of IV.5.6
  refine ((flat_tfae (B := Bhat) Mhat (I.map (algebraMap A Ahat)) hI).out 1 4).2 fun n ↦ ?_
  exact Module.Flat.of_linearEquiv (tensorQuotientPowEquiv I n
    (algebraMap_quotient_pow_surjective I (IsNoetherian.noetherian I) n)).symm

/-- IV.5.8: under the conditions of IV.5.6, with `J` an ideal of `B` such that
`IB ⊆ J ⊆ rad B`, `M` is `A`-flat if and only if its `J`-adic completion `M̂` is flat over the
`I`-adic completion `Â` (acting through the canonical map `Â → B̂`). -/
theorem flat_iff_flat_completion [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite B M]
    (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) ≤ J) (hJ : J ≤ Ideal.jacobson ⊥)
    (φ : AdicCompletion I A →+* AdicCompletion J B) (hφ : IsCompletionMap h φ) :
    Module.Flat A M ↔
      letI := Module.compHom (AdicCompletion J M) φ
      Module.Flat (AdicCompletion I A) (AdicCompletion J M) :=
  ⟨fun _ ↦ flat_completion_of_flat I J h φ hφ, flat_of_flat_completion I J h hJ φ hφ⟩

/-- IV.5.8 holds. -/
theorem flatIffFlatCompletionStatement : FlatIffFlatCompletionStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ I J h hJ φ hφ ↦ flat_iff_flat_completion I J h hJ φ hφ

end SGA.SGA1.ExposeIV
