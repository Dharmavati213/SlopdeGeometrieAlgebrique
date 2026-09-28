/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import SGA.Foundations.Formal.AdicRing

/-!
# Adic inverse systems of modules

Let `A` be a ring, complete for the `I`-adic topology. An *adic system* of `A`-modules
(EGA 0_I, §7.2) is a sequence of modules `Mₙ` with `Iⁿ⁺¹ Mₙ = 0` and surjections
`Mₙ₊₁ → Mₙ` with kernel `Iⁿ⁺¹ Mₙ₊₁`, i.e. `Mₙ = Mₙ₊₁ ⧸ Iⁿ⁺¹ Mₙ₊₁`. Every finite `A`-module `N`
gives the adic system `N ⧸ Iⁿ⁺¹ N`. Conversely (EGA 0_I, §7.2; Stacks, "Completion" /
"Algebraization"), if `M₀` is finite, the system comes from a finite `A`-module
(`Module.AdicSystem.exists_finite`). On coherent sheaves this says: coherent sheaves on
`Spf A` (compatible systems of finite `A ⧸ Iⁿ⁺¹`-modules) are the finite `A`-modules; it is the
algebraic input of the Grothendieck existence theorem.

Categorically: morphisms of adic systems (`Module.AdicSystem.Hom`) from `N ⧸ Iⁿ⁺¹ N` to
`N' ⧸ Iⁿ⁺¹ N'` are the linear maps `N → N'` when `N'` is complete
(`Module.AdicSystem.ofModuleMap_bijective`), and every adic system with `M₀` finite is isomorphic
to `N ⧸ Iⁿ⁺¹ N` for a finite `N` (`Module.AdicSystem.exists_finite_linearEquiv`); so for `A`
noetherian, `N ↦ (N ⧸ Iⁿ⁺¹ N)` is an equivalence between finite `A`-modules and adic systems
of finite modules (the affine case of the Grothendieck existence theorem, EGA III 5.1.4).
Systems given in base change form `(A ⧸ Iⁿ⁺¹) ⊗ Mₙ₊₁ ≅ Mₙ`, as systems of quasi-coherent sheaves
on the thickenings `Spec (A ⧸ Iⁿ⁺¹)` are, are adic systems by `Module.AdicSystem.ofTensorEquiv`.

The proof: lift generators of `M₀` to compatible surjections `gₙ : Aʳ → Mₙ` (using that `Aʳ` is
projective and Nakayama's lemma for the nilpotent ideal `I` acting on `Mₙ`); the kernels `Kₙ`
satisfy `Kₙ = Kₙ₊₁ + Iⁿ⁺¹ Aʳ`, and by completeness of `Aʳ` also `Kₙ = K + Iⁿ⁺¹ Aʳ` with
`K = ⋂ Kₙ`; then `N = Aʳ ⧸ K` works.
-/

universe u v

open Submodule
open scoped TensorProduct

namespace Submodule

variable {A : Type u} [CommRing A] {I : Ideal A} {M : Type v} [AddCommGroup M] [Module A M]

/-- Nakayama's lemma for a nilpotent ideal: if `N + I M = M` and `Iᵏ M = 0`, then `N = M`. -/
theorem eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot {N : Submodule A M}
    (h : N ⊔ I • ⊤ = ⊤) {k : ℕ} (hk : I ^ k • (⊤ : Submodule A M) = ⊥) : N = ⊤ := by
  have key : ∀ j : ℕ, N ⊔ I ^ j • ⊤ = ⊤ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hI : I • (⊤ : Submodule A M) ≤ N ⊔ I ^ (j + 1) • ⊤ := by
        rw [Submodule.smul_le]
        intro r hr m _
        have hm : m ∈ N ⊔ I ^ j • ⊤ := by rw [ih]; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
        rw [smul_add]
        refine add_mem (Submodule.mem_sup_left (N.smul_mem r ha)) (Submodule.mem_sup_right ?_)
        rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul hr hb
      exact eq_top_iff.mpr (h.symm.le.trans (sup_le le_sup_left hI))
  simpa [hk] using key k

end Submodule

/-- An *adic system* of modules over `(A, I)` (EGA 0_I, §7.2): modules `Mₙ` killed by `Iⁿ⁺¹`,
with surjections `Mₙ₊₁ → Mₙ` whose kernel is `Iⁿ⁺¹ Mₙ₊₁`. -/
structure Module.AdicSystem (A : Type u) [CommRing A] (I : Ideal A) where
  /-- The modules of the system. -/
  M : ℕ → Type v
  [addCommGroup : ∀ n, AddCommGroup (M n)]
  [module : ∀ n, Module A (M n)]
  pow_smul_eq_bot : ∀ n, (I ^ (n + 1) • ⊤ : Submodule A (M n)) = ⊥
  /-- The transition maps. -/
  π : ∀ n, M (n + 1) →ₗ[A] M n
  surjective : ∀ n, Function.Surjective (π n)
  ker_eq : ∀ n, LinearMap.ker (π n) = I ^ (n + 1) • ⊤

attribute [instance] Module.AdicSystem.addCommGroup Module.AdicSystem.module

namespace Module.AdicSystem

variable {A : Type u} [CommRing A] {I : Ideal A} (S : Module.AdicSystem.{u, v} A I)

section Lift

variable {r : ℕ} (g₀ : (Fin r → A) →ₗ[A] S.M 0)

/-- Compatible lifts `Aʳ → Mₙ` of a map `g₀ : Aʳ → M₀`. -/
noncomputable def liftSeq : ∀ n, (Fin r → A) →ₗ[A] S.M n
  | 0 => g₀
  | n + 1 => (Module.projective_lifting_property (S.π n) (liftSeq n) (S.surjective n)).choose

lemma π_comp_liftSeq (n : ℕ) : S.π n ∘ₗ S.liftSeq g₀ (n + 1) = S.liftSeq g₀ n :=
  (Module.projective_lifting_property (S.π n) (S.liftSeq g₀ n) (S.surjective n)).choose_spec

lemma liftSeq_surjective (hg₀ : Function.Surjective g₀) (n : ℕ) :
    Function.Surjective (S.liftSeq g₀ n) := by
  induction n with
  | zero => exact hg₀
  | succ n ih =>
    rw [← LinearMap.range_eq_top]
    refine Submodule.eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot (I := I) ?_
      (S.pow_smul_eq_bot (n + 1))
    refine eq_top_iff.mpr fun m _ ↦ ?_
    obtain ⟨a, ha⟩ := ih (S.π n m)
    have hmem : m - S.liftSeq g₀ (n + 1) a ∈ LinearMap.ker (S.π n) := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, π_comp_liftSeq, ha, sub_self]
    rw [S.ker_eq] at hmem
    have hle : (I ^ (n + 1) • ⊤ : Submodule A (S.M (n + 1))) ≤ I • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_self n.succ_ne_zero)
    rw [← sub_add_cancel m (S.liftSeq g₀ (n + 1) a)]
    exact add_mem (Submodule.mem_sup_right (hle hmem))
      (Submodule.mem_sup_left (LinearMap.mem_range_self _ a))

/-- The kernels `Kₙ` of the maps `Aʳ → Mₙ`. -/
noncomputable abbrev K (n : ℕ) : Submodule A (Fin r → A) := LinearMap.ker (S.liftSeq g₀ n)

lemma K_succ_le (n : ℕ) : S.K g₀ (n + 1) ≤ S.K g₀ n := fun a ha ↦ by
  rw [LinearMap.mem_ker, ← π_comp_liftSeq, LinearMap.comp_apply, LinearMap.mem_ker.mp ha, map_zero]

lemma pow_smul_le_K (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule A (Fin r → A)) ≤ S.K g₀ n := by
  rw [Submodule.smul_le]
  intro x hx m _
  rw [LinearMap.mem_ker, map_smul]
  have : x • S.liftSeq g₀ n m ∈ (I ^ (n + 1) • ⊤ : Submodule A (S.M n)) :=
    Submodule.smul_mem_smul hx Submodule.mem_top
  rwa [S.pow_smul_eq_bot, Submodule.mem_bot] at this

lemma K_eq_K_succ_sup (hg₀ : Function.Surjective g₀) (n : ℕ) :
    S.K g₀ n = S.K g₀ (n + 1) ⊔ I ^ (n + 1) • ⊤ := by
  refine le_antisymm (fun a ha ↦ ?_) (sup_le (S.K_succ_le g₀ n) (S.pow_smul_le_K g₀ n))
  have hmem : S.liftSeq g₀ (n + 1) a ∈ LinearMap.ker (S.π n) := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, π_comp_liftSeq]
    exact ha
  rw [S.ker_eq, ← LinearMap.range_eq_top.mpr (S.liftSeq_surjective g₀ hg₀ (n + 1)),
    LinearMap.range_eq_map, ← Submodule.map_smul''] at hmem
  obtain ⟨c, hc, hca⟩ := hmem
  rw [← sub_add_cancel a c]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hc)
  rw [LinearMap.mem_ker, map_sub, hca, sub_self]

lemma K_antitone {m n : ℕ} (h : m ≤ n) : S.K g₀ n ≤ S.K g₀ m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (S.K_succ_le g₀ n).trans ih

/-- The intersection `K = ⋂ Kₙ`. -/
noncomputable abbrev Kinf : Submodule A (Fin r → A) := ⨅ n, S.K g₀ n

/-- By completeness, `Kₙ = K + Iⁿ⁺¹ Aʳ` (the Mittag-Leffler argument). -/
lemma K_eq_Kinf_sup [IsPrecomplete I A] (hg₀ : Function.Surjective g₀) (n : ℕ) :
    S.K g₀ n = S.Kinf g₀ ⊔ I ^ (n + 1) • ⊤ := by
  refine le_antisymm (fun a ha ↦ ?_)
    (sup_le (iInf_le _ n) (S.pow_smul_le_K g₀ n))
  have : IsPrecomplete I (Fin r → A) := .of_finite I _
  have step (j : ℕ) (x : Fin r → A) (hx : x ∈ S.K g₀ (n + j)) :
      ∃ y ∈ S.K g₀ (n + j + 1), x - y ∈ (I ^ (n + j + 1) • ⊤ : Submodule A (Fin r → A)) := by
    rw [S.K_eq_K_succ_sup g₀ hg₀] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨y, hy, by simpa using hz⟩
  choose! next hnext using step
  let c : ℕ → Fin r → A := fun j ↦ Nat.rec a (fun j x ↦ next j x) j
  have hc (j : ℕ) : c j ∈ S.K g₀ (n + j) := by
    induction j with
    | zero => exact ha
    | succ j ih => exact (hnext j (c j) ih).1
  have hcauchy (i j : ℕ) (hij : i ≤ j) :
      c i - c j ∈ (I ^ (n + i + 1) • ⊤ : Submodule A (Fin r → A)) := by
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      rw [← sub_add_sub_cancel (c i) (c j) (c (j + 1))]
      refine add_mem ih (Submodule.smul_mono_left
        (Ideal.pow_le_pow_right (show n + i + 1 ≤ n + j + 1 by lia)) ?_)
      exact (hnext j (c j) (hc j)).2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I (Fin r → A)› (f := c)
    fun {i j} hij ↦ by
      rw [SModEq.sub_mem]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (show i ≤ n + i + 1 by lia))
        (hcauchy i j hij)
  have hLK : L ∈ S.Kinf g₀ := by
    rw [Submodule.mem_iInf]
    intro m
    have h₁ : c (m + 1) - L ∈ (I ^ (m + 1) • ⊤ : Submodule A (Fin r → A)) :=
      SModEq.sub_mem.mp (hL (m + 1))
    have h₂ : c (m + 1) ∈ S.K g₀ m := S.K_antitone g₀ (by lia) (hc (m + 1))
    have := sub_mem h₂ (S.pow_smul_le_K g₀ m h₁)
    rwa [sub_sub_cancel] at this
  rw [← add_sub_cancel L a]
  refine add_mem (Submodule.mem_sup_left hLK) (Submodule.mem_sup_right ?_)
  have h₁ : c 0 - c (n + 1) ∈ (I ^ (n + 1) • ⊤ : Submodule A (Fin r → A)) := by
    simpa using hcauchy 0 (n + 1) (Nat.zero_le _)
  have h₂ : c (n + 1) - L ∈ (I ^ (n + 1) • ⊤ : Submodule A (Fin r → A)) :=
    SModEq.sub_mem.mp (hL (n + 1))
  have := add_mem h₁ h₂
  rwa [sub_add_sub_cancel] at this

end Lift

/-- Algebraization of adic systems of modules (EGA 0_I, §7.2): if `A` is `I`-adically complete
and `M₀` is finite, the adic system `(Mₙ)` is `(N ⧸ Iⁿ⁺¹ N)` for a finite `A`-module `N`. -/
theorem exists_finite [IsPrecomplete I A] [Module.Finite A (S.M 0)] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module A N) (q : ∀ n, N →ₗ[A] S.M n),
      Module.Finite A N ∧ (∀ n, Function.Surjective (q n)) ∧
      (∀ n, LinearMap.ker (q n) = I ^ (n + 1) • ⊤) ∧ ∀ n, S.π n ∘ₗ q (n + 1) = q n := by
  obtain ⟨r, g₀, hg₀⟩ := Module.Finite.exists_fin' A (S.M 0)
  let Kinf := S.Kinf g₀
  let q (n : ℕ) : ((Fin r → A) ⧸ Kinf) →ₗ[A] S.M n :=
    Kinf.liftQ (S.liftSeq g₀ n) (iInf_le _ n)
  refine ⟨(Fin r → A) ⧸ Kinf, inferInstance, inferInstance, q, inferInstance, fun n ↦ ?_,
    fun n ↦ ?_, fun n ↦ ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := S.liftSeq_surjective g₀ hg₀ n y
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  · rw [Submodule.ker_liftQ, ← K, S.K_eq_Kinf_sup g₀ hg₀ n, Submodule.map_sup,
      Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    simp [Kinf]
  · refine Submodule.linearMap_qext _ ?_
    rw [LinearMap.comp_assoc, Submodule.liftQ_mkQ, Submodule.liftQ_mkQ, π_comp_liftSeq]

end Module.AdicSystem

namespace Module.AdicSystem

variable {A : Type u} [CommRing A] (I : Ideal A)

lemma pow_smul_quotient_eq_bot (N : Type v) [AddCommGroup N] [Module A N] (n : ℕ) :
    (I ^ n • ⊤ : Submodule A (N ⧸ (I ^ n • ⊤ : Submodule A N))) = ⊥ := by
  rw [← Submodule.range_mkQ, LinearMap.range_eq_map, ← Submodule.map_smul'',
    Submodule.mkQ_map_self]

/-- An adic system given by base change: modules `Mₙ` killed by `Iⁿ⁺¹` with
`(A ⧸ Iⁿ⁺¹) ⊗_A Mₙ₊₁ ≅ Mₙ`. This is the form in which a compatible system of quasi-coherent
sheaves on the thickenings `Spec (A ⧸ Iⁿ⁺¹)` is given, pullback to `Spec (A ⧸ Iⁿ⁺¹)` being base
change. -/
noncomputable def ofTensorEquiv (M : ℕ → Type v) [∀ n, AddCommGroup (M n)]
    [∀ n, Module A (M n)] (hM : ∀ n, (I ^ (n + 1) • ⊤ : Submodule A (M n)) = ⊥)
    (e : ∀ n, (A ⧸ I ^ (n + 1)) ⊗[A] M (n + 1) ≃ₗ[A] M n) : Module.AdicSystem.{u, v} A I where
  M := M
  pow_smul_eq_bot := hM
  π n := (e n).toLinearMap ∘ₗ
    (TensorProduct.quotTensorEquivQuotSMul (M (n + 1)) (I ^ (n + 1))).symm.toLinearMap ∘ₗ
      Submodule.mkQ _
  surjective n := by
    rw [LinearMap.coe_comp, LinearMap.coe_comp]
    exact (e n).surjective.comp ((LinearEquiv.surjective _).comp (Submodule.mkQ_surjective _))
  ker_eq n := by
    rw [LinearEquiv.ker_comp, LinearEquiv.ker_comp, Submodule.ker_mkQ]

@[simp]
lemma ofTensorEquiv_π_apply (M : ℕ → Type v) [∀ n, AddCommGroup (M n)]
    [∀ n, Module A (M n)] (hM : ∀ n, (I ^ (n + 1) • ⊤ : Submodule A (M n)) = ⊥)
    (e : ∀ n, (A ⧸ I ^ (n + 1)) ⊗[A] M (n + 1) ≃ₗ[A] M n) (n : ℕ) (x : M (n + 1)) :
    (ofTensorEquiv I M hM e).π n x = (e n (1 ⊗ₜ x) : M n) := by
  change e n ((TensorProduct.quotTensorEquivQuotSMul (M (n + 1)) (I ^ (n + 1))).symm
    (Submodule.Quotient.mk x)) = _
  congr 1

/-- The adic system `(N ⧸ Iⁿ⁺¹ N)` of an `A`-module `N`. -/
noncomputable def ofModule (N : Type v) [AddCommGroup N] [Module A N] :
    Module.AdicSystem.{u, v} A I where
  M n := N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)
  pow_smul_eq_bot n := pow_smul_quotient_eq_bot I N (n + 1)
  π n := Submodule.factor (Submodule.pow_smul_top_le I N (Nat.le_succ (n + 1)))
  surjective n := Submodule.factor_surjective _
  ker_eq n := by
    rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ]

end Module.AdicSystem

namespace Module.AdicSystem

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Morphisms of adic systems: compatible families of linear maps. -/
@[ext]
structure Hom (S T : Module.AdicSystem.{u, v} A I) where
  /-- The components. -/
  app (n : ℕ) : S.M n →ₗ[A] T.M n
  comm (n : ℕ) : T.π n ∘ₗ app (n + 1) = app n ∘ₗ S.π n

variable (I)

lemma pow_smul_top_map {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (f : N →ₗ[A] N') (n : ℕ) :
    (I ^ n • ⊤ : Submodule A N) ≤ (I ^ n • ⊤ : Submodule A N').comap f := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- The reductions `N ⧸ Iⁿ⁺¹ N → N' ⧸ Iⁿ⁺¹ N'` of a linear map. -/
noncomputable def ofModuleMap {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (f : N →ₗ[A] N') : Hom (ofModule I N) (ofModule I N') where
  app n := Submodule.mapQ _ _ f (pow_smul_top_map I f (n + 1))
  comm n := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- Linear maps into an `I`-adically complete module are the compatible families of maps between
the reductions (EGA 0_I, §7.2): the functor `N ↦ (N ⧸ Iⁿ⁺¹ N)` is fully faithful on complete
modules. -/
theorem ofModuleMap_bijective {N N' : Type v} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] [IsAdicComplete I N'] :
    Function.Bijective (ofModuleMap I (N := N) (N' := N')) := by
  have ha : StrictMono (fun n : ℕ ↦ n + 1) := strictMono_id.add_const 1
  refine ⟨fun f g h ↦ ?_, fun φ ↦ ?_⟩
  · ext x
    refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun n ↦ ?_
    have h₁ : f x ≡ g x [SMOD (I ^ (n + 1) • ⊤ : Submodule A N')] :=
      congr(($h).app n (Submodule.Quotient.mk x))
    exact SModEq.mono (Submodule.pow_smul_top_le I N' n.le_succ) h₁
  · let F : ∀ n, N →ₗ[A] N' ⧸ (I ^ ((fun n : ℕ ↦ n + 1) n) • ⊤ : Submodule A N') :=
      fun n ↦ φ.app n ∘ₗ Submodule.mkQ _
    have hF : ∀ {m}, Submodule.factorPow I N' (ha.monotone m.le_succ) ∘ₗ F (m + 1) = F m := by
      intro m
      ext x
      exact congr($(φ.comm m) (Submodule.Quotient.mk x))
    refine ⟨IsAdicComplete.StrictMono.lift I ha F hF, ?_⟩
    ext n x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact IsAdicComplete.StrictMono.mk_lift I ha F hF y

end Module.AdicSystem

namespace Module.AdicSystem

variable {A : Type u} [CommRing A] {I : Ideal A} (S : Module.AdicSystem.{u, v} A I)

/-- Algebraization of adic systems of modules, as an isomorphism of systems (EGA 0_I, §7.2): if
`A` is `I`-adically complete and `M₀` is finite, there is a finite `A`-module `N` with
compatible isomorphisms `N ⧸ Iⁿ⁺¹ N ≅ Mₙ`. -/
theorem exists_finite_linearEquiv [IsPrecomplete I A] [Module.Finite A (S.M 0)] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Finite A N)
      (e : ∀ n, (ofModule I N).M n ≃ₗ[A] S.M n),
      ∀ n, S.π n ∘ₗ (e (n + 1)).toLinearMap = (e n).toLinearMap ∘ₗ (ofModule I N).π n := by
  obtain ⟨N, _, _, q, hN, hq, hker, hcomp⟩ := S.exists_finite
  refine ⟨N, inferInstance, inferInstance, hN,
    fun n ↦ (Submodule.quotEquivOfEq _ _ (hker n).symm).trans
      (LinearMap.quotKerEquivOfSurjective (q n) (hq n)), fun n ↦ ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congr($(hcomp n) y)

end Module.AdicSystem
