/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.SerrePKernelCounting
import SGA.SGA1.ExposeXIII.SerrePKernelFrobenius
import SGA.SGA1.ExposeXIII.SerrePKernelLift

/-!
# Invariant Artin–Schreier classes that are not coboundaries

The second half of Serre's theorem on `p`-group kernels (used in Raynaud's proof of XIII.2.13):
for the Galois algebra `B` of a continuous surjection `π₁(𝔸¹_k) → H` (`k` algebraically closed of
characteristic `p`) and a representation of `H` on `(ℤ/p)ʳ`, `r > 0`, some `H`-invariant
`a ∈ B ⊗ (ℤ/p)ʳ` is not of the form `bᵖ - b` (`exists_invariant_forall_not_root`). This is
Serre's "`H¹(π, N)` is infinite", proved by his degree count
(`SGA.SGA1.ExposeXIII.SerrePKernelCounting`): the invariants `invariants` form a non-zero
`k[T]`-module stable under Frobenius (non-zero by the Chase–Harrison–Rosenberg elements), and the
invariants that are coboundaries fall into finitely many classes modulo `℘` of invariants, one for
each function `H → (ℤ/p)ʳ` (`exists_castHom_eq_of_pow_eq`: `xᵖ = x` forces `x ∈ 𝔽_p` in a domain).
-/

universe u

namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

open Polynomial Matrix

section Invariants

variable (p : ℕ) [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] {B : Type u} [CommRing B]
  [IsDomain B] [CharP B p] [Algebra k[X] B] {H : Type*} [Group H]
  (ρH : H →* (B ≃ₐ[k[X]] B)) {r : ℕ} (CmH : H →* Matrix (Fin r) (Fin r) (ZMod p))

/-- The `H`-invariants of `Bʳ` for the diagonal action `σ ⋆ w = Cm(σ) σ(w)`, a `k[T]`-module. -/
def invariants : Submodule k[X] (Fin r → B) where
  carrier := {w | ∀ σ, castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ (w i)) = w}
  add_mem' {w w'} hw hw' σ := by
    have : (fun i ↦ ρH σ ((w + w') i)) = (fun i ↦ ρH σ (w i)) + fun i ↦ ρH σ (w' i) := by
      funext i
      simp
    rw [this, mulVec_add, hw σ, hw' σ]
  zero_mem' σ := by
    simp only [Pi.zero_apply, map_zero]
    exact mulVec_zero _
  smul_mem' c w hw σ := by
    have : (fun i ↦ ρH σ ((c • w) i)) = c • fun i ↦ ρH σ (w i) := by
      funext i
      simp
    rw [this, mulVec_smul, hw σ]

end Invariants

section Lemmas

variable (p : ℕ) [hp : Fact p.Prime] {B : Type*} [CommRing B] [IsDomain B] [CharP B p]

/-- In a domain of characteristic `p`, the solutions of `xᵖ = x` are the elements of `𝔽_p`. -/
lemma exists_castHom_eq_of_pow_eq {x : B} (hx : x ^ p = x) :
    ∃ c : ZMod p, ZMod.castHom (dvd_refl p) B c = x := by
  have hprod := congrArg (Polynomial.eval x)
    (ExposeXI.ArtinSchreier.X_pow_sub_X_eq_prod (A := B) (p := p))
  rw [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, hx, sub_self, add_zero, Polynomial.eval_prod] at hprod
  obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hc
  exact ⟨c, hc.symm⟩

end Lemmas

section Main

variable (p : ℕ) [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] {B : Type u} [CommRing B]
  [IsDomain B] [CharP B p] [Algebra k[X] B] {H : Type*} [Group H] [Finite H]
  (ρH : H →* (B ≃ₐ[k[X]] B)) {r : ℕ} (CmH : H →* Matrix (Fin r) (Fin r) (ZMod p))

omit [CharP k p] [IsDomain B] [Finite H] in
/-- The action `σ ⋆ w = Cm(σ) σ(w)` of `H` on `Bʳ` composes. -/
lemma star_mul (σ τ : H) (w : Fin r → B) :
    castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ ((castMat p B (CmH τ) *ᵥ fun j ↦ ρH τ (w j)) i)) =
      castMat p B (CmH (σ * τ)) *ᵥ fun i ↦ ρH (σ * τ) (w i) :=
  ((vecDistribMulAction p ρH CmH).mul_smul σ τ w).symm

omit [CharP k p] [IsDomain B] [Finite H] in
lemma star_sub (σ : H) (w w' : Fin r → B) :
    castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ ((w - w') i)) =
      castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ (w i)) - castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (w' i) := by
  rw [← mulVec_sub]
  congr 1
  funext i
  simp

omit [CharP k p] [IsDomain B] [Finite H] in
lemma star_frob (σ : H) (w : Fin r → B) :
    (fun i ↦ (castMat p B (CmH σ) *ᵥ fun j ↦ ρH σ (w j)) i ^ p) =
      castMat p B (CmH σ) *ᵥ fun j ↦ ρH σ (w j ^ p) := by
  funext i
  rw [castMat_mulVec_pow]
  simp only [map_pow]

/-- Serre's key lemma (the proper solution in the split case): when `k` is algebraically closed
(infinite and perfect is enough), `B` is a finite étale `k[T]`-algebra which is a domain with a
Galois action of `H` (given by Chase–Harrison–Rosenberg elements), and `r > 0`, some
`H`-invariant `a ∈ Bʳ` is not of the form `bᵖ - b`, i.e. defines a non-trivial torsor. -/
theorem exists_invariant_forall_not_root [Infinite k] [PerfectRing k p] [Module.Finite k[X] B]
    [Algebra.Etale k[X] B] (hr : 0 < r)
    (hCHR : ∃ (n : ℕ) (x y : Fin n → B), ∑ i, x i * y i = 1 ∧
      ∀ σ : H, σ ≠ 1 → ∑ i, x i * ρH σ (y i) = 0) :
    ∃ a ∈ invariants p ρH CmH, ∀ b : Fin r → B, ¬ ∀ i, b i ^ p - b i + a i = 0 := by
  classical
  have := Fintype.ofFinite H
  let : Algebra k B := ((algebraMap k[X] B).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let b := Module.Free.chooseBasis k[X] B
  have hd : IsUnit (Algebra.discr k[X] b) := (ExposeI.etale_iff_isUnit_discr b).mp inferInstance
  obtain ⟨c₀, c₂, hbd⟩ := exists_deg_pow_char_bounds_pi p b hd (ι := Fin r)
  let F : (Fin r → B) →+ (Fin r → B) :=
    { toFun := fun w i ↦ w i ^ p
      map_zero' := by
        funext i
        exact zero_pow hp.out.ne_zero
      map_add' := fun w w' ↦ by
        funext i
        exact add_pow_char _ _ _ }
  have hFapply : ∀ w i, F w i = w i ^ p := fun _ _ ↦ rfl
  have hF : ∀ (c : k) (w : Fin r → B), F (c • w) = c ^ p • F w := by
    intro c w
    funext i
    change (c • w i) ^ p = c ^ p • (w i ^ p)
    rw [Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow]
  have hFinj : Function.Injective F := by
    intro w w' h
    funext i
    have h1 : (w i - w' i) ^ p = 0 := by
      rw [sub_pow_char, ← hFapply, ← hFapply, h, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff hp.out.ne_zero |>.mp h1)
  set M := invariants p ρH CmH
  have hFM : ∀ m ∈ M, F m ∈ M := by
    intro m hm σ
    change (castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (m i ^ p)) = fun i ↦ m i ^ p
    rw [← star_frob, hm σ]
  -- `M ≠ 0`, from the Chase–Harrison–Rosenberg elements
  have hM : M ≠ ⊥ := by
    obtain ⟨n, x, y, h1, h2⟩ := hCHR
    let v : Fin r → B := fun i ↦ if i = ⟨0, hr⟩ then 1 else 0
    let tr : B → Fin r → B := fun c ↦ ∑ σ : H, castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (c * v i)
    have htr : ∀ c, tr c ∈ M := by
      intro c τ
      simp only [tr]
      have : (fun i ↦ ρH τ ((∑ σ : H, castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (c * v i)) i)) =
          ∑ σ : H, fun i ↦ ρH τ ((castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (c * v i)) i) := by
        funext i
        simp
      rw [this, mulVec_sum]
      simp_rw [star_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun _ ↦ rfl
    have hsum : ∑ j, x j • tr (y j) = v := by
      simp only [tr, Finset.smul_sum]
      rw [Finset.sum_comm]
      have hσ : ∀ σ : H, ∑ j, x j • (castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (y j * v i)) =
          castMat p B (CmH σ) *ᵥ fun i ↦ (∑ j, x j * ρH σ (y j)) * ρH σ (v i) := by
        intro σ
        calc ∑ j, x j • (castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (y j * v i))
            = ∑ j, castMat p B (CmH σ) *ᵥ (x j • fun i ↦ ρH σ (y j * v i)) := by
              simp_rw [mulVec_smul]
          _ = castMat p B (CmH σ) *ᵥ ∑ j, (x j • fun i ↦ ρH σ (y j * v i)) := by
              rw [mulVec_sum]
          _ = _ := by
              congr 1
              funext i
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul,
                mul_assoc]
      simp_rw [hσ]
      rw [Finset.sum_eq_single (1 : H)]
      · simp [h1]
      · intro σ _ hσ1
        rw [h2 σ hσ1]
        simp only [zero_mul]
        exact mulVec_zero _
      · intro h
        exact (h (Finset.mem_univ _)).elim
    intro hbot
    have hv : v = 0 := by
      rw [← hsum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have := htr (y j)
      rw [hbot, Submodule.mem_bot] at this
      rw [this, smul_zero]
    have := congrFun hv ⟨0, hr⟩
    simp [v] at this
  -- the invariants that are coboundaries fall into finitely many classes modulo `℘(M)`
  let star : H → (Fin r → B) → Fin r → B := fun σ w ↦
    castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (w i)
  have hstar_add : ∀ σ w w', star σ (w + w') = star σ w + star σ w' := by
    intro σ w w'
    simp only [star]
    rw [← mulVec_add]
    congr 1
    funext i
    simp
  let T : Set (Fin r → B) := {m | m ∈ M ∧ ∃ y, F y - y = m}
  have hTy : ∀ m ∈ T, ∃ y, F y - y = m := fun m hm ↦ hm.2
  choose! y hy using hTy
  have hcoord : ∀ m ∈ T, ∀ σ i, ∃ c : ZMod p,
      ZMod.castHom (dvd_refl p) B c = (star σ (y m) - y m) i := by
    intro m hm σ i
    apply exists_castHom_eq_of_pow_eq p
    have hFy : F (y m) = y m + m := by
      rw [add_comm]
      exact sub_eq_iff_eq_add.mp (hy m hm)
    have hσm : star σ m = m := hm.1 σ
    have hZ : F (star σ (y m) - y m) = star σ (y m) - y m := by
      have h1 : F (star σ (y m)) = star σ (F (y m)) := star_frob p ρH CmH σ (y m)
      rw [map_sub, h1, hFy, hstar_add, hσm]
      abel
    have := congrFun hZ i
    rw [hFapply] at this
    exact this
  choose! cl hcl using hcoord
  let rep : (H → Fin r → ZMod p) → Fin r → B := fun c ↦
    if h : ∃ m ∈ T, cl m = c then h.choose else 0
  obtain ⟨m, hmM, hm⟩ := exists_mem_forall_ne_add_sub (Pi.basis fun _ : Fin r ↦ b) F hF hFinj c₀ c₂
    (fun w ↦ (hbd w).1) (fun w ↦ (hbd w).2) M hM hFM (Finset.univ.image rep)
  refine ⟨m, hmM, fun bb hbb ↦ ?_⟩
  have hmT : m ∈ T := by
    refine ⟨hmM, -bb, ?_⟩
    funext i
    rw [Pi.sub_apply, hFapply, Pi.neg_apply, ExposeXI.ArtinSchreier.neg_pow_char]
    linear_combination -hbb i
  have hex : ∃ m' ∈ T, cl m' = cl m := ⟨m, hmT, rfl⟩
  have hrep : rep (cl m) = hex.choose := by simp only [rep, hex, ↓reduceDIte]
  obtain ⟨hm'T, hclm'⟩ := hex.choose_spec
  set m' := hex.choose
  have hx : y m - y m' ∈ M := by
    intro σ
    rw [star_sub]
    funext i
    have h1 := hcl m hmT σ i
    have h2 := hcl m' hm'T σ i
    rw [hclm'] at h2
    simp only [Pi.sub_apply] at h1 h2 ⊢
    change (star σ (y m)) i - (star σ (y m')) i = y m i - y m' i
    linear_combination h2 - h1
  refine hm m' (Finset.mem_image.mpr ⟨cl m, Finset.mem_univ _, hrep⟩) (y m - y m') hx ?_
  have e1 := hy m hmT
  have e2 := hy m' hm'T
  calc m = m' + ((F (y m) - y m) - (F (y m') - y m')) := by rw [e1, e2]; abel
    _ = m' + (F (y m - y m') - (y m - y m')) := by rw [map_sub]; abel

end Main

end SerrePKernel

end SGA.SGA1.ExposeXIII
