/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristic
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Cohomology.LerayTransfer
import SGA.Foundations.Cohomology.CohomologicalDimension

/-!
# Basic properties of the Euler characteristic

Let `X` be proper over a field `k`. We prove (EGA III 2.5; Hartshorne III Ex. 5.1; Stacks
Tags 0BEJ, 08AA):

* `Scheme.Modules.exists_H_subsingleton`: the cohomology of quasi-coherent modules vanishes above
  some degree `N` (the number of affines of a finite affine cover), so `χ(X, M)` is a finite sum
  (`Scheme.Modules.eulerChar_eq_sum_range`);
* `Scheme.Modules.eulerChar_of_shortExact`: `χ` is additive on short exact sequences of coherent
  modules (the long exact sequence and `Module.sum_alternating_finrank_eq_zero`);
* `Scheme.Modules.eulerChar_pushforward`: `χ(X, j_* M) = χ(Y, M)` for `j : Y ⟶ X` affine and `M`
  quasi-coherent (EGA III 1.3.3, `CohomologyAux.pushforwardHAddEquiv`);
* `Scheme.Modules.eulerChar_eq_zero_of_isEmpty`: `χ = 0` on the empty scheme;
* `Scheme.Hom.genus_eq_finrankH_unitModule`: the genus with `𝒪_X` as `CohomologyAux.unitModule X`.
-/

universe u v

open CategoryTheory Limits

namespace Module

variable {k : Type*} [Field k] {A B C : ℕ → Type v} [∀ n, AddCommGroup (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module k (A n)]
  [∀ n, Module k (B n)] [∀ n, Module k (C n)]

/-- **Alternating sum of dimensions in a long exact sequence**: for an exact sequence
`0 → A₀ → B₀ → C₀ → A₁ → B₁ → C₁ → ⋯` of finite-dimensional vector spaces with `A_N = 0`,
`Σ_{n < N} (-1)ⁿ (dim Aₙ - dim Bₙ + dim Cₙ) = 0`. -/
theorem sum_alternating_finrank_eq_zero [∀ n, FiniteDimensional k (A n)]
    [∀ n, FiniteDimensional k (B n)] [∀ n, FiniteDimensional k (C n)]
    (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] C n) (δ : ∀ n, C n →ₗ[k] A (n + 1))
    (hf : Function.Injective (f 0)) (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n, Function.Exact (g n) (δ n)) (hδf : ∀ n, Function.Exact (δ n) (f (n + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      ((finrank k (A n) : ℤ) - finrank k (B n) + finrank k (C n)) = 0 := by
  let c : ℕ → ℤ := fun n ↦ finrank k (LinearMap.range (δ n))
  let c' : ℕ → ℤ := fun n ↦ match n with
    | 0 => 0
    | n + 1 => c n
  have key : ∀ n, (finrank k (A n) : ℤ) - finrank k (B n) + finrank k (C n) = c' n + c n := by
    intro n
    have hA := LinearMap.finrank_range_add_finrank_ker (f n)
    have hB := LinearMap.finrank_range_add_finrank_ker (g n)
    have hC := LinearMap.finrank_range_add_finrank_ker (δ n)
    have eB : LinearMap.ker (g n) = LinearMap.range (f n) := (hfg n).linearMap_ker_eq
    have eC : LinearMap.ker (δ n) = LinearMap.range (g n) := (hgδ n).linearMap_ker_eq
    rw [eB] at hB
    rw [eC] at hC
    have hker : (finrank k (LinearMap.ker (f n)) : ℤ) = c' n := by
      cases n with
      | zero =>
        rw [LinearMap.ker_eq_bot.mpr hf, finrank_bot]
        rfl
      | succ m =>
        rw [(hδf m).linearMap_ker_eq]
    change _ = c' n + (finrank k (LinearMap.range (δ n)) : ℤ)
    omega
  have hsum : ∀ M, ∑ n ∈ Finset.range (M + 1), (-1 : ℤ) ^ n * (c' n + c n) = (-1) ^ M * c M := by
    intro M
    induction M with
    | zero => simp [c']
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [c', pow_succ]
      ring
  rcases N with _ | N
  · simp
  simp_rw [key]
  rw [hsum N]
  have : finrank k (LinearMap.range (δ N)) = 0 := by
    have h1 := Submodule.finrank_le (LinearMap.range (δ N))
    have h2 : finrank k (A (N + 1)) = 0 := finrank_zero_of_subsingleton
    omega
  simp [c, this]

end Module

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- On a scheme proper over a field, the cohomology of quasi-coherent modules vanishes above some
degree (the number of affines of a finite affine cover; Stacks Tags 01XD, 01FM). -/
theorem exists_H_subsingleton [IsProper f] :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent] (p : ℕ), N ≤ p → Subsingleton (M.H p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := CohomologyAux.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨n, U, hcov, hU⟩ := CohomologyAux.exists_cechCover' X
  refine ⟨n + 1, fun M _ p hp ↦ ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact M.H_subsingleton_of_card_le U hU hcov (by omega)

/-- `hᵖ(X, M) = 0` above the degree given by `exists_H_subsingleton`. -/
lemma finrankH_eq_zero_of_subsingleton (M : X.Modules) (p : ℕ) (h : Subsingleton (M.H p)) :
    finrankH f M p = 0 := by
  let _ := M.moduleOver f p ⊤
  exact Module.finrank_zero_of_subsingleton

/-- On a scheme proper over a field, `χ(X, M)` is the finite sum `Σ_{p < N} (-1)ᵖ hᵖ(X, M)` for
every quasi-coherent `M`, for some `N` independent of `M`. -/
theorem exists_eulerChar_eq_sum_range [IsProper f] :
    ∃ N : ℕ, ∀ (M : X.Modules) [M.IsQuasicoherent],
      eulerChar f M = ∑ p ∈ Finset.range N, (-1 : ℤ) ^ p * (finrankH f M p : ℤ) := by
  obtain ⟨N, hN⟩ := exists_H_subsingleton f
  refine ⟨N, fun M _ ↦ eulerChar_eq_sum f M _ fun p hp ↦ ?_⟩
  rw [Finset.mem_range, not_lt] at hp
  exact finrankH_eq_zero_of_subsingleton f M p (hN M p hp)

/-- **Additivity of the Euler characteristic** (Hartshorne III Ex. 5.1; Stacks Tag 08AA): for a
short exact sequence `0 → M₁ → M₂ → M₃ → 0` of coherent modules on a scheme proper over a field,
`χ(M₂) = χ(M₁) + χ(M₃)`. -/
theorem eulerChar_of_shortExact [IsProper f] {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    eulerChar f S.X₂ = eulerChar f S.X₁ + eulerChar f S.X₃ := by
  obtain ⟨N, hN⟩ := exists_eulerChar_eq_sum_range f
  obtain ⟨N', hN'⟩ := exists_H_subsingleton f
  have : S.X₁.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : S.X₂.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : S.X₃.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  -- Sum up to `max N N'` instead.
  have hsum : ∀ (M : X.Modules) [M.IsQuasicoherent],
      eulerChar f M = ∑ p ∈ Finset.range (N + N'), (-1 : ℤ) ^ p * (finrankH f M p : ℤ) :=
    fun M _ ↦ eulerChar_eq_sum f M _ fun p hp ↦ by
      rw [Finset.mem_range, not_lt] at hp
      exact finrankH_eq_zero_of_subsingleton f M p (hN' M p (by omega))
  rw [hsum S.X₁, hsum S.X₂, hsum S.X₃]
  let ρ := f.specStructureRingHom
  let _ (M : X.Modules) (p : ℕ) : Module k (M.H p) := M.moduleOver f p ⊤
  have hfin : ∀ (M : X.Modules) [M.IsCoherent] (p : ℕ), FiniteDimensional k (M.H p) :=
    fun M _ p ↦ properFinitenessStatement (.of k) X f M p
  have h := Module.sum_alternating_finrank_eq_zero (k := k) (A := fun p ↦ S.X₁.H p)
    (B := fun p ↦ S.X₂.H p) (C := fun p ↦ S.X₃.H p)
    (fun p ↦ CohomologyAux.H'.mapₗ (ρ := ρ) S.f p) (fun p ↦ CohomologyAux.H'.mapₗ (ρ := ρ) S.g p)
    (fun p ↦ CohomologyAux.H'.δₗ (ρ := ρ) hS p) ?_ (fun p ↦ Scheme.Modules.H'.exact_map_map hS p ⊤)
    (fun p ↦ Scheme.Modules.H'.exact_map_δ hS p ⊤) (fun p ↦ Scheme.Modules.H'.exact_δ_map hS p ⊤)
    (N + N') (hN' S.X₁ _ (by omega))
  · rw [eq_comm, ← sub_eq_zero, ← h, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [finrankH]
    ring
  · intro x y hxy
    have h := congrArg (Scheme.Modules.H.equiv₀ S.X₂) hxy
    change Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ x) =
      Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ y) at h
    have e (z : S.X₁.H 0) : Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ z) =
        S.f.app ⊤ (Scheme.Modules.H.equiv₀ S.X₁ z) :=
      CategoryTheory.Sheaf.H'.equiv₀_naturality (Scheme.Modules.Hom.toAbSheaf S.f) z
    rw [e, e] at h
    exact (Scheme.Modules.H.equiv₀ S.X₁).injective
      (CohomologyAux.app_injective_of_shortExact hS ⊤ h)

/-- **Invariance of the Euler characteristic under affine direct images** (EGA III 1.3.3; the
case `Rⁱ j_* = 0`, `i > 0`, of Stacks Tag 0BEK): for
`j : Y ⟶ X` affine, `X` proper over a field and `M` quasi-coherent on `Y`,
`χ(X, j_* M) = χ(Y, M)`, `Y` being a scheme over `k` through `j`. -/
theorem eulerChar_pushforward [IsProper f] {Y : Scheme.{u}} (j : Y ⟶ X) [IsAffineHom j]
    (M : Y.Modules) [M.IsQuasicoherent] :
    eulerChar f ((Scheme.Modules.pushforward j).obj M) = eulerChar (j ≫ f) M := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := CohomologyAux.isAffineHom_diagonal_of_isSeparated f
  have : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward j M
  obtain ⟨n, U, hcov, hU⟩ := CohomologyAux.exists_cechCover X
  let e := CohomologyAux.pushforwardHAddEquiv j M U hcov hU
    (fun x q ↦ M.H'_subsingleton_of_isAffineOpen ((hU x).preimage j) q)
  have hrank : ∀ p, finrankH f ((Scheme.Modules.pushforward j).obj M) p =
      finrankH (j ≫ f) M p := by
    intro p
    let _ := M.moduleOver (j ≫ f) p ⊤
    let _ := ((Scheme.Modules.pushforward j).obj M).moduleOver f p ⊤
    let e' : M.H p ≃ₗ[k] ((Scheme.Modules.pushforward j).obj M).H p :=
      { e p with
        map_smul' := fun r x ↦ by
          have h := CohomologyAux.pushforwardHAddEquiv_smul j M U hcov hU
            (fun x q ↦ M.H'_subsingleton_of_isAffineOpen ((hU x).preimage j) q) p
            (f.specStructureRingHom r) x
          refine Eq.trans ?_ h
          congr 1 }
    exact e'.finrank_eq.symm
  simp only [eulerChar_def, hrank]

/-- `Scheme.Hom.genus f` is `h¹(X, 𝒪_X)` with `𝒪_X` written as `CohomologyAux.unitModule X` (an
abbreviation typed as `X.Modules`, so that the `Scheme.Modules` instances apply and `rw` works). -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.genus_eq_finrankH_unitModule :
    f.genus = finrankH f (CohomologyAux.unitModule X) 1 :=
  rfl

/-- On the empty scheme, `χ(X, M) = 0` for every quasi-coherent `M`. -/
lemma eulerChar_eq_zero_of_isEmpty [IsEmpty X] (M : X.Modules) [M.IsQuasicoherent] :
    eulerChar f M = 0 := by
  rw [eulerChar_eq_sum f M ∅ fun p _ ↦
    finrankH_eq_zero_of_subsingleton f M p (Scheme.Modules.subsingleton_H_of_isEmpty M p)]
  rfl

end Scheme.Modules

end AlgebraicGeometry
