/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Artin–Rees for modules of homomorphisms

Let `R` be a noetherian ring, `J ⊆ R` an ideal and `M`, `N` finite `R`-modules. The systems
`Hom(M, N) / Jⁿ Hom(M, N)` and `Hom(M, N / Jⁿ N)` are pro-isomorphic; this is the algebraic
input of the full faithfulness in Grothendieck's existence theorem (proof of EGA III 5.1.4). We
prove the two halves in the form needed there:

* `CohomologyAux.exists_mem_pow_smul_of_forall_apply_mem`: a linear map with values in `J^{n+c} N`
  lies in `Jⁿ Hom(M, N)`;
* `CohomologyAux.exists_lift_comp_eq`: a linear map `M → N / J^{n+c} N`, reduced modulo `Jⁿ`,
  lifts to `M → N`.

Both follow from the Artin–Rees lemma (`Ideal.exists_pow_inf_eq_pow_smul`), applied to the image
of `Hom(M, N)` in `Nᵇ` (via generators of `M`) and to the image of `Hom(Rᵇ, N)` in `Hom(K, N)` for a
presentation `0 → K → Rᵇ → M → 0`.
-/

universe u v w

namespace AlgebraicGeometry.CohomologyAux

section ArtinReesHom

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

omit [IsNoetherianRing R] in
/-- A tuple whose entries lie in `J^k N` lies in `J^k Nᵇ`. -/
lemma pi_mem_pow_smul_top {N : Type v} [AddCommGroup N] [Module R N] {b : ℕ} (k : ℕ)
    (t : Fin b → N) (ht : ∀ i, t i ∈ (J ^ k • ⊤ : Submodule R N)) :
    t ∈ (J ^ k • ⊤ : Submodule R (Fin b → N)) := by
  classical
  rw [← Finset.univ_sum_single t]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have h1 : Pi.single i (t i) ∈
      (J ^ k • ⊤ : Submodule R N).map (LinearMap.single R (fun _ ↦ N) i) :=
    Submodule.mem_map_of_mem (ht i)
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

omit [IsNoetherianRing R] in
/-- The values of an element of `J^k Hom(M, N)` lie in `J^k N`. -/
lemma apply_mem_pow_smul_top {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (k : ℕ) {φ : M →ₗ[R] N} (hφ : φ ∈ (J ^ k • ⊤ : Submodule R (M →ₗ[R] N)))
    (m : M) : φ m ∈ (J ^ k • ⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on (p := fun ψ : M →ₗ[R] N ↦ ψ m ∈ (J ^ k • ⊤ : Submodule R N))
    hφ (fun a ha ψ _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy

/-- **Artin–Rees for `Hom`** (the "kernel" half of the pro-isomorphism
`Hom(M, N) / Jⁿ ~ Hom(M, N / Jⁿ N)`): for `M`, `N` finite over a noetherian ring, a linear map
`M → N` with values in `J^{n+c} N` lies in `Jⁿ Hom(M, N)`, for a constant `c`. -/
theorem exists_mem_pow_smul_of_forall_apply_mem {M : Type*} {N : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : M →ₗ[R] N), (∀ m, φ m ∈ (J ^ (n + c) • ⊤ : Submodule R N)) →
      φ ∈ (J ^ n • ⊤ : Submodule R (M →ₗ[R] N)) := by
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R M
  let ev : (M →ₗ[R] N) →ₗ[R] (Fin b → N) :=
    LinearMap.pi fun i ↦ LinearMap.applyₗ (π (Pi.single i 1))
  have hev : Function.Injective ev := by
    intro φ ψ h
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨x, rfl⟩ := hπ m
    classical
    have hx : x = ∑ i, x i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := congrFun h i
    simp only [ev, LinearMap.pi_apply, LinearMap.applyₗ_apply_apply] at this
    simp only [map_smul, this]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul J (LinearMap.range ev)
  refine ⟨c, fun n φ hφ ↦ ?_⟩
  have h1 : ev φ ∈ (J ^ (n + c) • ⊤ : Submodule R (Fin b → N)) ⊓ LinearMap.range ev :=
    ⟨pi_mem_pow_smul_top J _ _ fun i ↦ hφ _, ⟨φ, rfl⟩⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel] at h1
  have h2 : ev φ ∈ (J ^ n • ⊤ : Submodule R (M →ₗ[R] N)).map ev := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨ψ, hψ, hψφ⟩ := h2
  rw [← hev hψφ]
  exact hψ

/-- **Artin–Rees for `Hom`**, the "cokernel" half: for `M`, `N` finite over a noetherian ring there
is `c` such that every linear map `M → N / J^{n+c} N`, reduced modulo `Jⁿ`, lifts to a linear map
`M → N`. Here `N / J^{n+c} N` and `N / Jⁿ N` are given as
surjections `q : N → Q` with kernel inside `J^{n+c} N` and `q' : N → Q'` killing `Jⁿ N`, with a
transition map `T : Q → Q'`. -/
theorem exists_lift_comp_eq {M : Type*} {N : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ c : ℕ, ∀ (n : ℕ) {Q Q' : Type w} [AddCommGroup Q] [Module R Q] [AddCommGroup Q']
      [Module R Q'] (q : N →ₗ[R] Q) (q' : N →ₗ[R] Q') (T : Q →ₗ[R] Q'),
      Function.Surjective q → LinearMap.ker q ≤ J ^ (n + c) • ⊤ →
      J ^ n • ⊤ ≤ LinearMap.ker q' → T ∘ₗ q = q' →
      ∀ w : M →ₗ[R] Q, ∃ φ : M →ₗ[R] N, q' ∘ₗ φ = T ∘ₗ w := by
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R M
  let K := LinearMap.ker π
  have : Module.Finite R K := Module.IsNoetherian.finite R K
  let Res : ((Fin b → R) →ₗ[R] N) →ₗ[R] (K →ₗ[R] N) := LinearMap.lcomp R N K.subtype
  have : Module.Finite R (K →ₗ[R] N) := by
    obtain ⟨b', π', hπ'⟩ := Module.Finite.exists_fin' R K
    let pre : (K →ₗ[R] N) →ₗ[R] ((Fin b' → R) →ₗ[R] N) := LinearMap.lcomp R N π'
    have hinj : Function.Injective pre := fun f g h ↦ LinearMap.ext fun m ↦ by
      obtain ⟨x, rfl⟩ := hπ' m
      exact LinearMap.congr_fun h x
    exact Module.Finite.of_injective pre hinj
  obtain ⟨c₁, hc₁⟩ := exists_mem_pow_smul_of_forall_apply_mem J (M := K) (N := N)
  obtain ⟨c₂, hc₂⟩ := Ideal.exists_pow_inf_eq_pow_smul J (LinearMap.range Res)
  refine ⟨c₁ + c₂, fun n Q Q' _ _ _ _ q q' T hq hker hker' hT w ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property q (w ∘ₗ π) hq
  -- `ψ` maps `K` into `J^{n+c} N`
  have hψK : ∀ x : K, ψ x ∈ (J ^ ((n + c₂) + c₁) • ⊤ : Submodule R N) := by
    intro x
    have h0 : q (ψ x) = 0 := by
      have := LinearMap.congr_fun hψ x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2, map_zero] at this
      exact this
    have := hker (LinearMap.mem_ker.mpr h0)
    rwa [show n + (c₁ + c₂) = n + c₂ + c₁ by omega] at this
  have h1 : Res ψ ∈ (J ^ (n + c₂) • ⊤ : Submodule R (K →ₗ[R] N)) ⊓ LinearMap.range Res :=
    ⟨hc₁ (n + c₂) (Res ψ) hψK, ⟨ψ, rfl⟩⟩
  rw [hc₂ (n + c₂) (Nat.le_add_left c₂ n), Nat.add_sub_cancel] at h1
  have h2 : Res ψ ∈ (J ^ n • ⊤ : Submodule R ((Fin b → R) →ₗ[R] N)).map Res := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨ζ, hζ, hζψ⟩ := h2
  -- `ψ - ζ` kills `K`, hence factors through `M`
  have hK : K ≤ LinearMap.ker (ψ - ζ) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact (LinearMap.congr_fun hζψ ⟨x, hx⟩).symm
  let φ : M →ₗ[R] N := K.liftQ (ψ - ζ) hK ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hφ : ∀ x, φ (π x) = ψ x - ζ x := by
    intro x
    change K.liftQ (ψ - ζ) hK ((π.quotKerEquivOfSurjective hπ).symm (π x)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply,
      LinearMap.sub_apply]
  refine ⟨φ, LinearMap.ext fun m ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hπ m
  rw [LinearMap.comp_apply, hφ, map_sub,
    LinearMap.mem_ker.mp (hker' (apply_mem_pow_smul_top J n hζ x)), sub_zero, ← hT,
    LinearMap.comp_apply, ← LinearMap.comp_apply q ψ, hψ]
  rfl

end ArtinReesHom

end AlgebraicGeometry.CohomologyAux
