/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ArtinRees
import SGA.Foundations.Cohomology.CohomologyLemmas

/-!
# The theorem on formal functions

`AlgebraicGeometry.formalFunctionsStatement`: for `A` noetherian, `I ⊆ A`, `f : X ⟶ Spec A`
proper and `M` coherent, the canonical map `Hᵖ(X, M) → lim_n Hᵖ(X, M / I^{n+1} M)` extends to an
isomorphism `Hᵖ(X, M)^ ≅ lim_n Hᵖ(X, M / I^{n+1} M)` from the `I`-adic completion (EGA III 4.1.5;
Stacks Tag 02OC; Hartshorne III.11.1).

Proof (EGA III 4.1.7): the long exact sequences of `0 → I^{n+1} M → M → M / I^{n+1} M → 0` give
`0 → Hᵖ(X, M) / Fₙ → Hᵖ(X, M / I^{n+1} M) → Kₙ → 0` with
`Fₙ = Im(Hᵖ(X, I^{n+1} M) → Hᵖ(X, M))` and `Kₙ = Ker(H^{p+1}(X, I^{n+1} M) → H^{p+1}(X, M))`.
By `CohomologyAux.exists_range_ιPow_le` the filtration `(Fₙ)` is `I`-good, so
`lim Hᵖ(X, M) / Fₙ` is the `I`-adic completion; by `CohomologyAux.exists_inclPow_eq_zero` the
system `(Kₙ)` is essentially zero, so every compatible family lifts. Both facts come from the
finiteness of `⊕ₙ Hᵖ(X, Iⁿ M)` over the Rees algebra (`SGA.Foundations.Cohomology.ArtinRees`).
Here the connecting maps are natural (`Scheme.Modules.H'.δ_naturality`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of short complexes of `𝒪_X`-modules, on the underlying abelian sheaves. -/
noncomputable def abShortComplexMap {S₁ S₂ : ShortComplex X.Modules} (φ : S₁ ⟶ S₂) :
    abShortComplex S₁ ⟶ abShortComplex S₂ where
  τ₁ := Hom.toAbSheaf φ.τ₁
  τ₂ := Hom.toAbSheaf φ.τ₂
  τ₃ := Hom.toAbSheaf φ.τ₃
  comm₁₂ := by
    change (toAbSheafFunctor X).map φ.τ₁ ≫ (toAbSheafFunctor X).map S₂.f =
      (toAbSheafFunctor X).map S₁.f ≫ (toAbSheafFunctor X).map φ.τ₂
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  comm₂₃ := by
    change (toAbSheafFunctor X).map φ.τ₂ ≫ (toAbSheafFunctor X).map S₂.g =
      (toAbSheafFunctor X).map S₁.g ≫ (toAbSheafFunctor X).map φ.τ₃
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]

/-- **Naturality of the connecting maps** of the long exact cohomology sequence. -/
lemma H'.δ_naturality {S₁ S₂ : ShortComplex X.Modules} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ) (U : X.Opens) (x : S₁.X₃.H' n U) :
    H'.δ h₂ n U (H'.map φ.τ₃ n U x) = H'.map φ.τ₁ (n + 1) U (H'.δ h₁ n U x) :=
  comp_extClass_naturality.{u} (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (shortExact_abShortComplex h₁) (shortExact_abShortComplex h₂) (abShortComplexMap φ)
    (H'.toExt x)

end Scheme.Modules

namespace CohomologyAux

section Quot

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A) (M : X.Modules)

/-- The projection `M / I^{m+1} M ⟶ M / I^{n+1} M` for `n ≤ m`. -/
noncomputable def quotMap {m n : ℕ} (h : n ≤ m) :
    M.quotientIdealPow f I m ⟶ M.quotientIdealPow f I n :=
  cokernel.desc _ (M.toQuotientIdealPow f I n) (Sigma.hom_ext _ _ fun a ↦ by
    simp only [Scheme.Modules.idealPowSMul, Sigma.ι_desc_assoc, comp_zero]
    exact M.smulEnd_toQuotientIdealPow f I a.1 (Ideal.pow_le_pow_right (by omega) a.2))

@[reassoc (attr := simp)]
lemma toQuotientIdealPow_quotMap {m n : ℕ} (h : n ≤ m) :
    M.toQuotientIdealPow f I m ≫ quotMap I f M h = M.toQuotientIdealPow f I n :=
  cokernel.π_desc _ _ _

lemma quotMap_self (n : ℕ) : quotMap I f M (le_refl n) = 𝟙 _ := by
  rw [← cancel_epi (M.toQuotientIdealPow f I n), toQuotientIdealPow_quotMap, Category.comp_id]

lemma quotientIdealPowMap_quotMap {m n : ℕ} (h : n ≤ m) :
    M.quotientIdealPowMap f I m ≫ quotMap I f M h = quotMap I f M (h.trans (Nat.le_succ m)) := by
  rw [← cancel_epi (M.toQuotientIdealPow f I (m + 1)),
    Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_quotMap,
    toQuotientIdealPow_quotMap]

/-- Elements of the inverse limit are compatible under all the projections. -/
lemma formalLimit_quotMap (p : ℕ) (x : M.formalLimit f I p) {m n : ℕ} (h : n ≤ m) :
    Scheme.Modules.H'.map (quotMap I f M h) p ⊤ (x.1 m) = x.1 n := by
  induction m, h using Nat.le_induction with
  | base => rw [quotMap_self, Scheme.Modules.H'.map_apply]; exact Sheaf.H'.map_id_apply _
  | succ m hnm ih =>
    rw [← quotientIdealPowMap_quotMap I f M hnm, Scheme.Modules.H'.map_comp_apply, x.2 m, ih]

lemma H'_map_toQuotientIdealPow_quotMap (p : ℕ) {m n : ℕ} (h : n ≤ m) (y : M.H p) :
    Scheme.Modules.H'.map (quotMap I f M h) p ⊤
      (Scheme.Modules.H'.map (M.toQuotientIdealPow f I m) p ⊤ y) =
      Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤ y := by
  rw [← Scheme.Modules.H'.map_comp_apply, toQuotientIdealPow_quotMap]

end Quot

section Main

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules)

/-- The short exact sequence `0 → I^{n+1} M → M → M / I^{n+1} M → 0`. -/
noncomputable abbrev quotSES (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (ιPow f I M (n + 1)) (M.toQuotientIdealPow f I n)
    (ιPow_toQuotientIdealPow f I M n)

/-- The morphism of short exact sequences `quotSES m ⟶ quotSES n` for `n ≤ m`. -/
noncomputable def quotSESMap {m n : ℕ} (h : n ≤ m) : quotSES I f M m ⟶ quotSES I f M n where
  τ₁ := inclPow f I M (Nat.succ_le_succ h)
  τ₂ := 𝟙 M
  τ₃ := quotMap I f M h
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- **Compatible families lift** (EGA III 4.1.7, proof): for `f` proper and `M` coherent, every
component of an element of `lim_n Hᵖ(X, M / I^{n+1} M)` comes from `Hᵖ(X, M)`. This uses that the
kernels of `H^{p+1}(X, I^{n+1} M) → H^{p+1}(X, M)` form an essentially zero system
(`exists_inclPow_eq_zero`). -/
theorem exists_H'_map_toQuotientIdealPow_eq [IsProper f] [M.IsCoherent] (p : ℕ)
    (z : M.formalLimit f I p) (n : ℕ) :
    ∃ y : M.H p, Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤ y = z.1 n := by
  obtain ⟨c₂, hc₂⟩ := exists_inclPow_eq_zero I f M (p + 1)
  have hS (n : ℕ) := shortExact_quotientIdealPow f I M n
  have hδ : Scheme.Modules.H'.δ (hS n) p ⊤ (z.1 n) = 0 := by
    have hnat := Scheme.Modules.H'.δ_naturality (hS (n + c₂)) (hS n)
      (quotSESMap I f M (Nat.le_add_right n c₂)) p ⊤ (z.1 (n + c₂))
    rw [← formalLimit_quotMap I f M p z (Nat.le_add_right n c₂)]
    refine hnat.trans ?_
    exact hc₂ (n + c₂ + 1) (n + 1) (by omega) _
      ((Scheme.Modules.H'.exact_δ_map (hS (n + c₂)) p ⊤ _).mpr ⟨z.1 (n + c₂), rfl⟩)
  exact (Scheme.Modules.H'.exact_map_δ (hS n) p ⊤ (z.1 n)).mp hδ

end Main

end CohomologyAux

open CohomologyAux

/-- **The theorem on formal functions** (EGA III 4.1.5; Stacks Tag 02OC; Hartshorne III.11.1): for
`A` noetherian, `f : X ⟶ Spec A` proper and `M` coherent, the canonical map
`Hᵖ(X, M) → lim_n Hᵖ(X, M / I^{n+1} M)` extends to an `A`-linear isomorphism from the `I`-adic
completion of `Hᵖ(X, M)`. -/
theorem formalFunctionsStatement : FormalFunctionsStatement.{u} := by
  intro A _ I X f _ M _ p
  let _ := M.moduleOver f p ⊤
  let _ := Module.compHom (M.formalLimit f I p) f.specStructureRingHom
  let instQ : ∀ n, Module A ((M.quotientIdealPow f I n).H p) :=
    fun n ↦ (M.quotientIdealPow f I n).moduleOver f p ⊤
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  obtain ⟨c₁, hc₁⟩ := exists_range_ιPow_le I f M p
  have hS (n : ℕ) := shortExact_quotientIdealPow f I M n
  -- the components `Hᵖ(X, M) → Hᵖ(X, M / I^{n+1} M)` of the canonical map, `A`-linearly
  let φ : ∀ n, M.H p →ₗ[A] (M.quotientIdealPow f I n).H p := fun n ↦
    { toFun := Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤
      map_add' := map_add _
      map_smul' := fun a y ↦
        (Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤).map_smul
          (f.specStructureRingHom a) y }
  have hφ (n : ℕ) (y : M.H p) :
      φ n y = Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤ y := rfl
  have hker (n : ℕ) (y : M.H p) :
      φ n y = 0 ↔ y ∈ Set.range (Scheme.Modules.H'.map (ιPow f I M (n + 1)) p ⊤) :=
    Scheme.Modules.H'.exact_map_map (hS n) p ⊤ y
  have hI (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule A (M.H p)) ≤ LinearMap.ker (φ n) := by
    rw [Submodule.smul_le]
    intro a ha y _
    rw [LinearMap.mem_ker, hφ]
    change Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤
      (Scheme.Modules.H'.map (smulA M f a) p ⊤ y) = 0
    rw [← Scheme.Modules.H'.map_comp_apply, M.smulEnd_toQuotientIdealPow f I a ha,
      Scheme.Modules.H'.map_zero, LinearMap.zero_apply]
  let ψ : ∀ n, (M.H p ⧸ (I ^ (n + 1) • ⊤ : Submodule A (M.H p))) →ₗ[A]
      (M.quotientIdealPow f I n).H p := fun n ↦ Submodule.liftQ _ (φ n) (hI n)
  have hψ (n : ℕ) (y : M.H p) : ψ n (Submodule.Quotient.mk y) = φ n y := rfl
  have hφq {m n : ℕ} (h : n ≤ m) (y : M.H p) :
      Scheme.Modules.H'.map (quotMap I f M h) p ⊤ (φ m y) = φ n y :=
    H'_map_toQuotientIdealPow_quotMap I f M p h y
  -- the map `lim_n Hᵖ(X, M) / I^n → lim_n Hᵖ(X, M / I^{n+1} M)`
  have hmem (x : AdicCompletion I (M.H p)) :
      (fun n ↦ ψ n (x.val (n + 1))) ∈ M.formalLimit f I p := by
    intro n
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 2))
    have h1 : x.val (n + 1) = Submodule.Quotient.mk y := by
      rw [← x.property (Nat.le_succ (n + 1)), ← hy]
      rfl
    change Scheme.Modules.H'.map (M.quotientIdealPowMap f I n) p ⊤ (ψ (n + 1) (x.val (n + 2))) =
      ψ n (x.val (n + 1))
    rw [h1, ← hy, hψ, hψ, hφ, hφ, ← Scheme.Modules.H'.map_comp_apply,
      Scheme.Modules.toQuotientIdealPow_comp_map]
  let e₀ : AdicCompletion I (M.H p) →ₗ[A] M.formalLimit f I p :=
    { toFun := fun x ↦ ⟨fun n ↦ ψ n (x.val (n + 1)), hmem x⟩
      map_add' := fun x y ↦ Subtype.ext (funext fun n ↦ map_add (ψ n) _ _)
      map_smul' := fun a x ↦ Subtype.ext (funext fun n ↦ (ψ n).map_smul a (x.val (n + 1))) }
  have he₀ (x : AdicCompletion I (M.H p)) (n : ℕ) : (e₀ x).1 n = ψ n (x.val (n + 1)) := rfl
  -- injectivity: the filtration by the images of `Hᵖ(X, I^{n+1} M)` is `I`-good
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine AdicCompletion.ext fun n ↦ ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + c₁ + 1))
    have h0 : φ (n + c₁) y = 0 := by
      have h := congrArg (fun z : M.formalLimit f I p ↦ z.1 (n + c₁)) hx
      rw [he₀, ← hy, hψ] at h
      exact h
    obtain ⟨w, hw⟩ := (hker _ y).mp h0
    have hyI : y ∈ (I ^ n • ⊤ : Submodule A (M.H p)) := hw ▸ hc₁ (n + c₁ + 1) n (by omega) w
    rw [← x.property (show n ≤ n + c₁ + 1 by omega), ← hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hyI
  -- surjectivity: the kernels of `H^{p+1}(X, I^{n+1} M) → H^{p+1}(X, M)` form an essentially zero
  -- system, so every compatible family lifts
  have hsurj : Function.Surjective e₀ := by
    intro z
    have hlift : ∀ n, ∃ y, φ n y = z.1 n :=
      exists_H'_map_toQuotientIdealPow_eq I f M p z
    choose y hy using hlift
    have hyz {m n : ℕ} (h : n ≤ m) : φ n (y m) = z.1 n := by
      rw [← hφq h, hy, formalLimit_quotMap I f M p z h]
    let w : AdicCompletion.AdicCauchySequence I (M.H p) :=
      AdicCompletion.AdicCauchySequence.mk I (M.H p) (fun k ↦ y (k + c₁)) (fun k ↦ by
        rw [SModEq.sub_mem]
        have h0 : φ (k + c₁) (y (k + c₁) - y (k + 1 + c₁)) = 0 := by
          rw [map_sub, hyz le_rfl, hyz (by omega), sub_self]
        obtain ⟨v, hv⟩ := (hker _ _).mp h0
        exact hv ▸ hc₁ (k + c₁ + 1) k (by omega) v)
    refine ⟨AdicCompletion.mk I (M.H p) w, Subtype.ext (funext fun n ↦ ?_)⟩
    change ψ n (Submodule.Quotient.mk (y (n + 1 + c₁))) = z.1 n
    rw [hψ, hyz (by omega)]
  exact ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun x ↦ rfl⟩

end AlgebraicGeometry
