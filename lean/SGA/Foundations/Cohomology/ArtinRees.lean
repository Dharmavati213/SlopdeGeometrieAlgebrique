/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ReesCohomology
import SGA.Foundations.Cohomology.ReesBound
import SGA.Foundations.Cohomology.ProperFiniteness

/-!
# Artin–Rees statements for the cohomology of `Iⁿ M`

Let `A` be noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper and `M` coherent. The key input
of the theorem on formal functions (EGA III 4.1.5; Stacks Tag 02OC) is that the graded module
`⊕ₘ H^q(X, Iᵐ M)` is finite over the Rees algebra `B = ⊕ Iᵏ tᵏ`: it is `H^q(X_B, ⊕ Iᵐ M tᵐ)`, the
cohomology of a coherent module under the proper morphism `X_B ⟶ Spec B`
(`AlgebraicGeometry.properFinitenessStatement`). Consequences:

* `CohomologyAux.exists_range_ιPow_le`: `Im(Hᵖ(X, Iᵐ M) → Hᵖ(X, M)) ⊆ Iⁿ Hᵖ(X, M)` for
  `m ≥ n + c` (the filtration by these images is `I`-good);
* `CohomologyAux.exists_inclPow_eq_zero`: a class of `H^q(X, Iᵐ M)` vanishing in `H^q(X, M)`
  vanishes in `H^q(X, Iⁿ M)` for `m ≥ n + c` (the kernels form an essentially zero system).

The finite generation is used through `CohomologyAux.exists_rees_bound_H`, which combines Leray for
the affine morphism `X_B ⟶ X`, the projections `reesPi` (cohomology commutes with the direct sum
`⊕ Iᵐ M`) and the algebraic bound `CohomologyAux.exists_rees_bound`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf Polynomial

namespace AlgebraicGeometry.CohomologyAux

section Mult

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules)

/-- Multiplication by `a ∈ Iⁿ`, as a morphism `M ⟶ Iⁿ M`. -/
noncomputable def mult0 {n : ℕ} {a : A} (ha : a ∈ I ^ n) : M ⟶ IPow f I M n :=
  kernel.lift _ (smulA M f a) (smulA_comp_cokernel_π f I M ha)

@[reassoc (attr := simp)]
lemma mult0_ιPow {n : ℕ} {a : A} (ha : a ∈ I ^ n) :
    mult0 I f M ha ≫ ιPow f I M n = smulA M f a :=
  kernel.lift_ι _ _ _

/-- `Iʲ M → Iʲ⁺ᵏ M ⊆ Iⁿ M`, multiplication by `a ∈ Iᵏ ∩ Iⁿ`, factors through `Iʲ M ⊆ M`. -/
lemma multPow_inclPow {j k n : ℕ} {a : A} (ha : a ∈ I ^ k) (ha' : a ∈ I ^ n) (h : n ≤ j + k) :
    multPow f I M (n := j) ha ≫ inclPow f I M h = ιPow f I M j ≫ mult0 I f M ha' := by
  rw [← cancel_mono (ιPow f I M n), Category.assoc, inclPow_ιPow, multPow_ιPow, Category.assoc,
    mult0_ιPow]

lemma inclPow_comp {m n l : ℕ} (h₁ : n ≤ m) (h₂ : l ≤ n) :
    inclPow f I M h₁ ≫ inclPow f I M h₂ = inclPow f I M (h₂.trans h₁) := by
  rw [← cancel_mono (ιPow f I M l), Category.assoc, inclPow_ιPow, inclPow_ιPow, inclPow_ιPow]

include I in
lemma H'_map_reesIota_reesPi_self [M.IsQuasicoherent] (q m : ℕ) (y : (IPow f I M m).H q) :
    CategoryTheory.Sheaf.H'.map (reesPi I f M m) q ⊤
      (CategoryTheory.Sheaf.H'.map (reesIota I f M m) q ⊤ y) = y := by
  rw [← CategoryTheory.Sheaf.H'.map_comp_apply, reesIota_reesPi_self,
    CategoryTheory.Sheaf.H'.map_id_apply]

lemma H'_map_reesIota_reesPi_ne [M.IsQuasicoherent] (q : ℕ) {m p : ℕ} (hmp : m ≠ p)
    (y : (IPow f I M m).H q) :
    CategoryTheory.Sheaf.H'.map (reesPi I f M p) q ⊤
      (CategoryTheory.Sheaf.H'.map (reesIota I f M m) q ⊤ y) = 0 := by
  rw [← CategoryTheory.Sheaf.H'.map_comp_apply, reesIota_reesPi_ne I f M hmp,
    CategoryTheory.Sheaf.H'.map_zero_apply]

end Mult

section Bound

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) [IsProper f] (M : X.Modules) [M.IsCoherent]

/-- **The Rees bound in cohomology** (EGA III 4.1.5, proof). Let `f : X ⟶ Spec A` be proper, `A`
noetherian, `M` coherent, and let `Kₘ ⊆ H^q(X, Iᵐ M)` be subgroups. There is `c` such that for all
`n`, every family of additive maps `Φₘ` on `H^q(X, Iᵐ M)` which kills the images of `Kⱼ` under
multiplication by `a ∈ Iᵏ`, for all `j + k = n + c` with `k ≥ n`, kills `K_{n+c}`. This follows
from the finiteness of `H^q(X_B, ⊕ Iᵐ M tᵐ)` over the Rees algebra `B` (EGA III 3.2.1 for the
proper morphism `X_B ⟶ Spec B`, Leray for the affine morphism `X_B ⟶ X`) and
`CohomologyAux.exists_rees_bound`. -/
theorem exists_rees_bound_H (q : ℕ) (K : ∀ m, AddSubgroup ((IPow f I M m).H q)) :
    ∃ c, ∀ (n : ℕ) {T : Type u} [AddCommGroup T] (Φ : ∀ m, (IPow f I M m).H q →+ T),
      (∀ (j k : ℕ) (a : A) (ha : a ∈ I ^ k), j + k = n + c → n ≤ k → ∀ y ∈ K j,
        Φ (j + k) (Scheme.Modules.H'.map (multPow f I M (n := j) ha) q ⊤ y) = 0) →
      ∀ y ∈ K (n + c), Φ (n + c) y = 0 := by
  classical
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated f
  have := isQuasicoherent_reesSheaf I f M
  have := isQuasicoherent_reesPush I f M
  have := isCoherent_reesSheaf I f M
  have := isQuasicoherent_IPow I f M
  obtain ⟨N, U, hcov, hU⟩ := exists_cechCover X
  have hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin N) (q : ℕ),
      Subsingleton ((reesSheaf I f M).H' (q + 1) (reesFst I f ⁻¹ᵁ cechOpen U x)) :=
    fun x q ↦ (reesSheaf I f M).H'_subsingleton_of_isAffineOpen ((hU x).preimage _) q
  let E := pushforwardHAddEquiv (reesFst I f) (reesSheaf I f M) U hcov hU hacyc q
  let _ : Module (reesAlgebra I) ((reesSheaf I f M).H q) :=
    (reesSheaf I f M).moduleOver (reesSnd I f) q ⊤
  have : IsNoetherianRing (reesAlgebra I) := inferInstance
  have hfin : Module.Finite (reesAlgebra I) ((reesSheaf I f M).H q) :=
    properFinitenessStatement (reesRing I) (reesScheme I f) (reesSnd I f) (reesSheaf I f M) q
  let π : ∀ m, (reesSheaf I f M).H q →+ (IPow f I M m).H q := fun m ↦
    (CategoryTheory.Sheaf.H'.map (reesPi I f M m) q ⊤).hom.comp E.toAddMonoidHom
  let μ : ∀ (j : ℕ) {k : ℕ} {a : A}, a ∈ I ^ k → (IPow f I M j).H q →+ (IPow f I M (j + k)).H q :=
    fun j _ _ ha ↦ (Scheme.Modules.H'.map (multPow f I M (n := j) ha) q ⊤).toAddMonoidHom
  have hπ : ∀ m g, π m g = CategoryTheory.Sheaf.H'.map (reesPi I f M m) q ⊤ (E g) := fun _ _ ↦ rfl
  -- `E` intertwines the action of `b ∈ B` with `reesMul b`
  have hE : ∀ (b : reesAlgebra I) g, E (b • g) =
      CategoryTheory.Sheaf.H'.map (reesMul I f M b) q ⊤ (E g) := fun b g ↦
    pushforwardHAddEquiv_naturality (reesFst I f) U q
      ((reesSheaf I f M).smulEnd ((reesSnd I f).specStructureRingHom b)) hcov hU hacyc hacyc g
  have hsupp : ∀ g, ∃ N, ∀ m, N < m → π m g = 0 := fun g ↦
    exists_H'_map_eq_zero (reesPi I f M) (fun _ hV s ↦ exists_reesPi_eq_zero I f M hV s) q (E g)
  have hmul : ∀ {k : ℕ} {a : A} (ha : a ∈ I ^ k) (b : reesAlgebra I),
      (b : A[X]) = monomial k a → ∀ j g, π (j + k) (b • g) = μ j ha (π j g) := by
    intro k a ha b hb j g
    rw [hπ, hπ, hE, ← CategoryTheory.Sheaf.H'.map_comp_apply,
      reesMul_reesPi_monomial I f M ha b hb j, CategoryTheory.Sheaf.H'.map_comp_apply]
    rfl
  have hlt : ∀ {k : ℕ} {a : A} (b : reesAlgebra I), (b : A[X]) = monomial k a →
      ∀ m, m < k → ∀ g, π m (b • g) = 0 := by
    intro k a b hb m hm g
    rw [hπ, hE, ← CategoryTheory.Sheaf.H'.map_comp_apply,
      reesMul_reesPi_monomial_of_lt I f M b hb hm, CategoryTheory.Sheaf.H'.map_zero_apply]
  obtain ⟨c, hc⟩ := exists_rees_bound.{u} I π μ hsupp hmul hlt {g | ∀ m, π m g ∈ K m}
  refine ⟨c, fun n T _ Φ hΦ y hy ↦ ?_⟩
  let s := E.symm (CategoryTheory.Sheaf.H'.map (reesIota I f M (n + c)) q ⊤ y)
  have hEs : E s = CategoryTheory.Sheaf.H'.map (reesIota I f M (n + c)) q ⊤ y :=
    E.apply_symm_apply _
  have hsS : s ∈ {g | ∀ m, π m g ∈ K m} := by
    intro m
    rw [hπ, hEs]
    by_cases hm : n + c = m
    · subst hm
      rw [H'_map_reesIota_reesPi_self I f M]
      exact hy
    · rw [H'_map_reesIota_reesPi_ne I f M q hm]
      exact zero_mem _
  have h := hc n Φ (fun j k a ha hjk hnk g hg ↦ hΦ j k a ha hjk hnk _ (hg j)) s
    (Submodule.subset_span hsS)
  rwa [hπ, hEs, H'_map_reesIota_reesPi_self I f M] at h

/-- **Artin–Rees for the images** (EGA III 4.1.5, proof): there is `c` such that
`Im(Hᵖ(X, Iᵐ M) → Hᵖ(X, M)) ⊆ Iⁿ Hᵖ(X, M)` whenever `n + c ≤ m`. -/
theorem exists_range_ιPow_le (p : ℕ) :
    letI := M.moduleOver f p ⊤
    ∃ c, ∀ m n, n + c ≤ m → ∀ y : (IPow f I M m).H p,
      Scheme.Modules.H'.map (ιPow f I M m) p ⊤ y ∈ (I ^ n • ⊤ : Submodule A (M.H p)) := by
  let _ := M.moduleOver f p ⊤
  obtain ⟨c, hc⟩ := exists_rees_bound_H I f M p (fun _ ↦ ⊤)
  refine ⟨c, fun m n hnm y ↦ ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', m = n' + c := ⟨m - c, by omega⟩
  refine Submodule.smul_mono_left (Ideal.pow_le_pow_right (show n ≤ n' by omega)) ?_
  let Φ : ∀ m, (IPow f I M m).H p →+ M.H p ⧸ (I ^ n' • ⊤ : Submodule A (M.H p)) := fun m ↦
    (Submodule.mkQ _).toAddMonoidHom.comp (Scheme.Modules.H'.map (ιPow f I M m) p ⊤).toAddMonoidHom
  have key := hc n' Φ (fun j k a ha hjk hnk z _ ↦ ?_) y (AddSubgroup.mem_top y)
  · exact (Submodule.Quotient.mk_eq_zero _).mp key
  · change Submodule.Quotient.mk (Scheme.Modules.H'.map (ιPow f I M (j + k)) p ⊤
      (Scheme.Modules.H'.map (multPow f I M ha) p ⊤ z)) = 0
    rw [Submodule.Quotient.mk_eq_zero, ← Scheme.Modules.H'.map_comp_apply, multPow_ιPow,
      Scheme.Modules.H'.map_comp_apply]
    exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right hnk ha) Submodule.mem_top

/-- **Artin–Rees for the kernels** (EGA III 4.1.5, proof): there is `c` such that every class of
`H^q(X, Iᵐ M)` vanishing in `H^q(X, M)` already vanishes in `H^q(X, Iⁿ M)`, whenever
`n + c ≤ m`. -/
theorem exists_inclPow_eq_zero (q : ℕ) :
    ∃ c, ∀ m n (h : n + c ≤ m) (y : (IPow f I M m).H q),
      Scheme.Modules.H'.map (ιPow f I M m) q ⊤ y = 0 →
        Scheme.Modules.H'.map (inclPow f I M (le_of_add_le_left h)) q ⊤ y = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_rees_bound_H I f M q
    (fun m ↦ (Scheme.Modules.H'.map (ιPow f I M m) q ⊤).toAddMonoidHom.ker)
  refine ⟨c, fun m n hnm y hy ↦ ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', m = n' + c := ⟨m - c, by omega⟩
  let Φ : ∀ m, (IPow f I M m).H q →+ (IPow f I M n').H q := fun m ↦
    if h : n' ≤ m then (Scheme.Modules.H'.map (inclPow f I M h) q ⊤).toAddMonoidHom else 0
  have key := hc n' Φ (fun j k a ha hjk hnk z hz ↦ ?_) y ((AddMonoidHom.mem_ker).mpr hy)
  · have h1 : Φ (n' + c) y = Scheme.Modules.H'.map (inclPow f I M (Nat.le_add_right n' c)) q ⊤ y :=
      by simp only [Φ, Nat.le_add_right n' c, ↓reduceDIte]; rfl
    rw [← inclPow_comp I f M (Nat.le_add_right n' c) (show n ≤ n' by omega),
      Scheme.Modules.H'.map_comp_apply, ← h1, key, map_zero]
  · have h : n' ≤ j + k := by omega
    have ha' : a ∈ I ^ n' := Ideal.pow_le_pow_right hnk ha
    have h1 : Φ (j + k) (Scheme.Modules.H'.map (multPow f I M ha) q ⊤ z) =
        Scheme.Modules.H'.map (inclPow f I M h) q ⊤
          (Scheme.Modules.H'.map (multPow f I M ha) q ⊤ z) :=
      by simp only [Φ, h, ↓reduceDIte]; rfl
    rw [h1, ← Scheme.Modules.H'.map_comp_apply, multPow_inclPow I f M ha ha' h,
      Scheme.Modules.H'.map_comp_apply]
    have hz' : Scheme.Modules.H'.map (ιPow f I M j) q ⊤ z = 0 := (AddMonoidHom.mem_ker).mp hz
    rw [hz', map_zero]

end Bound

end AlgebraicGeometry.CohomologyAux
