/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.AffineHom
import SGA.Foundations.Cohomology.SeparatingSections
import SGA.Foundations.Cohomology.QuasiCoherentKernel
import SGA.Foundations.Cohomology.Serre

/-!
# Adic systems of quasi-coherent modules

Let `f : X ⟶ Spec A` and `I ⊆ A` an ideal. An adic system (`CohomologyAux.AdicSystem`; EGA 0_I
7.2, EGA III 5.1) is a sequence of quasi-coherent modules `Gₙ` with maps `Gₙ₊₁ ⟶ Gₙ` which, on
sections over affine opens `U`, are surjective with kernel `I^{n+1} Γ(Gₙ₊₁, U)`. The algebraic
systems are `(F / I^{n+1} F)ₙ` (`AdicSystem.ofModule`); the systems of Grothendieck's existence
theorem are those given by coherent modules on the thickenings `X_n`.

We record the transition maps `G_{j+d} ⟶ G_j` and their kernels, the multiplication maps
`mulUp : Γ(G₀, U) → Γ(Gₖ, U)`, `x ↦ a x̃` for `a ∈ Iᵏ`, the graded pieces
`I^{k+1} G_{k+1} = ker (G_{k+1} ⟶ Gₖ)` (`AdicSystem.grSucc`) and the multiplications
`G₀ ⟶ I^{k+1} G_{k+1}` (`AdicSystem.mulGr`), and the propagation of relations
(`AdicSystem.sum_mulUp_eq_zero`), which makes `⊕ₖ Iᵏ Gₖ` a module over `⊕ₖ Iᵏ / I^{k+1}`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- An **adic system** of quasi-coherent modules on `X` over `(A, I)` (EGA 0_I 7.2, EGA III 5.1):
modules `Gₙ` with transition maps `Gₙ₊₁ ⟶ Gₙ` which, on sections over every affine open `U`,
are surjective with kernel `I^{n+1} Γ(Gₙ₊₁, U)`; equivalently `Gₙ = Gₙ₊₁ / I^{n+1} Gₙ₊₁`. -/
structure AdicSystem where
  /-- The modules `Gₙ`. -/
  obj : ℕ → X.Modules
  /-- The transition maps. -/
  map (n : ℕ) : obj (n + 1) ⟶ obj n
  isQuasicoherent (n : ℕ) : (obj n).IsQuasicoherent
  surjective (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective ((map n).app U)
  map_app_eq_zero_iff (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(obj (n + 1), U)) :
    (map n).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(obj (n + 1), U))

namespace AdicSystem

variable {I f} (G : AdicSystem I f)

instance (n : ℕ) : (G.obj n).IsQuasicoherent := G.isQuasicoherent n

/-- The image of `J • ⊤` under a surjective linear map is `J • ⊤`. -/
lemma mem_map_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (φ : M →ₗ[R] N) (hφ : Function.Surjective φ)
    {y : N} (hy : y ∈ (J • ⊤ : Submodule R N)) : ∃ x ∈ (J • ⊤ : Submodule R M), φ x = y := by
  have : (J • ⊤ : Submodule R M).map φ = J • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  rw [← this] at hy
  exact hy

/-- `Gₙ` is killed by `I^{n+1}`. -/
lemma eq_zero_of_mem (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {s : Γ(G.obj n, U)}
    (hs : s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj n, U))) : s = 0 := by
  obtain ⟨t, ht, rfl⟩ := mem_map_smul_top _ (appLinearMap (G.map n) U) (G.surjective n hU) hs
  exact (G.map_app_eq_zero_iff n hU t).mpr ht

lemma smul_eq_zero (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {c : Γ(X, U)}
    (hc : c ∈ idealV f I U 1 ^ (n + 1)) (s : Γ(G.obj n, U)) : c • s = 0 :=
  G.eq_zero_of_mem n hU (Submodule.smul_mem_smul hc Submodule.mem_top)

/-- The projection `Gₖ ⟶ G₀`. -/
def toZero : ∀ k, G.obj k ⟶ G.obj 0
  | 0 => 𝟙 _
  | k + 1 => G.map k ≫ toZero k

@[simp] lemma toZero_zero : G.toZero 0 = 𝟙 _ := rfl

lemma toZero_succ (k : ℕ) : G.toZero (k + 1) = G.map k ≫ G.toZero k := rfl

lemma toZero_surjective (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((G.toZero k).app U) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih =>
    rw [toZero_succ, Scheme.Modules.Hom.comp_app]
    exact ih.comp (G.surjective k hU)

lemma toZero_app_eq_zero_iff (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(G.obj k, U)) :
    (G.toZero k).app U s = 0 ↔
      s ∈ (idealV f I U 1 • ⊤ : Submodule Γ(X, U) Γ(G.obj k, U)) := by
  induction k with
  | zero =>
    refine ⟨fun h ↦ ?_, fun h ↦ G.eq_zero_of_mem 0 hU (by simpa using h)⟩
    have : s = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ k ih =>
    rw [toZero_succ, Scheme.Modules.Hom.comp_app_apply, ih]
    constructor
    · intro h
      obtain ⟨t, ht, e⟩ := mem_map_smul_top _ (appLinearMap (G.map k) U) (G.surjective k hU) h
      have hst : s - t ∈ (idealV f I U 1 ^ (k + 1) • ⊤ : Submodule Γ(X, U) _) := by
        rw [← G.map_app_eq_zero_iff k hU, map_sub, sub_eq_zero]
        exact e.symm
      have hle : idealV f I U 1 ^ (k + 1) ≤ idealV f I U 1 := Ideal.pow_le_self (by omega)
      have := Submodule.smul_mono_left (N := (⊤ : Submodule Γ(X, U) Γ(G.obj (k + 1), U))) hle hst
      simpa using Submodule.add_mem _ this ht
    · intro h
      have := Submodule.mem_map_of_mem (f := appLinearMap (G.map k) U) h
      rw [Submodule.map_smul'', Submodule.map_top] at this
      exact Submodule.smul_mono le_rfl le_top this

/-- The transition `G_{j+d} ⟶ G_j`. -/
def transition (j : ℕ) : ∀ d, G.obj (j + d) ⟶ G.obj j
  | 0 => 𝟙 _
  | d + 1 => G.map (j + d) ≫ transition j d

lemma transition_succ (j d : ℕ) :
    G.transition j (d + 1) = G.map (j + d) ≫ G.transition j d := rfl

lemma toZero_add (j d : ℕ) : G.toZero (j + d) = G.transition j d ≫ G.toZero j := by
  induction d with
  | zero => exact (Category.id_comp _).symm
  | succ d ih => rw [transition_succ, Category.assoc, ← ih]; rfl

lemma transition_surjective (j d : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((G.transition j d).app U) := by
  induction d with
  | zero => exact Function.surjective_id
  | succ d ih =>
    rw [transition_succ, Scheme.Modules.Hom.comp_app]
    exact ih.comp (G.surjective (j + d) hU)

lemma transition_app_eq_zero_iff (j d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(G.obj (j + d), U)) :
    (G.transition j d).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (j + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj (j + d), U)) := by
  induction d with
  | zero =>
    refine ⟨fun h ↦ ?_, fun h ↦ G.eq_zero_of_mem j hU h⟩
    have : s = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ d ih =>
    rw [transition_succ, Scheme.Modules.Hom.comp_app_apply, ih]
    constructor
    · intro h
      obtain ⟨t, ht, e⟩ :=
        mem_map_smul_top _ (appLinearMap (G.map (j + d)) U) (G.surjective (j + d) hU) h
      have hst : s - t ∈ (idealV f I U 1 ^ (j + d + 1) • ⊤ : Submodule Γ(X, U) _) := by
        rw [← G.map_app_eq_zero_iff (j + d) hU, map_sub, sub_eq_zero]
        exact e.symm
      have hle : idealV f I U 1 ^ (j + d + 1) ≤ idealV f I U 1 ^ (j + 1) :=
        Ideal.pow_le_pow_right (by omega)
      have := Submodule.smul_mono_left (N := (⊤ : Submodule Γ(X, U) Γ(G.obj (j + d + 1), U)))
        hle hst
      simpa using Submodule.add_mem _ this ht
    · intro h
      have := Submodule.mem_map_of_mem (f := appLinearMap (G.map (j + d)) U) h
      rw [Submodule.map_smul'', Submodule.map_top] at this
      exact Submodule.smul_mono le_rfl le_top this

/-- `idealV f I U k = (I Γ(X, U))^k`. -/
lemma idealV_eq_pow (U : X.Opens) (k : ℕ) : idealV f I U k = idealV f I U 1 ^ k := by
  rw [idealV, idealV, Ideal.map_pow, pow_one]

lemma structMapV_mem_pow {U : X.Opens} {k : ℕ} {a : A} (ha : a ∈ I ^ k) :
    structMapV f U a ∈ idealV f I U 1 ^ k := by
  rw [← idealV_eq_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- **Multiplication from level `0`**: for `a ∈ Iᵏ`, the map `Γ(G₀, U) → Γ(Gₖ, U)`,
`x ↦ a x̃` for any lift `x̃` of `x` (well defined since `Gₖ` is killed by `I^{k+1}`). -/
def mulUp (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {a : A} (ha : a ∈ I ^ k) :
    Γ(G.obj 0, U) →ₗ[Γ(X, U)] Γ(G.obj k, U) :=
  (LinearMap.ker (appLinearMap (G.toZero k) U)).liftQ (structMapV f U a • LinearMap.id)
      (fun s hs ↦ by
        rw [LinearMap.mem_ker, appLinearMap_apply, G.toZero_app_eq_zero_iff k hU] at hs
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        refine G.eq_zero_of_mem k hU ?_
        have := Submodule.smul_mem_smul (structMapV_mem_pow (f := f) (U := U) ha) hs
        rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ] at this
        exact this) ∘ₗ
    ((appLinearMap (G.toZero k) U).quotKerEquivOfSurjective (G.toZero_surjective k hU)).symm

lemma mulUp_toZero (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {a : A} (ha : a ∈ I ^ k)
    (y : Γ(G.obj k, U)) :
    G.mulUp k hU ha ((G.toZero k).app U y) = structMapV f U a • y := by
  have : ((appLinearMap (G.toZero k) U).quotKerEquivOfSurjective
      (G.toZero_surjective k hU)).symm ((G.toZero k).app U y) = Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [mulUp, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply,
    LinearMap.smul_apply, LinearMap.id_apply]

lemma structMapV_res {U W : X.Opens} (h : W ≤ U) (a : A) :
    X.presheaf.map (homOfLE h).op (structMapV f U a) = structMapV f W a := by
  rw [structMapV_eq_map, structMapV_eq_map, presheaf_map_map]

lemma mulUp_res (k : ℕ) {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)
    {a : A} (ha : a ∈ I ^ k) (x : Γ(G.obj 0, U)) :
    G.mulUp k hW ha ((G.obj 0).presheaf.map (homOfLE h).op x) =
      (G.obj k).presheaf.map (homOfLE h).op (G.mulUp k hU ha x) := by
  obtain ⟨y, rfl⟩ := G.toZero_surjective k hU x
  rw [← hom_app_presheaf_map, mulUp_toZero, mulUp_toZero, Scheme.Modules.map_smul,
    structMapV_res]

/-- Lifting from level `0` through level `j`: `G_{j+d} → G_j` maps `a x̃` to `a x̃`. -/
lemma transition_mulUp (j d : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {a : A}
    (ha : a ∈ I ^ (j + d)) (ha' : a ∈ I ^ j) (x : Γ(G.obj 0, U)) :
    (G.transition j d).app U (G.mulUp (j + d) hU ha x) = G.mulUp j hU ha' x := by
  obtain ⟨y, rfl⟩ := G.toZero_surjective (j + d) hU x
  rw [mulUp_toZero, Scheme.Modules.Hom.app_smul, toZero_add, Scheme.Modules.Hom.comp_app_apply,
    mulUp_toZero]

/-- **The relations propagate**: if `Σ aₗ xₗ = 0` at level `j` (`aₗ ∈ Iʲ`), then
`Σ c aₗ xₗ = 0` at level `j + d` for `c ∈ Iᵈ`. -/
lemma sum_mulUp_eq_zero {ι : Type*} (s : Finset ι) (j d : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) (a : ι → A) (ha : ∀ l, a l ∈ I ^ j) {c : A} (hc : c ∈ I ^ d)
    (x : ι → Γ(G.obj 0, U)) (hx : ∑ l ∈ s, G.mulUp j hU (ha l) (x l) = 0) :
    ∑ l ∈ s, G.mulUp (j + d) hU (show c * a l ∈ I ^ (j + d) by
      rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hc (ha l)) (x l) = 0 := by
  choose y hy using fun l ↦ G.toZero_surjective (j + d) hU (x l)
  simp only [← hy, mulUp_toZero, map_mul, mul_smul]
  rw [← Finset.smul_sum]
  set S := ∑ l ∈ s, structMapV f U (a l) • y l
  have hS : (G.transition j d).app U S = 0 := by
    rw [← hx]
    simp only [S, map_sum, Scheme.Modules.Hom.app_smul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← hy l, toZero_add, Scheme.Modules.Hom.comp_app_apply, mulUp_toZero]
  rw [G.transition_app_eq_zero_iff j d hU] at hS
  refine G.eq_zero_of_mem (j + d) hU ?_
  have := Submodule.smul_mem_smul (structMapV_mem_pow (f := f) (U := U) hc) hS
  rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_add, show d + (j + 1) = j + d + 1 by omega]
    at this
  exact this

section Gr

/-- The transition maps are epimorphisms. -/
instance epi_map (n : ℕ) : Epi (G.map n) :=
  epi_of_surjective_app _ (G.map n) (fun V : X.affineOpens ↦ V.1) (iSup_affineOpens_eq_top X)
    (fun V ↦ V.2) fun V ↦ G.surjective n V.2

/-- The graded piece `I^{k+1} G_{k+1} = ker (G_{k+1} ⟶ G_k)`. -/
abbrev grSucc (k : ℕ) : X.Modules := kernel (G.map k)

lemma shortExact_grSucc (k : ℕ) :
    (ShortComplex.mk (kernel.ι (G.map k)) (G.map k) (kernel.condition _)).ShortExact :=
  shortExact_kernelSequence (G.map k)

instance (k : ℕ) : (G.grSucc k).IsQuasicoherent :=
  isQuasicoherent_X₁_of_shortExact (G.shortExact_grSucc k)

lemma grSucc_ι_app_injective (k : ℕ) (U : X.Opens) :
    Function.Injective ((kernel.ι (G.map k)).app U) :=
  app_injective_of_shortExact (G.shortExact_grSucc k) U

lemma mem_range_grSucc_ι (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(G.obj (k + 1), U)) :
    s ∈ Set.range ((kernel.ι (G.map k)).app U) ↔
      s ∈ (idealV f I U 1 ^ (k + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj (k + 1), U)) := by
  rw [← G.map_app_eq_zero_iff k hU]
  constructor
  · rintro ⟨t, rfl⟩
    rw [← Scheme.Modules.Hom.comp_app_apply, kernel.condition]
    rfl
  · exact exists_app_eq_of_shortExact (G.shortExact_grSucc k) U s

/-- Lift of a linear map through an injective linear map containing its range. -/
def liftLinear {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] (ι : P →ₗ[R] N) (hι : Function.Injective ι)
    (φ : M →ₗ[R] N) (h : ∀ m, φ m ∈ LinearMap.range ι) : M →ₗ[R] P :=
  (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ φ.codRestrict _ h

lemma liftLinear_spec {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (ι : P →ₗ[R] N)
    (hι : Function.Injective ι) (φ : M →ₗ[R] N) (h : ∀ m, φ m ∈ LinearMap.range ι) (m : M) :
    ι (liftLinear ι hι φ h m) = φ m := by
  simp only [liftLinear, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact LinearEquiv.ofInjective_symm_apply ι (h := hι) _

/-- The multiplication `Γ(G₀, U) → Γ(I^{k+1} G_{k+1}, U)`, `x ↦ a x̃`, for `a ∈ I^{k+1}`. -/
def mulGrFun (k : ℕ) {a : A} (ha : a ∈ I ^ (k + 1)) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(G.obj 0, U) →ₗ[Γ(X, U)] Γ(G.grSucc k, U) :=
  liftLinear (appLinearMap (kernel.ι (G.map k)) U) (G.grSucc_ι_app_injective k U)
    (G.mulUp (k + 1) hU ha) fun x ↦ by
      obtain ⟨y, rfl⟩ := G.toZero_surjective (k + 1) hU x
      rw [mulUp_toZero]
      exact (G.mem_range_grSucc_ι k hU _).mpr
        (Submodule.smul_mem_smul (structMapV_mem_pow ha) Submodule.mem_top)

lemma mulGrFun_spec (k : ℕ) {a : A} (ha : a ∈ I ^ (k + 1)) {U : X.Opens} (hU : IsAffineOpen U)
    (x : Γ(G.obj 0, U)) :
    (kernel.ι (G.map k)).app U (G.mulGrFun k ha hU x) = G.mulUp (k + 1) hU ha x := by
  have h := liftLinear_spec (appLinearMap (kernel.ι (G.map k)) U) (G.grSucc_ι_app_injective k U)
    (G.mulUp (k + 1) hU ha) (fun x ↦ by
      obtain ⟨y, rfl⟩ := G.toZero_surjective (k + 1) hU x
      rw [mulUp_toZero]
      exact (G.mem_range_grSucc_ι k hU _).mpr
        (Submodule.smul_mem_smul (structMapV_mem_pow ha) Submodule.mem_top)) x
  exact h

/-- The multiplication `G₀ ⟶ I^{k+1} G_{k+1}`, `x ↦ a x̃`, for `a ∈ I^{k+1}`. -/
def mulGr (k : ℕ) {a : A} (ha : a ∈ I ^ (k + 1)) : G.obj 0 ⟶ G.grSucc k :=
  AffineHomData.toHom
    { toFun U hU := G.mulGrFun k ha hU
      naturality {V W} hV hW h x := by
        apply G.grSucc_ι_app_injective k W
        rw [mulGrFun_spec, hom_app_presheaf_map, mulGrFun_spec]
        exact G.mulUp_res (k + 1) hV hW h ha x }

lemma mulGr_app (k : ℕ) {a : A} (ha : a ∈ I ^ (k + 1)) {U : X.Opens} (hU : IsAffineOpen U)
    (x : Γ(G.obj 0, U)) :
    (kernel.ι (G.map k)).app U ((G.mulGr k ha).app U x) = G.mulUp (k + 1) hU ha x := by
  rw [mulGr, AffineHomData.toHom_app _ hU]
  exact G.mulGrFun_spec k ha hU x

end Gr

end AdicSystem

section OfModule

variable [IsNoetherianRing A] (F : X.Modules) [F.IsQuasicoherent]

lemma quotientIdealPow_app_eq_zero_iff (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(F, U)) : (F.toQuotientIdealPow f I n).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(F, U)) := by
  rw [toQuotientIdealPow_app_eq_zero_iff, mem_range_ιPow_app f I F hU, AdicSystem.idealV_eq_pow]

instance isQuasicoherent_quotientIdealPow (n : ℕ) :
    (F.quotientIdealPow f I n).IsQuasicoherent :=
  have : (⨁ fun _ : Fin (numGens I (n + 1)) ↦ F).IsQuasicoherent := isQuasicoherent_biproduct _
  have : (cokernel (powMap f I F (n + 1))).IsQuasicoherent := isQuasicoherent_cokernel _
  Scheme.Modules.isQuasicoherent_of_iso (cokernelPowMapIso f I F n)

/-- The adic system `(F / I^{n+1} F)ₙ` of a quasi-coherent module. -/
def ofModule : AdicSystem I f where
  obj n := F.quotientIdealPow f I n
  map n := F.quotientIdealPowMap f I n
  isQuasicoherent n := inferInstance
  surjective n U hU := by
    intro y
    obtain ⟨t, rfl⟩ := toQuotientIdealPow_app_surjective I f n hU (M := F) y
    refine ⟨(F.toQuotientIdealPow f I (n + 1)).app U t, ?_⟩
    rw [← Scheme.Modules.Hom.comp_app_apply, Scheme.Modules.toQuotientIdealPow_comp_map]
  map_app_eq_zero_iff n U hU s := by
    constructor
    · intro h
      obtain ⟨t, rfl⟩ := toQuotientIdealPow_app_surjective I f (n + 1) hU (M := F) s
      rw [← Scheme.Modules.Hom.comp_app_apply, Scheme.Modules.toQuotientIdealPow_comp_map,
        quotientIdealPow_app_eq_zero_iff I f F n hU] at h
      have := Submodule.mem_map_of_mem
        (f := appLinearMap (F.toQuotientIdealPow f I (n + 1)) U) h
      rw [Submodule.map_smul'', Submodule.map_top] at this
      exact Submodule.smul_mono le_rfl le_top this
    · intro h
      obtain ⟨t, ht, rfl⟩ := AdicSystem.mem_map_smul_top _
        (appLinearMap (F.toQuotientIdealPow f I (n + 1)) U)
        (toQuotientIdealPow_app_surjective I f (n + 1) hU (M := F)) h
      change (F.quotientIdealPowMap f I n).app U ((F.toQuotientIdealPow f I (n + 1)).app U t) = 0
      rw [← Scheme.Modules.Hom.comp_app_apply, Scheme.Modules.toQuotientIdealPow_comp_map,
        quotientIdealPow_app_eq_zero_iff I f F n hU]
      exact ht

@[simp] lemma ofModule_obj (n : ℕ) : (ofModule I f F).obj n = F.quotientIdealPow f I n := rfl

@[simp] lemma ofModule_map (n : ℕ) : (ofModule I f F).map n = F.quotientIdealPowMap f I n := rfl

end OfModule

end AlgebraicGeometry.CohomologyAux
