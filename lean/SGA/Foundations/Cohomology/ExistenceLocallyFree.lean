/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.UniformVanishing
import SGA.Foundations.Cohomology.TwistGeneration
import SGA.Foundations.Cohomology.HomTwist


/-!
# Grothendieck's existence theorem for locally free adic systems on projective schemes

Let `A` be a noetherian `I`-adically complete ring and `κ : X ⟶ ℙ(τ; Spec A)` a closed immersion.
We prove that every *locally free* adic system `(Gₙ)` on `X` (`AdicSystem.IsLocallyFree`: over
affine opens, the sections of `Gₙ` are projective modules over `Γ(X, U) / I^{n+1}`) with `G₀`
coherent is the system `(F / I^{n+1} F)` of a coherent `F`
(`AdicSystem.exists_iso_quotientIdealPow_of_isLocallyFree`; EGA III 5.1.4 / 5.2 in the projective
case, Hartshorne II.9.6). This is the case of Grothendieck's existence theorem needed for the
algebraization of finite étale covers (SGA 1 IX.1.10, X.2.1).

* `twistFree L d k = (L^{⊗ -d})^{⊕ k}` and `twistFreeDesc`: morphisms out of it given by global
  sections of twists, `epi_twistFreeDesc`.
* `AdicSystem.exists_compatible_epi`: compatible epimorphisms `𝒪_X(-d)^k ⟶ Gₙ` (global
  generation of `G₀(d)`, `exists_epi_homOfSection_twist`, lifting of sections by the uniform
  vanishing of `H¹(X, I^{n+1} G_{n+1}(d))`, `AdicSystem.exists_subsingleton_H_twist_grSucc`, and
  Nakayama, `AdicSystem.epi_of_epi_comp_toZero`).
* `AdicSystem.kernelSystem`: the kernels of an epimorphism of adic systems onto a locally free one
  form an adic system.
* `descQuotientIdealPow`, `AdicSystem.smulA_eq_zero`: morphisms into modules killed by `I^{n+1}`
  factor through `M / I^{n+1} M`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section Helpers

variable {X : Scheme.{u}}

/-- An epimorphism of quasi-coherent modules is surjective on sections over affine opens. -/
lemma app_surjective_of_epi {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : P ⟶ Q) [Epi φ] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  have hS := shortExact_kernelSequence φ
  have : (kernel φ).IsQuasicoherent := isQuasicoherent_kernel φ
  exact TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
    (Scheme.Modules.shortExact_abShortComplex hS) U
    ((kernel φ).H'_subsingleton_of_isAffineOpen hU 0)

/-- **Nakayama's lemma for a nilpotent ideal**: if `N + J M = M` and `J^n M = 0` then `N = M`. -/
lemma Submodule.eq_top_of_sup_smul_eq_top_of_pow {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (J : Ideal R) (N : Submodule R M) (h : N ⊔ J • ⊤ = ⊤) (n : ℕ)
    (hn : J ^ n • (⊤ : Submodule R M) = ⊥) : N = ⊤ := by
  have key : ∀ m : ℕ, N ⊔ J ^ m • ⊤ = ⊤ := by
    intro m
    induction m with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ m ih =>
      apply top_le_iff.mp
      calc ⊤ = N ⊔ J ^ m • ⊤ := ih.symm
        _ = N ⊔ J ^ m • (N ⊔ J • ⊤) := by rw [h]
        _ ≤ N ⊔ J ^ (m + 1) • ⊤ := by
          rw [Submodule.smul_sup, ← Submodule.smul_assoc, smul_eq_mul, ← pow_succ]
          exact sup_le (le_sup_left) (sup_le ((Submodule.smul_le_right).trans le_sup_left)
            le_sup_right)
  have := key n
  rwa [hn, sup_bot_eq] at this

end Helpers

section TwistFree

/-- Precomposing the components of an epimorphism out of a biproduct with isomorphisms keeps it
epi. -/
lemma epi_biproduct_desc_iso_comp {C : Type*} [Category C] [Preadditive C] {J : Type}
    [Finite J] [HasFiniteBiproducts C] {f g : J → C} {W : C} (e : ∀ j, f j ≅ g j)
    (h : ∀ j, g j ⟶ W) [Epi (biproduct.desc h)] :
    Epi (biproduct.desc fun j ↦ (e j).hom ≫ h j) := by
  refine ⟨fun u v huv ↦ ?_⟩
  have : biproduct.desc h ≫ u = biproduct.desc h ≫ v := by
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    have := biproduct.ι _ j ≫= huv
    simp only [biproduct.ι_desc_assoc, Category.assoc] at this ⊢
    exact (cancel_epi (e j).hom).mp this
  exact (cancel_epi _).mp this

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- The module `(L^{⊗ -d})^{⊕ k}`. -/
abbrev twistFree (d : ℤ) (k : ℕ) : X.Modules := ⨁ fun _ : Fin k ↦ L.toModules (-d)

instance (d : ℤ) (k : ℕ) : (twistFree L d k).IsQuasicoherent := isQuasicoherent_biproduct _

variable {L}

/-- The morphism `(L^{⊗ -d})^{⊕ k} ⟶ M` defined by `k` global sections of `M ⊗ L^{⊗ d}`. -/
def twistFreeDesc {M : X.Modules} {d : ℤ} {k : ℕ} (s : Fin k → Γ(L.twist M d, ⊤)) :
    twistFree L d k ⟶ M :=
  biproduct.desc fun j ↦ (L.homToModulesAddEquiv M d).symm (s j)

lemma homToModulesAddEquiv_comp {M N : X.Modules} {d : ℤ} (φ' : L.toModules (-d) ⟶ M)
    (φ : M ⟶ N) :
    L.homToModulesAddEquiv N d (φ' ≫ φ) =
      (L.twistMap d φ).app ⊤ (L.homToModulesAddEquiv M d φ') := by
  rw [Scheme.LineBundle.homToModulesAddEquiv_apply, Scheme.LineBundle.homToModulesAddEquiv_apply,
    Scheme.LineBundle.twistMap_comp, ← Scheme.Modules.Hom.comp_app_apply]
  rfl

lemma twistFreeDesc_comp {M N : X.Modules} {d : ℤ} {k : ℕ} (s : Fin k → Γ(L.twist M d, ⊤))
    (φ : M ⟶ N) :
    twistFreeDesc s ≫ φ = twistFreeDesc (fun j ↦ (L.twistMap d φ).app ⊤ (s j)) := by
  refine biproduct.hom_ext' _ _ fun j ↦ ?_
  rw [twistFreeDesc, twistFreeDesc, biproduct.ι_desc_assoc, biproduct.ι_desc]
  apply (L.homToModulesAddEquiv N d).injective
  rw [homToModulesAddEquiv_comp, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

lemma inv_twistMap_eq_homOfSection {M : X.Modules} {d : ℤ} (φ : L.toModules (-d) ⟶ M) :
    (L.twistNegTwistIso d).inv ≫ L.twistMap d φ =
      homOfSection (L.twist M d) (L.homToModulesAddEquiv M d φ) := by
  rw [← unitHomAddEquiv_symm_apply]
  exact ((unitHomAddEquiv (L.twist M d)).symm_apply_apply _).symm

lemma twistMap_homToModulesAddEquiv_symm {M : X.Modules} {d : ℤ} (t : Γ(L.twist M d, ⊤)) :
    L.twistMap d ((L.homToModulesAddEquiv M d).symm t) =
      (L.twistNegTwistIso d).hom ≫ homOfSection (L.twist M d) t := by
  rw [← AddEquiv.apply_symm_apply (L.homToModulesAddEquiv M d) t, ← inv_twistMap_eq_homOfSection,
    Iso.hom_inv_id_assoc, AddEquiv.symm_apply_apply]

/-- If `k` global sections of `M(d)` generate it (the map `𝒪_X^k ⟶ M(d)` is epi), then
`(L^{⊗ -d})^{⊕ k} ⟶ M` is epi. -/
lemma epi_twistFreeDesc {M : X.Modules} {d : ℤ} {k : ℕ} (s : Fin k → Γ(L.twist M d, ⊤))
    [h : Epi (biproduct.desc fun j ↦ homOfSection (L.twist M d) (s j))] :
    Epi (twistFreeDesc s) := by
  let F := Scheme.LineBundle.twistFunctor X L d
  have e : F.map (twistFreeDesc s) = (F.mapBiproduct _).hom ≫
      biproduct.desc (f := F.obj ∘ fun _ : Fin k ↦ L.toModules (-d))
        (fun j ↦ (L.twistNegTwistIso d).hom ≫ homOfSection (L.twist M d) (s j)) := by
    rw [twistFreeDesc, ← biproduct.mapBiproduct_hom_desc]
    congr 1
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    rw [biproduct.ι_desc]
    refine (twistMap_homToModulesAddEquiv_symm (s j)).trans ?_
    exact (biproduct.ι_desc (f := F.obj ∘ fun _ : Fin k ↦ L.toModules (-d))
      (fun j ↦ (L.twistNegTwistIso d).hom ≫ homOfSection (L.twist M d) (s j)) j).symm
  have : Epi (biproduct.desc (f := F.obj ∘ fun _ : Fin k ↦ L.toModules (-d))
      (fun j ↦ (L.twistNegTwistIso d).hom ≫ homOfSection (L.twist M d) (s j))) :=
    epi_biproduct_desc_iso_comp (fun _ ↦ L.twistNegTwistIso d) _
  have : Epi (F.map (twistFreeDesc s)) := by
    rw [e]; exact @epi_comp _ _ _ _ _ _ inferInstance _ this
  exact F.epi_of_epi_map this

end TwistFree

section CompatibleEpi

open ProjectiveSpace

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}}

/-- Lifting global sections of twists along the transition maps of an adic system, when
`H¹(X, I^{n+1} G_{n+1}(d)) = 0`. -/
lemma AdicSystem.twistMap_map_app_top_surjective {f : X ⟶ Spec A} (G : AdicSystem I f)
    (L : X.LineBundle) (d : ℤ) (n : ℕ) (h : Subsingleton ((L.twist (G.grSucc n) d).H 1)) :
    Function.Surjective ((L.twistMap d (G.map n)).app ⊤) := by
  have hS := L.shortExact_map_twistFunctor d (G.shortExact_grSucc n)
  exact TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
    (Scheme.Modules.shortExact_abShortComplex hS) ⊤ h

/-- Nakayama for adic systems, on sections over an affine open. -/
lemma AdicSystem.app_surjective_of_comp_toZero {f : X ⟶ Spec A} (G : AdicSystem I f)
    {P : X.Modules} [P.IsQuasicoherent] (n : ℕ) (α : P ⟶ G.obj n) [Epi (α ≫ G.toZero n)]
    {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective (α.app U) := by
  let J := idealV f I U 1
  let N : Submodule Γ(X, U) Γ(G.obj n, U) := LinearMap.range (appLinearMap α U)
  have h1 : N ⊔ J • ⊤ = ⊤ := by
    refine top_le_iff.mp fun m _ ↦ ?_
    obtain ⟨e, he⟩ := app_surjective_of_epi (α ≫ G.toZero n) hU ((G.toZero n).app U m)
    have hm : m - α.app U e ∈ (J • ⊤ : Submodule Γ(X, U) Γ(G.obj n, U)) := by
      rw [← G.toZero_app_eq_zero_iff n hU, map_sub, ← he, Scheme.Modules.Hom.comp_app_apply,
        sub_self]
    have : m = α.app U e + (m - α.app U e) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨e, rfl⟩ hm
  have h2 : J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(G.obj n, U)) = ⊥ := by
    refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun c hc m _ ↦ ?_)
    rw [G.smul_eq_zero n hU hc m]
    exact zero_mem _
  have hN := Submodule.eq_top_of_sup_smul_eq_top_of_pow J N h1 (n + 1) h2
  intro m
  have hm : m ∈ N := hN ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := hm
  exact ⟨e, he⟩

/-- **Nakayama for adic systems**: a morphism `α : P ⟶ Gₙ` from a quasi-coherent module whose
composite with `Gₙ ⟶ G₀` is epi is epi. -/
lemma AdicSystem.epi_of_epi_comp_toZero {f : X ⟶ Spec A} (G : AdicSystem I f) {P : X.Modules}
    [P.IsQuasicoherent] (n : ℕ) (α : P ⟶ G.obj n) [Epi (α ≫ G.toZero n)] : Epi α := by
  refine epi_of_surjective_app _ _ (fun V : X.affineOpens ↦ V.1) (iSup_affineOpens_eq_top X)
    (fun V ↦ V.2) fun V ↦ G.app_surjective_of_comp_toZero I n α V.2

variable {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Compatible presentations of an adic system** (EGA III 5.2.x; Hartshorne II.9.6, first step):
for `X` closed in `ℙ(τ; Spec A)`, `A` noetherian, and `(G_n)` an adic system with `G₀` coherent,
there are `d` and compatible epimorphisms `𝒪_X(-d)^k ⟶ G_n`. They are given by global sections of
`G₀(d)` generating it, lifted step by step to `G_n(d)` using `H¹(X, I^{n+1} G_{n+1}(d)) = 0`
(`AdicSystem.exists_subsingleton_H_twist_grSucc`); surjectivity follows by Nakayama. -/
theorem AdicSystem.exists_compatible_epi [IsNoetherianRing A]
    (G : AdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)) [(G.obj 0).IsCoherent] :
    ∃ (d : ℤ) (k : ℕ)
      (α : ∀ n, twistFree ((twistingSheaf τ (Spec A)).pullback κ) d k ⟶ G.obj n),
      (∀ n, α (n + 1) ≫ G.map n = α n) ∧ ∀ n, Epi (α n) := by
  classical
  set L := (twistingSheaf τ (Spec A)).pullback κ
  have : (G.obj 0).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  obtain ⟨d₀, hd₀⟩ := AdicSystem.exists_subsingleton_H_twist_grSucc I κ G
  obtain ⟨n₀, hn₀⟩ := exists_epi_homOfSection_twist κ (G.obj 0)
  let d : ℕ := max n₀ d₀.toNat
  have hd : ((d : ℕ) : ℤ) ≥ d₀ :=
    (Int.self_le_toNat d₀).trans (by exact_mod_cast le_max_right n₀ d₀.toNat)
  obtain ⟨k, t, ht⟩ := hn₀ d (le_max_left _ _)
  have hsurj : ∀ n, Function.Surjective ((L.twistMap d (G.map n)).app ⊤) := fun n ↦
    G.twistMap_map_app_top_surjective I L d n (hd₀ d hd n 0)
  choose lift hlift using hsurj
  let s : ∀ n, Fin k → Γ(L.twist (G.obj n) d, ⊤) := fun n ↦
    Nat.rec (motive := fun n ↦ Fin k → Γ(L.twist (G.obj n) d, ⊤)) t
      (fun n sn j ↦ lift n (sn j)) n
  have hs : ∀ n j, (L.twistMap d (G.map n)).app ⊤ (s (n + 1) j) = s n j :=
    fun n j ↦ hlift n (s n j)
  have hcompat : ∀ n, twistFreeDesc (s (n + 1)) ≫ G.map n = twistFreeDesc (s n) := fun n ↦ by
    rw [twistFreeDesc_comp]
    congr 1
    funext j
    exact hs n j
  refine ⟨d, k, fun n ↦ twistFreeDesc (s n), hcompat, fun n ↦ ?_⟩
  have h0 : Epi (twistFreeDesc (s 0)) := epi_twistFreeDesc (s 0) (h := ht)
  have hcomp : ∀ n, twistFreeDesc (s n) ≫ G.toZero n = twistFreeDesc (s 0) := by
    intro n
    induction n with
    | zero => exact Category.comp_id _
    | succ n ih => rw [AdicSystem.toZero_succ, ← Category.assoc, hcompat, ih]
  have : Epi (twistFreeDesc (s n) ≫ G.toZero n) := by rw [hcomp]; exact h0
  exact G.epi_of_epi_comp_toZero I n _

end CompatibleEpi

section Kernel

variable {A : CommRingCat.{u}} {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec A}

/-- The lifting property of a module `P` projective over `R / K`: every surjection onto `P` from
an `R`-module killed by `K` splits. -/
def LiftingProperty {R : Type u} [CommRing R] (K : Ideal R) (P : Type u) [AddCommGroup P]
    [Module R P] : Prop :=
  ∀ {N : Type u} [AddCommGroup N] [Module R N], (∀ c ∈ K, ∀ x : N, c • x = 0) →
    ∀ φ : N →ₗ[R] P, Function.Surjective φ → ∃ ψ : P →ₗ[R] N, φ ∘ₗ ψ = LinearMap.id

/-- An adic system is *locally free* if over every affine open `U` each `Γ(Gₙ, U)` is projective
as a module over `Γ(X, U) / J^{n+1}`, `J = I Γ(X, U)`: every surjection onto it from a
`Γ(X, U)`-module killed by `J^{n+1}` splits (`LiftingProperty`). This holds for the adic systems of
locally free modules of finite rank on the thickenings `X_n`, e.g. the direct images of the
structure sheaves of finite étale `X_n`-schemes. -/
def AdicSystem.IsLocallyFree (G : AdicSystem I f) : Prop :=
  ∀ (n : ℕ) {U : X.Opens}, IsAffineOpen U →
    LiftingProperty (idealV f I U 1 ^ (n + 1)) Γ(G.obj n, U)

lemma kernel_ι_app_injective {P Q : X.Modules} (φ : P ⟶ Q) [Epi φ] (U : X.Opens) :
    Function.Injective ((kernel.ι φ).app U) :=
  app_injective_of_shortExact (shortExact_kernelSequence φ) U

lemma exists_kernel_ι_app_eq {P Q : X.Modules} (φ : P ⟶ Q) [Epi φ] (U : X.Opens)
    (s : Γ(P, U)) (hs : φ.app U s = 0) : ∃ k, (kernel.ι φ).app U k = s :=
  exists_app_eq_of_shortExact (shortExact_kernelSequence φ) U s hs

/-- A linear map sends `J • ⊤` into `J • ⊤`. -/
lemma mem_smul_top_of_linearMap {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (φ : M →ₗ[R] N) {x : M}
    (hx : x ∈ (J • ⊤ : Submodule R M)) : φ x ∈ (J • ⊤ : Submodule R N) := by
  have : (J • ⊤ : Submodule R M).map φ ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨x, hx, rfl⟩

variable (H G : AdicSystem I f) (φ : ∀ n, H.obj n ⟶ G.obj n)
  (hφ : ∀ n, φ (n + 1) ≫ G.map n = H.map n ≫ φ n) [∀ n, Epi (φ n)]

omit [∀ n, Epi (φ n)] in
@[reassoc]
lemma kernelMap_ι (n : ℕ) :
    kernel.map (φ (n + 1)) (φ n) (H.map n) (G.map n) (hφ n) ≫ kernel.ι (φ n) =
      kernel.ι (φ (n + 1)) ≫ H.map n :=
  kernel.lift_ι _ _ _

include hφ in
lemma kernelMap_app_surjective (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((kernel.map (φ (n + 1)) (φ n) (H.map n) (G.map n) (hφ n)).app U) := by
  intro k
  obtain ⟨t, ht⟩ := H.surjective n hU ((kernel.ι (φ n)).app U k)
  have hg : (G.map n).app U ((φ (n + 1)).app U t) = 0 := by
    rw [← Scheme.Modules.Hom.comp_app_apply, hφ, Scheme.Modules.Hom.comp_app_apply, ht,
      ← Scheme.Modules.Hom.comp_app_apply, kernel.condition]
    rfl
  rw [G.map_app_eq_zero_iff n hU] at hg
  obtain ⟨t', ht', ht'φ⟩ := AdicSystem.mem_map_smul_top _ (appLinearMap (φ (n + 1)) U)
    (app_surjective_of_epi (φ (n + 1)) hU) hg
  obtain ⟨k', hk'⟩ := exists_kernel_ι_app_eq (φ (n + 1)) U (t - t') (by
    rw [map_sub]
    change _ - appLinearMap (φ (n + 1)) U t' = 0
    rw [ht'φ, sub_self])
  refine ⟨k', kernel_ι_app_injective (φ n) U ?_⟩
  rw [← Scheme.Modules.Hom.comp_app_apply, kernelMap_ι H G φ hφ n,
    Scheme.Modules.Hom.comp_app_apply, hk', map_sub, ht, (H.map_app_eq_zero_iff n hU t').mpr ht',
    sub_zero]

include hφ in
lemma kernelMap_app_eq_zero_iff (hG : G.IsLocallyFree) (n : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) (k : Γ(kernel (φ (n + 1)), U)) :
    (kernel.map (φ (n + 1)) (φ n) (H.map n) (G.map n) (hφ n)).app U k = 0 ↔
      k ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(kernel (φ (n + 1)), U)) := by
  let ι₁ := appLinearMap (kernel.ι (φ (n + 1))) U
  have hι₁ : Function.Injective ι₁ := kernel_ι_app_injective (φ (n + 1)) U
  constructor
  · intro h
    have h1 : (H.map n).app U (ι₁ k) = 0 := by
      change (H.map n).app U ((kernel.ι (φ (n + 1))).app U k) = 0
      rw [← Scheme.Modules.Hom.comp_app_apply, ← kernelMap_ι H G φ hφ n,
        Scheme.Modules.Hom.comp_app_apply, h, map_zero]
    rw [H.map_app_eq_zero_iff n hU] at h1
    obtain ⟨ψ, hψ⟩ := hG (n + 1) hU (fun c hc x ↦ H.smul_eq_zero (n + 1) hU hc x)
      (appLinearMap (φ (n + 1)) U) (app_surjective_of_epi (φ (n + 1)) hU)
    let ρ : Γ(H.obj (n + 1), U) →ₗ[Γ(X, U)] Γ(H.obj (n + 1), U) :=
      LinearMap.id - ψ ∘ₗ appLinearMap (φ (n + 1)) U
    have hρ : ∀ x, ρ x ∈ LinearMap.range ι₁ := fun x ↦ by
      obtain ⟨w, hw⟩ := exists_kernel_ι_app_eq (φ (n + 1)) U (ρ x) (by
        change appLinearMap (φ (n + 1)) U (ρ x) = 0
        simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
        rw [← LinearMap.comp_apply (appLinearMap (φ (n + 1)) U) ψ, hψ, LinearMap.id_apply,
          sub_self])
      exact ⟨w, hw⟩
    let lam := AdicSystem.liftLinear ι₁ hι₁ ρ hρ
    have hlam : lam (ι₁ k) = k := by
      apply hι₁
      rw [AdicSystem.liftLinear_spec]
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      have : appLinearMap (φ (n + 1)) U (ι₁ k) = 0 := by
        change (φ (n + 1)).app U ((kernel.ι (φ (n + 1))).app U k) = 0
        rw [← Scheme.Modules.Hom.comp_app_apply, kernel.condition]
        rfl
      rw [this, map_zero, sub_zero]
    rw [← hlam]
    exact mem_smul_top_of_linearMap _ lam h1
  · intro h
    apply kernel_ι_app_injective (φ n) U
    rw [← Scheme.Modules.Hom.comp_app_apply, kernelMap_ι H G φ hφ n,
      Scheme.Modules.Hom.comp_app_apply, map_zero]
    exact (H.map_app_eq_zero_iff n hU _).mpr (mem_smul_top_of_linearMap _ ι₁ h)

/-- **The kernel of an epimorphism of adic systems onto a locally free adic system** is an adic
system: `0 → Kₙ → Hₙ → Gₙ → 0` stays exact modulo `I^{n+1}` since it splits locally. -/
def AdicSystem.kernelSystem (hG : G.IsLocallyFree) : AdicSystem I f where
  obj n := kernel (φ n)
  map n := kernel.map (φ (n + 1)) (φ n) (H.map n) (G.map n) (hφ n)
  isQuasicoherent _ := isQuasicoherent_kernel _
  surjective n _ hU := kernelMap_app_surjective H G φ hφ n hU
  map_app_eq_zero_iff n _ hU k := kernelMap_app_eq_zero_iff H G φ hφ hG n hU k

end Kernel

section Existence

open ProjectiveSpace

variable {X : Scheme.{u}}

/-- Finite biproducts of coherent modules are coherent. -/
lemma isCoherent_biproduct {J : Type} [Finite J] (G : J → X.Modules) [∀ j, (G j).IsCoherent] :
    (⨁ G).IsCoherent := by
  have : ∀ j, (G j).IsQuasicoherent := fun _ ↦ Scheme.Modules.IsCoherent.isQuasicoherent
  have : ∀ j, (G j).IsFiniteType := fun _ ↦ Scheme.Modules.IsCoherent.isFiniteType
  have := Fintype.ofFinite J
  have : (⨁ G).IsQuasicoherent := isQuasicoherent_biproduct _
  exact ⟨inferInstance, isFiniteType_of_finite_sections _ (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦
      finite_sections_biproduct G U.1 fun j ↦ finite_sections_of_isFiniteType (G j) U.2⟩

instance isCoherent_twistFree (L : X.LineBundle) (d : ℤ) (k : ℕ) :
    (twistFree L d k).IsCoherent := by
  have : (L.toModules (-d)).IsCoherent :=
    inferInstanceAs (L.twist (unitModule X) (-d)).IsCoherent
  exact isCoherent_biproduct _

/-- The cokernel of a morphism of coherent modules is coherent. -/
lemma isCoherent_cokernel' {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsCoherent] (b : P ⟶ Q) :
    (cokernel b).IsCoherent := by
  have : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hS := shortExact_kernelSequence (cokernel.π b)
  have : (ShortComplex.kernelSequence (cokernel.π b)).X₁.IsQuasicoherent := isQuasicoherent_image b
  have : (ShortComplex.kernelSequence (cokernel.π b)).X₂.IsCoherent := ‹Q.IsCoherent›
  exact isCoherent_X₃_of_shortExact hS

variable {A : CommRingCat.{u}} (I : Ideal A) (f : X ⟶ Spec A)

/-- A morphism into a module killed by `I^{n+1}` factors through `M / I^{n+1} M`. -/
def descQuotientIdealPow {M N : X.Modules} (n : ℕ) (φ : M ⟶ N)
    (hN : ∀ a ∈ I ^ (n + 1), smulA N f a = 0) : M.quotientIdealPow f I n ⟶ N :=
  cokernel.desc _ φ (Sigma.hom_ext _ _ fun a ↦ by
    rw [comp_zero, Scheme.Modules.idealPowSMul, Sigma.ι_desc_assoc]
    change smulA M f a.1 ≫ φ = 0
    rw [← smulA_naturality, hN a.1 a.2, comp_zero])

@[reassoc (attr := simp)]
lemma toQuotientIdealPow_descQuotientIdealPow {M N : X.Modules} (n : ℕ) (φ : M ⟶ N)
    (hN : ∀ a ∈ I ^ (n + 1), smulA N f a = 0) :
    M.toQuotientIdealPow f I n ≫ descQuotientIdealPow I f n φ hN = φ :=
  cokernel.π_desc _ _ _

variable {I f} in
/-- The `n`-th module of an adic system is killed by `I^{n+1}`. -/
lemma AdicSystem.smulA_eq_zero (G : AdicSystem I f) (n : ℕ) {a : A} (ha : a ∈ I ^ (n + 1)) :
    smulA (G.obj n) f a = 0 := by
  refine hom_ext_of_affine fun U hU s ↦ ?_
  rw [smulA_app, G.smul_eq_zero n hU (AdicSystem.structMapV_mem_pow ha) s]
  rfl

variable {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Grothendieck's existence theorem for locally free adic systems on a projective scheme**
(EGA III 5.1.4 / 5.2.x in the projective case; Hartshorne II.9.6 for locally free systems): let
`A` be a noetherian `I`-adically complete ring, `X` a closed subscheme of `ℙ(τ; Spec A)` and
`(Gₙ)` a locally free adic system on `X` with `G₀` coherent. Then there is a coherent `F` on `X`
with compatible isomorphisms `F / I^{n+1} F ≅ Gₙ`.

Proof: compatible presentations `𝒪(-d')^{k'} ⟶ 𝒪(-d)^k / I^{n+1} ⟶ Gₙ ⟶ 0` (the kernels form an
adic system since `Gₙ` is locally free, `AdicSystem.kernelSystem`), algebraization of the first
map by full faithfulness (`exists_comp_toQuotientIdealPow_eq`), and `F` its cokernel. -/
theorem AdicSystem.exists_iso_quotientIdealPow_of_isLocallyFree [IsNoetherianRing A]
    [IsAdicComplete I A] (G : AdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)) [(G.obj 0).IsCoherent]
    (hG : G.IsLocallyFree) :
    ∃ (F : X.Modules) (_ : F.IsCoherent)
      (e : ∀ n, F.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≅ G.obj n),
      ∀ n, (e (n + 1)).hom ≫ G.map n =
        F.quotientIdealPowMap (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ (e n).hom := by
  classical
  have : IsProper (κ ≫ ℙ(τ; Spec A) ↘ Spec A) := inferInstance
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  -- Step 1: compatible surjections from `E = 𝒪(-d)^k`.
  obtain ⟨d, k, α, hα, hαe⟩ := G.exists_compatible_epi I κ
  let E := twistFree ((twistingSheaf τ (Spec A)).pullback κ) d k
  let H := ofModule I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) E
  let φ : ∀ n, E.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ⟶ G.obj n := fun n ↦
    descQuotientIdealPow I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) n (α n) fun a ha ↦ G.smulA_eq_zero n ha
  have hφα : ∀ n, E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ φ n = α n := fun n ↦
    toQuotientIdealPow_descQuotientIdealPow I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) n (α n) _
  have hφ : ∀ n, φ (n + 1) ≫ G.map n = E.quotientIdealPowMap _ I n ≫ φ n := fun n ↦ by
    rw [← cancel_epi (E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I (n + 1)),
      reassoc_of% (hφα (n + 1)), hα, Scheme.Modules.toQuotientIdealPow_comp_map_assoc, hφα]
  have hφe : ∀ n, Epi (φ n) := fun n ↦ by
    have : Epi (E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ φ n) := by
      rw [hφα]; exact hαe n
    exact epi_of_epi (E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n) (φ n)
  -- Step 2: the kernels form an adic system; present it.
  let K := @AdicSystem.kernelSystem _ _ _ _ H G φ hφ hφe hG
  have hE0 : (E.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I 0).IsCoherent := by
    have : (IPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I E (0 + 1)).IsQuasicoherent :=
      isQuasicoherent_IPow I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) E (0 + 1)
    exact isCoherent_X₃_of_shortExact (shortExact_quotientIdealPow _ I E 0)
  have : (K.obj 0).IsCoherent := by
    have : (ShortComplex.kernelSequence (φ 0)).X₁.IsQuasicoherent := isQuasicoherent_kernel _
    have : (ShortComplex.kernelSequence (φ 0)).X₂.IsCoherent := hE0
    exact isCoherent_X₁_of_shortExact (shortExact_kernelSequence (φ 0))
  obtain ⟨d', k', α', hα', hα'e⟩ := K.exists_compatible_epi I κ
  let E' := twistFree ((twistingSheaf τ (Spec A)).pullback κ) d' k'
  -- Step 3: algebraize `E' ⟶ Kₙ ⟶ E / I^{n+1} E`.
  let β : ∀ n, E' ⟶ E.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n := fun n ↦
    α' n ≫ kernel.ι (φ n)
  have hβ : ∀ n, β (n + 1) ≫ E.quotientIdealPowMap _ I n = β n := fun n ↦ by
    have key : kernel.ι (φ (n + 1)) ≫ E.quotientIdealPowMap (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n =
        K.map n ≫ kernel.ι (φ n) := (kernelMap_ι H G φ hφ n).symm
    calc β (n + 1) ≫ E.quotientIdealPowMap (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n
        = α' (n + 1) ≫ (kernel.ι (φ (n + 1)) ≫ E.quotientIdealPowMap _ I n) :=
          Category.assoc _ _ _
      _ = α' (n + 1) ≫ (K.map n ≫ kernel.ι (φ n)) := congrArg (α' (n + 1) ≫ ·) key
      _ = (α' (n + 1) ≫ K.map n) ≫ kernel.ι (φ n) := (Category.assoc _ _ _).symm
      _ = β n := congrArg (· ≫ kernel.ι (φ n)) (hα' n)
  obtain ⟨b, hb⟩ := exists_comp_toQuotientIdealPow_eq I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) β hβ
  -- Step 4: `F = coker b`.
  let F := cokernel b
  have hF : F.IsCoherent := isCoherent_cokernel' b
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hbα : ∀ n, b ≫ α n = 0 := fun n ↦ by
    rw [← hφα n, reassoc_of% (hb n)]
    exact (Category.assoc _ _ _).trans ((congrArg (α' n ≫ ·) (kernel.condition (φ n))).trans
      comp_zero)
  let ρ : ∀ n, F ⟶ G.obj n := fun n ↦ cokernel.desc b (α n) (hbα n)
  let e : ∀ n, F.quotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ⟶ G.obj n := fun n ↦
    descQuotientIdealPow I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) n (ρ n) fun a ha ↦ G.smulA_eq_zero n ha
  have he : ∀ n, cokernel.π b ≫ F.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ e n = α n :=
    fun n ↦ by
    change cokernel.π b ≫ F.toQuotientIdealPow _ I n ≫ descQuotientIdealPow I _ n (ρ n) _ = α n
    rw [toQuotientIdealPow_descQuotientIdealPow, cokernel.π_desc]
  have heIso : ∀ n, IsIso (e n) := fun n ↦ by
    refine isIso_of_bijective_app_affine _ fun U hU ↦ ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y', rfl⟩ :=
        toQuotientIdealPow_app_surjective I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) n hU (M := F) x
      obtain ⟨y, rfl⟩ := cokernel_π_app_surjective b hU y'
      have h1 : (α n).app U y = 0 := by
        rw [← he n, Scheme.Modules.Hom.comp_app_apply, Scheme.Modules.Hom.comp_app_apply]
        exact hx
      rw [← hφα n, Scheme.Modules.Hom.comp_app_apply] at h1
      obtain ⟨z, hz⟩ := exists_kernel_ι_app_eq (φ n) U _ h1
      obtain ⟨w, rfl⟩ := app_surjective_of_epi (α' n) hU z
      have e1 : (E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n).app U (b.app U w) =
          (β n).app U w := by
        rw [← hb n]; rfl
      have h5 := e1.trans hz
      have h2 : (E.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n).app U
          (y - b.app U w) = 0 := by
        rw [map_sub, h5, sub_self]
      rw [quotientIdealPow_app_eq_zero_iff I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) E n hU] at h2
      have h3 := mem_smul_top_of_linearMap _ (appLinearMap (cokernel.π b) U) h2
      have h4 : (cokernel.π b).app U (b.app U w) = 0 := by
        rw [← Scheme.Modules.Hom.comp_app_apply, cokernel.condition]
        rfl
      change (cokernel.π b).app U (y - b.app U w) ∈ _ at h3
      rw [map_sub, h4, sub_zero] at h3
      exact (quotientIdealPow_app_eq_zero_iff I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) F n hU _).mpr h3
    · intro g
      obtain ⟨y, hy⟩ := app_surjective_of_epi (α n) hU g
      refine ⟨(F.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n).app U
        ((cokernel.π b).app U y), ?_⟩
      rw [← Scheme.Modules.Hom.comp_app_apply, ← Scheme.Modules.Hom.comp_app_apply, he n, hy]
  refine ⟨F, hF, fun n ↦ @asIso _ _ _ _ (e n) (heIso n), fun n ↦ ?_⟩
  change e (n + 1) ≫ G.map n = F.quotientIdealPowMap (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n ≫ e n
  rw [← cancel_epi (cokernel.π b ≫ F.toQuotientIdealPow (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I (n + 1))]
  rw [Category.assoc, reassoc_of% (he (n + 1)), hα, Category.assoc,
    Scheme.Modules.toQuotientIdealPow_comp_map_assoc, he]

end Existence

end AlgebraicGeometry.CohomologyAux
