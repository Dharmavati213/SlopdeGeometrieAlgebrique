/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentBiproduct
import SGA.Foundations.Cohomology.QuasiCoherentAbelian
import SGA.Foundations.QuasiCoherent.Sections
import SGA.Foundations.Cohomology.Statements

/-!
# The submodules `Iⁿ M`

For `f : X ⟶ Spec A` with `A` noetherian, an ideal `I ⊆ A` and an `𝒪_X`-module `M`:

* `CohomologyAux.IPow f I M n = Iⁿ M`, the image of `⊕_j M → M`, `(m_j) ↦ Σ gⱼ mⱼ` for chosen
  generators `gⱼ` of `Iⁿ`, with the inclusions `ιPow`, `inclPow : Iᵐ M ⟶ Iⁿ M` (`n ≤ m`) and the
  multiplications `multPow : Iⁿ M ⟶ Iⁿ⁺ᵉ M` by `a ∈ Iᵉ`;
* `CohomologyAux.mem_range_ιPow_app`: for `M` quasi-coherent and `V` affine,
  `Γ(Iⁿ M, V) = Iⁿ Γ(M, V)`;
* `CohomologyAux.shortExact_quotientIdealPow`: `0 → Iⁿ⁺¹ M → M → M / Iⁿ⁺¹ M → 0`, for the
  quotient `Scheme.Modules.quotientIdealPow` of `Statements`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) (I : Ideal A)

instance faithful_toAbSheafFunctor (X : Scheme.{u}) :
    (Scheme.Modules.toAbSheafFunctor X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance additive_toAbSheafFunctor (X : Scheme.{u}) :
    (Scheme.Modules.toAbSheafFunctor X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

section Smul

variable {f} (M : X.Modules)

/-- Multiplication by `a ∈ A` on an `𝒪_X`-module, for `X` over `Spec A`. -/
noncomputable abbrev smulA (f : X ⟶ Spec A) (a : A) : M ⟶ M :=
  M.smulEnd (f.specStructureRingHom a)

lemma smulA_toAbSheaf (a : A) :
    Scheme.Modules.Hom.toAbSheaf (smulA M f a) = M.smulHom (f.specStructureRingHom a) := rfl

lemma smulA_mul (a b : A) : smulA M f (a * b) = smulA M f b ≫ smulA M f a := by
  apply (Scheme.Modules.toAbSheafFunctor X).map_injective
  change M.smulHom _ = M.smulHom _ ≫ M.smulHom _
  rw [map_mul, Scheme.Modules.smulHom_mul]

lemma smulA_mul' (a b : A) : smulA M f (a * b) = smulA M f a ≫ smulA M f b := by
  rw [mul_comm, smulA_mul]

lemma smulA_add (a b : A) : smulA M f (a + b) = smulA M f a + smulA M f b := by
  apply (Scheme.Modules.toAbSheafFunctor X).map_injective
  change M.smulHom _ = (Scheme.Modules.toAbSheafFunctor X).map _
  rw [Functor.map_add]
  change _ = M.smulHom _ + M.smulHom _
  rw [map_add, Scheme.Modules.smulHom_add]

lemma smulA_sum {ι : Type*} (s : Finset ι) (a : ι → A) :
    smulA M f (∑ i ∈ s, a i) = ∑ i ∈ s, smulA M f (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply (Scheme.Modules.toAbSheafFunctor X).map_injective
    rw [Finset.sum_empty, Finset.sum_empty, Functor.map_zero]
    change M.smulHom _ = 0
    rw [map_zero, Scheme.Modules.smulHom_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, smulA_add, ih]

@[reassoc]
lemma smulA_naturality {M N : X.Modules} (φ : M ⟶ N) (a : A) :
    φ ≫ smulA N f a = smulA M f a ≫ φ := by
  apply (Scheme.Modules.toAbSheafFunctor X).map_injective
  simp only [Functor.map_comp]
  exact Scheme.Modules.Hom.toAbSheaf_smulHom φ _

/-- The ring map `A → Γ(X, V)`. -/
noncomputable abbrev structMapV (f : X ⟶ Spec A) (V : X.Opens) : A →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ V le_top).hom

lemma smulA_app (a : A) (V : X.Opens) (s : Γ(M, V)) :
    (smulA M f a).app V s = structMapV f V a • s := by
  change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (f.specStructureRingHom a) • s = _
  congr 1

end Smul

section Generators

variable [IsNoetherianRing A]

/-- The number of chosen generators of `Iⁿ`. -/
noncomputable def numGens (n : ℕ) : ℕ :=
  (Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (I ^ n))).choose

/-- Chosen generators of `Iⁿ`. -/
noncomputable def gens (n : ℕ) : Fin (numGens I n) → A :=
  (Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (I ^ n))).choose_spec.choose

lemma span_gens (n : ℕ) : Ideal.span (Set.range (gens I n)) = I ^ n :=
  (Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (I ^ n))).choose_spec.choose_spec

lemma gens_mem (n : ℕ) (j : Fin (numGens I n)) : gens I n j ∈ I ^ n := by
  rw [← span_gens I n]
  exact Ideal.subset_span ⟨j, rfl⟩

end Generators

section Powers

variable [IsNoetherianRing A] (M : X.Modules)

/-- The morphism `⊕_j M → M`, `(m_j) ↦ Σ gⱼ mⱼ`, for generators `gⱼ` of `Iⁿ`. -/
noncomputable def powMap (n : ℕ) : (⨁ fun _ : Fin (numGens I n) ↦ M) ⟶ M :=
  biproduct.desc fun j ↦ smulA M f (gens I n j)

lemma ι_powMap (n : ℕ) (j : Fin (numGens I n)) :
    biproduct.ι (fun _ : Fin (numGens I n) ↦ M) j ≫ powMap f I M n = smulA M f (gens I n j) :=
  biproduct.ι_desc _ _

/-- Multiplication by an element of `Iⁿ` vanishes modulo `Iⁿ M`. -/
@[reassoc]
lemma smulA_comp_cokernel_π {n : ℕ} {b : A} (hb : b ∈ I ^ n) :
    smulA M f b ≫ cokernel.π (powMap f I M n) = 0 := by
  rw [← span_gens I n] at hb
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hb
  rw [smulA_sum, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [smul_eq_mul, smulA_mul', Category.assoc, ← ι_powMap f I M n j, Category.assoc,
    cokernel.condition, comp_zero, comp_zero]

/-- The subsheaf `Iⁿ M ⊆ M` (the image of `⊕_j M → M`). -/
noncomputable abbrev IPow (n : ℕ) : X.Modules := Abelian.image (powMap f I M n)

/-- The inclusion `Iⁿ M ⟶ M`. -/
noncomputable abbrev ιPow (n : ℕ) : IPow f I M n ⟶ M := Abelian.image.ι (powMap f I M n)

lemma powMap_comp_cokernel_π_of_le {m n : ℕ} (h : n ≤ m) :
    powMap f I M m ≫ cokernel.π (powMap f I M n) = 0 :=
  biproduct.hom_ext' _ _ fun j ↦ by
    rw [← Category.assoc, ι_powMap, comp_zero]
    exact smulA_comp_cokernel_π f I M (Ideal.pow_le_pow_right h (gens_mem I m j))

/-- The inclusion `Iᵐ M ⊆ Iⁿ M` for `n ≤ m`. -/
noncomputable def inclPow {m n : ℕ} (h : n ≤ m) : IPow f I M m ⟶ IPow f I M n :=
  kernel.lift _ (ιPow f I M m) (by
    rw [← cancel_epi (Abelian.factorThruImage (powMap f I M m)), comp_zero, ← Category.assoc,
      Abelian.image.fac]
    exact powMap_comp_cokernel_π_of_le f I M h)

@[reassoc (attr := simp)]
lemma inclPow_ιPow {m n : ℕ} (h : n ≤ m) : inclPow f I M h ≫ ιPow f I M n = ιPow f I M m :=
  kernel.lift_ι _ _ _

/-- Multiplication by `a ∈ Iᵉ`, as a morphism `Iⁿ M ⟶ Iⁿ⁺ᵉ M`. -/
noncomputable def multPow {n e : ℕ} {a : A} (ha : a ∈ I ^ e) :
    IPow f I M n ⟶ IPow f I M (n + e) :=
  kernel.lift _ (ιPow f I M n ≫ smulA M f a) (by
    rw [← cancel_epi (Abelian.factorThruImage (powMap f I M n)), comp_zero, ← Category.assoc,
      ← Category.assoc, Abelian.image.fac]
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    rw [← Category.assoc, ← Category.assoc, ι_powMap, comp_zero, ← smulA_mul]
    refine smulA_comp_cokernel_π f I M ?_
    rw [pow_add, mul_comm]
    exact Ideal.mul_mem_mul ha (gens_mem I n j))

@[reassoc (attr := simp)]
lemma multPow_ιPow {n e : ℕ} {a : A} (ha : a ∈ I ^ e) :
    multPow f I M ha ≫ ιPow f I M (n + e) = ιPow f I M n ≫ smulA M f a :=
  kernel.lift_ι _ _ _

instance (n : ℕ) : Mono (ιPow f I M n) := inferInstance

end Powers

section Sections

/-- On an affine open, the sections of a quasi-coherent module surject onto those of its image
under a morphism to a quasi-coherent module. -/
lemma surjective_factorThruImage_app {E F : X.Modules} [E.IsQuasicoherent] [F.IsQuasicoherent]
    (φ : E ⟶ F) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective ((Abelian.factorThruImage φ).app V) := by
  have hS := shortExact_kernelSequence (Abelian.factorThruImage φ)
  have : (Abelian.image φ).IsQuasicoherent := isQuasicoherent_image φ
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsQuasicoherent :=
    ‹E.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₃.IsQuasicoherent :=
    ‹(Abelian.image φ).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS
  exact TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
    (Scheme.Modules.shortExact_abShortComplex hS) V
    ((ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.H'_subsingleton_of_isAffineOpen
      hV 0)

variable [IsNoetherianRing A] (M : X.Modules)

/-- The ideal `Iⁿ Γ(X, V)` of `Γ(X, V)`. -/
noncomputable abbrev idealV (V : X.Opens) (n : ℕ) : Ideal Γ(X, V) := (I ^ n).map (structMapV f V)

lemma idealV_eq_span (V : X.Opens) (n : ℕ) :
    idealV f I V n = Ideal.span (Set.range (structMapV f V ∘ gens I n)) := by
  rw [idealV, ← span_gens I n, Ideal.map_span, Set.range_comp]

lemma powMap_app (n : ℕ) (V : X.Opens) (u : Γ(⨁ fun _ : Fin (numGens I n) ↦ M, V)) :
    (powMap f I M n).app V u = ∑ j, structMapV f V (gens I n j) •
      (biproduct.π (fun _ : Fin (numGens I n) ↦ M) j).app V u := by
  have h : powMap f I M n = ∑ j, biproduct.π (fun _ : Fin (numGens I n) ↦ M) j ≫
      smulA M f (gens I n j) := by
    conv_lhs => rw [← Category.id_comp (powMap f I M n), ← biproduct.total, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Category.assoc, ι_powMap]
  rw [h, modules_sum_app_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulA_app]

/-- **Sections of `Iⁿ M` over an affine open** are `Iⁿ Γ(M, V)`. -/
lemma mem_range_ιPow_app [M.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (s : Γ(M, V)) : s ∈ Set.range ((ιPow f I M n).app V) ↔
      s ∈ idealV f I V n • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  have : (⨁ fun _ : Fin (numGens I n) ↦ M).IsQuasicoherent := isQuasicoherent_biproduct _
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := surjective_factorThruImage_app (powMap f I M n) hV t
    rw [← Scheme.Modules.Hom.comp_app_apply, Abelian.image.fac, powMap_app]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact Ideal.mem_map_of_mem _ (gens_mem I n j)
  · intro hs
    let Rng : AddSubgroup Γ(M, V) := ((ιPow f I M n).app V).hom.range
    change s ∈ Rng
    refine Submodule.smul_induction_on hs (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ Rng.add_mem hx hy)
    rw [idealV_eq_span] at hr
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, V)).mp hr
    rw [Finset.sum_smul]
    refine Rng.sum_mem fun j _ ↦ ?_
    refine ⟨(Abelian.factorThruImage (powMap f I M n)).app V
      ((biproduct.ι (fun _ : Fin (numGens I n) ↦ M) j).app V (c j • m)), ?_⟩
    change ((Abelian.factorThruImage (powMap f I M n) ≫ ιPow f I M n).app V
      ((biproduct.ι (fun _ : Fin (numGens I n) ↦ M) j).app V (c j • m))) = _
    rw [Abelian.image.fac, ← Scheme.Modules.Hom.comp_app_apply, ι_powMap, smulA_app, smul_eq_mul,
      mul_comm, mul_smul]
    rfl

end Sections

section Quotient

variable [IsNoetherianRing A] (M : X.Modules)

/-- `M / Iⁿ⁺¹ M` of `Statements` is the cokernel of `⊕_j M → M`. -/
noncomputable def cokernelPowMapIso (n : ℕ) :
    cokernel (powMap f I M (n + 1)) ≅ M.quotientIdealPow f I n where
  hom := cokernel.desc _ (M.toQuotientIdealPow f I n) (biproduct.hom_ext' _ _ fun j ↦ by
    rw [← Category.assoc, ι_powMap, comp_zero]
    exact M.smulEnd_toQuotientIdealPow f I _ (gens_mem I (n + 1) j))
  inv := cokernel.desc _ (cokernel.π (powMap f I M (n + 1))) (Sigma.hom_ext _ _ fun a ↦ by
    rw [← Category.assoc, Scheme.Modules.idealPowSMul, Sigma.ι_desc, comp_zero]
    exact smulA_comp_cokernel_π f I M a.2)
  hom_inv_id := by rw [← cancel_epi (cokernel.π _)]; simp
  inv_hom_id := by rw [← cancel_epi (cokernel.π _)]; simp

@[reassoc (attr := simp)]
lemma π_cokernelPowMapIso_hom (n : ℕ) :
    cokernel.π (powMap f I M (n + 1)) ≫ (cokernelPowMapIso f I M n).hom =
      M.toQuotientIdealPow f I n :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma ιPow_toQuotientIdealPow (n : ℕ) :
    ιPow f I M (n + 1) ≫ M.toQuotientIdealPow f I n = 0 := by
  rw [← π_cokernelPowMapIso_hom, ← Category.assoc, kernel.condition, zero_comp]

/-- `0 → Iⁿ⁺¹ M → M → M / Iⁿ⁺¹ M → 0`. -/
lemma shortExact_quotientIdealPow (n : ℕ) :
    (ShortComplex.mk (ιPow f I M (n + 1)) (M.toQuotientIdealPow f I n)
      (ιPow_toQuotientIdealPow f I M n)).ShortExact := by
  let S₀ := ShortComplex.mk (kernel.ι (cokernel.π (powMap f I M (n + 1))))
    (cokernel.π (powMap f I M (n + 1))) (kernel.condition _)
  have h₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := inferInstanceAs (Mono (kernel.ι _))
      epi_g := inferInstanceAs (Epi (cokernel.π _)) }
  exact ShortComplex.shortExact_of_iso (S₁ := S₀) (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (cokernelPowMapIso f I M n) (by simp [S₀]) (by simp [S₀])) h₀

end Quotient

end AlgebraicGeometry.CohomologyAux
