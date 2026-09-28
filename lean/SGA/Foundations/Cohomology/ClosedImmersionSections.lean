/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.SpecSections
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Sections of inverse images along closed immersions

Let `i : T ⟶ X` be a closed immersion, `M` a quasi-coherent `𝒪_X`-module and `U ⊆ X` an affine
open, with `I(U) = ker (Γ(X, U) → Γ(T, i⁻¹ U))`. Then `Γ(M, U) → Γ(i^* M, i⁻¹ U)` is surjective
with kernel `I(U) Γ(M, U)`, i.e. `Γ(i^* M, i⁻¹ U) = Γ(M, U) / I(U) Γ(M, U)` (EGA I 4.1.2).

* `Scheme.Modules.surjective_pullbackApp_SpecMap`, `mem_smul_top_of_pullbackApp_SpecMap_eq_zero`:
  the affine case `Spec C ⟶ Spec R`, from `C ⊗_R N = N / I N`.
* `Scheme.Modules.fromSpecSectionsEquiv`: `Γ(M, U) ≅ Γ(M|_{Spec Γ(X, U)}, ⊤)`, `Γ(X, U)`-linearly.
* `Scheme.Modules.surjective_pullbackApp_of_isClosedImmersion`,
  `Scheme.Modules.mem_smul_top_of_pullbackApp_eq_zero`,
  `Scheme.Modules.pullbackApp_eq_zero_of_mem_smul_top`: the general case.
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.CohomologyAux

/-- For a surjective ring map `R → C` with kernel `I`, the kernel of `N → C ⊗_R N`, `n ↦ 1 ⊗ n`,
is `I N`. -/
lemma mem_smul_top_of_one_tmul_eq_zero {R C N : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup N] [Module R N] (hα : Function.Surjective (algebraMap R C)) (n : N)
    (h : (1 : C) ⊗ₜ[R] n = 0) :
    n ∈ (RingHom.ker (algebraMap R C)) • (⊤ : Submodule R N) := by
  let I := RingHom.ker (algebraMap R C)
  let e : C ≃ₗ[R] R ⧸ I :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R C) hα).symm.toLinearEquiv
  have h2 := congrArg (fun t ↦ quotTensorEquivQuotSMul N I
    (TensorProduct.congr e (LinearEquiv.refl R N) t)) h
  simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, map_zero] at h2
  have he : e 1 = Ideal.Quotient.mk I 1 := by
    change (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R C) hα).symm 1 = _
    rw [map_one]
    rfl
  rw [he, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- For a surjective ring map `R → C`, every element of `C ⊗_R N` is of the form `1 ⊗ n`. -/
lemma exists_one_tmul_eq {R C N : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup N] [Module R N] (hα : Function.Surjective (algebraMap R C)) (t : C ⊗[R] N) :
    ∃ n : N, (1 : C) ⊗ₜ[R] n = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c n =>
    obtain ⟨r, rfl⟩ := hα c
    refine ⟨r • n, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.Scheme.Modules

open ModuleCat ChangeOfRings

variable {R C : CommRingCat.{u}} (α : R ⟶ C) (P : (Spec R).Modules)

lemma surjective_oneTmul (hα : Function.Surjective α) :
    Function.Surjective (oneTmul P.ΓSpec α) := by
  let _ := α.hom.toAlgebra
  intro t
  exact CohomologyAux.exists_one_tmul_eq (N := P.ΓSpec) hα t

lemma mem_smul_top_of_oneTmul_eq_zero (hα : Function.Surjective α) (m : P.ΓSpec)
    (h : oneTmul P.ΓSpec α m = 0) :
    m ∈ (RingHom.ker α.hom) • (⊤ : Submodule R P.ΓSpec) := by
  let _ := α.hom.toAlgebra
  exact CohomologyAux.mem_smul_top_of_one_tmul_eq_zero (N := P.ΓSpec) hα m h

/-- Along `Spec C ⟶ Spec R` for a surjection `R → C`, the inverse image map on global sections of
a quasi-coherent module is surjective. -/
lemma surjective_pullbackApp_SpecMap [P.IsQuasicoherent] (hα : Function.Surjective α) :
    Function.Surjective (pullbackApp (Spec.map α) P ⊤) := by
  intro y
  obtain ⟨m, hm⟩ := surjective_oneTmul α P hα (pullbackSpecMapΓAddEquiv α P y)
  exact ⟨m, (pullbackSpecMapΓAddEquiv α P).injective
    ((pullbackSpecMapΓAddEquiv_pullbackApp α P m).trans hm)⟩

/-- Along `Spec C ⟶ Spec R` for a surjection `R → C` with kernel `I`, the kernel of the inverse
image map on global sections of a quasi-coherent module `P` is `I Γ(P)`. -/
lemma mem_smul_top_of_pullbackApp_SpecMap_eq_zero [P.IsQuasicoherent]
    (hα : Function.Surjective α) (m : Γ(P, ⊤)) (h : pullbackApp (Spec.map α) P ⊤ m = 0) :
    m ∈ (RingHom.ker α.hom) • (⊤ : Submodule R Γ(P, ⊤)) := by
  have h' : oneTmul P.ΓSpec α m = 0 :=
    (pullbackSpecMapΓAddEquiv_pullbackApp α P m).symm.trans (by erw [h]; exact map_zero _)
  exact mem_smul_top_of_oneTmul_eq_zero α P hα m h'

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {T X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)

lemma top_le_fromSpec_preimage : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge

/-- The inverse image of sections along `Spec Γ(X, U) ⟶ X` for `U` affine is bijective onto global
sections. -/
lemma bijective_pullbackAppTop_fromSpec :
    Function.Bijective (pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU)) := by
  have hb := pullbackApp_bijective_of_isOpenImmersion hU.fromSpec M U hU.opensRange_fromSpec.ge
  have hr := ((pullback hU.fromSpec).obj M).presheaf.map_bijective_of_eq
    (homOfLE (top_le_fromSpec_preimage hU)) hU.fromSpec_preimage_self.symm
  have e : ⇑(pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU)) =
      ⇑(((pullback hU.fromSpec).obj M).presheaf.map
        (homOfLE (top_le_fromSpec_preimage hU)).op) ∘ ⇑(pullbackApp hU.fromSpec M U) := by
    ext x
    exact ConcreteCategory.comp_apply _ _ x
  rw [e]
  exact hr.comp hb

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of sections along `Spec Γ(X, U) ⟶ X` is `Γ(X, U)`-linear. -/
lemma pullbackAppTop_fromSpec_smul (r : Γ(X, U)) (s : Γ(M, U)) :
    pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU) (r • s) =
      r • pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU) s := by
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [pullbackApp_smul, Scheme.Modules.map_smul, smul_Spec_def]
  congr 1
  rw [hU.fromSpec_app_self, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Category.assoc, ← Functor.map_comp, ← op_comp]
  have h₁ : (⊤ : (Spec Γ(X, U)).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
  rw [h₁, op_id, CategoryTheory.Functor.map_id]
  have h₂ : homOfLE (top_le_fromSpec_preimage hU) ≫ eqToHom hU.fromSpec_preimage_self = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h₂, op_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The inverse image of sections along `Spec Γ(X, U) ⟶ X` as a `Γ(X, U)`-linear equivalence. -/
noncomputable def fromSpecSectionsEquiv :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ((pullback hU.fromSpec).obj M, ⊤) :=
  LinearEquiv.ofBijective
    { toFun := pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU)
      map_add' := map_add _
      map_smul' := pullbackAppTop_fromSpec_smul M hU }
    (bijective_pullbackAppTop_fromSpec M hU)

lemma fromSpecSectionsEquiv_apply (s : Γ(M, U)) :
    fromSpecSectionsEquiv M hU s = pullbackAppTop hU.fromSpec M U (top_le_fromSpec_preimage hU) s :=
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

section General

variable {T X : Scheme.{u}} (g : T ⟶ X) (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
  (hW : IsAffineOpen (g ⁻¹ᵁ U))

/-- The comparison map `Γ(g^* M, g⁻¹ U) → Γ((Spec γ)^* (M|_U), ⊤)` for affine opens `U` and
`g⁻¹ U`, where `γ = g.app U : Γ(X, U) → Γ(T, g⁻¹ U)`. It is bijective
(`pullbackCompare_bijective`). -/
noncomputable def pullbackCompare :
    Γ((pullback g).obj M, g ⁻¹ᵁ U) →+
      Γ((pullback (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl))).obj
        ((pullback hU.fromSpec).obj M), ⊤) :=
  ((((pullbackComp (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) hU.fromSpec).inv.app M).app ⊤).hom.comp
    ((((pullbackCongr
      (IsAffineOpen.SpecMap_appLE_fromSpec g hU hW le_rfl).symm).hom.app M).app
        ⊤).hom.comp
    ((((pullbackComp hW.fromSpec g).hom.app M).app ⊤).hom.comp
      (pullbackAppTop hW.fromSpec ((pullback g).obj M) (g ⁻¹ᵁ U)
        (top_le_fromSpec_preimage hW)).hom)))

lemma pullbackCompare_bijective : Function.Bijective (pullbackCompare g M hU hW) := by
  have h1 := bijective_pullbackAppTop_fromSpec ((pullback g).obj M) hW
  have h2 := ConcreteCategory.bijective_of_isIso
    (((pullbackComp hW.fromSpec g).hom.app M).app ⊤)
  have h3 := ConcreteCategory.bijective_of_isIso
    (((pullbackCongr (IsAffineOpen.SpecMap_appLE_fromSpec g hU hW
      le_rfl).symm).hom.app M).app ⊤)
  have h4 := ConcreteCategory.bijective_of_isIso
    (((pullbackComp (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) hU.fromSpec).inv.app M).app ⊤)
  exact h4.comp (h3.comp (h2.comp h1))

lemma pullbackCompare_pullbackApp (s : Γ(M, U)) :
    pullbackCompare g M hU hW (pullbackApp g M U s) =
      pullbackApp (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) ((pullback hU.fromSpec).obj M) ⊤
        (fromSpecSectionsEquiv M hU s) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec g hU hW le_rfl
  have hq : ⊤ ≤ (hW.fromSpec ≫ g) ⁻¹ᵁ U := top_le_fromSpec_preimage hW
  have hq' : ⊤ ≤ (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [e]; exact hq
  have s1 := pullbackAppTop_comp hW.fromSpec g M U hq s
  have s2 := pullbackAppTop_congr e.symm M U hq hq' s
  have s3 := pullbackAppTop_comp' (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) hU.fromSpec M U
    (top_le_fromSpec_preimage hU) hq' s
  change (((pullbackComp (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) hU.fromSpec).inv.app M).app ⊤)
    ((((pullbackCongr e.symm).hom.app M).app ⊤)
      ((((pullbackComp hW.fromSpec g).hom.app M).app ⊤)
        (pullbackAppTop hW.fromSpec ((pullback g).obj M) (g ⁻¹ᵁ U) hq
          (pullbackApp g M U s)))) = _
  rw [← s1, s2, s3]
  exact natIso_inv_app_hom_app (pullbackComp _ _) M ⊤ _

/-- The comparison map is `Γ(T, g⁻¹ U)`-linear. -/
lemma pullbackCompare_smul (c : Γ(T, g ⁻¹ᵁ U)) (z : Γ((pullback g).obj M, g ⁻¹ᵁ U)) :
    pullbackCompare g M hU hW (c • z) = c • pullbackCompare g M hU hW z := by
  change (((pullbackComp (Spec.map (g.appLE U (g ⁻¹ᵁ U) le_rfl)) hU.fromSpec).inv.app M).app ⊤)
    ((((pullbackCongr (IsAffineOpen.SpecMap_appLE_fromSpec g hU hW
      le_rfl).symm).hom.app M).app ⊤)
      ((((pullbackComp hW.fromSpec g).hom.app M).app ⊤)
        (pullbackAppTop hW.fromSpec ((pullback g).obj M) (g ⁻¹ᵁ U)
          (top_le_fromSpec_preimage hW) (c • z)))) = _
  rw [pullbackAppTop_fromSpec_smul, Hom.app_smul_Spec, Hom.app_smul_Spec, Hom.app_smul_Spec]
  rfl

end General

variable {T X : Scheme.{u}} (i : T ⟶ X) [IsClosedImmersion i] (M : X.Modules)
  {U : X.Opens} (hU : IsAffineOpen U)

/-- The comparison map `Γ(i^* M, i⁻¹ U) → Γ((Spec α)^* (M|_U), ⊤)` for a closed immersion `i` and an
affine open `U`, where `α = i.app U : Γ(X, U) → Γ(T, i⁻¹ U)`. -/
noncomputable abbrev closedImmersionCompare :
    Γ((pullback i).obj M, i ⁻¹ᵁ U) →+
      Γ((pullback (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl))).obj
        ((pullback hU.fromSpec).obj M), ⊤) :=
  pullbackCompare i M hU (hU.preimage i)

lemma closedImmersionCompare_injective : Function.Injective (closedImmersionCompare i M hU) :=
  (pullbackCompare_bijective i M hU (hU.preimage i)).1

lemma closedImmersionCompare_pullbackApp (s : Γ(M, U)) :
    closedImmersionCompare i M hU (pullbackApp i M U s) =
      pullbackApp (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl)) ((pullback hU.fromSpec).obj M) ⊤
        (fromSpecSectionsEquiv M hU s) :=
  pullbackCompare_pullbackApp i M hU (hU.preimage i) s

include hU in
/-- **Sections of `i^* M` for a closed immersion `i`** (EGA I 4.1.2, surjectivity): for `U` affine
and `M` quasi-coherent, `Γ(M, U) → Γ(i^* M, i⁻¹ U)` is surjective. -/
theorem surjective_pullbackApp_of_isClosedImmersion [M.IsQuasicoherent] :
    Function.Surjective (pullbackApp i M U) := by
  intro y
  have hα : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hU
  obtain ⟨t, ht⟩ := surjective_pullbackApp_SpecMap (i.appLE U (i ⁻¹ᵁ U) le_rfl)
    ((pullback hU.fromSpec).obj M) hα (closedImmersionCompare i M hU y)
  obtain ⟨s, rfl⟩ := (fromSpecSectionsEquiv M hU).surjective t
  refine ⟨s, closedImmersionCompare_injective i M hU ?_⟩
  rw [closedImmersionCompare_pullbackApp, ht]

include hU in
/-- **Sections of `i^* M` for a closed immersion `i`** (EGA I 4.1.2, kernel): for `U` affine and
`M` quasi-coherent, the kernel of `Γ(M, U) → Γ(i^* M, i⁻¹ U)` is `I(U) Γ(M, U)`, where
`I(U) = ker (Γ(X, U) → Γ(T, i⁻¹ U))`. -/
theorem mem_smul_top_of_pullbackApp_eq_zero [M.IsQuasicoherent] (s : Γ(M, U))
    (hs : pullbackApp i M U s = 0) :
    s ∈ (RingHom.ker (i.app U).hom) • (⊤ : Submodule Γ(X, U) Γ(M, U)) := by
  have hα : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hU
  have h0 : pullbackApp (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl)) ((pullback hU.fromSpec).obj M) ⊤
      (fromSpecSectionsEquiv M hU s) = 0 := by
    rw [← closedImmersionCompare_pullbackApp, hs]
    exact map_zero _
  have h1 := mem_smul_top_of_pullbackApp_SpecMap_eq_zero _ _ hα _ h0
  rw [← Scheme.Hom.app_eq_appLE] at h1
  have h2 : (RingHom.ker (i.app U).hom • (⊤ : Submodule Γ(X, U) Γ(M, U))).map
      (fromSpecSectionsEquiv M hU).toLinearMap =
      RingHom.ker (i.app U).hom • (⊤ : Submodule Γ(X, U) Γ((pullback hU.fromSpec).obj M, ⊤)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← h2] at h1
  obtain ⟨s', hs', hss'⟩ := h1
  rwa [(fromSpecSectionsEquiv M hU).injective hss'] at hs'

omit [IsClosedImmersion i] in
/-- The converse inclusion: `I(U) Γ(M, U)` is killed by `Γ(M, U) → Γ(i^* M, i⁻¹ U)`. -/
lemma pullbackApp_eq_zero_of_mem_smul_top (s : Γ(M, U))
    (hs : s ∈ (RingHom.ker (i.app U).hom) • (⊤ : Submodule Γ(X, U) Γ(M, U))) :
    pullbackApp i M U s = 0 := by
  refine Submodule.smul_induction_on hs (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [pullbackApp_smul, RingHom.mem_ker.mp hr, zero_smul]
  · rw [map_add, hx, hy, add_zero]

end AlgebraicGeometry.Scheme.Modules
