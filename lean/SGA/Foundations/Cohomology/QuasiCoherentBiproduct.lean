/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentKernel
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Finite biproducts of quasi-coherent modules

`CohomologyAux.biproductSections`: the sections of `⨁ F` are the families of sections of the
`F j`; `CohomologyAux.isQuasicoherent_biproduct`: finite biproducts of quasi-coherent modules are
quasi-coherent (EGA I 1.4.1: sections over basic opens of affines are localizations).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

lemma modules_sum_app_apply {M N : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N))
    (W : X.Opens) (x : Γ(M, W)) : (∑ i ∈ s, φ i).app W x = ∑ i ∈ s, (φ i).app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app, ← ih]
    rfl

variable {J : Type} [Fintype J] (F : J → X.Modules)

/-- The sections of a finite biproduct of `𝒪_X`-modules, componentwise. -/
noncomputable def biproductSections (W : X.Opens) : Γ(⨁ F, W) →+ ∀ j, Γ(F j, W) where
  toFun s j := (biproduct.π F j).app W s
  map_zero' := by ext j; exact map_zero _
  map_add' s t := by ext j; exact map_add _ _ _

lemma biproductSections_apply (W : X.Opens) (s : Γ(⨁ F, W)) (j : J) :
    biproductSections F W s j = (biproduct.π F j).app W s := rfl

lemma biproductSections_bijective (W : X.Opens) : Function.Bijective (biproductSections F W) := by
  classical
  have htot : ∀ s : Γ(⨁ F, W), ∑ j, (biproduct.ι F j).app W ((biproduct.π F j).app W s) = s := by
    intro s
    have h := congrArg (fun φ : ⨁ F ⟶ ⨁ F ↦ φ.app W s) (biproduct.total (f := F))
    simp only at h
    rw [modules_sum_app_apply] at h
    exact h
  refine ⟨fun s t hst ↦ ?_, fun t ↦ ⟨∑ j, (biproduct.ι F j).app W (t j), ?_⟩⟩
  · rw [← htot s, ← htot t]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact congrArg ((biproduct.ι F j).app W) (congrFun hst j)
  · ext k
    rw [biproductSections_apply, map_sum]
    rw [Finset.sum_eq_single k]
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π_self]
      rfl
    · intro j _ hjk
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π_ne _ hjk]
      rfl
    · intro h; exact (h (Finset.mem_univ k)).elim

/-- **Finite biproducts of quasi-coherent modules are quasi-coherent.** -/
theorem isQuasicoherent_biproduct [∀ j, (F j).IsQuasicoherent] : (⨁ F).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule _ (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U c ↦ ?_
  have hW : X.basicOpen c ⊓ U.1 = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  -- the componentwise maps as `Γ(X, U)`-linear maps
  let e (W : X.Opens) : ((⨁ F).presheafInf U.1).obj (op W) →ₗ[Γ(X, U.1)]
      (∀ j, ((F j).presheafInf U.1).obj (op W)) :=
    { toFun := fun s ↦ biproductSections F (W ⊓ U.1) s
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        ext j
        exact Scheme.Modules.Hom.app_smul (biproduct.π F j) _ _ }
  have he (W : X.Opens) : Function.Bijective (e W) := biproductSections_bijective F (W ⊓ U.1)
  let P : (∀ j, ((F j).presheafInf U.1).obj (op ⊤)) →ₗ[Γ(X, U.1)]
      (∀ j, ((F j).presheafInf U.1).obj (op (X.basicOpen c))) :=
    .pi fun j ↦ TopCat.Presheaf.resₗ ((F j).presheafInf U.1) ((F j).presheafInf_map_smul U.1)
      (le_top : X.basicOpen c ≤ ⊤) ∘ₗ .proj j
  have hP : IsLocalizedModule.Away c P := by
    have (j : J) := (F j).isLocalizedModule_presheafInf_top U.2 c hW
    exact IsLocalizedModule.pi _ _
  have hcomm : e (X.basicOpen c) ∘ₗ TopCat.Presheaf.resₗ ((⨁ F).presheafInf U.1)
      ((⨁ F).presheafInf_map_smul U.1) (le_top : X.basicOpen c ≤ ⊤) = P ∘ₗ e ⊤ := by
    ext s j
    exact CohomologyAux.hom_app_presheaf_map (biproduct.π F j) _ s
  refine (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers c)
    (e (X.basicOpen c)) (he _)).mp ?_
  rw [hcomm]
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers c) (e ⊤) (he ⊤)).mpr hP

end AlgebraicGeometry.CohomologyAux
