/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ReesSheaf

/-!
# The graded pieces of the Rees module

Let `f : X ⟶ Spec A` with `A` noetherian, `I ⊆ A` an ideal, `M` a quasi-coherent `𝒪_X`-module
and `q_B : X_B ⟶ X` the base change to the Rees algebra `B = ⊕ Iⁿ tⁿ`. On `X`, the direct image
`q_{B*}(⊕ Iᵐ M tᵐ)` (`CohomologyAux.reesPush`) has, over every affine open `V`, sections
`⊕ₘ Iᵐ Γ(M, V) tᵐ` (`reesSecEquiv`). We construct morphisms of abelian sheaves

* `reesIota n : Iⁿ M ⟶ q_{B*}(⊕ Iᵐ M tᵐ)`, `x ↦ x tⁿ`, and
* `reesPi n : q_{B*}(⊕ Iᵐ M tᵐ) ⟶ Iⁿ M`, the coefficient of `tⁿ`,

with `reesIota n ≫ reesPi n = 𝟙` and `reesIota j ≫ reesPi p = 0` for `j ≠ p` (EGA III 3.3.1
decomposes the Rees module as the direct sum of the `Iⁿ M`; we only need these projections).
They are defined on affine opens and extended by `CohomologyAux.affineHom`, which builds a morphism
of abelian sheaves from compatible additive maps on the affine opens.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Polynomial

namespace AlgebraicGeometry.CohomologyAux

/-- Monomorphisms of `𝒪_X`-modules are injective on sections. -/
lemma app_injective_of_mono' {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (V : X.Opens) : Function.Injective (φ.app V) := by
  have : Mono (Scheme.Modules.Hom.toAbSheaf φ) :=
    (Scheme.Modules.toAbSheafFunctor X).map_mono φ
  exact CategoryTheory.Sheaf.app_injective_of_mono (Scheme.Modules.Hom.toAbSheaf φ) V

section BasisHom

variable {X : Scheme.{u}}

/-- A morphism of abelian sheaves given on the affine opens, compatibly with restrictions. -/
noncomputable def affineHom {F G : X.Modules}
    (φ : ∀ V : X.Opens, IsAffineOpen V → (Γ(F, V) →+ Γ(G, V)))
    (hφ : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
      (s : Γ(F, V)), φ V' hV' (F.presheaf.map (homOfLE h).op s) =
        G.presheaf.map (homOfLE h).op (φ V hV s)) :
    F.toAbSheaf ⟶ G.toAbSheaf :=
  ObjectProperty.homMk <| TopCat.Sheaf.restrictHomEquivHom (B := fun U : X.affineOpens ↦ U.1)
    F.toAbSheaf.obj G.toAbSheaf (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
    { app V := AddCommGrpCat.ofHom (φ V.unop.1 V.unop.2)
      naturality V V' i := by
        ext s
        exact hφ V.unop.1 V'.unop.1 V.unop.2 V'.unop.2 (leOfHom i.unop.hom) s }

lemma affineHom_app {F G : X.Modules}
    (φ : ∀ V : X.Opens, IsAffineOpen V → (Γ(F, V) →+ Γ(G, V)))
    (hφ : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
      (s : Γ(F, V)), φ V' hV' (F.presheaf.map (homOfLE h).op s) =
        G.presheaf.map (homOfLE h).op (φ V hV s)) {V : X.Opens} (hV : IsAffineOpen V)
    (s : Γ(F, V)) : (affineHom φ hφ).hom.app (op V) s = φ V hV s := by
  have h := TopCat.Sheaf.extend_hom_app (B := fun U : X.affineOpens ↦ U.1) F.toAbSheaf.obj
    G.toAbSheaf (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
    { app V := AddCommGrpCat.ofHom (φ V.unop.1 V.unop.2)
      naturality V V' i := by
        ext s
        exact hφ V.unop.1 V'.unop.1 V.unop.2 V'.unop.2 (leOfHom i.unop.hom) s } ⟨V, hV⟩
  exact ConcreteCategory.congr_hom h s

/-- Morphisms of abelian sheaves agreeing on affine opens are equal. -/
lemma toAbSheaf_hom_ext_affine {F G : X.Modules} {α β : F.toAbSheaf ⟶ G.toAbSheaf}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (s : Γ(F, V)),
      α.hom.app (op V) s = β.hom.app (op V) s) : α = β := by
  apply (Sheaf.homEquiv).injective
  exact TopCat.Sheaf.hom_ext (B := fun U : X.affineOpens ↦ U.1) F.toAbSheaf.obj G.toAbSheaf
    (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
    fun (U : X.affineOpens) ↦ AddCommGrpCat.ext fun s ↦ h U.1 U.2 s

end BasisHom

section Rees

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]

/-- The direct image `q_{B*}` of the Rees sheaf, on `X`. -/
noncomputable abbrev reesPush : X.Modules :=
  (Scheme.Modules.pushforward (reesFst I f)).obj (reesSheaf I f M)

variable {V : X.Opens}

/-- `Γ(Iⁿ M, V) ≅ Iⁿ Γ(M, V)` for `V` affine. -/
noncomputable def ιPowEquiv (hV : IsAffineOpen V) (n : ℕ) :
    Γ(IPow f I M n, V) ≃+ (idealV f I V n • (⊤ : Submodule Γ(X, V) Γ(M, V))).toAddSubgroup :=
  (AddMonoidHom.ofInjective (f := ((ιPow f I M n).app V).hom)
    (app_injective_of_mono' (ιPow f I M n) V)).trans
    (AddEquiv.addSubgroupCongr (by
      ext x
      exact (mem_range_ιPow_app f I M hV n x)))

variable (hV : IsAffineOpen V)

lemma ιPowEquiv_apply (n : ℕ) (t : Γ(IPow f I M n, V)) :
    (ιPowEquiv I f M hV n t : Γ(M, V)) = (ιPow f I M n).app V t := rfl

/-- `Γ(q_{B*} Rees, V) ≅ ⊕ₙ Iⁿ Γ(M, V) tⁿ` for `V` affine. -/
noncomputable def reesSecEquiv (hV : IsAffineOpen V) : Γ(reesPush I f M, V) ≃+ reesSub I f M V :=
  (AddMonoidHom.ofInjective (reesSecMap_injective I f M hV)).trans
    (AddEquiv.addSubgroupCongr (range_reesSecMap I f M hV))

omit [IsNoetherianRing A] in
lemma reesSecEquiv_apply (s : Γ(reesPush I f M, V)) :
    (reesSecEquiv I f M hV s : PolynomialModule Γ(X, V) Γ(M, V)) = reesSecMap I f M hV s := rfl

include hV in
lemma single_mem_reesSub (n : ℕ) (t : Γ(IPow f I M n, V)) :
    PolynomialModule.single Γ(X, V) n ((ιPow f I M n).app V t) ∈ reesSub I f M V := by
  change ∀ j, _
  intro j
  rw [PolynomialModule.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact (mem_range_ιPow_app f I M hV _ _).mp ⟨t, rfl⟩
  · exact Submodule.zero_mem _

/-- `ιₙ` on sections over an affine open: `t ↦ t tⁿ`. -/
noncomputable def reesIotaApp (hV : IsAffineOpen V) (n : ℕ) :
    Γ(IPow f I M n, V) →+ Γ(reesPush I f M, V) where
  toFun t := (reesSecEquiv I f M hV).symm ⟨_, single_mem_reesSub I f M hV n t⟩
  map_zero' := by
    rw [← map_zero (reesSecEquiv I f M hV).symm]
    congr 1
    ext1
    simp
  map_add' t t' := by
    rw [← map_add (reesSecEquiv I f M hV).symm]
    congr 1
    ext1
    simp [PolynomialModule.single_add]

lemma reesSecMap_reesIotaApp (n : ℕ) (t : Γ(IPow f I M n, V)) :
    reesSecMap I f M hV (reesIotaApp I f M hV n t) =
      PolynomialModule.single Γ(X, V) n ((ιPow f I M n).app V t) := by
  rw [← reesSecEquiv_apply]
  change ((reesSecEquiv I f M hV ((reesSecEquiv I f M hV).symm
    ⟨_, single_mem_reesSub I f M hV n t⟩) : PolynomialModule Γ(X, V) Γ(M, V))) = _
  rw [AddEquiv.apply_symm_apply]

/-- `πₙ` on sections over an affine open: the coefficient of `tⁿ`. -/
noncomputable def reesPiApp (hV : IsAffineOpen V) (n : ℕ) :
    Γ(reesPush I f M, V) →+ Γ(IPow f I M n, V) where
  toFun s := (ιPowEquiv I f M hV n).symm ⟨(reesSecMap I f M hV s).coeff n,
    reesSecMap_mem I f M hV s n⟩
  map_zero' := by
    rw [← map_zero (ιPowEquiv I f M hV n).symm]
    congr 1
    ext1
    change ((reesSecMap I f M hV 0).coeff n : Γ(M, V)) = 0
    rw [map_zero]
    rfl
  map_add' s s' := by
    rw [← map_add (ιPowEquiv I f M hV n).symm]
    congr 1
    ext1
    have h := map_add (reesSecMap I f M hV) (@id Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) s)
      (@id Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) s')
    change ((reesSecMap I f M hV (s + s')).coeff n : Γ(M, V)) = _
    exact congrArg (fun p ↦ PolynomialModule.coeff p n) h

lemma ιPow_reesPiApp (n : ℕ) (s : Γ(reesPush I f M, V)) :
    (ιPow f I M n).app V (reesPiApp I f M hV n s) = (reesSecMap I f M hV s).coeff n := by
  rw [← ιPowEquiv_apply I f M hV]
  change ((ιPowEquiv I f M hV n ((ιPowEquiv I f M hV n).symm
    ⟨_, reesSecMap_mem I f M hV s n⟩) : Γ(M, V))) = _
  rw [AddEquiv.apply_symm_apply]

variable {V' : X.Opens} (hV' : IsAffineOpen V') (hle : V' ≤ V)

lemma reesIotaApp_restrict (n : ℕ) (t : Γ(IPow f I M n, V)) :
    reesIotaApp I f M hV' n ((IPow f I M n).presheaf.map (homOfLE hle).op t) =
      (reesPush I f M).presheaf.map (homOfLE hle).op (reesIotaApp I f M hV n t) := by
  apply reesSecMap_injective I f M hV'
  rw [reesSecMap_reesIotaApp]
  apply PolynomialModule.ext
  ext j
  refine Eq.trans ?_ (reesSecMap_restrict I f M hV hV' hle
    (@id Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) (reesIotaApp I f M hV n t)) j).symm
  have key : reesSecMap I f M hV
      (@id Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) (reesIotaApp I f M hV n t)) =
      PolynomialModule.single Γ(X, V) n ((ιPow f I M n).app V t) :=
    reesSecMap_reesIotaApp I f M hV n t
  rw [key, PolynomialModule.coeff_single,
    PolynomialModule.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs
  · exact CohomologyAux.hom_app_presheaf_map (ιPow f I M n) _ t
  · exact (map_zero _).symm

lemma reesPiApp_restrict (n : ℕ) (s : Γ(reesPush I f M, V)) :
    reesPiApp I f M hV' n ((reesPush I f M).presheaf.map (homOfLE hle).op s) =
      (IPow f I M n).presheaf.map (homOfLE hle).op (reesPiApp I f M hV n s) := by
  apply app_injective_of_mono' (ιPow f I M n) V'
  rw [ιPow_reesPiApp, CohomologyAux.hom_app_presheaf_map, ιPow_reesPiApp]
  exact reesSecMap_restrict I f M hV hV' hle s n

end Rees

section Maps

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]

/-- `ιₙ : Iⁿ M ⟶ q_{B*}(⊕ Iᵐ M tᵐ)`, `t ↦ t tⁿ`, on the underlying abelian sheaves. -/
noncomputable def reesIota (n : ℕ) : (IPow f I M n).toAbSheaf ⟶ (reesPush I f M).toAbSheaf :=
  affineHom (fun _ hV ↦ reesIotaApp I f M hV n)
    (fun _ _ hV hV' h t ↦ reesIotaApp_restrict I f M hV hV' h n t)

/-- `πₙ : q_{B*}(⊕ Iᵐ M tᵐ) ⟶ Iⁿ M`, the coefficient of `tⁿ`. -/
noncomputable def reesPi (n : ℕ) : (reesPush I f M).toAbSheaf ⟶ (IPow f I M n).toAbSheaf :=
  affineHom (fun _ hV ↦ reesPiApp I f M hV n)
    (fun _ _ hV hV' h s ↦ reesPiApp_restrict I f M hV hV' h n s)

lemma reesIota_app {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (t : Γ(IPow f I M n, V)) :
    (reesIota I f M n).hom.app (op V) t = reesIotaApp I f M hV n t :=
  affineHom_app _ _ hV t

lemma reesPi_app {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (s : Γ(reesPush I f M, V)) :
    (reesPi I f M n).hom.app (op V) s = reesPiApp I f M hV n s :=
  affineHom_app _ _ hV s

lemma reesPi_app' {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (s : (reesPush I f M).toAbSheaf.obj.obj (op V)) :
    (reesPi I f M n).hom.app (op V) s = reesPiApp I f M hV n s :=
  affineHom_app _ _ hV s

lemma toAbSheaf_comp_app_apply {F G H : X.Modules} (α : F.toAbSheaf ⟶ G.toAbSheaf)
    (β : G.toAbSheaf ⟶ H.toAbSheaf) (V : X.Opens) (s : Γ(F, V)) :
    (α ≫ β).hom.app (op V) s = β.hom.app (op V) (α.hom.app (op V) s) := rfl

lemma toAbSheaf_hom_app_apply {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens) (s : Γ(F, V)) :
    (Scheme.Modules.Hom.toAbSheaf φ).hom.app (op V) s = φ.app V s := rfl

lemma reesPi_reesIota_app {V : X.Opens} (hV : IsAffineOpen V) (j p : ℕ)
    (t : Γ(IPow f I M j, V)) :
    (ιPow f I M p).app V ((reesPi I f M p).hom.app (op V) ((reesIota I f M j).hom.app (op V) t)) =
      if j = p then (ιPow f I M j).app V t else 0 := by
  rw [reesIota_app I f M hV, reesPi_app I f M hV, ιPow_reesPiApp, reesSecMap_reesIotaApp,
    PolynomialModule.coeff_single, Finsupp.single_apply]

lemma reesIota_reesPi_self (n : ℕ) : reesIota I f M n ≫ reesPi I f M n = 𝟙 _ := by
  refine toAbSheaf_hom_ext_affine fun V hV t ↦ app_injective_of_mono' (ιPow f I M n) V ?_
  have h := reesPi_reesIota_app I f M hV n n t
  simp only [↓reduceIte] at h
  exact h

lemma reesIota_reesPi_ne {j p : ℕ} (hjp : j ≠ p) : reesIota I f M j ≫ reesPi I f M p = 0 := by
  refine toAbSheaf_hom_ext_affine fun V hV t ↦ app_injective_of_mono' (ιPow f I M p) V ?_
  have h := reesPi_reesIota_app I f M hV j p t
  simp only [hjp, ↓reduceIte] at h
  exact h.trans (map_zero _).symm

end Maps

end AlgebraicGeometry.CohomologyAux
