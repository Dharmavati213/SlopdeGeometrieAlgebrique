/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupLoopInertia
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupTame
import SGA.SGA1.ExposeV.ExactFunctors

/-!
# Orbits of an inertia group on the fibres of a Galois covering

The inertia side of the comparison of inertia groups with loops (XIII.2.12 over `ℂ`, registry row
C32). An inertia subgroup at a point `a` of a curve is the image of `π₁(T)`,
`T = U ×_X Spec 𝒪^{sh}_{X,a}`, transported along a path; when `T ≅ Spec K'` for a field `K'`, the
orbits of `π₁(T)` on the fibre of an étale covering `Y` of `T` are the points of `Y`: two geometric
points `D → Ω` of the finite étale `K'`-algebra `D` of `Y` lie in the same orbit iff they have the
same kernel (`LoopInertia.exists_smul_eq_iff_ker_eq`, a consequence of V.8.1).

* `exists_mem_range_autMap_smul_eq_iff`, `exists_smul_eq_iff_of_surjective_autWhiskerLeft`: orbits
  of the image of `π_{F} → π_{F'}` (induced by `H` with `H ⋙ F ≅ F'`) on `F'(X)` are the orbits of
  `π_F` on `F(H X)`, and of all of `π_{F'}` when `H` is fully faithful (V.6.9);
* `exists_smul_eq_iff_ker_eq_of_isIso`: for `κ : Spec K ⟶ T` an isomorphism, the orbits of
  `π₁(T, η̄ ≫ κ)` on the fibre of `Y ∈ FEt T` are the kernel classes of the geometric points of
  `TameGaloisAlgebra.pullbackAlgebra Y κ`.
-/

universe u w

open CategoryTheory PreGaloisCategory Opposite

namespace SGA.SGA1.ExposeXIII.LoopInertia

section AutMap

open ExposeV

variable {C : Type*} [Category C] {D : Type*} [Category D] (H : C ⥤ D)
  {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}} (e : H ⋙ F ≅ F')

lemma autMap_smul (σ : Aut F) {X : C} (x : F'.obj X) :
    autMap H e σ • x = e.hom.app X (σ.hom.app (H.obj X) (e.inv.app X x)) :=
  rfl

/-- **Orbits of the image of `autMap`.** For `e : H ⋙ F ≅ F'`, two points `x, y` of `F'(X)` are in
the same orbit of the image of `Aut F → Aut F'` iff `e⁻¹ x` and `e⁻¹ y` are in the same orbit of
`Aut F` on `F(H X)`. -/
theorem exists_mem_range_autMap_smul_eq_iff {X : C} (x y : F'.obj X) :
    (∃ k ∈ (autMap H e).range, k • x = y) ↔
      ∃ σ : Aut F, σ • (show F.obj (H.obj X) from e.inv.app X x) = e.inv.app X y := by
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    rw [autMap_smul]
    exact (FintypeCat.hom_inv_id_apply (e.app X) _).symm
  · rintro ⟨σ, hσ⟩
    refine ⟨_, ⟨σ, rfl⟩, ?_⟩
    rw [autMap_smul]
    change e.hom.app X (σ • (show F.obj (H.obj X) from e.inv.app X x)) = y
    rw [hσ]
    exact FintypeCat.inv_hom_id_apply (e.app X) y

/-- `autMap H e` is surjective when `autWhiskerLeft H F` is (e.g. `H` fully faithful between
Galois categories, V.6.9). -/
theorem surjective_autMap (hH : Function.Surjective (autWhiskerLeft H F)) :
    Function.Surjective (autMap H e) := by
  intro τ
  obtain ⟨σ, hσ⟩ := hH (e ≪≫ τ ≪≫ e.symm)
  refine ⟨σ, ?_⟩
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  have h := congrArg (fun ρ : Aut (H ⋙ F) ↦ ρ.hom.app X) hσ
  simp only [autWhiskerLeft_hom_app, Iso.trans_hom, NatTrans.comp_app] at h
  rw [autMap_hom_app, h]
  change e.inv.app X ≫ (e.hom.app X ≫ τ.hom.app X ≫ e.inv.app X) ≫ e.hom.app X = τ.hom.app X
  simp

/-- When `autWhiskerLeft H F` is surjective, the orbits of `Aut F'` on `F'(X)` are the orbits of
`Aut F` on `F(H X)`, through `e : H ⋙ F ≅ F'`. -/
theorem exists_smul_eq_iff_of_surjective_autWhiskerLeft
    (hH : Function.Surjective (autWhiskerLeft H F)) {X : C} (x y : F'.obj X) :
    (∃ τ : Aut F', τ • x = y) ↔
      ∃ σ : Aut F, σ • (show F.obj (H.obj X) from e.inv.app X x) = e.inv.app X y := by
  rw [← exists_mem_range_autMap_smul_eq_iff H e x y,
    (MonoidHom.range_eq_top.mpr (surjective_autMap H e hH))]
  simp

end AutMap

section Path

open ExposeV

variable {C : Type*} [Category C] {F₁ F₂ : C ⥤ FintypeCat.{w}}

/-- **Orbits are transported along paths.** For `γ : F₁ ≅ F₂` and `K ≤ Aut F₁`, two points
`x, y ∈ F₂(X)` are in the same orbit of `γ K γ⁻¹` iff `γ⁻¹ x` and `γ⁻¹ y` are in the same orbit of
`K`. -/
theorem exists_mem_map_conjAut_smul_eq_iff (γ : F₁ ≅ F₂) (K : Subgroup (Aut F₁)) {X : C}
    (x y : F₂.obj X) :
    (∃ k ∈ K.map γ.conjAut.toMonoidHom, k • x = y) ↔
      ∃ k ∈ K, k • (γ.inv.app X x) = γ.inv.app X y := by
  have hconj (k : Aut F₁) (z : F₂.obj X) :
      γ.conjAut k • z = γ.hom.app X (k • γ.inv.app X z) := by
    rw [Iso.conjAut_apply]
    rfl
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    change _ = γ.inv.app X (γ.conjAut k • x)
    rw [hconj]
    exact (FintypeCat.hom_inv_id_apply (γ.app X) _).symm
  · rintro ⟨k, hk, hky⟩
    refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
    change γ.conjAut k • x = y
    rw [hconj, hky]
    exact FintypeCat.inv_hom_id_apply (γ.app X) y

end Path

section Field

open AlgebraicGeometry ExposeV TameGaloisAlgebra

variable {T : Scheme.{u}} [ConnectedSpace T] {K : Type u} [Field K] (κ : Spec (.of K) ⟶ T)
  [IsIso κ] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Spec (.of K))

/-- **Orbits of `π₁` of a field-like base are kernel classes** (a consequence of V.8.1): for
`κ : Spec K ⟶ T` an isomorphism, an étale covering `Y` of `T` and two points `x, y` of its fibre
at `η ≫ κ`, some element of `π₁(T, η ≫ κ)` maps `x` to `y` iff the corresponding geometric points
`D → Ω` of the algebra `D = pullbackAlgebra Y κ` of `Y ×_T Spec K` (`TameGaloisAlgebra.fiberIso`)
have the same kernel. -/
theorem exists_smul_eq_iff_ker_eq_of_isIso (Y : FEt T) (x y : (FEt.fiber Ω (η ≫ κ)).obj Y) :
    letI := algebraOfPoint (.of K) Ω η
    (∃ τ : etaleFundamentalGroup Ω (η ≫ κ), τ • x = y) ↔
      RingHom.ker (toAlgHom K Ω ((fiberIso κ Ω η).hom.app Y x)) =
        RingHom.ker (toAlgHom K Ω ((fiberIso κ Ω η).hom.app Y y)) := by
  let := algebraOfPoint (.of K) Ω η
  have : (FEt.pullback κ).IsEquivalence :=
    inferInstanceAs (FEt.pullback (asIso κ).hom).IsEquivalence
  let H : FEt T ⥤ (CommAlgCat.FiniteEtale.{u} (CommRingCat.of K))ᵒᵖ :=
    FEt.pullback κ ⋙ (specEquivalence (.of K)).inverse
  have hH : H.Full ∧ H.Faithful := ⟨inferInstance, inferInstance⟩
  have : FiberFunctor (H ⋙ ExposeV.fiberFunctor (CommRingCat.of K) Ω) :=
    ExposeV.fiberFunctor_comp H _
  have hsurj :=
    ((surjective_autWhiskerLeft_tfae H (ExposeV.fiberFunctor (CommRingCat.of K) Ω)).out 1 3).mpr hH
  rw [exists_smul_eq_iff_of_surjective_autWhiskerLeft H
    (F := ExposeV.fiberFunctor (CommRingCat.of K) Ω) (fiberIso κ Ω η).symm hsurj x y]
  exact exists_smul_eq_iff_ker_eq K Ω _ _ _

omit [ConnectedSpace T] [IsIso κ] [IsSepClosed Ω] in
/-- **Equivariance of `fiberIso`**: the geometric point of `D = pullbackAlgebra Y κ` attached to
`g • x` (`g` an automorphism of `Y`) is the one attached to `x`, composed with the action of
`g⁻¹` on `D`. -/
lemma toAlgHom_fiberIso_map (Y : FEt T) (g : Aut Y) (x : (FEt.fiber Ω (η ≫ κ)).obj Y) :
    letI := algebraOfPoint (.of K) Ω η
    toAlgHom K Ω ((fiberIso κ Ω η).hom.app Y ((FEt.fiber Ω (η ≫ κ)).map g.hom x)) =
      (toAlgHom K Ω ((fiberIso κ Ω η).hom.app Y x)).comp
        (TameGaloisAlgebra.autHom Y κ g⁻¹).toAlgHom := by
  let := algebraOfPoint (.of K) Ω η
  have h := congrArg (fun f ↦ f x) ((fiberIso κ Ω η).hom.naturality g.hom)
  simp only [FintypeCat.comp_apply] at h
  rw [h]
  have h2 := comp_autHom Y κ Ω η g⁻¹ (toAlgHom K Ω ((fiberIso κ Ω η).hom.app Y x))
  rw [inv_inv] at h2
  exact h2.symm

end Field

section Inertia

open AlgebraicGeometry ExposeV TameGaloisAlgebra

variable {U T : Scheme.{u}} [ConnectedSpace T] (f : T ⟶ U) {K : Type u} [Field K]
  (κ : Spec (.of K) ⟶ T) [IsIso κ] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ Spec (.of K)) {Ω₁ : Type u} [Field Ω₁] [IsSepClosed Ω₁]
  {ξ : Spec (.of Ω₁) ⟶ U} (γ : etalePaths Ω Ω₁ ((η ≫ κ) ≫ f) ξ) (E : FEt U)

/-- The action of `Aut E` on the algebra `D` of `(f^* E) ×_T Spec K`. -/
noncomputable def autHomPullback :
    Aut E →* ((pullbackAlgebra ((FEt.pullback f).obj E) κ).obj ≃ₐ[K]
      (pullbackAlgebra ((FEt.pullback f).obj E) κ).obj) :=
  (TameGaloisAlgebra.autHom ((FEt.pullback f).obj E) κ).comp ((FEt.pullback f).mapAut E)

/-- The geometric point of the algebra `D` of `(f^* E) ×_T Spec K` attached to a point of the
fibre of `E` at `ξ`, through the path `γ`. -/
noncomputable def pointOfPath (e : (FEt.fiber Ω₁ ξ).obj E) :
    letI := algebraOfPoint (.of K) Ω η
    (pullbackAlgebra ((FEt.pullback f).obj E) κ).obj →ₐ[K] Ω :=
  letI := algebraOfPoint (.of K) Ω η
  toAlgHom K Ω ((fiberIso κ Ω η).hom.app ((FEt.pullback f).obj E)
    ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E (γ.inv.app E e)))

omit [IsSepClosed Ω₁] in
/-- **Orbits of an inertia-type subgroup.** Let `f : T ⟶ U` with `T ≅ Spec K` (`κ`), `η̄` a
geometric point of `Spec K` and `γ` a path from `η̄ ≫ κ ≫ f` to `ξ`, and let `H` be the image of
`π₁(T, η̄ ≫ κ) → π₁(U, ξ)` (`π₁(f)` followed by the change of base point along `γ`; e.g. an
inertia subgroup, `IsInertiaSubgroupAt`). For an étale covering `E` of `U`, a point `e` of its
fibre at `ξ` and `g ∈ Aut E`, some element of `H` maps `e` to `g • e` iff the automorphism
`g⁻¹` of the algebra `D` of `(f^* E) ×_T Spec K` fixes the kernel of the geometric point of `D`
attached to `e` (`pointOfPath`). -/
theorem exists_mem_map_smul_eq_iff_comap_eq (e : (FEt.fiber Ω₁ ξ).obj E) (g : Aut E) :
    (∃ k ∈ (etaleFundamentalGroup.map Ω f (η ≫ κ)).range.map
        (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω₁ γ).toMonoidHom,
        k • e = (FEt.fiber Ω₁ ξ).map g.hom e) ↔
      (RingHom.ker (pointOfPath f κ η γ E e)).comap
          ((autHomPullback f κ E g⁻¹ : _ ≃ₐ[K] _) : _ →+* _) =
        RingHom.ker (pointOfPath f κ η γ E e) := by
  let := algebraOfPoint (.of K) Ω η
  change (∃ k ∈ (etaleFundamentalGroup.map Ω f (η ≫ κ)).range.map γ.conjAut.toMonoidHom,
    k • e = (FEt.fiber Ω₁ ξ).map g.hom e) ↔ _
  rw [exists_mem_map_conjAut_smul_eq_iff]
  have hγ : γ.inv.app E ((FEt.fiber Ω₁ ξ).map g.hom e) =
      (FEt.fiber Ω ((η ≫ κ) ≫ f)).map g.hom (γ.inv.app E e) := by
    have := congrArg (fun φ ↦ φ e) (γ.inv.naturality g.hom)
    simp only [FintypeCat.comp_apply] at this
    exact this
  rw [hγ]
  change (∃ k ∈ (autMap (FEt.pullback f) (FEt.pullbackFiberIso Ω f (η ≫ κ))).range, _) ↔ _
  rw [exists_mem_range_autMap_smul_eq_iff]
  set e' := (FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E (γ.inv.app E e)
  have he : (FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E
      ((FEt.fiber Ω ((η ≫ κ) ≫ f)).map g.hom (γ.inv.app E e)) =
      (FEt.fiber Ω (η ≫ κ)).map ((FEt.pullback f).mapAut E g).hom e' := by
    have := congrArg (fun φ ↦ φ (γ.inv.app E e))
      ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.naturality g.hom)
    simp only [FintypeCat.comp_apply] at this
    exact this
  rw [he]
  change (∃ σ : etaleFundamentalGroup Ω (η ≫ κ), σ • e' = _) ↔ _
  rw [exists_smul_eq_iff_ker_eq_of_isIso κ Ω η, toAlgHom_fiberIso_map, eq_comm]
  simp only [pointOfPath, autHomPullback, MonoidHom.comp_apply, map_inv]
  rfl

omit [ConnectedSpace T] [IsIso κ] [IsSepClosed Ω] [IsSepClosed Ω₁] in
/-- The geometric point of the algebra `D` of `(f^* E) ×_T Spec K` attached to a point of the fibre
of `E` at `η̄ ≫ κ ≫ f`, and its equivariance: `ψ (g • e) = ψ e ∘ g⁻¹`. -/
lemma toAlgHom_fiberIso_pullbackFiberIso_map (e : (FEt.fiber Ω ((η ≫ κ) ≫ f)).obj E) (g : Aut E) :
    letI := algebraOfPoint (.of K) Ω η
    toAlgHom K Ω ((fiberIso κ Ω η).hom.app ((FEt.pullback f).obj E)
        ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E ((FEt.fiber Ω _).map g.hom e))) =
      (toAlgHom K Ω ((fiberIso κ Ω η).hom.app ((FEt.pullback f).obj E)
        ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E e))).comp
        (autHomPullback f κ E g⁻¹).toAlgHom := by
  let := algebraOfPoint (.of K) Ω η
  have he : (FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E ((FEt.fiber Ω ((η ≫ κ) ≫ f)).map g.hom e) =
      (FEt.fiber Ω (η ≫ κ)).map ((FEt.pullback f).mapAut E g).hom
        ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.app E e) := by
    have := congrArg (fun φ ↦ φ e) ((FEt.pullbackFiberIso Ω f (η ≫ κ)).inv.naturality g.hom)
    simp only [FintypeCat.comp_apply] at this
    exact this
  rw [he, toAlgHom_fiberIso_map]
  simp only [autHomPullback, MonoidHom.comp_apply, map_inv]
  rfl

omit [ConnectedSpace T] [IsIso κ] [IsSepClosed Ω₁] in
/-- **`Aut E` acts simply transitively on the geometric points of `D`** for a Galois covering `E`
of a connected `U`: `g ↦ φ ∘ g` is bijective for every `K`-algebra map `φ : D → Ω`, `D` the
algebra of `(f^* E) ×_T Spec K` (`autHomPullback`). -/
theorem bijective_comp_autHomPullback [ConnectedSpace U] [IsGalois E] :
    letI := algebraOfPoint (.of K) Ω η
    ∀ φ : (pullbackAlgebra ((FEt.pullback f).obj E) κ).obj →ₐ[K] Ω,
      Function.Bijective fun g : Aut E ↦ φ.comp (autHomPullback f κ E g).toAlgHom := by
  let := algebraOfPoint (.of K) Ω η
  intro φ
  -- the bijection `ψ : F(E) → Hom_K(D, Ω)`
  let α := (FEt.pullbackFiberIso Ω f (η ≫ κ)).symm.app E ≪≫
    (fiberIso κ Ω η).app ((FEt.pullback f).obj E)
  let ψ : (FEt.fiber Ω ((η ≫ κ) ≫ f)).obj E → _ := fun e ↦ toAlgHom K Ω (α.hom e)
  have hψ : Function.Bijective ψ := (FintypeCat.equivEquivIso.symm α).bijective
  obtain ⟨x, hx⟩ := hψ.2 φ
  have hbij := evaluation_aut_bijective_of_isGalois (FEt.fiber Ω ((η ≫ κ) ≫ f)) E x
  have key : (fun g : Aut E ↦ φ.comp (autHomPullback f κ E g).toAlgHom) =
      ψ ∘ (fun g : Aut E ↦ (FEt.fiber Ω ((η ≫ κ) ≫ f)).map g.hom x) ∘ (fun g ↦ g⁻¹) := by
    funext g
    simp only [Function.comp_apply]
    rw [← hx]
    have := toAlgHom_fiberIso_pullbackFiberIso_map f κ η E x g⁻¹
    rw [inv_inv] at this
    exact this.symm
  rw [key]
  exact hψ.comp (hbij.comp (Equiv.inv _).bijective)

end Inertia

end SGA.SGA1.ExposeXIII.LoopInertia
