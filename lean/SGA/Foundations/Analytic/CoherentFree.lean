/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.CoherentSheaf

/-!
# Sections of finite free modules

Let `X` be a locally ringed space and `I` a finite type. The free `𝒪_X`-module `𝒪_X^I`
(mathlib's `SheafOfModules.free I`, a coproduct of copies of `𝒪_X`) has, over every open `V`,
the basis sections `eᵢ|_V` (`LocallyRingedSpace.Modules.freeBasis`): every section over `V` is
`∑ᵢ aᵢ eᵢ|_V` with `aᵢ ∈ 𝒪_X(V)` (`exists_eq_sum_smul_freeBasis`), and the morphism
`𝒪_X^I ⟶ M` given by sections `sᵢ` of `M` sends `∑ᵢ aᵢ eᵢ|_V` to `∑ᵢ aᵢ sᵢ|_V`
(`freeHomEquiv_symm_app_sum_smul_freeBasis`). This is how relations between sections of a module
are read off the kernel of `𝒪_X^I ⟶ M` (Serre, *Faisceaux algébriques cohérents*, §2).

On stalks the germs of the `eᵢ` form a basis (`stalkFreeLinearEquiv_germ_freeBasis`,
`sum_smul_germ_freeBasis_eq_zero_iff`, `generatesAt_freeBasis`), so the relations between sections
`uⱼ = ∑ᵢ bⱼᵢ eᵢ` are those of the coefficient matrix (`mem_stalkRelations_freeModule_iff`). With
the matrix form of Oka's theorem this gives **the coherence of `𝒪^I` on `𝕜^σ`**
(`AnalyticGeometry.isCoherentOn_freeModule_modelSpace`).
-/

noncomputable section

-- the ring structure on sections of `X.ringCatSheaf` is only defeq to that of `X.presheaf` after
-- unfolding, which `rw` does not do otherwise
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} {I : Type u}

/-- The free module `𝒪_X^I` as an `𝒪_X`-module. -/
abbrev freeModule (X : LocallyRingedSpace.{u}) (I : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) I

/-- The `i`-th basis section of `𝒪_X^I` over `V`. -/
abbrev freeBasis (i : I) (V : Opens X) : (freeModule X I).presheaf.obj (op V) :=
  (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op V)

/-- The value of a section of a module over `V`, as an element of the module of sections. -/
abbrev sectionAt (M : X.Modules) (s : M.sections) (V : Opens X) : M.presheaf.obj (op V) :=
  s.val (op V)

lemma freeBasis_eq (i : I) (V : Opens X) :
    freeBasis (X := X) i V = (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op V)
      (1 : X.ringCatSheaf.obj.obj (op V)) :=
  rfl

/-- A morphism of `𝒪_X`-modules is `𝒪_X(V)`-linear on sections over `V`. -/
lemma app_smul {M N : X.Modules} (f : M ⟶ N) (V : Opens X) (a : X.presheaf.obj (op V))
    (m : M.presheaf.obj (op V)) :
    f.val.app (op V) (a • m) = a • f.val.app (op V) m :=
  (f.val.app (op V)).hom.map_smul a m

/-- The morphism `𝒪_X ⟶ 𝒪_X^I` onto the `i`-th summand sends `a` to `a eᵢ`. -/
lemma ιFree_app (i : I) (V : Opens X) (a : X.presheaf.obj (op V)) :
    (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op V) a = a • freeBasis i V := by
  rw [freeBasis_eq]
  refine Eq.trans ?_ (app_smul _ V a _)
  congr 1
  exact (mul_one a).symm

/-- Evaluating morphisms of `𝒪_X`-modules on a section is additive in the morphism. -/
def appAddHom {M N : X.Modules} (V : Opens X) (m : M.presheaf.obj (op V)) :
    (M ⟶ N) →+ N.presheaf.obj (op V) where
  toFun f := f.val.app (op V) m
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection `𝒪_X^I ⟶ 𝒪_X` onto the `i`-th summand. -/
def freeProj [DecidableEq I] (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Sigma.desc fun j ↦ if j = i then 𝟙 _ else 0

@[reassoc]
lemma ιFree_freeProj [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ freeProj i = if j = i then 𝟙 _ else 0 :=
  Sigma.ι_desc _ _

lemma sum_freeProj_ιFree [Fintype I] [DecidableEq I] :
    ∑ i, freeProj (X := X) i ≫ SheafOfModules.ιFree (R := X.ringCatSheaf) i =
      𝟙 (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  have h1 : ∀ i, SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ freeProj i ≫
      SheafOfModules.ιFree i = if j = i then SheafOfModules.ιFree i else 0 := fun i ↦ by
    by_cases hij : j = i
    · subst hij
      simp [← Category.assoc, ιFree_freeProj]
    · simp [← Category.assoc, ιFree_freeProj, hij]
  refine (Preadditive.comp_sum _ _ _).trans ?_
  refine (Finset.sum_congr rfl fun i _ ↦ h1 i).trans ?_
  refine (Finset.sum_ite_eq Finset.univ j _).trans ?_
  exact (ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_univ j))).trans (Category.comp_id _).symm

/-- **Sections of a finite free module**: every section of `𝒪_X^I` over `V` is `∑ᵢ aᵢ eᵢ|_V`. -/
theorem exists_eq_sum_smul_freeBasis [Fintype I] (V : Opens X)
    (f : (freeModule X I).presheaf.obj (op V)) :
    ∃ a : I → X.presheaf.obj (op V), f = ∑ i, a i • freeBasis i V := by
  classical
  refine ⟨fun i ↦ (freeProj i).val.app (op V) f, ?_⟩
  have h := congrArg (appAddHom (N := freeModule X I) V f) (sum_freeProj_ιFree (X := X) (I := I))
  rw [map_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact ιFree_app i V _

/-- The morphism `𝒪_X^I ⟶ M` given by sections `sᵢ` of `M` sends `eᵢ|_V` to `sᵢ|_V`. -/
lemma freeHomEquiv_symm_app_freeBasis (M : X.Modules) (s : I → M.sections) (i : I)
    (V : Opens X) :
    ((SheafOfModules.freeHomEquiv M).symm s).val.app (op V) (freeBasis i V) =
      M.sectionAt (s i) V :=
  congrArg (fun t : M.sections ↦ t.val (op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)

/-- The morphism `𝒪_X^I ⟶ M` given by sections `sᵢ` of `M` sends `∑ᵢ aᵢ eᵢ|_V` to
`∑ᵢ aᵢ sᵢ|_V`. -/
lemma freeHomEquiv_symm_app_sum_smul_freeBasis [Fintype I] (M : X.Modules) (s : I → M.sections)
    (V : Opens X) (a : I → X.presheaf.obj (op V)) :
    ((SheafOfModules.freeHomEquiv M).symm s).val.app (op V) (∑ i, a i • freeBasis i V) =
      ∑ i, a i • M.sectionAt (s i) V := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [app_smul, freeHomEquiv_symm_app_freeBasis]

/-! ### Stalks of finite free modules -/

/-- The germ of the basis section `eᵢ` is the `i`-th basis vector of the stalk `𝒪_{X,x}^{(I)}`. -/
lemma stalkFreeLinearEquiv_germ_freeBasis (i : I) (V : Opens X) (x : X) (hx : x ∈ V) :
    stalkFreeLinearEquiv x I ((freeModule X I).presheaf.germ V x hx (freeBasis i V)) =
      Finsupp.single i 1 := by
  have h1 : (freeModule X I).presheaf.germ V x hx (freeBasis i V) =
      (stalkFunctor x).map (SheafOfModules.ιFree (R := X.ringCatSheaf) i)
        ((structureModule X).presheaf.germ V x hx (1 : X.presheaf.obj (op V))) :=
    (stalkMap_germ (SheafOfModules.ιFree (R := X.ringCatSheaf) i) x V hx _).symm
  rw [h1, stalkFreeLinearEquiv_map_ιFree]
  congr 1
  exact (stalkUnitLinearEquiv_germ x V hx _).trans (map_one _)

/-- In the stalk, `∑ᵢ aᵢ (eᵢ)ₓ` has coordinates `a`. -/
lemma stalkFreeLinearEquiv_sum_smul_germ_freeBasis [Fintype I] (V : Opens X) (x : X)
    (hx : x ∈ V) (a : I → X.presheaf.stalk x) :
    stalkFreeLinearEquiv x I
      (∑ i, a i • (freeModule X I).presheaf.germ V x hx (freeBasis i V)) =
      ∑ i, Finsupp.single i (a i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, stalkFreeLinearEquiv_germ_freeBasis, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The germs of the basis sections are linearly independent: `∑ᵢ aᵢ (eᵢ)ₓ = 0` iff `a = 0`. -/
lemma sum_smul_germ_freeBasis_eq_zero_iff [Fintype I] (V : Opens X) (x : X) (hx : x ∈ V)
    (a : I → X.presheaf.stalk x) :
    ∑ i, a i • (freeModule X I).presheaf.germ V x hx (freeBasis i V) = 0 ↔ a = 0 := by
  classical
  rw [← (stalkFreeLinearEquiv x I).map_eq_zero_iff,
    stalkFreeLinearEquiv_sum_smul_germ_freeBasis]
  constructor
  · intro h
    funext i
    have := congrArg (fun f : I →₀ X.presheaf.stalk x ↦ f i) h
    simpa [Finsupp.finsetSum_apply, Finsupp.single_apply] using this
  · rintro rfl
    simp

/-- The relations between sections `uⱼ = ∑ᵢ bⱼᵢ eᵢ` of a finite free module are the relations of
the matrix of their coefficients: `∑ⱼ cⱼ (uⱼ)ₓ = 0` iff `∑ⱼ cⱼ (bⱼᵢ)ₓ = 0` for every `i`. -/
lemma mem_stalkRelations_freeModule_iff [Fintype I] {J : Type*} [Fintype J] {W : Opens X}
    (u : J → (freeModule X I).presheaf.obj (op W)) (b : J → I → X.presheaf.obj (op W))
    (hb : ∀ j, u j = ∑ i, b j i • freeBasis i W) (x : X) (hx : x ∈ W)
    (c : J → X.presheaf.stalk x) :
    c ∈ (freeModule X I).stalkRelations u x hx ↔
      ∀ i, ∑ j, c j * X.presheaf.germ W x hx (b j i) = 0 := by
  rw [mem_stalkRelations]
  have h : ∑ j, c j • (freeModule X I).presheaf.germ W x hx (u j) =
      ∑ i, (∑ j, c j * X.presheaf.germ W x hx (b j i)) •
        (freeModule X I).presheaf.germ W x hx (freeBasis i W) := by
    simp_rw [hb, germ_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [h, sum_smul_germ_freeBasis_eq_zero_iff]
  exact funext_iff

/-- The basis sections generate the finite free module at every point. -/
lemma generatesAt_freeBasis [Finite I] (V : Opens X) (x : X) (hx : x ∈ V) :
    (freeModule X I).GeneratesAt (fun i ↦ freeBasis i V) x hx := by
  have := Fintype.ofFinite I
  rw [GeneratesAt, eq_top_iff]
  intro m _
  set f := stalkFreeLinearEquiv x I m
  have hm : m = ∑ i, f i • (freeModule X I).presheaf.germ V x hx (freeBasis i V) := by
    apply (stalkFreeLinearEquiv x I).injective
    rw [stalkFreeLinearEquiv_sum_smul_germ_freeBasis, Finsupp.univ_sum_single]
  rw [hm]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end AlgebraicGeometry.LocallyRingedSpace.Modules

namespace AnalyticGeometry

open AlgebraicGeometry LocallyRingedSpace Modules

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type} [Fintype σ]

/-- **Oka's theorem for finite free modules**: the relations between finitely many sections of
`𝒪^I` over an open `W ⊆ 𝕜^σ` are of finite type (the matrix form of Oka's theorem,
`hasFiniteRelationsNear`). -/
theorem hasFiniteRelations_freeModule_modelSpace {I : Type} [Finite I]
    {W : Opens (modelSpace 𝕜 (σ → 𝕜))} {p : ℕ}
    (u : Fin p → (freeModule (modelSpace 𝕜 (σ → 𝕜)) I).presheaf.obj (op W)) :
    (freeModule (modelSpace 𝕜 (σ → 𝕜)) I).HasFiniteRelations u := by
  classical
  have := Fintype.ofFinite I
  intro x hx
  choose b hb using fun j ↦ exists_eq_sum_smul_freeBasis W (u j)
  let B : Fin p → I → analyticSections 𝕜 (E := σ → 𝕜) W := fun j i ↦ b j i
  let A : I → Fin p → (σ → 𝕜) → 𝕜 := fun i j ↦ extendByZero (B j i).1
  obtain ⟨V, hV, hxV, hA, n, g, hg, hgen⟩ :=
    hasFiniteRelationsNear A x fun i j ↦ (B j i).2 ⟨x, hx⟩
  let W' : Opens (modelSpace 𝕜 (σ → 𝕜)) := ⟨V, hV⟩ ⊓ W
  have hW' : W' ≤ W := inf_le_right
  let r : Fin n → Fin p → (modelSpace 𝕜 (σ → 𝕜)).presheaf.obj (op W') := fun k j ↦
    ofAnalyticOnNhd (E := σ → 𝕜) (U := W') (g k j) fun y hy ↦ hg k j y hy.1
  have hr : ∀ y (hy : y ∈ W') k j, (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W' y hy (r k j) =
      germOf (g k j) (hg k j y hy.1) := fun y hy k j ↦ by
    refine (germ_eq_germOf W' hy (r k j)).trans (germOf_congr _ ?_)
    filter_upwards [W'.2.mem_nhds hy] with z hz
    rw [extendByZero_of_mem _ hz]
    rfl
  have hs : ∀ y (hy : y ∈ W) j i, (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W y hy (b j i) =
      germOf (A i j) ((B j i).2 ⟨y, hy⟩) := fun y hy j i ↦
    germ_eq_germOf W hy (b j i)
  have hrel : ∀ y (hy : y ∈ W'),
      (freeModule (modelSpace 𝕜 (σ → 𝕜)) I).stalkRelations u y (hW' hy) =
        Submodule.span _
          (Set.range fun k j ↦ (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W' y hy (r k j)) :=
      fun y hy ↦ by
    have key : ∀ c : Fin p → (analyticPresheaf 𝕜 (σ → 𝕜)).stalk y,
        ((∀ i, ∑ j, c j * germOf (A i j) (hA i j y hy.1) = 0) ↔
          c ∈ Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk y)
            (Set.range fun k j ↦ germOf (g k j) (hg k j y hy.1))) := by
      intro c
      rw [← hgen y hy.1, mem_matrixRelationModule]
    ext c
    rw [mem_stalkRelations_freeModule_iff u b hb]
    simp only [hs y (hW' hy), hr y hy]
    exact key c
  refine ⟨W', hW', ⟨hxV, hx⟩, n, r, fun k ↦ ?_, hrel⟩
  refine sum_smul_eq_zero_of_germ fun y hy ↦ ?_
  rw [stalkRelations_resSection, hrel y hy]
  exact Submodule.subset_span ⟨k, rfl⟩

/-- **Oka's coherence theorem for finite free modules**: `𝒪^I` is coherent on `𝕜^σ`. -/
theorem isCoherentOn_freeModule_modelSpace {I : Type} [Finite I]
    (Ω : Opens (modelSpace 𝕜 (σ → 𝕜))) :
    (freeModule (modelSpace 𝕜 (σ → 𝕜)) I).IsCoherentOn Ω := by
  classical
  have := Fintype.ofFinite I
  let e := Fintype.equivFin I
  refine ⟨fun x hx ↦ ⟨Ω, le_rfl, hx, Fintype.card I, fun k ↦ freeBasis (e.symm k) Ω,
    fun y hy ↦ ?_⟩, fun W _ p u ↦ hasFiniteRelations_freeModule_modelSpace u⟩
  have := generatesAt_freeBasis (X := modelSpace 𝕜 (σ → 𝕜)) (I := I) Ω y hy
  unfold GeneratesAt at this ⊢
  rw [← this]
  congr 1
  ext m
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨e.symm k, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp⟩

end AnalyticGeometry
