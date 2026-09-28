/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.AffineVanishing
import SGA.Foundations.Cohomology.Modules
import SGA.Foundations.Cohomology.CechComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Serre's vanishing theorem on affine opens of arbitrary schemes

For any scheme `X`, any quasi-coherent `𝒪_X`-module `F` and any affine open `V ⊆ X`,
`Hᵖ(V, F) = 0` for `p > 0` (EGA III 1.3.1; Stacks Project, Tag 01XB). In particular the higher
cohomology of a quasi-coherent module on an affine scheme vanishes.

The proof applies Cartan's criterion (`TopCat.Sheaf.H'_subsingleton_of_cech`) on `X` itself, to
the basis of affine opens and the standard covers of an affine open `V` by `D(fᵢ)`,
`fᵢ ∈ Γ(X, V)`. The Čech complexes of `F` for standard covers are exact because the sections of
`F` over `D(a) ⊆ V` form the localization `Γ(F, V)_a` (EGA I 1.4.1, 1.3.7), which we deduce from
mathlib's description of quasi-coherent modules on `Spec Γ(X, V)` by restricting along
`IsAffineOpen.fromSpec`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_presheafInf_top`: `Γ(F, V) → Γ(F, D(c))` is
  a localization at `c ∈ Γ(X, V)` (stated for the presheaf `W ↦ Γ(F, W ⊓ V)` of
  `Γ(X, V)`-modules, `Scheme.Modules.presheafInf`).
* `AlgebraicGeometry.Scheme.Modules.cechComplex_exactAt_basicOpen`: exactness of Čech complexes
  of `F` for standard covers of affine opens (Stacks Tag 01X9).
* `AlgebraicGeometry.Scheme.Modules.H'_subsingleton_of_isAffineOpen`: Serre's vanishing theorem.
* `AlgebraicGeometry.Scheme.Modules.H_subsingleton_of_isAffine`: its global form on an affine
  scheme.
* `AlgebraicGeometry.Scheme.Modules.cechHomologyLinearEquiv`: Čech cohomology of a
  quasi-coherent module for a finite cover by affine opens with affine finite intersections
  computes its cohomology, `Γ(X, 𝒪_X)`-linearly (Stacks Tag 01XD; EGA III 1.4.1);
  `nonempty_cechHomologyIso_H` is the version for a cover of a scheme with affine diagonal.
* `AlgebraicGeometry.Scheme.Modules.cechComplex_exactAt_iff_subsingleton_H'`: on a scheme with
  affine diagonal (e.g. separated), for a finite cover of an open `W` by affine opens, the Čech
  complex of a quasi-coherent module is exact in degree `p ≥ 1` iff `Hᵖ(W, F) = 0` (Leray, Stacks
  Tag 01XD, vanishing form).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- Restricting a section `r ∈ Γ(X, V)` to `fromSpec(U)` corresponds, under `fromSpec`, to
restricting `r ∈ Γ(Spec Γ(X, V), ⊤)` to `U`. -/
lemma CohomologyAux.appIso_fromSpec_map (U : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ U ≤ V) (r : Γ(X, V)) :
    (hV.fromSpec.appIso U).hom (X.presheaf.map (homOfLE h).op r) =
      (Spec Γ(X, V)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X, V)).inv r) := by
  rw [Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality_assoc,
    IsAffineOpen.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

variable (F : X.Modules)

/-- The `Γ(X, V)`-module structure of the sections of `F|_{Spec Γ(X, V)}` (as a module over
`Spec Γ(X, V)`) is the one of `Γ(F, fromSpec(U))` through restriction
`Γ(X, V) → Γ(X, fromSpec U)`. -/
lemma CohomologyAux.restrictAppIso_smul (U : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ U ≤ V) (r : Γ(X, V)) (x : Γ(F.restrict hV.fromSpec, U)) :
    (F.restrictAppIso hV.fromSpec U).hom (r • x) =
      X.presheaf.map (homOfLE h).op r • (F.restrictAppIso hV.fromSpec U).hom x := by
  rw [Scheme.Modules.smul_Spec_def]
  refine (Scheme.Modules.smul_restrictAppIso_hom_apply hV.fromSpec F U _ x).trans ?_
  rw [← CohomologyAux.appIso_fromSpec_map hV U h r, Iso.hom_inv_id_apply]

lemma CohomologyAux.map_map_eq_map_map {T : TopCat.{u}}
    (P : TopCat.Presheaf AddCommGrpCat.{u} T)
    {U₁ U₂ U₃ U₂' : (TopologicalSpace.Opens T)ᵒᵖ} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₂')
    (d : U₂' ⟶ U₃) (s : P.obj U₁) : P.map b (P.map a s) = P.map d (P.map c s) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← ConcreteCategory.comp_apply, ← P.map_comp,
    Subsingleton.elim (a ≫ b) (c ≫ d)]

/-- A morphism of presheaves inducing bijections on Čech cochains transfers exactness of Čech
complexes. -/
lemma CohomologyAux.cechComplex_exactAt_of_bijective {T : TopCat.{u}} {ι : Type*}
    (U : ι → TopologicalSpace.Opens T) {P Q : TopCat.Presheaf AddCommGrpCat.{u} T} (φ : P ⟶ Q)
    (hφ : ∀ m, Function.Bijective (TopCat.Presheaf.cechCochainMap U φ m)) (p : ℕ)
    (h : (TopCat.Presheaf.cechComplex U Q).ExactAt (p + 1)) :
    (TopCat.Presheaf.cechComplex U P).ExactAt (p + 1) := by
  rw [TopCat.Presheaf.cechComplex_exactAt_succ_iff] at h ⊢
  intro c hc
  obtain ⟨b, hb⟩ := h (TopCat.Presheaf.cechCochainMap U φ (p + 1) c)
    (by rw [TopCat.Presheaf.cechD_cechCochainMap, hc, map_zero])
  obtain ⟨b', rfl⟩ := (hφ p).2 b
  refine ⟨b', (hφ (p + 1)).1 ?_⟩
  rw [← TopCat.Presheaf.cechD_cechCochainMap, hb]

lemma CohomologyAux.iInf_basicOpen_eq {X : Scheme.{u}} {V : X.Opens} {m : ℕ}
    (g : Fin (m + 1) → Γ(X, V)) :
    ⨅ a, X.basicOpen (g a) = X.basicOpen (∏ a, g a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : ⨅ a, X.basicOpen (g a) =
        X.basicOpen (g 0) ⊓ ⨅ a : Fin (m + 1), X.basicOpen (g a.succ) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a ↦ iInf_le _ a.succ))
        (le_iInf fun a ↦ Fin.cases inf_le_left (fun b ↦ inf_le_right.trans (iInf_le _ b)) a)
    rw [h, ih, ← Scheme.basicOpen_mul, ← Fin.prod_univ_succ]

namespace Scheme.Modules

variable (V)

/-- The functor `W ↦ W ⊓ V` on opens. -/
@[simps]
def _root_.AlgebraicGeometry.CohomologyAux.opensInfFunctor {T : Type*} [TopologicalSpace T]
    (V : TopologicalSpace.Opens T) : TopologicalSpace.Opens T ⥤ TopologicalSpace.Opens T where
  obj W := W ⊓ V
  map h := homOfLE (inf_le_inf_right V h.le)

/-- The presheaf `W ↦ Γ(F, W ⊓ V)`; its sections are `Γ(X, V)`-modules. -/
noncomputable def presheafInf : TopCat.Presheaf AddCommGrpCat.{u} X :=
  (CohomologyAux.opensInfFunctor V).op ⋙ F.presheaf

noncomputable instance (W : X.Opens) : Module Γ(X, V) ((F.presheafInf V).obj (op W)) :=
  letI : Module Γ(X, W ⊓ V) ((F.presheafInf V).obj (op W)) :=
    inferInstanceAs (Module Γ(X, W ⊓ V) Γ(F, W ⊓ V))
  Module.compHom _ (X.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom

lemma presheafInf_map_smul ⦃W W' : X.Opens⦄ (h : W' ≤ W) (r : Γ(X, V))
    (s : (F.presheafInf V).obj (op W)) :
    (F.presheafInf V).map (homOfLE h).op (r • s) = r • (F.presheafInf V).map (homOfLE h).op s := by
  let s' : Γ(F, W ⊓ V) := s
  change F.presheaf.map (homOfLE (inf_le_inf_right V h)).op
      (X.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op r • s') =
    X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op r •
      F.presheaf.map (homOfLE (inf_le_inf_right V h)).op s'
  rw [map_smul, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- The restriction `F(W) → F(W ⊓ V)`, a morphism of presheaves `F ⟶ presheafInf F V`. -/
noncomputable def toPresheafInf : F.presheaf ⟶ F.presheafInf V where
  app W := F.presheaf.map (homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op
  naturality _ _ _ := (F.presheaf.map_comp _ _).symm.trans
    ((congrArg F.presheaf.map (Subsingleton.elim _ _)).trans (F.presheaf.map_comp _ _))

variable {V}

lemma _root_.AlgebraicGeometry.CohomologyAux.image_fromSpec_le (U : (Spec Γ(X, V)).Opens) :
    hV.fromSpec ''ᵁ U ≤ V :=
  (Scheme.Hom.image_mono _ le_top).trans
    ((Scheme.Hom.image_top_eq_opensRange _).le.trans hV.opensRange_fromSpec.le)

/-- The identification of the sections of `F|_{Spec Γ(X, V)}` over `U` with the sections of
`presheafInf F V` over `W`, when `W ⊓ V ≤ fromSpec(U)`, as a `Γ(X, V)`-linear map. -/
noncomputable def restrictFromSpecₗ (U : (Spec Γ(X, V)).Opens) (W : X.Opens)
    (hW : W ⊓ V ≤ hV.fromSpec ''ᵁ U) :
    Γ(F.restrict hV.fromSpec, U) →ₗ[Γ(X, V)] (F.presheafInf V).obj (op W) where
  toFun x := F.presheaf.map (homOfLE hW).op ((F.restrictAppIso hV.fromSpec U).hom x)
  map_add' x y := by simp only [map_add]; rfl
  map_smul' r x := by
    rw [CohomologyAux.restrictAppIso_smul hV F U (CohomologyAux.image_fromSpec_le hV U), map_smul,
      ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl

lemma bijective_restrictFromSpecₗ (U : (Spec Γ(X, V)).Opens) (W : X.Opens)
    (hW : W ⊓ V = hV.fromSpec ''ᵁ U) :
    Function.Bijective (F.restrictFromSpecₗ hV U W hW.le) := by
  have : IsIso (homOfLE hW.le).op := ⟨(homOfLE hW.ge).op, Subsingleton.elim _ _,
    Subsingleton.elim _ _⟩
  exact (ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE hW.le).op)).comp
    (ConcreteCategory.bijective_of_isIso (F.restrictAppIso hV.fromSpec U).hom)

/-- For a quasi-coherent `F` and an affine open `V`, the restriction `Γ(F, V) → Γ(F, D(c))` is a
localization at `c ∈ Γ(X, V)` (EGA I 1.4.1, 1.3.7). Stated for the presheaf
`W ↦ Γ(F, W ⊓ V)` of `Γ(X, V)`-modules. -/
theorem isLocalizedModule_presheafInf_top (hV : IsAffineOpen V) [F.IsQuasicoherent] (c : Γ(X, V))
    {W : X.Opens} (hW : W ⊓ V = X.basicOpen c) :
    IsLocalizedModule.Away c (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : W ≤ ⊤)) := by
  let G := F.restrict hV.fromSpec
  have hG : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing G).mp inferInstance
  have h₁ : ⊤ ⊓ V = hV.fromSpec ''ᵁ ⊤ := by
    rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  have h₂ : W ⊓ V = hV.fromSpec ''ᵁ basicOpen' c := by
    rw [hV.fromSpec_image_basicOpen, hW]
  have comm : TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : W ≤ ⊤) ∘ₗ F.restrictFromSpecₗ hV ⊤ ⊤ h₁.le =
      F.restrictFromSpecₗ hV (basicOpen' c) W h₂.le ∘ₗ
        ((modulesSpecToSheaf.obj G).obj.map (basicOpen' c).leTop.op).hom := by
    ext x
    exact CohomologyAux.map_map_eq_map_map F.presheaf _ _ _ _ _
  change IsLocalizedModule (Submonoid.powers c) _
  refine (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers c)
    (F.restrictFromSpecₗ hV ⊤ ⊤ h₁.le)
    (F.bijective_restrictFromSpecₗ hV ⊤ ⊤ h₁)).mp ?_
  rw [comm]
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers c)
      (F.restrictFromSpecₗ hV (basicOpen' c) W h₂.le)
      (F.bijective_restrictFromSpecₗ hV (basicOpen' c) W h₂)).mpr
    (hG c)

/-- **Converse of `isLocalizedModule_presheafInf_top`** (EGA I 1.4.1): if the restrictions
`Γ(V, F) → Γ(D(c), F)` are localizations for all `c ∈ Γ(X, V)`, `V` affine, then `F` is
quasi-coherent on `V` (its restriction along `Spec Γ(X, V) ≅ V` is quasi-coherent). -/
theorem isQuasicoherent_restrict_fromSpec_of_isLocalizedModule (hV : IsAffineOpen V)
    (hloc : ∀ c : Γ(X, V), IsLocalizedModule.Away c
      (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤))) :
    (F.restrict hV.fromSpec).IsQuasicoherent := by
  let G := F.restrict hV.fromSpec
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  intro c
  have hW : X.basicOpen c ⊓ V = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  have h₁ : ⊤ ⊓ V = hV.fromSpec ''ᵁ ⊤ := by
    rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  have h₂ : X.basicOpen c ⊓ V = hV.fromSpec ''ᵁ basicOpen' c := by
    rw [hV.fromSpec_image_basicOpen, hW]
  have comm : TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : X.basicOpen c ≤ ⊤) ∘ₗ F.restrictFromSpecₗ hV ⊤ ⊤ h₁.le =
      F.restrictFromSpecₗ hV (basicOpen' c) (X.basicOpen c) h₂.le ∘ₗ
        ((modulesSpecToSheaf.obj G).obj.map (basicOpen' c).leTop.op).hom := by
    ext x
    exact CohomologyAux.map_map_eq_map_map F.presheaf _ _ _ _ _
  have h := (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers c)
    (F.restrictFromSpecₗ hV ⊤ ⊤ h₁.le)
    (F.bijective_restrictFromSpecₗ hV ⊤ ⊤ h₁)).mpr (hloc c)
  rw [comm] at h
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers c)
    (F.restrictFromSpecₗ hV (basicOpen' c) (X.basicOpen c) h₂.le)
    (F.bijective_restrictFromSpecₗ hV (basicOpen' c) (X.basicOpen c) h₂)).mp h

/-- For a quasi-coherent `F`, an affine open `V` and `a, b ∈ Γ(X, V)`, the restriction
`Γ(F, D(a)) → Γ(F, D(ab))` is a localization at `b` (the opens being given up to intersection
with `V`). -/
theorem isLocalizedModule_presheafInf (hV : IsAffineOpen V) [F.IsQuasicoherent] (a b : Γ(X, V))
    {W₁ W₂ : X.Opens} (h₁ : W₁ ⊓ V = X.basicOpen a) (h₂ : W₂ ⊓ V = X.basicOpen (a * b))
    (h : W₂ ≤ W₁) :
    IsLocalizedModule.Away b
      (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V) h) := by
  have := F.isLocalizedModule_presheafInf_top hV a h₁
  have := F.isLocalizedModule_presheafInf_top hV (a * b) h₂
  exact IsLocalizedModule.Away.of_comp a b
    (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V) (le_top : W₁ ≤ ⊤))
    (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V) (le_top : W₂ ≤ ⊤)) _
    fun m ↦ TopCat.Presheaf.map_map_apply _ _ _ m

lemma cechOpen_basicOpen {n m : ℕ} (f : Fin n → Γ(X, V)) (y : Fin (m + 1) → Fin n) :
    TopCat.Presheaf.cechOpen (fun i ↦ X.basicOpen (f i)) y = X.basicOpen (∏ a, f (y a)) :=
  CohomologyAux.iInf_basicOpen_eq (fun a ↦ f (y a))

lemma cechOpen_cons_basicOpen {n m : ℕ} (f : Fin n → Γ(X, V)) (k : Fin n)
    (y : Fin (m + 1) → Fin n) :
    TopCat.Presheaf.cechOpen (fun i ↦ X.basicOpen (f i)) (Fin.cons k y : Fin (m + 2) → Fin n) =
      X.basicOpen ((∏ a, f (y a)) * f k) := by
  rw [cechOpen_basicOpen, Fin.prod_univ_succ, mul_comm]
  rfl

/-- **Exactness of the Čech complex of a quasi-coherent module for a standard cover of an affine
open** (Stacks Tag 01X9): if `V` is affine and `f₁, …, fₙ ∈ Γ(X, V)` generate the unit ideal, the
Čech complex of `F` for the cover of `V` by the `D(fᵢ)` is exact in positive degrees. -/
theorem cechComplex_exactAt_basicOpen (hV : IsAffineOpen V) [F.IsQuasicoherent] {n : ℕ}
    (f : Fin n → Γ(X, V)) (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    (TopCat.Presheaf.cechComplex (fun i ↦ X.basicOpen (f i)) F.presheaf).ExactAt (p + 1) := by
  let U : Fin n → X.Opens := fun i ↦ X.basicOpen (f i)
  have hUV {m : ℕ} (x : Fin (m + 1) → Fin n) : TopCat.Presheaf.cechOpen U x ≤ V :=
    (TopCat.Presheaf.cechOpen_le U x 0).trans (X.basicOpen_le _)
  refine CohomologyAux.cechComplex_exactAt_of_bijective U (F.toPresheafInf V) (fun m ↦ ?_) p ?_
  · refine ⟨fun c c' h ↦ funext fun x ↦ ?_, fun c ↦ ?_⟩
    · have : IsIso (homOfLE (inf_le_left : TopCat.Presheaf.cechOpen U x ⊓ V ≤ _)).op :=
        ⟨(homOfLE (le_inf le_rfl (hUV x))).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      exact (ConcreteCategory.bijective_of_isIso (F.presheaf.map
        (homOfLE (inf_le_left : TopCat.Presheaf.cechOpen U x ⊓ V ≤ _)).op)).1 (congrFun h x)
    · choose c' hc' using fun x : Fin (m + 1) → Fin n ↦
        have : IsIso (homOfLE (inf_le_left : TopCat.Presheaf.cechOpen U x ⊓ V ≤ _)).op :=
          ⟨(homOfLE (le_inf le_rfl (hUV x))).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
        (ConcreteCategory.bijective_of_isIso (F.presheaf.map
          (homOfLE (inf_le_left : TopCat.Presheaf.cechOpen U x ⊓ V ≤ _)).op)).2 (c x)
      exact ⟨c', funext hc'⟩
  · refine TopCat.Presheaf.cechComplex_exactAt_of_isLocalizedModule (F.presheafInf_map_smul V) U f 1
      (by rw [hf]; exact Ideal.le_radical Submodule.mem_top)
      (fun x ↦ by rw [map_one]; exact isUnit_one) (fun k y ↦ ?_) p
    exact F.isLocalizedModule_presheafInf hV _ (f k)
      ((congrArg (· ⊓ V) (cechOpen_basicOpen f y)).trans (inf_eq_left.mpr (X.basicOpen_le _)))
      ((congrArg (· ⊓ V) (cechOpen_cons_basicOpen f k y)).trans
        (inf_eq_left.mpr (X.basicOpen_le _)))
      _

variable (X) in
/-- Finite covers of an affine open `V` by standard opens `D(fᵢ)`, `fᵢ ∈ Γ(X, V)` generating the
unit ideal. -/
def IsStandardAffineCover ⦃n : ℕ⦄ (U : Fin n → X.Opens) : Prop :=
  ∃ (V : X.Opens) (_ : IsAffineOpen V) (f : Fin n → Γ(X, V)),
    Ideal.span (Set.range f) = ⊤ ∧ ∀ i, U i = X.basicOpen (f i)

variable (X) in
/-- Every open cover of an affine open `V` is refined by a standard cover of `V`. -/
lemma exists_isStandardAffineCover_refinement (V : X.Opens) (hV : IsAffineOpen V)
    (W : V → X.Opens) (hW : ∀ x, x.1 ∈ W x) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), IsStandardAffineCover X U ∧ ⨆ i, U i = V ∧
      ∀ i, ∃ x, U i ≤ W x := by
  choose f hfW hxf using fun x : V ↦ hV.exists_basicOpen_le (V := W x) ⟨x.1, hW x⟩ x.2
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V ↦ (X.basicOpen (f x) : Set X))
    (fun x ↦ (X.basicOpen (f x)).2) fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxf ⟨y, hy⟩⟩
  let e := t.equivFin.symm
  have hsup : ⨆ i, X.basicOpen (f (e i)) = V := by
    refine le_antisymm (iSup_le fun i ↦ X.basicOpen_le _) fun y hy ↦ ?_
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hyx
  refine ⟨t.card, fun i ↦ X.basicOpen (f (e i)), ⟨V, hV, fun i ↦ f (e i), ?_, fun _ ↦ rfl⟩, hsup,
    fun i ↦ ⟨e i, hfW _⟩⟩
  rw [← hV.iSup_basicOpen_eq_self_iff, iSup_range' (fun g ↦ X.basicOpen g)]
  exact hsup

/-- **Serre's vanishing theorem** (EGA III 1.3.1; Stacks Tag 01XB): for a quasi-coherent
`𝒪_X`-module `F` on any scheme `X` and an affine open `V ⊆ X`, `Hᵖ(V, F) = 0` for `p > 0`. -/
theorem H'_subsingleton_of_isAffineOpen [F.IsQuasicoherent] (hV : IsAffineOpen V) (p : ℕ) :
    Subsingleton (F.toAbSheaf.H' (p + 1) V) := by
  have hCov : ∀ ⦃n⦄ (U : Fin n → X.Opens), IsStandardAffineCover X U →
      ∀ ⦃p⦄ (x : Fin (p + 1) → Fin n), TopCat.Presheaf.cechOpen U x ∈ {V | IsAffineOpen V} := by
    rintro n U ⟨V', hV', f, -, hUf⟩ p x
    obtain rfl : U = fun i ↦ X.basicOpen (f i) := funext hUf
    rw [Set.mem_ofPred_eq, cechOpen_basicOpen]
    exact hV'.basicOpen _
  have hF : TopCat.Sheaf.CechAcyclic (X := X.carrier) (IsStandardAffineCover X) F.toAbSheaf := by
    rintro n U ⟨V', hV', f, hf, hUf⟩ p
    obtain rfl : U = fun i ↦ X.basicOpen (f i) := funext hUf
    exact F.cechComplex_exactAt_basicOpen hV' f hf p
  exact TopCat.Sheaf.H'_subsingleton_of_cech (X := X.carrier) hCov
    (fun V hV ↦ exists_isStandardAffineCover_refinement X V hV) p _ hF hV

/-- **Serre's vanishing theorem** for affine schemes (EGA III 1.3.1; Stacks Tag 01XB;
Hartshorne III.3.5 in the noetherian case): `Hᵖ(X, F) = 0` for `p > 0`, `X` affine and `F`
quasi-coherent. -/
theorem H_subsingleton_of_isAffine [IsAffine X] [F.IsQuasicoherent] (p : ℕ) :
    Subsingleton (F.H (p + 1)) :=
  F.H'_subsingleton_of_isAffineOpen (isAffineOpen_top X) p

lemma isAffineOpen_cechOpen [IsAffineHom (pullback.diagonal (terminal.from X))] {n : ℕ}
    {U : Fin n → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) :
    ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x)
  | 0, x => by
    rw [show TopCat.Presheaf.cechOpen U x = U (x 0) from
      le_antisymm (TopCat.Presheaf.cechOpen_le U x 0)
        (le_iInf fun a ↦ by rw [Fin.fin_one_eq_zero a])]
    exact hU _
  | m + 1, x => by
    rw [← Fin.cons_self_tail x, TopCat.Presheaf.cechOpen_cons_eq]
    exact (hU _).inf (isAffineOpen_cechOpen hU _)

/-- **Leray's theorem for quasi-coherent sheaves, vanishing form** (Stacks Tag 01XD; EGA III
1.4.1): on a scheme with affine diagonal (e.g. a separated scheme), let `U₁, …, Uₙ` be affine
opens with union `W` and `F` quasi-coherent. For every `p ≥ 1`, the Čech complex of `F` for
`(Uᵢ)` is exact in degree `p` if and only if `Hᵖ(W, F) = 0`. (The isomorphism
`Ȟᵖ(U, F) ≅ Hᵖ(W, F)` is `Scheme.Modules.nonempty_cechHomologyIso`.) -/
theorem cechComplex_exactAt_iff_subsingleton_H' [IsAffineHom (pullback.diagonal (terminal.from X))]
    [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (p : ℕ) :
    (TopCat.Presheaf.cechComplex U F.presheaf).ExactAt (p + 1) ↔
      Subsingleton (F.toAbSheaf.H' (p + 1) (⨆ i, U i)) :=
  TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H' (X := X.carrier) U p F.toAbSheaf
    fun x q ↦ F.H'_subsingleton_of_isAffineOpen (isAffineOpen_cechOpen hU x) q

/-- **Čech cohomology of quasi-coherent modules** (Stacks Tag 01XD; EGA III 1.4.1; Hartshorne
III.4.5): let `U₁, …, Uₙ` be affine opens of a scheme `X` all of whose finite intersections are
affine, `W = ⋃ Uᵢ`, and `F` quasi-coherent. Then `Ȟᵖ(U, F) ≅ Hᵖ(W, F)` for all `p`. See
`cechHomologyLinearEquiv` for the `Γ(X, 𝒪_X)`-linear version. -/
theorem nonempty_cechHomologyIso [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (p : ℕ) :
    Nonempty ((TopCat.Presheaf.cechComplex U F.presheaf).homology p ≅
      F.toAbSheaf.H' p (⨆ i, U i)) :=
  TopCat.Sheaf.nonempty_cechHomologyIso (X := X.carrier) (U := U) p F.toAbSheaf
    fun x q ↦ F.H'_subsingleton_of_isAffineOpen (hU x) q

/-- **Čech cohomology of quasi-coherent modules on schemes with affine diagonal** (e.g. separated
schemes; Stacks Tag 01XD; Hartshorne III.4.5): for affine opens `U₁, …, Uₙ` covering `X` and `F`
quasi-coherent, `Ȟᵖ(U, F) ≅ Hᵖ(X, F)`. -/
theorem nonempty_cechHomologyIso_H [IsAffineHom (pullback.diagonal (terminal.from X))]
    [F.IsQuasicoherent] {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (p : ℕ) :
    Nonempty ((TopCat.Presheaf.cechComplex U F.presheaf).homology p ≅
      AddCommGrpCat.of (F.H p)) := by
  obtain ⟨e⟩ := F.nonempty_cechHomologyIso U (isAffineOpen_cechOpen hU) p
  rw [hcov] at e
  exact ⟨e⟩

section Linear

variable {n : ℕ} (U : Fin n → X.Opens) (p : ℕ)

lemma cechComplexMap_add {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ ψ : P ⟶ Q) :
    TopCat.Presheaf.cechComplexMap U (φ + ψ) =
      TopCat.Presheaf.cechComplexMap U φ + TopCat.Presheaf.cechComplexMap U ψ := by
  ext m : 1
  exact AddCommGrpCat.ext fun c ↦ rfl

lemma cechComplexMap_zero {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} :
    TopCat.Presheaf.cechComplexMap U (0 : P ⟶ Q) = 0 := by
  ext m : 1
  exact AddCommGrpCat.ext fun c ↦ rfl

/-- The action of `Γ(X, 𝒪_X)` on the Čech cohomology `Ȟᵖ(U, F)` of an `𝒪_X`-module. -/
noncomputable def cechSMulRingHom :
    Γ(X, ⊤) →+* AddMonoid.End ((TopCat.Presheaf.cechComplex U F.presheaf).homology p) where
  toFun r :=
    (HomologicalComplex.homologyMap (TopCat.Presheaf.cechComplexMap U (F.smulHom r).hom) p).hom
  map_one' := by
    rw [smulHom_one]
    change (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplexFunctor U).map
      (𝟙 _)) p).hom = _
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    rfl
  map_mul' r s := by
    rw [smulHom_mul]
    change (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplexFunctor U).map
      ((F.smulHom s).hom ≫ (F.smulHom r).hom)) p).hom = _
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp]
    rfl
  map_zero' := by
    rw [smulHom_zero]
    change (HomologicalComplex.homologyMap (TopCat.Presheaf.cechComplexMap U 0) p).hom = _
    rw [cechComplexMap_zero, HomologicalComplex.homologyMap_zero]
    rfl
  map_add' r s := by
    rw [smulHom_add]
    change (HomologicalComplex.homologyMap
      (TopCat.Presheaf.cechComplexMap U ((F.smulHom r).hom + (F.smulHom s).hom)) p).hom = _
    rw [cechComplexMap_add, HomologicalComplex.homologyMap_add]
    rfl

noncomputable instance : Module Γ(X, ⊤) ((TopCat.Presheaf.cechComplex U F.presheaf).homology p) :=
  Module.compHom _ (F.cechSMulRingHom U p)

/-- **Čech cohomology of quasi-coherent modules, linear form** (Stacks Tag 01XD; EGA III 1.4.1):
for affine opens `U₁, …, Uₙ` all of whose finite intersections are affine and `F` quasi-coherent,
`Ȟᵖ(U, F) ≅ Hᵖ(⋃ Uᵢ, F)` as `Γ(X, 𝒪_X)`-modules. -/
noncomputable def cechHomologyLinearEquiv [F.IsQuasicoherent]
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x)) :
    (TopCat.Presheaf.cechComplex U F.presheaf).homology p ≃ₗ[Γ(X, ⊤)] F.H' p (⨆ i, U i) :=
  let hL : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) U F.toAbSheaf :=
    ⟨fun x q ↦ F.H'_subsingleton_of_isAffineOpen (hU x) q⟩
  let e := TopCat.Sheaf.cechHomologyIso p F.toAbSheaf hL
  { e.addCommGroupIsoToAddEquiv with
    map_smul' := fun r x ↦ by
      have h := congrArg
        (fun (f : (TopCat.Presheaf.cechComplex U F.toAbSheaf.obj).homology p ⟶
          F.toAbSheaf.H' p (⨆ i, U i)) ↦ f x)
        (TopCat.Sheaf.cechHomologyIso_naturality p hL hL (F.smulHom r))
      exact h }

end Linear

end Scheme.Modules

end AlgebraicGeometry
