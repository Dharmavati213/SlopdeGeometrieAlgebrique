/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Finite étale schemes over a limit of schemes

Let `c.pt = lim Eᵢ` be the limit of a cofiltered diagram of quasi-compact and quasi-separated
schemes with affine transition maps. We prove that the functor `colimᵢ FEt(Eᵢ) ⟶ FEt(c.pt)` is an
equivalence (EGA IV 8.8.2, 8.10.5, 17.7.8; Stacks 01ZC, 01ZM, 07RP), in the following form:

* objects: every finite étale `c.pt`-scheme `Y` is the base change `c.pt ×_{Eⱼ} Yⱼ` of a finite
  étale `Eⱼ`-scheme `Yⱼ` for some `j`
  (`AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale`);
* morphisms: for `X₁ ⟶ Eⱼ` quasi-compact and quasi-separated and `X₂ ⟶ Eⱼ` locally of finite
  presentation, every `Eⱼ`-morphism `X₁ ×_{Eⱼ} c.pt ⟶ X₂` comes from some `X₁ ×_{Eⱼ} Eₖ`
  (`Scheme.exists_hom_of_isPullback`, deduced from mathlib's
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), uniquely after refining
  (`Scheme.exists_map_comp_eq_of_isPullback`); isomorphisms descend
  (`Scheme.exists_iso_of_isPullback`).

The affine case is commutative algebra: a finite étale `R`-algebra, `R = colim Rⱼ`, is the base
change of a finite étale algebra over a subring of finite type over `ℤ`
(`Algebra.exists_subalgebra_fg_of_etale_of_finite`, from mathlib's noetherian approximation of
étale algebras), hence over some `Rⱼ` (`CommRingCat.exists_finite_etale_isPushout_of_isColimit`).
The general case is by induction on the number of affine opens covering some `Eᵢ`: the
descended pieces over `V` and `W` become isomorphic over `V ∩ W` at some level, and are glued as
a pushout along open immersions (`Scheme.exists_isPullback_of_sup_eq_top`); the comparison with
`Y` is checked over the two opens (`Scheme.exists_isPullback_of_sup_eq_top'`).
-/

universe u

open CategoryTheory Limits TensorProduct

section Algebra

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2, 8.10.5, 17.7.8 (noetherian approximation of finite étale algebras): a finite
étale `R`-algebra `B` is `R ⊗_{A₀} B₀` for a subring `A₀ ⊆ R` of finite type over `ℤ` and a finite
étale `A₀`-algebra `B₀`. -/
theorem Algebra.exists_subalgebra_fg_of_etale_of_finite {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.Etale R B] [Module.Finite R B] :
    ∃ (A₀ : Subalgebra ℤ R) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Algebra.Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧ Nonempty (B ≃ₐ[R] R ⊗[A₀] B₀) := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R B
  -- generators of `B₀` and integral equations of their images in `B`
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A₀ B₀).FG)
  have hint (b : B₀) : IsIntegral R (e.symm (1 ⊗ₜ b)) := Algebra.IsIntegral.isIntegral _
  choose p hpm hp using hint
  -- enlarge `A₀` by the coefficients of these equations
  let A₁ : Subalgebra ℤ R := A₀ ⊔ Algebra.adjoin ℤ ↑(s.biUnion fun b ↦ (p b).coeffs)
  have hA₁ : A₁.FG := hA₀.sup (Subalgebra.fg_adjoin_finset _)
  have hA₀₁ : A₀ ≤ A₁ := le_sup_left
  let : Algebra A₀ A₁ := (Subalgebra.inclusion hA₀₁).toAlgebra
  have : IsScalarTower A₀ A₁ R := .of_algebraMap_eq fun _ ↦ rfl
  let B₁ := A₁ ⊗[A₀] B₀
  let e₁ : R ⊗[A₁] B₁ ≃ₐ[R] R ⊗[A₀] B₀ := Algebra.TensorProduct.cancelBaseChange A₀ A₁ R R B₀
  refine ⟨A₁, B₁, inferInstance, inferInstance, hA₁, inferInstance, ?_, ⟨e.trans e₁.symm⟩⟩
  -- `B₁` is generated over `A₁` by the `1 ⊗ b`, `b ∈ s`, which are integral
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] R ⊗[A₁] B₁) :=
    Algebra.TensorProduct.includeRight_injective Subtype.val_injective
  have hb (b : B₀) (hb : b ∈ s) : IsIntegral A₁ ((1 : A₁) ⊗ₜ[A₀] b : B₁) := by
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := algebraMap A₁ R) ((Polynomial.lifts_iff_coeff_lifts _).mpr fun n ↦ by
        by_cases hn : (p b).coeff n = 0
        · exact ⟨0, by rw [map_zero, hn]⟩
        · refine ⟨⟨_, (le_sup_right : _ ≤ A₁) (Algebra.subset_adjoin ?_)⟩, rfl⟩
          exact Finset.mem_biUnion.mpr ⟨b, hb, Polynomial.coeff_mem_coeffs hn⟩) (hpm b)
    refine ⟨q, hqm, hinj ?_⟩
    rw [map_zero, ← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply,
      ← Polynomial.aeval_map_algebraMap R, hq]
    apply (e.trans e₁.symm).symm.injective
    have hx : (e.trans e₁.symm).symm (Algebra.TensorProduct.includeRight ((1 : A₁) ⊗ₜ[A₀] b)) =
        e.symm (1 ⊗ₜ b) := by
      change e.symm (e₁ ((1 : R) ⊗ₜ[A₁] ((1 : A₁) ⊗ₜ[A₀] b))) = _
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact (congrArg (Polynomial.aeval · (p b)) hx).trans ((Polynomial.aeval_def _ _).trans (hp b))
  have hadj : Algebra.adjoin A₁ ((fun b ↦ ((1 : A₁) ⊗ₜ[A₀] b : B₁)) '' ↑s) = ⊤ := by
    set T := Algebra.adjoin A₁ ((fun b ↦ ((1 : A₁) ⊗ₜ[A₀] b : B₁)) '' ↑s) with hT
    have h1 (b : B₀) : ((1 : A₁) ⊗ₜ[A₀] b : B₁) ∈ T := by
      have hb : b ∈ Algebra.adjoin A₀ (↑s : Set B₀) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
      | algebraMap r =>
        have : ((1 : A₁) ⊗ₜ[A₀] algebraMap A₀ B₀ r : B₁) =
            algebraMap A₁ B₁ (algebraMap A₀ A₁ r) := by
          rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.algebraMap_apply]
          rfl
        rw [this]
        exact T.algebraMap_mem _
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | mul x y _ _ hx hy =>
        convert mul_mem hx hy using 1
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    clear_value T
    refine eq_top_iff.mpr fun x ↦ ?_
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem T
    | add x y hx hy => exact add_mem hx hy
    | tmul a b =>
      have : (a ⊗ₜ[A₀] b : B₁) = algebraMap A₁ B₁ a * ((1 : A₁) ⊗ₜ[A₀] b) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
        rfl
      rw [this]
      exact mul_mem (T.algebraMap_mem a) (h1 b)
  have : Algebra.IsIntegral A₁ B₁ := ⟨fun x ↦ by
    have hx : x ∈ Algebra.adjoin A₁ ((fun b ↦ ((1 : A₁) ⊗ₜ[A₀] b : B₁)) '' ↑s) := hadj ▸ trivial
    exact (Algebra.adjoin_le (S := integralClosure A₁ B₁)
      (by rintro _ ⟨b, hb', rfl⟩; exact hb b hb')) hx⟩
  exact Algebra.IsIntegral.finite

end Algebra

namespace CommRingCat

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2, 8.10.5, 17.7.8: let `R = colim Rⱼ` be a filtered colimit of commutative rings and
`φ : R ⟶ B` finite étale. Then there are `j`, a finite étale `Rⱼ ⟶ Bⱼ` and `ψ : Bⱼ ⟶ B` such that
the square `Rⱼ ⟶ R, Rⱼ ⟶ Bⱼ, R ⟶ B, Bⱼ ⟶ B` is a pushout, i.e. `B ≅ R ⊗_{Rⱼ} Bⱼ`. -/
@[stacks 07RP]
theorem exists_finite_etale_isPushout_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) {B : CommRingCat.{u}}
    (φ : c.pt ⟶ B) (hφ : φ.hom.Etale) (hφ' : φ.hom.Finite) :
    ∃ (j : J) (Bj : CommRingCat.{u}) (φj : F.obj j ⟶ Bj) (ψ : Bj ⟶ B),
      φj.hom.Etale ∧ φj.hom.Finite ∧ IsPushout (c.ι.app j) φj φ ψ := by
  algebraize [φ.hom]
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, hB₀', ⟨e⟩⟩ :=
    Algebra.exists_subalgebra_fg_of_etale_of_finite (R := c.pt) (B := B)
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp this
  -- `A₀ ⟶ R` factors through some `Rⱼ`
  let Z : CommRingCat.{u} := .of (ULift.{u} ℤ)
  let f : Z ⟶ .of A₀ := ofHom ((algebraMap ℤ A₀).comp ULift.ringEquiv.toRingHom)
  have hf : f.hom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr ‹_›).comp
      (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective)
  let α : (Functor.const J).obj Z ⟶ F :=
    { app j := ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
      naturality j j' g := by ext; simp }
  obtain ⟨j, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit Z F α f c
    hc hf (ofHom A₀.val) (fun i ↦ by ext; simp [f, α])
  let : Algebra A₀ (F.obj j) := g'.hom.toAlgebra
  have hι (r : A₀) : c.ι.app j (algebraMap A₀ (F.obj j) r) = algebraMap A₀ c.pt r :=
    (congrArg (fun φ ↦ φ.hom r) hg').symm
  let ιj : F.obj j →ₐ[A₀] c.pt := { (c.ι.app j).hom with commutes' := hι }
  let m : F.obj j ⊗[A₀] B₀ →ₐ[A₀] c.pt ⊗[A₀] B₀ :=
    Algebra.TensorProduct.map ιj (AlgHom.id A₀ B₀)
  refine ⟨j, .of (F.obj j ⊗[A₀] B₀), ofHom (algebraMap (F.obj j) (F.obj j ⊗[A₀] B₀)),
    ofHom (e.symm.toRingHom.comp m.toRingHom),
    RingHom.etale_algebraMap.mpr inferInstance, RingHom.finite_algebraMap.mpr inferInstance, ?_⟩
  have t := CommRingCat.isPushout_tensorProduct A₀ (F.obj j) B₀
  have s := CommRingCat.isPushout_tensorProduct A₀ c.pt B₀
  have s' : IsPushout (ofHom (algebraMap A₀ (F.obj j)) ≫ c.ι.app j) (ofHom (algebraMap A₀ B₀))
      (ofHom (S := c.pt ⊗[A₀] B₀) Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := F.obj j ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom) := by
    have e₁ : ofHom (algebraMap A₀ (F.obj j)) ≫ c.ι.app j = ofHom (algebraMap A₀ c.pt) := by
      ext r
      exact hι r
    have e₂ : ofHom (S := F.obj j ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom =
          ofHom (S := c.pt ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom := by
      ext b
      simp [m]
    rw [e₁, e₂]
    exact s
  have r := IsPushout.of_left s' (by ext x; simp [m, ιj]) t
  refine r.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso
    (by simp) (by simp; rfl) ?_ (by simp)
  ext x
  have hx : (x ⊗ₜ[A₀] (1 : B₀) : c.pt ⊗[A₀] B₀) = algebraMap c.pt (c.pt ⊗[A₀] B₀) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  simp only [Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
    hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  change e.symm (x ⊗ₜ[A₀] (1 : B₀)) = φ.hom x
  rw [hx, AlgEquiv.commutes]
  rfl

end CommRingCat

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2, 17.7.8 (affine case): over the limit of a cofiltered diagram of affine schemes
with affine transition maps, every finite étale scheme is the base change of a finite étale scheme
over some member of the diagram. -/
theorem Scheme.exists_isPullback_of_isLimit_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, IsAffine (E.obj i)] (hc : IsLimit c)
    {Y : Scheme.{u}} (q : Y ⟶ c.pt) [IsFinite q] [Etale q] :
    ∃ (j : I) (Yj : Scheme.{u}) (qj : Yj ⟶ E.obj j) (e : Y ⟶ Yj),
      IsFinite qj ∧ Etale qj ∧ IsPullback e q qj (c.π.app j) := by
  have hΓ := (nonempty_isColimit_Γ_mapCocone E c hc).some
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffine Y := isAffine_of_isAffineHom q
  let φ : Γ(c.pt, ⊤) ⟶ Γ(Y, ⊤) := q.appTop
  have hφ : φ.hom.Etale := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹_›
  have hφ' : φ.hom.Finite := q.finite_appTop
  obtain ⟨j, Bj, φj, ψ, hφj, hφj', H⟩ :=
    CommRingCat.exists_finite_etale_isPushout_of_isColimit hΓ φ hφ hφ'
  have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ H
  have : Etale (Spec.map φj) := HasRingHomProperty.Spec_iff.mpr hφj
  have : IsFinite (Spec.map φj) := (IsFinite.SpecMap_iff _).mpr hφj'
  refine ⟨j.unop, Spec Bj, Spec.map φj ≫ (E.obj j.unop).isoSpec.inv, Y.isoSpec.hom ≫ Spec.map ψ,
    inferInstance, inferInstance, ?_⟩
  refine hSpec.flip.of_iso Y.isoSpec.symm (Iso.refl _) c.pt.isoSpec.symm
    (E.obj j.unop).isoSpec.symm (by simp) ?_ (by simp) ?_
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality q
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality (X := c.pt) (c.π.app j.unop)

section BaseChange

set_option backward.isDefEq.respectTransparency false in
variable (E) in
/-- For `p : X ⟶ E.obj j`, the diagram `k ↦ X ×_{E j} E k` over `Over j`. -/
@[simps]
noncomputable def Scheme.baseChangeDiagram {j : I} {X : Scheme.{u}} (p : X ⟶ E.obj j) :
    Over j ⥤ Scheme.{u} where
  obj k := pullback p (E.map k.hom)
  map {k k'} g := pullback.map p (E.map k.hom) p (E.map k'.hom) (𝟙 X) (E.map g.left) (𝟙 _)
    (by simp) (by rw [Category.comp_id, ← E.map_comp, Over.w g])
  map_id k := by
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp g g' := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Over.comp_left, Functor.map_comp, Category.comp_id, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The projections `X ×_{E j} E k ⟶ E k`. -/
@[simps]
noncomputable def Scheme.baseChangeDiagramSnd {j : I} {X : Scheme.{u}} (p : X ⟶ E.obj j) :
    Scheme.baseChangeDiagram E p ⟶ Over.forget j ⋙ E where
  app _ := pullback.snd _ _
  naturality _ _ _ := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.isPullback_baseChangeDiagram_map {j : I} {X : Scheme.{u}} (p : X ⟶ E.obj j)
    {k k' : Over j} (g : k ⟶ k') :
    IsPullback ((Scheme.baseChangeDiagram E p).map g) (pullback.snd p (E.map k.hom))
      (pullback.snd p (E.map k'.hom)) (E.map g.left) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have h₁ : (Scheme.baseChangeDiagram E p).map g ≫ pullback.fst p (E.map k'.hom) =
      pullback.fst p (E.map k.hom) := by
    simp [pullback.map]
  have h₂ : E.map g.left ≫ E.map k'.hom = E.map k.hom := by rw [← E.map_comp, Over.w g]
  rw [h₁, h₂]
  exact IsPullback.of_hasPullback _ _

instance [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] {j : I} {X : Scheme.{u}} (p : X ⟶ E.obj j)
    {k k' : Over j} (g : k ⟶ k') : IsAffineHom ((Scheme.baseChangeDiagram E p).map g) :=
  MorphismProperty.of_isPullback (Scheme.isPullback_baseChangeDiagram_map p g).flip inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The cone over `k ↦ X ×_{E j} E k` defined by a cartesian square `Y ⟶ X` over
`c.pt ⟶ E j`. -/
@[simps]
noncomputable def Scheme.baseChangeCone {j : I} {X Y : Scheme.{u}} {p : X ⟶ E.obj j}
    {e : Y ⟶ X} {q : Y ⟶ c.pt} (h : IsPullback e q p (c.π.app j)) :
    Cone (Scheme.baseChangeDiagram E p) where
  pt := Y
  π.app k := pullback.lift e (q ≫ c.π.app k.left) (by rw [h.w, Category.assoc, c.w k.hom])
  π.naturality k k' g := by
    apply pullback.hom_ext
    · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        baseChangeDiagram_map, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        baseChangeDiagram_map, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, c.w g.left]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a cartesian square to a lower level of the diagram. -/
lemma Scheme.isPullback_baseChangeCone {j : I} {X Y : Scheme.{u}} {p : X ⟶ E.obj j}
    {e : Y ⟶ X} {q : Y ⟶ c.pt} (h : IsPullback e q p (c.π.app j)) (k : Over j) :
    IsPullback ((Scheme.baseChangeCone h).π.app k) q (pullback.snd p (E.map k.hom))
      (c.π.app k.left) := by
  have s : IsPullback e q p (c.π.app k.left ≫ E.map k.hom) := by rwa [c.w k.hom]
  have t := IsPullback.of_right' s (IsPullback.of_hasPullback _ _)
  have key : (Scheme.baseChangeCone h).π.app k =
      (IsPullback.of_hasPullback p (E.map k.hom)).lift e (q ≫ c.π.app k.left)
        (by rw [s.w, Category.assoc]) := by
    apply pullback.hom_ext <;> simp
  rw [key]
  exact t

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal in
/-- The limit of `k ↦ X ×_{E j} E k` is `X ×_{E j} c.pt`. -/
noncomputable def Scheme.isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) {j : I}
    {X Y : Scheme.{u}} {p : X ⟶ E.obj j} {e : Y ⟶ X} {q : Y ⟶ c.pt}
    (h : IsPullback e q p (c.π.app j)) : IsLimit (Scheme.baseChangeCone h) :=
  isLimitOfIsPullbackOfIsConnected (Scheme.baseChangeDiagramSnd p) (Scheme.baseChangeCone h)
    (c.whisker (Over.forget j))
    { hom := q
      w _ := (pullback.lift_snd _ _ _).symm }
    (fun k ↦ Scheme.isPullback_baseChangeCone h k)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) c).symm hc)

set_option backward.isDefEq.respectTransparency false in
/-- The projections `X ×_{E j} E k ⟶ E j`. -/
@[simps]
noncomputable def Scheme.baseChangeDiagramToBase {j : I} {X : Scheme.{u}} (p : X ⟶ E.obj j) :
    Scheme.baseChangeDiagram E p ⟶ (Functor.const _).obj (E.obj j) where
  app k := pullback.snd _ _ ≫ E.map k.hom
  naturality k k' g := by
    simp only [Functor.const_obj_obj, baseChangeDiagram_map, Functor.const_obj_map,
      Category.comp_id, pullback.map, pullback.lift_snd_assoc,
      Category.assoc, ← E.map_comp, Over.w g]

lemma Scheme.compactSpace_baseChangeDiagram [∀ i, CompactSpace (E.obj i)] {j : I}
    {X : Scheme.{u}} (p : X ⟶ E.obj j) [QuasiCompact p] (k : Over j) :
    CompactSpace ((Scheme.baseChangeDiagram E p).obj k) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd p (E.map k.hom))
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback p (E.map k.hom)) ‹_›) _

lemma Scheme.quasiSeparatedSpace_baseChangeDiagram [∀ i, QuasiSeparatedSpace (E.obj i)] {j : I}
    {X : Scheme.{u}} (p : X ⟶ E.obj j) [QuasiSeparated p] (k : Over j) :
    QuasiSeparatedSpace ((Scheme.baseChangeDiagram E p).obj k) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd p (E.map k.hom)) _
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback p (E.map k.hom)) ‹_›)

set_option backward.isDefEq.respectTransparency false in
/-- The base change `X₁ ×_{E j} E l ⟶ X₂ ×_{E j} E l` of a morphism
`θ : X₁ ×_{E j} E k ⟶ X₂ ×_{E j} E k` over `E k`, for `l ⟶ k`. -/
noncomputable def Scheme.baseChangeDiagramMapHom {j : I} {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ E.obj j}
    {p₂ : X₂ ⟶ E.obj j} {k l : Over j} (g : l ⟶ k)
    (θ : pullback p₁ (E.map k.hom) ⟶ pullback p₂ (E.map k.hom))
    (hθ : θ ≫ pullback.snd _ _ = pullback.snd _ _) :
    pullback p₁ (E.map l.hom) ⟶ pullback p₂ (E.map l.hom) :=
  pullback.lift ((Scheme.baseChangeDiagram E p₁).map g ≫ θ ≫ pullback.fst _ _)
    (pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hθ]
      simp only [baseChangeDiagram_map, pullback.map, pullback.lift_snd_assoc]
      rw [Category.assoc, ← E.map_comp, Over.w g])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Scheme.baseChangeDiagramMapHom_fst {j : I} {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ E.obj j}
    {p₂ : X₂ ⟶ E.obj j} {k l : Over j} (g : l ⟶ k)
    (θ : pullback p₁ (E.map k.hom) ⟶ pullback p₂ (E.map k.hom))
    (hθ : θ ≫ pullback.snd _ _ = pullback.snd _ _) :
    Scheme.baseChangeDiagramMapHom g θ hθ ≫ pullback.fst _ _ =
      (Scheme.baseChangeDiagram E p₁).map g ≫ θ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Scheme.baseChangeDiagramMapHom_snd {j : I} {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ E.obj j}
    {p₂ : X₂ ⟶ E.obj j} {k l : Over j} (g : l ⟶ k)
    (θ : pullback p₁ (E.map k.hom) ⟶ pullback p₂ (E.map k.hom))
    (hθ : θ ≫ pullback.snd _ _ = pullback.snd _ _) :
    Scheme.baseChangeDiagramMapHom g θ hθ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma Scheme.baseChangeDiagramMapHom_comp_map {j : I} {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ E.obj j}
    {p₂ : X₂ ⟶ E.obj j} {k l : Over j} (g : l ⟶ k)
    (θ : pullback p₁ (E.map k.hom) ⟶ pullback p₂ (E.map k.hom))
    (hθ : θ ≫ pullback.snd _ _ = pullback.snd _ _) :
    Scheme.baseChangeDiagramMapHom g θ hθ ≫ (Scheme.baseChangeDiagram E p₂).map g =
      (Scheme.baseChangeDiagram E p₁).map g ≫ θ := by
  apply pullback.hom_ext
  · simp [baseChangeDiagramMapHom, pullback.map]
  · simp only [baseChangeDiagramMapHom, baseChangeDiagram_map, pullback.map, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, hθ]

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
  [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (i), relative form (Stacks 01ZC): let `X₁ ⟶ E j` be quasi-compact and
quasi-separated, `X₂ ⟶ E j` locally of finite presentation, and `Y = X₁ ×_{E j} c.pt`. Every
`E j`-morphism `Y ⟶ X₂` comes from an `E j`-morphism `X₁ ×_{E j} E k ⟶ X₂` for some `k`. -/
theorem Scheme.exists_hom_of_isPullback (hc : IsLimit c) {j : I} {X₁ X₂ Y : Scheme.{u}}
    {p₁ : X₁ ⟶ E.obj j} (p₂ : X₂ ⟶ E.obj j) [QuasiCompact p₁] [QuasiSeparated p₁]
    [LocallyOfFinitePresentation p₂] {e₁ : Y ⟶ X₁} {q : Y ⟶ c.pt}
    (h : IsPullback e₁ q p₁ (c.π.app j)) (e₂ : Y ⟶ X₂) (he₂ : e₂ ≫ p₂ = q ≫ c.π.app j) :
    ∃ (k : Over j) (b : pullback p₁ (E.map k.hom) ⟶ X₂),
      b ≫ p₂ = pullback.snd p₁ (E.map k.hom) ≫ E.map k.hom ∧
        (Scheme.baseChangeCone h).π.app k ≫ b = e₂ := by
  have := Scheme.compactSpace_baseChangeDiagram p₁
  have := Scheme.quasiSeparatedSpace_baseChangeDiagram p₁
  obtain ⟨k, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Scheme.baseChangeDiagram E p₁) (Scheme.baseChangeDiagramToBase p₁) p₂
    (Scheme.baseChangeCone h) (Scheme.isLimitBaseChangeCone hc h) e₂ (by
      ext k
      simp [he₂, c.w k.hom])
  exact ⟨k, b, hb', hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (i), uniqueness (Stacks 01ZC): two `E j`-morphisms `X₁ ×_{E j} E k ⟶ X₂`
(`X₂` locally of finite type over `E j`) which agree on `X₁ ×_{E j} c.pt` agree on
`X₁ ×_{E j} E l` for some `l ⟶ k`. -/
theorem Scheme.exists_map_comp_eq_of_isPullback (hc : IsLimit c) {j : I} {X₁ X₂ Y : Scheme.{u}}
    {p₁ : X₁ ⟶ E.obj j} (p₂ : X₂ ⟶ E.obj j) [QuasiCompact p₁] [QuasiSeparated p₁]
    [LocallyOfFiniteType p₂] {e₁ : Y ⟶ X₁} {q : Y ⟶ c.pt}
    (h : IsPullback e₁ q p₁ (c.π.app j)) {k : Over j} (b b' : pullback p₁ (E.map k.hom) ⟶ X₂)
    (hb : b ≫ p₂ = pullback.snd p₁ (E.map k.hom) ≫ E.map k.hom)
    (hb' : b' ≫ p₂ = pullback.snd p₁ (E.map k.hom) ≫ E.map k.hom)
    (hbb' : (Scheme.baseChangeCone h).π.app k ≫ b = (Scheme.baseChangeCone h).π.app k ≫ b') :
    ∃ (l : Over j) (g : l ⟶ k),
      (Scheme.baseChangeDiagram E p₁).map g ≫ b = (Scheme.baseChangeDiagram E p₁).map g ≫ b' := by
  have := Scheme.compactSpace_baseChangeDiagram p₁
  have := Scheme.quasiSeparatedSpace_baseChangeDiagram p₁
  exact Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (Scheme.baseChangeDiagram E p₁)
    (Scheme.baseChangeDiagramToBase p₁) p₂ (Scheme.baseChangeCone h)
    (Scheme.isLimitBaseChangeCone hc h) b b' hb.symm hb'.symm hbb'

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (i) for isomorphisms: two finitely presented `E j`-schemes `X₁`, `X₂` whose
base changes to `c.pt` are the same `Y` become isomorphic over some `E k`, compatibly with the
identifications with `Y`. -/
theorem Scheme.exists_iso_of_isPullback (hc : IsLimit c) {j : I} {X₁ X₂ Y : Scheme.{u}}
    {p₁ : X₁ ⟶ E.obj j} {p₂ : X₂ ⟶ E.obj j} [QuasiCompact p₁] [QuasiSeparated p₁]
    [LocallyOfFinitePresentation p₁] [QuasiCompact p₂] [QuasiSeparated p₂]
    [LocallyOfFinitePresentation p₂] {e₁ : Y ⟶ X₁} {e₂ : Y ⟶ X₂} {q : Y ⟶ c.pt}
    (h₁ : IsPullback e₁ q p₁ (c.π.app j)) (h₂ : IsPullback e₂ q p₂ (c.π.app j)) :
    ∃ (k : Over j) (θ : pullback p₁ (E.map k.hom) ≅ pullback p₂ (E.map k.hom)),
      θ.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        (Scheme.baseChangeCone h₁).π.app k ≫ θ.hom = (Scheme.baseChangeCone h₂).π.app k := by
  obtain ⟨k₁, b₁, hb₁, hb₁'⟩ := Scheme.exists_hom_of_isPullback hc p₂ h₁ e₂ h₂.w
  obtain ⟨k₂, b₂, hb₂, hb₂'⟩ := Scheme.exists_hom_of_isPullback hc p₁ h₂ e₁ h₁.w
  let k₃ := IsCofiltered.min k₁ k₂
  let g₁ : k₃ ⟶ k₁ := IsCofiltered.minToLeft k₁ k₂
  let g₂ : k₃ ⟶ k₂ := IsCofiltered.minToRight k₁ k₂
  -- the two morphisms at level `k₃`
  let θ₀ : pullback p₁ (E.map k₃.hom) ⟶ pullback p₂ (E.map k₃.hom) :=
    pullback.lift ((Scheme.baseChangeDiagram E p₁).map g₁ ≫ b₁) (pullback.snd _ _) (by
      rw [Category.assoc, hb₁]
      simp only [baseChangeDiagram_map, pullback.map, pullback.lift_snd_assoc]
      rw [Category.assoc, ← E.map_comp, Over.w g₁])
  let θ₀' : pullback p₂ (E.map k₃.hom) ⟶ pullback p₁ (E.map k₃.hom) :=
    pullback.lift ((Scheme.baseChangeDiagram E p₂).map g₂ ≫ b₂) (pullback.snd _ _) (by
      rw [Category.assoc, hb₂]
      simp only [baseChangeDiagram_map, pullback.map, pullback.lift_snd_assoc]
      rw [Category.assoc, ← E.map_comp, Over.w g₂])
  have hθ₀ : θ₀ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hθ₀' : θ₀' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hπθ₀ : (Scheme.baseChangeCone h₁).π.app k₃ ≫ θ₀ = (Scheme.baseChangeCone h₂).π.app k₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, Cone.w, hb₁']
      simp
    · simp [θ₀]
  have hπθ₀' : (Scheme.baseChangeCone h₂).π.app k₃ ≫ θ₀' =
      (Scheme.baseChangeCone h₁).π.app k₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, Cone.w, hb₂']
      simp
    · simp [θ₀']
  -- the composites become identities at a lower level
  obtain ⟨k₄, g₄, hg₄⟩ := Scheme.exists_map_comp_eq_of_isPullback hc p₁ h₁
    (θ₀ ≫ θ₀' ≫ pullback.fst _ _) (pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hθ₀',
      reassoc_of% hθ₀]) pullback.condition
    (by rw [reassoc_of% hπθ₀, reassoc_of% hπθ₀'])
  obtain ⟨k₅, g₅, hg₅⟩ := Scheme.exists_map_comp_eq_of_isPullback hc p₂ h₂
    (θ₀' ≫ θ₀ ≫ pullback.fst _ _) (pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hθ₀,
      reassoc_of% hθ₀']) pullback.condition
    (by rw [reassoc_of% hπθ₀', reassoc_of% hπθ₀])
  obtain ⟨k, h₄, h₅, hk⟩ := IsCofiltered.cospan g₄ g₅
  let g := h₄ ≫ g₄
  let θ := Scheme.baseChangeDiagramMapHom g θ₀ hθ₀
  let θ' := Scheme.baseChangeDiagramMapHom g θ₀' hθ₀'
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp, Scheme.baseChangeDiagramMapHom_fst,
        ← Category.assoc, Scheme.baseChangeDiagramMapHom_comp_map g θ₀ hθ₀, Category.assoc]
      simp only [g, Functor.map_comp, Category.assoc]
      rw [hg₄]
      simp [pullback.map]
    · simp [θ, θ']
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp, Scheme.baseChangeDiagramMapHom_fst,
        ← Category.assoc, Scheme.baseChangeDiagramMapHom_comp_map g θ₀' hθ₀', Category.assoc]
      simp only [g, hk, Functor.map_comp, Category.assoc]
      rw [hg₅]
      simp [pullback.map]
    · simp [θ, θ']
  refine ⟨k, ⟨θ, θ', hθθ', hθ'θ⟩, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, Scheme.baseChangeDiagramMapHom_fst, ← Category.assoc, Cone.w]
    have e₁ : (Scheme.baseChangeCone h₁).π.app k₃ ≫ θ₀ ≫ pullback.fst _ _ = e₂ := by
      simp only [θ₀, pullback.lift_fst]
      rw [← Category.assoc, Cone.w, hb₁']
    have e₂' : (Scheme.baseChangeCone h₂).π.app k ≫ pullback.fst _ _ = e₂ := by simp
    exact e₁.trans e₂'.symm
  · simp [θ]

end BaseChange

section Gluing

set_option backward.isDefEq.respectTransparency false in
/-- Gluing two schemes lying over the members `V`, `W` of an open cover of `S` along isomorphic
restrictions to `V ⊓ W` (given as a scheme `AM` over `V ⊓ W` with cartesian squares). -/
theorem Scheme.exists_isPullback_of_sup_eq_top {S : Scheme.{u}} (V W : S.Opens)
    {AV AW AM : Scheme.{u}} (pV : AV ⟶ V) (pW : AW ⟶ W) (pM : AM ⟶ (V ⊓ W : S.Opens))
    (iV : AM ⟶ AV) (iW : AM ⟶ AW)
    (hV : IsPullback iV pM pV (S.homOfLE inf_le_left))
    (hW : IsPullback iW pM pW (S.homOfLE inf_le_right)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S) (jV : AV ⟶ P) (jW : AW ⟶ P),
      iV ≫ jV = iW ≫ jW ∧ IsPullback jV pV p V.ι ∧ IsPullback jW pW p W.ι := by
  have : IsOpenImmersion iV := MorphismProperty.of_isPullback hV.flip inferInstance
  have : IsOpenImmersion iW := MorphismProperty.of_isPullback hW.flip inferInstance
  let p : pushout iV iW ⟶ S := pushout.desc (pV ≫ V.ι) (pW ≫ W.ι) (by
    rw [reassoc_of% hV.w, reassoc_of% hW.w, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have hinl : pushout.inl iV iW ≫ p = pV ≫ V.ι := pushout.inl_desc _ _ _
  have hinr : pushout.inr iV iW ≫ p = pW ≫ W.ι := pushout.inr_desc _ _ _
  -- every point of the pushout comes from `AV` or from `AW`
  have hsurj (z : ↥(pushout iV iW)) :
      (∃ a, pushout.inl iV iW a = z) ∨ ∃ b, pushout.inr iV iW b = z := by
    obtain ⟨t, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span iV iW) z
    rcases t with _ | _ | _
    · left
      refine ⟨iV x, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact congrArg (fun φ ↦ φ x) (colimit.w (span iV iW) WalkingSpan.Hom.fst)
    · exact .inl ⟨x, rfl⟩
    · exact .inr ⟨x, rfl⟩
  -- the points of `AW` over `V` come from `AM`
  have hW' (b : AW) (hb : (pW ≫ W.ι) b ∈ V) : ∃ m, iW m = b := by
    let m' : (V ⊓ W : S.Opens) := ⟨(pW ≫ W.ι) b, hb, (pW b).2⟩
    obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback hW b m'
      (Subtype.ext (by simp [m']))
    exact ⟨m, hm⟩
  have hV' (a : AV) (ha : (pV ≫ V.ι) a ∈ W) : ∃ m, iV m = a := by
    let m' : (V ⊓ W : S.Opens) := ⟨(pV ≫ V.ι) a, (pV a).2, ha⟩
    obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback hV a m'
      (Subtype.ext (by simp [m']))
    exact ⟨m, hm⟩
  refine ⟨pushout iV iW, p, pushout.inl _ _, pushout.inr _ _, pushout.condition, ?_, ?_⟩
  · refine (IsOpenImmersion.isPullback pV (pushout.inl _ _) V.ι p hinl ?_).flip
    ext z
    rw [Scheme.Opens.opensRange_ι]
    change p z ∈ V ↔ z ∈ Set.range _
    constructor
    · intro hz
      rcases hsurj z with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact ⟨a, rfl⟩
      · rw [← Scheme.Hom.comp_apply, hinr] at hz
        obtain ⟨m, rfl⟩ := hW' b hz
        refine ⟨iV m, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
    · rintro ⟨a, rfl⟩
      rw [← Scheme.Hom.comp_apply, hinl, Scheme.Hom.comp_apply]
      exact (pV a).2
  · refine (IsOpenImmersion.isPullback pW (pushout.inr _ _) W.ι p hinr ?_).flip
    ext z
    rw [Scheme.Opens.opensRange_ι]
    change p z ∈ W ↔ z ∈ Set.range _
    constructor
    · intro hz
      rcases hsurj z with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [← Scheme.Hom.comp_apply, hinl] at hz
        obtain ⟨m, rfl⟩ := hV' a hz
        refine ⟨iW m, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
      · exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      rw [← Scheme.Hom.comp_apply, hinr, Scheme.Hom.comp_apply]
      exact (pW b).2

lemma Scheme.isOpenCover_cond {X : Scheme.{u}} {U V : X.Opens} (h : U ⊔ V = ⊤) :
    TopologicalSpace.IsOpenCover (fun b : Bool ↦ cond b U V) := by
  rw [TopologicalSpace.IsOpenCover, iSup_bool_eq]
  exact h

lemma Scheme.pullback_fst_eq_snd_ι {X : Scheme.{u}} (U : X.Opens) :
    pullback.fst U.ι U.ι = pullback.snd U.ι U.ι :=
  (cancel_mono U.ι).mp pullback.condition

set_option backward.isDefEq.respectTransparency false in
/-- If a scheme `Y` over `X` is, over the members `XV = g⁻¹ V`, `XW = g⁻¹ W` of an open cover of
`X` coming from an open cover of `S`, the base change of pieces `AV`, `AW` of a scheme `P` over
`S`, compatibly on the overlap, then `Y` is the base change of `P` along `g : X ⟶ S`. -/
theorem Scheme.exists_isPullback_of_sup_eq_top' {S X Y P : Scheme.{u}} {g : X ⟶ S}
    {q : Y ⟶ X} {p : P ⟶ S} {V W : S.Opens} (hVW : V ⊔ W = ⊤) {XV XW : X.Opens}
    (hXV : g ⁻¹ᵁ V = XV) (hXW : g ⁻¹ᵁ W = XW)
    {AV AW : Scheme.{u}} {pV : AV ⟶ V} {pW : AW ⟶ W} {jV : AV ⟶ P} {jW : AW ⟶ P}
    (hjV : IsPullback jV pV p V.ι) (hjW : IsPullback jW pW p W.ι)
    {eV : (q ⁻¹ᵁ XV : Scheme) ⟶ AV} {eW : (q ⁻¹ᵁ XW : Scheme) ⟶ AW}
    (heV : IsPullback eV (q ∣_ XV) pV (g.resLE V XV hXV.ge))
    (heW : IsPullback eW (q ∣_ XW) pW (g.resLE W XW hXW.ge))
    (hcompat : Y.homOfLE (inf_le_left : q ⁻¹ᵁ XV ⊓ q ⁻¹ᵁ XW ≤ _) ≫ eV ≫ jV =
      Y.homOfLE inf_le_right ≫ eW ≫ jW) :
    ∃ e : Y ⟶ P, IsPullback e q p g ∧ (q ⁻¹ᵁ XV).ι ≫ e = eV ≫ jV ∧
      (q ⁻¹ᵁ XW).ι ≫ e = eW ≫ jW := by
  have hX : XV ⊔ XW = ⊤ := by rw [← hXV, ← hXW, ← Scheme.Hom.preimage_sup, hVW]; rfl
  have hY : q ⁻¹ᵁ XV ⊔ q ⁻¹ᵁ XW = ⊤ := by rw [← Scheme.Hom.preimage_sup, hX]; rfl
  let 𝒰 := Y.openCoverOfIsOpenCover _ (Scheme.isOpenCover_cond hY)
  let f : ∀ b : Bool, 𝒰.X b ⟶ P := fun b ↦
    Bool.casesOn (motive := fun b ↦ 𝒰.X b ⟶ P) b (eW ≫ jW) (eV ≫ jV)
  have hcompat' : Y.homOfLE (inf_le_left : q ⁻¹ᵁ XW ⊓ q ⁻¹ᵁ XV ≤ _) ≫ eW ≫ jW =
      Y.homOfLE inf_le_right ≫ eV ≫ jV := by
    have := congrArg (Y.homOfLE (inf_comm (q ⁻¹ᵁ XW) (q ⁻¹ᵁ XV)).le ≫ ·) hcompat
    simpa only [Scheme.homOfLE_homOfLE_assoc] using this.symm
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ f y := by
    intro x y
    cases x <;> cases y
    · exact congrArg (· ≫ f false) (Scheme.pullback_fst_eq_snd_ι (q ⁻¹ᵁ XW))
    · have hP := isPullback_opens_inf (q ⁻¹ᵁ XW) (q ⁻¹ᵁ XV)
      rw [← cancel_epi hP.isoPullback.hom]
      change hP.isoPullback.hom ≫ pullback.fst (q ⁻¹ᵁ XW).ι (q ⁻¹ᵁ XV).ι ≫ eW ≫ jW =
        hP.isoPullback.hom ≫ pullback.snd (q ⁻¹ᵁ XW).ι (q ⁻¹ᵁ XV).ι ≫ eV ≫ jV
      rw [hP.isoPullback_hom_fst_assoc, hP.isoPullback_hom_snd_assoc]
      exact hcompat'
    · have hP := isPullback_opens_inf (q ⁻¹ᵁ XV) (q ⁻¹ᵁ XW)
      rw [← cancel_epi hP.isoPullback.hom]
      change hP.isoPullback.hom ≫ pullback.fst (q ⁻¹ᵁ XV).ι (q ⁻¹ᵁ XW).ι ≫ eV ≫ jV =
        hP.isoPullback.hom ≫ pullback.snd (q ⁻¹ᵁ XV).ι (q ⁻¹ᵁ XW).ι ≫ eW ≫ jW
      rw [hP.isoPullback_hom_fst_assoc, hP.isoPullback_hom_snd_assoc]
      exact hcompat
    · exact congrArg (· ≫ f true) (Scheme.pullback_fst_eq_snd_ι (q ⁻¹ᵁ XV))
  let e := 𝒰.glueMorphisms f hf
  have heV' : (q ⁻¹ᵁ XV).ι ≫ e = eV ≫ jV := 𝒰.ι_glueMorphisms f hf true
  have heW' : (q ⁻¹ᵁ XW).ι ≫ e = eW ≫ jW := 𝒰.ι_glueMorphisms f hf false
  refine ⟨e, ?_, heV', heW'⟩
  refine (Scheme.isPullback_of_openCover q e g p
    (X.openCoverOfIsOpenCover _ (Scheme.isOpenCover_cond hX)) fun b ↦ ?_).flip
  cases b
  · have sq := heW.paste_horiz hjW
    rw [Scheme.Hom.resLE_comp_ι] at sq
    refine sq.flip.of_iso (pullbackRestrictIsoRestrict q XW).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Category.comp_id _) ?_ (by simp; rfl) (by simp)
    change (eW ≫ jW) ≫ 𝟙 P = (pullbackRestrictIsoRestrict q XW).inv ≫ pullback.fst q XW.ι ≫ e
    rw [Category.comp_id, pullbackRestrictIsoRestrict_inv_fst_assoc, heW']
  · have sq := heV.paste_horiz hjV
    rw [Scheme.Hom.resLE_comp_ι] at sq
    refine sq.flip.of_iso (pullbackRestrictIsoRestrict q XV).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Category.comp_id _) ?_ (by simp; rfl) (by simp)
    change (eV ≫ jV) ≫ 𝟙 P = (pullbackRestrictIsoRestrict q XV).inv ≫ pullback.fst q XV.ι ≫ e
    rw [Category.comp_id, pullbackRestrictIsoRestrict_inv_fst_assoc, heV']

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism over two nested open subsets gives a cartesian square. -/
lemma Scheme.isPullback_homOfLE_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : Y.Opens} (h : U ≤ U') :
    IsPullback (X.homOfLE (f.preimage_mono h)) (f ∣_ U) (f ∣_ U') (Y.homOfLE h) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · rw [← cancel_mono U'.ι]
    simp [morphismRestrict_ι]
  · rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
    ext x
    simp [← Scheme.Hom.comp_apply, morphismRestrict_ι]

@[reassoc]
lemma Scheme.homOfLE_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U ≤ U') (hV : V ≤ V') (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') :
    X.homOfLE hV ≫ f.resLE U' V' e' = f.resLE U V e ≫ Y.homOfLE hU := by
  rw [← cancel_mono U'.ι]
  simp

/-- A morphism which is, over the members of a cover of the base by two opens, a base change of
morphisms with a property `P` local on the target, has `P`. -/
lemma Scheme.of_isPullback_of_sup_eq_top {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] {S T : Scheme.{u}} (p : T ⟶ S) {V W : S.Opens}
    (h : V ⊔ W = ⊤) {AV AW : Scheme.{u}} {jV : AV ⟶ T} {pV : AV ⟶ V} {jW : AW ⟶ T}
    {pW : AW ⟶ W} (hV : IsPullback jV pV p V.ι) (hW : IsPullback jW pW p W.ι) (hpV : P pV)
    (hpW : P pW) : P p := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (fun b : Bool ↦ cond b V W)
    (by rw [iSup_bool_eq]; exact h)).mpr fun b ↦ ?_
  cases b
  · let e := hW.isoIsPullback _ _ (isPullback_morphismRestrict p W).flip
    have he : e.hom ≫ p ∣_ W = pW := hW.isoIsPullback_hom_snd _ _ _
    change P (p ∣_ W)
    rw [← P.cancel_left_of_respectsIso e.hom, he]
    exact hpW
  · let e := hV.isoIsPullback _ _ (isPullback_morphismRestrict p V).flip
    have he : e.hom ≫ p ∣_ V = pV := hV.isoIsPullback_hom_snd _ _ _
    change P (p ∣_ V)
    rw [← P.cancel_left_of_respectsIso e.hom, he]
    exact hpV

end Gluing

section Descent

variable (c) in
/-- Every finite étale scheme over the vertex `c.pt` of the cone `c` is the base change of a finite
étale scheme over some member `E.obj j` of the diagram. -/
def Scheme.FiniteEtaleDescends : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ c.pt) [IsFinite q] [Etale q],
    ∃ (j : I) (Yj : Scheme.{u}) (qj : Yj ⟶ E.obj j) (e : Y ⟶ Yj),
      IsFinite qj ∧ Etale qj ∧ IsPullback e q qj (c.π.app j)

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
  [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]

omit [IsCofiltered I] [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] in
lemma Scheme.compactSpace_opensDiagram_obj {i : I} {U : (E.obj i).Opens}
    (hU : IsCompact (U : Set (E.obj i))) (j : Over i) :
    CompactSpace ((opensDiagram E i U).obj j) :=
  isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := E.map j.hom) _ U.2 hU)

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
  [∀ i, CompactSpace (E.obj i)] in
lemma Scheme.quasiSeparatedSpace_opensDiagram_obj {i : I} (U : (E.obj i).Opens) (j : Over i) :
    QuasiSeparatedSpace ((opensDiagram E i U).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (E.map j.hom ⁻¹ᵁ U).2).mp
    (.of_quasiSeparatedSpace _)

omit [∀ i, CompactSpace (E.obj i)] in
set_option backward.isDefEq.respectTransparency false in
/-- The gluing step of EGA IV 8.8.2 (ii) (Stacks 01ZM) for finite étale schemes: if
`E.obj i = V ∪ W` with `V`, `W` quasi-compact, and finite étale schemes over the preimages of `V`
and `W` in `c.pt` descend, then finite étale schemes over `c.pt` descend. -/
theorem Scheme.finiteEtaleDescends_of_sup_eq_top (hc : IsLimit c) {i : I}
    {V W : (E.obj i).Opens} (hVW : V ⊔ W = ⊤) (hVc : IsCompact (V : Set (E.obj i)))
    (hWc : IsCompact (W : Set (E.obj i)))
    (HV : Scheme.FiniteEtaleDescends (opensCone E c i V))
    (HW : Scheme.FiniteEtaleDescends (opensCone E c i W)) :
    Scheme.FiniteEtaleDescends c := by
  intro Y q _ _
  let XV := c.π.app i ⁻¹ᵁ V
  let XW := c.π.app i ⁻¹ᵁ W
  let XM := c.π.app i ⁻¹ᵁ (V ⊓ W)
  have hMc : IsCompact ((V ⊓ W : (E.obj i).Opens) : Set (E.obj i)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ V.2 hVc W.2 hWc
  have := Scheme.compactSpace_opensDiagram_obj (E := E) hMc
  have := Scheme.quasiSeparatedSpace_opensDiagram_obj (E := E) (V ⊓ W)
  let EV := opensDiagram E i V
  let EW := opensDiagram E i W
  let EM := opensDiagram E i (V ⊓ W)
  -- the descents over `V` and `W`, at a common level `j₀`
  obtain ⟨jV, YV, qV, eV, _, _, hV⟩ := HV (q ∣_ XV)
  obtain ⟨jW, YW, qW, eW, _, _, hW⟩ := HW (q ∣_ XW)
  let j₀ : Over i := IsCofiltered.min jV jW
  let kV : Over jV := Over.mk (IsCofiltered.minToLeft jV jW)
  let kW : Over jW := Over.mk (IsCofiltered.minToRight jV jW)
  let qV₀ := pullback.snd qV (EV.map kV.hom)
  let qW₀ := pullback.snd qW (EW.map kW.hom)
  have : IsFinite qV₀ := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale qV₀ := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsFinite qW₀ := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale qW₀ := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have hV₀ := Scheme.isPullback_baseChangeCone (E := EV) (c := opensCone E c i V) hV kV
  have hW₀ := Scheme.isPullback_baseChangeCone (E := EW) (c := opensCone E c i W) hW kW
  let eV₀ := (Scheme.baseChangeCone (E := EV) (c := opensCone E c i V) hV).π.app kV
  let eW₀ := (Scheme.baseChangeCone (E := EW) (c := opensCone E c i W) hW).π.app kW
  -- their restrictions over `V ⊓ W`
  let ιV₀ : EM.obj j₀ ⟶ EV.obj j₀ := (E.obj j₀.left).homOfLE
    (Scheme.Hom.preimage_mono _ inf_le_left)
  let ιW₀ : EM.obj j₀ ⟶ EW.obj j₀ := (E.obj j₀.left).homOfLE
    (Scheme.Hom.preimage_mono _ inf_le_right)
  have hVM : IsPullback (Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_left)) ≫
      eV₀) (q ∣_ XM) qV₀
      ((opensCone E c i (V ⊓ W)).π.app j₀ ≫ ιV₀) := by
    have h := (Scheme.isPullback_homOfLE_morphismRestrict q
      ((c.π.app i).preimage_mono inf_le_left : XM ≤ XV)).paste_horiz hV₀
    convert h using 1
    exact (Scheme.homOfLE_resLE _ _ _ _ _).symm
  have hWM : IsPullback (Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_right)) ≫
      eW₀) (q ∣_ XM) qW₀
      ((opensCone E c i (V ⊓ W)).π.app j₀ ≫ ιW₀) := by
    have h := (Scheme.isPullback_homOfLE_morphismRestrict q
      ((c.π.app i).preimage_mono inf_le_right : XM ≤ XW)).paste_horiz hW₀
    convert h using 1
    exact (Scheme.homOfLE_resLE _ _ _ _ _).symm
  have hM₁ := IsPullback.of_right' hVM (IsPullback.of_hasPullback qV₀ ιV₀)
  have hMW₁ := IsPullback.of_right' hWM (IsPullback.of_hasPullback qW₀ ιW₀)
  have : IsFinite (pullback.snd qV₀ ιV₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale (pullback.snd qV₀ ιV₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsFinite (pullback.snd qW₀ ιW₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale (pullback.snd qW₀ ιW₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  -- the two restrictions over `V ⊓ W` become isomorphic at some level `l`
  obtain ⟨k, θ, hθ, hθ'⟩ := Scheme.exists_iso_of_isPullback (E := EM)
    (c := opensCone E c i (V ⊓ W)) (isLimitOpensCone E c hc i (V ⊓ W)) hM₁ hMW₁
  let l : Over i := k.left
  let g : l ⟶ j₀ := k.hom
  -- the pieces at level `l`
  let pV := pullback.snd qV₀ (EV.map g)
  let pW := pullback.snd qW₀ (EW.map g)
  let pM := pullback.snd (pullback.snd qV₀ ιV₀) (EM.map g)
  let pMB := pullback.snd (pullback.snd qW₀ ιW₀) (EM.map g)
  have : IsFinite pV := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale pV := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsFinite pW := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : Etale pW := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  let ιVl : EM.obj l ⟶ EV.obj l := (E.obj l.left).homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)
  let ιWl : EM.obj l ⟶ EW.obj l :=
    (E.obj l.left).homOfLE (Scheme.Hom.preimage_mono _ inf_le_right)
  have hcV : EM.map g ≫ ιV₀ = ιVl ≫ EV.map g := by
    rw [← cancel_mono (E.map j₀.hom ⁻¹ᵁ V).ι]
    simp [EM, EV, ιV₀, ιVl]
  have hcW : EM.map g ≫ ιW₀ = ιWl ≫ EW.map g := by
    rw [← cancel_mono (E.map j₀.hom ⁻¹ᵁ W).ι]
    simp [EM, EW, ιW₀, ιWl]
  have outerV := (IsPullback.of_hasPullback (pullback.snd qV₀ ιV₀) (EM.map g)).paste_horiz
    (IsPullback.of_hasPullback qV₀ ιV₀)
  rw [hcV] at outerV
  have hiV := IsPullback.of_right' outerV (IsPullback.of_hasPullback qV₀ (EV.map g))
  have outerW := (IsPullback.of_hasPullback (pullback.snd qW₀ ιW₀) (EM.map g)).paste_horiz
    (IsPullback.of_hasPullback qW₀ ιW₀)
  rw [hcW] at outerW
  have hiW' := IsPullback.of_right' outerW (IsPullback.of_hasPullback qW₀ (EW.map g))
  obtain ⟨iV, hiV, hiVfst⟩ : ∃ iV : pullback (pullback.snd qV₀ ιV₀) (EM.map g) ⟶
      pullback qV₀ (EV.map g), IsPullback iV pM pV ιVl ∧
        iV ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
    ⟨_, hiV, IsPullback.lift_fst _ _ _ _⟩
  obtain ⟨iW', hiW', hiWfst⟩ : ∃ iW' : pullback (pullback.snd qW₀ ιW₀) (EM.map g) ⟶
      pullback qW₀ (EW.map g), IsPullback iW' pMB pW ιWl ∧
        iW' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
    ⟨_, hiW', IsPullback.lift_fst _ _ _ _⟩
  have hiW : IsPullback (θ.hom ≫ iW') pM pW ιWl := by
    refine hiW'.of_iso θ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      change _ = θ.inv ≫ pullback.snd (pullback.snd qV₀ ιV₀) (EM.map k.hom)
      rw [← hθ, Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp
  -- gluing
  obtain ⟨P, p, jV', jW', hjVW, hjV, hjW⟩ := Scheme.exists_isPullback_of_sup_eq_top
    (E.map l.hom ⁻¹ᵁ V) (E.map l.hom ⁻¹ᵁ W) pV pW pM iV (θ.hom ≫ iW') hiV hiW
  have hVWl : E.map l.hom ⁻¹ᵁ V ⊔ E.map l.hom ⁻¹ᵁ W = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hVW]; rfl
  have hpF : IsFinite p := Scheme.of_isPullback_of_sup_eq_top p hVWl hjV hjW ‹_› ‹_›
  have hpE : Etale p := Scheme.of_isPullback_of_sup_eq_top p hVWl hjV hjW ‹_› ‹_›
  -- comparison with `Y`
  have hXV : c.π.app l.left ⁻¹ᵁ (E.map l.hom ⁻¹ᵁ V) = XV := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hXW : c.π.app l.left ⁻¹ᵁ (E.map l.hom ⁻¹ᵁ W) = XW := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hVl := Scheme.isPullback_baseChangeCone (E := EV) (c := opensCone E c i V) hV₀ k
  have hWl := Scheme.isPullback_baseChangeCone (E := EW) (c := opensCone E c i W) hW₀ k
  let eVl := (Scheme.baseChangeCone (E := EV) (c := opensCone E c i V) hV₀).π.app k
  let eWl := (Scheme.baseChangeCone (E := EW) (c := opensCone E c i W) hW₀).π.app k
  let eM := (Scheme.baseChangeCone (E := EM) (c := opensCone E c i (V ⊓ W)) hM₁).π.app k
  let eMB := (Scheme.baseChangeCone (E := EM) (c := opensCone E c i (V ⊓ W)) hMW₁).π.app k
  have heVl : eVl ≫ pullback.fst _ _ = eV₀ := by simp [eVl, eV₀]
  have heWl : eWl ≫ pullback.fst _ _ = eW₀ := by simp [eWl, eW₀]
  have heVl' : eVl ≫ pV = q ∣_ XV ≫ (opensCone E c i V).π.app l := by
    simp [eVl, pV, qV₀, g, l]
  have heWl' : eWl ≫ pW = q ∣_ XW ≫ (opensCone E c i W).π.app l := by
    simp [eWl, pW, qW₀, g, l]
  have heM : eM ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_left)) ≫ eV₀ := by
    simp [eM]
  have heMB : eMB ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_right)) ≫ eW₀ := by
    simp [eMB]
  have heM' : eM ≫ pM = q ∣_ XM ≫ (opensCone E c i (V ⊓ W)).π.app l := by
    simp [eM, pM, g, l]
  have heMB' : eMB ≫ pMB = q ∣_ XM ≫ (opensCone E c i (V ⊓ W)).π.app l := by
    simp [eMB, pMB, g, l]
  have hresV : Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_left)) ≫
      q ∣_ XV ≫ (opensCone E c i V).π.app l =
        q ∣_ XM ≫ (opensCone E c i (V ⊓ W)).π.app l ≫ ιVl := by
    rw [← cancel_mono (E.map l.hom ⁻¹ᵁ V).ι]
    simp [ιVl, XV, XM, morphismRestrict_ι_assoc]
  have hresW : Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_right)) ≫
      q ∣_ XW ≫ (opensCone E c i W).π.app l =
        q ∣_ XM ≫ (opensCone E c i (V ⊓ W)).π.app l ≫ ιWl := by
    rw [← cancel_mono (E.map l.hom ⁻¹ᵁ W).ι]
    simp [ιWl, XW, XM, morphismRestrict_ι_assoc]
  have hθ'' : eM ≫ θ.hom = eMB := hθ'
  have hstarV : Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_left)) ≫ eVl =
      eM ≫ iV := by
    apply pullback.hom_ext
    · rw [Category.assoc, heVl, Category.assoc, hiVfst, heM]
    · change _ ≫ pV = _ ≫ pV
      rw [Category.assoc, heVl', Category.assoc, hiV.w, reassoc_of% heM', hresV]
  have hstarW : Y.homOfLE (q.preimage_mono ((c.π.app i).preimage_mono inf_le_right)) ≫ eWl =
      eM ≫ θ.hom ≫ iW' := by
    apply pullback.hom_ext
    · rw [Category.assoc, heWl, Category.assoc, Category.assoc, hiWfst, reassoc_of% hθ'', heMB]
    · change _ ≫ pW = _ ≫ pW
      rw [Category.assoc, heWl', Category.assoc, Category.assoc, hiW'.w, reassoc_of% hθ'',
        reassoc_of% heMB', hresW]
  obtain ⟨e, he, -, -⟩ := Scheme.exists_isPullback_of_sup_eq_top' (g := c.π.app l.left) (q := q)
    (p := p) hVWl hXV hXW hjV hjW hVl hWl (by
      have h1 := hstarV =≫ jV'
      have h2 := hstarW =≫ jW'
      simp only [Category.assoc] at h1 h2
      refine h1.trans (Eq.trans ?_ h2.symm)
      rw [hjVW, Category.assoc])
  exact ⟨l.left, P, p, e, hpF, hpE, he⟩

omit [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] in
/-- Finite étale schemes descend along the limit of a cofiltered diagram with affine transition
maps as soon as some member of the diagram is affine. -/
theorem Scheme.finiteEtaleDescends_of_isAffine (hc : IsLimit c) (i₀ : I) [IsAffine (E.obj i₀)] :
    Scheme.FiniteEtaleDescends c := by
  intro Y q _ _
  let E' := Over.forget i₀ ⋙ E
  have : ∀ {j j' : Over i₀} (f : j ⟶ j'), IsAffineHom (E'.map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (E.map f.left))
  have : ∀ j : Over i₀, IsAffine (E'.obj j) := fun j ↦
    @isAffine_of_isAffineHom _ _ (E.map j.hom)
      (‹∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f)› j.hom) ‹IsAffine (E.obj i₀)›
  obtain ⟨j, Yj, qj, e, h₁, h₂, h₃⟩ := Scheme.exists_isPullback_of_isLimit_of_isAffine (E := E')
    (c := c.whisker (Over.forget i₀))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc) q
  exact ⟨j.left, Yj, qj, e, h₁, h₂, h₃⟩

end Descent

section Induction

private lemma iSup_fin_succ_eq_sup {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 1) → α) :
    ⨆ k, f k = f 0 ⊔ ⨆ k : Fin n, f k.succ :=
  le_antisymm (iSup_le fun k ↦ Fin.cases le_sup_left
      (fun k ↦ le_sup_of_le_right (le_iSup (fun k : Fin n ↦ f k.succ) k)) k)
    (sup_le (le_iSup f 0) (iSup_le fun k ↦ le_iSup f k.succ))

/-- (Implementation) Descent of finite étale schemes, by induction on the number of affine opens
covering some member of the diagram. -/
theorem Scheme.finiteEtaleDescends_of_iSup_eq_top (n : ℕ) :
    ∀ {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
      [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
      [∀ i, QuasiSeparatedSpace (E.obj i)] {c : Cone E} (_ : IsLimit c) (i : I)
      (V : Fin n → (E.obj i).Opens), (∀ k, IsAffineOpen (V k)) → ⨆ k, V k = ⊤ →
        Scheme.FiniteEtaleDescends c := by
  induction n with
  | zero =>
    intro I _ _ E _ _ _ c hc i V _ hV
    have : IsEmpty (E.obj i) := ⟨fun x ↦ by
      have : x ∈ (⊤ : (E.obj i).Opens) := trivial
      rw [← hV] at this
      simp at this⟩
    have : IsAffine (E.obj i) := isAffine_of_isEmpty
    exact Scheme.finiteEtaleDescends_of_isAffine hc i
  | succ n ih =>
    intro I _ _ E _ _ _ c hc i V hVa hV
    let W : (E.obj i).Opens := ⨆ k : Fin n, V k.succ
    have hVW : V 0 ⊔ W = ⊤ := by rw [← hV, iSup_fin_succ_eq_sup]
    have hVc : IsCompact (V 0 : Set (E.obj i)) := (hVa 0).isCompact
    have hWc : IsCompact (W : Set (E.obj i)) := by
      simp only [W, TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun k ↦ (hVa k.succ).isCompact
    have := Scheme.compactSpace_opensDiagram_obj (E := E) hVc
    have := Scheme.compactSpace_opensDiagram_obj (E := E) hWc
    have := Scheme.quasiSeparatedSpace_opensDiagram_obj (E := E) (V 0)
    have := Scheme.quasiSeparatedSpace_opensDiagram_obj (E := E) W
    let o : Over i := Over.mk (𝟙 i)
    -- the affine piece
    have HV : Scheme.FiniteEtaleDescends (opensCone E c i (V 0)) := by
      have : IsAffine ((opensDiagram E i (V 0)).obj o) := (hVa 0).preimage (E.map (𝟙 i))
      exact Scheme.finiteEtaleDescends_of_isAffine (isLimitOpensCone E c hc i (V 0)) o
    -- the other piece, by induction
    have HW : Scheme.FiniteEtaleDescends (opensCone E c i W) := by
      refine ih (isLimitOpensCone E c hc i W) o
        (fun k ↦ (E.map o.hom ⁻¹ᵁ W).ι ⁻¹ᵁ (E.map o.hom ⁻¹ᵁ V k.succ)) (fun k ↦ ?_) ?_
      · refine ((hVa k.succ).preimage (E.map o.hom)).preimage_of_isOpenImmersion
          (E.map o.hom ⁻¹ᵁ W).ι ?_
        rw [Scheme.Opens.opensRange_ι]
        exact Scheme.Hom.preimage_mono _ (le_iSup (fun k : Fin n ↦ V k.succ) k)
      · have h1 := (E.map o.hom ⁻¹ᵁ W).ι.preimage_iSup (fun k : Fin n ↦ E.map o.hom ⁻¹ᵁ V k.succ)
        have h2 := (E.map o.hom).preimage_iSup (fun k : Fin n ↦ V k.succ)
        refine h1.symm.trans ?_
        rw [← h2]
        exact Scheme.Opens.ι_preimage_self _
    exact Scheme.finiteEtaleDescends_of_sup_eq_top hc hVW hVc hWc HV HW

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
  [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]

/-- **EGA IV 8.8.2 (ii), 17.7.8** (Stacks 01ZM, 07RP): let `c.pt = lim Eᵢ` be the limit of a
cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps. Every
finite étale `c.pt`-scheme `Y` is the base change `Y = c.pt ×_{Eⱼ} Yⱼ` of a finite étale
`Eⱼ`-scheme `Yⱼ` for some `j`. -/
@[stacks 01ZM]
theorem Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale (hc : IsLimit c)
    {Y : Scheme.{u}} (q : Y ⟶ c.pt) [IsFinite q] [Etale q] :
    ∃ (j : I) (Yj : Scheme.{u}) (qj : Yj ⟶ E.obj j) (e : Y ⟶ Yj),
      IsFinite qj ∧ Etale qj ∧ IsPullback e q qj (c.π.app j) := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  let 𝒰 := (E.obj i).affineCover.finiteSubcover
  let eq := Fintype.equivFin 𝒰.I₀
  refine Scheme.finiteEtaleDescends_of_iSup_eq_top _ hc i
    (fun k ↦ (𝒰.f (eq.symm k)).opensRange) (fun k ↦ isAffineOpen_opensRange _) ?_ q
  rw [← 𝒰.iSup_opensRange]
  exact (eq.symm.iSup_comp (g := fun x ↦ (𝒰.f x).opensRange))

end Induction

end AlgebraicGeometry
