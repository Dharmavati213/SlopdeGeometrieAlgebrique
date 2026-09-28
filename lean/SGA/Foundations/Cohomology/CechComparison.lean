/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Leray
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Čech cohomology computes cohomology (Leray's theorem)

Let `U₁, …, Uₙ` be opens of a topological space with union `W` and `F` an abelian sheaf with
`H^q(U_x, F) = 0` for `q > 0` on all finite intersections `U_x`. Then
`Ȟᵖ(U, F) ≅ Hᵖ(W, F)` for all `p` (Leray; Stacks Project, Tag 01ET; Godement II.5.9.1), where
`Ȟᵖ(U, F)` is the homology of `TopCat.Presheaf.cechComplex U F`.

The isomorphism is obtained by dimension shifting along `0 → F → I → Q → 0` with `I` injective:
in degree `0` both sides are `F(W)` (`TopCat.Presheaf.cechH0Map`); in degree `1` both sides are
the cokernel of `I(W) → Q(W)`; in degree `p + 2` the connecting maps give
`Ȟ^{p+2}(U, F) ≅ Ȟ^{p+1}(U, Q)` and `H^{p+2}(W, F) ≅ H^{p+1}(W, Q)`. The resulting isomorphisms
`TopCat.Sheaf.cechHomologyIso` are natural in `F` (`TopCat.Sheaf.cechHomologyIso_naturality`),
hence compatible with any ring of endomorphisms acting on `F` (e.g. `Γ(X, 𝒪_X)` for an
`𝒪_X`-module, see `SGA.Foundations.Cohomology.AffineOpenVanishing`).
-/

universe w u

open CategoryTheory Limits TopologicalSpace Opposite Abelian TopCat.Presheaf

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {n : ℕ} (U : Fin n → Opens X)

/-- The augmentation `P(⋃ Uᵢ) → Č⁰(U, P)`, as a morphism of abelian groups. -/
noncomputable def cechAugmentationHom (P : TopCat.Presheaf AddCommGrpCat.{u} X) :
    P.obj (op (⨆ i, U i)) ⟶ (cechComplex U P).X 0 :=
  AddCommGrpCat.ofHom (cechAugmentation U P)

lemma cechAugmentationHom_apply (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    (s : P.obj (op (⨆ i, U i))) : cechAugmentationHom U P s = cechAugmentation U P s :=
  rfl

lemma cechAugmentation_comp_d (P : TopCat.Presheaf AddCommGrpCat.{u} X) :
    cechAugmentationHom U P ≫ (cechComplex U P).d 0 1 = 0 :=
  AddCommGrpCat.ext fun s ↦ (cechComplex_d_apply U P 0 _).trans (cechD_cechAugmentation U P s)

/-- The canonical map `P(⋃ Uᵢ) → Ȟ⁰(U, P)`. -/
noncomputable def cechH0Map (P : TopCat.Presheaf AddCommGrpCat.{u} X) :
    P.obj (op (⨆ i, U i)) ⟶ (cechComplex U P).homology 0 :=
  (cechComplex U P).liftCycles (cechAugmentationHom U P) 1 (by simp)
    (cechAugmentation_comp_d U P) ≫ (cechComplex U P).homologyπ 0

lemma cechAugmentation_naturality {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ : P ⟶ Q)
    (s : P.obj (op (⨆ i, U i))) :
    cechCochainMap U φ 0 (cechAugmentation U P s) = cechAugmentation U Q (φ.app _ s) :=
  funext fun _ ↦ NatTrans.naturality_apply φ _ s

/-- The morphism of Čech complexes induced by a morphism of presheaves. -/
noncomputable def cechComplexMap {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ : P ⟶ Q) :
    cechComplex U P ⟶ cechComplex U Q :=
  (cechComplexFunctor U).map φ

lemma cechComplexMap_f_apply {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ : P ⟶ Q) (m : ℕ)
    (c : CechCochain U P m) : (cechComplexMap U φ).f m c = cechCochainMap U φ m c :=
  rfl

lemma cechH0Map_naturality {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (φ : P ⟶ Q) :
    cechH0Map U P ≫ HomologicalComplex.homologyMap (cechComplexMap U φ) 0 =
      φ.app _ ≫ cechH0Map U Q := by
  rw [cechH0Map, cechH0Map, Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  exact AddCommGrpCat.ext fun s ↦ cechAugmentation_naturality U φ s

/-- For a sheaf, `F(⋃ Uᵢ) → Ȟ⁰(U, F)` is an isomorphism. -/
instance isIso_cechH0Map (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) : IsIso (cechH0Map U F.obj) := by
  have hl : IsIso ((cechComplex U F.obj).liftCycles (cechAugmentationHom U F.obj) 1 (by simp)
      (cechAugmentation_comp_d U F.obj)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro s t h
      apply cechAugmentation_injective U F
      have := congrArg (fun z ↦ (cechComplex U F.obj).iCycles 0 z) h
      simp only [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i] at this
      exact this
    · intro z
      have hinj : Function.Injective ((cechComplex U F.obj).iCycles 0) :=
        (AddCommGrpCat.mono_iff_injective _).mp inferInstance
      have hz : cechD U F.obj 0 ((cechComplex U F.obj).iCycles 0 z) = 0 :=
        (cechComplex_d_apply U F.obj 0 _).symm.trans
          ((ConcreteCategory.comp_apply _ _ z).symm.trans
            (congrArg (fun (f : (cechComplex U F.obj).cycles 0 ⟶ (cechComplex U F.obj).X 1) ↦ f z)
              ((cechComplex U F.obj).iCycles_d 0 1)))
      obtain ⟨t, ht⟩ := exists_cechAugmentation_eq U F _ hz
      refine ⟨t, hinj ?_⟩
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
      exact ht
  rw [cechH0Map]
  infer_instance

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {n : ℕ} (U : Fin n → Opens X)

section ShortExact

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact)

/-- The short complex of Čech complexes associated to a short complex of sheaves. -/
noncomputable abbrev cechShortComplex : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk (cechComplexMap U S.f.hom) (cechComplexMap U S.g.hom) (by
    ext m : 1
    exact AddCommGrpCat.ext fun c ↦ cechCochainMap_g_f U m c)

include hS in
/-- If `0 → F → I → Q → 0` is short exact and `I → Q` is onto on the sections over every `U_x`,
the Čech complexes form a short exact sequence. -/
lemma cechShortComplex_shortExact
    (hsurj : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      Function.Surjective (S.g.hom.app (op (cechOpen U x)))) :
    (cechShortComplex U (S := S)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m ↦ ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ab_exact_iff]
    intro c hc
    exact exists_cechCochainMap_eq hS U m c hc
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (cechCochainMap_injective hS U m)
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro q
    choose i hi using fun x ↦ hsurj x (q x)
    exact ⟨i, funext hi⟩

end ShortExact

section Ext

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (W : Opens X)

/-- The connecting map `Hᵖ(W, Q) → H^{p+1}(W, F)` of `0 → F → I → Q → 0`. -/
noncomputable def H'δ (p : ℕ) : S.X₃.H' p W ⟶ S.X₁.H' (p + 1) W :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp _ rfl)

lemma H'δ_apply {p : ℕ} (x : S.X₃.H' p W) : H'δ hS W p x = x.comp hS.extClass rfl :=
  rfl

lemma H'.map_comp_H'δ : CategoryTheory.Sheaf.H'.map S.g 0 W ≫ H'δ hS W 0 = 0 := by
  ext x
  change ((show Ext _ _ 0 from x).comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma H'δ_bijective [Injective S.X₂] (p : ℕ) : Function.Bijective (H'δ hS W (p + 1)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS (show Ext _ _ (p + 1) from x) rfl hx
    rw [← hy, show y = 0 from Ext.eq_zero_of_injective y, Ext.zero_comp]
    rfl
  · intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS (show Ext _ _ (p + 2) from x)
      (Ext.eq_zero_of_injective _) (n₀ := p + 1) rfl
    exact ⟨y, hy⟩

lemma H'δ_zero_surjective [Injective S.X₂] : Function.Surjective (H'δ hS W 0) := by
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS (show Ext _ _ 1 from x)
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  exact ⟨y, hy⟩

/-- The exact sequence `H⁰(W, I) → H⁰(W, Q) → H¹(W, F)`. -/
lemma H'δ_exact : (ShortComplex.mk _ _ (H'.map_comp_H'δ hS W)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact Ext.covariant_sequence_exact₃ _ hS (show Ext _ _ 0 from x) rfl hx

end Ext

variable [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The isomorphism `Ȟ⁰(U, F) ≅ H⁰(W, F) = F(W)`. -/
noncomputable def cechH0Iso (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) : (cechComplex U F.obj).homology 0 ≅ F.H' 0 (⨆ i, U i) :=
  (asIso (cechH0Map U F.obj)).symm ≪≫
    (CategoryTheory.Sheaf.H'.equiv₀ F (⨆ i, U i)).symm.toAddCommGrpIso

lemma cechH0Iso_naturality {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (φ : F ⟶ G) :
    HomologicalComplex.homologyMap (cechComplexMap U φ.hom) 0 ≫ (cechH0Iso U G).hom =
      (cechH0Iso U F).hom ≫ CategoryTheory.Sheaf.H'.map φ 0 (⨆ i, U i) := by
  rw [← cancel_epi (cechH0Map U F.obj)]
  simp only [cechH0Iso, Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc,
    cechH0Map_naturality, IsIso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  ext s
  exact (CategoryTheory.Sheaf.H'.equiv₀_symm_naturality φ s).symm

/-- `F` is *Leray-acyclic* for the family `U`: `H^q(U_x, F) = 0` for all `q > 0` and all finite
intersections `U_x` of members of `U`. -/
structure IsLerayAcyclic
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop where
  subsingleton_H' {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ) :
    Subsingleton (F.H' (q + 1) (cechOpen U x))

section InjSeq

variable (F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The short exact sequence `0 → F → I(F) → Q(F) → 0`, `I(F)` the chosen injective hull. -/
noncomputable abbrev injSeq :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

omit [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
lemma injSeq_shortExact : (injSeq F).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact (Injective.ι F)
    mono_f := by change Mono (Injective.ι F); infer_instance
    epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }

instance : Injective (injSeq F).X₂ := inferInstanceAs (Injective (Injective.under F))

variable {U F} in
lemma IsLerayAcyclic.surjective (hF : IsLerayAcyclic U F) {m : ℕ} (x : Fin (m + 1) → Fin n) :
    Function.Surjective ((injSeq F).g.hom.app (op (cechOpen U x))) :=
  surjective_app_of_subsingleton_H'_one (injSeq_shortExact F) _ (hF.subsingleton_H' x 0)

variable {U F} in
lemma IsLerayAcyclic.injSeqX₃ (hF : IsLerayAcyclic U F) : IsLerayAcyclic U (injSeq F).X₃ :=
  ⟨fun x q ↦ (subsingleton_H'_succ_iff (injSeq_shortExact F) _ q).mpr
    (hF.subsingleton_H' x (q + 1))⟩

variable {F G} in
/-- An extension `I(F) ⟶ I(G)` of `φ : F ⟶ G`. -/
noncomputable def injMap (φ : F ⟶ G) : (injSeq F).X₂ ⟶ (injSeq G).X₂ :=
  Injective.factorThru (φ ≫ Injective.ι G) (Injective.ι F)

omit [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
variable {F G} in
lemma ι_injMap (φ : F ⟶ G) : (injSeq F).f ≫ injMap φ = φ ≫ (injSeq G).f :=
  Injective.comp_factorThru _ _

variable {F G} in
/-- The morphism `injSeq F ⟶ injSeq G` extending `φ : F ⟶ G`. -/
noncomputable def injSeqMap (φ : F ⟶ G) : injSeq F ⟶ injSeq G where
  τ₁ := φ
  τ₂ := injMap φ
  τ₃ := cokernel.desc (Injective.ι F) (injMap φ ≫ cokernel.π (Injective.ι G)) (by
      rw [← Category.assoc, ι_injMap, Category.assoc, cokernel.condition, comp_zero])
  comm₁₂ := (ι_injMap φ).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

omit [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
lemma isZero_homology_injSeq (q : ℕ) :
    IsZero ((cechComplex U (injSeq F).X₂.obj).homology (q + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (cechComplex_exactAt_of_injective (injSeq F).X₂ U q)

end InjSeq

variable {U} in
lemma IsLerayAcyclic.shortExact_cechShortComplex
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : IsLerayAcyclic U F) : (cechShortComplex U (S := injSeq F)).ShortExact :=
  cechShortComplex_shortExact U (injSeq_shortExact F) hF.surjective

variable {U} in
/-- The morphism of short complexes of Čech complexes induced by a morphism of short complexes of
sheaves. -/
noncomputable def cechShortComplexMap
    {S₁ S₂ : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (φ : S₁ ⟶ S₂) : cechShortComplex U (S := S₁) ⟶ cechShortComplex U (S := S₂) where
  τ₁ := cechComplexMap U φ.τ₁.hom
  τ₂ := cechComplexMap U φ.τ₂.hom
  τ₃ := cechComplexMap U φ.τ₃.hom
  comm₁₂ := by
    ext m : 1
    exact AddCommGrpCat.ext fun c ↦ funext fun x ↦ congrArg (fun f ↦ f.hom.app _ (c x)) φ.comm₁₂
  comm₂₃ := by
    ext m : 1
    exact AddCommGrpCat.ext fun c ↦ funext fun x ↦ congrArg (fun f ↦ f.hom.app _ (c x)) φ.comm₂₃

variable {U}

/-- The connecting isomorphism `Hᵖ(W, Q(F)) ≅ H^{p+1}(W, F)` for `p ≥ 1`. -/
noncomputable def H'δIso (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (W : Opens X) (p : ℕ) :
    (injSeq F).X₃.H' (p + 1) W ≅ F.H' (p + 2) W :=
  (AddEquiv.ofBijective (H'δ (injSeq_shortExact F) W (p + 1)).hom
    (H'δ_bijective (injSeq_shortExact F) W p)).toAddCommGrpIso

lemma complexShape_up_rel_succ (p : ℕ) : (ComplexShape.up ℕ).Rel p (p + 1) := rfl

/-- `Ȟ¹(U, F)` is the cokernel of `Ȟ⁰(U, I(F)) → Ȟ⁰(U, Q(F))`. -/
noncomputable def cechH1IsCokernel {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (hF : IsLerayAcyclic U F) :
    IsColimit (CokernelCofork.ofπ
      (hF.shortExact_cechShortComplex.δ 0 1 (complexShape_up_rel_succ 0))
      (hF.shortExact_cechShortComplex.comp_δ 0 1 (complexShape_up_rel_succ 0))) :=
  haveI := hF.shortExact_cechShortComplex.epi_δ 0 1 (complexShape_up_rel_succ 0)
    (isZero_homology_injSeq U F 0)
  (hF.shortExact_cechShortComplex.homology_exact₃ 0 1 (complexShape_up_rel_succ 0)).gIsCokernel

/-- `H¹(W, F)` is the cokernel of `H⁰(W, I(F)) → H⁰(W, Q(F))`. -/
noncomputable def H'1IsCokernel (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (W : Opens X) :
    IsColimit (CokernelCofork.ofπ (H'δ (injSeq_shortExact F) W 0)
      (H'.map_comp_H'δ (injSeq_shortExact F) W)) :=
  haveI := (AddCommGrpCat.epi_iff_surjective _).mpr
    (H'δ_zero_surjective (injSeq_shortExact F) W)
  (H'δ_exact (injSeq_shortExact F) W).gIsCokernel

/-- The comparison isomorphisms `Ȟᵖ(U, F) ≅ Hᵖ(⋃ Uᵢ, F)` for a Leray-acyclic sheaf `F`
(Leray's theorem, Stacks Tag 01ET), constructed by dimension shifting. They are natural in `F`
(`cechHomologyIso_naturality`). -/
noncomputable def cechHomologyIso :
    (p : ℕ) → (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) →
      IsLerayAcyclic U F → ((cechComplex U F.obj).homology p ≅ F.H' p (⨆ i, U i))
  | 0, F, _ => cechH0Iso U F
  | 1, F, hF =>
    CokernelCofork.mapIsoOfIsColimit (cechH1IsCokernel hF) (H'1IsCokernel F (⨆ i, U i))
      (Arrow.isoMk (cechH0Iso U (injSeq F).X₂) (cechH0Iso U (injSeq F).X₃)
        (cechH0Iso_naturality U (injSeq F).g).symm)
  | p + 2, F, hF =>
    (hF.shortExact_cechShortComplex.δIso (p + 1) (p + 2) (complexShape_up_rel_succ (p + 1))
      (isZero_homology_injSeq U F p)
      (isZero_homology_injSeq U F (p + 1))).symm ≪≫
      cechHomologyIso (p + 1) (injSeq F).X₃ hF.injSeqX₃ ≪≫ H'δIso F (⨆ i, U i) p

lemma H'δ_naturality {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (φ : F ⟶ G) (W : Opens X) (p : ℕ) :
    CategoryTheory.Sheaf.H'.map (injSeqMap φ).τ₃ p W ≫ H'δ (injSeq_shortExact G) W p =
      H'δ (injSeq_shortExact F) W p ≫ CategoryTheory.Sheaf.H'.map φ (p + 1) W := by
  ext x
  change ((show Ext _ _ p from x).comp (Ext.mk₀ (injSeqMap φ).τ₃) (add_zero p)).comp
      (injSeq_shortExact G).extClass rfl =
    ((show Ext _ _ p from x).comp (injSeq_shortExact F).extClass rfl).comp (Ext.mk₀ φ)
      (add_zero (p + 1))
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    ← (injSeq_shortExact F).extClass_naturality (injSeq_shortExact G) (injSeqMap φ)]
  rfl

lemma cechHomologyIso_one_comp {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (hF : IsLerayAcyclic U F) :
    hF.shortExact_cechShortComplex.δ 0 1 (complexShape_up_rel_succ 0) ≫
        (cechHomologyIso 1 F hF).hom =
      (cechH0Iso U (injSeq F).X₃).hom ≫ H'δ (injSeq_shortExact F) (⨆ i, U i) 0 := by
  rw [cechHomologyIso.eq_2, CokernelCofork.mapIsoOfIsColimit_hom]
  have h := CokernelCofork.π_mapOfIsColimit (cechH1IsCokernel hF)
    (CokernelCofork.ofπ _ (H'.map_comp_H'δ (injSeq_shortExact F) (⨆ i, U i)))
    (Arrow.isoMk (cechH0Iso U (injSeq F).X₂) (cechH0Iso U (injSeq F).X₃)
        (cechH0Iso_naturality U (injSeq F).g).symm).hom
  rw [Cofork.π_ofπ, Cofork.π_ofπ] at h
  exact h

lemma H'δIso_hom (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (W : Opens X) (p : ℕ) : (H'δIso F W p).hom = H'δ (injSeq_shortExact F) W (p + 1) :=
  rfl

/-- The comparison isomorphisms of Leray's theorem are natural. -/
theorem cechHomologyIso_naturality :
    ∀ (p : ℕ) {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
      (hF : IsLerayAcyclic U F) (hG : IsLerayAcyclic U G) (φ : F ⟶ G),
      HomologicalComplex.homologyMap (cechComplexMap U φ.hom) p ≫ (cechHomologyIso p G hG).hom =
        (cechHomologyIso p F hF).hom ≫ CategoryTheory.Sheaf.H'.map φ p (⨆ i, U i)
  | 0, F, G, hF, hG, φ => by
    rw [cechHomologyIso.eq_1, cechHomologyIso.eq_1]
    exact cechH0Iso_naturality U φ
  | 1, F, G, hF, hG, φ => by
    have := hF.shortExact_cechShortComplex.epi_δ 0 1 (complexShape_up_rel_succ 0)
      (isZero_homology_injSeq U F 0)
    rw [← cancel_epi (hF.shortExact_cechShortComplex.δ 0 1 (complexShape_up_rel_succ 0))]
    have hδ := HomologicalComplex.HomologySequence.δ_naturality (cechShortComplexMap (injSeqMap φ))
      hF.shortExact_cechShortComplex hG.shortExact_cechShortComplex 0 1
      (complexShape_up_rel_succ 0)
    rw [← Category.assoc, show cechComplexMap U φ.hom = (cechShortComplexMap (injSeqMap φ)).τ₁
      from rfl, hδ, Category.assoc, cechHomologyIso_one_comp, ← Category.assoc,
      show (cechShortComplexMap (U := U) (injSeqMap φ)).τ₃ = cechComplexMap U (injSeqMap φ).τ₃.hom
      from rfl, cechH0Iso_naturality U (injSeqMap φ).τ₃, Category.assoc, H'δ_naturality,
      ← Category.assoc, ← cechHomologyIso_one_comp, Category.assoc]
  | p + 2, F, G, hF, hG, φ => by
    have ih := cechHomologyIso_naturality (p + 1) hF.injSeqX₃ hG.injSeqX₃ (injSeqMap φ).τ₃
    have hδ := HomologicalComplex.HomologySequence.δ_naturality (cechShortComplexMap (injSeqMap φ))
      hF.shortExact_cechShortComplex hG.shortExact_cechShortComplex (p + 1) (p + 2)
      (complexShape_up_rel_succ (p + 1))
    rw [cechHomologyIso.eq_3, cechHomologyIso.eq_3]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, H'δIso_hom]
    have h1 : HomologicalComplex.homologyMap (cechComplexMap U φ.hom) (p + 2) ≫
        (hG.shortExact_cechShortComplex.δIso (p + 1) (p + 2) (complexShape_up_rel_succ (p + 1))
          (isZero_homology_injSeq U G p) (isZero_homology_injSeq U G (p + 1))).inv =
        (hF.shortExact_cechShortComplex.δIso (p + 1) (p + 2) (complexShape_up_rel_succ (p + 1))
          (isZero_homology_injSeq U F p) (isZero_homology_injSeq U F (p + 1))).inv ≫
          HomologicalComplex.homologyMap (cechComplexMap U (injSeqMap φ).τ₃.hom) (p + 1) := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact hδ
    rw [← Category.assoc, h1, Category.assoc, ← Category.assoc
      (HomologicalComplex.homologyMap (cechComplexMap U (injSeqMap φ).τ₃.hom) (p + 1)), ih,
      Category.assoc, H'δ_naturality]

/-- **Leray's theorem** (Stacks Tag 01ET): if `H^q(U_x, F) = 0` for all `q > 0` and all finite
intersections `U_x` of the `Uᵢ`, then `Ȟᵖ(U, F) ≅ Hᵖ(⋃ Uᵢ, F)` for every `p`. -/
theorem nonempty_cechHomologyIso (p : ℕ)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (F.H' (q + 1) (cechOpen U x))) :
    Nonempty ((cechComplex U F.obj).homology p ≅ F.H' p (⨆ i, U i)) :=
  ⟨cechHomologyIso p F ⟨hF⟩⟩

end TopCat.Sheaf
