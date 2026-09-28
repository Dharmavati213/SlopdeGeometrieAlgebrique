/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import SGA.Foundations.EtaleStalkStructureSheaf
import SGA.Foundations.Etale.Functoriality

/-!
# The strict localization as a limit of affine étale neighbourhoods

Let `x̄ : Spec Ω ⟶ X` be a geometric point, `Ω` separably closed. The affine étale
neighbourhoods of `x̄` (the elements of the fibre functor on the affine étale site
`AlgebraicGeometry.Scheme.AffineEtale`) form an essentially small cofiltered category, which is
initial among all étale neighbourhoods. We fix a small cofiltered model
`AlgebraicGeometry.Scheme.Hom.AffineEtaleNbhd x̄` of it, with the diagram
`AlgebraicGeometry.Scheme.Hom.affineEtaleNbhdDiagram x̄` of affine schemes, and show that
`Spec 𝒪^{sh}_{X,x̄}` with the maps `Spec 𝒪^{sh}_{X,x̄} ⟶ V` given by the points of the
neighbourhoods is its limit (`AlgebraicGeometry.Scheme.Hom.isLimitAffineEtaleNbhdCone`; EGA IV
18.8.1, SGA 4 VIII 4.4, Stacks 04HX). On global sections this is the description of
`𝒪^{sh}_{X,x̄}` as the stalk of the étale structure sheaf
(`AlgebraicGeometry.Scheme.Hom.etaleStructureStalkIso`).

For `f : Y ⟶ X`, the base changes `Y ×_X V` form a diagram with limit `Y ×_X Spec 𝒪^{sh}_{X,x̄}`
(`AlgebraicGeometry.Scheme.Hom.isLimitAffineEtaleNbhdPullbackCone`).

We also record that a cone of affine schemes is a limit as soon as its image under `Γ` is a
colimit (`AlgebraicGeometry.Scheme.isLimitOfIsColimitΓ`).
-/

universe u

open CategoryTheory Limits Opposite

noncomputable section

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

/-- A cone of affine schemes whose image under `Γ` is a colimit is a limit cone: `Spec` preserves
limits and every affine scheme is the spectrum of its ring of global sections. -/
def Scheme.isLimitOfIsColimitΓ {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}} (c : Cone D)
    [∀ i, IsAffine (D.obj i)] [IsAffine c.pt] (hc : IsColimit (Scheme.Γ.mapCocone c.op)) :
    IsLimit c := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have hΓ : IsLimit (Scheme.Γ.rightOp.mapCone c) :=
    isLimitConeRightOpOfCocone (D.op ⋙ Scheme.Γ) hc
  have h₁ : IsLimit ((Scheme.Γ.rightOp ⋙ Scheme.Spec).mapCone c) :=
    isLimitOfPreserves Scheme.Spec hΓ
  have : IsIso (ΓSpec.adjunction.unit.app c.pt) := @IsAffine.affine c.pt ‹_›
  refine (IsLimit.postcomposeHomEquiv (asIso α) c) (h₁.ofIsoLimit ?_)
  refine Cone.ext (asIso (ΓSpec.adjunction.unit.app c.pt)).symm fun i ↦ ?_
  simp only [Functor.comp_obj, Functor.mapCone_pt, Iso.symm_hom, asIso_inv, Functor.mapCone_π_app,
    Functor.comp_map, Cone.postcompose_obj_pt, Cone.postcompose_obj_π, NatTrans.comp_app,
    asIso_hom, α, Functor.whiskerLeft_app]
  rw [IsIso.eq_inv_comp]
  exact (ΓSpec.adjunction.unit.naturality (c.π.app i)).symm

namespace Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The affine étale neighbourhoods of `ξ`: the category of elements of the fibre functor of `ξ`
restricted to the affine étale site. -/
abbrev AffineEtaleNbhdCat : Type (u + 1) :=
  (AffineEtale.Spec X ⋙ (pointSmallEtale ξ).fiber).Elements

/-- The inclusion of the affine étale neighbourhoods into all étale neighbourhoods. -/
abbrev affineEtaleNbhdCatι :
    ξ.AffineEtaleNbhdCat ⥤ (pointSmallEtale ξ).fiber.Elements :=
  Functor.Elements.precomp (AffineEtale.Spec X) (pointSmallEtale ξ).fiber

instance : ξ.affineEtaleNbhdCatι.Faithful where
  map_injective {a b} g g' h := by
    apply Subtype.ext
    exact (AffineEtale.Spec X).map_injective (congrArg Subtype.val h)

instance : ξ.affineEtaleNbhdCatι.Full where
  map_surjective {a b} g := ⟨⟨(AffineEtale.Spec X).preimage g.1, by
    change (pointSmallEtale ξ).fiber.map ((AffineEtale.Spec X).map _) a.2 = b.2
    rw [Functor.map_preimage]
    exact g.2⟩, Subtype.ext ((AffineEtale.Spec X).map_preimage g.1)⟩

/-- Every étale neighbourhood of `ξ` is refined by an affine one. -/
lemma exists_affineEtaleNbhdCatι_hom (e : (pointSmallEtale ξ).fiber.Elements) :
    ∃ a : ξ.AffineEtaleNbhdCat, Nonempty (ξ.affineEtaleNbhdCatι.obj a ⟶ e) := by
  obtain ⟨V, v⟩ := e
  obtain ⟨U, hU, hxU, T, ρ, hρ, τ, hτ, g, hg⟩ := ξ.exists_affineEtaleNbhd_hom V v
  have : Etale (Spec.map ρ ≫ hU.fromSpec) := by
    have : Etale (Spec.map ρ) := HasRingHomProperty.Spec_iff.mpr hρ
    infer_instance
  exact ⟨⟨AffineEtale.mk (Spec.map ρ ≫ hU.fromSpec), ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ⟩,
    ⟨⟨g, hg⟩⟩⟩

instance : IsCofiltered ξ.AffineEtaleNbhdCat :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful ξ.affineEtaleNbhdCatι
    ξ.exists_affineEtaleNbhdCatι_hom

instance : ξ.affineEtaleNbhdCatι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful ξ.affineEtaleNbhdCatι
    ξ.exists_affineEtaleNbhdCatι_hom

instance : InitiallySmall.{u} ξ.AffineEtaleNbhdCat := initiallySmall_of_essentiallySmall _

/-- A small cofiltered model of the category of affine étale neighbourhoods of `ξ`. -/
abbrev AffineEtaleNbhd : Type u := InitiallySmall.CofilteredInitialModel.{u} ξ.AffineEtaleNbhdCat

/-- The initial functor from `AffineEtaleNbhd ξ` to the étale neighbourhoods of `ξ`. -/
def affineEtaleNbhdFunctor : ξ.AffineEtaleNbhd ⥤ (pointSmallEtale ξ).fiber.Elements :=
  InitiallySmall.fromCofilteredInitialModel.{u} ξ.AffineEtaleNbhdCat ⋙ ξ.affineEtaleNbhdCatι

instance : ξ.affineEtaleNbhdFunctor.Initial := by
  unfold affineEtaleNbhdFunctor
  infer_instance

/-- The étale neighbourhood of `ξ` underlying an object of `AffineEtaleNbhd ξ`. -/
abbrev AffineEtaleNbhd.nbhd {ξ : Spec (.of Ω) ⟶ X} (k : ξ.AffineEtaleNbhd) : X.Etale :=
  (ξ.affineEtaleNbhdFunctor.obj k).1

/-- The point over `ξ` of the neighbourhood `k.nbhd`. -/
abbrev AffineEtaleNbhd.point {ξ : Spec (.of Ω) ⟶ X} (k : ξ.AffineEtaleNbhd) :
    (pointSmallEtale ξ).fiber.obj k.nbhd :=
  (ξ.affineEtaleNbhdFunctor.obj k).2

instance (k : ξ.AffineEtaleNbhd) : IsAffine k.nbhd.left := by
  change IsAffine (Spec _)
  infer_instance

lemma exists_affineEtaleNbhdFunctor_hom (e : (pointSmallEtale ξ).fiber.Elements) :
    ∃ k : ξ.AffineEtaleNbhd, Nonempty (ξ.affineEtaleNbhdFunctor.obj k ⟶ e) :=
  (Functor.initial_iff_of_isCofiltered ξ.affineEtaleNbhdFunctor).mp inferInstance |>.1 e

/-- The diagram `k ↦ V_k` of affine étale neighbourhoods of `ξ`. -/
def affineEtaleNbhdDiagram : ξ.AffineEtaleNbhd ⥤ Scheme.{u} :=
  ξ.affineEtaleNbhdFunctor ⋙ CategoryOfElements.π _ ⋙ Etale.forget X ⋙ Over.forget X

instance (k : ξ.AffineEtaleNbhd) : IsAffine (ξ.affineEtaleNbhdDiagram.obj k) :=
  inferInstanceAs (IsAffine k.nbhd.left)

/-- The cone over the affine étale neighbourhoods with vertex `Spec 𝒪^{sh}_{X,x̄}`. -/
@[simps]
def affineEtaleNbhdCone : Cone ξ.affineEtaleNbhdDiagram where
  pt := Spec ξ.strictLocalization
  π :=
    { app k := ξ.etaleNbhdHom k.nbhd k.point
      naturality k k' g := by
        change 𝟙 _ ≫ ξ.etaleNbhdHom _ _ =
          ξ.etaleNbhdHom _ _ ≫ (ξ.affineEtaleNbhdFunctor.map g).1.left
        rw [Category.id_comp, etaleNbhdHom_naturality]
        congr 1
        exact ((ξ.affineEtaleNbhdFunctor.map g).2).symm }

instance : IsAffine ξ.affineEtaleNbhdCone.pt := inferInstanceAs (IsAffine (Spec _))

/-- EGA IV 18.8.1, SGA 4 VIII 4.4, Stacks 04HX: `Spec 𝒪^{sh}_{X,x̄}` is the limit of the affine
étale neighbourhoods of `x̄`. -/
def isLimitAffineEtaleNbhdCone : IsLimit ξ.affineEtaleNbhdCone := by
  let P := X.etaleStructurePresheaf
  let Φ := ξ.affineEtaleNbhdFunctor
  have hP : IsColimit (((pointSmallEtale ξ).presheafFiberCocone P).whisker Φ.op) :=
    (Functor.Final.isColimitWhiskerEquiv Φ.op _).symm
      ((pointSmallEtale ξ).isColimitPresheafFiberCocone P)
  have hι (k : ξ.AffineEtaleNbhd) :
      (pointSmallEtale ξ).toPresheafFiber k.nbhd k.point P ≫ ξ.etaleStructureStalkHom =
        (ξ.etaleNbhdHom k.nbhd k.point).appTop ≫ (ΓSpecIso ξ.strictLocalization).hom :=
    (pointSmallEtale ξ).toPresheafFiber_presheafFiberDesc (P := P) _ _ _ _
  refine Scheme.isLimitOfIsColimitΓ _ (hP.ofIsoColimit (Cocone.ext
    (ξ.etaleStructureStalkIso ≪≫ (ΓSpecIso ξ.strictLocalization).symm) fun k ↦ ?_))
  change (pointSmallEtale ξ).toPresheafFiber k.unop.nbhd k.unop.point P ≫
    ξ.etaleStructureStalkHom ≫ (ΓSpecIso ξ.strictLocalization).inv =
      (ξ.etaleNbhdHom k.unop.nbhd k.unop.point).appTop
  rw [← Category.assoc, hι, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- The diagram `k ↦ Y ×_X V_k` of base changes of the affine étale neighbourhoods of `ξ`
(`Y ×_X V_k` is the underlying scheme of `(Etale.pullback f).obj V_k`). -/
@[simps]
def affineEtaleNbhdPullbackDiagram : ξ.AffineEtaleNbhd ⥤ Scheme.{u} where
  obj k := pullback k.nbhd.hom f
  map {k k'} g := pullback.map _ _ _ _ (ξ.affineEtaleNbhdDiagram.map g) (𝟙 Y) (𝟙 X)
    ((Category.comp_id _).trans
      (Over.w ((Etale.forget X).map (ξ.affineEtaleNbhdFunctor.map g).1)).symm)
    (by simp)
  map_id k := by
    apply pullback.hom_ext <;>
      simp only [Functor.id_obj, Functor.const_obj_obj, pullback.map,
        CategoryTheory.Functor.map_id, Category.comp_id, limit.lift_π, PullbackCone.mk_π_app,
        Category.id_comp]
    exact Category.comp_id _
  map_comp g g' := by
    apply pullback.hom_ext <;> simp [pullback.map]

/-- The projections `Y ×_X V_k ⟶ V_k`. -/
@[simps]
def affineEtaleNbhdPullbackDiagramFst :
    ξ.affineEtaleNbhdPullbackDiagram f ⟶ ξ.affineEtaleNbhdDiagram where
  app k := pullback.fst k.nbhd.hom f
  naturality k k' g := by simp [pullback.map]

/-- The cone over `k ↦ Y ×_X V_k` with vertex `Y ×_X Spec 𝒪^{sh}_{X,x̄}`. -/
@[simps]
def affineEtaleNbhdPullbackCone : Cone (ξ.affineEtaleNbhdPullbackDiagram f) where
  pt := pullback ξ.fromSpecStrictLocalization f
  π :=
    { app k := pullback.map _ _ _ _ (ξ.etaleNbhdHom k.nbhd k.point) (𝟙 Y) (𝟙 X)
        (by rw [Category.comp_id]; exact (etaleNbhdHom_comp_hom ξ _ _).symm) (by simp)
      naturality k k' g := by
        have := ξ.affineEtaleNbhdCone.w g
        simp only [affineEtaleNbhdCone_π_app] at this
        apply pullback.hom_ext
        · simp [pullback.map, ← this]
        · simp [pullback.map] }

lemma isPullback_affineEtaleNbhdPullbackCone (k : ξ.AffineEtaleNbhd) :
    IsPullback ((ξ.affineEtaleNbhdPullbackCone f).π.app k)
      (pullback.fst ξ.fromSpecStrictLocalization f) (pullback.fst k.nbhd.hom f)
      (ξ.etaleNbhdHom k.nbhd k.point) := by
  have h₁ := (IsPullback.of_hasPullback ξ.fromSpecStrictLocalization f).flip
  have e₁ : (ξ.affineEtaleNbhdPullbackCone f).π.app k ≫ pullback.snd k.nbhd.hom f =
      pullback.snd ξ.fromSpecStrictLocalization f := by
    simp [pullback.map]
  have e₂ : ξ.etaleNbhdHom k.nbhd k.point ≫ k.nbhd.hom = ξ.fromSpecStrictLocalization :=
    etaleNbhdHom_comp_hom ξ _ _
  refine IsPullback.of_right (h₁₁ := (ξ.affineEtaleNbhdPullbackCone f).π.app k)
    (h₁₂ := pullback.snd k.nbhd.hom f) (h₂₂ := k.nbhd.hom) ?_ (by simp [pullback.map])
    (IsPullback.of_hasPullback k.nbhd.hom f).flip
  rw [e₁, e₂]
  exact h₁

attribute [local instance] IsCofiltered.isConnected in
/-- The limit of `k ↦ Y ×_X V_k` is `Y ×_X Spec 𝒪^{sh}_{X,x̄}`. -/
def isLimitAffineEtaleNbhdPullbackCone : IsLimit (ξ.affineEtaleNbhdPullbackCone f) :=
  isLimitOfIsPullbackOfIsConnected (ξ.affineEtaleNbhdPullbackDiagramFst f)
    (ξ.affineEtaleNbhdPullbackCone f) ξ.affineEtaleNbhdCone
    { hom := pullback.fst _ _
      w k := by simp [affineEtaleNbhdPullbackCone] }
    (fun k ↦ ξ.isPullback_affineEtaleNbhdPullbackCone f k) ξ.isLimitAffineEtaleNbhdCone

end Scheme.Hom

end AlgebraicGeometry
