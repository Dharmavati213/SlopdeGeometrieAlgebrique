/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import SGA.Foundations.Limits.FiniteEtale
import SGA.Foundations.SpecStalkLimit

/-!
# Base change along a filtered colimit of rings

Let `R ⟶ F(j)` be a filtered diagram of `R`-algebras with colimit `R ⟶ A` and `X` a scheme over
`Spec R`. Then `X ×_R Spec A` is the limit of the `X ×_R Spec F(j)`, with affine transition
maps (EGA IV 8.2); if `X` is quasi-compact and quasi-separated, every finite étale
`X ×_R Spec A`-scheme comes from some `X ×_R Spec F(j)` (EGA IV 8.8.2, 17.7.8,
`AlgebraicGeometry.Scheme.exists_isPullback_pullbackSpec_of_isFinite_of_etale`).

This applies for instance to `A` the union of its finitely generated `R`-subalgebras, or to an
algebraic field extension, the union of its finite subextensions. We also record the case of the
local scheme `Z ×_X Spec 𝒪_{X,x}`, the limit of the preimages of the affine open neighbourhoods of
`x` (`AlgebraicGeometry.Scheme.exists_isPullback_preimage_of_isFinite_of_etale`).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {J : Type u} [SmallCategory J] {R : CommRingCat.{u}} {F : J ⥤ CommRingCat.{u}}
  (α : (Functor.const J).obj R ⟶ F) {X : Scheme.{u}} (h : X ⟶ Spec R)

lemma Scheme.specMap_comp_specMap_app {j j' : J} (f : j ⟶ j') :
    Spec.map (F.map f) ≫ Spec.map (α.app j) = Spec.map (α.app j') := by
  rw [← Spec.map_comp, ← α.naturality f]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The diagram `j ↦ X ×_{Spec R} Spec F(j)`. -/
@[simps]
noncomputable def Scheme.pullbackSpecDiagram : Jᵒᵖ ⥤ Scheme.{u} where
  obj j := pullback h (Spec.map (α.app j.unop))
  map {j j'} f := pullback.map h (Spec.map (α.app j.unop)) h (Spec.map (α.app j'.unop)) (𝟙 X)
    (Spec.map (F.map f.unop)) (𝟙 _) (by simp)
    (by rw [Category.comp_id, Scheme.specMap_comp_specMap_app])
  map_id j := by
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp f g := by
    apply pullback.hom_ext <;> simp [pullback.map]

/-- The projections `X ×_{Spec R} Spec F(j) ⟶ Spec F(j)`. -/
@[simps]
noncomputable def Scheme.pullbackSpecDiagramSnd :
    Scheme.pullbackSpecDiagram α h ⟶ F.op ⋙ Scheme.Spec where
  app _ := pullback.snd _ _
  naturality _ _ _ := pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.isPullback_pullbackMap {X₀ Y₁ Y₂ B : Scheme.{u}} (h : X₀ ⟶ B) (g₁ : Y₁ ⟶ B)
    (g₂ : Y₂ ⟶ B) (φ : Y₁ ⟶ Y₂) (hφ : φ ≫ g₂ = g₁) :
    IsPullback (pullback.map h g₁ h g₂ (𝟙 X₀) φ (𝟙 B) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hφ]))
      (pullback.snd h g₁) (pullback.snd h g₂) φ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst h g₂) (v₁₃ := h) (h₂₂ := g₂) ?_ ?_
    (IsPullback.of_hasPullback h g₂)
  · rw [pullback.lift_fst, Category.comp_id, hφ]
    exact IsPullback.of_hasPullback h g₁
  · exact pullback.lift_snd _ _ _

instance {j j' : Jᵒᵖ} (f : j ⟶ j') : IsAffineHom ((Scheme.pullbackSpecDiagram α h).map f) :=
  MorphismProperty.of_isPullback (Scheme.isPullback_pullbackMap h _ _ _
    (Scheme.specMap_comp_specMap_app α f.unop)).flip inferInstance

instance [CompactSpace X] (j : Jᵒᵖ) : CompactSpace ((Scheme.pullbackSpecDiagram α h).obj j) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst h (Spec.map (α.app j.unop)))
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback h _).flip inferInstance) _

instance [QuasiSeparatedSpace X] (j : Jᵒᵖ) :
    QuasiSeparatedSpace ((Scheme.pullbackSpecDiagram α h).obj j) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst h (Spec.map (α.app j.unop))) _
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback h _).flip inferInstance)

variable {c : Cocone F} (ρ : R ⟶ c.pt) (hρ : ∀ j, α.app j ≫ c.ι.app j = ρ)

set_option backward.isDefEq.respectTransparency false in
/-- The cone over `j ↦ X ×_{Spec R} Spec F(j)` with vertex `X ×_{Spec R} Spec A`. -/
@[simps]
noncomputable def Scheme.pullbackSpecCone : Cone (Scheme.pullbackSpecDiagram α h) where
  pt := pullback h (Spec.map ρ)
  π.app j := pullback.map h (Spec.map ρ) h (Spec.map (α.app j.unop)) (𝟙 X)
    (Spec.map (c.ι.app j.unop)) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp, hρ])
  π.naturality j j' f := by
    apply pullback.hom_ext
    · simp [pullback.map]
    · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        pullbackSpecDiagram_map, pullback.map, pullback.lift_snd, Category.assoc,
        pullback.lift_snd_assoc, ← Spec.map_comp, Cocone.w]

attribute [local instance] IsCofiltered.isConnected in
/-- EGA IV 8.2: `X ×_{Spec R} Spec A` is the limit of the `X ×_{Spec R} Spec F(j)` when
`A = colim F(j)`. -/
noncomputable def Scheme.isLimitPullbackSpecCone [IsFiltered J] (hc : IsColimit c) :
    IsLimit (Scheme.pullbackSpecCone α h ρ hρ) :=
  isLimitOfIsPullbackOfIsConnected (Scheme.pullbackSpecDiagramSnd α h)
    (Scheme.pullbackSpecCone α h ρ hρ) (Scheme.Spec.mapCone c.op)
    { hom := pullback.snd h (Spec.map ρ)
      w _ := (pullback.lift_snd _ _ _).symm }
    (fun j ↦ Scheme.isPullback_pullbackMap h _ _ _ (by rw [← Spec.map_comp, hρ]))
    (isLimitOfPreserves Scheme.Spec hc.op)

/-- EGA IV 8.8.2, 17.7.8: if `A = colim F(j)` is a filtered colimit of `R`-algebras and `X` is a
quasi-compact and quasi-separated scheme over `Spec R`, every finite étale
`X ×_{Spec R} Spec A`-scheme is the base change of a finite étale `X ×_{Spec R} Spec F(j)`-scheme
for some `j`. -/
theorem Scheme.exists_isPullback_pullbackSpec_of_isFinite_of_etale [IsFiltered J]
    (hc : IsColimit c) [CompactSpace X] [QuasiSeparatedSpace X] {Y : Scheme.{u}}
    (q : Y ⟶ pullback h (Spec.map ρ)) [IsFinite q] [Etale q] :
    ∃ (j : J) (Yj : Scheme.{u}) (qj : Yj ⟶ pullback h (Spec.map (α.app j))) (e : Y ⟶ Yj),
      IsFinite qj ∧ Etale qj ∧
        IsPullback e q qj ((Scheme.pullbackSpecCone α h ρ hρ).π.app (Opposite.op j)) := by
  let q' : Y ⟶ (Scheme.pullbackSpecCone α h ρ hρ).pt := q
  have : IsFinite q' := ‹IsFinite q›
  have : Etale q' := ‹Etale q›
  obtain ⟨j, Yj, qj, e, h₁, h₂, h₃⟩ := Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale
    (Scheme.isLimitPullbackSpecCone α h ρ hρ hc) q'
  exact ⟨j.unop, Yj, qj, e, h₁, h₂, h₃⟩

/-- EGA IV 8.8.2, 17.7.8 for the local scheme `Z ×_X Spec 𝒪_{X,x}`: for `p : Z ⟶ X`
quasi-compact and quasi-separated, every finite étale `Z ×_X Spec 𝒪_{X,x}`-scheme is the base
change of a finite étale scheme over `p⁻¹(U)` for some affine open neighbourhood `U` of `x`. -/
theorem Scheme.exists_isPullback_preimage_of_isFinite_of_etale {X Z : Scheme.{u}} (x : X)
    (p : Z ⟶ X) [QuasiCompact p] [QuasiSeparated p] {Y : Scheme.{u}}
    (q : Y ⟶ pullback p (X.fromSpecStalk x)) [IsFinite q] [Etale q] :
    ∃ (U : X.AffineNhds x) (YU : Scheme.{u}) (qU : YU ⟶ (p ⁻¹ᵁ U.1 : Scheme.{u}))
      (e : Y ⟶ YU), IsFinite qU ∧ Etale qU ∧
        IsPullback e q qU ((Scheme.preimageCone x p).π.app U) :=
  Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale (Scheme.isLimitPreimageCone x p) q

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5, 17.7.8 for étale coverings: let `p : Z ⟶ X` be quasi-compact, quasi-separated
and locally of finite presentation. If `Z ×_X Spec 𝒪_{X,x} ⟶ Spec 𝒪_{X,x}` is finite and étale,
then `p` is finite and étale over a neighbourhood of `x`. -/
theorem Scheme.exists_isFinite_etale_morphismRestrict {X Z : Scheme.{u}} (x : X) (p : Z ⟶ X)
    [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation p]
    [IsFinite (pullback.snd p (X.fromSpecStalk x))] [Etale (pullback.snd p (X.fromSpecStalk x))] :
    ∃ U : X.Opens, x ∈ U ∧ IsFinite (p ∣_ U) ∧ Etale (p ∣_ U) := by
  obtain ⟨j, Yj, qj, e, hqf, hqe, h₂⟩ := Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale
    (X.isLimitStalkCone x) (pullback.snd p (X.fromSpecStalk x))
  have h₁ : IsPullback ((Scheme.preimageCone x p).π.app j) (pullback.snd p (X.fromSpecStalk x))
      (p ∣_ j.1) ((X.stalkCone x).π.app j) := Scheme.isPullback_preimageCone_π_app x p j
  obtain ⟨k, θ, hθ, -⟩ := Scheme.exists_iso_of_isPullback (X.isLimitStalkCone x) h₁ h₂
  have hpb := (Scheme.isPullback_preimageDiagram_map x p k.hom).flip
  have hiso : p ∣_ k.left.1 = hpb.isoPullback.hom ≫ θ.hom ≫ pullback.snd qj
      ((X.affineNhdsDiagram x).map k.hom) := by
    rw [hθ, IsPullback.isoPullback_hom_snd]
  refine ⟨k.left.1, k.left.2.2, ?_, ?_⟩
  · rw [hiso]
    infer_instance
  · rw [hiso]
    infer_instance

end AlgebraicGeometry
