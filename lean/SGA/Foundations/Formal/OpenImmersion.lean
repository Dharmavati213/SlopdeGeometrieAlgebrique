/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion
import SGA.Foundations.Formal.FormalColimit

/-!
# Open immersions between formal colimits

Let `G ⟶ F` be a morphism of thickening sequences of schemes whose components `Gₙ ⟶ Fₙ` are open
immersions. Then the induced morphism `lim→ Gₙ ⟶ lim→ Fₙ` of formal schemes is an open
immersion (EGA I, §10.6). The sections of `lim→ Fₙ` over an open `V` are `lim← Γ(Fₙ, V)`
(`PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit`), and the components
`Γ(Fₙ, V) → Γ(Gₙ, V)` are isomorphisms for `V` in the image of `Gₙ`.

In particular the restriction of a formal scheme `lim→ Fₙ` to an open subset is the formal
colimit of the restrictions of the `Fₙ`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.PresheafedSpace

variable {D D' : ℕ ⥤ PresheafedSpace.{_, _, u} CommRingCat.{u}}

/-- In a diagram of presheafed spaces whose transition maps are homeomorphisms, the maps to the
colimit are homeomorphisms. -/
lemma isIso_forget_map_colimit_ι
    (hD : ∀ {i j : ℕ} (f : i ⟶ j), IsIso ((D ⋙ PresheafedSpace.forget _).map f)) (n : ℕ) :
    IsIso ((PresheafedSpace.forget _).map (colimit.ι D n)) := by
  let H := PresheafedSpace.forget CommRingCat.{u}
  have h₀ : IsIso (colimit.ι (D ⋙ H) 0) := isIso_ι_of_isInitial isInitialBot _
  have hn : IsIso (colimit.ι (D ⋙ H) n) := by
    rw [← colimit.w (D ⋙ H) (homOfLE (Nat.zero_le n))] at h₀
    exact IsIso.of_isIso_comp_left ((D ⋙ H).map (homOfLE (Nat.zero_le n))) _
  rw [← ι_preservesColimitIso_inv H D n]
  infer_instance


variable {D D' : ℕ ⥤ PresheafedSpace.{_, _, u} CommRingCat.{u}} (β : D' ⟶ D)

lemma map_ι_colimMap_obj (V : Opens (Limits.colimit D).carrier) (j : ℕ) :
    (Opens.map (β.app j).base).obj ((Opens.map (colimit.ι D j).base).obj V) =
      (Opens.map (colimit.ι D' j).base).obj ((Opens.map (colimMap β).base).obj V) := by
  rw [← Opens.map_comp_obj, ← Opens.map_comp_obj, ← comp_base, ← comp_base, ι_colimMap]

set_option backward.isDefEq.respectTransparency false in
/-- The components `Γ(D j, V) ⟶ Γ(D' j, β⁻¹ V)` of a morphism of diagrams, on the componentwise
diagrams computing the sections of the colimits. -/
noncomputable def componentwiseMap (V : Opens (Limits.colimit D).carrier) :
    componentwiseDiagram D V ⟶ componentwiseDiagram D' ((Opens.map (colimMap β).base).obj V) where
  app j := (β.app (unop j)).c.app (op ((Opens.map (colimit.ι D (unop j)).base).obj V)) ≫
    (D'.obj (unop j)).presheaf.map (eqToHom (congr_arg op (map_ι_colimMap_obj β V (unop j))))
  naturality {j k} f := by
    have h := congr_app (β.naturality f.unop) (op ((Opens.map (colimit.ι D (unop j)).base).obj V))
    simp only [comp_c_app] at h
    dsimp [componentwiseDiagram]
    simp only [Category.assoc]
    erw [(β.app (unop k)).c.naturality_assoc, (D'.map f.unop).c.naturality_assoc]
    rw [reassoc_of% h]
    simp only [TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp]
    congr 3

set_option backward.isDefEq.respectTransparency false in
lemma colimMap_c_app (V : Opens (Limits.colimit D).carrier) :
    (colimMap β).c.app (op V) = (colimitPresheafObjIsoComponentwiseLimit D V).hom ≫
      limMap (componentwiseMap β V) ≫
        (colimitPresheafObjIsoComponentwiseLimit D' ((Opens.map (colimMap β).base).obj V)).inv := by
  rw [← cancel_mono (colimitPresheafObjIsoComponentwiseLimit D' _).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine limit.hom_ext fun j ↦ ?_
  rw [Category.assoc, Category.assoc, limMap_π, colimitPresheafObjIsoComponentwiseLimit_hom_π,
    ← Category.assoc (colimitPresheafObjIsoComponentwiseLimit D V).hom,
    colimitPresheafObjIsoComponentwiseLimit_hom_π, componentwiseMap]
  have h := congr_app (ι_colimMap β (unop j)) (op V)
  rw [comp_c_app, comp_c_app] at h
  rw [h, Category.assoc]

lemma colimMap_base_apply {n : ℕ} (x : D'.obj n) :
    (colimMap β).base ((colimit.ι D' n).base x) = (colimit.ι D n).base ((β.app n).base x) := by
  rw [← TopCat.comp_app, ← comp_base, ι_colimMap, comp_base, TopCat.comp_app]

variable (hD : ∀ {i j : ℕ} (f : i ⟶ j), IsIso ((D ⋙ PresheafedSpace.forget _).map f))
  (hD' : ∀ {i j : ℕ} (f : i ⟶ j), IsIso ((D' ⋙ PresheafedSpace.forget _).map f))
include hD hD'

/-- A morphism of diagrams of open immersions between diagrams of homeomorphisms induces an open
immersion of the colimits (EGA I, §10.6). -/
theorem isOpenImmersion_colimMap [∀ j, PresheafedSpace.IsOpenImmersion (β.app j)] :
    PresheafedSpace.IsOpenImmersion (colimMap β) := by
  have h₀ := isIso_forget_map_colimit_ι hD
  have h₀' := isIso_forget_map_colimit_ι hD'
  let e (n : ℕ) := TopCat.homeoOfIso (asIso ((PresheafedSpace.forget _).map (colimit.ι D n)))
  let e' (n : ℕ) := TopCat.homeoOfIso (asIso ((PresheafedSpace.forget _).map (colimit.ι D' n)))
  have hbase : ⇑(colimMap β).base = e 0 ∘ (β.app 0).base ∘ (e' 0).symm := by
    ext x
    obtain ⟨y, rfl⟩ := (e' 0).surjective x
    change _ = (e 0) ((β.app 0).base ((e' 0).symm ((e' 0) y)))
    rw [Homeomorph.symm_apply_apply]
    exact colimMap_base_apply β y
  have hopen : Topology.IsOpenEmbedding (colimMap β).base := by
    rw [hbase]
    exact (e 0).isOpenEmbedding.comp
      ((PresheafedSpace.IsOpenImmersion.base_open (f := β.app 0)).comp (e' 0).symm.isOpenEmbedding)
  refine ⟨hopen, fun U ↦ ?_⟩
  rw [colimMap_c_app]
  have hτ (j : ℕᵒᵖ) : IsIso ((componentwiseMap β (hopen.functor.obj U)).app j) := by
    have hW : (Opens.map (colimit.ι D (unop j)).base).obj (hopen.functor.obj U) =
        (PresheafedSpace.IsOpenImmersion.base_open (f := β.app (unop j))).functor.obj
          ((Opens.map (colimit.ι D' (unop j)).base).obj U) := by
      ext x
      simp only [Opens.map_coe, IsOpenMap.coe_functor_obj, Set.mem_preimage, Set.mem_image,
        SetLike.mem_coe]
      constructor
      · rintro ⟨u, hu, hux⟩
        obtain ⟨y, rfl⟩ := (e' (unop j)).surjective u
        refine ⟨y, hu, (e (unop j)).injective ?_⟩
        exact (colimMap_base_apply β y).symm.trans hux
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, hy, colimMap_base_apply β y⟩
    have : IsIso ((β.app (unop j)).c.app
        (op ((Opens.map (colimit.ι D (unop j)).base).obj (hopen.functor.obj U)))) := by
      rw [hW]
      infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this
      ((D'.obj (unop j)).presheaf.mapIso
        (eqToIso (congr_arg op (map_ι_colimMap_obj β _ (unop j))))).isIso_hom
  have : IsIso (componentwiseMap β (hopen.functor.obj U)) := NatIso.isIso_of_isIso_app _
  infer_instance

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.Scheme

open PresheafedSpace

variable {F G : ℕ ⥤ Scheme.{u}} (α : G ⟶ F)

/-- The morphism `lim→ Gₙ ⟶ lim→ Fₙ` of formal colimits induced by `α : G ⟶ F`. -/
noncomputable def formalColimit.map : formalColimit G ⟶ formalColimit F :=
  colimMap (Functor.whiskerRight α Scheme.forgetToLocallyRingedSpace)

@[reassoc (attr := simp)]
lemma formalColimit.ι_map (n : ℕ) :
    formalColimit.ι G n ≫ formalColimit.map α = (α.app n).toLRSHom ≫ formalColimit.ι F n :=
  ι_colimMap _ n

@[simp]
lemma formalColimit.map_id : formalColimit.map (𝟙 F) = 𝟙 (formalColimit F) := by
  refine formalColimit.hom_ext _ fun n ↦ ?_
  rw [formalColimit.ι_map, NatTrans.id_app, Category.comp_id]
  exact Category.id_comp _

@[reassoc (attr := simp)]
lemma formalColimit.map_comp {H : ℕ ⥤ Scheme.{u}} (β : H ⟶ G) :
    formalColimit.map β ≫ formalColimit.map α = formalColimit.map (β ≫ α) := by
  refine formalColimit.hom_ext _ fun n ↦ ?_
  rw [formalColimit.ι_map_assoc, formalColimit.ι_map, formalColimit.ι_map, NatTrans.comp_app,
    Scheme.Hom.comp_toLRSHom, Category.assoc]

instance : PreservesColimitsOfShape ℕ
    (LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  inferInstance

/-- A morphism of thickening sequences whose components are open immersions induces an open
immersion of the formal colimits (EGA I, §10.6). -/
theorem formalColimit.isOpenImmersion_map [IsThickeningSequence F] [IsThickeningSequence G]
    [∀ n, IsOpenImmersion (α.app n)] :
    LocallyRingedSpace.IsOpenImmersion (formalColimit.map α) := by
  let P := LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forgetToPresheafedSpace
  let ℱ := F ⋙ Scheme.forgetToLocallyRingedSpace
  let 𝒢 := G ⋙ Scheme.forgetToLocallyRingedSpace
  let β := Functor.whiskerRight (Functor.whiskerRight α Scheme.forgetToLocallyRingedSpace) P
  have hβ (j : ℕ) : PresheafedSpace.IsOpenImmersion (β.app j) :=
    inferInstanceAs (PresheafedSpace.IsOpenImmersion (α.app j).toLRSHom.toHom)
  have hF {i j : ℕ} (f : i ⟶ j) : IsIso ((ℱ ⋙ P ⋙ PresheafedSpace.forget _).map f) :=
    IsThickeningSequence.isIso_forgetToTop_map F f
  have hG {i j : ℕ} (f : i ⟶ j) : IsIso ((𝒢 ⋙ P ⋙ PresheafedSpace.forget _).map f) :=
    IsThickeningSequence.isIso_forgetToTop_map G f
  have := isOpenImmersion_colimMap β hF hG
  have key : P.map (colimMap (Functor.whiskerRight α Scheme.forgetToLocallyRingedSpace)) =
      (preservesColimitIso P 𝒢).hom ≫ colimMap β ≫ (preservesColimitIso P ℱ).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    refine (isColimitOfPreserves P (colimit.isColimit 𝒢)).hom_ext fun j ↦ ?_
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp_assoc]
    erw [ι_colimMap, ι_preservesColimitIso_hom_assoc, ι_colimMap]
    rw [Functor.map_comp_assoc, ι_preservesColimitIso_hom]
    rfl
  change PresheafedSpace.IsOpenImmersion
    (P.map (colimMap (Functor.whiskerRight α Scheme.forgetToLocallyRingedSpace)))
  rw [key]
  infer_instance

end AlgebraicGeometry.Scheme
