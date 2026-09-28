/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.QuotientEtale
import SGA.SGA1.ExposeV.SchemeGaloisCategory

/-!
# SGA 1, Exposé V: quotients of étale coverings by finite groups (V.3.4, (G 2) of V.7)

Let `S` be any scheme, `X` an étale covering of `S` (finite étale) and `G` a finite group
acting on `X` by `S`-automorphisms. The quotient `X/G = Spec_S (f_* 𝒪_X)^G` of Cor. V.1.8
(`RelativeQuotient.lean`) is again an étale covering:

* `finite_etale_fromQuotient` (V.3.4 for any base, in `QuotientEtale.lean`): `X/G` is finite
  étale over `S`.
* `fetQuotientCoconeIsColimit`: `X ⟶ X/G` is a quotient in the category `FEt S` of étale
  coverings, so `FEt S` has quotients by finite groups.
* `nonempty_isColimit_geometricPoints_mapCocone`: for a geometric point `s̄ : Spec Ω ⟶ S` with
  `Ω` separably closed, the geometric points of `X/G` over `s̄` are the `G`-orbits of those of
  `X` (`exists_geometricPoint_lift_of_isSeparable`, `exists_comp_eq_of_comp_eq`).
* `FEt.hasQuotients`: every scheme satisfies the axiom (G 2) for quotients, which completes the
  proof that `FEt S` is a Galois category for connected `S` (`FEt.galoisCategory`);
  `FEt.hasQuotientsStatement` proves `FEt.HasQuotientsStatement`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section FEtQuotient

variable {S : Scheme.{u}} {G : Type u} [Group G] (K : SingleObj G ⥤ FEt S)

/-- The right action of `G` on the étale covering `K(⋆)`: `g` acts by `K(g⁻¹)`. -/
noncomputable def fetAction (g : G) :
    (K.obj (SingleObj.star G)).left ⟶ (K.obj (SingleObj.star G)).left :=
  (K.map (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)).left

lemma isRightAction_fetAction : IsRightAction (fetAction K) where
  map_one := by
    rw [fetAction, inv_one, ← SingleObj.id_as_one, K.map_id]
    rfl
  map_mul g h := by
    rw [fetAction, fetAction, fetAction, mul_inv_rev, ← SingleObj.comp_as_mul, K.map_comp]
    rfl

lemma fetAction_comp (g : G) :
    fetAction K g ≫ (K.obj (SingleObj.star G)).hom = (K.obj (SingleObj.star G)).hom :=
  MorphismProperty.Over.w _

variable [Finite G]

instance : IsFinite (K.obj (SingleObj.star G)).hom := (K.obj (SingleObj.star G)).prop.1
instance : Etale (K.obj (SingleObj.star G)).hom := (K.obj (SingleObj.star G)).prop.2

/-- The quotient `X/G` of the étale covering `X = K(⋆)`, as an étale covering (V.3.4). -/
noncomputable def fetQuotient : FEt S :=
  MorphismProperty.Over.mk ⊤ (fromQuotient (fetAction_comp K))
    (finite_etale_fromQuotient (isRightAction_fetAction K) (fetAction_comp K))

/-- The quotient morphism `X ⟶ X/G` in `FEt S`. -/
noncomputable def fetQuotientι : K.obj (SingleObj.star G) ⟶ fetQuotient K :=
  MorphismProperty.Over.homMk (toQuotient (fetAction_comp K)) (toQuotient_fromQuotient _)

lemma isQuotient_fetQuotientι :
    IsQuotient (fun g : G ↦ (K.map (g : SingleObj.star G ⟶ SingleObj.star G)).left)
      (fetQuotientι K).left := by
  have h := isQuotient_toQuotient (fetAction_comp K) (isRightAction_fetAction K)
  have hK : ∀ g : G, (K.map (g : SingleObj.star G ⟶ SingleObj.star G)).left = fetAction K g⁻¹ :=
    fun g ↦ by rw [fetAction, inv_inv]
  refine ⟨fun g ↦ by rw [hK]; exact h.comp_eq _, fun f hf ↦ h.existsUnique f fun g ↦ ?_⟩
  rw [fetAction, ← inv_inv g, inv_inv g⁻¹]
  exact hf _

/-- The cocone `X ⟶ X/G` in `FEt S`. -/
noncomputable def fetQuotientCocone : Cocone K where
  pt := fetQuotient K
  ι :=
    { app _ := fetQuotientι K
      naturality _ _ g := by
        ext
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact (isQuotient_fetQuotientι K).comp_eq g }

/-- V.1, V.3.4: the quotient `X/G` of an étale covering by a finite group is a colimit in the
category of étale coverings of `S`, for any scheme `S`. -/
noncomputable def fetQuotientCoconeIsColimit : IsColimit (fetQuotientCocone K) := by
  have hq := isQuotient_fetQuotientι K
  have hw : ∀ (s : Cocone K) (g : G),
      (K.map (g : SingleObj.star G ⟶ SingleObj.star G)).left ≫ (s.ι.app (SingleObj.star G)).left =
        (s.ι.app (SingleObj.star G)).left := fun s g ↦ by
    exact congr_arg (fun m ↦ m.left) (s.w (j := SingleObj.star G) (j' := SingleObj.star G) g)
  have hover : ∀ s : Cocone K, hq.desc _ (hw s) ≫ s.pt.hom = (fetQuotient K).hom := fun s ↦
    hq.hom_ext (by
      rw [hq.fac_assoc, MorphismProperty.Over.w]
      exact MorphismProperty.Over.w _)
  refine
    { desc s := MorphismProperty.Over.homMk (hq.desc _ (hw s)) (hover s)
      fac s j := ?_
      uniq s m hm := ?_ }
  · obtain rfl : j = SingleObj.star G := rfl
    ext
    exact hq.fac _ (hw s)
  · apply MorphismProperty.Over.Hom.ext
    refine hq.hom_ext ?_
    have := congr_arg (fun m ↦ m.left) (hm (SingleObj.star G))
    exact this.trans (hq.fac _ (hw s)).symm

instance FEt.hasColimitsOfShape_singleObj : HasColimitsOfShape (SingleObj G) (FEt S) :=
  ⟨fun K ↦ ⟨⟨⟨_, fetQuotientCoconeIsColimit K⟩⟩⟩⟩

section Fiber

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

omit [Finite G] in
lemma fetAction_eq (g : G) :
    (K.map (g : SingleObj.star G ⟶ SingleObj.star G)).left = fetAction K g⁻¹ := by
  rw [fetAction, inv_inv]

/-- V.7, (G 5) for quotients: the geometric points of `X/G` over `s̄` are the `G`-orbits of those
of `X` (`Ω` separably closed). -/
lemma nonempty_isColimit_geometricPoints_mapCocone :
    Nonempty (IsColimit ((geometricPoints s).mapCocone (fetQuotientCocone K))) := by
  let X := K.obj (SingleObj.star G)
  have hT := isRightAction_fetAction K
  have hTf := fetAction_comp K
  let p := toQuotient hTf
  let q := fromQuotient hTf
  have hpq : p ≫ q = X.hom := toQuotient_fromQuotient hTf
  have hsec : ∀ U, SectionsAreInvariant (fetAction K) p (comp_toQuotient hTf) U :=
    sectionsAreInvariant_toQuotient hTf
  refine nonempty_isColimit_singleObj _ (fun z ↦ ?_) (fun x y hxy ↦ ?_)
  · -- lifting geometric points along `X ⟶ X/G`
    let z' : Over.mk s ⟶ Over.mk q := z
    have hz : z'.left ≫ q = s := Over.w z'
    have hsurj := surjective_of_sectionsAreInvariant hT (comp_toQuotient hTf)
      (fun U _ ↦ hsec U) (p := p)
    obtain ⟨x₀, hx₀⟩ := hsurj.surj (z'.left (IsLocalRing.closedPoint Ω))
    have : Etale (p ≫ q) := by rw [hpq]; infer_instance
    obtain ⟨x', hx', -⟩ := exists_geometricPoint_lift_of_isSeparable p z'.left x₀ hx₀
      (isSeparable_residueFieldMap_of_etale_comp p q x₀)
    let x : (geometricPoints s).obj X := Over.homMk x' (by
      change x' ≫ X.hom = s
      rw [← hpq, ← Category.assoc, hx', hz])
    refine ⟨x, ?_⟩
    apply Over.OverMorphism.ext
    exact hx'
  · -- two geometric points of `X` with the same image in `X/G` are conjugate
    let x' : Over.mk s ⟶ Over.mk X.hom := x
    let y' : Over.mk s ⟶ Over.mk X.hom := y
    have h : x'.left ≫ p = y'.left ≫ p := congr_arg (fun m ↦ m.left) hxy
    obtain ⟨g, hg⟩ := exists_comp_eq_of_comp_eq hT (comp_toQuotient hTf) hsec x'.left y'.left h
    refine ⟨g⁻¹, ?_⟩
    apply Over.OverMorphism.ext
    change x'.left ≫ (K.map _).left = y'.left
    rw [fetAction_eq, inv_inv, hg]

instance : PreservesColimitsOfShape (SingleObj G) (geometricPoints s) where
  preservesColimit {K} := preservesColimit_of_preserves_colimit_cocone
    (fetQuotientCoconeIsColimit K) (nonempty_isColimit_geometricPoints_mapCocone K Ω s).some

/-- V.7, (G 5) for quotients: the fiber functor at a geometric point commutes with quotients by
finite groups. -/
instance FEt.preservesColimitsOfShape_singleObj_fiber :
    PreservesColimitsOfShape (SingleObj G) (FEt.fiber Ω s) := by
  have : PreservesColimitsOfShape (SingleObj G) (FEt.fiber Ω s ⋙ FintypeCat.incl) :=
    preservesColimitsOfShape_of_natIso (FEt.fiberInclIso Ω s).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (FEt.fiber Ω s) FintypeCat.incl

end Fiber

end FEtQuotient

/-- V.1, V.3.4, V.7 (G 2): the étale coverings of any scheme have quotients by finite groups,
and the fiber functors at geometric points commute with them. -/
instance FEt.hasQuotients (S : Scheme.{u}) : FEt.HasQuotients S where
  hasColimitsOfShape _ _ _ := inferInstance
  preservesColimitsOfShape _ _ _ _ _ _ _ := inferInstance

/-- (G 2) for quotients holds for every scheme. -/
theorem FEt.hasQuotientsStatement : FEt.HasQuotientsStatement.{u} := fun S ↦ FEt.hasQuotients S

end SGA.SGA1.ExposeV
