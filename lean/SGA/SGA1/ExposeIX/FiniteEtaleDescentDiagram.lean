/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.FundamentalGroupDescent

/-!
# SGA 1, Exposé IX, §5: the descent diagram of finite étale coverings

For `g : S' ⟶ S`, the categories of finite étale coverings of `S'`, `S'' = S' ×_S S'` and
`S''' = S'' ×_{S'} S''`, with the inverse image functors along the projections and the canonical
isomorphisms between iterated inverse images, form the diagram (*) of IX.5
(`fetDescentDiagram`). The inverse images along `g` carry canonical descent data
(`fetCanonicalDatum`), which satisfy the cocycle condition (`isCocycle_fetCanonicalDatum`); `g` is
an effective descent morphism for finite étale coverings when the resulting comparison functor is
an equivalence. With these, the abstract form of IX.5.6 describes `π₁(S)` as the cokernel of
`π₁(S'') ⇉ π₁(S')` (`fetQuotientRelationsEquiv`), for any fibre functors at compatible points
(the categories of étale coverings are Galois categories by V.7).

For the fibre functors of Exposé V at a geometric point `s'` of `S'` and its diagonal images the
compatibilities hold (`fetDiagonalPoint`, `isTrivialOn_fetDiagonalPoint`), which gives IX.5.6 for
the fundamental groups `π₁(S', s') → π₁(S, g(s'))` (`ker_etaleFundamentalGroup_map_eq_relations`,
`etaleFundamentalGroupQuotientRelationsEquiv`).
-/

universe u w

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PreGaloisCategory

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section

variable {C : Type*} [Category C] [HasPullbacks C]

/-- Morphisms into an iterated pullback `((X ×_S S') ×_{S'} T₂) ×_{T₂} T₃` are determined by their
components in `X` and `T₃`. -/
lemma hom_ext_pullback₃ {X S S' T₂ T₃ W : C} {x : X ⟶ S} {g : S' ⟶ S} {p : T₂ ⟶ S'}
    {q : T₃ ⟶ T₂} (a b : W ⟶ pullback (pullback.snd (pullback.snd x g) p) q)
    (hs : a ≫ pullback.snd _ q = b ≫ pullback.snd _ q)
    (h : a ≫ pullback.fst _ q ≫ pullback.fst _ p ≫ pullback.fst x g =
      b ≫ pullback.fst _ q ≫ pullback.fst _ p ≫ pullback.fst x g) : a = b := by
  have h₂ : a ≫ pullback.fst _ q ≫ pullback.snd _ p = b ≫ pullback.fst _ q ≫ pullback.snd _ p := by
    rw [pullback.condition, reassoc_of% hs]
  have h₁ : a ≫ pullback.fst _ q ≫ pullback.fst _ p ≫ pullback.snd x g =
      b ≫ pullback.fst _ q ≫ pullback.fst _ p ≫ pullback.snd x g := by
    rw [pullback.condition, reassoc_of% h₂]
  refine pullback.hom_ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_) hs
  · simpa only [Category.assoc] using h
  · simpa only [Category.assoc] using h₁
  · simpa only [Category.assoc] using h₂

end

section

variable {A B B' T T' : Scheme.{u}}

/-- The projection `p^* Y ⟶ Y` of the inverse image of a finite étale covering. -/
noncomputable abbrev fetProj (p : T ⟶ T') (Y : MorphismProperty.Over FEt ⊤ T') :
    ((pb p).obj Y).left ⟶ Y.left :=
  pullback.fst Y.hom p

@[reassoc]
lemma fetPullback_map_left_fetProj (p : T ⟶ T') {Y Z : MorphismProperty.Over FEt ⊤ T'} (φ : Y ⟶ Z) :
    ((pb p).map φ).left ≫ fetProj p Z = fetProj p Y ≫ φ.left :=
  pullback.lift_fst _ _ _

/-- For `a ≫ f = a' ≫ f'`, the canonical isomorphism `a^* f^* ≅ a'^* f'^*`. -/
noncomputable def fetPullbackCompCongr (f : B ⟶ T') (a : A ⟶ B) (f' : B' ⟶ T') (a' : A ⟶ B')
    (h : a ≫ f = a' ≫ f') : pb f ⋙ pb a ≅ pb f' ⋙ pb a' :=
  (MorphismProperty.Over.pullbackComp a f).symm ≪≫ MorphismProperty.Over.pullbackCongr h ≪≫
    MorphismProperty.Over.pullbackComp a' f'

@[reassoc]
lemma pullbackComp_hom_app_left_fetProj (a : A ⟶ B) (f : B ⟶ T')
    (Y : MorphismProperty.Over FEt ⊤ T') :
    ((MorphismProperty.Over.pullbackComp a f).hom.app Y).left ≫ fetProj a ((pb f).obj Y) ≫
      fetProj f Y = fetProj (a ≫ f) Y :=
  MorphismProperty.Over.pullbackComp_left_fst_fst a f Y

@[reassoc]
lemma pullbackComp_inv_app_left_fetProj (a : A ⟶ B) (f : B ⟶ T')
    (Y : MorphismProperty.Over FEt ⊤ T') :
    ((MorphismProperty.Over.pullbackComp a f).inv.app Y).left ≫ fetProj (a ≫ f) Y =
      fetProj a ((pb f).obj Y) ≫ fetProj f Y := by
  rw [← pullbackComp_hom_app_left_fetProj a f Y, ← Category.assoc,
    ← MorphismProperty.Comma.comp_left, Iso.inv_hom_id_app]
  exact Category.id_comp _

@[reassoc]
lemma pullbackCongr_hom_app_left_fetProj {a a' : T ⟶ T'} (h : a = a')
    (Y : MorphismProperty.Over FEt ⊤ T') :
    ((MorphismProperty.Over.pullbackCongr h).hom.app Y).left ≫ fetProj a' Y = fetProj a Y :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h Y

@[reassoc]
lemma fetPullbackCompCongr_hom_app_left_fetProj (f : B ⟶ T') (a : A ⟶ B) (f' : B' ⟶ T')
    (a' : A ⟶ B')
    (h : a ≫ f = a' ≫ f') (Y : MorphismProperty.Over FEt ⊤ T') :
    ((fetPullbackCompCongr f a f' a' h).hom.app Y).left ≫ fetProj a' ((pb f').obj Y) ≫
      fetProj f' Y = fetProj a ((pb f).obj Y) ≫ fetProj f Y := by
  simp only [fetPullbackCompCongr, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    MorphismProperty.Comma.comp_left]
  rw [Category.assoc, Category.assoc, pullbackComp_hom_app_left_fetProj,
    pullbackCongr_hom_app_left_fetProj, pullbackComp_inv_app_left_fetProj]

end

section

variable {S S' T₂ T₃ : Scheme.{u}}

/-- Morphisms into an iterated inverse image `q^* p^* g^* X` of finite étale coverings are
determined by their component in `X`. -/
lemma hom_ext_fetPullback₃ (g : S' ⟶ S) (p : T₂ ⟶ S') (q : T₃ ⟶ T₂)
    (X : MorphismProperty.Over FEt ⊤ S)
    {W : MorphismProperty.Over FEt ⊤ T₃} (φ ψ : W ⟶ (pb q).obj ((pb p).obj ((pb g).obj X)))
    (h : φ.left ≫ fetProj q _ ≫ fetProj p _ ≫ fetProj g X =
      ψ.left ≫ fetProj q _ ≫ fetProj p _ ≫ fetProj g X) :
    φ = ψ := by
  ext : 1
  exact hom_ext_pullback₃ φ.left ψ.left
    ((MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm) h

end

section

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- The first projection `S''' = S'' ×_{S'} S'' → S''`, onto the factors `1, 2`. -/
noncomputable abbrev tripleProj₂₁ : pullback (pullback.snd g g) (pullback.fst g g) ⟶ pullback g g :=
  pullback.fst _ _

/-- The second projection `S''' → S''`, onto the factors `2, 3`. -/
noncomputable abbrev tripleProj₃₂ : pullback (pullback.snd g g) (pullback.fst g g) ⟶ pullback g g :=
  pullback.snd _ _

/-- The projection `S''' → S''` onto the factors `1, 3`. -/
noncomputable abbrev tripleProj₃₁ : pullback (pullback.snd g g) (pullback.fst g g) ⟶ pullback g g :=
  pullback.lift (tripleProj₂₁ g ≫ pullback.fst g g) (tripleProj₃₂ g ≫ pullback.snd g g) (by
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      pullback.condition])

/-- The descent diagram of finite étale coverings attached to `g : S' ⟶ S`. -/
noncomputable abbrev fetDescentDiagram : DescentDiagram (MorphismProperty.Over FEt ⊤ S')
    (MorphismProperty.Over FEt ⊤ (pullback g g))
    (MorphismProperty.Over FEt ⊤ (pullback (pullback.snd g g) (pullback.fst g g))) where
  p₁ := pb (pullback.fst g g)
  p₂ := pb (pullback.snd g g)
  p₂₁ := pb (tripleProj₂₁ g)
  p₃₂ := pb (tripleProj₃₂ g)
  p₃₁ := pb (tripleProj₃₁ g)
  e₁ := fetPullbackCompCongr _ _ _ _ (pullback.lift_fst _ _ _).symm
  e₂ := fetPullbackCompCongr _ _ _ _
    (pullback.condition (f := pullback.snd g g) (g := pullback.fst g g))
  e₃ := fetPullbackCompCongr _ _ _ _ (pullback.lift_snd _ _ _)

/-- The canonical descent datum on inverse images of finite étale coverings of `S`. -/
noncomputable def fetCanonicalDatum :
    pb g ⋙ (fetDescentDiagram g).p₁ ≅ pb g ⋙ (fetDescentDiagram g).p₂ :=
  fetPullbackCompCongr _ _ _ _ (pullback.condition (f := g) (g := g))

/-- The canonical descent data on inverse images satisfy the cocycle condition. -/
lemma isCocycle_fetCanonicalDatum (X : MorphismProperty.Over FEt ⊤ S) :
    (fetDescentDiagram g).IsCocycle ((fetCanonicalDatum g).app X) := by
  apply hom_ext_fetPullback₃ g (pullback.snd g g) (tripleProj₃₂ g) X
  simp only [MorphismProperty.Comma.comp_left, fetDescentDiagram, fetCanonicalDatum,
    Iso.app_hom]
  simp only [Category.assoc]
  rw [fetPullback_map_left_fetProj_assoc, fetPullbackCompCongr_hom_app_left_fetProj,
    fetPullbackCompCongr_hom_app_left_fetProj_assoc,
    fetPullback_map_left_fetProj_assoc, fetPullbackCompCongr_hom_app_left_fetProj,
    fetPullbackCompCongr_hom_app_left_fetProj_assoc, fetPullback_map_left_fetProj_assoc,
    fetPullbackCompCongr_hom_app_left_fetProj,
    fetPullbackCompCongr_hom_app_left_fetProj_assoc]

end

section IX56

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- The comparison functor `X ↦ (g^* X, canonical descent datum)` of `g` for finite étale
coverings; `g` is a descent (resp. effective descent) morphism for finite étale coverings when it
is fully faithful (resp. an equivalence), cf. IX.3.3, IX.4.12. -/
noncomputable abbrev fetComparison :=
  (fetDescentDiagram g).comparison (pb g) (fetCanonicalDatum g) (isCocycle_fetCanonicalDatum g)

variable {F' : MorphismProperty.Over FEt ⊤ S' ⥤ FintypeCat.{w}}
  {F'' : MorphismProperty.Over FEt ⊤ (pullback g g) ⥤ FintypeCat.{w}}
  {F''' : MorphismProperty.Over FEt ⊤ (pullback (pullback.snd g g) (pullback.fst g g)) ⥤
    FintypeCat.{w}}
  [FiberFunctor F'] [FiberFunctor F''] [F'''.Faithful] [FiberFunctor (pb g ⋙ F')]
  (P : (fetDescentDiagram g).DiagonalPoint F' F'' F''')

omit [FiberFunctor (pb g ⋙ F')] in
/-- IX.5.6, the kernel: if `g` is an effective descent morphism for finite étale coverings and
`S''` is connected, the kernel of `π₁(S', s') → π₁(S, s)` is the closed normal subgroup generated
by the `p₁*(g'') p₂*(g'')⁻¹`, `g'' ∈ π₁(S'', Δ s')`. The fibre functors `F'`, `F''`, `F'''` are
taken at a geometric point `s'` of `S'` and at its diagonal images, with the identifications `P`
and `hP`. -/
theorem ker_autMap_pullback_eq_relations (hP : P.IsTrivialOn (pb g) (fetCanonicalDatum g))
    [(fetComparison g).EssSurj] :
    (autMap (pb g) F').ker = P.relations :=
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F'
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  P.ker_autMap_eq_relations (isCocycle_fetCanonicalDatum g) hP

/-- IX.5.6: if `g` is an effective descent morphism for finite étale coverings and `S'`, `S''` are
connected, then `π₁(S, s)` is the quotient of `π₁(S', s')` by the closed normal subgroup generated
by the `p₁*(g'') p₂*(g'')⁻¹`, `g'' ∈ π₁(S'', Δ s')`: the cokernel of `p₁*, p₂*` in the category of
profinite groups. -/
noncomputable def fetQuotientRelationsEquiv (hP : P.IsTrivialOn (pb g) (fetCanonicalDatum g))
    [(fetComparison g).IsEquivalence] :
    Aut F' ⧸ P.relations ≃ₜ* Aut (pb g ⋙ F') :=
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F'
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (pb g ⋙ F')
  P.quotientRelationsEquiv (isCocycle_fetCanonicalDatum g) hP

end IX56

section IX56Etale

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (Ω : Type u) [Field Ω] (s' : Spec (.of Ω) ⟶ S')

/-- The image `Δ s'` of a geometric point `s'` of `S'` under the diagonal `S' ⟶ S''`. -/
noncomputable def diagonalPoint₂ : Spec (.of Ω) ⟶ pullback g g :=
  pullback.lift s' s' rfl

/-- The image of a geometric point `s'` of `S'` under the diagonal `S' ⟶ S'''`. -/
noncomputable def diagonalPoint₃ :
    Spec (.of Ω) ⟶ pullback (pullback.snd g g) (pullback.fst g g) :=
  pullback.lift (diagonalPoint₂ g Ω s') (diagonalPoint₂ g Ω s') (by
    rw [diagonalPoint₂, pullback.lift_snd, pullback.lift_fst])

lemma diagonalPoint₂_fst : diagonalPoint₂ g Ω s' ≫ pullback.fst g g = s' :=
  pullback.lift_fst _ _ _

lemma diagonalPoint₂_snd : diagonalPoint₂ g Ω s' ≫ pullback.snd g g = s' :=
  pullback.lift_snd _ _ _

lemma diagonalPoint₃_proj₂₁ : diagonalPoint₃ g Ω s' ≫ tripleProj₂₁ g = diagonalPoint₂ g Ω s' :=
  pullback.lift_fst _ _ _

lemma diagonalPoint₃_proj₃₂ : diagonalPoint₃ g Ω s' ≫ tripleProj₃₂ g = diagonalPoint₂ g Ω s' :=
  pullback.lift_snd _ _ _

lemma diagonalPoint₃_proj₃₁ : diagonalPoint₃ g Ω s' ≫ tripleProj₃₁ g = diagonalPoint₂ g Ω s' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, diagonalPoint₃_proj₂₁]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, diagonalPoint₃_proj₃₂]

lemma assoc_eq_of_eq {C : Type*} [Category C] {W A B D D' E : C} (a : W ⟶ A) (e : A ⟶ B)
    (f₁ : B ⟶ D) (f₂ : D ⟶ E) (g₁ : A ⟶ D') (g₂ : D' ⟶ E) (h : e ≫ f₁ ≫ f₂ = g₁ ≫ g₂) :
    ((a ≫ e) ≫ f₁) ≫ f₂ = (a ≫ g₁) ≫ g₂ := by
  simp [h]

open SGA.SGA1.ExposeV

lemma fetDiagonalPoint_comm₁ (Y : MorphismProperty.Over FEt ⊤ S') :
    (FEt.fiber Ω (diagonalPoint₃ g Ω s')).map ((fetDescentDiagram g).e₁.hom.app Y) ≫
      (FEt.pullbackFiberIso Ω (tripleProj₃₁ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₃₁ g Ω s')).hom.app
          ((FEt.pullback (pullback.fst g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.fst g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_fst g Ω s')).hom.app Y =
    (FEt.pullbackFiberIso Ω (tripleProj₂₁ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₂₁ g Ω s')).hom.app
          ((FEt.pullback (pullback.fst g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.fst g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_fst g Ω s')).hom.app Y := by
  refine FintypeCat.hom_ext _ _ fun x ↦ FEt.fiber_ext_point Ω ?_
  simp only [ConcreteCategory.comp_apply, Iso.trans_hom, NatTrans.comp_app]
  rw [FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_pullbackFiberIso,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_map]
  exact assoc_eq_of_eq _ _ _ _ _ _ (fetPullbackCompCongr_hom_app_left_fetProj _ _ _ _ _ Y)

lemma fetDiagonalPoint_comm₂ (Y : MorphismProperty.Over FEt ⊤ S') :
    (FEt.fiber Ω (diagonalPoint₃ g Ω s')).map ((fetDescentDiagram g).e₂.hom.app Y) ≫
      (FEt.pullbackFiberIso Ω (tripleProj₃₂ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₃₂ g Ω s')).hom.app
          ((FEt.pullback (pullback.fst g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.fst g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_fst g Ω s')).hom.app Y =
    (FEt.pullbackFiberIso Ω (tripleProj₂₁ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₂₁ g Ω s')).hom.app
          ((FEt.pullback (pullback.snd g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.snd g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_snd g Ω s')).hom.app Y := by
  refine FintypeCat.hom_ext _ _ fun x ↦ FEt.fiber_ext_point Ω ?_
  simp only [ConcreteCategory.comp_apply, Iso.trans_hom, NatTrans.comp_app]
  rw [FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_pullbackFiberIso,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_map]
  exact assoc_eq_of_eq _ _ _ _ _ _ (fetPullbackCompCongr_hom_app_left_fetProj _ _ _ _ _ Y)

lemma fetDiagonalPoint_comm₃ (Y : MorphismProperty.Over FEt ⊤ S') :
    (FEt.fiber Ω (diagonalPoint₃ g Ω s')).map ((fetDescentDiagram g).e₃.hom.app Y) ≫
      (FEt.pullbackFiberIso Ω (tripleProj₃₂ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₃₂ g Ω s')).hom.app
          ((FEt.pullback (pullback.snd g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.snd g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_snd g Ω s')).hom.app Y =
    (FEt.pullbackFiberIso Ω (tripleProj₃₁ g) (diagonalPoint₃ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₃_proj₃₁ g Ω s')).hom.app
          ((FEt.pullback (pullback.snd g g)).obj Y) ≫
      (FEt.pullbackFiberIso Ω (pullback.snd g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_snd g Ω s')).hom.app Y := by
  refine FintypeCat.hom_ext _ _ fun x ↦ FEt.fiber_ext_point Ω ?_
  simp only [ConcreteCategory.comp_apply, Iso.trans_hom, NatTrans.comp_app]
  rw [FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_pullbackFiberIso,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_map]
  exact assoc_eq_of_eq _ _ _ _ _ _ (fetPullbackCompCongr_hom_app_left_fetProj _ _ _ _ _ Y)

/-- IX.5: the fibre functors of Exposé V at a geometric point `s'` of `S'` and at its diagonal
images in `S''` and `S'''`, identified by base change. With these choices the classes of paths
of IX.5 are trivial. -/
noncomputable def fetDiagonalPoint :
    (fetDescentDiagram g).DiagonalPoint (FEt.fiber Ω s') (FEt.fiber Ω (diagonalPoint₂ g Ω s'))
      (FEt.fiber Ω (diagonalPoint₃ g Ω s')) where
  d₁ := FEt.pullbackFiberIso Ω (pullback.fst g g) _ ≪≫ FEt.fiberCongr Ω (diagonalPoint₂_fst g Ω s')
  d₂ := FEt.pullbackFiberIso Ω (pullback.snd g g) _ ≪≫ FEt.fiberCongr Ω (diagonalPoint₂_snd g Ω s')
  d₂₁ := FEt.pullbackFiberIso Ω (tripleProj₂₁ g) _ ≪≫
    FEt.fiberCongr Ω (diagonalPoint₃_proj₂₁ g Ω s')
  d₃₂ := FEt.pullbackFiberIso Ω (tripleProj₃₂ g) _ ≪≫
    FEt.fiberCongr Ω (diagonalPoint₃_proj₃₂ g Ω s')
  d₃₁ := FEt.pullbackFiberIso Ω (tripleProj₃₁ g) _ ≪≫
    FEt.fiberCongr Ω (diagonalPoint₃_proj₃₁ g Ω s')
  comm₁ := fetDiagonalPoint_comm₁ g Ω s'
  comm₂ := fetDiagonalPoint_comm₂ g Ω s'
  comm₃ := fetDiagonalPoint_comm₃ g Ω s'

lemma fetDiagonalPoint_trivial (X : MorphismProperty.Over FEt ⊤ S) :
    (FEt.fiber Ω (diagonalPoint₂ g Ω s')).map ((fetCanonicalDatum g).hom.app X) ≫
      (FEt.pullbackFiberIso Ω (pullback.snd g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_snd g Ω s')).hom.app ((FEt.pullback g).obj X) =
    (FEt.pullbackFiberIso Ω (pullback.fst g g) (diagonalPoint₂ g Ω s') ≪≫
        FEt.fiberCongr Ω (diagonalPoint₂_fst g Ω s')).hom.app ((FEt.pullback g).obj X) := by
  refine FintypeCat.hom_ext _ _ fun x ↦ FEt.fiber_ext_pullback Ω g ?_
  simp only [ConcreteCategory.comp_apply, Iso.trans_hom, NatTrans.comp_app]
  rw [FEt.fiberPoint_fiberCongr, FEt.fiberPoint_fiberCongr, FEt.fiberPoint_pullbackFiberIso,
    FEt.fiberPoint_pullbackFiberIso, FEt.fiberPoint_map]
  exact assoc_eq_of_eq _ _ _ _ _ _ (fetPullbackCompCongr_hom_app_left_fetProj _ _ _ _ _ X)

/-- At the diagonal point, the canonical descent data of inverse images of étale coverings are
the identity on fibres. -/
lemma isTrivialOn_fetDiagonalPoint :
    (fetDiagonalPoint g Ω s').IsTrivialOn (pb g) (fetCanonicalDatum g) :=
  fetDiagonalPoint_trivial g Ω s'

variable [IsSepClosed Ω] [ConnectedSpace S'] [ConnectedSpace ↥(pullback g g)]
  [ConnectedSpace ↥(pullback (pullback.snd g g) (pullback.fst g g))]

/-- IX.5.6, the kernel, for the fundamental groups of Exposé V: if `g : S' ⟶ S` is an effective
descent morphism for étale coverings and `S'`, `S''`, `S'''` are connected, the kernel of
`π₁(S', s') → π₁(S, g(s'))` is the closed normal subgroup generated by the elements
`p₁*(h) p₂*(h)⁻¹`, `h ∈ π₁(S'', Δ s')`. (SGA assumes only `S'` and `S''` connected; the
connectedness of `S'''` is used to compare descent data on a single fibre.) -/
theorem ker_etaleFundamentalGroup_map_eq_relations [(fetComparison g).EssSurj] :
    (etaleFundamentalGroup.map Ω g s').ker = (fetDiagonalPoint g Ω s').relations := by
  rw [← ker_autMap_pullback_eq_relations g (fetDiagonalPoint g Ω s')
    (isTrivialOn_fetDiagonalPoint g Ω s'), etaleFundamentalGroup.map, autMap_eq_conjAut_comp]
  ext σ
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, MulEquiv.map_eq_one_iff]

/-- The isomorphism `Aut (g^• ⋙ F_{s'}) ≃ₜ* π₁(S, g(s'))` given by base change. -/
noncomputable def autPullbackFiberContinuousMulEquiv :
    Aut (pb g ⋙ FEt.fiber Ω s') ≃ₜ* etaleFundamentalGroup Ω (s' ≫ g) :=
  { (FEt.pullbackFiberIso Ω g s').conjAut with
    continuous_toFun := continuous_conjAut _
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (FEt.pullbackFiberIso Ω g s').conjAut.toEquiv) (continuous_conjAut _) }

/-- IX.5.6 for the fundamental groups of Exposé V: if `g : S' ⟶ S` is an effective descent
morphism for étale coverings and `S'`, `S''`, `S'''` are connected (hence `S` too), then
`π₁(S, g(s'))` is the quotient of `π₁(S', s')` by the closed normal subgroup generated by the
`p₁*(h) p₂*(h)⁻¹`, `h ∈ π₁(S'', Δ s')`: the cokernel of `π₁(S'') ⇉ π₁(S')` in profinite
groups. -/
noncomputable def etaleFundamentalGroupQuotientRelationsEquiv [ConnectedSpace S]
    [(fetComparison g).IsEquivalence] :
    etaleFundamentalGroup Ω s' ⧸ (fetDiagonalPoint g Ω s').relations ≃ₜ*
      etaleFundamentalGroup Ω (s' ≫ g) :=
  have : FiberFunctor (pb g ⋙ FEt.fiber Ω s') :=
    fiberFunctor_of_iso (FEt.pullbackFiberIso Ω g s').symm
  (fetQuotientRelationsEquiv g (fetDiagonalPoint g Ω s')
    (isTrivialOn_fetDiagonalPoint g Ω s')).trans (autPullbackFiberContinuousMulEquiv g Ω s')

end IX56Etale

end SGA.SGA1.ExposeIX
