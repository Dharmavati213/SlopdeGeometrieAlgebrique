/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé V, §7: the fundamental group of an étale covering

V.7: let `g : S' ⟶ S` be an étale covering, `a'` a geometric point of `S'` and `a = g(a')`.
Then `u = π₁(g; a') : π₁(S', a') → π₁(S, a)` is an isomorphism of `π₁(S', a')` onto the
stabilizer `U` of `a' ∈ F_a(S')`, an open subgroup of `π₁(S, a)`
(`etaleFundamentalGroup.injective_map_and_range_eq_stabilizer`).

SGA deduces this from V.6.13. We argue directly, which needs no connectedness hypothesis. The
functor `g_! : FEt S' ⥤ FEt S` (composition with `g`) is left adjoint to `g^•`, and the fibre
`F_{a'}(Y)` of an étale covering `Y` of `S'` is the part of `F_a(g_! Y)` lying over
`a' ∈ F_a(S')`. The abstract statement is `injective_autMap_and_range_eq_stabilizer`: an
automorphism of `F_a` fixing `a'` restricts to these subsets (`autOfFixes`).
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

section Adjunction

variable {C C' : Type*} [Category C] [Category C'] {F : C ⥤ FintypeCat.{w}}
  {F' : C' ⥤ FintypeCat.{w}} {G : C' ⥤ C} {H : C ⥤ C'}

lemma autMap_hom_app_iso_hom_apply (e : H ⋙ F' ≅ F) (σ : Aut F') (X : C)
    (x : F'.obj (H.obj X)) :
    (autMap H e σ).hom.app X (e.hom.app X x) = e.hom.app X (σ.hom.app (H.obj X) x) := by
  rw [autMap_hom_app, FintypeCat.comp_apply, FintypeCat.comp_apply]
  congr 2
  exact FintypeCat.hom_inv_id_apply (e.app X) x

variable (adj : G ⊣ H) (ι : F' ⟶ G ⋙ F) (e : H ⋙ F' ≅ F)
  (he : ∀ X (x : F'.obj (H.obj X)), e.hom.app X x = F.map (adj.counit.app X) (ι.app (H.obj X) x))

include he

/-- `ι_Y(y)` is the image of `η_Y(y) ∈ F'(H G Y)` under `e : F'(H G Y) ≅ F(G Y)`. -/
lemma ι_app_eq_iso_hom (Y : C') (y : F'.obj Y) :
    ι.app Y y = e.hom.app (G.obj Y) (F'.map (adj.unit.app Y) y) := by
  rw [he, FunctorToFintypeCat.naturality]
  change ι.app Y y = F.map (adj.counit.app (G.obj Y)) (F.map (G.map (adj.unit.app Y)) (ι.app Y y))
  rw [← FintypeCat.comp_apply, ← F.map_comp]
  simp

lemma ι_app_hom_app (σ : Aut F') (Y : C') (y : F'.obj Y) :
    ι.app Y (σ.hom.app Y y) = (autMap H e σ).hom.app (G.obj Y) (ι.app Y y) := by
  rw [ι_app_eq_iso_hom adj ι e he, ι_app_eq_iso_hom adj ι e he, autMap_hom_app_iso_hom_apply,
    FunctorToFintypeCat.naturality]
  rfl

/-- If `F'` injects naturally into `F ∘ G` for a left adjoint `G` of `H`, compatibly with
`e : F' ∘ H ≅ F`, then `ᵗH : Aut F' → Aut F` is injective. -/
theorem injective_autMap_of_adjunction (hι : ∀ Y, Function.Injective (ι.app Y)) :
    Function.Injective (autMap H e) := by
  intro σ₁ σ₂ h
  apply Iso.ext
  ext Y y
  apply hι Y
  rw [ι_app_hom_app adj ι e he, ι_app_hom_app adj ι e he, h]

omit he in
/-- An automorphism `τ` of `F` preserving the images of `ι` restricts to an automorphism of `F'`
(`ι` injective). -/
noncomputable def autOfFixes (hι : ∀ Y, Function.Injective (ι.app Y)) (τ : Aut F)
    (hτ : ∀ Y (y : F'.obj Y), ∃ y', ι.app Y y' = τ.hom.app (G.obj Y) (ι.app Y y)) : Aut F' :=
  NatIso.ofComponents (fun Y ↦ FintypeCat.equivEquivIso (Equiv.ofBijective
      (fun y ↦ (hτ Y y).choose) (Finite.injective_iff_bijective.1 fun y₁ y₂ h ↦ by
        apply hι Y
        have h' := congrArg (ι.app Y) h
        rw [(hτ Y y₁).choose_spec, (hτ Y y₂).choose_spec] at h'
        exact (FintypeCat.hom_inv_id_apply (τ.app _) _).symm.trans
          ((congrArg (τ.app (G.obj Y)).inv h').trans (FintypeCat.hom_inv_id_apply (τ.app _) _)))))
    fun {Y Y'} φ ↦ by
      ext y
      apply hι Y'
      change ι.app Y' (hτ Y' (F'.map φ y)).choose = ι.app Y' (F'.map φ (hτ Y y).choose)
      rw [(hτ Y' _).choose_spec, FunctorToFintypeCat.naturality F' (G ⋙ F) ι φ,
        FunctorToFintypeCat.naturality F' (G ⋙ F) ι φ, (hτ Y y).choose_spec]
      exact FunctorToFintypeCat.naturality F F τ.hom (G.map φ) _

omit he in
lemma ι_app_autOfFixes (hι : ∀ Y, Function.Injective (ι.app Y)) (τ : Aut F)
    (hτ : ∀ Y (y : F'.obj Y), ∃ y', ι.app Y y' = τ.hom.app (G.obj Y) (ι.app Y y)) (Y : C')
    (y : F'.obj Y) :
    ι.app Y ((autOfFixes ι hι τ hτ).hom.app Y y) = τ.hom.app (G.obj Y) (ι.app Y y) :=
  (hτ Y y).choose_spec

lemma autMap_autOfFixes (hι : ∀ Y, Function.Injective (ι.app Y)) (τ : Aut F)
    (hτ : ∀ Y (y : F'.obj Y), ∃ y', ι.app Y y' = τ.hom.app (G.obj Y) (ι.app Y y)) :
    autMap H e (autOfFixes ι hι τ hτ) = τ := by
  apply Iso.ext
  ext X x
  obtain ⟨x, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective (e.hom.app X)).1 inferInstance).2 x
  rw [autMap_hom_app_iso_hom_apply, he, he, ι_app_autOfFixes]
  exact (FunctorToFintypeCat.naturality F F τ.hom (adj.counit.app X) _).symm

/-- Abstract form of V.7 (compare V.6.13): let `G ⊣ H` with `H : C ⥤ C'`, `F'` a functor on `C'`
which injects naturally into `F ∘ G` (`ι`), compatibly with `e : F' ∘ H ≅ F`, such that the
image of `F'(Y)` in `F(G Y)` is exactly the inverse image of a point `p ∈ F(S₀)` under a given
`q_Y : G Y ⟶ S₀`. If `F'` has a one-point fibre, then `ᵗH : Aut F' → Aut F` is an isomorphism
onto the stabilizer of `p`. -/
theorem injective_autMap_and_range_eq_stabilizer (hι : ∀ Y, Function.Injective (ι.app Y))
    {S₀ : C} (p : F.obj S₀) (q : ∀ Y, G.obj Y ⟶ S₀) (hq : ∀ Y y, F.map (q Y) (ι.app Y y) = p)
    (hfib : ∀ Y z, F.map (q Y) z = p → ∃ y, ι.app Y y = z) (T : C') [Subsingleton (F'.obj T)]
    (p₀ : F'.obj T) :
    Function.Injective (autMap H e) ∧
      (autMap H e).range = MulAction.stabilizer (Aut F) p := by
  refine ⟨injective_autMap_of_adjunction adj ι e he hι, le_antisymm ?_ fun τ hτ ↦ ?_⟩
  · rintro _ ⟨σ, rfl⟩
    change (autMap H e σ).hom.app S₀ p = p
    have h1 := FunctorToFintypeCat.naturality F F (autMap H e σ).hom (q T) (ι.app T p₀)
    have h2 := ι_app_hom_app adj ι e he σ T p₀
    rw [Subsingleton.elim (σ.hom.app T p₀) p₀] at h2
    rw [← hq T p₀]
    exact h1.trans (congrArg (fun z ↦ F.map (q T) z) h2.symm)
  · have hτ' : τ.hom.app S₀ p = p := hτ
    have hfix (Y : C') (y : F'.obj Y) : ∃ y', ι.app Y y' = τ.hom.app (G.obj Y) (ι.app Y y) := by
      apply hfib
      rw [← FunctorToFintypeCat.naturality, hq, hτ']
    exact ⟨autOfFixes ι hι τ hfix, autMap_autOfFixes adj ι e he hι τ hfix⟩

end Adjunction

section Scheme

variable {S S' W : Scheme.{u}} (g : S' ⟶ S) (hg : finiteEtaleHom g) {t : W ⟶ S'}
  {F' : FEt S' ⥤ FintypeCat.{u}} {F : FEt S ⥤ FintypeCat.{u}}
  (e' : F' ⋙ FintypeCat.incl ≅ geometricPoints t)
  (e : F ⋙ FintypeCat.incl ≅ geometricPoints (t ≫ g))

/-- V.7: an étale covering `Y ⟶ S'` of an étale covering `g : S' ⟶ S` is an étale covering of
`S` (the functor `g_!`, left adjoint to `g^•`). -/
noncomputable abbrev FEt.postcomp : FEt S' ⥤ FEt S :=
  MorphismProperty.Over.map ⊤ hg

lemma pointOfIso_toEquiv_symm {S W : Scheme.{u}} {t : W ⟶ S} {F : FEt S ⥤ FintypeCat.{u}}
    (e : F ⋙ FintypeCat.incl ≅ geometricPoints t) {X : FEt S} (a : (geometricPoints t).obj X) :
    pointOfIso e ((e.app X).toEquiv.symm a) = a.left := by
  unfold pointOfIso
  rw [Equiv.apply_symm_apply]

/-- The geometric point of `g_! Y` over `t ≫ g` underlying a geometric point of `Y` over `t`. -/
noncomputable def pointPostcomp (Y : FEt S') (x : F'.obj Y) : F.obj ((FEt.postcomp g hg).obj Y) :=
  (e.app _).toEquiv.symm (Over.homMk (pointOfIso e' x) (by
    change pointOfIso e' x ≫ (Y.hom ≫ g) = t ≫ g
    rw [← Category.assoc, pointOfIso_comp]))

lemma pointOfIso_pointPostcomp (Y : FEt S') (x : F'.obj Y) :
    pointOfIso e (pointPostcomp g hg e' e Y x) = pointOfIso e' x :=
  pointOfIso_toEquiv_symm e _

/-- The natural injection `F_{t}(Y) ⟶ F_{t ≫ g}(g_! Y)`. -/
noncomputable def fiberPostcomp : F' ⟶ FEt.postcomp g hg ⋙ F where
  app Y := FintypeCat.homMk (pointPostcomp g hg e' e Y)
  naturality {Y Y'} φ := by
    ext x
    apply pointOfIso_injective e
    change pointOfIso e (pointPostcomp g hg e' e Y' (F'.map φ x)) =
      pointOfIso e (F.map ((FEt.postcomp g hg).map φ) (pointPostcomp g hg e' e Y x))
    rw [pointOfIso_map, pointOfIso_pointPostcomp, pointOfIso_pointPostcomp, pointOfIso_map]
    rfl

lemma fiberPostcomp_app_apply (Y : FEt S') (x : F'.obj Y) :
    (fiberPostcomp g hg e' e).app Y x = pointPostcomp g hg e' e Y x :=
  rfl

lemma injective_fiberPostcomp_app (Y : FEt S') :
    Function.Injective ((fiberPostcomp g hg e' e).app Y) := fun x y h ↦ by
  apply pointOfIso_injective e'
  rw [← pointOfIso_pointPostcomp g hg e' e, ← pointOfIso_pointPostcomp g hg e' e]
  exact congrArg (pointOfIso e) h

/-- The iso `F_t ∘ g^• ≅ F_{t ≫ g}` (for `F = F_{t ≫ g}`, `F' = F_t` this is
`FEt.pullbackFiberIso`). -/
noncomputable abbrev pullbackIsoOfIso : FEt.pullback g ⋙ F' ≅ F :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl
    (Functor.associator (FEt.pullback g) F' FintypeCat.incl ≪≫
      Functor.isoWhiskerLeft (FEt.pullback g) e' ≪≫ pullbackGeometricPointsIso g t ≪≫ e.symm)

lemma pullbackIsoOfIso_hom_app_eq (X : FEt S) (x : F'.obj ((FEt.pullback g).obj X)) :
    (pullbackIsoOfIso g e' e).hom.app X x =
      F.map ((MorphismProperty.Over.mapPullbackAdj finiteEtaleHom ⊤ g hg trivial).counit.app X)
        ((fiberPostcomp g hg e' e).app _ x) := by
  apply pointOfIso_injective e
  rw [pointOfIso_cancel, pointOfIso_map, fiberPostcomp_app_apply, pointOfIso_pointPostcomp]
  rfl

/-- The geometric point `t` of `S'`, as a point of the fibre of the covering `S'` of `S`. -/
noncomputable def coveringPointOfIso :
    F.obj (MorphismProperty.Over.mk ⊤ g hg) :=
  (e.app _).toEquiv.symm (Over.homMk t rfl)

lemma pointOfIso_coveringPointOfIso : pointOfIso e (coveringPointOfIso g hg e) = t :=
  pointOfIso_toEquiv_symm e _

/-- V.7 for fibre functors described by geometric points: `π₁(g; t) : Aut F_t → Aut F_{t ≫ g}`
is an isomorphism onto the stabilizer of the point `t ∈ F_{t ≫ g}(S')`. -/
theorem injective_autMap_pullback_and_range_eq_stabilizer :
    Function.Injective (autMap (FEt.pullback g) (pullbackIsoOfIso g e' e)) ∧
      (autMap (FEt.pullback g) (pullbackIsoOfIso g e' e)).range =
        MulAction.stabilizer (Aut F) (coveringPointOfIso g hg e) := by
  let T : FEt S' := MorphismProperty.Over.mk ⊤ (𝟙 S') (finiteEtaleHom.id_mem S')
  have : Subsingleton (F'.obj T) := ⟨fun x y ↦ pointOfIso_injective e'
    (((Category.comp_id _).symm.trans (pointOfIso_comp e' x)).trans
      ((pointOfIso_comp e' y).symm.trans (Category.comp_id _)))⟩
  let p₀ : F'.obj T := (e'.app T).toEquiv.symm (Over.homMk t (Category.comp_id t))
  have hpt (Y : FEt S') (z : F.obj ((FEt.postcomp g hg).obj Y)) :
      pointOfIso e (F.map (MorphismProperty.Over.homMk Y.hom rfl :
        (FEt.postcomp g hg).obj Y ⟶ MorphismProperty.Over.mk ⊤ g hg) z) =
        pointOfIso e z ≫ Y.hom :=
    pointOfIso_map e _ z
  refine injective_autMap_and_range_eq_stabilizer
    (MorphismProperty.Over.mapPullbackAdj finiteEtaleHom ⊤ g hg trivial)
    (fiberPostcomp g hg e' e) (pullbackIsoOfIso g e' e) (pullbackIsoOfIso_hom_app_eq g hg e' e)
    (injective_fiberPostcomp_app g hg e' e) (coveringPointOfIso g hg e)
    (fun Y ↦ MorphismProperty.Over.homMk Y.hom rfl) (fun Y y ↦ ?_) (fun Y z hz ↦ ?_) T p₀
  · apply pointOfIso_injective e
    rw [hpt, fiberPostcomp_app_apply, pointOfIso_pointPostcomp, pointOfIso_coveringPointOfIso]
    exact pointOfIso_comp e' y
  · have hz' : pointOfIso e z ≫ Y.hom = t := by
      rw [← hpt, hz, pointOfIso_coveringPointOfIso]
    refine ⟨(e'.app Y).toEquiv.symm (Over.homMk (pointOfIso e z) hz'), ?_⟩
    apply pointOfIso_injective e
    rw [fiberPostcomp_app_apply, pointOfIso_pointPostcomp]
    exact pointOfIso_toEquiv_symm e' _

end Scheme

section Fiber

variable {S S' : Scheme.{u}} (Ω : Type u) [Field Ω] (g : S' ⟶ S) (hg : finiteEtaleHom g)
  (s : Spec (CommRingCat.of Ω) ⟶ S')

/-- The geometric point `a'` of `S'`, as a point of the fibre `F_a(S')` of the étale covering
`S'` of `S` at `a = g(a')`. -/
noncomputable abbrev FEt.coveringPoint :
    (FEt.fiber Ω (s ≫ g)).obj (MorphismProperty.Over.mk ⊤ g hg) :=
  coveringPointOfIso g hg (FEt.fiberInclIso Ω (s ≫ g))

lemma FEt.fiberPoint_coveringPoint : FEt.fiberPoint Ω (FEt.coveringPoint Ω g hg s) = s :=
  pointOfIso_coveringPointOfIso g hg _

/-- **V.7**: if `g : S' ⟶ S` is an étale covering and `a'` a geometric point of `S'`, then
`π₁(g; a') : π₁(S', a') → π₁(S, g(a'))` is injective, with image the stabilizer of
`a' ∈ F_{g(a')}(S')`. -/
theorem etaleFundamentalGroup.injective_map_and_range_eq_stabilizer :
    Function.Injective (etaleFundamentalGroup.map Ω g s) ∧
      (etaleFundamentalGroup.map Ω g s).range =
        MulAction.stabilizer (etaleFundamentalGroup Ω (s ≫ g)) (FEt.coveringPoint Ω g hg s) :=
  injective_autMap_pullback_and_range_eq_stabilizer g hg (FEt.fiberInclIso Ω s)
    (FEt.fiberInclIso Ω (s ≫ g))

include hg in
/-- V.7: the image of `π₁(S', a') → π₁(S, a)` is an open subgroup. -/
theorem etaleFundamentalGroup.isOpen_range_map :
    IsOpen ((etaleFundamentalGroup.map Ω g s).range : Set (etaleFundamentalGroup Ω (s ≫ g))) := by
  have := obj_discreteTopology (FEt.fiber Ω (s ≫ g)) (MorphismProperty.Over.mk ⊤ g hg)
  rw [(etaleFundamentalGroup.injective_map_and_range_eq_stabilizer Ω g hg s).2]
  exact stabilizer_isOpen _ _

/-- V.7: `π₁(S', a')` is isomorphic, as a topological group, to the open subgroup
`(etaleFundamentalGroup.map Ω g s).range` of `π₁(S, a)` (the stabilizer of `a' ∈ F_a(S')`). -/
noncomputable def etaleFundamentalGroup.mapRangeEquiv :
    etaleFundamentalGroup Ω s ≃ₜ* (etaleFundamentalGroup.map Ω g s).range :=
  have h := (etaleFundamentalGroup.injective_map_and_range_eq_stabilizer Ω g hg s).1
  have hc : Continuous (MonoidHom.ofInjective h) :=
    (etaleFundamentalGroup.continuous_map Ω g s).subtype_mk _
  { MonoidHom.ofInjective h with
    continuous_toFun := hc
    continuous_invFun :=
      (hc.homeoOfEquivCompactToT2 (f := (MonoidHom.ofInjective h).toEquiv)).continuous_symm }

end Fiber

end SGA.SGA1.ExposeV
