/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.SchemeGaloisCategory
import SGA.SGA1.ExposeV.NormalBase
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeV.GaloisAxioms

/-!
# SGA 1, Exposé V, §7: functoriality of `π₁`

Complements to `SGA.SGA1.ExposeV.FundamentalGroup` and `SGA.SGA1.ExposeV.SchemeGaloisCategory`.

* Base change along an isomorphism `S ≅ T` is an equivalence `FEt S ≌ FEt T`
  (`FEt.pullbackEquivalence`), so (G 2) for quotients transfers along isomorphisms
  (`FEt.hasQuotients_of_iso`); in particular it holds for connected affine schemes
  (`FEt.hasQuotients_of_isAffine`, from the affine case). For all schemes it is
  `FEt.hasQuotients` (`SGA.SGA1.ExposeV.QuotientHasQuotients`), so `FEt S` is a Galois category for
  every connected `S`.
* The fiber functors at equal geometric points are isomorphic (`FEt.fiberCongr`). A point of
  `F_{s̄}(X)` is a geometric point `Spec Ω ⟶ X` over `s̄` (`FEt.fiberPoint`); the maps
  `F_{s̄}(φ)` and `F_{t̄}(f^• X) ≅ F_{f ∘ t̄}(X)` compose geometric points with `φ` and with the
  projection `f^• X ⟶ X` (`FEt.fiberPoint_map`, `FEt.fiberPoint_pullbackFiberIso`). These are
  stated for abstract functors first, since the kernel should not unfold `FEt.fiber`.
* V.6.3, functoriality of `π₁(f)`: `autMap_comp`, `autMap_congr`; if `f₁ ≫ f₂ = 𝟙` the composite
  `π₁(f₂) ∘ π₁(f₁)` is a conjugation (`etaleFundamentalGroup.exists_map_comp_map_eq_conjAut`,
  used for the splitting IX.6.4).
* Over a separably closed field every étale covering is completely decomposed, hence
  `π₁(Spec Ω', t̄) = 1` (`etaleFundamentalGroup.eq_one_of_isSepClosed`), and a composite
  `π₁(T) → π₁(S) → π₁(R)` is trivial as soon as `T → S → R` factors through a scheme with trivial
  fundamental group (`etaleFundamentalGroup.map_comp_map_eq_one`). This is the triviality of
  `π₁(X̄_y) → π₁(X) → π₁(Y)` in X.1.4 and IX.6.1.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

section PullbackEquivalence

variable {S T : Scheme.{u}}

lemma isIso_pullback_fst_id {A B : Scheme.{u}} (a : A ⟶ B) : IsIso (pullback.fst a (𝟙 B)) :=
  inferInstance

/-- Base change of étale coverings along the identity is the identity. -/
noncomputable def FEt.pullbackId (S : Scheme.{u}) : FEt.pullback (𝟙 S) ≅ 𝟭 (FEt S) :=
  NatIso.ofComponents (fun Y ↦ MorphismProperty.Over.isoMk
    (@asIso _ _ _ _ (pullback.fst Y.hom (𝟙 S)) (isIso_pullback_fst_id Y.hom)) (by
      change pullback.fst Y.hom (𝟙 S) ≫ Y.hom = pullback.snd Y.hom (𝟙 S)
      rw [pullback.condition, Category.comp_id])) (fun φ ↦ by
      ext : 1
      exact pullback.lift_fst _ _ _)

/-- V.7: base change along an isomorphism `e : S ≅ T` is an equivalence between the categories of
étale coverings. -/
noncomputable def FEt.pullbackEquivalence (e : S ≅ T) : FEt S ≌ FEt T :=
  CategoryTheory.Equivalence.mk (FEt.pullback e.inv) (FEt.pullback e.hom)
    ((FEt.pullbackId S).symm ≪≫ (MorphismProperty.Over.pullbackCongr e.hom_inv_id).symm ≪≫
      MorphismProperty.Over.pullbackComp e.hom e.inv)
    ((MorphismProperty.Over.pullbackComp e.inv e.hom).symm ≪≫
      MorphismProperty.Over.pullbackCongr e.inv_hom_id ≪≫ FEt.pullbackId T)

instance (e : S ≅ T) : (FEt.pullback e.inv).IsEquivalence :=
  (FEt.pullbackEquivalence e).isEquivalence_functor

instance (e : S ≅ T) : (FEt.pullback e.hom).IsEquivalence :=
  (FEt.pullbackEquivalence e).isEquivalence_inverse

/-- An étale covering which is an isomorphism onto the base is a final object of `FEt S`. -/
noncomputable def FEt.isTerminalOfIsIso (Y : FEt S) [IsIso Y.hom] : IsTerminal Y :=
  IsTerminal.ofUniqueHom
    (fun Z ↦ MorphismProperty.Over.homMk ((Z.hom : Z.left ⟶ S) ≫ inv (Y.hom : Y.left ⟶ S))
      (by simp))
    (fun Z φ ↦ by
      ext
      have : φ.left ≫ (Y.hom : Y.left ⟶ S) = Z.hom := MorphismProperty.Over.w φ
      simp [← this])

instance (f : S ⟶ T) [IsIso f] : (FEt.pullback f).IsEquivalence :=
  inferInstanceAs (FEt.pullback (asIso f).hom).IsEquivalence

/-- Base change along a composite of two morphisms along which base change is an equivalence is
an equivalence. -/
lemma FEt.isEquivalence_pullback_comp {R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R)
    [(FEt.pullback f).IsEquivalence] [(FEt.pullback g).IsEquivalence] :
    (FEt.pullback (f ≫ g)).IsEquivalence :=
  Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp f g).symm

/-- If base change along `f ≫ g` and along `g` are equivalences, so is base change along `f`. -/
lemma FEt.isEquivalence_pullback_of_comp {R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R)
    [(FEt.pullback (f ≫ g)).IsEquivalence] [(FEt.pullback g).IsEquivalence] :
    (FEt.pullback f).IsEquivalence :=
  have : (FEt.pullback g ⋙ FEt.pullback f).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp f g)
  Functor.isEquivalence_of_comp_left (FEt.pullback g) (FEt.pullback f)

/-- The geometric point `Spec κ(x)ᵃˡᵍ ⟶ S` above a point `x` of `S`, with values in an algebraic
closure of the residue field. -/
noncomputable def geometricPointAt (S : Scheme.{u}) (x : S) :
    Spec (CommRingCat.of (AlgebraicClosure (S.residueField x))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x)
    (AlgebraicClosure (S.residueField x)))) ≫ S.fromSpecResidueField x

/-- The fiber functors at equal geometric points are isomorphic. -/
noncomputable def FEt.fiberCongr (Ω : Type u) [Field Ω] {s s' : Spec (CommRingCat.of Ω) ⟶ S}
    (h : s = s') : FEt.fiber Ω s ≅ FEt.fiber Ω s' :=
  eqToIso (by rw [h])

/-- (G 2) for quotients is invariant under isomorphism of the base. -/
lemma FEt.hasQuotients_of_iso (e : S ≅ T) [FEt.HasQuotients T] : FEt.HasQuotients S where
  hasColimitsOfShape G _ _ :=
    have := FEt.HasQuotients.hasColimitsOfShape (S := T) G
    Adjunction.hasColimitsOfShape_of_equivalence (FEt.pullback e.inv)
  preservesColimitsOfShape G _ _ Ω _ _ s := by
    have := FEt.HasQuotients.preservesColimitsOfShape (S := T) G Ω (s ≫ e.hom)
    have : PreservesColimitsOfShape (SingleObj G)
        (FEt.pullback e.inv ⋙ FEt.fiber Ω (s ≫ e.hom)) := comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso
      (FEt.pullbackFiberIso Ω e.inv (s ≫ e.hom) ≪≫ FEt.fiberCongr Ω (by simp))

/-- V.7, (G 2) for quotients over an affine base, deduced from the case of `Spec R`: the étale
coverings of a connected affine scheme have quotients by finite groups, compatible with the fiber
functors. (Subsumed by `FEt.hasQuotients`, which holds for every scheme.) -/
theorem FEt.hasQuotients_of_isAffine [IsAffine S] [ConnectedSpace S] : FEt.HasQuotients S :=
  have : ConnectedSpace (PrimeSpectrum Γ(S, ⊤)) :=
    (Scheme.homeoOfIso S.isoSpec).surjective.connectedSpace
      (Scheme.homeoOfIso S.isoSpec).continuous
  FEt.hasQuotients_of_iso S.isoSpec

example [ConnectedSpace S] : GaloisCategory (FEt S) := inferInstance

end PullbackEquivalence



section FiberPoints

/-! Elementwise description of the fiber functors. The lemmas are first stated for abstract
functors, so that the kernel does not unfold `FEt.fiber` when checking the instances. -/

lemma incl_iso_naturality_apply {C : Type*} [Category C] {F : C ⥤ FintypeCat.{u}}
    {G : C ⥤ Type u} (e : F ⋙ FintypeCat.incl ≅ G) {X Y : C} (φ : X ⟶ Y) (x : F.obj X) :
    (e.app Y).toEquiv (F.map φ x) = G.map φ ((e.app X).toEquiv x) :=
  ConcreteCategory.congr_hom (e.hom.naturality φ) x

lemma fullyFaithfulCancelRight_comp_apply {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {F : D ⥤ FintypeCat.{u}} {F' : C ⥤ FintypeCat.{u}} {G : D ⥤ Type u} {G' : C ⥤ Type u}
    (e : F ⋙ FintypeCat.incl ≅ G) (e' : F' ⋙ FintypeCat.incl ≅ G') (p : H ⋙ G ≅ G') (X : C)
    (x : F.obj (H.obj X)) :
    (e'.app X).toEquiv ((Functor.fullyFaithfulCancelRight FintypeCat.incl
      (Functor.associator H F FintypeCat.incl ≪≫ Functor.isoWhiskerLeft H e ≪≫ p ≪≫
        e'.symm)).hom.app X x) = p.hom.app X ((e.app (H.obj X)).toEquiv x) := by
  change e'.hom.app X (FintypeCat.incl.map ((Functor.fullyFaithfulCancelRight FintypeCat.incl
      (Functor.associator H F FintypeCat.incl ≪≫ Functor.isoWhiskerLeft H e ≪≫ p ≪≫
        e'.symm)).hom.app X) x) = _
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp

lemma geometricPoints_map_left {S W : Scheme.{u}} (t : W ⟶ S) {X Y : FEt S} (φ : X ⟶ Y)
    (a : (geometricPoints t).obj X) : ((geometricPoints t).map φ a).left = a.left ≫ φ.left :=
  rfl

lemma pullbackGeometricPointsIso_hom_app_left {S T W : Scheme.{u}} (f : T ⟶ S) (t : W ⟶ T)
    (X : FEt S) (a : (geometricPoints t).obj ((FEt.pullback f).obj X)) :
    ((pullbackGeometricPointsIso f t).hom.app X a).left = a.left ≫ pullback.fst X.hom f :=
  rfl

section PointOfIso

variable {S W : Scheme.{u}} {t : W ⟶ S} {F : FEt S ⥤ FintypeCat.{u}}
  (e : F ⋙ FintypeCat.incl ≅ geometricPoints t)

/-- The underlying morphism of a point of a fiber functor identified with geometric points. -/
noncomputable def pointOfIso {X : FEt S} (x : F.obj X) : W ⟶ X.left :=
  ((e.app X).toEquiv x).left

lemma pointOfIso_comp {X : FEt S} (x : F.obj X) : pointOfIso e x ≫ X.hom = t :=
  Over.w ((e.app X).toEquiv x)

lemma pointOfIso_map {X Y : FEt S} (φ : X ⟶ Y) (x : F.obj X) :
    pointOfIso e (F.map φ x) = pointOfIso e x ≫ φ.left :=
  congrArg (fun a ↦ Over.Hom.left a) (incl_iso_naturality_apply e φ x)

lemma pointOfIso_injective {X : FEt S} {x y : F.obj X} (h : pointOfIso e x = pointOfIso e y) :
    x = y :=
  (e.app X).toEquiv.injective (Over.OverMorphism.ext h)

end PointOfIso

variable {S T : Scheme.{u}} (Ω : Type u) [Field Ω]

/-- A point of the fiber is determined by the underlying geometric point. -/
lemma FEt.fiber_ext {s : Spec (CommRingCat.of Ω) ⟶ S} {X : FEt S} {x y : (FEt.fiber Ω s).obj X}
    (h : (FEt.fiberEquiv Ω s X x).left = (FEt.fiberEquiv Ω s X y).left) : x = y :=
  (FEt.fiberEquiv Ω s X).injective (Over.OverMorphism.ext h)

/-- The image of a geometric point of `X` under `φ : X ⟶ Y`. -/
lemma FEt.fiberEquiv_map_left {s : Spec (CommRingCat.of Ω) ⟶ S} {X Y : FEt S} (φ : X ⟶ Y)
    (x : (FEt.fiber Ω s).obj X) :
    (FEt.fiberEquiv Ω s Y ((FEt.fiber Ω s).map φ x)).left =
      (FEt.fiberEquiv Ω s X x).left ≫ φ.left :=
  (congrArg (fun a ↦ Over.Hom.left a)
    (incl_iso_naturality_apply (FEt.fiberInclIso Ω s) φ x)).trans
    (geometricPoints_map_left s φ _)

/-- V.7: the isomorphism `F_{t̄}(f^• X) ≅ F_{f ∘ t̄}(X)` composes geometric points with the
projection `f^• X ⟶ X`. -/
lemma FEt.fiberEquiv_pullbackFiberIso_hom_left (f : T ⟶ S) (t : Spec (CommRingCat.of Ω) ⟶ T)
    (X : FEt S) (x : (FEt.fiber Ω t).obj ((FEt.pullback f).obj X)) :
    (FEt.fiberEquiv Ω (t ≫ f) X ((FEt.pullbackFiberIso Ω f t).hom.app X x)).left =
      (FEt.fiberEquiv Ω t _ x).left ≫ pullback.fst X.hom f :=
  (congrArg (fun a ↦ Over.Hom.left a) (fullyFaithfulCancelRight_comp_apply (FEt.pullback f)
    (FEt.fiberInclIso Ω t) (FEt.fiberInclIso Ω (t ≫ f)) (pullbackGeometricPointsIso f t) X
      x)).trans (pullbackGeometricPointsIso_hom_app_left f t X _)

/-- The fiber functors at equal geometric points have the same geometric points. -/
lemma FEt.fiberEquiv_fiberCongr_hom_left {s s' : Spec (CommRingCat.of Ω) ⟶ S} (h : s = s')
    (X : FEt S) (x : (FEt.fiber Ω s).obj X) :
    (FEt.fiberEquiv Ω s' X ((FEt.fiberCongr Ω h).hom.app X x)).left =
      (FEt.fiberEquiv Ω s X x).left := by
  subst h
  rfl

/-- The underlying morphism `Spec Ω ⟶ X` of a point of the fiber `F_{s̄}(X)`. -/
noncomputable abbrev FEt.fiberPoint {s : Spec (CommRingCat.of Ω) ⟶ S} {X : FEt S}
    (x : (FEt.fiber Ω s).obj X) : Spec (CommRingCat.of Ω) ⟶ X.left :=
  pointOfIso (FEt.fiberInclIso Ω s) x

lemma FEt.fiberPoint_comp {s : Spec (CommRingCat.of Ω) ⟶ S} {X : FEt S}
    (x : (FEt.fiber Ω s).obj X) : FEt.fiberPoint Ω x ≫ X.hom = s :=
  pointOfIso_comp _ x

lemma FEt.fiberPoint_map {s : Spec (CommRingCat.of Ω) ⟶ S} {X Y : FEt S} (φ : X ⟶ Y)
    (x : (FEt.fiber Ω s).obj X) :
    FEt.fiberPoint Ω ((FEt.fiber Ω s).map φ x) = FEt.fiberPoint Ω x ≫ φ.left :=
  pointOfIso_map _ φ x

/-- The projection `f^• X ⟶ X`. -/
noncomputable abbrev FEt.proj (f : T ⟶ S) (X : FEt S) : ((FEt.pullback f).obj X).left ⟶ X.left :=
  pullback.fst X.hom f

lemma pointOfIso_cancel {W : Scheme.{u}} (f : T ⟶ S) (t : W ⟶ T) {F : FEt T ⥤ FintypeCat.{u}}
    {F' : FEt S ⥤ FintypeCat.{u}} (e : F ⋙ FintypeCat.incl ≅ geometricPoints t)
    (e' : F' ⋙ FintypeCat.incl ≅ geometricPoints (t ≫ f)) (X : FEt S)
    (x : F.obj ((FEt.pullback f).obj X)) :
    pointOfIso e' ((Functor.fullyFaithfulCancelRight FintypeCat.incl
      (Functor.associator (FEt.pullback f) F FintypeCat.incl ≪≫
        Functor.isoWhiskerLeft (FEt.pullback f) e ≪≫ pullbackGeometricPointsIso f t ≪≫
          e'.symm)).hom.app X x) = pointOfIso e x ≫ FEt.proj f X :=
  (congrArg (fun a ↦ Over.Hom.left a) (fullyFaithfulCancelRight_comp_apply (FEt.pullback f)
    e e' (pullbackGeometricPointsIso f t) X x)).trans
    (pullbackGeometricPointsIso_hom_app_left f t X _)

lemma FEt.fiberPoint_pullbackFiberIso (f : T ⟶ S) (t : Spec (CommRingCat.of Ω) ⟶ T)
    (X : FEt S) (x : (FEt.fiber Ω t).obj ((FEt.pullback f).obj X)) :
    FEt.fiberPoint Ω ((FEt.pullbackFiberIso Ω f t).hom.app X x) =
      FEt.fiberPoint Ω x ≫ FEt.proj f X :=
  pointOfIso_cancel f t (FEt.fiberInclIso Ω t) (FEt.fiberInclIso Ω (t ≫ f)) X x

lemma FEt.fiberPoint_fiberCongr {s s' : Spec (CommRingCat.of Ω) ⟶ S} (h : s = s')
    (X : FEt S) (x : (FEt.fiber Ω s).obj X) :
    FEt.fiberPoint Ω ((FEt.fiberCongr Ω h).hom.app X x) = FEt.fiberPoint Ω x := by
  subst h
  rfl

lemma FEt.fiber_ext_point {s : Spec (CommRingCat.of Ω) ⟶ S} {X : FEt S}
    {x y : (FEt.fiber Ω s).obj X} (h : FEt.fiberPoint Ω x = FEt.fiberPoint Ω y) : x = y :=
  pointOfIso_injective _ h

/-- A point of the fiber of a base change `f^• X` is determined by its image in `X`. -/
lemma FEt.fiber_ext_pullback (f : T ⟶ S) {t : Spec (CommRingCat.of Ω) ⟶ T} {X : FEt S}
    {x y : (FEt.fiber Ω t).obj ((FEt.pullback f).obj X)}
    (h : FEt.fiberPoint Ω x ≫ FEt.proj f X = FEt.fiberPoint Ω y ≫ FEt.proj f X) : x = y :=
  FEt.fiber_ext_point Ω (pullback.hom_ext h
    ((FEt.fiberPoint_comp Ω x).trans (FEt.fiberPoint_comp Ω y).symm))

end FiberPoints

section CompletelyDecomposed

variable {C : Type*} [Category C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

lemma subsingleton_fiber_of_isTerminal {Y : C} (hY : IsTerminal Y) : Subsingleton (F.obj Y) := by
  have ht : IsTerminal (F.obj Y) := hY.isTerminalObj F _
  constructor
  intro a b
  have := ht.hom_ext (FintypeCat.homMk (X := FintypeCat.of PUnit.{w + 1}) fun _ ↦ a)
    (FintypeCat.homMk fun _ ↦ b)
  have h := congrArg (fun f ↦ f PUnit.unit) this
  simp only at h
  exact h

/-- If the fibres of all connected objects are points, the fundamental group is trivial. -/
lemma aut_eq_one_of_forall_isConnected
    (h : ∀ Y : C, IsConnected Y → Subsingleton (F.obj Y)) (σ : Aut F) : σ = 1 := by
  apply Iso.ext
  ext Z z
  obtain ⟨Y, i, y, rfl, hY, -⟩ := fiber_in_connected_component F Z z
  have := h Y hY
  exact (mulAction_naturality F σ i y).trans (congrArg (F.map i) (Subsingleton.elim _ _))

lemma subsingleton_fiber_terminal : Subsingleton (F.obj (⊤_ C)) := by
  have ht : IsTerminal (F.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj F _
  constructor
  intro a b
  have := ht.hom_ext (FintypeCat.homMk (X := FintypeCat.of PUnit.{w + 1}) fun _ ↦ a)
    (FintypeCat.homMk fun _ ↦ b)
  have h := congrArg (fun f ↦ f PUnit.unit) this
  simp only at h
  exact h

/-- V.6.4: `Aut F` acts trivially on the fibre of a finite sum of copies of the final object. -/
lemma smul_eq_of_iso_sigma_terminal {X : C} {n : ℕ} (φ : X ≅ ∐ fun _ : Fin n ↦ ⊤_ C)
    (σ : Aut F) (x : F.obj X) : σ • x = x := by
  have := subsingleton_fiber_terminal F
  have hc := isColimitOfPreserves F (coproductIsCoproduct fun _ : Fin n ↦ ⊤_ C)
  obtain ⟨⟨j⟩, a, ha⟩ := Limits.FintypeCat.jointly_surjective _ _ hc (F.map φ.hom x)
  let a' : F.obj (⊤_ C) := a
  have hx : F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j ≫ φ.inv) a' = x := by
    rw [F.map_comp, FintypeCat.comp_apply]
    erw [ha]
    exact FintypeCat.hom_inv_id_apply (F.mapIso φ) x
  rw [← hx, mulAction_naturality]
  congr 1
  exact Subsingleton.elim _ _

/-- If every object of a Galois category is completely decomposed (a finite sum of copies of
the final object), its fundamental group is trivial. -/
lemma aut_eq_one_of_forall_iso_sigma_terminal
    (h : ∀ X : C, ∃ n : ℕ, Nonempty (X ≅ ∐ fun _ : Fin n ↦ ⊤_ C)) (σ : Aut F) : σ = 1 := by
  apply Iso.ext
  ext X x
  obtain ⟨n, ⟨φ⟩⟩ := h X
  exact smul_eq_of_iso_sigma_terminal F φ σ x

omit [GaloisCategory C] in
/-- An automorphism of a functor which is the identity on an object is the identity on every
isomorphic object. -/
lemma aut_app_eq_id_of_iso {D : Type*} [Category D] {G : C ⥤ D} (σ : G ≅ G) {A B : C}
    (ψ : A ≅ B) (h : σ.hom.app A = 𝟙 _) : σ.hom.app B = 𝟙 _ := by
  have := σ.hom.naturality ψ.hom
  rw [h, Category.id_comp] at this
  rw [← cancel_epi (G.map ψ.hom), this, Category.comp_id]

end CompletelyDecomposed

section AutMap

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}}

/-- V.6.3, functoriality of `autMap`: `ᵗ(H K) = ᵗK ᵗH`. -/
lemma autMap_comp (H : C ⥤ D) (e : H ⋙ F ≅ F') {F'' : E ⥤ FintypeCat.{w}} (K : E ⥤ C)
    (e' : K ⋙ F' ≅ F'') :
    (autMap K e').comp (autMap H e) =
      autMap (K ⋙ H) (Functor.associator K H F ≪≫ Functor.isoWhiskerLeft K e ≪≫ e') :=
  rfl

/-- `autMap` only depends on the functor up to isomorphism. -/
lemma autMap_congr {H H' : C ⥤ D} (ρ : H ≅ H') (e' : H' ⋙ F ≅ F') :
    autMap H (Functor.isoWhiskerRight ρ F ≪≫ e') = autMap H' e' := by
  ext σ : 1
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp only [autMap_hom_app, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc]
  rw [← σ.hom.naturality_assoc, ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id,
    Category.id_comp]

/-- `autMap` of the identity functor is a conjugation. -/
lemma autMap_id {F₁ F₂ : C ⥤ FintypeCat.{w}} (e : 𝟭 C ⋙ F₁ ≅ F₂) :
    autMap (𝟭 C) e = (((Functor.leftUnitor F₁).symm ≪≫ e).conjAut).toMonoidHom := by
  ext σ : 1
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [autMap_hom_app, Iso.conjAut_hom, Iso.conj_apply]

/-- If `K ⋙ H` is isomorphic to the identity, the composite `ᵗK ᵗH` is a conjugation by an
isomorphism of fibre functors. -/
lemma exists_autMap_comp_eq_conjAut (H : C ⥤ D) (e : H ⋙ F ≅ F') {F'' : D ⥤ FintypeCat.{w}}
    (K : D ⥤ C) (e' : K ⋙ F' ≅ F'') (ρ : K ⋙ H ≅ 𝟭 D) :
    ∃ φ : F ≅ F'', (autMap K e').comp (autMap H e) = φ.conjAut.toMonoidHom := by
  let E₀ := Functor.associator K H F ≪≫ Functor.isoWhiskerLeft K e ≪≫ e'
  refine ⟨(Functor.leftUnitor F).symm ≪≫ (Functor.isoWhiskerRight ρ.symm F ≪≫ E₀), ?_⟩
  rw [autMap_comp, ← autMap_id, ← autMap_congr ρ]
  congr 1
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [E₀, ← F.map_comp_assoc]

end AutMap

section Trivial

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- V.7, V.8: the fundamental group of the spectrum of a separably closed field is trivial,
at every geometric point. -/
theorem etaleFundamentalGroup.eq_one_of_isSepClosed (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
    (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω')) (σ : etaleFundamentalGroup Ω t) :
    σ = 1 :=
  aut_eq_one_of_forall_iso_sigma_terminal _ (FEt.exists_iso_sigma_terminal Ω') σ

instance (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
    (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω')) :
    Subsingleton (etaleFundamentalGroup Ω t) :=
  ⟨fun σ τ ↦ by
    rw [etaleFundamentalGroup.eq_one_of_isSepClosed Ω Ω' t σ,
      etaleFundamentalGroup.eq_one_of_isSepClosed Ω Ω' t τ]⟩

variable {T S R P : Scheme.{u}}

omit [IsSepClosed Ω] in
/-- If `π₁(f; t̄)` kills `σ`, then `σ` acts trivially on the fibres of all coverings pulled back
along `f`. -/
lemma etaleFundamentalGroup.hom_app_pullback_eq_id (p : T ⟶ P)
    (t : Spec (CommRingCat.of Ω) ⟶ T) (σ : etaleFundamentalGroup Ω t)
    (hσ : etaleFundamentalGroup.map Ω p t σ = 1) (Z : FEt P) :
    σ.hom.app ((FEt.pullback p).obj Z) = 𝟙 _ := by
  have h := congrArg (fun τ : etaleFundamentalGroup Ω (t ≫ p) ↦ τ.hom.app Z) hσ
  simp only [etaleFundamentalGroup.map, autMap_hom_app] at h
  have h1 : (Iso.hom (1 : etaleFundamentalGroup Ω (t ≫ p))).app Z = 𝟙 _ := rfl
  rw [h1] at h
  have := congrArg (fun k ↦ (FEt.pullbackFiberIso Ω p t).hom.app Z ≫ k ≫
    (FEt.pullbackFiberIso Ω p t).inv.app Z) h
  simpa using this

omit [IsSepClosed Ω] in
/-- V.7 (the formal part of the triviality of `π₁(X̄_y) → π₁(X) → π₁(Y)` in X.1.4 and IX.6.1):
if `f₁ ≫ f₂ = p ≫ q` and `π₁(P, t̄ ≫ p) = 1`, then `π₁(T, t̄) → π₁(S) → π₁(R)` is trivial. -/
theorem etaleFundamentalGroup.map_comp_map_eq_one (f₁ : T ⟶ S) (f₂ : S ⟶ R) (p : T ⟶ P)
    (q : P ⟶ R) (w : f₁ ≫ f₂ = p ≫ q) (t : Spec (CommRingCat.of Ω) ⟶ T)
    (hP : ∀ τ : etaleFundamentalGroup Ω (t ≫ p), τ = 1) :
    (etaleFundamentalGroup.map Ω f₂ (t ≫ f₁)).comp (etaleFundamentalGroup.map Ω f₁ t) = 1 := by
  ext σ : 1
  have key (X : FEt R) : (etaleFundamentalGroup.map Ω f₂ (t ≫ f₁)
      (etaleFundamentalGroup.map Ω f₁ t σ)).hom.app X = 𝟙 _ := by
    let ρ : (FEt.pullback f₁).obj ((FEt.pullback f₂).obj X) ≅
        (FEt.pullback p).obj ((FEt.pullback q).obj X) :=
      ((MorphismProperty.Over.pullbackComp f₁ f₂).app X).symm ≪≫
        (MorphismProperty.Over.pullbackCongr w).app X ≪≫
          (MorphismProperty.Over.pullbackComp p q).app X
    have h₁ : σ.hom.app ((FEt.pullback p).obj ((FEt.pullback q).obj X)) = 𝟙 _ :=
      etaleFundamentalGroup.hom_app_pullback_eq_id Ω p t σ (hP _) _
    have h₂ := aut_app_eq_id_of_iso σ ρ.symm h₁
    simp only [etaleFundamentalGroup.map, autMap_hom_app, h₂]
    simp
  apply Iso.ext
  exact NatTrans.ext (funext key)

omit [IsSepClosed Ω] in
/-- V.7: if `f₁ ≫ f₂ = 𝟙`, the composite `π₁(T, t̄) → π₁(S) → π₁(T)` is the conjugation by an
isomorphism of fiber functors (a class of paths from `t̄` to `f₂(f₁(t̄))`). -/
theorem etaleFundamentalGroup.exists_map_comp_map_eq_conjAut (f₁ : T ⟶ S) (f₂ : S ⟶ T)
    (h : f₁ ≫ f₂ = 𝟙 T) (t : Spec (CommRingCat.of Ω) ⟶ T) :
    ∃ φ : FEt.fiber Ω t ≅ FEt.fiber Ω ((t ≫ f₁) ≫ f₂),
      (etaleFundamentalGroup.map Ω f₂ (t ≫ f₁)).comp (etaleFundamentalGroup.map Ω f₁ t) =
        φ.conjAut.toMonoidHom :=
  exists_autMap_comp_eq_conjAut _ _ _ _
    ((MorphismProperty.Over.pullbackComp f₁ f₂).symm ≪≫
      MorphismProperty.Over.pullbackCongr h ≪≫ FEt.pullbackId T)

end Trivial

end SGA.SGA1.ExposeV
