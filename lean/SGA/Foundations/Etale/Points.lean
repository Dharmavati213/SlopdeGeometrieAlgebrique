/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Conservative
import SGA.Foundations.Etale.Functoriality

/-!
# Fibers of inverse images at geometric points

The fiber of `f^* F` at a geometric point `s` of `X` is the fiber of `F` at the geometric point
`s ≫ f` of `Y` (`Scheme.sheafFiberEtalePullbackIso`). Since geometric points form a
conservative family of points of the small étale site (mathlib's
`Scheme.isConservativeFamilyOfPoints_pointSmallEtale'`), we deduce:

* the inverse image `f^*` of étale sheaves of sets is left exact;
* the inverse images along a jointly surjective family of étale morphisms jointly reflect
  isomorphisms and monomorphisms.

## References

* [SGA 4, Exposé VIII, 1.1 and 3.5][sga4]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

universe u

open CategoryTheory Limits

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

lemma pointSmallEtale_fiber_map_apply {S : Scheme.{u}} (s : Spec (.of Ω) ⟶ S)
    {W₁ W₂ : S.Etale} (g : W₁ ⟶ W₂) (x : (Scheme.pointSmallEtale s).fiber.obj W₁) :
    (Scheme.pointSmallEtale s).fiber.map g x = x ≫ (Scheme.Etale.forget S).map g :=
  rfl

@[simp]
lemma Etale.forget_map_left {S : Scheme.{u}} {W₁ W₂ : S.Etale} (g : W₁ ⟶ W₂) :
    ((Scheme.Etale.forget S).map g).left = g.left :=
  rfl

/-- The natural transformation `Φ_{s ≫ f}.fiber ⟶ u ⋙ Φ_s.fiber`. -/
noncomputable def pointSmallEtaleFiberHom :
    (Scheme.pointSmallEtale (s ≫ f)).fiber ⟶
      Etale.pullback f ⋙ (Scheme.pointSmallEtale s).fiber where
  app W := ↾fun (a : Over.mk (s ≫ f) ⟶ (Scheme.Etale.forget Y).obj W) ↦
    (Over.homMk (Limits.pullback.lift a.left s (by simpa using Over.w a))
      (Limits.pullback.lift_snd _ _ _) :
      Over.mk s ⟶ (Scheme.Etale.forget X).obj ((Etale.pullback f).obj W))
  naturality W₁ W₂ φ := by
    ext a
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · simp [pointSmallEtale_fiber_map_apply]
    · simp [pointSmallEtale_fiber_map_apply]

/-- The inverse of `pointSmallEtaleFiberHom`. -/
noncomputable def pointSmallEtaleFiberInv :
    Etale.pullback f ⋙ (Scheme.pointSmallEtale s).fiber ⟶
      (Scheme.pointSmallEtale (s ≫ f)).fiber where
  app W := ↾fun (b : Over.mk s ⟶ (Scheme.Etale.forget X).obj ((Etale.pullback f).obj W)) ↦
    (Over.homMk (b.left ≫ Limits.pullback.fst W.hom f) (by
      have : b.left ≫ Limits.pullback.snd W.hom f = s := Over.w b
      dsimp
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, this]) :
      Over.mk (s ≫ f) ⟶ (Scheme.Etale.forget Y).obj W)
  naturality W₁ W₂ φ := by
    ext b
    apply Over.OverMorphism.ext
    simp [pointSmallEtale_fiber_map_apply]

/-- The fiber functor of the point `s ≫ f` of the étale site of `Y` is the fiber functor of the
point `s` of the étale site of `X` composed with the base change functor. -/
noncomputable def pointSmallEtaleFiberIso :
    (Scheme.pointSmallEtale (s ≫ f)).fiber ≅
      Etale.pullback f ⋙ (Scheme.pointSmallEtale s).fiber where
  hom := pointSmallEtaleFiberHom f s
  inv := pointSmallEtaleFiberInv f s
  hom_inv_id := by
    ext W a
    apply Over.OverMorphism.ext
    simp [pointSmallEtaleFiberHom, pointSmallEtaleFiberInv]
  inv_hom_id := by
    ext W b
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · simp [pointSmallEtaleFiberHom, pointSmallEtaleFiberInv]
    · have : b.left ≫ Limits.pullback.snd W.hom f = s := Over.w b
      simpa [pointSmallEtaleFiberHom, pointSmallEtaleFiberInv] using this.symm

instance : InitiallySmall.{u} (Etale.pullback f ⋙ (Scheme.pointSmallEtale s).fiber).Elements := by
  let e := Cat.equivOfIso (Functor.elementsFunctor.mapIso (pointSmallEtaleFiberIso f s))
  have : e.functor.IsLeftAdjoint := e.toAdjunction.isLeftAdjoint
  exact @initiallySmall_of_initial_of_initiallySmall _ _ _ _
    (Scheme.pointSmallEtale (s ≫ f)).initiallySmall e.functor
    (Functor.initial_of_isLeftAdjoint e.functor)

/-- The fiber functor of the point of the étale site of `Y` obtained from the geometric point `s`
of `X` by base change is the composition of `f^*` with the fiber functor at `s`. -/
noncomputable def sheafFiberComapIso :
    ((Scheme.pointSmallEtale s).comap (Etale.pullback f)
      (Etale.coverPreserving_pullback f)).sheafFiber ≅
        etalePullback f ⋙ (Scheme.pointSmallEtale s).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberComapIso _ _ _ (Type u)

variable (X) in
lemma isConservativeFamilyOfPoints_pointSmallEtale :
    (ObjectProperty.ofObj (fun (x : X) ↦ Scheme.pointSmallEtale
      ((Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) _).2
        ⟨x, CommRingCat.ofHom
          (algebraMap (X.residueField x) _)⟩))).IsConservativeFamilyOfPoints :=
  Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

/-- The inverse image functor of étale sheaves is left exact (SGA 4 VIII 1.1). -/
instance : PreservesFiniteLimits (etalePullback f) := by
  constructor
  intro J _ _
  constructor
  intro K
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply (isConservativeFamilyOfPoints_pointSmallEtale
    X).jointlyReflectIsomorphisms_type.jointlyReflectsLimit
  rintro ⟨Φ, hΦ⟩
  refine Nonempty.some ?_
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  exact ⟨IsLimit.mapConeEquiv (sheafFiberComapIso f _)
    (isLimitOfPreserves _ (limit.isLimit K))⟩

/-- The point `s ≫ f` of the étale site of `Y` is isomorphic to the point obtained from `s` by
base change along `f`. -/
noncomputable def comapPointSmallEtaleIso :
    (Scheme.pointSmallEtale s).comap (Etale.pullback f) (Etale.coverPreserving_pullback f) ≅
      Scheme.pointSmallEtale (s ≫ f) where
  hom := ⟨(pointSmallEtaleFiberIso f s).hom⟩
  inv := ⟨(pointSmallEtaleFiberIso f s).inv⟩
  hom_inv_id := by
    ext1
    exact (pointSmallEtaleFiberIso f s).inv_hom_id
  inv_hom_id := by
    ext1
    exact (pointSmallEtaleFiberIso f s).hom_inv_id

/-- The fiber of `f^* F` at the geometric point `s` of `X` is the fiber of `F` at `s ≫ f`. -/
noncomputable def sheafFiberEtalePullbackIso :
    (Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := Type u) ≅
      etalePullback f ⋙ (Scheme.pointSmallEtale s).sheafFiber where
  hom := (comapPointSmallEtaleIso f s).hom.sheafFiber ≫ (sheafFiberComapIso f s).hom
  inv := (sheafFiberComapIso f s).inv ≫ (comapPointSmallEtaleIso f s).inv.sheafFiber
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc,
      ← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (comapPointSmallEtaleIso f s).inv.sheafFiber,
      ← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id, Category.id_comp, Iso.inv_hom_id]

/-- The inverse image functors along a jointly surjective family of étale morphisms jointly
reflect isomorphisms. -/
lemma isIso_of_forall_isIso_etalePullback {ι : Type*} {V : ι → Scheme.{u}} (e : ∀ i, V i ⟶ Y)
    [∀ i, Etale (e i)] (he : ∀ y : Y, ∃ i v, e i v = y)
    {A B : Sheaf Y.smallEtaleTopology (Type u)} (φ : A ⟶ B)
    (hφ : ∀ i, IsIso ((etalePullback (e i)).map φ)) : IsIso φ := by
  rw [(isConservativeFamilyOfPoints_pointSmallEtale Y).jointlyReflectIsomorphisms_type.isIso_iff]
  rintro ⟨Φ, hΦ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  dsimp only
  generalize (Scheme.SpecToEquivOfField (SeparableClosure (Y.residueField y)) Y).invFun
    ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩ = t
  obtain ⟨i, v, hv⟩ := he (t default)
  obtain ⟨l, rfl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (e i) t v hv
  rw [NatIso.isIso_map_iff (sheafFiberEtalePullbackIso (e i) l)]
  have := hφ i
  exact Functor.map_isIso (Scheme.pointSmallEtale l).sheafFiber ((etalePullback (e i)).map φ)

/-- The inverse image functors along a jointly surjective family of étale morphisms jointly
reflect monomorphisms. -/
lemma mono_of_forall_mono_etalePullback {ι : Type*} {V : ι → Scheme.{u}} (e : ∀ i, V i ⟶ Y)
    [∀ i, Etale (e i)] (he : ∀ y : Y, ∃ i v, e i v = y)
    {A B : Sheaf Y.smallEtaleTopology (Type u)} (φ : A ⟶ B)
    (hφ : ∀ i, Mono ((etalePullback (e i)).map φ)) : Mono φ := by
  rw [(isConservativeFamilyOfPoints_pointSmallEtale
    Y).jointlyReflectIsomorphisms_type.jointlyReflectMonomorphisms.mono_iff]
  rintro ⟨Φ, hΦ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  dsimp only
  generalize (Scheme.SpecToEquivOfField (SeparableClosure (Y.residueField y)) Y).invFun
    ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩ = t
  obtain ⟨i, v, hv⟩ := he (t default)
  obtain ⟨l, rfl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (e i) t v hv
  have := hφ i
  have : Mono ((etalePullback (e i) ⋙ (Scheme.pointSmallEtale l).sheafFiber).map φ) :=
    Functor.map_mono (Scheme.pointSmallEtale l).sheafFiber ((etalePullback (e i)).map φ)
  rw [← NatIso.naturality_2 (sheafFiberEtalePullbackIso (e i) l) φ]
  infer_instance

end AlgebraicGeometry.Scheme
