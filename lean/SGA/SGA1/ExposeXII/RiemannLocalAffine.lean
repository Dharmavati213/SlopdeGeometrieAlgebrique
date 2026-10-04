/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannFull

/-!
# SGA 1, Exposé XII, 5.1: the affine and the scheme forms of `Ψ`

The Riemann existence theorem is stated twice: for finite étale algebras over `A` of finite type
over `ℂ` (`pointsFunctor ℂ A`, `RiemannExistenceStatement`) and for finite étale coverings of a
scheme `X` locally of finite type over `ℂ` (`schemePointsFunctor ℂ X`,
`SchemeRiemannExistenceStatement`). Here we compare the two for `X = Spec A`:

* `pointsFunctorIsoSpec`: `pointsFunctor ℂ A` is `S ↦ Spec S` (`specCoveringFunctor`, an
  equivalence by V.7) followed by `schemePointsFunctor ℂ (Spec A)` and by the transport of
  coverings along the homeomorphism `A(ℂ) ≃ (Spec A)(ℂ)` (`specHomeomorph`,
  `TopCat.FiniteCovering.mapHomeomorph`);
* consequently `pointsFunctor ℂ A` is full (instance, from step 1) of the proof of XII.5.1 for
  schemes, `SGA.SGA1.ExposeXII.RiemannFull`), `isEquivalence_pointsFunctor_iff`, and
  `riemannExistence_of_schemeRiemannExistence` (the scheme form implies the affine form, for
  `A : Type`).
-/

noncomputable section

universe u

open CategoryTheory Topology Set AlgebraicGeometry

namespace TopCat.FiniteCovering

variable {X Y : TopCat.{u}}

/-- Transport of finite coverings along a homeomorphism `e : X ≃ₜ Y`: a covering `p : E → X`
becomes `e ∘ p : E → Y`. -/
def mapHomeomorph (e : X ≃ₜ Y) : FiniteCovering X ⥤ FiniteCovering Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.map (TopCat.ofHom (e : C(X, Y))))
    fun E ↦ ⟨E.isCoveringMap.homeomorph_comp e, fun y ↦ by
      have : ((TopCat.ofHom (e : C(X, Y)) : X ⟶ Y).hom ∘ E.obj.hom.hom) ⁻¹' {y} =
          E.obj.hom ⁻¹' {e.symm y} := by
        ext a
        exact e.toEquiv.eq_symm_apply.symm
      exact this ▸ E.property.2 (e.symm y)⟩

@[simp] lemma mapHomeomorph_obj_left (e : X ≃ₜ Y) (E : FiniteCovering X) :
    ((mapHomeomorph e).obj E).obj.left = E.obj.left := rfl

/-- Transporting along `e` and then along `e.symm` gives back the original covering. -/
def mapHomeomorphCompSymmIso (e : X ≃ₜ Y) :
    mapHomeomorph e ⋙ mapHomeomorph e.symm ≅ 𝟭 (FiniteCovering X) :=
  NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
    ext a
    exact (e.symm_apply_apply (E.obj.hom a)).symm))) fun f ↦ by
    ext
    rfl

/-- Transport of finite coverings along a homeomorphism, as an equivalence of categories. -/
def mapHomeomorphEquivalence (e : X ≃ₜ Y) : FiniteCovering X ≌ FiniteCovering Y :=
  .mk (mapHomeomorph e) (mapHomeomorph e.symm) (mapHomeomorphCompSymmIso e).symm
    (by simpa using mapHomeomorphCompSymmIso e.symm)

instance (e : X ≃ₜ Y) : (mapHomeomorph e).IsEquivalence :=
  (mapHomeomorphEquivalence e).isEquivalence_functor

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

namespace SchemePoints

variable {K : Type u} [Field K]

attribute [local instance] specOver sectionsAlgebra

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K] (R : Type u) [CommRing R]
  [Algebra K R]

/-- The `K`-points of `R` are the `K`-points of `Spec R` (`specPoint`; `ΓSpecAlgEquiv` is in
`SGA.SGA1.ExposeXII.SchemePoints`). -/
def specPointHomeomorph : Points K R ≃ₜ SchemePoints K (Spec (.of R)) :=
  (Points.homeomorph (ΓSpecAlgEquiv (K := K) R)).trans homeomorphPoints.symm

@[simp] lemma specPointHomeomorph_apply (χ : Points K R) :
    specPointHomeomorph R χ = specPoint R χ :=
  (specPoint_eq_chart R χ).symm

lemma specPointHomeomorph_apply_val (χ : Points K R) :
    (specPointHomeomorph R χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) := by
  rw [specPointHomeomorph_apply]
  rfl

/-- `specPointHomeomorph`, for any `K`-scheme structure on `Spec R` whose structure morphism is
`Spec` of `K → R`. -/
def specPointHomeomorph' (i : (Spec (.of R)).Over (Spec (.of K)))
    (h : i.hom = Spec.map (CommRingCat.ofHom (algebraMap K R))) :
    Points K R ≃ₜ @SchemePoints K _ (Spec (.of R)) i where
  toFun χ := ⟨Spec.map (CommRingCat.ofHom χ.toRingHom),
    (congrArg (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ ·) h).trans (specPoint R χ).2⟩
  invFun p := (specPointHomeomorph R).symm ⟨p.1, (congrArg (p.1 ≫ ·) h).symm.trans p.2⟩
  left_inv χ := by
    refine ((specPointHomeomorph R).symm_apply_eq).mpr (Subtype.ext ?_)
    exact (specPointHomeomorph_apply_val R χ).symm
  right_inv p := by
    refine Subtype.ext ?_
    change Spec.map (CommRingCat.ofHom ((specPointHomeomorph R).symm _).toRingHom) = p.1
    rw [← specPointHomeomorph_apply_val]
    exact congrArg Subtype.val ((specPointHomeomorph R).apply_symm_apply _)
  continuous_toFun := by
    obtain ⟨f⟩ := i
    change f = _ at h
    subst h
    exact (specPointHomeomorph R).continuous.congr fun χ ↦
      Subtype.ext (specPointHomeomorph_apply_val R χ)
  continuous_invFun := by
    obtain ⟨f⟩ := i
    change f = _ at h
    subst h
    exact (specPointHomeomorph R).symm.continuous

lemma specPointHomeomorph'_apply_val (i : (Spec (.of R)).Over (Spec (.of K)))
    (h : i.hom = Spec.map (CommRingCat.ofHom (algebraMap K R))) (χ : Points K R) :
    (specPointHomeomorph' R i h χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) := rfl

end SchemePoints

end SGA.SGA1.ExposeXII

namespace SGA.SGA1.ExposeXII

open CommAlgCat Opposite

section Comparison

variable (A : Type) [CommRing A] [Algebra ℂ A]

attribute [local instance] SchemePoints.specOver

/-- The étale covering `Spec S → Spec A` of a finite étale `A`-algebra `S`. -/
def specCovering (S : FiniteEtale A) : FiniteEtaleCovering (Spec (.of A)) :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap A S))) <| by
    refine ⟨?_, ?_⟩
    · rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.mpr inferInstance

/-- `S ↦ Spec S`, from finite étale `A`-algebras to étale coverings of `Spec A`
(`ExposeV.specFunctor`, with objects written as `Spec S → Spec A`). -/
def specCoveringFunctor : (FiniteEtale A)ᵒᵖ ⥤ FiniteEtaleCovering (Spec (.of A)) where
  obj S := specCovering A S.unop
  map {S T} f := MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact f.unop.hom.hom.commutes a) trivial
  map_id S := by
    ext : 1
    exact Spec.map_id _
  map_comp f g := by
    ext : 1
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

/-- `specCoveringFunctor` is `ExposeV.specFunctor`. -/
def specCoveringFunctorIso : specCoveringFunctor A ≅ ExposeV.specFunctor (.of A) :=
  NatIso.ofComponents (fun S ↦ MorphismProperty.Over.isoMk (Iso.refl _)) fun f ↦ by
    ext : 1
    exact (Category.comp_id _).trans (Category.id_comp _).symm

instance : (specCoveringFunctor A).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _ (specCoveringFunctorIso A).symm
    (ExposeV.specEquivalence (.of A)).isEquivalence_functor

lemma overOfCovering_specCovering_hom (S : FiniteEtale A) :
    letI := algebraOfFiniteEtale ℂ A S
    (overOfCovering ℂ (Spec (.of A)) (specCovering A S)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
  let := algebraOfFiniteEtale ℂ A S
  change Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) =
    Spec.map (CommRingCat.ofHom ((algebraMap A S).comp (algebraMap ℂ A)))
  rw [← Spec.map_comp]
  rfl

/-- For a finite étale `A`-algebra `S`, the `ℂ`-points of `S` are the `ℂ`-points of the étale
covering `Spec S → Spec A`. -/
def pointsHomeomorphSpec (S : FiniteEtale A) :
    letI := algebraOfFiniteEtale ℂ A S
    Points ℂ S ≃ₜ ((schemePointsFunctor ℂ (Spec (.of A))).obj (specCovering A S)).obj.left :=
  letI := algebraOfFiniteEtale ℂ A S
  SchemePoints.specPointHomeomorph' S (overOfCovering ℂ (Spec (.of A)) (specCovering A S))
    (overOfCovering_specCovering_hom A S)

lemma pointsHomeomorphSpec_apply_val (S : FiniteEtale A) :
    letI := algebraOfFiniteEtale ℂ A S
    ∀ χ : Points ℂ S,
      (pointsHomeomorphSpec A S χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) := by
  intro χ
  rfl

/-- The `ℂ`-points of `Spec A` are the `ℂ`-points of `A`. -/
abbrev specHomeomorph : Points ℂ A ≃ₜ SchemePoints ℂ (Spec (.of A)) :=
  SchemePoints.specPointHomeomorph A

/-- Transport of finite coverings from `(Spec A)(ℂ)` to `A(ℂ)`. -/
abbrev specTransport : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ (Spec (.of A)))) ⥤
    TopCat.FiniteCovering (TopCat.of (Points ℂ A)) :=
  TopCat.FiniteCovering.mapHomeomorph (X := TopCat.of _) (Y := TopCat.of _) (specHomeomorph A).symm

/-- The comparison of the affine and the scheme forms of `Ψ`, on objects: for a finite étale
`A`-algebra `S`, the finite covering `S(ℂ) → X(ℂ)` is `(Spec S)(ℂ) → (Spec A)(ℂ)`. -/
def pointsFunctorObjIso (S : (FiniteEtale A)ᵒᵖ) :
    (pointsFunctor ℂ A).obj S ≅ (specTransport A).obj
      ((schemePointsFunctor ℂ (Spec (.of A))).obj ((specCoveringFunctor A).obj S)) :=
  ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo (pointsHomeomorphSpec A S.unop)) (by
    let := algebraOfFiniteEtale ℂ A S.unop
    have := isScalarTower_of_finiteEtale ℂ A S.unop
    refine TopCat.hom_ext (ContinuousMap.ext fun χ ↦ ?_)
    apply (specHomeomorph A).injective
    change specHomeomorph A ((specHomeomorph A).symm _) = specHomeomorph A (Points.proj A S.unop χ)
    rw [Homeomorph.apply_symm_apply]
    refine SchemePoints.ext ?_
    rw [SchemePoints.specPointHomeomorph_apply_val]
    change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A S.unop)) = _
    rw [← Spec.map_comp]
    rfl))

/-- XII.5.1: the affine form `pointsFunctor ℂ A` of `Ψ` is the scheme form for `Spec A`, composed
with the equivalence `S ↦ Spec S` (V.7) and with the transport of coverings along
`A(ℂ) ≃ (Spec A)(ℂ)`. -/
def pointsFunctorIsoSpec : pointsFunctor ℂ A ≅ specCoveringFunctor A ⋙
    schemePointsFunctor ℂ (Spec (.of A)) ⋙ specTransport A :=
  NatIso.ofComponents (pointsFunctorObjIso A) fun {S T} f ↦ by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (TopCat.hom_ext
      (ContinuousMap.ext fun χ ↦ ?_)))
    let := overOfCovering ℂ (Spec (.of A)) ((specCoveringFunctor A).obj T)
    let := algebraOfFiniteEtale ℂ A S.unop
    let := algebraOfFiniteEtale ℂ A T.unop
    refine SchemePoints.ext ?_
    change Spec.map (CommRingCat.ofHom (Points.map _ χ).toRingHom) =
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)
    rw [← Spec.map_comp]
    rfl

lemma locallyOfFiniteType_specOver [Algebra.FiniteType ℂ A] :
    LocallyOfFiniteType (Spec (.of A) ↘ Spec (.of ℂ)) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

attribute [local instance] locallyOfFiniteType_specOver

/-- XII.5.1, proof of 1), affine case: for `A` of finite type over `ℂ` (`A : Type`), the functor
`Ψ` from finite étale `A`-algebras to finite coverings of `X(ℂ)`, `X = Spec A`, is full (from the
scheme case, `exists_map_eq_schemePointsFunctor`). -/
instance [Algebra.FiniteType ℂ A] : (pointsFunctor ℂ A).Full :=
  Functor.Full.of_iso (pointsFunctorIsoSpec A).symm

/-- XII.5.1 for `X = Spec A`, `A : Type`: the affine form of the Riemann existence theorem for `A`
(`Ψ` an equivalence on finite étale `A`-algebras) is equivalent to the scheme form for
`Spec A`. -/
theorem isEquivalence_pointsFunctor_iff [Algebra.FiniteType ℂ A] :
    (pointsFunctor ℂ A).IsEquivalence ↔ (schemePointsFunctor ℂ (Spec (.of A))).IsEquivalence := by
  rw [Functor.isEquivalence_iff_of_iso (pointsFunctorIsoSpec A)]
  constructor
  · intro h
    have h2 : (schemePointsFunctor ℂ (Spec (.of A)) ⋙ specTransport A).IsEquivalence :=
      @Functor.isEquivalence_of_comp_left _ _ _ _ _ _ (specCoveringFunctor A) _ inferInstance h
    exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ (specTransport A) inferInstance h2
  · intro h
    infer_instance

end Comparison

/-- XII.5.1: the scheme form of the Riemann existence theorem implies the affine form (in
universe `0`). -/
theorem riemannExistence_of_schemeRiemannExistence (H : SchemeRiemannExistenceStatement) :
    RiemannExistenceStatement.{0} := fun A _ _ _ ↦
  letI := SchemePoints.specOver (K := ℂ) A
  haveI := locallyOfFiniteType_specOver A
  (isEquivalence_pointsFunctor_iff A).mpr (H (Spec (.of A)))

end SGA.SGA1.ExposeXII
