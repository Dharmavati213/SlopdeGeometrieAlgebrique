/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherDescent
import SGA.SGA1.ExposeXII.RiemannLocalAffine

/-!
# SGA 1, Exposé XII, 5.1, proof of 2) a): descent along finite surjective maps, affine form

`riemannExistenceFiniteDescent : RiemannExistenceFiniteDescentStatement`: for an injective finite
map `φ : A → B` of `ℂ`-algebras of finite type and a finite covering `E` of `A(ℂ)`, if the pullback
of `E` to `B(ℂ)` comes from a finite étale `B`-algebra, then `E` comes from a finite étale
`A`-algebra. This is the scheme form `RiemannHigher.mem_essImage_schemePointsFunctor_of_isFinite`
for `Spec B → Spec A` (finite, and surjective since `φ` is injective and integral), transported
along `A(ℂ) ≃ (Spec A)(ℂ)`:

* `RiemannHigher.mem_essImage_pointsFunctor_iff`: a covering of `A(ℂ)` is in the essential image
  of the affine `Ψ` iff its transport to `(Spec A)(ℂ)` is in that of the scheme `Ψ`;
* `RiemannHigher.baseChangeSpecIso`: the transport commutes with base change along `φ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology Set

namespace SGA.SGA1.ExposeXII

namespace RiemannHigher

open CommAlgCat Opposite

section Affine

attribute [local instance] SchemePoints.specOver locallyOfFiniteType_specOver

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Transport of finite coverings from `A(ℂ)` to `(Spec A)(ℂ)`. -/
abbrev toSpecCovering (A : Type) [CommRing A] [Algebra ℂ A] :
    TopCat.FiniteCovering (TopCat.of (Points ℂ A)) ⥤
      TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ (Spec (.of A)))) :=
  TopCat.FiniteCovering.mapHomeomorph (X := TopCat.of _) (Y := TopCat.of _) (specHomeomorph A)

/-- A finite covering of `A(ℂ)` is in the essential image of the affine `Ψ` if and only if its
transport to `(Spec A)(ℂ)` is in the essential image of the scheme `Ψ`. -/
lemma mem_essImage_pointsFunctor_iff [Algebra.FiniteType ℂ A]
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) :
    (pointsFunctor ℂ A).essImage E ↔
      (schemePointsFunctor ℂ (Spec (.of A))).essImage ((toSpecCovering A).obj E) := by
  -- `toSpecCovering A ⋙ specTransport A ≅ 𝟭`
  let ι₁ : toSpecCovering A ⋙ specTransport A ≅ 𝟭 _ :=
    TopCat.FiniteCovering.mapHomeomorphCompSymmIso (X := TopCat.of (Points ℂ A))
      (Y := TopCat.of (SchemePoints ℂ (Spec (.of A)))) (specHomeomorph A)
  let ι₂ : specTransport A ⋙ toSpecCovering A ≅ 𝟭 _ :=
    TopCat.FiniteCovering.mapHomeomorphCompSymmIso (X := TopCat.of (SchemePoints ℂ (Spec (.of A))))
      (Y := TopCat.of (Points ℂ A)) (specHomeomorph A).symm
  constructor
  · rintro ⟨S, ⟨i⟩⟩
    refine ⟨(specCoveringFunctor A).obj S, ⟨?_⟩⟩
    exact (ι₂.app _).symm ≪≫ (toSpecCovering A).mapIso
      (((pointsFunctorIsoSpec A).app S).symm ≪≫ i)
  · rintro ⟨Y, ⟨j⟩⟩
    obtain ⟨S, ⟨k⟩⟩ := Functor.EssSurj.mem_essImage (F := specCoveringFunctor A) Y
    refine ⟨S, ⟨?_⟩⟩
    exact (pointsFunctorIsoSpec A).app S ≪≫
      (specTransport A).mapIso ((schemePointsFunctor ℂ (Spec (.of A))).mapIso k ≪≫ j) ≪≫ ι₁.app E

/-- `Spec` of a `ℂ`-algebra map. -/
abbrev specMap (φ : A →ₐ[ℂ] B) : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

instance (φ : A →ₐ[ℂ] B) : (specMap φ).IsOver (Spec (.of ℂ)) := ⟨by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact φ.commutes c⟩

lemma map_specMap_specHomeomorph (φ : A →ₐ[ℂ] B) (χ : Points ℂ B) :
    SchemePoints.map (specMap φ) (specHomeomorph B χ) = specHomeomorph A (Points.map φ χ) := by
  refine SchemePoints.ext ?_
  change (specHomeomorph B χ).1 ≫ specMap φ = (specHomeomorph A (Points.map φ χ)).1
  rw [SchemePoints.specPointHomeomorph_apply_val, SchemePoints.specPointHomeomorph_apply_val,
    ← Spec.map_comp]
  rfl

/-- The transport to `Spec` commutes with base change: for `φ : A → B`, the pullback of a
covering `E` of `A(ℂ)` to `B(ℂ)`, transported to `(Spec B)(ℂ)`, is the pullback along
`(Spec B)(ℂ) → (Spec A)(ℂ)` of the transport of `E`. -/
def baseChangeSpecIso (φ : A →ₐ[ℂ] B) (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) :
    (toSpecCovering B).obj ((TopCat.FiniteCovering.baseChange (pointsHom φ)).obj E) ≅
      (TopCat.FiniteCovering.baseChange (schemePointsHom (specMap φ))).obj
        ((toSpecCovering A).obj E) := by
  refine TopCat.FiniteCovering.isoOfBijective
    ⟨fun q : (Points.map φ).Pullback E.obj.hom ↦
      (⟨(specHomeomorph B q.1.1, q.1.2), by
        change SchemePoints.map (specMap φ) _ = specHomeomorph A (E.obj.hom q.1.2)
        rw [map_specMap_specHomeomorph, ← q.2]⟩ : (SchemePoints.map (specMap φ)).Pullback
          ((toSpecCovering A).obj E).obj.hom), by fun_prop⟩ (fun _ ↦ rfl)
    ⟨fun q₁ q₂ h ↦ ?_, fun q ↦ ?_⟩
  · have h₁ : specHomeomorph B (q₁ : (Points.map φ).Pullback E.obj.hom).1.1 =
        specHomeomorph B (q₂ : (Points.map φ).Pullback E.obj.hom).1.1 :=
      congrArg (fun x : (SchemePoints.map (specMap φ)).Pullback
        ((toSpecCovering A).obj E).obj.hom ↦ x.1.1) h
    have h₂ : (q₁ : (Points.map φ).Pullback E.obj.hom).1.2 =
        (q₂ : (Points.map φ).Pullback E.obj.hom).1.2 :=
      congrArg (fun x : (SchemePoints.map (specMap φ)).Pullback
        ((toSpecCovering A).obj E).obj.hom ↦ x.1.2) h
    exact Subtype.ext (Prod.ext ((specHomeomorph B).injective h₁) h₂)
  · obtain ⟨⟨p, e⟩, hpe⟩ := q
    refine ⟨(⟨((specHomeomorph B).symm p, e), ?_⟩ : (Points.map φ).Pullback E.obj.hom), ?_⟩
    · apply (specHomeomorph A).injective
      rw [← map_specMap_specHomeomorph, Homeomorph.apply_symm_apply]
      exact hpe
    · refine Subtype.ext (Prod.ext ?_ rfl)
      exact (specHomeomorph B).apply_symm_apply p

end Affine

end RiemannHigher

open RiemannHigher

attribute [local instance] SchemePoints.specOver locallyOfFiniteType_specOver in
/-- XII.5.1, proof of 2) a), affine form: descent of the Riemann existence theorem, for one
covering, along an injective finite map `A → B` of `ℂ`-algebras of finite type (e.g. the
normalization of a reduced `A`), from the scheme form `mem_essImage_schemePointsFunctor_of_isFinite`
for `Spec B → Spec A`. -/
theorem riemannExistenceFiniteDescent : RiemannExistenceFiniteDescentStatement := by
  intro A B _ _ _ _ _ _ φ hfin hinj E h
  rw [mem_essImage_pointsFunctor_iff] at h ⊢
  have : IsFinite (specMap φ) := (IsFinite.SpecMap_iff _).mpr hfin
  have : Surjective (specMap φ) := ⟨(RingHom.IsIntegral.comap_surjective hfin.to_isIntegral hinj :)⟩
  refine mem_essImage_schemePointsFunctor_of_isFinite (specMap φ) _ ?_
  obtain ⟨Y, ⟨j⟩⟩ := h
  exact ⟨Y, ⟨j ≪≫ baseChangeSpecIso φ E⟩⟩

end SGA.SGA1.ExposeXII
