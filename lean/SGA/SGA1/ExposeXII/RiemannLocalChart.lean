/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannLocal
import SGA.SGA1.ExposeXII.RiemannLocalAffine

/-!
# SGA 1, Exposé XII, 5.1: reduction to the affine case

SGA reduces XII.5.1 to the case `X` affine, by step 1) of the proof (`Ψ` is fully faithful, so
the finite étale coverings attached to the restrictions of a finite covering `E` of `X(ℂ)` to the
affine opens of `X` glue). Here:

* `RiemannLocal.localModelsOfIso`: local models of a finite covering `E` of `X(ℂ)` over a family
  `B` of affine opens (`RiemannLocal.AffineOpenBasis`) from finite étale `Γ(X, U)`-algebras `S_U`
  with `S_U(ℂ) ≅ E|_U`, where `E|_U` is the restriction of `E` to `U(ℂ) ⊆ X(ℂ)`, transported to
  `Γ(X, U)(ℂ)` along the chart (`RiemannLocal.chartCovering`), and `Y_U = Spec S_U → U`;
* `RiemannLocal.mem_essImage_schemePointsFunctor`: the per-object form, `E` is in the essential
  image of `Ψ` if its restrictions to the members of `B` are in the essential images of the
  affine `Ψ`;
* `RiemannLocal.isEquivalence_schemePointsFunctor_of_essSurj`: XII.5.1 for `X` from the affine
  form for the `Γ(X, U)` (gluing, `SGA.SGA1.ExposeXII.RiemannLocal`);
* `schemeRiemannExistence_of_riemannExistence` and `schemeRiemannExistence_iff`: the scheme form
  `SchemeRiemannExistenceStatement` of XII.5.1 is equivalent to the affine form
  `RiemannExistenceStatement.{0}`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Set AlgebraicGeometry Opposite CommAlgCat

namespace SGA.SGA1.ExposeXII

namespace RiemannLocal

/-- The restriction of a finite covering `p : E → B` to a subset `t ⊆ B`: `p⁻¹(t) → t`. -/
def restrictCovering {B : TopCat.{u}} (E : TopCat.FiniteCovering B) (t : Set B) :
    TopCat.FiniteCovering (TopCat.of t) :=
  ⟨Over.mk (TopCat.ofHom ⟨t.restrictPreimage E.obj.hom, E.obj.hom.hom.continuous.restrictPreimage⟩),
    E.isCoveringMap.restrictPreimage t, fun x ↦ by
      refine ((E.property.2 x.1).preimage Subtype.val_injective.injOn).subset fun e he ↦ ?_
      change t.restrictPreimage E.obj.hom e = x at he
      change E.obj.hom e.1 = x.1
      rw [← he]
      rfl⟩

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

attribute [local instance] SchemePoints.sectionsAlgebra

omit [X.Over (Spec (.of ℂ))] in
/-- `U.2`, with its type written as `IsAffineOpen U.1` (rewriting with lemmas about
`IsAffineOpen` fails on the membership form `U.1 ∈ X.affineOpens`). -/
private lemma isAffineOpen_val (U : X.affineOpens) : IsAffineOpen U.1 := U.2

/-- The chart `Γ(X, U)(ℂ) → X(ℂ)` of an affine open `U`, as a homeomorphism onto `U(ℂ)`. -/
def chartHomeomorph (U : X.affineOpens) :
    Points ℂ Γ(X, U.1) ≃ₜ {x : SchemePoints ℂ X | x.pt ∈ U.1} :=
  (SchemePoints.isOpenEmbedding_chart (isAffineOpen_val U)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (SchemePoints.range_chart (isAffineOpen_val U)))

@[simp] lemma chartHomeomorph_apply_val (U : X.affineOpens) (φ : Points ℂ Γ(X, U.1)) :
    (chartHomeomorph U φ).1 = SchemePoints.chart (isAffineOpen_val U) φ := rfl

lemma isOpen_setOf_pt_mem (U : X.Opens) : IsOpen {x : SchemePoints ℂ X | x.pt ∈ U} :=
  U.isOpen.preimage SchemePoints.continuous_pt

variable (E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ X)))

/-- The restriction of a finite covering `E` of `X(ℂ)` to an affine open `U`, as a finite covering
of `Γ(X, U)(ℂ)` (through the chart). -/
def chartCovering (U : X.affineOpens) : TopCat.FiniteCovering (TopCat.of (Points ℂ Γ(X, U.1))) :=
  (TopCat.FiniteCovering.mapHomeomorph (X := TopCat.of {x : SchemePoints ℂ X | x.pt ∈ U.1})
    (Y := TopCat.of (Points ℂ Γ(X, U.1))) (chartHomeomorph U).symm).obj
    (restrictCovering E {x : SchemePoints ℂ X | x.pt ∈ U.1})

lemma chart_chartCovering_hom (U : X.affineOpens) (e : (chartCovering E U).obj.left) :
    SchemePoints.chart (isAffineOpen_val U) ((chartCovering E U).obj.hom e) = E.obj.hom e.1 := by
  change ((chartHomeomorph U) ((chartHomeomorph U).symm ⟨E.obj.hom e.1, e.2⟩)).1 = _
  rw [Homeomorph.apply_symm_apply]

section LocalModel

variable {E} {U : X.affineOpens} (S : FiniteEtale Γ(X, U.1))

/-- The covering `Spec S → U` of a finite étale `Γ(X, U)`-algebra `S`. -/
def chartπ : Spec (.of S) ⟶ U.1.toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) S)) ≫ (isAffineOpen_val U).isoSpec.inv

omit [X.Over (Spec (.of ℂ))] in
lemma chartπ_ι : chartπ S ≫ U.1.ι = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) S)) ≫
    (isAffineOpen_val U).fromSpec := by
  rw [chartπ, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

instance : IsFinite (chartπ S) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) S))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [chartπ]
  infer_instance

instance : Etale (chartπ S) := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  rw [chartπ]
  infer_instance

lemma overVia_chartπ_hom :
    letI := algebraOfFiniteEtale ℂ Γ(X, U.1) S
    (overVia (chartπ S ≫ U.1.ι)).hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
  let := algebraOfFiniteEtale ℂ Γ(X, U.1) S
  change (chartπ S ≫ U.1.ι) ≫ X ↘ Spec (.of ℂ) = _
  rw [chartπ_ι, Category.assoc, SchemePoints.fromSpec_over, ← Spec.map_comp]
  rfl

/-- The `ℂ`-points of `Spec S` (with its `ℂ`-structure through `Spec S → U ⊆ X`) are the
`ℂ`-points of `S`. -/
def chartPointsHomeomorph :
    letI := algebraOfFiniteEtale ℂ Γ(X, U.1) S
    Points ℂ S ≃ₜ @SchemePoints ℂ _ (Spec (.of S)) (overVia (chartπ S ≫ U.1.ι)) :=
  letI := algebraOfFiniteEtale ℂ Γ(X, U.1) S
  SchemePoints.specPointHomeomorph' S _ (overVia_chartπ_hom S)

lemma chartPointsHomeomorph_apply_val :
    letI := algebraOfFiniteEtale ℂ Γ(X, U.1) S
    ∀ χ : Points ℂ S, (chartPointsHomeomorph S χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) :=
  fun _ ↦ rfl

/-- The `ℂ`-structure of `Spec S`, through `Spec S → U ⊆ X`. -/
abbrev chartOver : (Spec (.of S)).Over (Spec (.of ℂ)) := overVia (chartπ S ≫ U.1.ι)

attribute [local instance] chartOver

instance : (chartπ S ≫ U.1.ι).IsOver (Spec (.of ℂ)) := isOverVia (chartπ S ≫ U.1.ι)

variable (ψ : (pointsFunctor ℂ Γ(X, U.1)).obj (op S) ≅ chartCovering E U)

/-- The homeomorphism `S(ℂ) ≃ E|_U` underlying `ψ`. -/
def chartLeftHomeomorph :
    ((pointsFunctor ℂ Γ(X, U.1)).obj (op S)).obj.left ≃ₜ (chartCovering E U).obj.left :=
  TopCat.homeoOfIso ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso ψ)

lemma chartCovering_hom_chartLeftHomeomorph
    (p : ((pointsFunctor ℂ Γ(X, U.1)).obj (op S)).obj.left) :
    (chartCovering E U).obj.hom (chartLeftHomeomorph S ψ p) =
      ((pointsFunctor ℂ Γ(X, U.1)).obj (op S)).obj.hom p :=
  congr($(Over.w ψ.hom.hom) p)

/-- The local model of `E` over `U` given by `S` and `ψ`: `(Spec S)(ℂ) ≃ S(ℂ) ≃ E|_U ⊆ E`. -/
def chartφ (y : SchemePoints ℂ (Spec (.of S))) : E.obj.left :=
  (chartLeftHomeomorph S ψ ((chartPointsHomeomorph S).symm y)).1

lemma isOpenEmbedding_chartφ : IsOpenEmbedding (chartφ S ψ) :=
  (isOpen_setOf_pt_mem U.1).preimage E.obj.hom.hom.continuous |>.isOpenEmbedding_subtypeVal
    |>.comp (chartLeftHomeomorph S ψ).isOpenEmbedding
    |>.comp (chartPointsHomeomorph S).symm.isOpenEmbedding

lemma range_chartφ : range (chartφ S ψ) = E.obj.hom ⁻¹' {x | x.pt ∈ U.1} := by
  ext e
  constructor
  · rintro ⟨y, rfl⟩
    exact (chartLeftHomeomorph S ψ ((chartPointsHomeomorph S).symm y)).2
  · intro he
    let q : (chartCovering E U).obj.left := ⟨e, he⟩
    refine ⟨chartPointsHomeomorph S ((chartLeftHomeomorph S ψ).symm q), ?_⟩
    exact (congrArg (fun z ↦ (chartLeftHomeomorph S ψ z).1)
      ((chartPointsHomeomorph S).symm_apply_apply _)).trans
      (congrArg Subtype.val ((chartLeftHomeomorph S ψ).apply_symm_apply q))

lemma hom_chartφ (y : SchemePoints ℂ (Spec (.of S))) :
    E.obj.hom (chartφ S ψ y) = SchemePoints.map (chartπ S ≫ U.1.ι) y := by
  let := algebraOfFiniteEtale ℂ Γ(X, U.1) S
  have := isScalarTower_of_finiteEtale ℂ Γ(X, U.1) S
  obtain ⟨χ, rfl⟩ := (chartPointsHomeomorph S).surjective y
  have hχ : chartφ S ψ (chartPointsHomeomorph S χ) = (chartLeftHomeomorph S ψ χ).1 :=
    congrArg (fun z ↦ (chartLeftHomeomorph S ψ z).1) ((chartPointsHomeomorph S).symm_apply_apply χ)
  rw [hχ, ← chart_chartCovering_hom]
  refine (congrArg (SchemePoints.chart (isAffineOpen_val U))
    (chartCovering_hom_chartLeftHomeomorph S ψ χ)).trans (SchemePoints.ext ?_)
  have h1 : ((pointsFunctor ℂ Γ(X, U.1)).obj (op S)).obj.hom χ = Points.proj Γ(X, U.1) S χ := rfl
  have h2 : (SchemePoints.chart (isAffineOpen_val U) (Points.proj Γ(X, U.1) S χ)).1 =
      Spec.map (CommRingCat.ofHom (Points.proj Γ(X, U.1) S χ).toRingHom) ≫
        (isAffineOpen_val U).fromSpec := rfl
  have h3 : (SchemePoints.map (chartπ S ≫ U.1.ι) (chartPointsHomeomorph S χ)).1 =
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ chartπ S ≫ U.1.ι := rfl
  have h4 : CommRingCat.ofHom (Points.proj Γ(X, U.1) S χ).toRingHom =
      CommRingCat.ofHom (algebraMap Γ(X, U.1) S) ≫ CommRingCat.ofHom χ.toRingHom := by
    ext a
    rfl
  refine (congrArg (fun φ ↦ (SchemePoints.chart (isAffineOpen_val U) φ).1) h1).trans
    (h2.trans (Eq.trans ?_ h3.symm))
  rw [h4, Spec.map_comp, Category.assoc, chartπ_ι]

end LocalModel

/-- XII.5.1, reduction to the affine case: local models of `E` over a family `B` of affine opens,
from finite étale `Γ(X, U)`-algebras `S_U` with `S_U(ℂ) ≅ E|_U` (`chartCovering`). -/
def localModelsOfIso (B : AffineOpenBasis X) (S : ∀ U : B.I, FiniteEtale Γ(X, U.1))
    (ψ : ∀ U : B.I, (pointsFunctor ℂ Γ(X, U.1)).obj (op (S U)) ≅
      chartCovering E ⟨U.1, B.isAffineOpen U.2⟩) :
    LocalModels B E where
  Y U := Spec (.of (S U))
  π U := chartπ (U := ⟨U.1, B.isAffineOpen U.2⟩) (S U)
  isFinite _ := inferInstance
  etale _ := inferInstance
  φ U := chartφ (U := ⟨U.1, B.isAffineOpen U.2⟩) (S U) (ψ U)
  isOpenEmbedding U := isOpenEmbedding_chartφ (U := ⟨U.1, B.isAffineOpen U.2⟩) (S U) (ψ U)
  range_φ U := range_chartφ (U := ⟨U.1, B.isAffineOpen U.2⟩) (S U) (ψ U)
  hom_φ U := hom_chartφ (U := ⟨U.1, B.isAffineOpen U.2⟩) (S U) (ψ U)

variable [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] in
/-- XII.5.1, reduction to the affine case, for one covering: a finite covering `E` of `X(ℂ)` is
in the essential image of `Ψ` as soon as, for a family `B` of affine opens of `X` forming a basis
of the topology (e.g. the affine opens contained in some member of an open cover), its
restriction to every `U` in `B` is in the essential image of the affine `Ψ` for `Γ(X, U)`. -/
theorem mem_essImage_schemePointsFunctor (B : AffineOpenBasis X)
    (H : ∀ U : B.I, (pointsFunctor ℂ Γ(X, U.1)).essImage
      (chartCovering E ⟨U.1, B.isAffineOpen U.2⟩)) :
    (schemePointsFunctor ℂ X).essImage E :=
  (localModelsOfIso E B (fun U ↦ (H U).choose.unop) fun U ↦ (H U).choose_spec.some).mem_essImage

variable [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] in
/-- XII.5.1 for `X`, from the affine form for the rings `Γ(X, U)`, `U ⊆ X` affine open (SGA's
reduction to the affine case): if the affine `Ψ` is essentially surjective for every `Γ(X, U)`,
then `Ψ` is an equivalence for `X`. -/
theorem isEquivalence_schemePointsFunctor_of_essSurj
    (H : ∀ U : X.affineOpens, (pointsFunctor ℂ Γ(X, U.1)).EssSurj) :
    (schemePointsFunctor ℂ X).IsEquivalence where
  essSurj := ⟨fun E ↦ mem_essImage_schemePointsFunctor E (AffineOpenBasis.top X) fun U ↦
    (H ⟨U.1, U.2⟩).mem_essImage _⟩

end RiemannLocal

/-- XII.5.1: the affine form of the Riemann existence theorem (`RiemannExistenceStatement`, for
`A : Type`) implies the scheme form, by gluing over the affine opens
(`RiemannLocal.isEquivalence_schemePointsFunctor_of_essSurj`). -/
theorem schemeRiemannExistence_of_riemannExistence (H : RiemannExistenceStatement.{0}) :
    SchemeRiemannExistenceStatement := by
  intro X _ _
  refine RiemannLocal.isEquivalence_schemePointsFunctor_of_essSurj fun U ↦ ?_
  let := SchemePoints.sectionsAlgebra (K := ℂ) U.1
  have := SchemePoints.finiteType_sections (K := ℂ) U.2
  have := H Γ(X, U.1)
  infer_instance

/-- XII.5.1: the scheme form and the affine form (for `A : Type`) of the Riemann existence
theorem are equivalent. -/
theorem schemeRiemannExistence_iff :
    SchemeRiemannExistenceStatement ↔ RiemannExistenceStatement.{0} :=
  ⟨riemannExistence_of_schemeRiemannExistence, schemeRiemannExistence_of_riemannExistence⟩

end SGA.SGA1.ExposeXII
