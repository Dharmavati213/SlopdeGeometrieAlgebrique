/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannLocalAffine
import SGA.Foundations.Analytic.RiemannSurfacePunctures

/-!
# SGA 1, Exposé XII, 5.1 passes to finite étale coverings

If the Riemann existence theorem holds for `X = Spec A`, it holds for every finite étale covering
`Y = Spec B → X` (`isEquivalence_pointsFunctor_of_finiteEtale`): a finite covering `E` of `Y(ℂ)`
is, through `Y(ℂ) → X(ℂ)`, a finite covering of `X(ℂ)`, hence `T(ℂ)` for a finite étale
`A`-algebra `T`; the projection `E → Y(ℂ)` is a morphism of coverings of `X(ℂ)`, hence comes from
an `A`-algebra map `B → T` (`Ψ` is full); then `T` is finite étale over `B`, and `T(ℂ) ≅ E` over
`Y(ℂ)`. (`Ψ` is fully faithful for `B` anyway.) With the Riemann existence theorem for `ℂ ∖ S`,
this covers every affine curve finite étale over some `ℂ ∖ S`, e.g. every smooth affine curve
minus finitely many points.

The topological input: the composite of two coverings with finite fibres is a covering
(`IsCoveringMap.comp_of_finite`, registry row C16), from xii4's
`IsCoveringMap.isClosedMap_of_finite` and `IsCoveringMap.t2Space`
(`SGA.Foundations.Analytic.RiemannSurfacePunctures`).
-/

noncomputable section

open CategoryTheory Topology Set

namespace IsCoveringMap

variable {E X B : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]
  {p : E → X} {q : X → B}

/-- The composite of two coverings with finite fibres is a covering with finite fibres. -/
theorem comp_of_finite [T2Space X] (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (hqfin : ∀ b, (q ⁻¹' {b}).Finite) (hpfin : ∀ x, (p ⁻¹' {x}).Finite) :
    IsCoveringMap (q ∘ p) := by
  have := hp.t2Space
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine ((hq.isClosedMap_of_finite hqfin).comp (hp.isClosedMap_of_finite hpfin))
    |>.isCoveringMapOn_of_isLocalHomeomorphOn (fun b _ ↦ ?_)
    (hq.isLocalHomeomorph.comp hp.isLocalHomeomorph).isLocalHomeomorphOn
  rw [preimage_comp, ← biUnion_of_singleton (q ⁻¹' {b}), preimage_iUnion₂]
  exact (hqfin b).biUnion fun x _ ↦ hpfin x

omit [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B] in
lemma finite_preimage_comp (hqfin : ∀ b, (q ⁻¹' {b}).Finite) (hpfin : ∀ x, (p ⁻¹' {x}).Finite)
    (b : B) : ((q ∘ p) ⁻¹' {b}).Finite := by
  rw [preimage_comp, ← biUnion_of_singleton (q ⁻¹' {b}), preimage_iUnion₂]
  exact (hqfin b).biUnion fun x _ ↦ hpfin x

end IsCoveringMap

namespace SGA.SGA1.ExposeXII

open CommAlgCat Opposite

namespace FiniteEtaleTransfer

variable {A : Type} [CommRing A] [Algebra ℂ A] (B : FiniteEtale.{0} A)

/-- A finite covering of `Y(ℂ)`, `Y = Spec B`, as a finite covering of `X(ℂ)`, `X = Spec A`. -/
def compCovering :
    letI := algebraOfFiniteEtale ℂ A B
    TopCat.FiniteCovering (TopCat.of (Points ℂ B)) →
      TopCat.FiniteCovering (TopCat.of (Points ℂ A)) :=
  letI := algebraOfFiniteEtale ℂ A B
  fun E ↦
    have : T2Space ((pointsFunctor ℂ A).obj (op B)).obj.left := Points.isEmbedding_coe.t2Space
    ⟨Over.mk (E.obj.hom ≫ ((pointsFunctor ℂ A).obj (op B)).obj.hom),
      ((pointsFunctor ℂ A).obj (op B)).isCoveringMap.comp_of_finite E.isCoveringMap
        ((pointsFunctor ℂ A).obj (op B)).property.2 E.property.2,
      fun b ↦ IsCoveringMap.finite_preimage_comp (q := ((pointsFunctor ℂ A).obj (op B)).obj.hom)
        (p := E.obj.hom) ((pointsFunctor ℂ A).obj (op B)).property.2 E.property.2 b⟩

/-- The projection `E → Y(ℂ)`, as a morphism of finite coverings of `X(ℂ)`. -/
def compCoveringHom
    (E : letI := algebraOfFiniteEtale ℂ A B; TopCat.FiniteCovering (TopCat.of (Points ℂ B))) :
    compCovering B E ⟶ (pointsFunctor ℂ A).obj (op B) :=
  letI := algebraOfFiniteEtale ℂ A B
  ObjectProperty.homMk (Over.homMk E.obj.hom rfl)

/-- A finite étale `A`-algebra `T` with an `A`-algebra map `φ : B → T`, as a finite étale
`B`-algebra. -/
def toB (T : FiniteEtale.{0} A) (φ : B.obj →ₐ[A] T.obj) : FiniteEtale.{0} B :=
  letI : Algebra B T := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A B T := .of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  haveI : Module.Finite B T := Module.Finite.of_restrictScalars_finite A B T
  haveI : Algebra.Etale B T := Algebra.Etale.of_restrictScalars A B T
  FiniteEtale.of B T

/-- `T` with its `ℂ`-structure through `B` is `T` with its `ℂ`-structure through `A`. -/
def toBAlgEquiv (T : FiniteEtale.{0} A) (φ : B.obj →ₐ[A] T.obj) :
    letI := algebraOfFiniteEtale ℂ A B
    letI := algebraOfFiniteEtale ℂ B (toB B T φ)
    letI := algebraOfFiniteEtale ℂ A T
    (toB B T φ).obj ≃ₐ[ℂ] T.obj :=
  letI := algebraOfFiniteEtale ℂ A B
  letI := algebraOfFiniteEtale ℂ B (toB B T φ)
  letI := algebraOfFiniteEtale ℂ A T
  { toRingEquiv := RingEquiv.refl _
    commutes' := fun c ↦ by
      change φ (algebraMap A B (algebraMap ℂ A c)) = algebraMap A T (algebraMap ℂ A c)
      exact φ.commutes _ }

/-- If `Ψ_A(T) ≅ E` over `X(ℂ)` and the projection `E → Y(ℂ)` is `Ψ_A(g)` for `g : B → T`, then
`T`, as a finite étale `B`-algebra, has `Ψ_B(T) ≅ E`. -/
def isoOfMap
    (E : letI := algebraOfFiniteEtale ℂ A B; TopCat.FiniteCovering (TopCat.of (Points ℂ B)))
    (T : (FiniteEtale.{0} A)ᵒᵖ) (i : (pointsFunctor ℂ A).obj T ≅ compCovering B E)
    (g : T ⟶ op B) (hg : (pointsFunctor ℂ A).map g = i.hom ≫ compCoveringHom B E) :
    letI := algebraOfFiniteEtale ℂ A B
    (pointsFunctor ℂ B).obj (op (toB B T.unop g.unop.hom.hom)) ≅ E :=
  letI := algebraOfFiniteEtale ℂ A B
  letI := algebraOfFiniteEtale ℂ B (toB B T.unop g.unop.hom.hom)
  letI := algebraOfFiniteEtale ℂ A T.unop
  ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo
    ((Points.homeomorph (toBAlgEquiv B T.unop g.unop.hom.hom)).symm.trans
      (TopCat.homeoOfIso ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso i)))) (by
    refine TopCat.hom_ext (ContinuousMap.ext fun χ ↦ ?_)
    have h1 := congr($(congrArg
      (fun k : (pointsFunctor ℂ A).obj T ⟶ (pointsFunctor ℂ A).obj (op B) ↦ k.hom.left) hg)
      ((Points.homeomorph (toBAlgEquiv B T.unop g.unop.hom.hom)).symm χ))
    exact h1.symm))

variable [Algebra.FiniteType ℂ A]

/-- XII.5.1 passes to finite étale coverings, for one covering: if `Ψ` is an equivalence for `A`,
every finite covering `E` of `Y(ℂ)`, `Y = Spec B` finite étale over `Spec A`, is `T(ℂ)` for a
finite étale `B`-algebra `T`. -/
theorem mem_essImage_of_isEquivalence [(pointsFunctor ℂ A).IsEquivalence]
    (E : letI := algebraOfFiniteEtale ℂ A B; TopCat.FiniteCovering (TopCat.of (Points ℂ B))) :
    letI := algebraOfFiniteEtale ℂ A B
    (pointsFunctor ℂ B).essImage E := by
  obtain ⟨T, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := pointsFunctor ℂ A) (compCovering B E)
  exact ⟨_, ⟨isoOfMap B E T i _ ((pointsFunctor ℂ A).map_preimage _)⟩⟩

end FiniteEtaleTransfer

/-- XII.5.1 passes to finite étale coverings: if the Riemann existence theorem holds for
`X = Spec A` (`A : Type` of finite type over `ℂ`), it holds for every finite étale covering
`Y = Spec B` of `X`. -/
theorem isEquivalence_pointsFunctor_of_finiteEtale {A : Type} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [(pointsFunctor ℂ A).IsEquivalence] (B : FiniteEtale.{0} A) :
    letI := algebraOfFiniteEtale ℂ A B
    (pointsFunctor ℂ B).IsEquivalence := by
  let := algebraOfFiniteEtale ℂ A B
  have := isScalarTower_of_finiteEtale ℂ A B
  have : Algebra.FiniteType ℂ B := .trans (S := A) inferInstance inferInstance
  have : (pointsFunctor ℂ B).EssSurj :=
    ⟨fun E ↦ FiniteEtaleTransfer.mem_essImage_of_isEquivalence B E⟩
  exact { }

end SGA.SGA1.ExposeXII
