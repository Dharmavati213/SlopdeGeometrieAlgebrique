/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Conj
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.Foundations.Topology.FiniteCovering
import SGA.SGA1.ExposeV.FiniteEtaleSpec

/-!
# SGA 1, Exposé XII, §5: the Riemann existence theorem

XII.5.1 states that for a scheme `X` locally of finite type over `ℂ`, the functor
`X' ↦ X'^an` from finite étale coverings of `X` to finite étale coverings of `X^an` is an
equivalence; XII.5.2 deduces that the étale fundamental group of `X` is the profinite completion
of the topological fundamental group of `X^an`.

Here:
* `schemePointsFunctor K X` is the functor `Ψ` on points, from the category `FEt X` of V.7
  (finite étale `X`-schemes) to the category `TopCat.FiniteCovering` of finite coverings of `X(K)`
  (`SchemePoints.isCoveringMap_map`), and `SchemeRiemannExistenceStatement` records XII.5.1;
* for `X = Spec A`, `pointsFunctor 𝕜 A` is the functor `Ψ` on points, from finite étale
  `A`-algebras to finite coverings of `X(𝕜)`, for any proper nontrivially normed field `𝕜`
  (`Points.isCoveringMap_proj`);
  it is compatible with the fibre functors (`pointsFunctorCompFiberIso`) and faithful for `A` of
  finite type over an algebraically closed `𝕜` (instance below);
* `RiemannExistenceStatement` records XII.5.1 (affine case) and
  `FundamentalGroupComparisonStatement` records XII.5.2; `fundamentalGroupComparison` derives
  the latter from the former, the connectedness comparison XII.2.4 and the topological
  description of finite coverings of `X(ℂ)` (`CoveringFundamentalGroupStatement`), through the
  formal comparison of automorphism groups of fibre functors `autContinuousMulEquiv`. The last
  two inputs are proved (`Points.connectedComparison`, `coveringFundamentalGroupStatement`), so
  XII.5.2 follows from XII.5.1 alone (`fundamentalGroupComparison_of_riemannExistence`,
  `StatementCorollaries.lean`).

What is known about XII.5.1 (proved in later files; XII.5.1 itself is open in general):

* step 1) of SGA's proof: `Ψ` is fully faithful over `ℂ`, for `X : Scheme.{0}` (faithful:
  instance in `FundamentalGroup.lean`; full: instance in `RiemannFull.lean`) and for `A : Type`
  (faithful: instance below; full: instance in `RiemannLocalAffine.lean`);
* the scheme form and the affine form are equivalent
  (`schemeRiemannExistence_iff : SchemeRiemannExistenceStatement ↔ RiemannExistenceStatement.{0}`,
  `RiemannLocalChart.lean`), and the affine form does not depend on the universe
  (`riemannExistence_iff_zero`, `RiemannReductionUniverse.lean`);
* proved cases: `X(ℂ)` simply connected
  (`isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`, e.g. `𝔸ⁿ_ℂ`,
  `riemannExistence_mvPolynomial`; `RiemannSimplyConnected.lean`), `𝔾_{m,ℂ}`
  (`riemannExistence_laurentPolynomial`, `RiemannKummer.lean`), and `ℂ` minus a finite set
  (`PuncturedPlane.riemannExistence_coordRing`) together with its finite étale coverings
  (`PuncturedPlane.riemannExistence_finiteEtale`), both in `GAGAFiberSeparating.lean` (this
  project's route, not SGA's).

The analytic parts of §5 (XII.5.3, the Grauert–Remmert theorem XII.5.4, XII.5.5) concern normal
analytic spaces, which mathlib does not have.
-/

noncomputable section

namespace SGA.SGA1.ExposeXII

open CategoryTheory Topology Set

universe w u

section PointsFunctor

variable (𝕜 : Type w) [NontriviallyNormedField 𝕜] (A : Type u) [CommRing A] [Algebra 𝕜 A]

open CommAlgCat

/-- A finite étale `A`-algebra, as a `𝕜`-algebra through `A`. -/
abbrev algebraOfFiniteEtale (S : FiniteEtale.{u} A) : Algebra 𝕜 S :=
  ((algebraMap A S).comp (algebraMap 𝕜 A)).toAlgebra

lemma isScalarTower_of_finiteEtale (S : FiniteEtale.{u} A) :
    letI := algebraOfFiniteEtale 𝕜 A S
    IsScalarTower 𝕜 A S :=
  letI := algebraOfFiniteEtale 𝕜 A S
  .of_algebraMap_eq fun _ ↦ rfl

variable [ProperSpace 𝕜]

/-- XII.5.1, the functor `Ψ` on points: the finite covering `S(𝕜) → X(𝕜)` of a finite étale
`A`-algebra `S` (`Points.isCoveringMap_proj`). -/
def coveringOfFiniteEtale (S : FiniteEtale.{u} A) :
    TopCat.FiniteCovering (TopCat.of (Points 𝕜 A)) :=
  letI := algebraOfFiniteEtale 𝕜 A S
  haveI := isScalarTower_of_finiteEtale 𝕜 A S
  ⟨Over.mk (TopCat.ofHom ⟨Points.proj A S, Points.continuous_map _⟩),
    Points.isCoveringMap_proj, Points.finite_proj_preimage⟩

/-- XII.5.1: the functor `Ψ` from finite étale `A`-algebras (i.e. finite étale coverings of
`X = Spec A`) to finite coverings of `X(𝕜)`. -/
def pointsFunctor : (FiniteEtale.{u} A)ᵒᵖ ⥤ TopCat.FiniteCovering (TopCat.of (Points 𝕜 A)) where
  obj S := coveringOfFiniteEtale 𝕜 A S.unop
  map {S T} f :=
    letI := algebraOfFiniteEtale 𝕜 A S.unop
    letI := algebraOfFiniteEtale 𝕜 A T.unop
    haveI := isScalarTower_of_finiteEtale 𝕜 A S.unop
    haveI := isScalarTower_of_finiteEtale 𝕜 A T.unop
    ObjectProperty.homMk (Over.homMk (TopCat.ofHom
      ⟨Points.map (f.unop.hom.hom.restrictScalars 𝕜), Points.continuous_map _⟩) (by
        ext ψ a
        let ψ' : Points 𝕜 S.unop := ψ
        exact congrArg ψ' (f.unop.hom.hom.commutes a)))

/-- The fibre of `S(𝕜) → X(𝕜)` over `φ` is the set of `A`-algebra maps `S → 𝕜`, where `𝕜` is an
`A`-algebra through `φ`. -/
def fiberEquiv (φ : Points 𝕜 A) (S : FiniteEtale.{u} A) :
    letI := algebraOfFiniteEtale 𝕜 A S
    haveI := isScalarTower_of_finiteEtale 𝕜 A S
    (Points.proj A S ⁻¹' {φ} : Set (Points 𝕜 S)) ≃
      @AlgHom A S 𝕜 _ _ _ _ φ.toRingHom.toAlgebra :=
  letI := algebraOfFiniteEtale 𝕜 A S
  haveI := isScalarTower_of_finiteEtale 𝕜 A S
  Points.fiberEquivAlgHom φ

/-- The fibre functor on finite étale `A`-algebras at the geometric point `φ : A → 𝕜`. -/
abbrev etaleFiber (φ : Points 𝕜 A) : (FiniteEtale.{u} A)ᵒᵖ ⥤ FintypeCat.{max u w} :=
  @FiniteEtale.fiber A _ 𝕜 _ φ.toRingHom.toAlgebra

/-- The functor `Ψ` is compatible with the fibre functors at `φ`. -/
def pointsFunctorCompFiberIso (φ : Points 𝕜 A) :
    pointsFunctor 𝕜 A ⋙ TopCat.FiniteCovering.fiber φ ≅ etaleFiber 𝕜 A φ :=
  NatIso.ofComponents (fun S ↦ FintypeCat.equivEquivIso (fiberEquiv 𝕜 A φ S.unop)) fun f ↦ by
    ext ψ
    rfl

/-- XII.5.1, proof of 1), faithfulness: the functor `Ψ` is faithful when `A` is of finite type
over the algebraically closed field `𝕜`. -/
instance [IsAlgClosed 𝕜] [Algebra.FiniteType 𝕜 A] : (pointsFunctor 𝕜 A).Faithful where
  map_injective {S T} f g h := by
    let := algebraOfFiniteEtale 𝕜 A S.unop
    let := algebraOfFiniteEtale 𝕜 A T.unop
    have := isScalarTower_of_finiteEtale 𝕜 A S.unop
    have := isScalarTower_of_finiteEtale 𝕜 A T.unop
    have : Algebra.FiniteType 𝕜 S.unop :=
      .trans (S := A) inferInstance inferInstance
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (CommAlgCat.hom_ext ?_))
    refine Points.algHom_ext_of_map_eq (K := 𝕜) fun ψ ↦ ?_
    exact congr($(congr(($h).hom.left)) ψ)

end PointsFunctor

section Galois

open PreGaloisCategory

/-- XII.5.2, formal part: an equivalence of categories compatible with fibre functors identifies
the (profinite) automorphism groups of the fibre functors. -/
def autContinuousMulEquiv {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    [G.IsEquivalence] {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}} (i : G ⋙ F ≅ F') :
    Aut F ≃ₜ* Aut F' := by
  let hG := (G.asEquivalence.congrLeft (E := FintypeCat.{w})).fullyFaithfulInverse
  let e : Aut F ≃* Aut F' := (hG.autMulEquivOfFullyFaithful F).trans i.conjAut
  have he (σ : Aut F) (X : C) : (e σ).app X = (i.app X).symm ≪≫ σ.app (G.obj X) ≪≫ i.app X :=
    rfl
  have hcont : Continuous e := by
    rw [(autEmbedding_isClosedEmbedding F').isInducing.continuous_iff, continuous_pi_iff]
    intro X
    change Continuous fun σ ↦ autEmbedding F' (e σ) X
    have : (fun σ ↦ autEmbedding F' (e σ) X) =
        (fun τ : Aut (F.obj (G.obj X)) ↦ (i.app X).symm ≪≫ τ ≪≫ i.app X) ∘
          (fun σ ↦ autEmbedding F σ (G.obj X)) := by
      funext σ
      rw [Function.comp_apply, autEmbedding_apply, autEmbedding_apply, he]
    rw [this]
    exact continuous_of_discreteTopology.comp
      ((continuous_apply _).comp (autEmbedding_isClosedEmbedding F).continuous)
  exact { e with
    continuous_toFun := hcont
    continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

end Galois

/-! ### The functor on points for schemes -/

section SchemeLevel

open AlgebraicGeometry

variable (K : Type u) [NontriviallyNormedField K] [ProperSpace K] (X : Scheme.{u})
  [X.Over (Spec (.of K))]

/-- The category of finite étale coverings of a scheme `X` (finite étale `X`-schemes): the
category `FEt X` of V.7. -/
abbrev FiniteEtaleCovering (X : Scheme.{u}) : Type (u + 1) := ExposeV.FEt X

/-- The structure morphism of a finite étale `X`-scheme. -/
abbrev FiniteEtaleCovering.hom' {X : Scheme.{u}} (Y : FiniteEtaleCovering X) : Y.left ⟶ X :=
  Y.hom

lemma FiniteEtaleCovering.w {X : Scheme.{u}} {Y Y' : FiniteEtaleCovering X} (g : Y ⟶ Y') :
    g.left ≫ Y'.hom' = Y.hom' := by
  simpa using g.w

/-- A finite étale `X`-scheme, as a `K`-scheme. -/
abbrev overOfCovering (Y : FiniteEtaleCovering X) : Y.left.Over (Spec (.of K)) :=
  .ofHom (Y.hom' ≫ X ↘ Spec (.of K))

omit [ProperSpace K] in
lemma isOver_hom (Y : FiniteEtaleCovering X) :
    letI := overOfCovering K X Y
    Y.hom'.IsOver (Spec (.of K)) :=
  letI := overOfCovering K X Y
  ⟨rfl⟩

/-- XII.5.1, the functor `Ψ` on points: the finite covering `Y(K) → X(K)` of a finite étale
`X`-scheme `Y` (`SchemePoints.isCoveringMap_map`). -/
def coveringOfFiniteEtaleCovering (Y : FiniteEtaleCovering X) :
    TopCat.FiniteCovering (TopCat.of (SchemePoints K X)) :=
  letI := overOfCovering K X Y
  haveI := isOver_hom K X Y
  haveI : IsFinite Y.hom' := Y.prop.1
  haveI : Etale Y.hom' := Y.prop.2
  ⟨Over.mk (TopCat.ofHom ⟨SchemePoints.map Y.hom', SchemePoints.continuous_map _⟩),
    SchemePoints.isCoveringMap_map _, SchemePoints.finite_map_preimage _⟩

/-- XII.5.1: the functor `Ψ` from finite étale coverings of `X` to finite coverings of `X(K)`. -/
def schemePointsFunctor :
    FiniteEtaleCovering X ⥤ TopCat.FiniteCovering (TopCat.of (SchemePoints K X)) where
  obj := coveringOfFiniteEtaleCovering K X
  map {Y Y'} g :=
    letI := overOfCovering K X Y
    letI := overOfCovering K X Y'
    haveI : g.left.IsOver (Spec (.of K)) := ⟨by
      change g.left ≫ Y'.hom' ≫ X ↘ Spec (.of K) = Y.hom' ≫ X ↘ Spec (.of K)
      rw [← Category.assoc, FiniteEtaleCovering.w g]⟩
    ObjectProperty.homMk (Over.homMk (TopCat.ofHom
      ⟨SchemePoints.map (K := K) g.left, SchemePoints.continuous_map _⟩) (by
        ext p
        exact SchemePoints.ext (by
          change (p.1 ≫ g.left) ≫ Y'.hom' = p.1 ≫ Y.hom'
          rw [Category.assoc, FiniteEtaleCovering.w g])))

end SchemeLevel

/-! ### The Riemann existence theorem and the comparison of fundamental groups -/

section Statements

/-- XII.5.1 (statement only), "Riemann existence theorem": for a scheme `X` locally of finite
type over `ℂ`, the functor `Y ↦ Y(ℂ)` from finite étale coverings of `X` to finite coverings of
`X(ℂ)` is an equivalence of categories. (SGA uses finite étale coverings of the analytic space
`X^an`; these are the finite topological coverings of `X(ℂ)`, the analytic structure lifting
uniquely along a local homeomorphism.) The functor is fully faithful (faithful: instance in
`SGA.SGA1.ExposeXII.FundamentalGroup`; full: instance in `SGA.SGA1.ExposeXII.RiemannFull`), so
what is open is essential surjectivity. Equivalent to the affine form in universe `0`,
`RiemannExistenceStatement.{0}` (`schemeRiemannExistence_iff`,
`SGA.SGA1.ExposeXII.RiemannLocalChart`). -/
def SchemeRiemannExistenceStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (.of ℂ))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of ℂ))],
    (schemePointsFunctor ℂ X).IsEquivalence

/-- XII.5.1 (statement only), "Riemann existence theorem", affine case: for `A` of finite type
over `ℂ`, the functor `Ψ` from finite étale coverings of `X = Spec A` to finite coverings of
`X(ℂ)` is an equivalence of categories. (SGA states it with finite étale coverings of the analytic
space `X^an`; these are the same as finite topological coverings of `X(ℂ)`, the analytic
structure lifting uniquely along a local homeomorphism.) The functor is faithful (instance above)
and, for `A : Type`, full (instance in `SGA.SGA1.ExposeXII.RiemannLocalAffine`). The statement
does not depend on the universe `u` (`riemannExistence_iff_zero`,
`SGA.SGA1.ExposeXII.RiemannReductionUniverse`), and in universe `0` it is equivalent to the scheme
form `SchemeRiemannExistenceStatement` (`schemeRiemannExistence_iff`,
`SGA.SGA1.ExposeXII.RiemannLocalChart`). -/
def RiemannExistenceStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A],
    (pointsFunctor ℂ A).IsEquivalence

/-- XII.5.2 (statement), affine case: for `X = Spec A` connected, `A` of finite type over
`ℂ`, and `x ∈ X(ℂ)`, the étale fundamental group of `X` at `x` (the automorphism group of the
fibre functor at `x`, V.4) is isomorphic, as a profinite group, to the profinite completion of
the topological fundamental group `π₁(X(ℂ), x)`. SGA's isomorphism is canonical; only its
existence is stated here. Proved from XII.5.1 alone
(`fundamentalGroupComparison_of_riemannExistence`, `SGA.SGA1.ExposeXII.StatementCorollaries`);
open without it. -/
def FundamentalGroupComparisonStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A],
    ConnectedSpace (PrimeSpectrum A) → ∀ x : Points ℂ A,
      Nonempty (Aut (etaleFiber ℂ A x) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup (Points ℂ A) x)))

/-- The topological input of the proof of XII.5.2: for `X(ℂ)` connected, the
automorphism group of the fibre functor of finite coverings of `X(ℂ)` at `x` is the profinite
completion of `π₁(X(ℂ), x)`, every finite covering being a quotient of the universal covering by
a subgroup of finite index. Proved in every universe (`coveringFundamentalGroupStatement`,
`SGA.SGA1.ExposeXII.StatementCorollaries`), since `X(ℂ)` is locally path-connected and
semilocally simply connected. -/
def CoveringFundamentalGroupStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A],
    ConnectedSpace (Points ℂ A) → ∀ x : Points ℂ A,
      Nonempty (Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (Points ℂ A)) x) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup (Points ℂ A) x)))

variable {A : Type u} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- XII.5.2, first step, from XII.5.1: the étale fundamental group of `X = Spec A` at `x` is the
automorphism group of the fibre functor at `x` of finite coverings of `X(ℂ)`. -/
def etaleAutEquivOfRiemannExistence (H : RiemannExistenceStatement.{u}) (x : Points ℂ A) :
    Aut (etaleFiber ℂ A x) ≃ₜ* Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (Points ℂ A)) x) :=
  haveI := H A
  (autContinuousMulEquiv (pointsFunctor ℂ A) (pointsFunctorCompFiberIso ℂ A x)).symm

/-- XII.5.2, proof: the comparison of fundamental groups follows from the Riemann existence
theorem XII.5.1, the connectedness comparison XII.2.4 (proved as `Points.connectedComparison`;
see `fundamentalGroupComparison'`), and the topological description of the finite coverings of
`X(ℂ)`. -/
theorem fundamentalGroupComparison (H : RiemannExistenceStatement.{u})
    (Hc : Points.ConnectedComparisonStatement.{u}) (Ht : CoveringFundamentalGroupStatement.{u}) :
    FundamentalGroupComparisonStatement.{u} := by
  intro A _ _ _ hA x
  have := Hc A hA
  obtain ⟨e⟩ := Ht A this x
  exact ⟨(etaleAutEquivOfRiemannExistence H x).trans e⟩

end Statements

end SGA.SGA1.ExposeXII
