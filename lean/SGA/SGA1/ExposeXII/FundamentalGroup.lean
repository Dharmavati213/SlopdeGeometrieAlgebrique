/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExistence
import SGA.SGA1.ExposeXII.Smooth
import SGA.SGA1.ExposeXII.Connected
import SGA.Foundations.Topology.CoveringGalois
import SGA.SGA1.ExposeV.FundamentalGroup
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# SGA 1, Exposé XII, 5.2: the étale and the topological fundamental groups

For a `K`-scheme `X` (`K = ℂ`, or any proper nontrivially normed field) and `x ∈ X(K)`, the
functor `Ψ : Y ↦ Y(K)` from étale coverings of `X` (the category `FEt X` of V.7) to finite
coverings of `X(K)` is faithful when `K` is algebraically closed and `X` locally of finite type
(step 1) of the proof of XII.5.1, `SchemePoints.eq_of_forall_comp_eq`; instance below). For
`K = ℂ` it is also full (instance in `RiemannFull.lean`), so step 1) is proved. It is compatible
with the fibre functors: the fibre of `Y(K) → X(K)` over `x` is
the fibre functor of V.7 at the geometric point `x : Spec K ⟶ X`
(`schemePointsFunctorCompFiberIso`). Hence:

* if `Ψ` is an equivalence (the Riemann existence theorem XII.5.1), the étale fundamental group
  `π₁(X, x)` of V.7 is the automorphism group of the fibre functor of finite coverings of `X(K)`
  (`etaleFundamentalGroupEquivAutFiber`), which is the profinite completion of `π₁(X(K), x)` when
  `X(K)` is connected, locally path-connected and semilocally simply connected
  (`nonempty_etaleFundamentalGroup_continuousMulEquiv`);
* this applies to `X` smooth over `ℂ` (`X(ℂ)` is then locally homeomorphic to `ℂⁿ`), giving XII.5.2
  for smooth connected `X` from XII.5.1 alone (`schemeFundamentalGroupComparison_of_smooth`,
  using XII.2.4, `SchemePoints.connectedComparison`);
* for general `X`, SGA uses, without comment, only that every finite étale covering of `X^an` is
  a quotient of the universal covering by a subgroup of finite index. That holds because `X(ℂ)`
  is connected, locally path-connected and semilocally simply connected, and all three are
  proved (XII.2.4, `locallyPathConnectedStatement`, `semilocallySimplyConnectedStatement`), so
  XII.5.1 alone implies XII.5.2 (`schemeFundamentalGroupComparison_of_riemannExistence`,
  `LocalTopologySLSC.lean`). That supersedes `schemeFundamentalGroupComparison` here, which
  assumes the stronger `LocallyContractibleStatement`.

The affine versions (with the fibre functors of finite étale algebras) are
`fundamentalGroupComparison_of_smooth'`, `fundamentalGroupComparison'` and
`coveringFundamentalGroupStatement_of_stronglyLocallyContractible`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Set AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace SchemePoints

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Y' : Scheme.{u}} [Y.Over (Spec (.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K))]

/-- XII.5.1, proof of 1), scheme level: two morphisms `a b : Y ⟶ Y'` over `X`, with `Y' ⟶ X`
unramified, which agree on the `K`-points of `Y`, are equal. Their equalizer is an open
subscheme of `Y` (the diagonal of `Y'` over `X` is an open immersion) containing every closed
point, hence is all of `Y` (`Y` is a Jacobson scheme). -/
theorem eq_of_forall_comp_eq (q : Y' ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
    (a b : Y ⟶ Y') (hab : a ≫ q = b ≫ q) (h : ∀ p : SchemePoints K Y, p.1 ≫ a = p.1 ≫ b) :
    a = b := by
  let l := pullback.lift a b hab
  let d := pullback.diagonal q
  have : IsIso (pullback.snd d l) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨?_⟩⟩
    rw [← Set.range_eq_univ, IsOpenImmersion.range_pullbackSnd]
    have := jacobsonSpace (K := K) (X := Y)
    by_contra hne
    have hC : ((l ⁻¹ᵁ d.opensRange : Y.Opens) : Set Y)ᶜ.Nonempty := by
      rwa [nonempty_compl]
    obtain ⟨y, hyC, hy⟩ := nonempty_inter_closedPoints hC
      (l ⁻¹ᵁ d.opensRange).2.isClosed_compl.isLocallyClosed
    rw [← range_pt (K := K)] at hy
    obtain ⟨p, rfl⟩ := hy
    apply hyC
    have hp : p.1 ≫ l = (p.1 ≫ a) ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_fst,
          pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_snd,
          pullback.diagonal_snd, Category.comp_id, h p]
    have key (φ : Spec (.of K) ⟶ Y) (c : Spec (.of K)) (hφ : φ ≫ l = (φ ≫ a) ≫ d) :
        l (φ c) ∈ Set.range d := by
      rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
      exact mem_range_self _
    exact key p.1 _ hp
  have hl : l = inv (pullback.snd d l) ≫ pullback.fst d l ≫ d := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  calc a = l ≫ pullback.fst q q := (pullback.lift_fst _ _ _).symm
    _ = l ≫ pullback.snd q q := by
      rw [hl, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    _ = b := pullback.lift_snd _ _ _

end SchemePoints

section SchemeFaithful

variable (K : Type u) [NontriviallyNormedField K] [ProperSpace K] [IsAlgClosed K]
  (X : Scheme.{u}) [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- XII.5.1, proof of 1): the functor `Ψ : Y ↦ Y(K)` from finite étale `X`-schemes to finite
coverings of `X(K)` is faithful, for `X` locally of finite type over the algebraically closed
field `K`. -/
instance : (schemePointsFunctor K X).Faithful where
  map_injective {Y Y'} g g' h := by
    let := overOfCovering K X Y
    have : IsFinite Y.hom' := Y.prop.1
    have : Etale Y'.hom' := Y'.prop.2
    have : LocallyOfFiniteType (Y.left ↘ Spec (.of K)) := by
      change LocallyOfFiniteType (Y.hom' ≫ X ↘ Spec (.of K))
      infer_instance
    ext
    refine SchemePoints.eq_of_forall_comp_eq (K := K) Y'.hom' g.left g'.left
      (by rw [FiniteEtaleCovering.w, FiniteEtaleCovering.w]) fun p ↦ ?_
    exact congrArg Subtype.val congr($(congr(($h).hom.left)) p)

end SchemeFaithful

section SchemeFiber

variable (K : Type u) [NontriviallyNormedField K] [ProperSpace K] {X : Scheme.{u}}
  [X.Over (Spec (.of K))]

omit [ProperSpace K] in
lemma comp_over_eq_id (x : SchemePoints K X) {Y : Scheme.{u}} (f : Y ⟶ X)
    {p : Spec (.of K) ⟶ Y} (h : p ≫ f = x.1) : p ≫ (f ≫ X ↘ Spec (.of K)) = 𝟙 _ := by
  rw [← Category.assoc, h]
  exact x.2

/-- For a finite étale `X`-scheme `Y` and `x ∈ X(K)`, the fibre of `Y(K) → X(K)` over `x` is the
set of geometric points of `Y` over `x : Spec K ⟶ X`. -/
def fiberEquivGeometricPoints (x : SchemePoints K X) (Y : FiniteEtaleCovering X) :
    FintypeCat.incl.obj ((TopCat.FiniteCovering.fiber x).obj ((schemePointsFunctor K X).obj Y)) ≃
      (ExposeV.geometricPoints x.1).obj Y where
  toFun e :=
    letI := overOfCovering K X Y
    haveI := isOver_hom K X Y
    let p : SchemePoints K Y.left := e.1
    have h : SchemePoints.map (K := K) Y.hom' p = x := e.2
    Over.homMk (p.1 : Spec (.of K) ⟶ Y.left) (congrArg (fun q : SchemePoints K X ↦ q.1) h)
  invFun a :=
    letI := overOfCovering K X Y
    let p : Spec (.of K) ⟶ Y.left := a.left
    have h : p ≫ Y.hom' = x.1 := Over.w a
    let q : SchemePoints K Y.left := ⟨p, comp_over_eq_id K x Y.hom' h⟩
    ⟨q, SchemePoints.ext h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- XII.5.2: the functor `Ψ : Y ↦ Y(K)` is compatible with the fibre functors at `x ∈ X(K)`: the
fibre of `Y(K) → X(K)` over `x` is the fibre functor of V.7 at the geometric point `x`. -/
def schemePointsFunctorCompFiberIso (x : SchemePoints K X) :
    schemePointsFunctor K X ⋙ TopCat.FiniteCovering.fiber x ≅ ExposeV.FEt.fiber K x.1 :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl
    (NatIso.ofComponents (fun Y ↦ (fiberEquivGeometricPoints K x Y).toIso) (fun {Y Y'} g ↦ by
      ext e
      apply Over.OverMorphism.ext
      rfl) ≪≫ (ExposeV.FEt.fiberInclIso K x.1).symm)

/-- XII.5.2, first step, from XII.5.1: if `Ψ` is an equivalence, the étale fundamental group
`π₁(X, x)` of V.7 is the automorphism group of the fibre functor at `x` of finite coverings of
`X(K)`. -/
def etaleFundamentalGroupEquivAutFiber [(schemePointsFunctor K X).IsEquivalence]
    (x : SchemePoints K X) :
    ExposeV.etaleFundamentalGroup K x.1 ≃ₜ*
      Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (SchemePoints K X)) x) :=
  (autContinuousMulEquiv (schemePointsFunctor K X) (schemePointsFunctorCompFiberIso K x)).symm

/-- XII.5.2: if `Ψ` is an equivalence (XII.5.1) and `X(K)` is connected, locally path-connected
and semilocally simply connected, the étale fundamental group `π₁(X, x)` is the profinite
completion of `π₁(X(K), x)`. -/
theorem nonempty_etaleFundamentalGroup_continuousMulEquiv
    [(schemePointsFunctor K X).IsEquivalence] [ConnectedSpace (SchemePoints K X)]
    [LocallyPathConnectedSpace (SchemePoints K X)]
    [SemilocallySimplyConnectedSpace (SchemePoints K X)] (x : SchemePoints K X) :
    Nonempty (ExposeV.etaleFundamentalGroup K x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints K X) x))) :=
  have ⟨e⟩ := TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv
    (TopCat.of (SchemePoints K X)) x
  ⟨(etaleFundamentalGroupEquivAutFiber K x).trans e⟩

end SchemeFiber

section Complex

/-- XII.5.2, smooth case: for `X` smooth over `ℂ` with `X(ℂ)` connected, the Riemann existence
theorem XII.5.1 implies that the étale fundamental group `π₁(X, x)` is the profinite completion
of `π₁(X(ℂ), x)`. -/
theorem nonempty_etaleFundamentalGroup_continuousMulEquiv_of_smooth
    (H : SchemeRiemannExistenceStatement) (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [Smooth (X ↘ Spec (.of ℂ))] [ConnectedSpace (SchemePoints ℂ X)] (x : SchemePoints ℂ X) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x))) :=
  have := H X
  have := SchemePoints.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) X
  nonempty_etaleFundamentalGroup_continuousMulEquiv ℂ x

/-- (Statement only) a strong form of the topological input of the proof of XII.5.2: for `X`
locally of finite type over `ℂ`, `X(ℂ)` is strongly locally contractible (every point has a basis
of contractible neighbourhoods). SGA's proof of XII.5.2 uses, without comment, only that every
finite covering of `X(ℂ)` is a quotient of the universal covering, which holds because `X(ℂ)` is
connected, locally path-connected and semilocally simply connected. It never cites
triangulation; IX.5.7 mentions the triangulability of singular varieties only as an assumption
that its argument avoids. Those weaker properties are proved (`locallyPathConnectedStatement`,
`semilocallySimplyConnectedStatement`), so this statement is not needed for XII.5.2
(`schemeFundamentalGroupComparison_of_riemannExistence`). Proved cases: `X` smooth
(`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`) and `dim X ≤ 1`
(`SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one`). In general it
follows from the local conic structure of complex algebraic sets, or from their triangulability,
neither of which is formalized. -/
def LocallyContractibleStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    StronglyLocallyContractibleSpace (SchemePoints ℂ X)

/-- XII.5.2 (statement): for `X` connected and locally of finite type over `ℂ` and `x ∈ X(ℂ)`,
the étale fundamental group `π₁(X, x)` of V.7 is isomorphic, as a topological group, to the
profinite completion of the topological fundamental group `π₁(X(ℂ), x)`. -/
def SchemeFundamentalGroupComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    ConnectedSpace X → ∀ x : SchemePoints ℂ X,
      Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion
          (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x)))

/-- XII.5.2, smooth case: for `X` connected and smooth over `ℂ`, the Riemann existence theorem
XII.5.1 implies that the étale fundamental group `π₁(X, x)` is the profinite completion of
`π₁(X(ℂ), x)` (`X(ℂ)` is connected by XII.2.4, `SchemePoints.connectedComparison`). -/
theorem schemeFundamentalGroupComparison_of_smooth (H : SchemeRiemannExistenceStatement)
    (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [Smooth (X ↘ Spec (.of ℂ))] (hX : ConnectedSpace X)
    (x : SchemePoints ℂ X) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x))) :=
  have := SchemePoints.connectedComparison X hX
  nonempty_etaleFundamentalGroup_continuousMulEquiv_of_smooth H X x

/-- XII.5.2, proof: the comparison of fundamental groups follows from the Riemann existence
theorem XII.5.1 and the strong local contractibility of `X(ℂ)` (`LocallyContractibleStatement`;
with the connectedness comparison XII.2.4, `SchemePoints.connectedComparison`). Superseded by
`schemeFundamentalGroupComparison_of_riemannExistence` (`LocalTopologySLSC.lean`), which needs
only XII.5.1. -/
theorem schemeFundamentalGroupComparison (H : SchemeRiemannExistenceStatement)
    (Ht : LocallyContractibleStatement) : SchemeFundamentalGroupComparisonStatement := by
  intro X _ _ hX x
  have := SchemePoints.connectedComparison X hX
  have := H X
  have := Ht X
  exact nonempty_etaleFundamentalGroup_continuousMulEquiv ℂ x

end Complex

section Affine

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- XII.5.2, topological input, affine case: if `X(ℂ)` is connected and strongly locally
contractible, the automorphism group of the fibre functor of finite coverings of `X(ℂ)` at `x` is
the profinite completion of `π₁(X(ℂ), x)`. -/
theorem nonempty_autFiber_continuousMulEquiv_of_stronglyLocallyContractible
    [StronglyLocallyContractibleSpace (Points ℂ A)] [ConnectedSpace (Points ℂ A)]
    (x : Points ℂ A) :
    Nonempty (Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (Points ℂ A)) x) ≃ₜ*
      ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (FundamentalGroup (Points ℂ A) x))) :=
  TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv (TopCat.of (Points ℂ A)) x

/-- `CoveringFundamentalGroupStatement` holds as soon as the spaces `X(ℂ)` are strongly locally
contractible (e.g. triangulable). -/
theorem coveringFundamentalGroupStatement_of_stronglyLocallyContractible
    (h : ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A],
      StronglyLocallyContractibleSpace (Points ℂ A)) :
    CoveringFundamentalGroupStatement.{u} := fun A _ _ _ _ x ↦
  have := h A
  nonempty_autFiber_continuousMulEquiv_of_stronglyLocallyContractible x

/-- XII.5.2, affine smooth case: for `A` smooth over `ℂ` with `X(ℂ)` connected, the Riemann
existence theorem XII.5.1 implies that the automorphism group of the fibre functor of finite étale
`A`-algebras at `x` (the étale fundamental group) is the profinite completion of
`π₁(X(ℂ), x)`. -/
theorem fundamentalGroupComparison_of_smooth (H : RiemannExistenceStatement.{u})
    [Algebra.Smooth ℂ A] [ConnectedSpace (Points ℂ A)] (x : Points ℂ A) :
    Nonempty (Aut (etaleFiber ℂ A x) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (Points ℂ A) x))) :=
  have := Points.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) (A := A)
  have ⟨e⟩ := nonempty_autFiber_continuousMulEquiv_of_stronglyLocallyContractible x
  ⟨(etaleAutEquivOfRiemannExistence H x).trans e⟩

/-- XII.5.2, affine smooth case: for `A` smooth over `ℂ` with `Spec A` connected, the Riemann
existence theorem XII.5.1 implies that the étale fundamental group is the profinite completion of
`π₁(X(ℂ), x)` (`X(ℂ)` is connected by XII.2.4, `Points.connectedComparison`). -/
theorem fundamentalGroupComparison_of_smooth' (H : RiemannExistenceStatement.{u})
    [Algebra.Smooth ℂ A] [ConnectedSpace (PrimeSpectrum A)] (x : Points ℂ A) :
    Nonempty (Aut (etaleFiber ℂ A x) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (Points ℂ A) x))) :=
  have := Points.connectedSpace_of_connectedSpace_primeSpectrum (A := A)
  fundamentalGroupComparison_of_smooth H x

/-- XII.5.2, affine case, proof: the comparison of fundamental groups follows from the Riemann
existence theorem XII.5.1 and the topological description of the finite coverings of `X(ℂ)`
(with XII.2.4, `Points.connectedComparison`). -/
theorem fundamentalGroupComparison' (H : RiemannExistenceStatement.{u})
    (Ht : CoveringFundamentalGroupStatement.{u}) : FundamentalGroupComparisonStatement.{u} :=
  fundamentalGroupComparison H Points.connectedComparison Ht

end Affine

end SGA.SGA1.ExposeXII
