/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExistence
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé XII, 5.1: coverings cut out by a separable polynomial

Let `R` be a `ℂ`-algebra and `P ∈ R[T]` monic and separable (`P` and `P'` generate the unit ideal),
so that `R[T]/(P)` is finite étale over `R` (I.7.4, `ExposeI.etale_adjoinRoot_of_separable`). Its
`ℂ`-points are the pairs `(ψ, w)` of a point `ψ` of `R` and a root `w` of `P(ψ)`. A finite covering
`E` of `R(ℂ)` with a continuous `F : E → ℂ` whose fibrewise characteristic polynomial is `P`
(`SeparableCovering.IsFiberCharpoly`: over every `ψ`, `P(ψ) = ∏_{e ↦ ψ} (T - F(e))`) is therefore
`R[T]/(P)(ℂ)`, through `e ↦ (p(e), F(e))` (`SeparableCovering.mem_essImage_pointsFunctor`).

This is the local step of this project's proof of XII.5.1 for curves (not SGA's route; see
`SGA.SGA1.ExposeXII.RiemannCurves`): over the open set where a holomorphic function `F` on a
covering of `ℂ ∖ S` separates the fibres, the covering is cut out by the fibrewise characteristic
polynomial of `F`.

Also `TopCat.FiniteCovering.isoOfBijective`: a continuous bijection between finite coverings,
compatible with the projections, is an isomorphism (it is a local homeomorphism).
-/

noncomputable section

universe u

open CategoryTheory Topology Set Polynomial

namespace TopCat.FiniteCovering

variable {X : TopCat.{u}} {E₁ E₂ : FiniteCovering X}

/-- A continuous bijection between finite coverings of `X`, compatible with the projections, is a
homeomorphism (it is a local homeomorphism, both projections being covering maps). -/
def homeomorphOfBijective (f : C(E₁.obj.left, E₂.obj.left))
    (hf : ∀ e, E₂.obj.hom (f e) = E₁.obj.hom e) (hb : Function.Bijective f) :
    E₁.obj.left ≃ₜ E₂.obj.left :=
  have hloc : IsLocalHomeomorph f := by
    refine IsLocalHomeomorph.of_comp (g := E₂.obj.hom) ?_ E₂.isCoveringMap.isLocalHomeomorph
      f.continuous
    have : E₂.obj.hom ∘ f = E₁.obj.hom := funext hf
    rw [this]
    exact E₁.isCoveringMap.isLocalHomeomorph
  (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen f.continuous hloc.isOpenMap

@[simp] lemma homeomorphOfBijective_apply (f : C(E₁.obj.left, E₂.obj.left))
    (hf : ∀ e, E₂.obj.hom (f e) = E₁.obj.hom e) (hb : Function.Bijective f) (e : E₁.obj.left) :
    homeomorphOfBijective f hf hb e = f e := rfl

/-- A continuous bijection between finite coverings of `X`, compatible with the projections, is an
isomorphism of finite coverings. -/
def isoOfBijective (f : C(E₁.obj.left, E₂.obj.left))
    (hf : ∀ e, E₂.obj.hom (f e) = E₁.obj.hom e) (hb : Function.Bijective f) : E₁ ≅ E₂ :=
  ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo (homeomorphOfBijective f hf hb)) (by
    ext e
    exact hf e))

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

namespace SeparableCovering

open CommAlgCat

variable {R : Type u} [CommRing R] [Algebra ℂ R] {P : R[X]}

/-- `R[T]/(P)`, for `P` monic and separable, as a finite étale `R`-algebra (I.7.4). -/
def finiteEtale (hP : P.Monic) (hsep : P.Separable) : FiniteEtale.{u} R :=
  haveI := hP.finite_adjoinRoot
  haveI := ExposeI.etale_adjoinRoot_of_separable hP hsep
  FiniteEtale.of R (AdjoinRoot P)

variable (E : TopCat.FiniteCovering (TopCat.of (Points ℂ R)))

/-- `P` is the fibrewise characteristic polynomial of `F : E → ℂ`: over every point `ψ` of `R`,
`P(ψ) = ∏_{e ↦ ψ} (T - F(e))`. -/
def IsFiberCharpoly (P : R[X]) (F : E.obj.left → ℂ) : Prop :=
  ∀ ψ : Points ℂ R, ∃ s : Finset E.obj.left, (∀ e, e ∈ s ↔ E.obj.hom e = ψ) ∧
    P.map ψ.toRingHom = ∏ e ∈ s, (X - C (F e))

variable {E} {F : E.obj.left → ℂ}

lemma eval₂_eq_zero (h : IsFiberCharpoly E P F) (e : E.obj.left) :
    P.eval₂ (E.obj.hom e).toRingHom (F e) = 0 := by
  obtain ⟨s, hs, hP⟩ := h (E.obj.hom e)
  rw [← eval_map, hP, eval_prod]
  exact Finset.prod_eq_zero ((hs e).mpr rfl) (by simp)

variable (hP : P.Monic) (hsep : P.Separable)

/-- The `ℂ`-algebra structure of `R[T]/(P)` through `R`. -/
abbrev instAlgebra : Algebra ℂ (finiteEtale hP hsep) := algebraOfFiniteEtale ℂ R _

attribute [local instance] instAlgebra

instance : IsScalarTower ℂ R (finiteEtale hP hsep) := isScalarTower_of_finiteEtale ℂ R _

/-- The root `T` of `P` in `R[T]/(P)`. -/
abbrev root : finiteEtale hP hsep := AdjoinRoot.root P

omit [Algebra ℂ R] in
lemma algebraMap_finiteEtale : algebraMap R (finiteEtale hP hsep) = AdjoinRoot.of P := rfl

variable {hP hsep}

/-- The point `(p(e), F(e))` of `R[T]/(P)`. -/
def pointOf (h : IsFiberCharpoly E P F) (e : E.obj.left) : Points ℂ (finiteEtale hP hsep) :=
  Points.ofRingHomOver (E.obj.hom e) (AdjoinRoot.lift (E.obj.hom e).toRingHom (F e)
    (eval₂_eq_zero h e)) (RingHom.ext fun _ ↦ AdjoinRoot.lift_of (eval₂_eq_zero h e))

lemma pointOf_root (h : IsFiberCharpoly E P F) (e : E.obj.left) :
    pointOf (hP := hP) (hsep := hsep) h e (root hP hsep) = F e :=
  AdjoinRoot.lift_root (eval₂_eq_zero h e)

lemma pointOf_mk (h : IsFiberCharpoly E P F) (e : E.obj.left) (q : R[X]) :
    pointOf (hP := hP) (hsep := hsep) h e (AdjoinRoot.mk P q) =
      q.eval₂ (E.obj.hom e).toRingHom (F e) :=
  AdjoinRoot.lift_mk (eval₂_eq_zero h e) q

lemma proj_pointOf (h : IsFiberCharpoly E P F) (e : E.obj.left) :
    Points.proj R (finiteEtale hP hsep) (pointOf h e) = E.obj.hom e :=
  Points.proj_ofRingHomOver _ _ _

lemma continuous_pointOf (h : IsFiberCharpoly E P F) (hF : Continuous F) :
    Continuous (pointOf (hP := hP) (hsep := hsep) h) := by
  refine Points.continuous_iff.mpr fun a ↦ ?_
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  simp_rw [pointOf_mk, eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (((Points.continuous_apply (q.coeff i)).comp E.obj.hom.hom.continuous)).mul (hF.pow i)

lemma pointOf_injective (h : IsFiberCharpoly E P F) :
    Function.Injective (pointOf (hP := hP) (hsep := hsep) h) := by
  intro e e' hee'
  have hb : E.obj.hom e = E.obj.hom e' := by
    rw [← proj_pointOf h e, ← proj_pointOf h e', hee']
  have hF : F e = F e' := by
    rw [← pointOf_root (hP := hP) (hsep := hsep) h e, ← pointOf_root (hP := hP) (hsep := hsep) h e',
      hee']
  obtain ⟨s, hs, hPs⟩ := h (E.obj.hom e)
  have hsep' : (∏ e ∈ s, (X - C (F e))).Separable := hPs ▸ hsep.map
  exact separable_prod_X_sub_C_iff'.mp hsep' e ((hs e).mpr rfl) e' ((hs e').mpr hb.symm) hF

lemma pointOf_surjective (h : IsFiberCharpoly E P F) :
    Function.Surjective (pointOf (hP := hP) (hsep := hsep) h) := by
  intro χ
  let ψ := Points.proj R (finiteEtale hP hsep) χ
  have hψ : ψ.toRingHom = χ.toRingHom.comp (algebraMap R (finiteEtale hP hsep)) := rfl
  have h0 : P.eval₂ (algebraMap R (finiteEtale hP hsep)) (root hP hsep) = 0 :=
    AdjoinRoot.eval₂_root P
  have hroot : (P.map ψ.toRingHom).eval (χ (root hP hsep)) = 0 := by
    rw [eval_map, hψ]
    change P.eval₂ (χ.toRingHom.comp _) (χ.toRingHom (root hP hsep)) = 0
    rw [← hom_eval₂, h0, map_zero]
  obtain ⟨s, hs, hPs⟩ := h ψ
  rw [hPs, eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨e, he, hroot⟩ := hroot
  have heψ : E.obj.hom e = ψ := (hs e).mp he
  refine ⟨e, Points.ext fun a ↦ ?_⟩
  have hring : (AdjoinRoot.lift (E.obj.hom e).toRingHom (F e) (eval₂_eq_zero h e)) =
      χ.toRingHom := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · rw [AdjoinRoot.lift_comp_of, heψ]
      rfl
    · rw [AdjoinRoot.lift_root]
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hroot
      exact hroot.symm
  exact congr($hring a)

variable (hP hsep) in
/-- The covering `E` is `R[T]/(P)(ℂ)`, through `e ↦ (p(e), F(e))`. -/
def iso (h : IsFiberCharpoly E P F) (hF : Continuous F) :
    E ≅ (pointsFunctor ℂ R).obj (Opposite.op (finiteEtale hP hsep)) :=
  TopCat.FiniteCovering.isoOfBijective
    (E₂ := (pointsFunctor ℂ R).obj (Opposite.op (finiteEtale hP hsep)))
    ⟨pointOf h, continuous_pointOf h hF⟩ (proj_pointOf h)
    ⟨pointOf_injective (hP := hP) (hsep := hsep) h, pointOf_surjective h⟩

/-- A finite covering `E` of `R(ℂ)` with a continuous `F : E → ℂ` whose fibrewise characteristic
polynomial is a monic separable `P ∈ R[T]` is in the essential image of `Ψ`: it is
`R[T]/(P)(ℂ)`. -/
theorem mem_essImage_pointsFunctor (hP : P.Monic) (hsep : P.Separable)
    (h : IsFiberCharpoly E P F) (hF : Continuous F) : (pointsFunctor ℂ R).essImage E :=
  ⟨Opposite.op (finiteEtale hP hsep), ⟨(iso hP hsep h hF).symm⟩⟩

end SeparableCovering

end SGA.SGA1.ExposeXII
