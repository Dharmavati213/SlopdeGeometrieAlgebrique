/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherGeneric
import SGA.SGA1.ExposeXII.RiemannReductionFiniteEtale
import SGA.SGA1.ExposeXII.RiemannLocalAffine

/-!
# Generic algebraicity passes to finite étale coverings

Let `B` be a finite étale `A`-algebra (`A` of finite type over `ℂ`) and `E` a finite covering of
`Y(ℂ)`, `Y = Spec B`. If `E`, seen as a covering of `X(ℂ)` through `Y(ℂ) → X(ℂ)`
(`FiniteEtaleTransfer.compCovering`), is algebraic over `D(g) ⊆ X`, then `E` is algebraic over
`D(g) ⊆ Y` (`RiemannHigher.IsGenericallyAlgebraic.of_compCovering`): over `D(g)`, the map
`E → Y(ℂ)` is a map of algebraic coverings of `D(g)(ℂ)`, hence algebraic by the full faithfulness
of `Ψ` (XII.5.1, step 1)). This is the generic form of `isEquivalence_pointsFunctor_of_finiteEtale`.
-/

noncomputable section

open CategoryTheory Topology Opposite CommAlgCat TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

namespace FiniteEtaleTransfer

variable {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (B : FiniteEtale.{0} A)

/-- XII.5.1 passes to finite étale coverings, for one covering: if the covering `E` of
`Y(ℂ)`, seen as a covering of `X(ℂ)`, is `T(ℂ)` for a finite étale `A`-algebra `T`, then `E` is
`T(ℂ)` for `T` as a finite étale `B`-algebra. -/
theorem mem_essImage_of_compCovering
    (E : letI := algebraOfFiniteEtale ℂ A B; TopCat.FiniteCovering (TopCat.of (Points ℂ B)))
    (h : (pointsFunctor ℂ A).essImage (compCovering B E)) :
    letI := algebraOfFiniteEtale ℂ A B
    (pointsFunctor ℂ B).essImage E := by
  obtain ⟨T, ⟨i⟩⟩ := h
  exact ⟨_, ⟨isoOfMap B E T i _ ((pointsFunctor ℂ A).map_preimage _)⟩⟩

end FiniteEtaleTransfer

namespace RiemannHigher

open FiniteEtaleTransfer

variable {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (B : FiniteEtale.{0} A)

section Away

variable (g : A)

/-- A copy of the localization `B_g`, on which the `ℂ`-algebra structure through `A_g` will be put
(the one through `B` of `Localization.Away` is not definitionally the same). -/
def AwayCopy : Type := Localization.Away (algebraMap A B g)

instance : CommRing (AwayCopy B g) :=
  inferInstanceAs (CommRing (Localization.Away (algebraMap A B g)))

instance : Algebra B (AwayCopy B g) :=
  inferInstanceAs (Algebra B (Localization.Away (algebraMap A B g)))

instance : IsLocalization.Away (algebraMap A B g) (AwayCopy B g) :=
  inferInstanceAs (IsLocalization.Away (algebraMap A B g) (Localization.Away (algebraMap A B g)))

instance : Algebra A (AwayCopy B g) := ((algebraMap B _).comp (algebraMap A B)).toAlgebra

instance : IsScalarTower A B (AwayCopy B g) := .of_algebraMap_eq fun _ ↦ rfl

/-- `B_g` is an `A_g`-algebra. -/
instance awayAlgebra : Algebra (Localization.Away g) (AwayCopy B g) :=
  (IsLocalization.Away.lift g (S := Localization.Away g) (g := algebraMap A (AwayCopy B g))
    (by
      rw [IsScalarTower.algebraMap_apply A B (AwayCopy B g)]
      exact IsLocalization.Away.algebraMap_isUnit _)).toAlgebra

instance : IsScalarTower A (Localization.Away g) (AwayCopy B g) :=
  .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq g _ a).symm

instance : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)) (AwayCopy B g) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  infer_instance

instance : Module.Finite (Localization.Away g) (AwayCopy B g) :=
  .of_isLocalization A B (Submonoid.powers g)

instance : Algebra.Etale (Localization.Away g) (AwayCopy B g) :=
  have : Algebra.Etale B (AwayCopy B g) := .of_isLocalizationAway (algebraMap A B g)
  have : Algebra.Etale A (AwayCopy B g) := .comp A B _
  .of_restrictScalars A (Localization.Away g) _

/-- `B_g` as a finite étale `A_g`-algebra. -/
abbrev awayFiniteEtale : FiniteEtale.{0} (Localization.Away g) :=
  FiniteEtale.of (Localization.Away g) (AwayCopy B g)

end Away

/-- **Generic algebraicity passes to finite étale coverings.** Let `B` be a finite étale
`A`-algebra and `E` a finite covering of `Y(ℂ)`, `Y = Spec B`. If `E`, as a covering of `X(ℂ)`
(`compCovering`), is algebraic over `D(g)`, `g ∈ A` a nonzerodivisor, then `E` is algebraic over
`D(g) ⊆ Y`. -/
theorem IsGenericallyAlgebraic.of_compCovering
    (E : letI := algebraOfFiniteEtale ℂ A B; TopCat.FiniteCovering (TopCat.of (Points ℂ B)))
    (h : IsGenericallyAlgebraic (compCovering B E)) :
    letI := algebraOfFiniteEtale ℂ A B
    IsGenericallyAlgebraic E := by
  let := algebraOfFiniteEtale ℂ A B
  have := isScalarTower_of_finiteEtale ℂ A B
  obtain ⟨g, hg, hE⟩ := h
  have hgB : algebraMap A B g ∈ nonZeroDivisors B := by
    rw [← isRegular_iff_mem_nonZeroDivisors] at hg ⊢
    have hreg : IsSMulRegular B (algebraMap A B g) := IsSMulRegular.of_flat hg.left
    exact ⟨hreg, fun a b hab ↦ hreg (by simpa [mul_comm] using hab)⟩
  refine ⟨algebraMap A B g, hgB, ?_⟩
  let A' := Localization.Away g
  let B'' := awayFiniteEtale B g
  let := algebraOfFiniteEtale ℂ A' B''
  have := isScalarTower_of_finiteEtale ℂ A' B''
  have hc (c : ℂ) : algebraMap ℂ (AwayCopy B g) c =
      algebraMap B (AwayCopy B g) (algebraMap ℂ B c) := by
    change algebraMap A' (AwayCopy B g) (algebraMap ℂ A' c) = _
    rw [IsScalarTower.algebraMap_apply ℂ A A', ← IsScalarTower.algebraMap_apply A A' (AwayCopy B g),
      IsScalarTower.algebraMap_apply A B (AwayCopy B g)]
    rfl
  let e : Localization.Away (algebraMap A B g) ≃ₐ[ℂ] AwayCopy B g :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun c ↦ (hc c).symm
  refine mem_essImage_of_baseChange_bijective e ?_
  refine mem_essImage_of_compCovering B'' _ ?_
  set E₁ := restrictAway (algebraMap A B g) E
  set E₂ := (baseChange (pointsHom e.toAlgHom)).obj E₁
  -- the point of `B` under a point of `E₂`
  have key (q : E₂.obj.left) (b : B) :
      (E₂.obj.hom q) (algebraMap B (AwayCopy B g) b) =
        (E.obj.hom (baseChangeSnd _ E (baseChangeSnd _ E₁ q))) b := by
    have h₂ := hom_baseChangeSnd _ E₁ q
    have h₁ := hom_baseChangeSnd _ E (baseChangeSnd _ E₁ q)
    have := h₁.trans (congrArg (pointsHom (IsScalarTower.toAlgHom ℂ B
      (Localization.Away (algebraMap A B g)))) h₂)
    exact (congr($this b)).symm
  let f : E₂.obj.left → (restrictAway g (compCovering B E)).obj.left := fun q ↦
    baseChangeMk _ _ (Points.proj A' (AwayCopy B g) (E₂.obj.hom q))
      (baseChangeSnd _ E (baseChangeSnd _ E₁ q)) (by
        ext a
        change (E₂.obj.hom q) (algebraMap A' (AwayCopy B g) (algebraMap A A' a)) =
          (E.obj.hom (baseChangeSnd _ E (baseChangeSnd _ E₁ q))) (algebraMap A B a)
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B (AwayCopy B g),
          key])
  have : IsScalarTower ℂ B (AwayCopy B g) := .of_algebraMap_eq hc
  have hfc : Continuous f := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact (Points.continuous_map _).comp (E₂.obj.hom.hom.continuous)
    · exact ((baseChangeSnd _ E).hom.continuous).comp (baseChangeSnd _ E₁).hom.continuous
  have hinj : Function.Injective f := by
    intro q q' hqq'
    have he : baseChangeSnd _ E (baseChangeSnd _ E₁ q) =
        baseChangeSnd _ E (baseChangeSnd _ E₁ q') :=
      congrArg (baseChangeSnd _ (compCovering B E)) hqq'
    have hχ : E₂.obj.hom q = E₂.obj.hom q' :=
      Points.map_injective_of_isLocalizationAway (K := ℂ) (A := B) (B := AwayCopy B g)
        (algebraMap A B g) (Points.ext fun b ↦
          (key q b).trans ((congrArg (fun x ↦ (E.obj.hom x) b) he).trans (key q' b).symm))
    have h₁ : baseChangeSnd _ E₁ q = baseChangeSnd _ E₁ q' :=
      baseChange_ext ((hom_baseChangeSnd _ E₁ q).trans ((congrArg (pointsHom e.toAlgHom) hχ).trans
        (hom_baseChangeSnd _ E₁ q').symm)) he
    exact baseChange_ext hχ h₁
  have hsurj : Function.Surjective f := by
    intro p
    let φ' := (restrictAway g (compCovering B E)).obj.hom p
    let ε := baseChangeSnd _ (compCovering B E) p
    have hp := hom_baseChangeSnd _ (compCovering B E) p
    have hpa (a : A) : φ' (algebraMap A A' a) = (E.obj.hom ε) (algebraMap A B a) :=
      congr($hp a).symm
    have hne : (E.obj.hom ε) (algebraMap A B g) ≠ 0 := by
      rw [← hpa]
      exact ((IsLocalization.Away.algebraMap_isUnit g).map φ').ne_zero
    obtain ⟨χ', hχ'⟩ : E.obj.hom ε ∈ Set.range (Points.map (K := ℂ)
        (IsScalarTower.toAlgHom ℂ B (Localization.Away (algebraMap A B g)))) := by
      rw [Points.range_map_of_isLocalizationAway (algebraMap A B g)]
      exact hne
    let q₁ : E₁.obj.left := baseChangeMk _ E χ' ε hχ'
    let χ'' : Points ℂ (AwayCopy B g) := pointsHom e.symm.toAlgHom χ'
    have hχ'' : pointsHom e.toAlgHom χ'' = E₁.obj.hom q₁ := by
      ext x
      change χ' (e.symm (e x)) = χ' x
      rw [AlgEquiv.symm_apply_apply]
    refine ⟨baseChangeMk _ E₁ χ'' q₁ hχ'', baseChange_ext ?_ rfl⟩
    change Points.proj A' (AwayCopy B g) χ'' = φ'
    refine Points.map_injective_of_isLocalizationAway (K := ℂ) (A := A) (B := A') g
      (Points.ext fun a ↦ ?_)
    change χ'' (algebraMap A' (AwayCopy B g) (algebraMap A A' a)) = φ' (algebraMap A A' a)
    rw [hpa, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B (AwayCopy B g)]
    change χ' (algebraMap B _ (algebraMap A B a)) = _
    exact congr($hχ' (algebraMap A B a))
  exact Functor.essImage.ofIso (TopCat.FiniteCovering.isoOfBijective
    (E₁ := compCovering B'' E₂) ⟨f, hfc⟩ (fun _ ↦ rfl) ⟨hinj, hsurj⟩).symm hE

end RiemannHigher

end SGA.SGA1.ExposeXII
