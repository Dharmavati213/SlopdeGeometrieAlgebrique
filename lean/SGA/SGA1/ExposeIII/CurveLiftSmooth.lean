/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftStage
import SGA.Foundations.Dimension.FiberDimension
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.RingHom.Smooth

/-!
# SGA 1, Exposé III, 7.4: smoothness of a flat proper lift with smooth closed fibre

Let `A` be a local ring and `f : Y ⟶ Spec A` flat, proper and of finite presentation, whose closed
fibre `Y₀ = Y ×_A A / 𝔪` is smooth of relative dimension `n` over the field `A / 𝔪`. Then `f` is
smooth of relative dimension `n` (`CurveLift.smoothOfRelativeDimension_of_isPullback`). This is the
last step of the proof of SGA 1 III.7.4 in this formalization: the algebraization `Y` of the formal
lifts is only known to be flat and proper with closed fibre `X₀` (SGA 1 III.7.2 states that the
algebraization of a smooth formal scheme is smooth, which is the same argument).

* `CurveLift.formallySmooth_fiber_of_surjective` (algebra): the fibre `κ(p) ⊗_R S` over a maximal
  ideal `p` is formally smooth if `S / p S` is, as an `R / p`-algebra.
* `CurveLift.mem_smoothLocus_of_isPullback_of_isMaximal`: `f` is smooth at the points of the
  closed fibre (Stacks 00TF, `Algebra.IsSmoothAt.of_formallySmooth_fiber`, needs flatness).
* `CurveLift.eq_top_of_forall_closedPoint`: over a local ring, an open subset of a universally
  closed `Y` containing the closed fibre is all of `Y`.
* `CurveLift.smoothOfRelativeDimension_of_forall_specializes`: a smooth morphism is smooth of
  relative dimension `n` if every point specializes to a point where the fibre has dimension `n`.

## References

* [SGA 1, II.2.1, III.7.2][SGA1]; Stacks Project, Tag 00TF; [EGA IV, 17.5.1].
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace SGA.SGA1.ExposeIII.CurveLift

section Algebra

/-- **The fibre over a maximal ideal**: let `R → S` be an algebra, `p ⊆ R` a maximal ideal, `ψ`
a surjection of `R` onto `R₀` with kernel `p`, `π` a surjection of `S` onto `S₀` with kernel `p S`,
and `φ₀ : R₀ → S₀` with `φ₀ ψ = π (R → S)`. If `φ₀` is formally smooth, the fibre `κ(p) ⊗_R S`
is formally smooth over `κ(p)`. -/
theorem formallySmooth_fiber_of_surjective {R S R₀ S₀ : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing R₀] [CommRing S₀] (p : Ideal R) [p.IsMaximal] (ψ : R →+* R₀)
    (hψ : Function.Surjective ψ) (hkψ : RingHom.ker ψ = p) (π : S →+* S₀)
    (hπ : Function.Surjective π) (hkπ : RingHom.ker π = p.map (algebraMap R S))
    (φ₀ : R₀ →+* S₀) (hφ₀ : φ₀.comp ψ = π.comp (algebraMap R S)) (h : φ₀.FormallySmooth) :
    Algebra.FormallySmooth p.ResidueField (p.Fiber S) := by
  let eK : (R ⧸ p) ≃ₐ[R] p.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
      p.bijective_algebraMap_quotient_residueField
  let e₂ : p.Fiber S ≃ₐ[R] S ⧸ p.map (algebraMap R S) :=
    (Algebra.TensorProduct.congr eK.symm AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm R (R ⧸ p) S).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p).symm.restrictScalars R))
  let e₃ : S ⧸ p.map (algebraMap R S) ≃+* S₀ :=
    (Ideal.quotEquivOfEq hkπ.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₁ : R ⧸ p ≃+* R₀ :=
    (Ideal.quotEquivOfEq hkψ.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  let E : p.Fiber S ≃+* S₀ := e₂.toRingEquiv.trans e₃
  have he₃ (s : S) : e₃ (Ideal.Quotient.mk _ s) = π s := rfl
  have he₁ (r : R) : e₁ (Ideal.Quotient.mk _ r) = ψ r := rfl
  have hE (r : R) : E (algebraMap R (p.Fiber S) r) = π (algebraMap R S r) := by
    change e₃ (e₂ (algebraMap R _ r)) = _
    rw [AlgEquiv.commutes, ← Ideal.Quotient.mk_algebraMap, he₃]
  have hE1 (r : R) : (eK.symm.toRingEquiv.trans e₁) (algebraMap R p.ResidueField r) = ψ r := by
    change e₁ (eK.symm (algebraMap R p.ResidueField r)) = _
    rw [AlgEquiv.commutes, ← Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_self,
      RingHom.id_apply, he₁]
  have key : algebraMap p.ResidueField (p.Fiber S) =
      E.symm.toRingHom.comp (φ₀.comp (eK.symm.toRingEquiv.trans e₁).toRingHom) := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := eK.surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h1 : eK (Ideal.Quotient.mk p r) = algebraMap R p.ResidueField r := rfl
    rw [h1, ← IsScalarTower.algebraMap_apply]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hE1]
    apply E.injective
    rw [RingEquiv.apply_symm_apply, hE]
    exact (RingHom.congr_fun hφ₀ r).symm
  rw [← RingHom.formallySmooth_algebraMap, key]
  exact RingHom.FormallySmooth.respectsIso.1 _ _ (RingHom.FormallySmooth.respectsIso.2 _ _ h)

end Algebra

section Scheme

variable {X X' Y Y₀ : Scheme.{u}} {B C R R₀ : CommRingCat.{u}}

/-- The ring homomorphisms `B → Γ(X', U)` and `C → Γ(X, W)` of schemes over `Spec B`, `Spec C`
are compatible with a morphism `k : X ⟶ X'` over `Spec C ⟶ Spec B`. -/
lemma appLE_ΓSpecIso_inv_comp (ψ : B ⟶ C) (f : X ⟶ Spec C) (f' : X' ⟶ Spec B) (k : X ⟶ X')
    (hw : k ≫ f' = f ≫ Spec.map ψ) {U : X'.Opens} {W : X.Opens} (hle : W ≤ k ⁻¹ᵁ U) (b : B) :
    f.appLE ⊤ W (le_top.trans_eq f.preimage_top.symm) ((Scheme.ΓSpecIso C).inv (ψ b)) =
      k.appLE U W hle (f'.appLE ⊤ U (le_top.trans_eq f'.preimage_top.symm)
        ((Scheme.ΓSpecIso B).inv b)) := by
  have h1 := congrArg (fun g ↦ g.hom b) (Scheme.ΓSpecIso_inv_naturality ψ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
  rw [h1]
  have h2 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso B).inv b))
    (Scheme.Hom.appLE_comp_appLE k f' ⊤ U W (le_top.trans_eq f'.preimage_top.symm) hle)
  have h3 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso B).inv b))
    (Scheme.Hom.comp_appLE f (Spec.map ψ) ⊤ W
      (le_top.trans_eq (f ≫ Spec.map ψ).preimage_top.symm))
  have h4 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso B).inv b))
    (CohomologyAux.appLE_eq_of_eq hw ⊤ W (hle.trans (k.preimage_mono
      (le_top.trans_eq f'.preimage_top.symm))) (le_top.trans_eq (f ≫ Spec.map ψ).preimage_top.symm))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2 h3 h4
  rw [h2, h4, h3]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness at the points of the closed fibre** (SGA 1 II.2.1 at the closed fibre; Stacks
00TF): let `f : Y ⟶ Spec R` be flat and locally of finite presentation, `ψ : R ⟶ R₀` surjective
with maximal kernel, and `Y₀ = Y ×_R R₀` smooth over `R₀`. Then `f` is smooth at every point of
`Y₀`. -/
theorem mem_smoothLocus_of_isPullback_of_isMaximal (f : Y ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (ψ : R ⟶ R₀) (hψ : Function.Surjective ψ)
    (hmax : (RingHom.ker ψ.hom).IsMaximal) {j : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Spec R₀}
    (H : IsPullback j f₀ f (Spec.map ψ)) [Smooth f₀] (y : Y₀) : j y ∈ f.smoothLocus := by
  have : IsClosedImmersion (Spec.map ψ) := IsClosedImmersion.spec_of_surjective _ hψ
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j y)) isOpen_univ
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top.trans_eq f.preimage_top.symm
  have hW : IsAffineOpen (j ⁻¹ᵁ V) := hV.preimage j
  have hyW : y ∈ j ⁻¹ᵁ V := hyV
  let := (f.appLE ⊤ V hVU).hom.toAlgebra
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) V hV hVU hyV]
  have : Algebra.FinitePresentation Γ(Spec R, ⊤) Γ(Y, V) :=
    f.finitePresentation_appLE (isAffineOpen_top _) hV hVU
  have : Module.Flat Γ(Spec R, ⊤) Γ(Y, V) :=
    HasRingHomProperty.appLE (P := @Flat) f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hVU
  -- the reduction `ψ' : Γ(Spec R, ⊤) → R₀` and its kernel `p`
  let ψ' : Γ(Spec R, ⊤) →+* R₀ := ψ.hom.comp (Scheme.ΓSpecIso R).hom.hom
  have hψ' : Function.Surjective ψ' :=
    hψ.comp (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  have hp : (RingHom.ker ψ.hom).map (Scheme.ΓSpecIso R).inv.hom = RingHom.ker ψ' := by
    rw [show (Scheme.ΓSpecIso R).inv.hom =
      ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm : R →+* Γ(Spec R, ⊤)) from rfl,
      Ideal.map_comap_of_equiv, RingEquiv.symm_symm]
    ext a
    exact Iff.rfl
  have : (RingHom.ker ψ').IsMaximal := by
    rw [← RingHom.comap_ker]
    exact Ideal.comap_isMaximal_of_surjective _
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  -- the reduction `π : Γ(Y, V) → Γ(Y₀, j⁻¹ V)`
  obtain ⟨hπ, hkπ⟩ := appLE_surjective_ker_of_isPullback_specMap ψ hψ H hV
    (rfl : j ⁻¹ᵁ V = j ⁻¹ᵁ V)
  have hkπ' : RingHom.ker (j.appLE V (j ⁻¹ᵁ V) le_rfl).hom =
      (RingHom.ker ψ').map (algebraMap Γ(Spec R, ⊤) Γ(Y, V)) := by
    rw [hkπ, ← hp, Ideal.map_map]
    rfl
  -- the closed fibre `φ₀ : R₀ → Γ(Y₀, j⁻¹ V)`
  let φ₀ : R₀ →+* Γ(Y₀, j ⁻¹ᵁ V) :=
    (f₀.appLE ⊤ (j ⁻¹ᵁ V) (le_top.trans_eq f₀.preimage_top.symm)).hom.comp
      (Scheme.ΓSpecIso R₀).inv.hom
  have hφ₀ : φ₀.FormallySmooth := by
    have h := f₀.smooth_appLE (isAffineOpen_top _) hW (le_top.trans_eq f₀.preimage_top.symm)
    exact RingHom.FormallySmooth.respectsIso.2 _
      (Scheme.ΓSpecIso R₀).commRingCatIsoToRingEquiv.symm h.formallySmooth
  have hcomp : φ₀.comp ψ' =
      (j.appLE V (j ⁻¹ᵁ V) le_rfl).hom.comp (algebraMap Γ(Spec R, ⊤) Γ(Y, V)) := by
    refine RingHom.ext fun a ↦ ?_
    have := appLE_ΓSpecIso_inv_comp ψ f₀ f j H.w (U := V) (W := j ⁻¹ᵁ V) le_rfl
      ((Scheme.ΓSpecIso R).hom a)
    simp only [Iso.hom_inv_id_apply] at this
    exact this
  -- the point `q` lies over the maximal ideal `p`
  set q := (hV.primeIdealOf ⟨j y, hyV⟩).asIdeal
  have hq : (hW.primeIdealOf ⟨y, hyW⟩).asIdeal.comap (j.appLE V (j ⁻¹ᵁ V) le_rfl).hom = q :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV (j ⁻¹ᵁ V) hW
      le_rfl hyW)
  have hle : RingHom.ker ψ' ≤ q.under Γ(Spec R, ⊤) := by
    intro a ha
    rw [Ideal.under, Ideal.mem_comap, ← hq, Ideal.mem_comap]
    have := RingHom.congr_fun hcomp a
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [← this, RingHom.mem_ker.mp ha, map_zero]
    exact zero_mem _
  have heq : RingHom.ker ψ' = q.under Γ(Spec R, ⊤) :=
    ‹(RingHom.ker ψ').IsMaximal›.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  have : q.LiesOver (RingHom.ker ψ') := ⟨heq⟩
  have : Algebra.FormallySmooth (RingHom.ker ψ').ResidueField
      ((RingHom.ker ψ').Fiber Γ(Y, V)) :=
    formallySmooth_fiber_of_surjective (RingHom.ker ψ') ψ' hψ' rfl _ hπ hkπ' φ₀ hcomp hφ₀
  exact Algebra.IsSmoothAt.of_formallySmooth_fiber (RingHom.ker ψ') q

/-- Over a local ring, every point of a universally closed scheme specializes to a point of the
closed fibre. -/
theorem exists_specializes_closedPoint [IsLocalRing R] (f : Y ⟶ Spec R) [UniversallyClosed f]
    (y : Y) : ∃ z : Y, y ⤳ z ∧ f z = IsLocalRing.closedPoint R := by
  have hc : IsClosed (f '' closure {y}) := f.isClosedMap _ isClosed_closure
  obtain ⟨z, hz, hfz⟩ := (IsLocalRing.specializes_closedPoint (f y)).mem_closed hc
    ⟨y, subset_closure rfl, rfl⟩
  exact ⟨z, specializes_iff_mem_closure.mpr hz, hfz⟩

/-- For `ψ : R ⟶ R₀` with maximal kernel, `Spec R₀ ⟶ Spec R` maps every point to the point
`ker ψ`. -/
lemma specMap_apply_eq_of_isMaximal (ψ : R ⟶ R₀) (hmax : (RingHom.ker ψ.hom).IsMaximal)
    (s s' : Spec R₀) : Spec.map ψ s = Spec.map ψ s' := by
  have key (t : Spec R₀) : (Spec.map ψ t).asIdeal = RingHom.ker ψ.hom := by
    refine (hmax.eq_of_le (Spec.map ψ t).2.ne_top fun a ha ↦ ?_).symm
    change ψ.hom a ∈ t.asIdeal
    rw [RingHom.mem_ker.mp ha]
    exact zero_mem _
  exact PrimeSpectrum.ext ((key s).trans (key s').symm)

/-- For `ψ : R ⟶ R₀` with maximal kernel and `Y₀ = Y ×_R R₀`, the points of `Y₀` are exactly the
points of `Y` in the fibre of a point of `Y₀`. -/
lemma range_eq_preimage_of_isPullback (f : Y ⟶ Spec R) (ψ : R ⟶ R₀)
    (hmax : (RingHom.ker ψ.hom).IsMaximal) {j : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Spec R₀}
    (H : IsPullback j f₀ f (Spec.map ψ)) (y : Y₀) : Set.range j = f ⁻¹' {f (j y)} := by
  have hw (y' : Y₀) : f (j y') = Spec.map ψ (f₀ y') := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  ext z
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨y', rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, hw, hw]
    exact specMap_apply_eq_of_isMaximal ψ hmax _ _
  · have hz' : f z = Spec.map ψ (f₀ y) := by rw [hz, hw]
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback z (f₀ y) hz'
    refine ⟨H.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw₁]

/-- The quotient of `R` by a surjection `ψ` with maximal kernel is a field. -/
lemma isField_of_isMaximal (ψ : R ⟶ R₀) (hψ : Function.Surjective ψ)
    (hmax : (RingHom.ker ψ.hom).IsMaximal) : IsField R₀ :=
  MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    (RingHom.quotientKerEquivOfSurjective hψ).symm.toMulEquiv

/-- **The fibre dimension along the closed fibre**: if `Y₀ = Y ×_R R₀` (`ψ : R ⟶ R₀` surjective
with maximal kernel) is smooth of relative dimension `n` over `R₀`, the fibre of `f` through a
point of `Y₀` has dimension `n` there. -/
theorem fiberDimAt_eq_of_isPullback (f : Y ⟶ Spec R) (ψ : R ⟶ R₀) (hψ : Function.Surjective ψ)
    (hmax : (RingHom.ker ψ.hom).IsMaximal) {j : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Spec R₀}
    (H : IsPullback j f₀ f (Spec.map ψ)) (n : ℕ) [SmoothOfRelativeDimension n f₀] (y : Y₀) :
    f.fiberDimAt (j y) = n := by
  have : IsClosedImmersion (Spec.map ψ) := IsClosedImmersion.spec_of_surjective _ hψ
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  have hr := range_eq_preimage_of_isPullback f ψ hmax H y
  let e : Y₀ ≃ₜ (f ⁻¹' {f (j y)}) :=
    j.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
  have he : e y = ⟨j y, rfl⟩ := rfl
  rw [Scheme.Hom.fiberDimAt_eq, ← he, e.topologicalKrullDimAt_eq]
  exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (isField_of_isMaximal ψ hψ hmax)
    f₀ n y

set_option backward.isDefEq.respectTransparency false in
/-- A smooth morphism is smooth of some relative dimension `d` on a neighbourhood of every point
`x`, where `d` is the dimension at `x` of the fibre through `x`. -/
theorem exists_smoothOfRelativeDimension_nhds {S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) ∧
      f.fiberDimAt x = d := by
  obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (‹Algebra.IsStandardSmooth Γ(S, U) Γ(X, V)›).out
  have hP : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hres : SmoothOfRelativeDimension P.dimension (f.resLE U V e) := by
    have : IsAffine V := hV
    have : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
    have : (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension))).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp
        (HasRingHomProperty.isLocal_ringHomProperty
          (@SmoothOfRelativeDimension P.dimension)).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hP)
  have hVf : SmoothOfRelativeDimension P.dimension (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact (inferInstance : SmoothOfRelativeDimension (P.dimension + 0) (f.resLE U V e ≫ U.ι))
  exact ⟨V, P.dimension, hxV, hVf,
    f.fiberDimAt_eq_of_isStandardSmoothOfRelativeDimension_appLE hU hV e P.dimension hP hxV⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth morphism is smooth of relative dimension `n` if every point specializes to a point
at which the fibre has dimension `n`. -/
theorem smoothOfRelativeDimension_of_forall_specializes {S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (n : ℕ) (h : ∀ x : X, ∃ x', x ⤳ x' ∧ f.fiberDimAt x' = n) :
    SmoothOfRelativeDimension n f := by
  choose x' hx' hdim using h
  choose V d hxV hV hd using fun x ↦ exists_smoothOfRelativeDimension_nhds f (x' x)
  refine IsZariskiLocalAtSource.of_iSup_eq_top V (eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (hx' x).mem_open (V x).2 (hxV x)⟩) fun x ↦ ?_
  have hdn : d x = n := by
    have := (hd x).symm.trans (hdim x)
    exact_mod_cast this
  rw [← hdn]
  exact hV x

/-- **A flat proper morphism to a local scheme with smooth closed fibre is smooth** (SGA 1 III.7.2,
smoothness of the algebraization; SGA 1 II.2.1 and Stacks 00TF at the closed fibre, then
properness): let `R` be a local ring, `f : Y ⟶ Spec R` flat, universally closed and locally of
finite presentation, `ψ : R ⟶ R₀` surjective with maximal kernel, and `Y₀ = Y ×_R R₀` smooth of
relative dimension `n` over `R₀`. Then `f` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_isPullback [IsLocalRing R] (f : Y ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] [UniversallyClosed f] (ψ : R ⟶ R₀)
    (hψ : Function.Surjective ψ) (hmax : (RingHom.ker ψ.hom).IsMaximal) {j : Y₀ ⟶ Y}
    {f₀ : Y₀ ⟶ Spec R₀} (H : IsPullback j f₀ f (Spec.map ψ)) (n : ℕ)
    [SmoothOfRelativeDimension n f₀] : SmoothOfRelativeDimension n f := by
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth n f₀
  -- the closed fibre is the fibre over the closed point
  have hcl : ∀ z : Y, f z = IsLocalRing.closedPoint R → z ∈ Set.range j := by
    intro z hz
    have : Nontrivial R₀ := (isField_of_isMaximal ψ hψ hmax).nontrivial
    obtain ⟨s⟩ : Nonempty (Spec R₀) := inferInstanceAs (Nonempty (PrimeSpectrum R₀))
    have hmaxR : RingHom.ker ψ.hom = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal hmax
    have hs : Spec.map ψ s = IsLocalRing.closedPoint R := by
      refine PrimeSpectrum.ext ?_
      change _ = IsLocalRing.maximalIdeal R
      rw [← hmaxR]
      refine (hmax.eq_of_le (Spec.map ψ s).2.ne_top fun a ha ↦ ?_).symm
      change ψ.hom a ∈ s.asIdeal
      rw [RingHom.mem_ker.mp ha]
      exact zero_mem _
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback z s (hz.trans hs.symm)
    refine ⟨H.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw₁]
  -- smooth: the smooth locus contains the closed fibre, hence everything
  have hsm : Smooth f := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
    intro z _
    obtain ⟨z', hzz', hz'⟩ := exists_specializes_closedPoint f z
    obtain ⟨y, rfl⟩ := hcl z' hz'
    exact hzz'.mem_open f.smoothLocus.2
      (mem_smoothLocus_of_isPullback_of_isMaximal f ψ hψ hmax H y)
  refine smoothOfRelativeDimension_of_forall_specializes f n fun z ↦ ?_
  obtain ⟨z', hzz', hz'⟩ := exists_specializes_closedPoint f z
  obtain ⟨y, rfl⟩ := hcl z' hz'
  exact ⟨j y, hzz', fiberDimAt_eq_of_isPullback f ψ hψ hmax H n y⟩

end Scheme

end SGA.SGA1.ExposeIII.CurveLift
