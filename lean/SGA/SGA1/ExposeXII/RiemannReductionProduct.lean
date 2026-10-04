/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import SGA.SGA1.ExposeXII.RiemannExtension

/-!
# SGA 1, Exposé XII, 5.1 for finite products

`isEquivalence_pointsFunctor_pi`: if the Riemann existence theorem XII.5.1 holds for finitely many
`ℂ`-algebras `B i` of finite type, it holds for their product `R = ∏ B i` (`Spec R` is the disjoint
union of the `Spec B i`). A finite covering `E` of `R(ℂ) = ⊔ B i(ℂ)` restricts to finite coverings
`E_i` of the `B i(ℂ)`, which are `C i(ℂ)` for finite étale `B i`-algebras `C i`; then `∏ C i` is a
finite étale `R`-algebra whose points are `⊔ C i(ℂ) ≅ E`.

The ingredients:

* `Points.exists_apply_single_ne_zero`, `Points.apply_single_eq_zero_or`: a `ℂ`-point of a finite
  product factors through exactly one factor (`R → B i` is the localization away from the
  idempotent `Pi.single i 1`, `Points.isLocalizationAway_pi`);
* `exists_bijective_of_isOpenEmbedding` (general topology): open embeddings `Γ i : W i → E` and
  `r i : W i → Y` whose ranges partition `E` and `Y` glue to a continuous bijection `E → Y`.

This is used for the normalization of a reducible curve, a finite product of normal curves.
-/

noncomputable section

open CategoryTheory Topology Set Filter Module CommAlgCat Opposite

namespace SGA.SGA1.ExposeXII

namespace RiemannProduct

section Topology

variable {ι : Type*} {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {W : ι → Type*}
  [∀ i, TopologicalSpace (W i)]

/-- **Gluing along partitions into open pieces**: open embeddings `Γ i : W i → E` and
`r i : W i → Y` whose ranges are pairwise disjoint and cover `E`, resp. `Y`, define a continuous
bijection `Φ : E → Y` with `Φ ∘ Γ i = r i`. -/
theorem exists_bijective_of_isOpenEmbedding {Γ : ∀ i, W i → E} {r : ∀ i, W i → Y}
    (hΓ : ∀ i, IsOpenEmbedding (Γ i)) (hr : ∀ i, IsOpenEmbedding (r i))
    (hΓd : Pairwise fun i j ↦ Disjoint (range (Γ i)) (range (Γ j)))
    (hrd : Pairwise fun i j ↦ Disjoint (range (r i)) (range (r j)))
    (hΓc : ∀ e, ∃ i, e ∈ range (Γ i)) (hrc : ∀ y, ∃ i, y ∈ range (r i)) :
    ∃ Φ : E → Y, Continuous Φ ∧ Function.Bijective Φ ∧ ∀ i w, Φ (Γ i w) = r i w := by
  classical
  choose idx hidx using hΓc
  let Φ : E → Y := fun e ↦ r (idx e) (hidx e).choose
  have hidx_eq (i : ι) (w : W i) : idx (Γ i w) = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hΓd hne) (hidx (Γ i w)) (mem_range_self w)
  have hΦ (i : ι) (w : W i) : Φ (Γ i w) = r i w := by
    have key : ∀ (j : ι) (hj : j = i) (w' : W j), Γ j w' = Γ i w → r j w' = r i w := by
      rintro j rfl w' h
      rw [(hΓ j).injective h]
    exact key _ (hidx_eq i w) _ (hidx (Γ i w)).choose_spec
  refine ⟨Φ, continuous_iff_continuousAt.mpr fun e ↦ ?_, ⟨fun e₁ e₂ h ↦ ?_, fun y ↦ ?_⟩, hΦ⟩
  · obtain ⟨i, w, rfl⟩ : ∃ i w, Γ i w = e := by
      obtain ⟨i, w, hw⟩ := (⟨idx e, hidx e⟩ : ∃ i, e ∈ range (Γ i))
      exact ⟨i, w, hw⟩
    rw [← (hΓ i).continuousAt_iff]
    have : Φ ∘ Γ i = r i := funext (hΦ i)
    rw [this]
    exact (hr i).continuous.continuousAt
  · obtain ⟨i, w₁, rfl⟩ : ∃ i w, Γ i w = e₁ := by
      obtain ⟨w, hw⟩ := hidx e₁
      exact ⟨_, w, hw⟩
    obtain ⟨j, w₂, rfl⟩ : ∃ j w, Γ j w = e₂ := by
      obtain ⟨w, hw⟩ := hidx e₂
      exact ⟨_, w, hw⟩
    rw [hΦ, hΦ] at h
    obtain rfl : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hrd hne) (mem_range_self w₁) (h ▸ mem_range_self w₂)
    rw [(hr i).injective h]
  · obtain ⟨i, w, rfl⟩ := hrc y
    exact ⟨Γ i w, hΦ i w⟩

end Topology

end RiemannProduct

namespace Points

variable {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra ℂ (B i)]

omit [∀ i, Algebra ℂ (B i)] in
/-- `B i` is the localization of `∏ B j` away from the idempotent `Pi.single i 1`. -/
lemma isLocalizationAway_pi [DecidableEq ι] (i : ι) :
    letI := (Pi.evalRingHom B i).toAlgebra
    IsLocalization.Away (Pi.single i 1 : ∀ j, B j) (B i) := by
  let := (Pi.evalRingHom B i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
    ((Pi.evalRingHom B i).surjective)
  simp [IsIdempotentElem, ← Pi.single_mul_left]

/-- A `ℂ`-point of a finite product does not vanish on some idempotent `Pi.single i 1`. -/
lemma exists_apply_single_ne_zero [Finite ι] [DecidableEq ι] (φ : Points ℂ (∀ i, B i)) :
    ∃ i, φ (Pi.single i 1) ≠ 0 := by
  have := Fintype.ofFinite ι
  by_contra! H
  have h1 : ∑ i, (Pi.single i 1 : ∀ j, B j) = 1 := by
    ext j
    simp [Finset.sum_apply]
  have : φ (∑ i, (Pi.single i 1 : ∀ j, B j)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ H i
  rw [h1, map_one] at this
  exact one_ne_zero this

/-- A `ℂ`-point of a product vanishes on one of two distinct idempotents `Pi.single i 1`. -/
lemma apply_single_eq_zero_or [DecidableEq ι] {i j : ι} (hij : i ≠ j) (φ : Points ℂ (∀ i, B i)) :
    φ (Pi.single i 1) = 0 ∨ φ (Pi.single j 1) = 0 := by
  rw [← mul_eq_zero, ← map_mul]
  have : (Pi.single i 1 : ∀ k, B k) * Pi.single j 1 = 0 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hij]
    · simp [hk]
  rw [this, map_zero]

end Points

open RiemannHigher in
/-- **XII.5.1 for finite products**: if `Ψ` is an equivalence for finitely many `ℂ`-algebras
`B i` of finite type, it is an equivalence for `∏ B i`. -/
theorem isEquivalence_pointsFunctor_pi {ι : Type} [Finite ι] (B : ι → Type) [∀ i, CommRing (B i)]
    [∀ i, Algebra ℂ (B i)] [∀ i, Algebra.FiniteType ℂ (B i)]
    (h : ∀ i, (pointsFunctor ℂ (B i)).IsEquivalence) :
    (pointsFunctor ℂ (∀ i, B i)).IsEquivalence := by
  classical
  have (i : ι) : Algebra.FinitePresentation ℂ (B i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FiniteType ℂ (∀ i, B i) := inferInstance
  refine { essSurj := ⟨fun E ↦ ?_⟩ }
  let (i : ι) : Algebra (∀ i, B i) (B i) := (Pi.evalRingHom B i).toAlgebra
  have (i : ι) : IsScalarTower ℂ (∀ i, B i) (B i) := .of_algebraMap_eq fun _ ↦ rfl
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : (∀ i, B i)) (B i) :=
    Points.isLocalizationAway_pi B i
  let ι' (i : ι) : TopCat.of (Points ℂ (B i)) ⟶ TopCat.of (Points ℂ (∀ i, B i)) :=
    pointsHom (IsScalarTower.toAlgHom ℂ (∀ i, B i) (B i))
  have hι (i : ι) : IsOpenEmbedding (ι' i) :=
    Points.isOpenEmbedding_map_of_isLocalizationAway (Pi.single i 1 : (∀ i, B i))
  have hιrange (i : ι) : range (ι' i) = {φ : Points ℂ (∀ i, B i) | φ (Pi.single i 1) ≠ 0} :=
    Points.range_map_of_isLocalizationAway (Pi.single i 1 : (∀ i, B i))
  have hT (i : ι) := Functor.EssSurj.mem_essImage (F := pointsFunctor ℂ (B i))
    ((TopCat.FiniteCovering.baseChange (ι' i)).obj E)
  choose T hT using hT
  -- the finite étale `B i`-algebras `C i` and their product `(∀ i, C i)`
  let C (i : ι) : Type := (T i).unop.obj
  let (i : ι) : Algebra ℂ (C i) := algebraOfFiniteEtale ℂ (B i) (T i).unop
  have (i : ι) : IsScalarTower ℂ (B i) (C i) := isScalarTower_of_finiteEtale ℂ (B i) (T i).unop
  let (i : ι) : Algebra (∀ i, B i) (C i) :=
    ((algebraMap (B i) (C i)).comp (Pi.evalRingHom B i)).toAlgebra
  have (i : ι) : IsScalarTower (∀ i, B i) (B i) (C i) := .of_algebraMap_eq fun _ ↦ rfl
  have (i : ι) : IsScalarTower ℂ (∀ i, B i) (C i) := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ (B i) (C i)]
    rfl
  have (i : ι) : Algebra.Etale (∀ i, B i) (C i) := by
    have : Algebra.Etale (∀ i, B i) (B i) :=
      Algebra.Etale.of_isLocalizationAway (Pi.single i 1 : (∀ i, B i))
    exact Algebra.Etale.comp (∀ i, B i) (B i) (C i)
  have (i : ι) : Module.Finite (∀ i, B i) (C i) := by
    have : Module.Finite (∀ i, B i) (B i) :=
      Module.Finite.of_surjective (Algebra.linearMap (∀ i, B i) (B i))
        (Pi.evalRingHom B i).surjective
    exact Module.Finite.trans (B i) (C i)
  -- the `∏ B i`-algebra structure on `∏ C i` through the factors (not the componentwise
  -- instance `Pi.instAlgebraForall`, which mathlib's étaleness of products does not see)
  let : Algebra (∀ i, B i) (∀ i, C i) := Pi.algebra ι C
  have : Algebra.Etale (∀ i, B i) (∀ i, C i) := inferInstance
  let (i : ι) : Algebra (∀ i, C i) (C i) := (Pi.evalRingHom C i).toAlgebra
  have (i : ι) : IsScalarTower ℂ (∀ i, C i) (C i) := .of_algebraMap_eq fun _ ↦ rfl
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : (∀ i, C i)) (C i) :=
    Points.isLocalizationAway_pi C i
  let r (i : ι) : Points ℂ (C i) → Points ℂ (∀ i, C i) :=
    Points.map (IsScalarTower.toAlgHom ℂ (∀ i, C i) (C i))
  have hr (i : ι) : IsOpenEmbedding (r i) :=
    Points.isOpenEmbedding_map_of_isLocalizationAway (Pi.single i 1 : (∀ i, C i))
  have hrrange (i : ι) : range (r i) = {ψ : Points ℂ (∀ i, C i) | ψ (Pi.single i 1) ≠ 0} :=
    Points.range_map_of_isLocalizationAway (Pi.single i 1 : (∀ i, C i))
  -- `Γ i : C i(ℂ) → E`, onto the part of `E` over `B i(ℂ)`
  let j (i : ι) := TopCat.homeoOfIso ((Over.forget _).mapIso ((ObjectProperty.ι _).mapIso
    (hT i).some))
  let Γ (i : ι) : Points ℂ (C i) → E.obj.left := fun w ↦
    TopCat.FiniteCovering.baseChangeSnd (ι' i) E (j i w)
  have hΓ (i : ι) : IsOpenEmbedding (Γ i) :=
    (TopCat.FiniteCovering.isOpenEmbedding_baseChangeSnd (hι i) E).1.comp (j i).isOpenEmbedding
  have hΓrange (i : ι) : range (Γ i) = E.obj.hom ⁻¹' {φ | φ (Pi.single i 1) ≠ 0} := by
    rw [← hιrange, ← (TopCat.FiniteCovering.isOpenEmbedding_baseChangeSnd (hι i) E).2]
    exact (j i).surjective.range_comp (TopCat.FiniteCovering.baseChangeSnd (ι' i) E)
  have hΓr (i : ι) (w : Points ℂ (C i)) :
      E.obj.hom (Γ i w) = Points.proj (∀ i, B i) (∀ i, C i) (r i w) := by
    refine (TopCat.FiniteCovering.hom_baseChangeSnd (ι' i) E (j i w)).trans ?_
    refine (congrArg (ι' i) (TopCat.FiniteCovering.hom_left_apply (hT i).some.hom w)).trans ?_
    ext b
    rfl
  obtain ⟨Φ, hΦc, hΦb, hΦΓ⟩ := RiemannProduct.exists_bijective_of_isOpenEmbedding hΓ hr
    (fun i j hij ↦ by
      change Disjoint (range (Γ i)) (range (Γ j))
      rw [hΓrange, hΓrange, Set.disjoint_left]
      rintro e h₁ h₂
      exact (Points.apply_single_eq_zero_or B hij (E.obj.hom e)).elim h₁ h₂)
    (fun i j hij ↦ by
      change Disjoint (range (r i)) (range (r j))
      rw [hrrange, hrrange, Set.disjoint_left]
      rintro ψ h₁ h₂
      exact (Points.apply_single_eq_zero_or C hij ψ).elim h₁ h₂)
    (fun e ↦ by
      obtain ⟨i, hi⟩ := Points.exists_apply_single_ne_zero B (E.obj.hom e)
      exact ⟨i, by rw [hΓrange]; exact hi⟩)
    (fun ψ ↦ by
      obtain ⟨i, hi⟩ := Points.exists_apply_single_ne_zero C ψ
      exact ⟨i, by rw [hrrange]; exact hi⟩)
  refine RiemannExtension.mem_essImage_pointsFunctor_of_bijective E hΦc (fun e ↦ ?_) hΦb
  obtain ⟨i, hi⟩ := Points.exists_apply_single_ne_zero B (E.obj.hom e)
  obtain ⟨w, rfl⟩ : e ∈ range (Γ i) := by rw [hΓrange]; exact hi
  rw [hΦΓ, ← hΓr]

end SGA.SGA1.ExposeXII
