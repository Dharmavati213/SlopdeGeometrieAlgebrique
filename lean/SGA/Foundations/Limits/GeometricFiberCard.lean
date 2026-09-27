/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.SeparableDegree

/-!
# The geometric number of points of the fibres of a quasi-finite morphism

For `f : X ⟶ Y` and `y ∈ Y`, the *geometric number of points* `n(y)` of the fibre `f⁻¹(y)` is
`∑_{x ∈ f⁻¹(y)} [κ(x) : κ(y)]_s` (`Scheme.Hom.geometricFiberCard`). When `f` is locally
quasi-finite with finite fibres, it is the number of `Ω`-points of `X` over any geometric point
`Spec Ω ⟶ Y` at `y` (`Scheme.Hom.natCard_pointsOver`), hence invariant under base change
(`Scheme.Hom.geometricFiberCard_of_isPullback`).

EGA IV 15.5.1:
* `Scheme.Hom.isOpen_setOf_le_geometricFiberCard`: for `f` separated, universally open and
  locally quasi-finite with finite fibres, `y ↦ n(y)` is lower semicontinuous;
* `Scheme.Hom.universallyClosed_of_geometricFiberCard_eq`,
  `Scheme.Hom.isFinite_of_geometricFiberCard_eq`: if moreover `n` is constant, `f` is
  universally closed, hence finite if `f` is quasi-compact and locally of finite type
  (Zariski's main theorem, via mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite`);
* `Scheme.Hom.isLocallyConstant_geometricFiberCard`: for `f` finite étale, `n` is locally constant.

All are proved by induction on `n`, passing from `f` to the second projection
`X ×_Y X ∖ Δ ⟶ X` (`Scheme.Hom.diagonalComplSnd`), whose geometric number of points at `x` is
`n(f x) - 1` (`Scheme.Hom.geometricFiberCard_diagonalComplSnd_add_one`): the geometric points of
`X ×_Y X ∖ Δ` over a geometric point `x̄` of `X` are the geometric points of `X` over `f ∘ x̄`
other than `x̄`.
-/

universe u

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct

/-- Let `f` be an open map, `U` an open set, `w ∈ U` and `η` a generization of `f w` with only
finitely many points of `U` over it. Then `w` has a generization in `U` over `η`. -/
theorem IsOpenMap.exists_specializes_of_finite {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenMap f) {U : Set X} (hU : IsOpen U) {w : X}
    (hw : w ∈ U) {η : Y} (hη : η ⤳ f w) (hfin : (U ∩ f ⁻¹' {η}).Finite) :
    ∃ s ∈ U, f s = η ∧ s ⤳ w := by
  by_contra! h
  have hw' : w ∉ closure (U ∩ f ⁻¹' {η}) := by
    rw [← Set.biUnion_of_singleton (U ∩ f ⁻¹' {η}), hfin.closure_biUnion]
    simp only [Set.mem_iUnion, not_exists]
    intro s hs hws
    exact h s hs.1 hs.2 (specializes_iff_mem_closure.mpr hws)
  obtain ⟨o, ho, hwo, hoS⟩ : ∃ o, IsOpen o ∧ w ∈ o ∧ ¬ (o ∩ (U ∩ f ⁻¹' {η})).Nonempty := by
    simpa [mem_closure_iff] using hw'
  obtain ⟨s, ⟨hso, hsU⟩, hs⟩ := hη.mem_open (hf _ (ho.inter hU)) ⟨w, ⟨hwo, hw⟩, rfl⟩
  exact hoS ⟨s, hso, hsU, hs⟩

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section ResidueField

set_option backward.isDefEq.respectTransparency false in
/-- The residue field extensions of a locally quasi-finite morphism are finite. -/
theorem Scheme.Hom.finite_residueFieldMap [LocallyQuasiFinite f] (x : X) :
    (f.residueFieldMap x).hom.Finite := by
  have hq : (f.stalkMap x).hom.QuasiFinite := f.quasiFiniteAt x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (ResidueField (X.presheaf.stalk x)) :=
    inferInstanceAs (Algebra.QuasiFinite (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)))
  let κY := ResidueField (Y.presheaf.stalk (f x))
  let κX := ResidueField (X.presheaf.stalk x)
  have : Module.Finite κY (κY ⊗[Y.presheaf.stalk (f x)] κX) := .of_quasiFinite
  let φ : κY ⊗[Y.presheaf.stalk (f x)] κX →ₐ[κY] κX :=
    Algebra.TensorProduct.lift (Algebra.ofId κY κX) (AlgHom.id _ κX)
      fun _ _ ↦ Commute.all _ _
  have hφ : Function.Surjective φ := fun y ↦ ⟨1 ⊗ₜ y, by simp [φ]⟩
  have : Module.Finite κY κX := .of_surjective φ.toLinearMap hφ
  exact RingHom.finite_algebraMap.mpr this

/-- The residue field extensions of a locally quasi-finite morphism are finite. -/
theorem Scheme.Hom.finiteDimensional_residueField [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (Y.residueField (f x)) (X.residueField x) :=
  f.finite_residueFieldMap x

end ResidueField

section GeometricPoints

/-- The *geometric number of points* `n(y)` of the fibre `f⁻¹(y)` (EGA IV 15.5.1): the sum of
the separable degrees `[κ(x) : κ(y)]_s` over the points `x` of the fibre (zero if the fibre is
infinite). When `f` is locally quasi-finite with finite fibres, this is the number of points of
the geometric fibre, i.e. of `Ω`-points of `X` over any geometric point `Spec Ω → Y` at `y` with
`Ω` algebraically closed (`Scheme.Hom.natCard_pointsOver`). -/
noncomputable def Scheme.Hom.geometricFiberCard (y : Y) : ℕ :=
  ∑ᶠ x : f ⁻¹' {y}, letI := (f.residueFieldMap x.1).hom.toAlgebra
    Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1)

variable {Ω : Type u} [Field Ω]

/-- The `Ω`-points of `X` lying over a given `Ω`-point `t` of `Y`. -/
abbrev Scheme.Hom.PointsOver (t : Spec (.of Ω) ⟶ Y) : Type u :=
  {a : Spec (.of Ω) ⟶ X // a ≫ f = t}

lemma Scheme.specMap_comp_fromSpecResidueField_injective (x : X)
    {φ ψ : X.residueField x ⟶ .of Ω}
    (h : Spec.map φ ≫ X.fromSpecResidueField x = Spec.map ψ ≫ X.fromSpecResidueField x) :
    φ = ψ := by
  have := (Scheme.SpecToEquivOfField Ω X).symm.injective (a₁ := ⟨x, φ⟩) (a₂ := ⟨x, ψ⟩) h
  exact eq_of_heq (Sigma.mk.inj_iff.mp this).2

set_option backward.isDefEq.respectTransparency false in
/-- The `Ω`-points of `X` at `x` over `Spec Ω → Spec κ(f x) → Y` are the `κ(f x)`-embeddings of
`κ(x)` into `Ω`. -/
noncomputable def Scheme.Hom.pointsOverAtEquiv (x : X) (φ : Y.residueField (f x) ⟶ .of Ω) :
    letI := φ.hom.toAlgebra
    letI := (f.residueFieldMap x).hom.toAlgebra
    (X.residueField x →ₐ[Y.residueField (f x)] Ω) ≃
      {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField (f x)} := by
  let := φ.hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let F : (X.residueField x →ₐ[Y.residueField (f x)] Ω) →
      {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField (f x)} :=
    fun ψ ↦ ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x,
      Scheme.fromSpecResidueField_apply x _, by
      rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext t
      exact ψ.commutes t⟩
  refine Equiv.ofBijective F ⟨fun ψ₁ ψ₂ h ↦ ?_, fun a ↦ ?_⟩
  · have := Scheme.specMap_comp_fromSpecResidueField_injective x (congrArg Subtype.val h)
    ext t
    exact congr($this t)
  · obtain ⟨a, ha, haf⟩ := a
    obtain ⟨⟨x', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective a
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply] at ha haf ⊢
    subst ha
    have hψ : f.residueFieldMap x' ≫ ψ = φ := by
      apply Scheme.specMap_comp_fromSpecResidueField_injective (f x')
      rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← haf, Category.assoc]
    refine ⟨{ ψ.hom with commutes' := fun t ↦ congr($hψ t) }, ?_⟩
    rfl

lemma Scheme.specMap_comp_fromSpecResidueField_apply (y : Y) (φ : Y.residueField y ⟶ .of Ω) :
    (Spec.map φ ≫ Y.fromSpecResidueField y) (closedPoint Ω) = y :=
  Scheme.fromSpecResidueField_apply y _

/-- The `Ω`-points of `X` over `Spec Ω → Spec κ(y) → Y`, sorted by their image point. -/
noncomputable def Scheme.Hom.pointsOverEquivSigma (y : Y) (φ : Y.residueField y ⟶ .of Ω) :
    f.PointsOver (Spec.map φ ≫ Y.fromSpecResidueField y) ≃
      Σ x : f ⁻¹' {y}, {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x.1 ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField y} :=
  let g : f.PointsOver (Spec.map φ ≫ Y.fromSpecResidueField y) → f ⁻¹' {y} := fun a ↦
    ⟨a.1 (closedPoint Ω), by
      change (a.1 ≫ f) (closedPoint Ω) = y
      rw [a.2, Scheme.specMap_comp_fromSpecResidueField_apply]⟩
  (Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight fun x ↦
    { toFun := fun a ↦ ⟨a.1.1, congrArg Subtype.val a.2, a.1.2⟩
      invFun := fun a ↦ ⟨⟨a.1, a.2.2⟩, Subtype.ext a.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })

set_option backward.isDefEq.respectTransparency false in
/-- For `Ω` algebraically closed, the number of `Ω`-points at `x` over `Spec Ω → Spec κ(y) → Y`
is the separable degree `[κ(x) : κ(y)]_s`. -/
theorem Scheme.Hom.natCard_pointsOver_at_eq [IsAlgClosed Ω] [LocallyQuasiFinite f] (y : Y)
    (φ : Y.residueField y ⟶ .of Ω) (x : X) (hx : f x = y) :
    Nat.card {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField y} =
      letI := (f.residueFieldMap x).hom.toAlgebra
      Field.finSepDegree (Y.residueField (f x)) (X.residueField x) := by
  subst hx
  let := φ.hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  have := f.finiteDimensional_residueField x
  rw [← Nat.card_congr (f.pointsOverAtEquiv x φ), Field.finSepDegree_eq_of_isAlgClosed _ _ Ω]

lemma Scheme.Hom.finSepDegree_pos [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    0 < Field.finSepDegree (Y.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have := f.finiteDimensional_residueField x
  exact Nat.pos_of_ne_zero NeZero.out

lemma Scheme.Hom.finite_and_nonempty_pointsOver_at [IsAlgClosed Ω] [LocallyQuasiFinite f]
    (y : Y) (φ : Y.residueField y ⟶ .of Ω) (x : X) (hx : f x = y) :
    Finite {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField y} ∧
      Nonempty {a : Spec (.of Ω) ⟶ X //
        a (closedPoint Ω) = x ∧ a ≫ f = Spec.map φ ≫ Y.fromSpecResidueField y} := by
  have h := f.natCard_pointsOver_at_eq y φ x hx
  have h' := f.finSepDegree_pos x
  rw [← h] at h'
  exact ⟨(Nat.card_pos_iff.mp h').2, (Nat.card_pos_iff.mp h').1⟩

/-- **The geometric number of points** (EGA IV 15.5.1): if `f` is locally quasi-finite with
finite fibre over `y` and `Ω` is algebraically closed, the number of `Ω`-points of `X` over
`Spec Ω → Spec κ(y) → Y` is `n(y)`. -/
theorem Scheme.Hom.natCard_pointsOver [IsAlgClosed Ω] [LocallyQuasiFinite f] (y : Y)
    (φ : Y.residueField y ⟶ .of Ω) (hy : (f ⁻¹' {y}).Finite) :
    Nat.card (f.PointsOver (Spec.map φ ≫ Y.fromSpecResidueField y)) = f.geometricFiberCard y := by
  have : Fintype (f ⁻¹' {y}) := hy.fintype
  have (x : f ⁻¹' {y}) := (f.finite_and_nonempty_pointsOver_at y φ x.1 x.2).1
  rw [Nat.card_congr (f.pointsOverEquivSigma y φ), Nat.card_sigma, geometricFiberCard,
    finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun x _ ↦ f.natCard_pointsOver_at_eq y φ x.1 x.2

theorem Scheme.Hom.finite_pointsOver [IsAlgClosed Ω] [LocallyQuasiFinite f] (y : Y)
    (φ : Y.residueField y ⟶ .of Ω) (hy : (f ⁻¹' {y}).Finite) :
    Finite (f.PointsOver (Spec.map φ ≫ Y.fromSpecResidueField y)) := by
  have : Finite (f ⁻¹' {y}) := hy
  have (x : f ⁻¹' {y}) := (f.finite_and_nonempty_pointsOver_at y φ x.1 x.2).1
  exact .of_equiv _ (f.pointsOverEquivSigma y φ).symm

theorem Scheme.Hom.exists_pointsOver_apply_eq [IsAlgClosed Ω] [LocallyQuasiFinite f] (y : Y)
    (φ : Y.residueField y ⟶ .of Ω) (x : X) (hx : f x = y) :
    ∃ a : f.PointsOver (Spec.map φ ≫ Y.fromSpecResidueField y), a.1 (closedPoint Ω) = x := by
  obtain ⟨⟨a, ha, haf⟩⟩ := (f.finite_and_nonempty_pointsOver_at y φ x hx).2
  exact ⟨⟨a, haf⟩, ha⟩

lemma Scheme.eq_specMap_comp_fromSpecResidueField (t : Spec (.of Ω) ⟶ Y) :
    ∃ (y : Y) (φ : Y.residueField y ⟶ .of Ω), t = Spec.map φ ≫ Y.fromSpecResidueField y :=
  ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω Y t).symm⟩

/-- `n(y)` counts the `Ω`-points of `X` over any `Ω`-point of `Y` at `y`, `Ω` algebraically
closed. -/
theorem Scheme.Hom.natCard_pointsOver' [IsAlgClosed Ω] [LocallyQuasiFinite f]
    (t : Spec (.of Ω) ⟶ Y) (ht : (f ⁻¹' {t (closedPoint Ω)}).Finite) :
    Nat.card (f.PointsOver t) = f.geometricFiberCard (t (closedPoint Ω)) := by
  obtain ⟨y, φ, rfl⟩ := Scheme.eq_specMap_comp_fromSpecResidueField t
  rw [Scheme.specMap_comp_fromSpecResidueField_apply] at ht ⊢
  exact f.natCard_pointsOver y φ ht

theorem Scheme.Hom.finite_pointsOver' [IsAlgClosed Ω] [LocallyQuasiFinite f]
    (t : Spec (.of Ω) ⟶ Y) (ht : (f ⁻¹' {t (closedPoint Ω)}).Finite) :
    Finite (f.PointsOver t) := by
  obtain ⟨y, φ, rfl⟩ := Scheme.eq_specMap_comp_fromSpecResidueField t
  rw [Scheme.specMap_comp_fromSpecResidueField_apply] at ht
  exact f.finite_pointsOver y φ ht

theorem Scheme.Hom.exists_pointsOver_apply_eq' [IsAlgClosed Ω] [LocallyQuasiFinite f]
    (t : Spec (.of Ω) ⟶ Y) (x : X) (hx : f x = t (closedPoint Ω)) :
    ∃ a : f.PointsOver t, a.1 (closedPoint Ω) = x := by
  obtain ⟨y, φ, rfl⟩ := Scheme.eq_specMap_comp_fromSpecResidueField t
  rw [Scheme.specMap_comp_fromSpecResidueField_apply] at hx
  exact f.exists_pointsOver_apply_eq y φ x hx

/-- The fibre of `f` at the image of an `Ω`-point `t` is finite if the `Ω`-points over `t` are
finitely many (`Ω` algebraically closed). -/
theorem Scheme.Hom.finite_preimage_of_finite_pointsOver [IsAlgClosed Ω] [LocallyQuasiFinite f]
    (t : Spec (.of Ω) ⟶ Y) [Finite (f.PointsOver t)] :
    (f ⁻¹' {t (closedPoint Ω)}).Finite := by
  refine (Set.finite_range fun a : f.PointsOver t ↦ a.1 (closedPoint Ω)).subset fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := f.exists_pointsOver_apply_eq' t x hx
  exact ⟨a, ha⟩

lemma Scheme.Hom.geometricFiberCard_eq_zero_of_isEmpty (y : Y) (hy : f ⁻¹' {y} = ∅) :
    f.geometricFiberCard y = 0 := by
  have : IsEmpty (f ⁻¹' {y}) := Set.isEmpty_coe_sort.mpr hy
  rw [geometricFiberCard, finsum_of_isEmpty]

lemma Scheme.Hom.nonempty_preimage_of_geometricFiberCard_ne_zero (y : Y)
    (hy : f.geometricFiberCard y ≠ 0) : (f ⁻¹' {y}).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h ↦ hy (f.geometricFiberCard_eq_zero_of_isEmpty y h)

lemma Scheme.Hom.geometricFiberCard_ne_zero [LocallyQuasiFinite f] (x : X)
    (hx : (f ⁻¹' {f x}).Finite) : f.geometricFiberCard (f x) ≠ 0 := by
  have : Fintype (f ⁻¹' {f x}) := hx.fintype
  rw [geometricFiberCard, finsum_eq_sum_of_fintype]
  exact (Finset.sum_pos (fun x' _ ↦ f.finSepDegree_pos x'.1) ⟨⟨x, rfl⟩, Finset.mem_univ _⟩).ne'

/-- `n(y)` is at least the number of points of the fibre. -/
lemma Scheme.Hom.natCard_preimage_le_geometricFiberCard [LocallyQuasiFinite f] (y : Y)
    (hy : (f ⁻¹' {y}).Finite) : Nat.card (f ⁻¹' {y}) ≤ f.geometricFiberCard y := by
  have : Fintype (f ⁻¹' {y}) := hy.fintype
  rw [geometricFiberCard, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun x _ ↦ f.finSepDegree_pos x.1

/-- If `κ(y)` is separably closed, `n(y)` is the number of points of the fibre. -/
lemma Scheme.Hom.geometricFiberCard_eq_natCard [LocallyQuasiFinite f] (y : Y)
    (hy : (f ⁻¹' {y}).Finite) [IsSepClosed (Y.residueField y)] :
    f.geometricFiberCard y = Nat.card (f ⁻¹' {y}) := by
  have : Fintype (f ⁻¹' {y}) := hy.fintype
  rw [geometricFiberCard, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun ⟨x, hx⟩ _ ↦ ?_
  obtain rfl : f x = y := hx
  let := (f.residueFieldMap x).hom.toAlgebra
  have := f.finiteDimensional_residueField x
  exact IsPurelyInseparable.finSepDegree_eq_one _ _

end GeometricPoints

section BaseChange

variable {Ω : Type u} [Field Ω] {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

/-- The `Ω`-points of a base change `X' = X ×_Y Y'` over `t : Spec Ω ⟶ Y'` are the `Ω`-points of
`X` over `t ≫ g`. -/
@[simps]
noncomputable def Scheme.Hom.pointsOverEquivOfIsPullback (h : IsPullback g' f' f g)
    (t : Spec (.of Ω) ⟶ Y') :
    f'.PointsOver t ≃ f.PointsOver (t ≫ g) where
  toFun a := ⟨a.1 ≫ g', by rw [Category.assoc, h.w, ← Category.assoc, a.2]⟩
  invFun a := ⟨h.lift a.1 t a.2, h.lift_snd _ _ _⟩
  left_inv a := Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (by rw [h.lift_snd, a.2]))
  right_inv a := Subtype.ext (h.lift_fst _ _ _)

/-- The canonical geometric point `Spec κ(y)‾ ⟶ Y` at `y`. -/
noncomputable abbrev Scheme.fromSpecAlgClosure (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
      Y.fromSpecResidueField y

lemma Scheme.fromSpecAlgClosure_apply (Y : Scheme.{u}) (y : Y) :
    Y.fromSpecAlgClosure y (closedPoint (AlgebraicClosure (Y.residueField y))) = y :=
  Scheme.specMap_comp_fromSpecResidueField_apply y _

variable [LocallyQuasiFinite f]

/-- The fibres of a base change of a locally quasi-finite morphism with finite fibres are
finite. -/
theorem Scheme.Hom.finite_preimage_of_isPullback (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (h : IsPullback g' f' f g) (y' : Y') : (f' ⁻¹' {y'}).Finite := by
  have : LocallyQuasiFinite f' := MorphismProperty.of_isPullback h ‹_›
  let t := Y'.fromSpecAlgClosure y'
  have : Finite (f.PointsOver (t ≫ g)) := f.finite_pointsOver' _ (hf _)
  have : Finite (f'.PointsOver t) := .of_equiv _ (f.pointsOverEquivOfIsPullback h t).symm
  have h' := f'.finite_preimage_of_finite_pointsOver t
  rwa [Scheme.fromSpecAlgClosure_apply] at h'

/-- The geometric number of points is invariant under base change (EGA IV 15.5.1). -/
theorem Scheme.Hom.geometricFiberCard_of_isPullback (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (h : IsPullback g' f' f g) (y' : Y') :
    f'.geometricFiberCard y' = f.geometricFiberCard (g y') := by
  have : LocallyQuasiFinite f' := MorphismProperty.of_isPullback h ‹_›
  let t := Y'.fromSpecAlgClosure y'
  have h1 : Nat.card (f'.PointsOver t) = f'.geometricFiberCard y' :=
    f'.natCard_pointsOver y' _ (Scheme.Hom.finite_preimage_of_isPullback f hf h y')
  have h2 := f.natCard_pointsOver' (t ≫ g) (hf _)
  have h3 : (t ≫ g) (closedPoint (AlgebraicClosure (Y'.residueField y'))) = g y' := by
    change g (t (closedPoint _)) = g y'
    rw [Scheme.fromSpecAlgClosure_apply]
  rw [← h1, Nat.card_congr (f.pointsOverEquivOfIsPullback h t), h2, h3]

end BaseChange

section Diagonal

variable {Ω : Type u} [Field Ω] [IsSeparated f]

/-- Two `Ω`-points `a`, `b` of `X` with `a ≫ f = b ≫ f` are equal if `(a, b)` lies on the
diagonal of `X ×_Y X`. -/
lemma Scheme.Hom.eq_of_lift_mem_range_diagonal (a b : Spec (.of Ω) ⟶ X) (h : a ≫ f = b ≫ f)
    (hab : pullback.lift a b h (closedPoint Ω) ∈ Set.range (pullback.diagonal f)) : a = b := by
  obtain ⟨x₀, hx₀⟩ := hab
  let l := pullback.lift a b h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l)
    (g := pullback.diagonal f) (closedPoint Ω) x₀ hx₀.symm
  have : Surjective (pullback.fst l (pullback.diagonal f)) :=
    ⟨fun s ↦ ⟨z, by rw [hz]; exact Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.fst l (pullback.diagonal f))
  have hl : l = inv (pullback.fst l _) ≫ pullback.snd l (pullback.diagonal f) ≫
      pullback.diagonal f := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = l ≫ pullback.fst f f := (pullback.lift_fst _ _ _).symm
  have hb : b = l ≫ pullback.snd f f := (pullback.lift_snd _ _ _).symm
  rw [ha, hb, hl]
  simp

/-- The complement `X ×_Y X ∖ Δ` of the diagonal, an open subscheme of `X ×_Y X`. -/
def Scheme.Hom.diagonalCompl : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ,
    (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The second projection `X ×_Y X ∖ Δ ⟶ X`. -/
noncomputable def Scheme.Hom.diagonalComplSnd : (f.diagonalCompl : Scheme) ⟶ X :=
  f.diagonalCompl.ι ≫ pullback.snd f f

instance : IsSeparated f.diagonalComplSnd := by
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

instance [UniversallyOpen f] : UniversallyOpen f.diagonalComplSnd := by
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

instance [LocallyQuasiFinite f] : LocallyQuasiFinite f.diagonalComplSnd := by
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

instance [LocallyOfFiniteType f] : LocallyOfFiniteType f.diagonalComplSnd := by
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

lemma Scheme.Hom.diagonalComplSnd_apply (z : f.diagonalCompl) :
    f.diagonalComplSnd z = pullback.snd f f z.1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `Ω`-points of `X ×_Y X ∖ Δ` over an `Ω`-point `t` of `X` (via the second projection) are
the `Ω`-points of `X` over `t ≫ f` other than `t`. -/
noncomputable def Scheme.Hom.diagonalComplSndPointsOverEquiv (t : Spec (.of Ω) ⟶ X) :
    f.diagonalComplSnd.PointsOver t ≃ {a : f.PointsOver (t ≫ f) // a.1 ≠ t} where
  toFun b := ⟨⟨b.1 ≫ f.diagonalCompl.ι ≫ pullback.fst f f, by
      have hb : b.1 ≫ f.diagonalCompl.ι ≫ pullback.snd f f = t := b.2
      calc _ = (b.1 ≫ f.diagonalCompl.ι ≫ pullback.snd f f) ≫ f := by
            simp [pullback.condition]
        _ = t ≫ f := by rw [hb]⟩, by
    intro hb
    have hb' : b.1 ≫ f.diagonalCompl.ι ≫ pullback.snd f f = t := b.2
    have e : b.1 ≫ f.diagonalCompl.ι = t ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simpa using hb
      · simpa using hb'
    have hmem := (b.1 (closedPoint Ω)).2
    change (b.1 ≫ f.diagonalCompl.ι) (closedPoint Ω) ∈ f.diagonalCompl at hmem
    rw [e] at hmem
    exact hmem ⟨_, rfl⟩⟩
  invFun a := ⟨IsOpenImmersion.lift f.diagonalCompl.ι (pullback.lift a.1.1 t a.1.2) (by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι]
      intro hs
      rw [Subsingleton.elim s (closedPoint Ω)] at hs
      exact a.2 (f.eq_of_lift_mem_range_diagonal _ _ _ hs)), by
    rw [Scheme.Hom.diagonalComplSnd, IsOpenImmersion.lift_fac_assoc, pullback.lift_snd]⟩
  left_inv b := by
    have hb' : b.1 ≫ f.diagonalCompl.ι ≫ pullback.snd f f = t := b.2
    apply Subtype.ext
    rw [← cancel_mono f.diagonalCompl.ι, IsOpenImmersion.lift_fac]
    apply pullback.hom_ext
    · simp
    · simpa using hb'.symm
  right_inv a := by
    apply Subtype.ext; apply Subtype.ext
    simp

lemma Scheme.Hom.finite_preimage_diagonalComplSnd [LocallyQuasiFinite f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (x : X) : (f.diagonalComplSnd ⁻¹' {x}).Finite := by
  have h := Scheme.Hom.finite_preimage_of_isPullback f hf
    (IsPullback.of_hasPullback f f) x
  have e : f.diagonalComplSnd ⁻¹' {x} =
      f.diagonalCompl.ι ⁻¹' (pullback.snd f f ⁻¹' {x}) := rfl
  rw [e]
  exact h.preimage f.diagonalCompl.ι.isOpenEmbedding.injective.injOn

/-- The geometric number of points of `X ×_Y X ∖ Δ ⟶ X` at `x` is `n(f x) - 1`. -/
theorem Scheme.Hom.geometricFiberCard_diagonalComplSnd_add_one [LocallyQuasiFinite f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (x : X) :
    f.diagonalComplSnd.geometricFiberCard x + 1 = f.geometricFiberCard (f x) := by
  let t := X.fromSpecAlgClosure x
  have h1 : Nat.card (f.diagonalComplSnd.PointsOver t) = f.diagonalComplSnd.geometricFiberCard x :=
    f.diagonalComplSnd.natCard_pointsOver x _ (f.finite_preimage_diagonalComplSnd hf x)
  have h2 := f.natCard_pointsOver' (t ≫ f) (hf _)
  have h3 : (t ≫ f) (closedPoint (AlgebraicClosure (X.residueField x))) = f x := by
    change f (t (closedPoint _)) = f x
    rw [Scheme.fromSpecAlgClosure_apply]
  rw [h3] at h2
  have : Finite (f.PointsOver (t ≫ f)) := f.finite_pointsOver' _ (hf _)
  have := Fintype.ofFinite (f.PointsOver (t ≫ f))
  rw [← h1, ← h2, Nat.card_congr (f.diagonalComplSndPointsOverEquiv t)]
  classical
  let t₀ : f.PointsOver (t ≫ f) := ⟨t, rfl⟩
  have e : {a : f.PointsOver (t ≫ f) // a.1 ≠ t} ≃ {a // ¬ a = t₀} :=
    Equiv.subtypeEquivRight fun a ↦ not_congr (Subtype.ext_iff (a1 := a) (a2 := t₀)).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 0 < Fintype.card (f.PointsOver (t ≫ f)) := Fintype.card_pos_iff.mpr ⟨t₀⟩
  omega

end Diagonal

section Semicontinuity

lemma Scheme.Hom.setOf_succ_le_geometricFiberCard [IsSeparated f] [LocallyQuasiFinite f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (k : ℕ) :
    {y | k + 1 ≤ f.geometricFiberCard y} =
      f '' {x | k ≤ f.diagonalComplSnd.geometricFiberCard x} := by
  ext y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := f.nonempty_preimage_of_geometricFiberCard_ne_zero y
      (by simp only [Set.mem_ofPred_eq] at hy; omega)
    refine ⟨x, ?_, rfl⟩
    have := f.geometricFiberCard_diagonalComplSnd_add_one hf x
    simp only [Set.mem_ofPred_eq] at hy ⊢
    omega
  · rintro ⟨x, hx, rfl⟩
    have := f.geometricFiberCard_diagonalComplSnd_add_one hf x
    simp only [Set.mem_ofPred_eq] at hx ⊢
    omega

/-- **EGA IV 15.5.1 (i)**: for a separated, universally open, locally quasi-finite morphism with
finite fibres, the geometric number of points `y ↦ n(y)` is lower semicontinuous:
`{y | k ≤ n(y)}` is open. (Geometric points of the fibres can merge under specialization, but
cannot disappear.) -/
theorem Scheme.Hom.isOpen_setOf_le_geometricFiberCard (k : ℕ) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [UniversallyOpen f] [LocallyQuasiFinite f],
      (∀ y, (f ⁻¹' {y}).Finite) → IsOpen {y | k ≤ f.geometricFiberCard y} := by
  induction k with
  | zero => intro X Y f _ _ _ _; simp
  | succ k ih =>
    intro X Y f _ _ _ hf
    rw [f.setOf_succ_le_geometricFiberCard hf]
    exact f.isOpenMap _ (ih _ (f.finite_preimage_diagonalComplSnd hf))

lemma Scheme.Hom.isEmpty_of_geometricFiberCard_eq_zero [LocallyQuasiFinite f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hn : ∀ y, f.geometricFiberCard y = 0) : IsEmpty X :=
  ⟨fun x ↦ f.geometricFiberCard_ne_zero x (hf _) (hn _)⟩

/-- The key step of EGA IV 15.5.1 (ii): a separated, universally open, locally quasi-finite
morphism with finite fibres and constant geometric number of points is a closed map. -/
theorem Scheme.Hom.isClosedMap_of_geometricFiberCard_eq (m : ℕ) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [UniversallyOpen f] [LocallyQuasiFinite f],
      (∀ y, (f ⁻¹' {y}).Finite) → (∀ y, f.geometricFiberCard y = m) → IsClosedMap f := by
  induction m with
  | zero =>
    intro X Y f _ _ _ hf hn
    have := f.isEmpty_of_geometricFiberCard_eq_zero hf hn
    intro Z _
    rw [Set.eq_empty_of_isEmpty Z, Set.image_empty]
    exact isClosed_empty
  | succ m ih =>
    intro X Y f _ _ _ hf hn
    -- `X ×_Y X ∖ Δ ⟶ X` has constant geometric number of points `m`
    have hg : IsClosedMap f.diagonalComplSnd := ih _ (f.finite_preimage_diagonalComplSnd hf)
      fun x ↦ by have := f.geometricFiberCard_diagonalComplSnd_add_one hf x; rw [hn] at this; omega
    -- hence the second projection `X ×_Y X ⟶ X` is closed
    have hsnd : IsClosedMap (pullback.snd f f) := by
      intro Z hZ
      have e : pullback.snd f f '' Z = pullback.diagonal f ⁻¹' Z ∪
          f.diagonalComplSnd '' (f.diagonalCompl.ι ⁻¹' Z) := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          by_cases hzΔ : z ∈ Set.range (pullback.diagonal f)
          · obtain ⟨x₀, rfl⟩ := hzΔ
            left
            simpa [← Scheme.Hom.comp_apply] using hz
          · right
            exact ⟨⟨z, hzΔ⟩, hz, rfl⟩
        · rintro (hx | ⟨z, hz, rfl⟩)
          · exact ⟨_, hx, by simp [← Scheme.Hom.comp_apply]⟩
          · exact ⟨_, hz, rfl⟩
      rw [e]
      exact (hZ.preimage (pullback.diagonal f).continuous).union
        (hg _ (hZ.preimage f.diagonalCompl.ι.continuous))
    -- `f` is surjective and open
    have hsurj (y : Y) : ∃ x, f x = y :=
      f.nonempty_preimage_of_geometricFiberCard_ne_zero y (by rw [hn]; omega)
    intro W hW
    have h1 : f ⁻¹' (f '' W) = pullback.snd f f '' (pullback.fst f f ⁻¹' W) := by
      ext x
      constructor
      · rintro ⟨w, hw, hwx⟩
        obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) w x hwx
        exact ⟨z, by simpa [hz₁] using hw, hz₂⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨pullback.fst f f z, hz, ?_⟩
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h2 : (f '' W)ᶜ = f '' (f ⁻¹' (f '' W))ᶜ := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hsurj y
        exact ⟨x, hy, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [← isOpen_compl_iff, h2]
    refine f.isOpenMap _ ?_
    rw [isOpen_compl_iff, h1]
    exact hsnd _ (hW.preimage (pullback.fst f f).continuous)

/-- **EGA IV 15.5.1 (ii)**: a separated, universally open, locally quasi-finite morphism with
finite fibres whose geometric number of points is constant is universally closed. -/
theorem Scheme.Hom.universallyClosed_of_geometricFiberCard_eq [IsSeparated f] [UniversallyOpen f]
    [LocallyQuasiFinite f] (hf : ∀ y, (f ⁻¹' {y}).Finite) (m : ℕ)
    (hn : ∀ y, f.geometricFiberCard y = m) : UniversallyClosed f := by
  constructor
  intro X' Y' i₁ i₂ f' h
  have : IsSeparated f' := MorphismProperty.of_isPullback h.flip ‹_›
  have : UniversallyOpen f' := MorphismProperty.of_isPullback h.flip ‹_›
  have : LocallyQuasiFinite f' := MorphismProperty.of_isPullback h.flip ‹_›
  exact Scheme.Hom.isClosedMap_of_geometricFiberCard_eq m f'
    (Scheme.Hom.finite_preimage_of_isPullback f hf h.flip) fun y' ↦ by
      rw [Scheme.Hom.geometricFiberCard_of_isPullback f hf h.flip, hn]

/-- **EGA IV 15.5.1 (ii)**: a separated, universally open, quasi-finite morphism of finite type
with constant geometric number of points is finite. -/
theorem Scheme.Hom.isFinite_of_geometricFiberCard_eq [IsSeparated f] [UniversallyOpen f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f] (m : ℕ)
    (hn : ∀ y, f.geometricFiberCard y = m) : IsFinite f := by
  have := f.universallyClosed_of_geometricFiberCard_eq f.finite_preimage_singleton m hn
  have : IsProper f := ⟨⟩
  exact .of_isProper_of_locallyQuasiFinite f

lemma Scheme.Hom.geometricFiberCard_morphismRestrict [LocallyQuasiFinite f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (U : Y.Opens) (y : U) :
    (f ∣_ U).geometricFiberCard y = f.geometricFiberCard y.1 :=
  Scheme.Hom.geometricFiberCard_of_isPullback f hf (isPullback_morphismRestrict f U).flip y

/-- **EGA IV 15.5.1 (ii)**, local form: if the geometric number of points is constant on an open
`U`, then `f` is finite over `U`. -/
theorem Scheme.Hom.isFinite_morphismRestrict_of_geometricFiberCard_eq [IsSeparated f]
    [UniversallyOpen f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U : Y.Opens) (m : ℕ) (hn : ∀ y ∈ U, f.geometricFiberCard y = m) : IsFinite (f ∣_ U) :=
  have : UniversallyOpen (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹_›
  (f ∣_ U).isFinite_of_geometricFiberCard_eq m fun y ↦
    (f.geometricFiberCard_morphismRestrict f.finite_preimage_singleton U y).trans (hn _ y.2)

end Semicontinuity

section FiniteEtale

variable [IsFinite f] [Etale f]

instance : IsFinite f.diagonalComplSnd := by
  have := FormallyUnramified.isOpenImmersion_diagonal f
  have : IsClosedImmersion f.diagonalCompl.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl)
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

instance : Etale f.diagonalComplSnd := by
  unfold Scheme.Hom.diagonalComplSnd; infer_instance

/-- For a finite étale morphism, `{y | k ≤ n(y)}` is closed. -/
theorem Scheme.Hom.isClosed_setOf_le_geometricFiberCard (k : ℕ) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f],
      IsClosed {y | k ≤ f.geometricFiberCard y} := by
  induction k with
  | zero => intro X Y f _ _; simp
  | succ k ih =>
    intro X Y f _ _
    rw [f.setOf_succ_le_geometricFiberCard f.finite_preimage_singleton]
    exact f.isClosedMap _ (ih _)

/-- The geometric number of points of a finite étale morphism is locally constant
(EGA IV 15.5.1; SGA 1 I.10.9). -/
theorem Scheme.Hom.isLocallyConstant_geometricFiberCard :
    IsLocallyConstant f.geometricFiberCard := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro k
  have e : f.geometricFiberCard ⁻¹' {k} =
      {y | k ≤ f.geometricFiberCard y} ∩ {y | k + 1 ≤ f.geometricFiberCard y}ᶜ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_compl_iff, not_le]
    omega
  rw [e]
  exact (f.isOpen_setOf_le_geometricFiberCard k f.finite_preimage_singleton).inter
    (f.isClosed_setOf_le_geometricFiberCard (k + 1)).isOpen_compl

end FiniteEtale

section Preimmersion

/-- The residue field maps of a preimmersion are isomorphisms (its stalk maps are surjective). -/
instance Scheme.Hom.isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsPreimmersion g] (x : X) : IsIso (g.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(g.residueFieldMap x).hom.injective, fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := g.stalkMap_surjective x b
  exact ⟨Y.residue (g x) c, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

/-- The stalk maps of a flat preimmersion (for instance `Spec 𝒪_{X,x} ⟶ X`, or a base change of
it) are isomorphisms: they are surjective, and injective as flat local homomorphisms. -/
lemma Scheme.Hom.bijective_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Flat g] [IsPreimmersion g] (x : X) : Function.Bijective (g.stalkMap x) := by
  refine ⟨?_, g.stalkMap_surjective x⟩
  let _ := (g.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) := Flat.stalkMap g x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)

/-- A scheme with a flat preimmersion to a reduced scheme is reduced. -/
lemma isReduced_of_flat_of_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g]
    [IsPreimmersion g] [IsReduced Y] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨_, hsurj⟩ := g.bijective_stalkMap_of_flat_of_isPreimmersion x
    refine ⟨fun a ha ↦ ?_⟩
    obtain ⟨b, rfl⟩ := hsurj a
    have hb : IsNilpotent b := by
      obtain ⟨n, hn⟩ := ha
      exact ⟨n, (g.bijective_stalkMap_of_flat_of_isPreimmersion x).1
        (by rw [map_pow, hn, map_zero])⟩
    rw [hb.eq_zero, map_zero]
  exact isReduced_of_isReduced_stalk X

/-- Given a commutative square `φ ≫ b = a ≫ ψ` of fields with `a`, `b` isomorphisms,
`[E : F] = [E' : F']` for the algebra structures given by `φ` and `ψ`. -/
lemma finrank_eq_of_isIso {F E F' E' : CommRingCat.{u}} (φ : F ⟶ E) (ψ : F' ⟶ E') (a : F ⟶ F')
    (b : E ⟶ E') [IsIso a] [IsIso b] (h : φ ≫ b = a ≫ ψ) :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    Module.finrank F E = Module.finrank F' E' := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (asIso a).commRingCatIsoToRingEquiv
    (asIso b).commRingCatIsoToRingEquiv ?_
  ext x
  exact congrArg (fun χ : F ⟶ E' ↦ χ x) h.symm

/-- The degree `∑_{x ∈ f⁻¹(y)} [κ(x) : κ(y)]` of the fibre `f⁻¹(y)` (zero if the fibre is
infinite). -/
noncomputable def Scheme.Hom.fiberDegree (y : Y) : ℕ :=
  ∑ᶠ x : f ⁻¹' {y}, f.residueDegree x.1

variable {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
/-- The degree of the fibres is invariant under base change along a preimmersion (for instance
an open immersion, or `Spec 𝒪_{Y,y} ⟶ Y`), which does not change the residue fields. -/
theorem Scheme.Hom.fiberDegree_of_isPullback [IsPreimmersion g] (h : IsPullback g' f' f g)
    (y' : Y') : f'.fiberDegree y' = f.fiberDegree (g y') := by
  have : IsPreimmersion g' := MorphismProperty.of_isPullback h.flip ‹_›
  have hgy (x' : X') (hx' : f' x' = y') : f (g' x') = g y' := by
    rw [← hx', ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  let e : f' ⁻¹' {y'} → f ⁻¹' {g y'} := fun x' ↦ ⟨g' x'.1, hgy x'.1 x'.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab ↦ Subtype.ext (g'.isEmbedding.injective (congrArg Subtype.val hab)),
      fun ⟨x, hx⟩ ↦ ?_⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' hx
    refine ⟨⟨h.isoPullback.inv z, ?_⟩, Subtype.ext ?_⟩
    · change f' (h.isoPullback.inv z) = y'
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    · change g' (h.isoPullback.inv z) = x
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
  rw [fiberDegree, fiberDegree, ← finsum_comp_equiv (Equiv.ofBijective e he)]
  refine finsum_congr fun ⟨x', hx'⟩ ↦ ?_
  change f'.residueDegree x' = f.residueDegree (g' x')
  have hsq : f.residueFieldMap (g' x') ≫ g'.residueFieldMap x' =
      ((Y.residueFieldCongr (by rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply])).hom ≫
        g.residueFieldMap (f' x')) ≫ f'.residueFieldMap x' := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr h.w,
      Scheme.residueFieldMap_comp, Category.assoc]
  exact (finrank_eq_of_isIso _ _ _ _ hsq).symm

end Preimmersion

end AlgebraicGeometry
