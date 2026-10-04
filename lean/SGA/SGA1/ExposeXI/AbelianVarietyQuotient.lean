/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.FundamentalGroupDescent
import SGA.SGA1.ExposeV.FiniteQuotientProperties
import SGA.SGA1.ExposeV.InertiaGroups
import SGA.SGA1.ExposeV.QuotientEtale
import SGA.SGA1.ExposeV.RelativeQuotient
import SGA.SGA1.ExposeXI.AbelianVarietyMulN

/-!
# SGA 1, Exposé XI.2.1 in every characteristic, from `n_A` being an isogeny

SGA recalls (XI.2) that multiplication by `n > 0` on an abelian variety `A` over an algebraically
closed field `k` is an isogeny (`MulNIsogenyStatement`), and deduces XI.2.1 from it together with
Serre–Lang. We prove this deduction (`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`):
`MulNIsogenyStatement` implies `AbelianVarietyFundamentalGroupStatement`.

What `exists_tateModule_equiv_of_isogeny` (`AbelianVarietyIsogeny`) still needs is, for every `n`,
an étale covering of `A` through which `n_A` lifts injectively on `K_n`. When `p ∣ n` in
characteristic `p`, `n_A` is not étale; its "étale part" is built as follows
(`exists_lift_mulN_injective`):

* `K_n` acts on `A` by translations (`translate`), freely: the inertia groups are trivial
  (`eq_one_of_mem_inertiaGroup_translate`), since a translation fixing a point `Spec κ(x) ⟶ A`
  is the identity in the group `A(κ(x))`;
* the quotient `B = A / K_n` exists, relative to the finite morphism `n_A` (V.1.8,
  `ExposeV.quotientScheme`), and `A ⟶ B` is a finite étale Galois covering with group `K_n`
  (V.2.3, `ExposeV.etale_of_inertiaGroup_eq`);
* `h : B ⟶ A` (with `n_A = (A ⟶ B) ≫ h`) is finite, surjective and radicial
  (`universallyInjective_fromQuotient_translate`): two geometric points of `A` with the same
  image under `n_A` differ by an `Ω`-point of the kernel of `n_A`, which is a `k`-point since that
  kernel is finite over `k` (`exists_torsionPoints_comp_eq`);
* by the topological invariance of the étale site (IX.4.10 for étale coverings,
  `ExposeIX.essSurj_fetPullback_of_isFinite`), the étale covering `A ⟶ B` is the base change of
  an étale covering `Y ⟶ A`, and `A ≅ Y ×_A B ⟶ Y` lifts `n_A` and is injective.

For `n` invertible in `k`, `n_A` is an isogeny (`mulNIsogeny_of_ne_zero`), so in characteristic
`p > 0` only `p_A` has to be assumed an isogeny (`exists_tateModule_equiv_of_charP`). No theorem of
the cube is used here; it enters only through that assumption.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

namespace SGA.SGA1.ExposeXI

section Translate

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

/-- The action of `K_n` on `A` by the translations `y ↦ y · a`. -/
noncomputable abbrev translate (n : ℕ) (a : torsionPoints A n) : A.left ⟶ A.left :=
  (GrpObj.mulRight (a : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom.left

lemma isRightAction_translate (n : ℕ) :
    ExposeV.IsRightAction (translate A n) where
  map_one := by
    change (GrpObj.mulRight (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom.left = _
    rw [← MonObj.one_eq_one, GrpObj.mulRight_one]
    rfl
  map_mul a b := by
    change (GrpObj.mulRight ((a : 𝟙_ (Over (Spec (.of k))) ⟶ A) *
      (b : 𝟙_ (Over (Spec (.of k))) ⟶ A))).hom.left =
      ((GrpObj.mulRight (a : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom ≫
        (GrpObj.mulRight (b : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom).left
    have key (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
        (GrpObj.mulRight x).hom = 𝟙 A * (toUnit A ≫ x) := by
      rw [← comp_mulRight_hom, Category.id_comp]
    congr 1
    rw [comp_mulRight_hom, key, key, MonObj.comp_mul, _root_.mul_assoc]

lemma translate_comp_mulN (n : ℕ) (a : torsionPoints A n) :
    translate A n a ≫ (mulN A n).left = (mulN A n).left :=
  congrArg CommaMorphism.left
    (mulRight_hom_comp_mulN_of_pow_eq_one A _ ((mem_torsionPoints A).mp a.2))

end Translate

section Points

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsCommMonObj A] [LocallyOfFiniteType A.hom] (n : ℕ)

/-- The inertia groups of the action of `K_n` on `A` by translations are trivial: a translation
`τ_a` fixing the point `Spec κ(x) ⟶ A` fixes it in the group `A(κ(x))`, so `a = 1`. -/
theorem eq_one_of_mem_inertiaGroup_translate (x : A.left) (a : torsionPoints A n)
    (ha : a ∈ ExposeV.inertiaGroup (translate A n) x) : a = 1 := by
  let s := A.left.fromSpecResidueField x
  let S : Over (Spec (.of k)) := Over.mk (s ≫ A.hom)
  let s' : S ⟶ A := Over.homMk s rfl
  have h₁ : s' ≫ (GrpObj.mulRight (a : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom = s' :=
    Over.OverMorphism.ext ha
  rw [comp_mulRight_hom, mul_eq_left] at h₁
  have h₂ : toUnit S ≫ (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) = toUnit S ≫ 1 := by
    rw [h₁, ← MonObj.one_eq_one, ← Hom.one_def]
  have h₃ : (s ≫ A.hom) ≫ pointLeft A a = (s ≫ A.hom) ≫ pointLeft A 1 :=
    congrArg CommaMorphism.left h₂
  obtain ⟨t⟩ : Nonempty (Spec (A.left.residueField x)) := inferInstance
  have h₄ := congrArg (fun f ↦ f t) h₃
  simp only [Scheme.Hom.comp_apply] at h₄
  have hpt : A.hom (s t) = closedPoint k := Subsingleton.elim _ _
  rw [hpt] at h₄
  exact Subtype.ext (pointLeft_injective h₄)

/-- If `n_A` is finite, two points `a₁ a₂ : Spec Ω ⟶ A` with values in a field and with the same
image under `n_A` differ by the translation by an element of `K_n`. Indeed `a₁ a₂⁻¹` is an
`Ω`-point of the kernel of `n_A`; its image is a point of the finite fibre of `n_A` over the
origin, hence a closed point, and an `Ω`-point at a closed point comes from a `k`-point
(`eq_comp_pointOfClosedPoint`). -/
theorem exists_torsionPoints_comp_eq [IsFinite (mulN A n).left] {Ω : Type u} [Field Ω]
    (a₁ a₂ : Spec (.of Ω) ⟶ A.left) (h : a₁ ≫ (mulN A n).left = a₂ ≫ (mulN A n).left) :
    ∃ c : torsionPoints A n, a₁ = a₂ ≫ translate A n c := by
  have hS : a₂ ≫ A.hom = a₁ ≫ A.hom := by
    rw [← Over.w (mulN A n), ← Category.assoc, ← h, Category.assoc]
  let S : Over (Spec (.of k)) := Over.mk (a₁ ≫ A.hom)
  let b₁ : S ⟶ A := Over.homMk a₁ rfl
  let b₂ : S ⟶ A := Over.homMk a₂ hS
  have hm (x : S ⟶ A) : x ≫ mulN A n = x ^ n := by
    rw [mulN, MonObj.comp_pow, Category.comp_id]
  have hpow : b₁ ^ n = b₂ ^ n := by
    rw [← hm, ← hm]
    exact Over.OverMorphism.ext h
  let c := b₁ * b₂⁻¹
  have hc : c ^ n = 1 := by rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  -- the point `c` lies over the origin
  have hcn : c.left ≫ (mulN A n).left = (a₁ ≫ A.hom) ≫ unitSection A := by
    have := congrArg CommaMorphism.left ((hm c).trans hc)
    rw [Hom.one_def] at this
    exact this
  have he : IsClosed {unitSection A (closedPoint k)} :=
    ((pointEquivClosedPoint A.hom) ⟨unitSection A, Over.w η[A]⟩).2
  obtain ⟨t⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have hz : (mulN A n).left (c.left t) = unitSection A (closedPoint k) := by
    have := congrArg (fun f ↦ f t) hcn
    simp only [Scheme.Hom.comp_apply] at this
    rw [this]
    exact congrArg (unitSection A) (Subsingleton.elim _ _)
  have hzc : IsClosed {c.left t} :=
    (mulN A n).left.isClosed_singleton_of_isClosed_singleton_apply (hz ▸ he)
  let q := pointOfClosedPoint A.hom (c.left t) hzc
  let c₀ : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk q (pointOfClosedPoint_comp A.hom _ hzc)
  have hcc₀ : toUnit S ≫ c₀ = c := by
    apply Over.OverMorphism.ext
    let cl : Spec (.of Ω) ⟶ A.left := c.left
    change (a₁ ≫ A.hom) ≫ q = cl
    have ht : cl (closedPoint Ω) = cl t := congrArg cl (Subsingleton.elim _ _)
    rw [eq_comp_pointOfClosedPoint A.hom hzc cl ht]
    congr 1
    exact (Over.w c).symm
  have hc₀ : c₀ ∈ torsionPoints A n := by
    rw [mem_torsionPoints]
    apply pointLeft_injective
    rw [← pointLeft_comp_mulN, pointLeft_one]
    exact (congrArg (mulN A n).left (pointOfClosedPoint_apply A.hom _ hzc _)).trans hz
  refine ⟨⟨c₀, hc₀⟩, congrArg CommaMorphism.left (?_ : b₁ = b₂ ≫ _)⟩
  rw [comp_mulRight_hom]
  change b₁ = b₂ * (toUnit S ≫ c₀)
  rw [hcc₀, mul_comm, inv_mul_cancel_right]

end Points

section Quotient

/-! ### The quotient `A / K_n` over `n_A` -/

attribute [local instance] finite_torsionPoints

open ExposeV

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsCommMonObj A] [LocallyOfFiniteType A.hom] (n : ℕ) [IsFinite (mulN A n).left]

/-- `A ⟶ A / K_n` is étale (V.2.3: the inertia groups are trivial). -/
theorem etale_toQuotient_translate : Etale (toQuotient (translate_comp_mulN A n)) :=
  etale_of_inertiaGroup_eq (isRightAction_translate A n) (comp_toQuotient _)
    (sectionsAreInvariant_toQuotient _) (eq_one_of_mem_inertiaGroup_translate A n)

lemma surjective_toQuotient_translate : Surjective (toQuotient (translate_comp_mulN A n)) :=
  surjective_of_sectionsAreInvariant (isRightAction_translate A n) (comp_toQuotient _)
    fun U _ ↦ sectionsAreInvariant_toQuotient _ U

/-- `A ⟶ A / K_n` is finite (V.1.5). -/
theorem isFinite_toQuotient_translate : IsFinite (toQuotient (translate_comp_mulN A n)) := by
  have : LocallyOfFiniteType (toQuotient (translate_comp_mulN A n) ≫
      fromQuotient (translate_comp_mulN A n)) := by
    rw [toQuotient_fromQuotient]
    infer_instance
  exact isFinite_of_locallyOfFiniteType_comp (isRightAction_translate A n) (comp_toQuotient _)
    (fun U _ ↦ sectionsAreInvariant_toQuotient _ U) (fromQuotient (translate_comp_mulN A n))

/-- `A / K_n ⟶ A` is finite: it is affine and universally closed, hence integral, and of finite
type (V.1.5, `A` being noetherian). -/
theorem isFinite_fromQuotient_translate : IsFinite (fromQuotient (translate_comp_mulN A n)) := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := surjective_toQuotient_translate A n
  have hc : toQuotient (translate_comp_mulN A n) ≫ fromQuotient (translate_comp_mulN A n) =
      (mulN A n).left := toQuotient_fromQuotient _
  have : LocallyOfFiniteType (toQuotient (translate_comp_mulN A n) ≫
      fromQuotient (translate_comp_mulN A n)) := by rw [hc]; infer_instance
  have : UniversallyClosed (toQuotient (translate_comp_mulN A n) ≫
      fromQuotient (translate_comp_mulN A n)) := by rw [hc]; infer_instance
  have : UniversallyClosed (fromQuotient (translate_comp_mulN A n)) :=
    UniversallyClosed.of_comp_surjective (toQuotient (translate_comp_mulN A n)) _
  have : IsIntegralHom (fromQuotient (translate_comp_mulN A n)) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have : LocallyOfFiniteType (fromQuotient (translate_comp_mulN A n)) :=
    locallyOfFiniteType_of_comp (isRightAction_translate A n) (comp_toQuotient _)
      (fun U _ ↦ sectionsAreInvariant_toQuotient _ U) _
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- `A / K_n ⟶ A` is radicial: two geometric points of `A / K_n` with the same image in `A` lift
to geometric points of `A` with the same image under `n_A`, which differ by an element of `K_n`
(`exists_torsionPoints_comp_eq`). -/
theorem universallyInjective_fromQuotient_translate :
    UniversallyInjective (fromQuotient (translate_comp_mulN A n)) := by
  set p := toQuotient (translate_comp_mulN A n)
  set h := fromQuotient (translate_comp_mulN A n)
  have hph : p ≫ h = (mulN A n).left := toQuotient_fromQuotient _
  have : Etale p := etale_toQuotient_translate A n
  have : Surjective p := surjective_toQuotient_translate A n
  refine ((tfae_universallyInjective h).out 1 2).mpr ?_
  intro K _ b₁ b₂ hb
  simp only at hb
  let Ω := AlgebraicClosure K
  let j : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Epi j := by
    have : Flat j := HasRingHomProperty.Spec_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat K Ω))
    have : Surjective j := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
    infer_instance
  -- geometric points of `A / K_n` lift to `A`
  have hlift (b : Spec (.of Ω) ⟶ quotientScheme (translate_comp_mulN A n)) :
      ∃ a : Spec (.of Ω) ⟶ A.left, a ≫ p = b := by
    obtain ⟨w, hw⟩ := p.surjective (b (closedPoint Ω))
    have : Etale (p ≫ 𝟙 _) := by rw [Category.comp_id]; infer_instance
    obtain ⟨a, ha, -⟩ := exists_geometricPoint_lift_of_isSeparable p b w hw
      (isSeparable_residueFieldMap_of_etale_comp p (𝟙 _) w)
    exact ⟨a, ha⟩
  obtain ⟨a₁, ha₁⟩ := hlift (j ≫ b₁)
  obtain ⟨a₂, ha₂⟩ := hlift (j ≫ b₂)
  have h₁₂ : a₁ ≫ (mulN A n).left = a₂ ≫ (mulN A n).left := by
    rw [← hph, ← Category.assoc, ha₁, ← Category.assoc, ha₂, Category.assoc, Category.assoc, hb]
  obtain ⟨c, hc⟩ := exists_torsionPoints_comp_eq A n a₁ a₂ h₁₂
  refine (cancel_epi j).mp ?_
  rw [← ha₁, ← ha₂, hc, Category.assoc, comp_toQuotient]

-- `MorphismProperty.pullback_fst` for `@UniversallyInjective` needs this option (as in mathlib's
-- `Morphisms/Integral.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- If `n_A` is finite and surjective, there is an étale covering `Y` of `A` through which `n_A`
lifts injectively on `K_n`: by IX.4.10 for étale coverings along the finite radicial surjective
`A / K_n ⟶ A`, the finite étale `A ⟶ A / K_n` is the base change of some `Y`, and
`A ≅ Y ×_A (A / K_n) ⟶ Y` is the lift. -/
theorem exists_lift_mulN_injective [Surjective (mulN A n).left] :
    ∃ (Y : ExposeV.FEt A.left) (g : A.left ⟶ Y.left), g ≫ Y.hom = (mulN A n).left ∧
      ∀ a b : torsionPoints A n, pointLeft A a ≫ g = pointLeft A b ≫ g → a = b := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  set p := toQuotient (translate_comp_mulN A n)
  set h := fromQuotient (translate_comp_mulN A n)
  have hph : p ≫ h = (mulN A n).left := toQuotient_fromQuotient _
  have := isFinite_fromQuotient_translate A n
  have := universallyInjective_fromQuotient_translate A n
  have : Surjective (p ≫ h) := by rw [hph]; infer_instance
  have : Surjective h := Surjective.of_comp p h
  have := ExposeIX.essSurj_fetPullback_of_isFinite h
  let Y' : ExposeV.FEt (quotientScheme (translate_comp_mulN A n)) :=
    MorphismProperty.Over.mk ⊤ p
      ⟨isFinite_toQuotient_translate A n, etale_toQuotient_translate A n⟩
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (ExposeV.FEt.pullback h) Y'
  let i : A.left ⟶ ((ExposeV.FEt.pullback h).obj Y).left := e.inv.left
  have hi : i ≫ ((ExposeV.FEt.pullback h).obj Y).hom = p := MorphismProperty.Over.w e.inv
  have : IsIso i := inferInstanceAs
    (IsIso ((MorphismProperty.Over.forget _ ⊤ _ ⋙ CategoryTheory.Over.forget _).map e.inv))
  let q : Y.left ⟶ A.left := Y.hom
  let pr : ((ExposeV.FEt.pullback h).obj Y).left ⟶ Y.left := pullback.fst q h
  have : UniversallyInjective pr :=
    MorphismProperty.pullback_fst (P := @UniversallyInjective) _ _ ‹UniversallyInjective h›
  refine ⟨Y, i ≫ pr, ?_, fun a b hab ↦ ?_⟩
  · have hY : pr ≫ q = ((ExposeV.FEt.pullback h).obj Y).hom ≫ h := pullback.condition
    change (i ≫ pr) ≫ q = _
    rw [Category.assoc, hY, ← Category.assoc, hi, hph]
  · have : UniversallyInjective (i ≫ pr) :=
      MorphismProperty.comp_mem @UniversallyInjective _ _ inferInstance ‹_›
    have hinj : Function.Injective (i ≫ pr) := (i ≫ pr).injective
    have := congrArg (fun f ↦ f (closedPoint k)) hab
    simp only at this
    exact Subtype.ext (pointLeft_injective (hinj this))

end Quotient

section Main

/-- XI.2.1 for an abelian variety all of whose multiplications `n_A` (`n > 0`) are isogenies
(finite and surjective): the canonical map `T(A) → π₁(A, 0)` is an isomorphism of topological
groups. -/
theorem exists_tateModule_equiv_of_mulNIsogeny (k : Type u) [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]
    (hiso : ∀ n : ℕ, 0 < n → IsFinite (mulN A n).left ∧ Surjective (mulN A n).left) :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyFundamentalGroupConclusion k A := by
  have := isCommMonObj_of_smooth A
  refine exists_tateModule_equiv_of_isogeny k A hiso fun n ↦ ?_
  have := (hiso n n.pos).1
  have := (hiso n n.pos).2
  exact exists_lift_mulN_injective A n

/-- If `p_A` is finite and surjective, so is `(pᵉ)_A`. -/
lemma isFinite_and_surjective_mulN_pow {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
    [ConnectedSpace A.left] {p : ℕ} (hp : IsFinite (mulN A p).left ∧ Surjective (mulN A p).left)
    (e : ℕ) : IsFinite (mulN A (p ^ e)).left ∧ Surjective (mulN A (p ^ e)).left := by
  induction e with
  | zero => simpa using mulNIsogeny_of_ne_zero A (n := 1) (by simp)
  | succ e ih =>
    have := ih.1
    have := ih.2
    have := hp.1
    have := hp.2
    rw [pow_succ, ← mulN_left_comp_mulN_left]
    exact ⟨inferInstance, inferInstance⟩

/-- XI.2.1 in characteristic `p > 0` for an abelian variety whose multiplication by `p` is an
isogeny: the canonical map `T(A) → π₁(A, 0)` is an isomorphism of topological groups. For `n`
prime to `p`, `n_A` is an isogeny by `mulNIsogeny_of_ne_zero`, so only `p_A` is assumed. -/
theorem exists_tateModule_equiv_of_charP (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [Smooth A.hom] [ConnectedSpace A.left]
    (hp : IsFinite (mulN A p).left ∧ Surjective (mulN A p).left) :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyFundamentalGroupConclusion k A := by
  have := isCommMonObj_of_smooth A
  refine exists_tateModule_equiv_of_mulNIsogeny k A fun n hn ↦ ?_
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hm : (m : k) ≠ 0 := (CharP.cast_eq_zero_iff k p m).not.mpr hpm
  have := (mulNIsogeny_of_ne_zero A hm).1
  have := (mulNIsogeny_of_ne_zero A hm).2
  have := (isFinite_and_surjective_mulN_pow A hp e).1
  have := (isFinite_and_surjective_mulN_pow A hp e).2
  rw [mul_comm, ← mulN_left_comp_mulN_left]
  exact ⟨inferInstance, inferInstance⟩

/-- XI.2.1 from the fact recalled by SGA that `n_A` is an isogeny: `MulNIsogenyStatement` implies
`AbelianVarietyFundamentalGroupStatement`. -/
theorem abelianVarietyFundamentalGroupStatement_of_mulNIsogeny
    (h : MulNIsogenyStatement.{u}) : AbelianVarietyFundamentalGroupStatement.{u} :=
  fun k _ _ A _ _ _ _ ↦ exists_tateModule_equiv_of_mulNIsogeny k A (h k A)

end Main

end SGA.SGA1.ExposeXI
