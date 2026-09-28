/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.SteinEtale
import SGA.SGA1.ExposeXI.Geometry

/-!
# SGA 1, Exposé XI.2: the fundamental group of an abelian variety is commutative

Since `π₁` commutes with products (X.1.7, `ExposeX.bijective_map_prod`), the multiplication of a
group scheme `A` over an algebraically closed field induces a homomorphism
`π₁(A) × π₁(A) → π₁(A)` which is unital, and the Eckmann–Hilton argument
(`mul_comm_of_monoidHom_prod`) shows that `π₁(A)` is commutative.

We prove this for any proper, connected and reduced `k`-scheme `X` with a rational point `e` and a
multiplication `m : X ×ₖ X ⟶ X` for which `e` is a two-sided unit (an "H-space";
`mul_comm_of_hSpace`), and deduce it for group schemes proper, connected and reduced over `k`,
in particular for abelian varieties (`mul_comm_of_monObj`). The unit laws only hold up to the
change of base point along the canonical paths of Exposé V, so instead of `m_*` we use that the
images of `π₁(X) ⟶ π₁(X ×ₖ X)` under the two inclusions `x ↦ (x, e)` and `x ↦ (e, x)` commute
(by X.1.7), and that `m_*` maps each of them isomorphically onto `π₁(X)`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

section Transport

variable {Ω : Type u} [Field Ω] {X Y : Scheme.{u}}

/-- The identification `π₁(X, s) ≅ π₁(X, s')` for equal geometric points `s = s'`. -/
noncomputable def fundamentalGroupCongr {s s' : Spec (.of Ω) ⟶ X} (h : s = s') :
    ExposeV.etaleFundamentalGroup Ω s ≃* ExposeV.etaleFundamentalGroup Ω s' := by
  subst h
  exact MulEquiv.refl _

lemma map_fundamentalGroupCongr (f : X ⟶ Y) {s s' : Spec (.of Ω) ⟶ X} (h : s = s')
    (σ : ExposeV.etaleFundamentalGroup Ω s) :
    ExposeV.etaleFundamentalGroup.map Ω f s' (fundamentalGroupCongr h σ) =
      fundamentalGroupCongr (congrArg (· ≫ f) h) (ExposeV.etaleFundamentalGroup.map Ω f s σ) := by
  subst h
  rfl

/-- If `i ≫ m = 𝟙`, the composite `π₁(T, t) ⟶ π₁(Y, t ≫ i) ⟶ π₁(T, t ≫ i ≫ m)` is bijective
(it is a conjugation, V.6.3). -/
lemma bijective_map_comp_map_of_comp_eq_id {T Y : Scheme.{u}} (i : T ⟶ Y) (m : Y ⟶ T)
    (hm : i ≫ m = 𝟙 T) (t : Spec (.of Ω) ⟶ T) :
    Function.Bijective ((ExposeV.etaleFundamentalGroup.map Ω m (t ≫ i)).comp
      (ExposeV.etaleFundamentalGroup.map Ω i t)) := by
  obtain ⟨φ, hφ⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω i m hm t
  rw [hφ]
  exact φ.conjAut.bijective

/-- Variant of `bijective_map_comp_map_of_comp_eq_id` in which the base point `t ≫ i` is replaced
by an equal point `c`. -/
lemma bijective_map_comp_congr_comp_map {T Y : Scheme.{u}} (i : T ⟶ Y) (m : Y ⟶ T)
    (hm : i ≫ m = 𝟙 T) (t : Spec (.of Ω) ⟶ T) {c : Spec (.of Ω) ⟶ Y} (h : t ≫ i = c) :
    Function.Bijective ((ExposeV.etaleFundamentalGroup.map Ω m c).comp
      ((fundamentalGroupCongr h).toMonoidHom.comp (ExposeV.etaleFundamentalGroup.map Ω i t))) := by
  subst h
  exact bijective_map_comp_map_of_comp_eq_id i m hm t

end Transport

/-- The group-theoretic core of the Eckmann–Hilton argument: if the images of `α, β : G ⟶ H`
commute, and `M : H ⟶ K` is injective on the image of `α` and maps the image of `β` onto `K`,
then `G` is commutative. -/
lemma mul_comm_of_commute_of_injective_of_surjective {G H K : Type*} [Group G] [Group H]
    [Group K] (α β : G →* H) (M : H →* K) (hcomm : ∀ x y, α x * β y = β y * α x)
    (hα : Function.Injective (M.comp α)) (hβ : Function.Surjective (M.comp β)) (a b : G) :
    a * b = b * a := by
  apply hα
  obtain ⟨y, hy⟩ := hβ (M (α b))
  simp only [MonoidHom.comp_apply, map_mul] at hy ⊢
  rw [← hy, ← map_mul, hcomm, map_mul]

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- XI.2 (Eckmann–Hilton): let `X` be a proper, connected and reduced scheme over an algebraically
closed field `k`, with a rational point `e` and a multiplication `m : X ×ₖ X ⟶ X` having `e` as a
two-sided unit. Then `π₁(X, e)` is commutative. -/
theorem mul_comm_of_hSpace {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsReduced X]
    [ConnectedSpace X] (e : Spec (.of k) ⟶ X) (he : e ≫ sX = 𝟙 _) (m : pullback sX sX ⟶ X)
    (hm₁ : pullback.lift (𝟙 X) (sX ≫ e) (by simp [he]) ≫ m = 𝟙 X)
    (hm₂ : pullback.lift (sX ≫ e) (𝟙 X) (by simp [he]) ≫ m = 𝟙 X)
    (a b : ExposeV.etaleFundamentalGroup k e) : a * b = b * a := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let i₁ : X ⟶ pullback sX sX := pullback.lift (𝟙 X) (sX ≫ e) (by simp [he])
  let i₂ : X ⟶ pullback sX sX := pullback.lift (sX ≫ e) (𝟙 X) (by simp [he])
  let c := e ≫ i₁
  have hi₁₁ : i₁ ≫ pullback.fst sX sX = 𝟙 X := pullback.lift_fst _ _ _
  have hi₁₂ : i₁ ≫ pullback.snd sX sX = sX ≫ e := pullback.lift_snd _ _ _
  have hi₂₁ : i₂ ≫ pullback.fst sX sX = sX ≫ e := pullback.lift_fst _ _ _
  have hi₂₂ : i₂ ≫ pullback.snd sX sX = 𝟙 X := pullback.lift_snd _ _ _
  have h₂₁ : e ≫ i₂ = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hi₂₁, hi₁₁, reassoc_of% he, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hi₂₂, hi₁₂, reassoc_of% he, Category.comp_id]
  have hc : c ≫ pullback.snd sX sX ≫ sX = 𝟙 _ := by
    rw [← Category.assoc, Category.assoc e, hi₁₂, Category.assoc, Category.assoc, he,
      Category.comp_id, he]
  have hΦ := ExposeX.bijective_map_prod sX sX c hc
  -- The inclusions `x ↦ (x, e)` and `x ↦ (e, x)` on fundamental groups.
  let α : ExposeV.etaleFundamentalGroup k e →* ExposeV.etaleFundamentalGroup k c :=
    ExposeV.etaleFundamentalGroup.map k i₁ e
  let β : ExposeV.etaleFundamentalGroup k e →* ExposeV.etaleFundamentalGroup k c :=
    (fundamentalGroupCongr h₂₁).toMonoidHom.comp (ExposeV.etaleFundamentalGroup.map k i₂ e)
  have hα : ∀ x, ExposeV.etaleFundamentalGroup.map k (pullback.snd sX sX) c (α x) = 1 := by
    have h := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one k i₁ (pullback.snd sX sX) sX e
      hi₁₂ e fun τ ↦ ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed k k _ τ
    intro x
    have h' := DFunLike.congr_fun h x
    rw [MonoidHom.comp_apply, MonoidHom.one_apply] at h'
    exact h'
  have hβ : ∀ x, ExposeV.etaleFundamentalGroup.map k (pullback.fst sX sX) c (β x) = 1 := by
    have h := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one k i₂ (pullback.fst sX sX) sX e
      hi₂₁ e fun τ ↦ ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed k k _ τ
    intro x
    have h' := DFunLike.congr_fun h x
    rw [MonoidHom.comp_apply, MonoidHom.one_apply] at h'
    simp only [β]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_fundamentalGroupCongr, h', map_one]
  -- By X.1.7, the images of `α` and `β` commute.
  have hcomm : ∀ x y, α x * β y = β y * α x := by
    intro x y
    apply hΦ.1
    simp only [map_mul, MonoidHom.prod_apply, Prod.mk_mul_mk]
    rw [hα, hβ, mul_one, one_mul, one_mul, mul_one]
  -- The multiplication maps both images isomorphically onto `π₁(X, c ≫ m)`.
  exact mul_comm_of_commute_of_injective_of_surjective α β
    (ExposeV.etaleFundamentalGroup.map k m c) hcomm
    (bijective_map_comp_map_of_comp_eq_id i₁ m hm₁ e).1
    (bijective_map_comp_congr_comp_map i₂ m hm₂ e h₂₁).2 a b

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- XI.2: the fundamental group of a monoid scheme `A` (in particular of a group scheme) which is
proper, connected and reduced over an algebraically closed field `k` is commutative; the base
point is the unit section. This applies to abelian varieties. -/
theorem mul_comm_of_monObj (A : Over (Spec (.of k))) [MonObj A] [IsProper A.hom]
    [IsReduced A.left] [ConnectedSpace A.left]
    (a b : ExposeV.etaleFundamentalGroup k (η[A].left : Spec (.of k) ⟶ A.left)) :
    a * b = b * a := by
  have he : (η[A].left : Spec (.of k) ⟶ A.left) ≫ A.hom = 𝟙 _ := Over.w η[A]
  refine mul_comm_of_hSpace A.hom η[A].left he μ[A].left ?_ ?_ a b
  · have h := congrArg CommaMorphism.left (lift_comp_one_right (𝟙 A) (toUnit A))
    simp only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] at h
    exact h
  · have h := congrArg CommaMorphism.left (lift_comp_one_left (toUnit A) (𝟙 A))
    simp only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] at h
    exact h

end SGA.SGA1.ExposeXI
