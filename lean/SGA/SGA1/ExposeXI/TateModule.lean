/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import SGA.SGA1.ExposeV.FundamentalGroupCovering
import SGA.SGA1.ExposeX.CoveringOfBase
import SGA.SGA1.ExposeXI.AbelianVariety
import SGA.SGA1.ExposeXI.SerreLang

/-!
# SGA 1, Exposé XI.2.1: the fundamental group of an abelian variety is its Tate module

XI.2.1 (Serre–Lang): for an abelian variety `A` over an algebraically closed field `k`, `π₁(A)`
is canonically isomorphic to `T(A) = lim_n K_n`, where `K_n` is the group of `k`-points of the
kernel of `n_A` and `K_{ns} → K_n` is multiplication by `s`
(`AbelianVarietyFundamentalGroupStatement`).

The isomorphism is pinned down as follows. By Serre–Lang (`serreLangStatement`), for every étale
covering `Y ⟶ A` and every point `y` of its fibre at the origin there are `n > 0` and a lift
`g : A ⟶ Y` of `n_A` with `g(0) = y` (`exists_mulNLifts`); it is unique
(`eq_of_comp_eq_of_unitSection`). For `x ∈ T(A)`, the automorphism of the fibre functor
corresponding to `x` maps `y` to `g(x_n)`.

What is formalized here:

* `T(A)` acts on the fibres of the étale coverings of `A` at the origin by `g(0) ↦ g(x_n)`, and
  naturally (`PreGaloisCategory.IsNaturalSMul`); this gives the canonical continuous homomorphism
  `T(A) → π₁(A, 0)` in every characteristic (`tateModuleToFundamentalGroup`, mathlib's
  `PreGaloisCategory.toAut`), the only map with the property above
  (`tateModuleToFundamentalGroup_unique`). It rests on the pointed lifting criterion
  `exists_lift_of_forall_smul_eq_of_apply` (in `SerreLang`), with its converse
  `pointedMap_smul_eq_of_lift` (here), both read off V.6.4 on the terminal covering
  (`ExposeX.exists_section_iff_forall_smul_eq`), and on Serre–Lang in its pointed form
  (`exists_mulNLifts`);
* the criterion (`exists_tateModule_equiv_of_isPretransitive`): the canonical map is an
  isomorphism of topological groups as soon as `T(A)` is compact, acts transitively on the fibres
  of connected coverings and faithfully on the fibres of all coverings (mathlib's
  `PreGaloisCategory.IsFundamentalGroup`). Sufficient conditions: every `K_n` finite
  (`compactSpace_tateModule`); `K_n` finite, `A(k)` divisible and every lift of `n_A` through a
  connected covering onto the fibre (`isPretransitive_tateModule`); for every `n`, a lift of `n_A`
  through some covering which is injective on `K_n` (`eq_one_of_forall_smul_eq`).

The geometric input for these conditions is in `AbelianVarietyIsogeny` (from `n_A` finite and
surjective), `AbelianVarietyMulN` (`n_A` étale for `n` invertible, hence XI.2.1 in
characteristic `0`: `exists_tateModule_equiv_of_charZero`) and `AbelianVarietyQuotient` (the
étale covering `A / K_n` descended along the radicial `A / K_n ⟶ A`, hence XI.2.1 from SGA's
cited fact that `n_A` is an isogeny: `abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`; in
characteristic `p > 0` only `p_A` needs to be an isogeny: `exists_tateModule_equiv_of_charP`).

SGA's consequence that the `ℓ`-primary component of `π₁(A)` is `T_ℓ(A)` is stated in
`TateModulePrimary` (`AbelianVarietyPrimaryComponentStatement`) and proved for `ℓ` invertible in
`k` in `TateModulePrimeToP`. SGA's `T(A) = ∏_ℓ T_ℓ(A)` and the equivalence of the two parts of
XI.2.1 are in `TateModuleProduct`, the functoriality in `A` (SGA's remark after XI.2.1) in
`TateModuleFunctoriality`.

Missing: in characteristic `p > 0`, the `p`-primary clause, which by `TateModuleProduct` is
equivalent to the first part. It follows from `p_A` being an isogeny (`MulNIsogenyStatement` for
`n = p`, from the theorem of the cube and an ample line bundle; SGA only recalls it).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace SGA.SGA1.ExposeXI

section PointedLifting

variable {Ω : Type u} [Field Ω] {S T : Scheme.{u}}

/-- The point of the fibre of `X` at `s̄` given by a geometric point `p` of `X` over `s̄`. It is
irreducible: unfolding it makes the kernel unfold the fibre functor. -/
noncomputable irreducible_def fiberMk {s : Spec (.of Ω) ⟶ S} (X : ExposeV.FEt S)
    (p : Spec (.of Ω) ⟶ X.left) (hp : p ≫ X.hom = s) : (ExposeV.FEt.fiber Ω s).obj X :=
  ((ExposeV.FEt.fiberInclIso Ω s).app X).toEquiv.symm (Over.homMk p hp)

@[simp]
lemma fiberPoint_fiberMk {s : Spec (.of Ω) ⟶ S} (X : ExposeV.FEt S) (p : Spec (.of Ω) ⟶ X.left)
    (hp : p ≫ X.hom = s) : ExposeV.FEt.fiberPoint Ω (fiberMk X p hp) = p := by
  rw [fiberMk_def]
  exact ExposeV.pointOfIso_toEquiv_symm _ _

variable [IsSepClosed Ω]

/-- The converse of `exists_lift_of_forall_smul_eq_of_apply` (in `SerreLang`): if `u : T ⟶ S`
lifts through an étale covering `Y` by some `g` with `g(t̄) = y`, then the image of `π₁(T, t̄)`
fixes `y`. The section `(g, 𝟙) : T ⟶ u^* Y` is a morphism from the terminal covering, so V.6.4
applies (`ExposeX.smul_eq_of_mem_range_section`). -/
lemma pointedMap_smul_eq_of_lift [ConnectedSpace T] (u : T ⟶ S) (t : Spec (.of Ω) ⟶ T)
    (s : Spec (.of Ω) ⟶ S) (h : t ≫ u = s) (Y : ExposeV.FEt S)
    (y : (ExposeV.FEt.fiber Ω s).obj Y) (g : T ⟶ Y.left) (hg : g ≫ Y.hom = u)
    (hg0 : t ≫ g = ExposeV.FEt.fiberPoint Ω y) (τ : ExposeV.etaleFundamentalGroup Ω t) :
    pointedMap Ω u t s h τ • y = y := by
  let E := ExposeV.FEt.pullbackFiberIso Ω u t ≪≫ ExposeV.FEt.fiberCongr Ω h
  have hEz : E.hom.app Y (E.inv.app Y y) = y := FintypeCat.inv_hom_id_apply (E.app Y) y
  have hfib : ExposeV.FEt.fiberPoint Ω y =
      ExposeV.FEt.fiberPoint Ω (E.inv.app Y y) ≫ ExposeV.FEt.proj u Y := by
    conv_lhs => rw [← hEz]
    change ExposeV.FEt.fiberPoint Ω ((ExposeV.FEt.fiberCongr Ω h).hom.app Y
      ((ExposeV.FEt.pullbackFiberIso Ω u t).hom.app Y _)) = _
    rw [ExposeV.FEt.fiberPoint_fiberCongr, ExposeV.FEt.fiberPoint_pullbackFiberIso]
  -- the section `(g, 𝟙)`, as a morphism from the terminal covering
  have := isIso_terminal_hom T
  let c : (⊤_ ExposeV.FEt T).left ⟶ T := (⊤_ ExposeV.FEt T).hom
  let q' : Y.left ⟶ S := Y.hom
  let sec : (⊤_ ExposeV.FEt T).left ⟶ ((ExposeV.FEt.pullback u).obj Y).left :=
    pullback.lift (f := q') (c ≫ g) c (by rw [Category.assoc, hg])
  let q : ⊤_ ExposeV.FEt T ⟶ (ExposeV.FEt.pullback u).obj Y :=
    MorphismProperty.Over.homMk sec (pullback.lift_snd _ _ _)
  let pt : (ExposeV.FEt.fiber Ω t).obj (⊤_ ExposeV.FEt T) :=
    fiberMk _ (t ≫ inv c) (by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
  have hsec : sec ≫ ExposeV.FEt.proj u Y = c ≫ g := pullback.lift_fst _ _ _
  have hq : (ExposeV.FEt.fiber Ω t).map q pt = E.inv.app Y y := by
    apply ExposeV.FEt.fiber_ext_pullback Ω u
    rw [ExposeV.FEt.fiberPoint_map, fiberPoint_fiberMk, ← hfib, Category.assoc, Category.assoc]
    change t ≫ inv c ≫ sec ≫ ExposeV.FEt.proj u Y = _
    rw [hsec, IsIso.inv_hom_id_assoc, hg0]
  have hfix : τ • E.inv.app Y y = E.inv.app Y y :=
    ExposeX.smul_eq_of_mem_range_section _ q ⟨pt, hq⟩ τ
  change E.hom.app Y (τ • E.inv.app Y y) = y
  rw [hfix, hEz]

end PointedLifting

section Canonical

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- The unit section (origin) `0 : Spec k ⟶ A` of a monoid scheme over `k`. -/
noncomputable abbrev unitSection [MonObj A] : Spec (.of k) ⟶ A.left := η[A].left

/-- The `k`-point `Spec k ⟶ A` underlying a point `x : 𝟙 ⟶ A` of `A` over `k`. -/
noncomputable abbrev pointLeft (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) : Spec (.of k) ⟶ A.left :=
  x.left

/-- The fibre functor of the étale coverings of `A` at the origin. -/
noncomputable abbrev originFiber [MonObj A] : ExposeV.FEt A.left ⥤ FintypeCat.{u} :=
  ExposeV.FEt.fiber k (unitSection A)

section Monoid

variable [MonObj A]

lemma pointLeft_one : pointLeft A (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = unitSection A := by
  rw [← MonObj.one_eq_one]

lemma pointLeft_comp_mulN (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) (n : ℕ) :
    pointLeft A x ≫ (mulN A n).left = pointLeft A (x ^ n) := by
  have h : x ≫ mulN A n = x ^ n := by rw [mulN, MonObj.comp_pow, Category.comp_id]
  exact congrArg CommaMorphism.left h

lemma mulN_comp_mulN (m n : ℕ) : mulN A m ≫ mulN A n = mulN A (m * n) := by
  rw [mulN, mulN, mulN, MonObj.comp_pow, Category.comp_id, pow_mul]

lemma mulN_left_comp_mulN_left (m n : ℕ) :
    (mulN A m).left ≫ (mulN A n).left = (mulN A (m * n)).left :=
  congrArg CommaMorphism.left (mulN_comp_mulN A m n)

/-- `n_A` lifts through the étale covering `Y` at every point of its fibre at the origin: for
every such `y` there is `g : A ⟶ Y` over `n_A` with `g(0) = y`. -/
def MulNLifts (Y : ExposeV.FEt A.left) (n : ℕ) : Prop :=
  ∀ y : (originFiber A).obj Y, ∃ g : A.left ⟶ Y.left,
    g ≫ Y.hom = (mulN A n).left ∧ unitSection A ≫ g = ExposeV.FEt.fiberPoint k y

variable {A}

lemma MulNLifts.mul_left {Y : ExposeV.FEt A.left} {n : ℕ} (h : MulNLifts A Y n) (m : ℕ) :
    MulNLifts A Y (m * n) := fun y ↦ by
  obtain ⟨g, hg, hg0⟩ := h y
  refine ⟨(mulN A m).left ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg, mulN_left_comp_mulN_left]
  · rw [← Category.assoc, unit_comp_mulN_left, hg0]

variable (A)

/-- A lift of `n_A` through an étale covering is determined by its value at the origin. -/
theorem eq_of_comp_eq_of_unitSection [ConnectedSpace A.left] {Y : ExposeV.FEt A.left}
    {g₁ g₂ : A.left ⟶ Y.left} (h : g₁ ≫ Y.hom = g₂ ≫ Y.hom)
    (h0 : unitSection A ≫ g₁ = unitSection A ≫ g₂) : g₁ = g₂ :=
  ExposeX.eq_of_comp_eq_of_connectedSpace Y.hom h (unitSection A) h0

variable [IsAlgClosed k] [IsProper A.hom] [IsReduced A.left] [ConnectedSpace A.left]

/-- XI.2.1, Serre–Lang in pointed form (the pointed version of `serreLangStatement`, which it
implies): for every étale covering `Y` of `A` there is `n > 0` such that `n_A` lifts through `Y`
at every point of the fibre at the origin. Like `serreLangStatement`, it is a few lines from the
key computation of `SerreLang`, that `n_A` acts on `π₁(A, 0)` by `σ ↦ σⁿ` (`pointedMap_mulN`);
here `n` is the order of the permutation group of the fibre, so that `Y` need not be
connected. -/
theorem exists_mulNLifts (Y : ExposeV.FEt A.left) : ∃ n : ℕ, 0 < n ∧ MulNLifts A Y n := by
  let F := originFiber A
  let N := Nat.card (Equiv.Perm (F.obj Y))
  refine ⟨N, Nat.card_pos, fun y ↦ ?_⟩
  have h := unit_comp_mulN_left A N
  refine exists_lift_of_forall_smul_eq_of_apply (mulN A N).left _ _ h Y y fun σ ↦ ?_
  rw [pointedMap_mulN A N h σ]
  have h1 : MulAction.toPermHom (Aut F) (F.obj Y) (σ ^ N) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  exact congrArg (fun p : Equiv.Perm (F.obj Y) ↦ p y) h1

variable {A}

/-- A choice of `n > 0` such that `n_A` lifts through `Y` (Serre–Lang). -/
noncomputable def liftDegree (Y : ExposeV.FEt A.left) : ℕ+ :=
  ⟨(exists_mulNLifts A Y).choose, (exists_mulNLifts A Y).choose_spec.1⟩

lemma mulNLifts_liftDegree (Y : ExposeV.FEt A.left) : MulNLifts A Y (liftDegree Y) :=
  (exists_mulNLifts A Y).choose_spec.2

end Monoid

section Torsion

variable [GrpObj A]

/-- Right translation by `x` on points with values in any `S`: `y ↦ y · x`. -/
lemma comp_mulRight_hom {S : Over (Spec (.of k))} (y : S ⟶ A)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    y ≫ (GrpObj.mulRight x).hom = y * (toUnit S ≫ x) := by
  rw [GrpObj.mulRight_hom, ← Hom.mul_def, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    comp_toUnit]

/-- Right translation by `x` maps the point `y` to `y * x`. -/
lemma pointLeft_comp_mulRight (x y : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    pointLeft A y ≫ (GrpObj.mulRight x).hom.left = pointLeft A (y * x) := by
  have h : y ≫ (GrpObj.mulRight x).hom = y * x := by
    rw [comp_mulRight_hom, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  exact congrArg CommaMorphism.left h

variable [IsCommMonObj A]

/-- Translations commute with multiplication by `n` up to the translation by `xⁿ`:
`τ_x ≫ n_A = n_A ≫ τ_{xⁿ}`. -/
lemma mulRight_hom_comp_mulN (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) (n : ℕ) :
    (GrpObj.mulRight x).hom ≫ mulN A n = mulN A n ≫ (GrpObj.mulRight (x ^ n)).hom := by
  rw [mulN, MonObj.comp_pow, Category.comp_id, GrpObj.mulRight_hom, GrpObj.mulRight_hom,
    ← Hom.mul_def, ← Hom.mul_def, mul_pow, ← MonObj.comp_pow, MonObj.comp_mul, Category.comp_id,
    ← Category.assoc, comp_toUnit]

/-- Right translation by a point `x` commutes with `n_A` when `xⁿ = 1`. -/
lemma mulRight_hom_comp_mulN_of_pow_eq_one {n : ℕ} (x : 𝟙_ (Over (Spec (.of k))) ⟶ A)
    (hx : x ^ n = 1) : (GrpObj.mulRight x).hom ≫ mulN A n = mulN A n := by
  rw [mulRight_hom_comp_mulN, hx, GrpObj.mulRight_hom, MonObj.comp_one, ← Hom.mul_def,
    _root_.mul_one, Category.comp_id]

variable {A} [ConnectedSpace A.left]

/-- The action of an `n`-torsion point `x` on the fibre of `Y` at the origin, when `n_A` lifts
through `Y`: `y ↦ g_y(x)`, where `g_y : A ⟶ Y` lifts `n_A` and `g_y(0) = y`. -/
noncomputable def torsionAct {Y : ExposeV.FEt A.left} {n : ℕ} (hn : MulNLifts A Y n)
    (x : torsionPoints A n) (y : (originFiber A).obj Y) : (originFiber A).obj Y :=
  fiberMk Y (pointLeft A x ≫ (hn y).choose) (by
    rw [Category.assoc, (hn y).choose_spec.1, pointLeft_comp_mulN,
      (mem_torsionPoints A).mp x.2, pointLeft_one])

/-- The action of `x` on `y` is `g(x)` for any lift `g` of `n_A` with `g(0) = y`. -/
lemma fiberPoint_torsionAct {Y : ExposeV.FEt A.left} {n : ℕ} (hn : MulNLifts A Y n)
    (x : torsionPoints A n) (y : (originFiber A).obj Y) {g : A.left ⟶ Y.left}
    (hg : g ≫ Y.hom = (mulN A n).left) (hg0 : unitSection A ≫ g = ExposeV.FEt.fiberPoint k y) :
    ExposeV.FEt.fiberPoint k (torsionAct hn x y) = pointLeft A x ≫ g := by
  rw [torsionAct, fiberPoint_fiberMk,
    eq_of_comp_eq_of_unitSection A ((hn y).choose_spec.1.trans hg.symm)
      ((hn y).choose_spec.2.trans hg0.symm)]

lemma torsionAct_one {Y : ExposeV.FEt A.left} {n : ℕ} (hn : MulNLifts A Y n)
    (y : (originFiber A).obj Y) : torsionAct hn 1 y = y := by
  obtain ⟨g, hg, hg0⟩ := hn y
  apply ExposeV.FEt.fiber_ext_point
  rw [fiberPoint_torsionAct hn 1 y hg hg0, OneMemClass.coe_one, pointLeft_one, hg0]

lemma torsionAct_mul {Y : ExposeV.FEt A.left} {n : ℕ} (hn : MulNLifts A Y n)
    (x x' : torsionPoints A n) (y : (originFiber A).obj Y) :
    torsionAct hn (x * x') y = torsionAct hn x (torsionAct hn x' y) := by
  obtain ⟨g, hg, hg0⟩ := hn y
  let τ := (GrpObj.mulRight (x' : 𝟙_ (Over (Spec (.of k))) ⟶ A)).hom
  have hτ : τ ≫ mulN A n = mulN A n :=
    mulRight_hom_comp_mulN_of_pow_eq_one A _ ((mem_torsionPoints A).mp x'.2)
  have hg' : (τ.left ≫ g) ≫ Y.hom = (mulN A n).left := by
    rw [Category.assoc, hg]
    exact congrArg CommaMorphism.left hτ
  have hg0' : unitSection A ≫ τ.left ≫ g = ExposeV.FEt.fiberPoint k (torsionAct hn x' y) := by
    rw [fiberPoint_torsionAct hn x' y hg hg0, ← Category.assoc, ← pointLeft_one,
      pointLeft_comp_mulRight, _root_.one_mul]
  apply ExposeV.FEt.fiber_ext_point
  rw [fiberPoint_torsionAct hn x _ hg' hg0', fiberPoint_torsionAct hn _ y hg hg0,
    ← Category.assoc, pointLeft_comp_mulRight, Subgroup.coe_mul]

/-- For `x ∈ T(A)`, the action of `x_n` on `y` is `g(x_m)` for any lift `g` of any `m_A` with
`g(0) = y`. -/
lemma fiberPoint_torsionAct_tateModule (x : tateModule A) {Y : ExposeV.FEt A.left} {n : ℕ+}
    (hn : MulNLifts A Y n) (y : (originFiber A).obj Y) (m : ℕ+)
    {g : A.left ⟶ Y.left} (hg : g ≫ Y.hom = (mulN A m).left)
    (hg0 : unitSection A ≫ g = ExposeV.FEt.fiberPoint k y) :
    ExposeV.FEt.fiberPoint k (torsionAct hn (x.1 n) y) = pointLeft A (x.1 m) ≫ g := by
  obtain ⟨gn, hgn, hgn0⟩ := hn y
  rw [fiberPoint_torsionAct hn _ y hgn hgn0]
  -- `m_A ≫ gₙ` and `n_A ≫ g` both lift `(mn)_A` and map `0` to `y`.
  have h : (mulN A m).left ≫ gn = (mulN A n).left ≫ g := by
    refine eq_of_comp_eq_of_unitSection A ?_ ?_
    · rw [Category.assoc, Category.assoc, hgn, hg, mulN_left_comp_mulN_left,
        mulN_left_comp_mulN_left, Nat.mul_comm]
    · rw [← Category.assoc, ← Category.assoc, unit_comp_mulN_left, unit_comp_mulN_left, hgn0,
        hg0]
  have hxn : pointLeft A (x.1 n) = pointLeft A (x.1 (n * m)) ≫ (mulN A m).left := by
    rw [pointLeft_comp_mulN, pow_tateModule]
  have hxm : pointLeft A (x.1 m) = pointLeft A (x.1 (n * m)) ≫ (mulN A n).left := by
    rw [pointLeft_comp_mulN, mul_comm n m, pow_tateModule]
  rw [hxn, hxm, Category.assoc, Category.assoc, h]

end Torsion

section TateModule

variable {A} [GrpObj A] [IsCommMonObj A] [IsAlgClosed k] [IsProper A.hom] [IsReduced A.left]
  [ConnectedSpace A.left]

/-- `T(A)` acts on the fibre at the origin of every étale covering `Y`: `x` maps `g(0)` to
`g(x_n)` for every lift `g` of `n_A` through `Y` (`fiberPoint_tateModule_smul`). -/
noncomputable instance (Y : ExposeV.FEt A.left) : MulAction (tateModule A) ((originFiber A).obj Y)
    where
  smul x y := torsionAct (mulNLifts_liftDegree Y) (x.1 (liftDegree Y)) y
  one_smul y := torsionAct_one (mulNLifts_liftDegree Y) y
  mul_smul _ _ y := torsionAct_mul (mulNLifts_liftDegree Y) _ _ y

/-- The action of `x ∈ T(A)` on the fibre of `Y`: `y ↦ g(x_n)` for any lift `g` of `n_A`
through `Y` with `g(0) = y`. -/
lemma fiberPoint_tateModule_smul (x : tateModule A) {Y : ExposeV.FEt A.left}
    (y : (originFiber A).obj Y) (n : ℕ+) {g : A.left ⟶ Y.left}
    (hg : g ≫ Y.hom = (mulN A n).left) (hg0 : unitSection A ≫ g = ExposeV.FEt.fiberPoint k y) :
    ExposeV.FEt.fiberPoint k (x • y) = pointLeft A (x.1 n) ≫ g :=
  fiberPoint_torsionAct_tateModule x _ y n hg hg0

instance : IsNaturalSMul (originFiber A) (tateModule A) where
  naturality x {Y Y'} φ y := by
    apply ExposeV.FEt.fiber_ext_point
    obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
    have hg' : (g ≫ φ.left) ≫ Y'.hom = (mulN A (liftDegree Y)).left := by
      rw [Category.assoc, MorphismProperty.Over.w φ, hg]
    have hg0' : unitSection A ≫ g ≫ φ.left =
        ExposeV.FEt.fiberPoint k ((originFiber A).map φ y) := by
      rw [ExposeV.FEt.fiberPoint_map, ← Category.assoc, hg0]
    rw [fiberPoint_tateModule_smul x _ _ hg' hg0', ExposeV.FEt.fiberPoint_map,
      fiberPoint_tateModule_smul x _ _ hg hg0, Category.assoc]

/-- The action of `T(A)` on each fibre factors through the discrete group `K_n`, so it is
continuous. -/
instance (Y : ExposeV.FEt A.left) : ContinuousSMul (tateModule A) ((originFiber A).obj Y) := by
  refine ⟨?_⟩
  let f : torsionPoints A (liftDegree Y) × (originFiber A).obj Y → (originFiber A).obj Y :=
    fun p ↦ torsionAct (mulNLifts_liftDegree Y) p.1 p.2
  change Continuous (f ∘ Prod.map (fun x : tateModule A ↦ x.1 (liftDegree Y)) id)
  exact continuous_of_discreteTopology.comp
    ((((continuous_apply _).comp continuous_subtype_val)).prodMap continuous_id)

variable (A)

/-- XI.2.1: the canonical homomorphism `T(A) → π₁(A, 0)`, in every characteristic: `x ∈ T(A)`
acts on the fibre at the origin of an étale covering `Y` by `g(0) ↦ g(x_n)`, for every lift `g`
of `n_A` through `Y` (`fiberPoint_tateModuleToFundamentalGroup_smul`). It is mathlib's
`PreGaloisCategory.toAut` for this action. -/
noncomputable def tateModuleToFundamentalGroup :
    tateModule A →* ExposeV.etaleFundamentalGroup k (unitSection A) :=
  toAut (originFiber A) (tateModule A)

variable {A}

lemma tateModuleToFundamentalGroup_smul (x : tateModule A) {Y : ExposeV.FEt A.left}
    (y : (originFiber A).obj Y) : tateModuleToFundamentalGroup A x • y = x • y :=
  toAut_hom_app_apply _ x y

/-- XI.2.1: the canonical map `T(A) → π₁(A, 0)` sends `x` to the automorphism of the fibre
functor which maps `g(0)` to `g(x_n)`, for every lift `g : A ⟶ Y` of `n_A` through an étale
covering `Y`. -/
theorem fiberPoint_tateModuleToFundamentalGroup_smul (x : tateModule A)
    {Y : ExposeV.FEt A.left} (y : (originFiber A).obj Y) (n : ℕ+)
    {g : A.left ⟶ Y.left} (hg : g ≫ Y.hom = (mulN A n).left)
    (hg0 : unitSection A ≫ g = ExposeV.FEt.fiberPoint k y) :
    ExposeV.FEt.fiberPoint k (tateModuleToFundamentalGroup A x • y) =
      pointLeft A (x.1 n) ≫ g := by
  rw [tateModuleToFundamentalGroup_smul]
  exact fiberPoint_tateModule_smul x y n hg hg0

variable (A)

/-- The canonical map `T(A) → π₁(A, 0)` is continuous. -/
theorem continuous_tateModuleToFundamentalGroup :
    Continuous (tateModuleToFundamentalGroup A) :=
  toAut_continuous (originFiber A) (tateModule A)

/-- The canonical map `T(A) → π₁(A, 0)` is the only map with the property of
`fiberPoint_tateModuleToFundamentalGroup_smul`. -/
theorem tateModuleToFundamentalGroup_unique
    (φ : tateModule A → ExposeV.etaleFundamentalGroup k (unitSection A))
    (hφ : ∀ (Y : ExposeV.FEt A.left) (n : ℕ+) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A n).left → ∀ (y : (originFiber A).obj Y),
      ExposeV.FEt.fiberPoint k y = unitSection A ≫ g →
      ∀ x : tateModule A, ExposeV.FEt.fiberPoint k (φ x • y) = pointLeft A (x.1 n) ≫ g) :
    φ = tateModuleToFundamentalGroup A := by
  funext x
  ext Y y
  obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
  apply ExposeV.FEt.fiber_ext_point
  exact (hφ Y _ g hg y hg0.symm x).trans
    (fiberPoint_tateModuleToFundamentalGroup_smul x y _ hg hg0).symm

end TateModule

end Canonical

section Statements

/-- The conclusion of XI.2.1 for a commutative group scheme `A` over `k`: there is an isomorphism
of topological groups `φ : T(A) ≃ π₁(A, 0)` such that, for every étale covering `Y ⟶ A`, every
`n > 0`, every lift `g : A ⟶ Y` of `n_A` and every `x ∈ T(A)`, `φ x` maps the point `g(0)` of the
fibre of `Y` at `0` to `g(x_n)`. -/
def AbelianVarietyFundamentalGroupConclusion (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsCommMonObj A] : Prop :=
  ∃ φ : tateModule A ≃ₜ* ExposeV.etaleFundamentalGroup k (unitSection A),
    ∀ (Y : ExposeV.FEt A.left) (n : ℕ+) (g : A.left ⟶ Y.left), g ≫ Y.hom = (mulN A n).left →
      ∀ (y : (ExposeV.FEt.fiber k (unitSection A)).obj Y),
        ExposeV.FEt.fiberPoint k y = unitSection A ≫ g →
        ∀ x : tateModule A, ExposeV.FEt.fiberPoint k (φ x • y) = pointLeft A (x.1 n) ≫ g

/-- XI.2.1 (Serre–Lang): let `A` be an abelian variety over an algebraically closed field `k`
(a group scheme over `k` which is proper, smooth and connected), `K_n` the group of `k`-points of
the kernel of multiplication by `n` (`torsionPoints`), and `T(A) = lim_n K_n` (`tateModule`; for
`m = ns`, `K_m → K_n` is multiplication by `s`). Then `π₁(A)` (at the origin) is canonically
isomorphic to `T(A)`.

The isomorphism `φ : T(A) ≃ π₁(A, 0)` is one of topological groups (each `K_n` discrete), and
"canonically" is made precise by the property that pins it down
(`AbelianVarietyFundamentalGroupConclusion`, `tateModuleToFundamentalGroup_unique`): for every
étale covering `Y ⟶ A`, every `n > 0`, every lift `g : A ⟶ Y` of `n_A` and every `x ∈ T(A)`,
`φ x` maps the point `g(0)` of the fibre of `Y` at `0` to `g(x_n)`. SGA's consequence that the
`ℓ`-primary component of `π₁(A)` is `T_ℓ(A)` is `AbelianVarietyPrimaryComponentStatement`
(`TateModulePrimary`), which follows from this one.

Proved in characteristic `0` as `exists_tateModule_equiv_of_charZero` (`AbelianVarietyMulN`). In
every characteristic it follows from SGA's cited fact that `n_A` is an isogeny
(`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`, `AbelianVarietyQuotient`). In
characteristic `p > 0` it holds for `A` as soon as `p_A` is an isogeny
(`exists_tateModule_equiv_of_charP`), and it is equivalent to the `p`-primary clause for `A`
(`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`, `TateModuleProduct`): the
`ℓ`-primary clauses for `ℓ ≠ p` are proved (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`,
`TateModulePrimeToP`). Open: that `p`-primary clause, or `p_A` an isogeny. -/
def AbelianVarietyFundamentalGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left],
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyFundamentalGroupConclusion k A

/-- A standard fact used in XI.2 (Mumford, *Abelian varieties*, §4, Application 2): for an
abelian variety `A` over an algebraically closed field `k` and an integer `n` invertible in `k`,
multiplication by `n` is étale. Proved as `mulNEtaleStatement` (in `AbelianVarietyMulN`). -/
def MulNEtaleStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] (n : ℕ), (n : k) ≠ 0 →
    Etale (mulN A n).left

/-- XI.2 (statement only; recalled by SGA, Mumford, *Abelian varieties*, §4, Application 2 and
§6, Application 2): for an abelian variety `A` over an algebraically closed field `k` and an
integer `n > 0`, multiplication by `n` is an isogeny: surjective with finite kernel, i.e. (`A`
being proper) finite and surjective. Its proof needs the theorem of the cube and an ample line
bundle on `A`. The case `n` invertible in `k` is `mulNIsogeny_of_ne_zero` (`AbelianVarietyMulN`),
so only `p_A` in characteristic `p > 0` is open. It implies XI.2.1
(`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`). -/
def MulNIsogenyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] (n : ℕ), 0 < n →
    IsFinite (mulN A n).left ∧ Surjective (mulN A n).left

end Statements

section Criterion

/-! ### When the canonical map is an isomorphism -/

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  [IsAlgClosed k] [IsProper A.hom] [IsReduced A.left] [ConnectedSpace A.left]

variable (A) in
/-- XI.2.1, the formal part: the canonical map `T(A) → π₁(A, 0)` is an isomorphism of topological
groups as soon as `T(A)` is compact, acts transitively on the fibres of the connected étale
coverings and faithfully on the fibres of all étale coverings (`T(A)` is then a fundamental group
of the Galois category `FEt A` in mathlib's sense, `PreGaloisCategory.IsFundamentalGroup`). -/
theorem exists_tateModule_equiv_of_isPretransitive [CompactSpace (tateModule A)]
    (htrans : ∀ (Y : ExposeV.FEt A.left) [IsConnected Y],
      MulAction.IsPretransitive (tateModule A) ((originFiber A).obj Y))
    (hfaith : ∀ x : tateModule A, (∀ (Y : ExposeV.FEt A.left) (y : (originFiber A).obj Y),
      x • y = y) → x = 1) :
    AbelianVarietyFundamentalGroupConclusion k A := by
  have : IsFundamentalGroup (originFiber A) (tateModule A) :=
    { transitive_of_isGalois := fun Y _ ↦ htrans Y
      continuous_smul := fun _ ↦ inferInstance
      non_trivial' := hfaith }
  refine ⟨ContinuousMulEquiv.mk' (toAutHomeo (originFiber A) (tateModule A))
    fun x y ↦ map_mul (tateModuleToFundamentalGroup A) x y, fun Y n g hg y hy x ↦ ?_⟩
  exact fiberPoint_tateModuleToFundamentalGroup_smul x y n hg hy.symm

/-- Transitivity of the action of `T(A)` on the fibre of a connected covering `Y`, from: `K_n`
finite, `A(k)` divisible, and every lift `g : A ⟶ Y` of an `n_A` maps `K_n` onto the fibre. -/
theorem isPretransitive_tateModule (hfin : ∀ n : ℕ+, Finite (torsionPoints A n))
    (hdiv : ∀ n : ℕ, 0 < n → ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A, ∃ b, b ^ n = a)
    (Y : ExposeV.FEt A.left)
    (hsurj : ∀ (n : ℕ+) (g : A.left ⟶ Y.left), g ≫ Y.hom = (mulN A n).left →
      ∀ y : (originFiber A).obj Y, ∃ a : torsionPoints A n,
        ExposeV.FEt.fiberPoint k y = pointLeft A a ≫ g) :
    MulAction.IsPretransitive (tateModule A) ((originFiber A).obj Y) := by
  refine ⟨fun y y' ↦ ?_⟩
  obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
  obtain ⟨a, ha⟩ := hsurj _ g hg y'
  obtain ⟨x, hx⟩ := exists_tateModule_apply_eq hfin hdiv _ a
  refine ⟨x, ExposeV.FEt.fiber_ext_point k ?_⟩
  rw [fiberPoint_tateModule_smul x y _ hg hg0, hx, ha]

/-- Faithfulness of the action of `T(A)`, from: for every `n > 0` some lift of `n_A` through an
étale covering is injective on `K_n`. -/
theorem eq_one_of_forall_smul_eq
    (hsep : ∀ n : ℕ+, ∃ (Y : ExposeV.FEt A.left) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A n).left ∧ ∀ a b : torsionPoints A n,
        pointLeft A a ≫ g = pointLeft A b ≫ g → a = b)
    (x : tateModule A)
    (hx : ∀ (Y : ExposeV.FEt A.left) (y : (originFiber A).obj Y), x • y = y) : x = 1 := by
  refine Subtype.ext (funext fun n ↦ ?_)
  obtain ⟨Y, g, hg, hinj⟩ := hsep n
  have hy : (unitSection A ≫ g) ≫ Y.hom = unitSection A := by
    rw [Category.assoc, hg, unit_comp_mulN_left]
  let y := fiberMk Y (unitSection A ≫ g) hy
  have h := fiberPoint_tateModule_smul x y n hg (fiberPoint_fiberMk _ _ _).symm
  rw [hx, fiberPoint_fiberMk] at h
  refine hinj _ 1 (h.symm.trans ?_)
  rw [OneMemClass.coe_one, pointLeft_one]

end Criterion

end SGA.SGA1.ExposeXI
