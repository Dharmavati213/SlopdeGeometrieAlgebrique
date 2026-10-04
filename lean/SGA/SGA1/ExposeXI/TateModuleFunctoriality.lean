/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.TateModulePrimary

/-!
# SGA 1, Exposé XI.2.1: the isomorphisms `T(A) ≅ π₁(A)` and `T_ℓ(A) ≅ π₁(A)_ℓ` are functorial

After XI.2.1 SGA notes that "these isomorphisms are functorial for variable `A`", and that
`T_ℓ(A)` is an additive functor in `A`. We prove this for the canonical maps, in every
characteristic:

* `tateModuleMap f : T(G) →* T(H)`, `(x_n) ↦ (f ∘ x_n)`, for a morphism of commutative group
  objects `f : G ⟶ H` (`torsionPointsMap` on each `K_n`). It is an additive functor:
  `tateModuleMap_id`, `tateModuleMap_comp` and `tateModuleMap_mul` (`T(f + g) = T(f) + T(g)`,
  written multiplicatively; `f * g` is a homomorphism by `isMonHom_mul`, `Geometry`). The same
  holds for `tateModuleAtMap f : T_ℓ(G) →* T_ℓ(H)`, which commutes with the section `T_ℓ → T`
  (`tateModuleMap_tateModuleOfAt`);
* `pointedMap_tateModuleToFundamentalGroup`: for a homomorphism `f : A ⟶ B` of commutative group
  schemes as in XI.2.1, `f_* ∘ (T(A) → π₁(A, 0)) = (T(B) → π₁(B, 0)) ∘ T(f)`, where
  `f_* : π₁(A, 0) → π₁(B, 0)` is `pointedMap` (`SerreLang`). A lift `g : B ⟶ Y` of `n_B` through
  an étale covering `Y` pulls back to the lift `(f ≫ g, n_A) : A ⟶ Y ×_B A` of `n_A`. Its
  `ℓ`-primary form is `pointedMap_tateModuleToFundamentalGroup_tateModuleOfAt`.
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace SGA.SGA1.ExposeXI

section Map

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G H : C} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]

/-- A morphism of commutative group objects maps `n`-torsion points to `n`-torsion points. -/
def torsionPointsMap (n : ℕ) : torsionPoints G n →* torsionPoints H n :=
  ((IsMonHom.monoidHom f (𝟙_ C)).comp (torsionPoints G n).subtype).codRestrict _ fun x ↦ by
    rw [mem_torsionPoints, MonoidHom.comp_apply, Subgroup.coe_subtype, IsMonHom.monoidHom_apply,
      ← MonObj.pow_comp, (mem_torsionPoints G).mp x.2, MonObj.one_comp]

lemma coe_torsionPointsMap (n : ℕ) (x : torsionPoints G n) :
    (torsionPointsMap f n x : 𝟙_ C ⟶ H) = (x : 𝟙_ C ⟶ G) ≫ f :=
  rfl

/-- XI.2.1 (remark): the map `T(f) : T(G) → T(H)`, `(x_n) ↦ (f ∘ x_n)`; `T` is an additive
functor (`tateModuleMap_id`, `tateModuleMap_comp`, `tateModuleMap_mul`). -/
def tateModuleMap : tateModule G →* tateModule H :=
  ((MonoidHom.pi fun n : ℕ+ ↦ (torsionPointsMap f n).comp (Pi.evalMonoidHom _ n)).comp
    (tateModule G).subtype).codRestrict _ fun x n s ↦ by
      change ((x.1 (n * s) : 𝟙_ C ⟶ G) ≫ f) ^ (s : ℕ) = (x.1 n : 𝟙_ C ⟶ G) ≫ f
      rw [← MonObj.pow_comp, pow_tateModule]

lemma coe_tateModuleMap_apply (x : tateModule G) (n : ℕ+) :
    ((tateModuleMap f x).1 n : 𝟙_ C ⟶ H) = (x.1 n : 𝟙_ C ⟶ G) ≫ f :=
  rfl

/-- XI.2.1 (remark): the map `T_ℓ(f) : T_ℓ(G) → T_ℓ(H)`, `(y_r) ↦ (f ∘ y_r)`. -/
def tateModuleAtMap (ℓ : ℕ) : tateModuleAt G ℓ →* tateModuleAt H ℓ :=
  ((MonoidHom.pi fun r : ℕ ↦ (torsionPointsMap f (ℓ ^ r)).comp (Pi.evalMonoidHom _ r)).comp
    (tateModuleAt G ℓ).subtype).codRestrict _ fun y r ↦ by
      change ((y.1 (r + 1) : 𝟙_ C ⟶ G) ≫ f) ^ ℓ = (y.1 r : 𝟙_ C ⟶ G) ≫ f
      rw [← MonObj.pow_comp]
      exact congrArg (· ≫ f) (y.2 r)

lemma coe_tateModuleAtMap_apply (ℓ : ℕ) (y : tateModuleAt G ℓ) (r : ℕ) :
    ((tateModuleAtMap f ℓ y).1 r : 𝟙_ C ⟶ H) = (y.1 r : 𝟙_ C ⟶ G) ≫ f :=
  rfl

/-- `T(f)` commutes with the sections `T_ℓ → T` (`tateModuleOfAt`). -/
lemma tateModuleMap_tateModuleOfAt {ℓ : ℕ} (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) :
    tateModuleMap f (tateModuleOfAt hℓ y) = tateModuleOfAt hℓ (tateModuleAtMap f ℓ y) :=
  Subtype.ext (funext fun n ↦ Subtype.ext (by
    change ((y.1 _ : 𝟙_ C ⟶ G) ^ primeToInv ℓ n) ≫ f = ((y.1 _ : 𝟙_ C ⟶ G) ≫ f) ^ primeToInv ℓ n
    exact MonObj.pow_comp _ _ _))

end Map

section Functor

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G H K : C} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj K] [IsCommMonObj K]

lemma tateModuleMap_id : tateModuleMap (𝟙 G) = MonoidHom.id (tateModule G) :=
  MonoidHom.ext fun x ↦ Subtype.ext (funext fun n ↦ Subtype.ext (by
    change (x.1 n : 𝟙_ C ⟶ G) ≫ 𝟙 G = x.1 n
    exact Category.comp_id _))

lemma tateModuleMap_comp (f : G ⟶ H) (g : H ⟶ K) [IsMonHom f] [IsMonHom g] :
    tateModuleMap (f ≫ g) = (tateModuleMap g).comp (tateModuleMap f) :=
  MonoidHom.ext fun x ↦ Subtype.ext (funext fun n ↦ Subtype.ext (by
    change (x.1 n : 𝟙_ C ⟶ G) ≫ f ≫ g = ((x.1 n : 𝟙_ C ⟶ G) ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm))

lemma tateModuleAtMap_id (ℓ : ℕ) : tateModuleAtMap (𝟙 G) ℓ = MonoidHom.id (tateModuleAt G ℓ) :=
  MonoidHom.ext fun y ↦ Subtype.ext (funext fun r ↦ Subtype.ext (by
    change (y.1 r : 𝟙_ C ⟶ G) ≫ 𝟙 G = y.1 r
    exact Category.comp_id _))

lemma tateModuleAtMap_comp (f : G ⟶ H) (g : H ⟶ K) [IsMonHom f] [IsMonHom g] (ℓ : ℕ) :
    tateModuleAtMap (f ≫ g) ℓ = (tateModuleAtMap g ℓ).comp (tateModuleAtMap f ℓ) :=
  MonoidHom.ext fun y ↦ Subtype.ext (funext fun r ↦ Subtype.ext (by
    change (y.1 r : 𝟙_ C ⟶ G) ≫ f ≫ g = ((y.1 r : 𝟙_ C ⟶ G) ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm))

/-- XI.2.1 (remark): `T` is additive, `T(f + g) = T(f) + T(g)` (written multiplicatively). -/
lemma tateModuleMap_mul (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] :
    tateModuleMap (f * g) = tateModuleMap f * tateModuleMap g :=
  MonoidHom.ext fun x ↦ Subtype.ext (funext fun n ↦ Subtype.ext (by
    change (x.1 n : 𝟙_ C ⟶ G) ≫ (f * g) = ((x.1 n : 𝟙_ C ⟶ G) ≫ f) * ((x.1 n : 𝟙_ C ⟶ G) ≫ g)
    exact MonObj.comp_mul _ _ _))

/-- XI.2.1 (remark): `T_ℓ` is additive, `T_ℓ(f + g) = T_ℓ(f) + T_ℓ(g)` (written
multiplicatively). -/
lemma tateModuleAtMap_mul (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] (ℓ : ℕ) :
    tateModuleAtMap (f * g) ℓ = tateModuleAtMap f ℓ * tateModuleAtMap g ℓ :=
  MonoidHom.ext fun y ↦ Subtype.ext (funext fun r ↦ Subtype.ext (by
    change (y.1 r : 𝟙_ C ⟶ G) ≫ (f * g) = ((y.1 r : 𝟙_ C ⟶ G) ≫ f) * ((y.1 r : 𝟙_ C ⟶ G) ≫ g)
    exact MonObj.comp_mul _ _ _))

end Functor

section Naturality

variable {k : Type u} [Field k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]

lemma unitSection_comp_left (f : A ⟶ B) [IsMonHom f] :
    unitSection A ≫ f.left = unitSection B :=
  congrArg CommaMorphism.left (IsMonHom.one_hom f)

/-- A homomorphism commutes with multiplication by `n`. -/
lemma mulN_comp (f : A ⟶ B) [IsMonHom f] (n : ℕ) : mulN A n ≫ f = f ≫ mulN B n := by
  rw [mulN, mulN, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

variable [IsCommMonObj A] [IsCommMonObj B] [IsAlgClosed k] [IsProper A.hom] [IsReduced A.left]
  [ConnectedSpace A.left] [IsProper B.hom] [IsReduced B.left] [ConnectedSpace B.left]

/-- XI.2.1 (remark, functoriality): for a homomorphism `f : A ⟶ B`, the canonical maps
`T(A) → π₁(A, 0)` and `T(B) → π₁(B, 0)` commute with `T(f)` and `f_* : π₁(A, 0) → π₁(B, 0)`. -/
theorem pointedMap_tateModuleToFundamentalGroup (f : A ⟶ B) [IsMonHom f] (x : tateModule A) :
    pointedMap k f.left (unitSection A) (unitSection B) (unitSection_comp_left f)
      (tateModuleToFundamentalGroup A x) = tateModuleToFundamentalGroup B (tateModuleMap f x) := by
  let E := ExposeV.FEt.pullbackFiberIso k f.left (unitSection A) ≪≫
    ExposeV.FEt.fiberCongr k (unitSection_comp_left f)
  ext Y y
  apply ExposeV.FEt.fiber_ext_point
  change ExposeV.FEt.fiberPoint k (E.hom.app Y (tateModuleToFundamentalGroup A x • E.inv.app Y y)) =
    ExposeV.FEt.fiberPoint k (tateModuleToFundamentalGroup B (tateModuleMap f x) • y)
  obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
  set n := liftDegree Y
  rw [fiberPoint_tateModuleToFundamentalGroup_smul (tateModuleMap f x) y n hg hg0]
  -- the point of the fibre of `f^* Y` corresponding to `y`
  set z := E.inv.app Y y
  have hEz : E.hom.app Y z = y := FintypeCat.inv_hom_id_apply (E.app Y) y
  have hfib (w : (originFiber A).obj ((ExposeV.FEt.pullback f.left).obj Y)) :
      ExposeV.FEt.fiberPoint k (E.hom.app Y w) =
        ExposeV.FEt.fiberPoint k w ≫ ExposeV.FEt.proj f.left Y := by
    change ExposeV.FEt.fiberPoint k ((ExposeV.FEt.fiberCongr k (unitSection_comp_left f)).hom.app Y
      ((ExposeV.FEt.pullbackFiberIso k f.left (unitSection A)).hom.app Y w)) = _
    rw [ExposeV.FEt.fiberPoint_fiberCongr, ExposeV.FEt.fiberPoint_pullbackFiberIso]
  -- the lift of `n_A` through `f^* Y = Y ×_B A`
  let q : Y.left ⟶ B.left := Y.hom
  have hw : (f.left ≫ g) ≫ q = (mulN A n).left ≫ f.left := by
    rw [Category.assoc, hg]
    exact (congrArg CommaMorphism.left (mulN_comp f n)).symm
  let g' : A.left ⟶ ((ExposeV.FEt.pullback f.left).obj Y).left :=
    pullback.lift (f.left ≫ g) (mulN A n).left hw
  have hg'1 : g' ≫ ExposeV.FEt.proj f.left Y = f.left ≫ g := pullback.lift_fst _ _ _
  have hg' : g' ≫ ((ExposeV.FEt.pullback f.left).obj Y).hom = (mulN A n).left :=
    pullback.lift_snd _ _ _
  have hg'0 : unitSection A ≫ g' = ExposeV.FEt.fiberPoint k z := by
    apply pullback.hom_ext
    · change (unitSection A ≫ g') ≫ ExposeV.FEt.proj f.left Y =
        ExposeV.FEt.fiberPoint k z ≫ ExposeV.FEt.proj f.left Y
      rw [← hfib, hEz, Category.assoc, hg'1, ← Category.assoc, unitSection_comp_left, hg0]
    · change (unitSection A ≫ g') ≫ ((ExposeV.FEt.pullback f.left).obj Y).hom =
        ExposeV.FEt.fiberPoint k z ≫ ((ExposeV.FEt.pullback f.left).obj Y).hom
      rw [ExposeV.FEt.fiberPoint_comp, Category.assoc, hg', unit_comp_mulN_left]
  rw [hfib, fiberPoint_tateModuleToFundamentalGroup_smul x z n hg' hg'0, Category.assoc, hg'1,
    coe_tateModuleMap_apply]
  rfl

/-- XI.2.1 (remark, functoriality), `ℓ`-primary form: for a homomorphism `f : A ⟶ B`, the maps
`T_ℓ(A) → π₁(A, 0)` and `T_ℓ(B) → π₁(B, 0)` of the `ℓ`-primary clause commute with `T_ℓ(f)` and
`f_* : π₁(A, 0) → π₁(B, 0)`. -/
theorem pointedMap_tateModuleToFundamentalGroup_tateModuleOfAt (f : A ⟶ B) [IsMonHom f] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (z : tateModuleAt A ℓ) :
    pointedMap k f.left (unitSection A) (unitSection B) (unitSection_comp_left f)
      (tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z)) =
      tateModuleToFundamentalGroup B (tateModuleOfAt hℓ (tateModuleAtMap f ℓ z)) := by
  rw [pointedMap_tateModuleToFundamentalGroup, tateModuleMap_tateModuleOfAt]

end Naturality

end SGA.SGA1.ExposeXI
