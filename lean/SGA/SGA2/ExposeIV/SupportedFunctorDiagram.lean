/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedQuotientStages

/-!
# The actual quotient-induced diagram `T(R/Jⁿ)`

For an additive contravariant functor on finite supported modules, the groups
`T(R/Jⁿ)` carry their canonical scalar actions. The transition maps are images
of the actual quotient maps, and are linear for those actions. This constructs
the input diagram in SGA 2, IV.1.3, without postulating a representing module or
compatibility of stagewise representations.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual cyclic module `R/Jⁿ`, with its proved support condition. -/
def supportedRingQuotient (J : Ideal R) (n : ℕ) : SupportedFGModuleCat J :=
  ⟨FGModuleCat.of R (R ⧸ J ^ n),
    (support_subset_zeroLocus_iff_exists_pow_le_annihilator J (R ⧸ J ^ n)).mpr
      ⟨n, by rw [Ideal.annihilator_quotient]⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cyclic quotient used in the diagram is the image of the rank-one
module in its quotient-ring stage, by the identity on quotient elements. -/
def supportedRingQuotientStageIso (J : Ideal R) (n : ℕ) :
    (supportedQuotientStage J n).obj (FGModuleCat.of (R ⧸ J ^ n) (R ⧸ J ^ n)) ≅
      supportedRingQuotient J n :=
  (supportedFiniteModuleProperty J).isoMk ((ModuleCat.isFG R).isoMk
    (LinearEquiv.toModuleIso (X₁ :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
        (ModuleCat.of (R ⧸ J ^ n) (R ⧸ J ^ n))) (X₂ := ModuleCat.of R (R ⧸ J ^ n))
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ (Algebra.smul_def r (show R ⧸ J ^ n from x)).symm }))

@[simp] theorem supportedRingQuotientStageIso_hom_apply (J : Ideal R) (n : ℕ)
    (x : R ⧸ J ^ n) : (supportedRingQuotientStageIso J n).hom.hom.hom.hom x = x := rfl

@[simp] theorem supportedRingQuotientStageIso_inv_apply (J : Ideal R) (n : ℕ)
    (x : R ⧸ J ^ n) : (supportedRingQuotientStageIso J n).inv.hom.hom.hom x = x := rfl

/-- The transition `R/Jᵐ → R/Jⁿ`, for `n ≤ m`, is the original quotient map. -/
def supportedRingQuotientMap (J : Ideal R) {n m : ℕ} (h : n ≤ m) :
    supportedRingQuotient J m ⟶ supportedRingQuotient J n :=
  ObjectProperty.homMk (FGModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right h)))

@[simp] theorem supportedRingQuotientMap_apply (J : Ideal R) {n m : ℕ} (h : n ≤ m)
    (r : R) :
    (supportedRingQuotientMap J h).hom.hom.hom (Ideal.Quotient.mk (J ^ m) r) =
      Ideal.Quotient.mk (J ^ n) r := rfl

@[simp] theorem supportedRingQuotientMap_refl (J : Ideal R) (n : ℕ) :
    supportedRingQuotientMap J (le_refl n) = 𝟙 (supportedRingQuotient J n) := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

@[simp] theorem supportedRingQuotientMap_comp (J : Ideal R) {n m k : ℕ}
    (hnm : n ≤ m) (hmk : m ≤ k) :
    supportedRingQuotientMap J hmk ≫ supportedRingQuotientMap J hnm =
      supportedRingQuotientMap J (hnm.trans hmk) := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  exact Submodule.factor_comp (Ideal.pow_le_pow_right hmk) (Ideal.pow_le_pow_right hnm)

/-- Quotient transitions are epimorphisms in the genuine supported category. -/
instance (J : Ideal R) {n m : ℕ} (h : n ≤ m) : Epi (supportedRingQuotientMap J h) := by
  apply (supportedFiniteInclusion J).epi_of_epi_map
  apply (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map
  exact (ModuleCat.epi_iff_surjective _).mpr
    (Submodule.factor_surjective (Ideal.pow_le_pow_right h))

/-- The inverse system of the actual cyclic quotients. -/
def supportedRingQuotientDiagram (J : Ideal R) : ℕᵒᵖ ⥤ SupportedFGModuleCat J where
  obj n := supportedRingQuotient J n.unop
  map f := supportedRingQuotientMap J (leOfHom f.unop)
  map_id n := supportedRingQuotientMap_refl J n.unop
  map_comp f g := (supportedRingQuotientMap_comp J (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The scalar homothety of `R/Jⁿ` vanishes for every scalar in `Jⁿ`. -/
theorem supportedRingQuotient_smul_id_eq_zero (J : Ideal R) (n : ℕ)
    {r : R} (hr : r ∈ J ^ n) :
    r • 𝟙 (supportedRingQuotient J n) = 0 := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext x
  exact Module.mem_annihilator.mp
    (show r ∈ Module.annihilator R (R ⧸ J ^ n) by
      rwa [Ideal.annihilator_quotient]) x

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- `Hₙ = T(R/Jⁿ)` with the canonical module structure, not an independently
chosen action. -/
def supportedFunctorStage (n : ℕ) : ModuleCat.{u} R :=
  (additiveFunctorModuleLift (R := R) T).obj (op (supportedRingQuotient J n))

/-- The linear transition is exactly the image under `T` of the quotient map. -/
def supportedFunctorTransition {n m : ℕ} (h : n ≤ m) :
    supportedFunctorStage J T n ⟶ supportedFunctorStage J T m :=
  (additiveFunctorModuleLift (R := R) T).map (supportedRingQuotientMap J h).op

@[simp] theorem supportedFunctorTransition_apply {n m : ℕ} (h : n ≤ m)
    (x : supportedFunctorStage J T n) :
    supportedFunctorTransition J T h x = T.map (supportedRingQuotientMap J h).op x := rfl

/-- The direct system entering the representation argument of IV.1.3. -/
def supportedFunctorDiagram : ℕ ⥤ ModuleCat.{u} R where
  obj n := supportedFunctorStage J T n
  map f := supportedFunctorTransition J T (leOfHom f)
  map_id n := by
    change (additiveFunctorModuleLift (R := R) T).map
      (supportedRingQuotientMap J (le_refl n)).op = _
    rw [supportedRingQuotientMap_refl]
    exact (additiveFunctorModuleLift (R := R) T).map_id _
  map_comp f g := by
    change (additiveFunctorModuleLift (R := R) T).map
      (supportedRingQuotientMap J ((leOfHom f).trans (leOfHom g))).op = _
    rw [← supportedRingQuotientMap_comp J (leOfHom f) (leOfHom g)]
    exact (additiveFunctorModuleLift (R := R) T).map_comp _ _

/-- Its scalar action is the image of scalar multiplication on the quotient. -/
theorem supportedFunctorStage_smul (n : ℕ) (r : R) (x : supportedFunctorStage J T n) :
    r • x = T.map (r • 𝟙 (op (supportedRingQuotient J n))) x := rfl

/-- The `n`-th group really is annihilated by `Jⁿ`. -/
theorem supportedFunctorStage_annihilator (n : ℕ) :
    J ^ n ≤ Module.annihilator R (supportedFunctorStage J T n) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  rw [supportedFunctorStage_smul]
  have h : r • 𝟙 (op (supportedRingQuotient J n)) = 0 := by
    apply Quiver.Hom.unop_inj
    exact supportedRingQuotient_smul_id_eq_zero J n hr
  rw [h, T.map_zero]
  rfl

/-- The canonical stage action therefore descends to the actual quotient ring. -/
@[instance_reducible] def supportedFunctorStageQuotientModule (n : ℕ) :
    Module (R ⧸ J ^ n) (supportedFunctorStage J T n) :=
  ((Module.isTorsionBySet_iff_subset_annihilator R (supportedFunctorStage J T n)).mpr
    (supportedFunctorStage_annihilator J T n)).module

/-- Restricting this quotient-ring action recovers the canonical `R`-action. -/
theorem supportedFunctorStageQuotientModule_mk_smul (n : ℕ) (r : R)
    (x : supportedFunctorStage J T n) :
    letI := supportedFunctorStageQuotientModule J T n
    Ideal.Quotient.mk (J ^ n) r • x = r • x := rfl

/-- Left exactness, when assumed, makes the actual transition maps injective. -/
instance [PreservesFiniteLimits T] {n m : ℕ} (h : n ≤ m) :
    Mono (supportedFunctorTransition J T h) := by
  apply (forget₂ (ModuleCat R) AddCommGrpCat).mono_of_mono_map
  change Mono (T.map (supportedRingQuotientMap J h).op)
  infer_instance

end SGA.SGA2.ExposeIV
