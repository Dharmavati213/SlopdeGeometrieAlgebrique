/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.TensorProduct.Maps
import SGA.Foundations.QuasiCoherent.Sections

/-!
# Sections of inverse images along morphisms of affine schemes

For a quasi-coherent module `P` on `Spec R` and a ring map `α : R ⟶ C`, the global sections of
the inverse image of `P` along `Spec C ⟶ Spec R` are `C ⊗_R Γ(Spec R, P)`
(Stacks, Tag 01I9). We also record some bookkeeping for extensions of scalars, and the rings
`B ⊗_A B` used in descent.
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry

section ExtendScalars

variable {A C C' : CommRingCat.{u}} (N₀ : ModuleCat.{u} A)

/-- `β : C → C'` as an `A`-linear map, for `α ≫ β = α'`. -/
def restrictScalarsHom (α : A ⟶ C) (α' : A ⟶ C') (β : C ⟶ C') (h : α ≫ β = α') :
    (ModuleCat.restrictScalars α.hom).obj (ModuleCat.of C C) →ₗ[A]
      (ModuleCat.restrictScalars α'.hom).obj (ModuleCat.of C' C') where
  toFun := β.hom
  map_add' := map_add β.hom
  map_smul' a c := by
    change β.hom (α.hom a * (show C from c)) = α'.hom a * β.hom (show C from c)
    rw [map_mul, ← h]; rfl

/-- For `β : C → C'` with `α ≫ β = α'`, the map `C ⊗_A N₀ → C' ⊗_A N₀`, `c ⊗ n ↦ β c ⊗ n`. -/
noncomputable def extendScalarsMap (α : A ⟶ C) (α' : A ⟶ C') (β : C ⟶ C') (h : α ≫ β = α') :
    (ModuleCat.extendScalars α.hom).obj N₀ →+ (ModuleCat.extendScalars α'.hom).obj N₀ :=
  (LinearMap.rTensor N₀ (restrictScalarsHom α α' β h)).toAddMonoidHom

open ModuleCat ChangeOfRings in
@[simp]
lemma extendScalarsMap_tmul (α : A ⟶ C) (α' : A ⟶ C') (β : C ⟶ C') (h : α ≫ β = α') (c : C)
    (n : N₀) :
    extendScalarsMap N₀ α α' β h (c ⊗ₜ[A, α.hom] n) = β.hom c ⊗ₜ[A, α'.hom] n := rfl

/-- The map `m ↦ 1 ⊗ m`, `N₀ → C ⊗_A N₀`. -/
noncomputable def oneTmul (α : A ⟶ C) : N₀ →+ (ModuleCat.extendScalars α.hom).obj N₀ :=
  (toExtendScalars N₀ α).toAddMonoidHom

open ModuleCat ChangeOfRings in
lemma oneTmul_apply (α : A ⟶ C) (n : N₀) : oneTmul N₀ α n = (1 : C) ⊗ₜ[A,α.hom] n := rfl

open ModuleCat ChangeOfRings in
lemma extendScalarsMap_oneTmul (α : A ⟶ C) (α' : A ⟶ C') (β : C ⟶ C') (h : α ≫ β = α')
    (n : N₀) : extendScalarsMap N₀ α α' β h (oneTmul N₀ α n) = oneTmul N₀ α' n := by
  change ((β.hom 1) ⊗ₜ[A,α'.hom] n : (ModuleCat.extendScalars α'.hom).obj N₀) =
    ((1 : C') ⊗ₜ[A,α'.hom] n : (ModuleCat.extendScalars α'.hom).obj N₀)
  rw [map_one]

open ModuleCat ChangeOfRings in
lemma extendScalarsMap_smul (α : A ⟶ C) (α' : A ⟶ C') (β : C ⟶ C') (h : α ≫ β = α') (c : C)
    (y : (ModuleCat.extendScalars α.hom).obj N₀) :
    extendScalarsMap N₀ α α' β h (c • y) = β.hom c • extendScalarsMap N₀ α α' β h y := by
  induction y using TensorProduct.induction_on with
  | zero =>
    change extendScalarsMap N₀ α α' β h (c • (0 : (ModuleCat.extendScalars α.hom).obj N₀)) =
      β.hom c • extendScalarsMap N₀ α α' β h 0
    rw [smul_zero, map_zero, smul_zero]
  | add y₁ y₂ e₁ e₂ =>
    change extendScalarsMap N₀ α α' β h
      (c • (@id ((ModuleCat.extendScalars α.hom).obj N₀) y₁ +
        @id ((ModuleCat.extendScalars α.hom).obj N₀) y₂)) =
      β.hom c • extendScalarsMap N₀ α α' β h
        (@id ((ModuleCat.extendScalars α.hom).obj N₀) y₁ +
          @id ((ModuleCat.extendScalars α.hom).obj N₀) y₂)
    rw [smul_add, map_add, map_add, smul_add]
    erw [e₁, e₂]
    rfl
  | tmul c' n =>
    exact congrArg (fun x : C' ↦ (x ⊗ₜ[A,α'.hom] n : (ModuleCat.extendScalars α'.hom).obj N₀))
      (map_mul β.hom c c')

variable {B : CommRingCat.{u}} (φ : A ⟶ B)

/-- `B ⊗_A B` for `φ : A ⟶ B`, as a bundled commutative ring. -/
noncomputable def tensorSelf : CommRingCat.{u} :=
  letI := φ.hom.toAlgebra
  CommRingCat.of (B ⊗[A] B)

/-- The first inclusion `B → B ⊗_A B`. -/
noncomputable def tensorSelfInl : B ⟶ tensorSelf φ :=
  letI := φ.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The second inclusion `B → B ⊗_A B`. -/
noncomputable def tensorSelfInr : B ⟶ tensorSelf φ :=
  letI := φ.hom.toAlgebra
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom

lemma tensorSelf_comm : φ ≫ tensorSelfInl φ = φ ≫ tensorSelfInr φ := by
  let := φ.hom.toAlgebra
  ext a
  change (φ.hom a) ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] (φ.hom a)
  have e : φ.hom a = a • (1 : B) := by rw [Algebra.smul_def, mul_one]; rfl
  rw [e, TensorProduct.smul_tmul]

end ExtendScalars

open ModuleCat ChangeOfRings in
/-- Additive maps out of `C ⊗_A M` which are `C`-semilinear are determined by their values on
the elements `1 ⊗ m`. -/
lemma extendScalars_addHom_ext {A C : CommRingCat.{u}} {α : A ⟶ C} {M : ModuleCat.{u} A}
    {X : Type*} [AddCommGroup X] [Module C X]
    (f₁ f₂ : (ModuleCat.extendScalars α.hom).obj M →+ X)
    (h₁ : ∀ (c : C) y, f₁ (c • y) = c • f₁ y) (h₂ : ∀ (c : C) y, f₂ (c • y) = c • f₂ y)
    (h : ∀ m, f₁ (oneTmul M α m) = f₂ (oneTmul M α m)) : f₁ = f₂ := by
  ext y
  induction y using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero]
  | add y₁ y₂ e₁ e₂ => erw [map_add, map_add, e₁, e₂]
  | tmul c m =>
    have e := (ModuleCat.ExtendScalars.smul_tmul (f := α.hom) (M := M) c 1 m).symm
    erw [mul_one] at e
    refine (congrArg f₁ e).trans ((h₁ c _).trans ?_)
    refine Eq.trans ?_ (congrArg f₂ e).symm
    exact (congrArg (fun z : X ↦ (@id (C : Type u) c) • z) (h m)).trans (h₂ c _).symm


open Scheme.Modules

section SpecSections

variable {R C : CommRingCat.{u}} (α : R ⟶ C) (P : (Spec R).Modules)

lemma top_le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := le_top

/-- The global sections of an `𝒪_{Spec R}`-module, as an `R`-module. -/
noncomputable abbrev Scheme.Modules.ΓSpec (P : (Spec R).Modules) : ModuleCat R :=
  (modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)

/-- For `P` quasi-coherent on `Spec R`, `P ≅ Γ(P)^~`. -/
noncomputable def Scheme.Modules.tildeΓIso [P.IsQuasicoherent] : tilde P.ΓSpec ≅ P :=
  @asIso _ _ _ _ P.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)

lemma Scheme.Modules.tildeΓIso_inv_app [P.IsQuasicoherent] (x : Γ(P, ⊤)) :
    (P.tildeΓIso).inv.app ⊤ x = tilde.toOpen P.ΓSpec ⊤ x := by
  have h : (P.tildeΓIso).hom.app ⊤ (tilde.toOpen P.ΓSpec ⊤ x) = x := by
    have := congr($(Scheme.Modules.toOpen_fromTildeΓ_app P ⊤).hom x)
    simp only [ModuleCat.hom_comp, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, ModuleCat.hom_id] at this
    exact this
  conv_lhs => rw [← h]
  exact iso_inv_app_hom_app P.tildeΓIso ⊤ _

/-- For `P` quasi-coherent on `Spec R` and `α : R ⟶ C`, the global sections of the inverse image
of `P` along `Spec C ⟶ Spec R` are `C ⊗_R Γ(Spec R, P)`. -/
@[stacks 01I9]
noncomputable def pullbackSpecMapΓAddEquiv [P.IsQuasicoherent] :
    Γ((Scheme.Modules.pullback (Spec.map α)).obj P, ⊤) ≃+
      (ModuleCat.extendScalars α.hom).obj P.ΓSpec :=
  (isoAppAddEquiv ((Scheme.Modules.pullback (Spec.map α)).mapIso P.tildeΓIso.symm) ⊤).trans <|
    (isoAppAddEquiv (pullbackSpecMapTildeIso α _) ⊤).trans
    (tilde.isoTop _).toLinearEquiv.symm.toAddEquiv

lemma pullbackSpecMapΓAddEquiv_apply [P.IsQuasicoherent]
    (z : Γ((Scheme.Modules.pullback (Spec.map α)).obj P, ⊤)) :
    pullbackSpecMapΓAddEquiv α P z = (tilde.isoTop _).inv
      (((pullbackSpecMapTildeIso α _).hom.app ⊤)
      (((Scheme.Modules.pullback (Spec.map α)).map P.tildeΓIso.inv).app ⊤ z)) := rfl

lemma pullbackSpecMapΓAddEquiv_pullbackAppTop [P.IsQuasicoherent] (m : Γ(P, ⊤)) :
    pullbackSpecMapΓAddEquiv α P (pullbackAppTop (Spec.map α) P ⊤ (top_le_preimage_top _) m) =
      oneTmul P.ΓSpec α m := by
  rw [pullbackSpecMapΓAddEquiv_apply,
    pullbackAppTop_eq_pullbackApp_map (Spec.map α) _ _ le_rfl (top_le_preimage_top _)]
  have e₀ : P.presheaf.map (homOfLE (le_refl (⊤ : (Spec R).Opens))).op m = m := by
    have e : homOfLE (le_refl (⊤ : (Spec R).Opens)) = 𝟙 _ := Subsingleton.elim _ _
    rw [e, op_id, CategoryTheory.Functor.map_id]; rfl
  rw [e₀]
  have e₅ : ((Scheme.Modules.pullback (Spec.map α)).map P.tildeΓIso.inv).app ⊤
      (pullbackApp (Spec.map α) P ⊤ m) =
      pullbackApp (Spec.map α) (tilde P.ΓSpec) ⊤ (P.tildeΓIso.inv.app ⊤ m) :=
    (pullbackApp_naturality (Spec.map α) P.tildeΓIso.inv ⊤ _).symm
  rw [e₅, tildeΓIso_inv_app]
  have e₇ := pullbackApp_SpecMap_tilde α P.ΓSpec m
  exact (congrArg (tilde.isoTop _).inv e₇).trans ((tilde.isoTop _).hom_inv_id_apply _)

lemma pullbackSpecMapΓAddEquiv_smul [P.IsQuasicoherent] (c : C)
    (z : Γ((Scheme.Modules.pullback (Spec.map α)).obj P, ⊤)) :
    pullbackSpecMapΓAddEquiv α P (c • z) = c • pullbackSpecMapΓAddEquiv α P z := by
  rw [pullbackSpecMapΓAddEquiv_apply, pullbackSpecMapΓAddEquiv_apply, Hom.app_smul_Spec,
    Hom.app_smul_Spec]
  exact map_smul (tilde.isoTop _).inv.hom c _

lemma pullbackSpecMapΓAddEquiv_pullbackApp [P.IsQuasicoherent] (m : Γ(P, ⊤)) :
    pullbackSpecMapΓAddEquiv α P (pullbackApp (Spec.map α) P ⊤ m) = oneTmul P.ΓSpec α m := by
  rw [← pullbackSpecMapΓAddEquiv_pullbackAppTop α P m]
  congr 1
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  have e : (homOfLE (top_le_preimage_top (Spec.map α)) : (⊤ : (Spec C).Opens) ⟶ _) = 𝟙 _ :=
    Subsingleton.elim _ _
  erw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma pullbackSpecMapΓAddEquiv_symm_smul_oneTmul [P.IsQuasicoherent] (c : C) (m : Γ(P, ⊤)) :
    (pullbackSpecMapΓAddEquiv α P).symm (c • oneTmul P.ΓSpec α m) =
      c • pullbackAppTop (Spec.map α) P ⊤ (top_le_preimage_top _) m := by
  rw [AddEquiv.symm_apply_eq, pullbackSpecMapΓAddEquiv_smul,
    pullbackSpecMapΓAddEquiv_pullbackAppTop]

end SpecSections


section Tensor

variable {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C)

/-- `B ⊗_A C`, for ring maps `φ : A ⟶ B` and `ψ : A ⟶ C`, as a bundled commutative ring. -/
noncomputable def tensorObj : CommRingCat.{u} :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.of (B ⊗[A] C)

/-- The inclusion `B ⟶ B ⊗_A C`. -/
noncomputable def tensorInl : B ⟶ tensorObj φ ψ :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion `C ⟶ B ⊗_A C`. -/
noncomputable def tensorInr : C ⟶ tensorObj φ ψ :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom

lemma isPushout_tensorObj : IsPushout φ ψ (tensorInl φ ψ) (tensorInr φ ψ) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  exact CommRingCat.isPushout_tensorProduct A B C

lemma tensorInl_comm : φ ≫ tensorInl φ ψ = ψ ≫ tensorInr φ ψ :=
  (isPushout_tensorObj φ ψ).w

lemma isPullback_SpecMap_tensorObj :
    IsPullback (Spec.map (tensorInl φ ψ)) (Spec.map (tensorInr φ ψ)) (Spec.map φ) (Spec.map ψ) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_tensorObj φ ψ)

end Tensor


section Cancel

open ModuleCat ChangeOfRings

variable {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C) (Q : ModuleCat.{u} C)

lemma tensorInl_mul_tensorInr (b : B) (c : C) :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    tensorInl φ ψ b * tensorInr φ ψ c = (b ⊗ₜ[A] c : B ⊗[A] C) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  change (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma tensor_addHom_ext {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [AddCommMonoid P] {f g : M ⊗[R] N →+ P}
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => exact h m n
  | add x y hx hy => simp [hx, hy]

/-- The map `(c, q) ↦ c • (1 ⊗ q)`, `C' → Q → C' ⊗_C Q`. -/
noncomputable def smulOneTmul {C C' : CommRingCat.{u}} (γ : C ⟶ C') (Q : ModuleCat.{u} C) :
    C' →+ (Q →+ (ModuleCat.extendScalars γ.hom).obj Q) where
  toFun c := (DistribSMul.toAddMonoidHom _ c).comp (oneTmul Q γ)
  map_zero' := by ext q; exact zero_smul C' (oneTmul Q γ q)
  map_add' c c' := by ext q; exact add_smul c c' (oneTmul Q γ q)

lemma smulOneTmul_apply {C C' : CommRingCat.{u}} (γ : C ⟶ C') (Q : ModuleCat.{u} C) (c : C')
    (q : Q) : smulOneTmul γ Q c q = c • oneTmul Q γ q := rfl

lemma oneTmul_smul {C C' : CommRingCat.{u}} (γ : C ⟶ C') (Q : ModuleCat.{u} C) (c : C) (q : Q) :
    oneTmul Q γ (c • q) = γ c • oneTmul Q γ q :=
  (toExtendScalars Q γ).map_smul c q

lemma tensorCancel_balance (a : A) (b : B) (q : Q) :
    smulOneTmul (tensorInr φ ψ) Q (tensorInl φ ψ (φ a * b)) q =
      smulOneTmul (tensorInr φ ψ) Q (tensorInl φ ψ b) (ψ a • q) := by
  rw [smulOneTmul_apply, smulOneTmul_apply, oneTmul_smul, smul_smul, map_mul,
    mul_comm (tensorInl φ ψ b)]
  congr 2
  exact congr($(tensorInl_comm φ ψ) a)

/-- For a `C`-module `Q`, the map `B ⊗_A Q → (B ⊗_A C) ⊗_C Q`, `b ⊗ q ↦ (b ⊗ 1) ⊗ q`. -/
noncomputable def tensorCancelHom :
    letI := φ.hom.toAlgebra
    B ⊗[A] (ModuleCat.restrictScalars ψ.hom).obj Q →+
      (ModuleCat.extendScalars (tensorInr φ ψ).hom).obj Q :=
  letI := φ.hom.toAlgebra
  TensorProduct.liftAddHom ((smulOneTmul (tensorInr φ ψ) Q).comp (tensorInl φ ψ).hom.toAddMonoidHom)
    (fun a b q ↦ tensorCancel_balance φ ψ Q a b q)


/-- Auxiliary map for `tensorCancelInv`: `b ↦ c ↦ q ↦ b ⊗ c q`. -/
noncomputable def tensorCancelInvAux :
    letI := φ.hom.toAlgebra
    B →+ C →+ (Q →+ B ⊗[A] (ModuleCat.restrictScalars ψ.hom).obj Q) :=
  letI := φ.hom.toAlgebra
  { toFun b :=
      { toFun c :=
          (TensorProduct.mk A B ((ModuleCat.restrictScalars ψ.hom).obj Q) b).toAddMonoidHom.comp
            (DistribSMul.toAddMonoidHom Q c)
        map_zero' := by
          ext q
          exact (congrArg (TensorProduct.mk A B ((ModuleCat.restrictScalars ψ.hom).obj Q) b)
            (zero_smul C q)).trans (map_zero _)
        map_add' c c' := by
          ext q
          exact (congrArg (TensorProduct.mk A B ((ModuleCat.restrictScalars ψ.hom).obj Q) b)
            (add_smul c c' q)).trans (map_add _ _ _) }
    map_zero' := by ext c q; exact TensorProduct.zero_tmul _ _
    map_add' b b' := by ext c q; exact TensorProduct.add_tmul _ _ _ }

/-- Auxiliary map for `tensorCancelInv`: `b ⊗ c ↦ q ↦ b ⊗ c q`. -/
noncomputable def tensorCancelInvAux' :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    B ⊗[A] C →+ (Q →+ B ⊗[A] (ModuleCat.restrictScalars ψ.hom).obj Q) :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  TensorProduct.liftAddHom (tensorCancelInvAux φ ψ Q) (fun a b c ↦ by
    ext q
    exact (TensorProduct.smul_tmul (R := A) (M := B) (N := (ModuleCat.restrictScalars ψ.hom).obj Q)
      a b (c • q)).trans (congrArg (TensorProduct.tmul A b) (mul_smul (ψ a) c q).symm))

lemma tensorCancelInvAux'_tmul (b : B) (c : C) (q : Q) :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    tensorCancelInvAux' φ ψ Q (b ⊗ₜ[A] c) q =
      b ⊗ₜ[A] (show (ModuleCat.restrictScalars ψ.hom).obj Q from c • q) := rfl

lemma tensorCancelInvAux'_smul (c : C) (t : letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra
      B ⊗[A] C) (q : Q) :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    letI : Module C (B ⊗[A] C) := Module.compHom _
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom
    tensorCancelInvAux' φ ψ Q (c • t) q = tensorCancelInvAux' φ ψ Q t (c • q) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  let : Module C (B ⊗[A] C) := Module.compHom _
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [smul_zero, map_zero]
    rfl
  | add t t' ht ht' =>
    rw [smul_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, ht, ht']
  | tmul b c' =>
    have e : c • (b ⊗ₜ[A] c' : B ⊗[A] C) = b ⊗ₜ[A] (c * c') := by
      change ((1 : B) ⊗ₜ[A] c) * (b ⊗ₜ[A] c') = b ⊗ₜ[A] (c * c')
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e, tensorCancelInvAux'_tmul, tensorCancelInvAux'_tmul, mul_comm, mul_smul]

/-- The inverse of `tensorCancelHom`. -/
noncomputable def tensorCancelInv :
    letI := φ.hom.toAlgebra
    (ModuleCat.extendScalars (tensorInr φ ψ).hom).obj Q →+
      B ⊗[A] (ModuleCat.restrictScalars ψ.hom).obj Q :=
  TensorProduct.liftAddHom (tensorCancelInvAux' φ ψ Q)
    (fun c t q ↦ tensorCancelInvAux'_smul φ ψ Q c t q)

lemma tensorCancelInv_smul_oneTmul (b : B) (q : Q) :
    letI := φ.hom.toAlgebra
    tensorCancelInv φ ψ Q (tensorInl φ ψ b • oneTmul Q (tensorInr φ ψ) q) =
      b ⊗ₜ[A] (show (ModuleCat.restrictScalars ψ.hom).obj Q from q) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  rw [oneTmul_apply]
  erw [ExtendScalars.smul_tmul, mul_one]
  exact (tensorCancelInvAux'_tmul φ ψ Q b 1 q).trans
    (congrArg (TensorProduct.tmul A b) (one_smul C q))

lemma tensorCancelInv_tensorCancelHom (x) :
    letI := φ.hom.toAlgebra
    tensorCancelInv φ ψ Q (tensorCancelHom φ ψ Q x) = x := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']
  | tmul b q => exact tensorCancelInv_smul_oneTmul φ ψ Q b q

lemma tensorCancelHom_tensorCancelInv_aux (b : B) (c : C) (q : Q) :
    letI := φ.hom.toAlgebra
    letI := ψ.hom.toAlgebra
    tensorCancelHom φ ψ Q (tensorCancelInv φ ψ Q ((show tensorObj φ ψ from b ⊗ₜ[A] c) ⊗ₜ[C,
      (tensorInr φ ψ).hom] q)) =
      (show tensorObj φ ψ from b ⊗ₜ[A] c) ⊗ₜ[C, (tensorInr φ ψ).hom] q := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  change tensorInl φ ψ b • oneTmul Q (tensorInr φ ψ) (c • q) = _
  rw [oneTmul_smul, smul_smul, tensorInl_mul_tensorInr, oneTmul_apply]
  erw [ExtendScalars.smul_tmul, mul_one]

lemma tensorCancelHom_tensorCancelInv (y) :
    tensorCancelHom φ ψ Q (tensorCancelInv φ ψ Q y) = y := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  induction y using TensorProduct.induction_on with
  | zero => erw [map_zero]; rfl
  | add y y' hy hy' => erw [map_add, map_add, hy, hy']; rfl
  | tmul t q =>
    have key := tensor_addHom_ext (R := A) (M := B) (N := C)
      (f := (tensorCancelHom φ ψ Q).comp ((tensorCancelInv φ ψ Q).comp
        ((TensorProduct.mk C ((ModuleCat.restrictScalars (tensorInr φ ψ).hom).obj
          (ModuleCat.of (tensorObj φ ψ) (tensorObj φ ψ))) Q).flip q).toAddMonoidHom))
      (g := ((TensorProduct.mk C ((ModuleCat.restrictScalars (tensorInr φ ψ).hom).obj
        (ModuleCat.of (tensorObj φ ψ) (tensorObj φ ψ))) Q).flip q).toAddMonoidHom)
      (fun b c ↦ tensorCancelHom_tensorCancelInv_aux φ ψ Q b c q)
    exact congr($key t)

theorem tensorCancelHom_bijective : Function.Bijective (tensorCancelHom φ ψ Q) :=
  Function.bijective_iff_has_inverse.mpr ⟨tensorCancelInv φ ψ Q,
    tensorCancelInv_tensorCancelHom φ ψ Q, tensorCancelHom_tensorCancelInv φ ψ Q⟩

end Cancel


section PullbackTop

open Scheme.Modules

variable {X Y Y' Y'' : Scheme.{u}}

/-- The inverse image `Γ(f^* E, ⊤) → Γ(w^* E, ⊤)` of global sections along `u` with `u ≫ f = w`. -/
noncomputable def Scheme.Modules.pullbackTop (u : Y' ⟶ Y) (f : Y ⟶ X) (w : Y' ⟶ X)
    (hw : u ≫ f = w) (E : X.Modules) :
    Γ((Scheme.Modules.pullback f).obj E, ⊤) ⟶ Γ((Scheme.Modules.pullback w).obj E, ⊤) :=
  pullbackApp u _ ⊤ ≫ (pullbackCompIso' u f w hw E).inv.app ⊤

lemma Scheme.Modules.pullbackTop_apply (u : Y' ⟶ Y) (f : Y ⟶ X) (w : Y' ⟶ X)
    (hw : u ≫ f = w) (E : X.Modules) (z : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    pullbackTop u f w hw E z = (pullbackCompIso' u f w hw E).inv.app ⊤ (pullbackApp u _ ⊤ z) :=
  rfl

lemma Scheme.Modules.pullbackTop_pullbackAppTop (u : Y' ⟶ Y) (f : Y ⟶ X) (w : Y' ⟶ X)
    (hw : u ≫ f = w) (E : X.Modules) (W : X.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ W) (hw' : ⊤ ≤ w ⁻¹ᵁ W)
    (s : Γ(E, W)) :
    pullbackTop u f w hw E (pullbackAppTop f E W hf s) = pullbackAppTop w E W hw' s :=
  pullbackCompIso'_inv_app_pullbackApp u f w hw E W hf hw' s

lemma Scheme.Modules.pullbackTop_congr {u u' : Y' ⟶ Y} (e : u = u') (f : Y ⟶ X) (w : Y' ⟶ X)
    (hw : u ≫ f = w) (hw' : u' ≫ f = w) (E : X.Modules)
    (z : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    pullbackTop u f w hw E z = pullbackTop u' f w hw' E z := by
  subst e; rfl

lemma Scheme.Modules.pullbackTop_SpecMap_smul {C C' : CommRingCat.{u}} (β : C ⟶ C')
    (f : Spec C ⟶ X) (w : Spec C' ⟶ X) (hw : Spec.map β ≫ f = w) (E : X.Modules) (c : C)
    (z : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    pullbackTop (Spec.map β) f w hw E (c • z) = β c • pullbackTop (Spec.map β) f w hw E z := by
  rw [pullbackTop_apply, pullbackTop_apply, pullbackApp_SpecMap_smul]
  exact Hom.app_smul_Spec _ ⊤ _ _


set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Modules.pullbackCompIso'_inv_comp (u' : Y'' ⟶ Y') (u : Y' ⟶ Y) (f : Y ⟶ X)
    (E : X.Modules) (h : (u' ≫ u) ≫ f = u' ≫ u ≫ f) :
    (Scheme.Modules.pullback u').map (pullbackCompIso' u f (u ≫ f) rfl E).inv ≫
      (pullbackCompIso' u' (u ≫ f) (u' ≫ u ≫ f) rfl E).inv =
    (pullbackComp u' u).hom.app _ ≫ (pullbackCompIso' (u' ≫ u) f (u' ≫ u ≫ f) h E).inv := by
  have := congr(NatTrans.app $(pseudofunctor_associativity u' u f) E)
  simp only [NatTrans.comp_app, Functor.comp_obj, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, eqToHom_refl,
    NatTrans.id_app, pullbackCompIso', pullbackCongr, eqToIso_refl, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Iso.refl_inv, Category.comp_id] at this ⊢
  erw [Category.comp_id]
  rw [← cancel_epi ((pullbackComp u' (u ≫ f)).inv.app E ≫
    (Scheme.Modules.pullback u').map ((pullbackComp u f).inv.app E))]
  simp only [Category.assoc]
  rw [this]
  simp [← Functor.map_comp_assoc]

lemma Scheme.Modules.pullbackTop_comp (u' : Y'' ⟶ Y') (u : Y' ⟶ Y) (f : Y ⟶ X) (w : Y' ⟶ X)
    (w' : Y'' ⟶ X) (hw : u ≫ f = w) (hw' : u' ≫ w = w') (h : (u' ≫ u) ≫ f = w')
    (E : X.Modules) (z : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    pullbackTop u' w w' hw' E (pullbackTop u f w hw E z) = pullbackTop (u' ≫ u) f w' h E z := by
  subst hw hw'
  have e1 := pullbackApp_naturality u' (pullbackCompIso' u f (u ≫ f) rfl E).inv ⊤
    (pullbackApp u _ ⊤ z)
  have e2 := pullbackApp_comp u' u ((Scheme.Modules.pullback f).obj E) ⊤ z
  rw [pullbackTop_apply, pullbackTop_apply, pullbackTop_apply]
  erw [e1, e2]
  have key := congr(Hom.app $(pullbackCompIso'_inv_comp u' u f E h) ⊤
    (pullbackApp u' _ ⊤ (pullbackApp u _ ⊤ z)))
  erw [Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at key
  exact key

end PullbackTop

end AlgebraicGeometry
