/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import SGA.SGA1.ExposeVIII.ModuleDescent

/-!
# SGA 1, Exposé VIII, §2: descent of preschemes affine over another one (affine case)

Theorem VIII.2.1 says that a faithfully flat quasi-compact `g : S' → S` is an effective descent
morphism for the fibered category of affine morphisms. SGA deduces it from VIII.1.1 through the
anti-equivalence between affine `S`-schemes and quasi-coherent `𝒪_S`-Algebras: a descent datum on
a quasi-coherent Algebra is a descent datum on the underlying Module whose isomorphism `φ` is an
isomorphism of Algebras.

Here `S = Spec A` and `S' = Spec B`, so affine `S`-schemes are the spectra of `A`-algebras. An
algebra descent datum is a module descent datum whose coaction `θ` is a ring homomorphism
(`AlgebraDescentDatum`); the invariants form a subalgebra, and `C ↦ B ⊗_A C` is an equivalence
between `A`-algebras and `B`-algebras with descent data (`toDescentAlgebra`, instance
`IsEquivalence`). The same holds for commutative algebras throughout, which is SGA's
convention for Algebras after the preliminary discussion of §2.

The geometric form of VIII.2.1, with descent data of schemes as in VIII.7, is proved for an affine
base in `SGA.SGA1.ExposeVIII.AffineSchemeDescent`, from the results here.
-/

universe u v w

open TensorProduct CategoryTheory

namespace SGA.SGA1.ExposeVIII

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

section Datum

variable (A B) (C : Type w) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- VIII.2: a descent datum on the `B`-algebra `C` relative to `A → B`: a descent datum on the
module `C` whose isomorphism `φ : C ⊗_A B ≅ B ⊗_A C` is an isomorphism of algebras, i.e. whose
coaction `θ : C → B ⊗_A C` is a homomorphism of rings. -/
@[ext]
structure AlgebraDescentDatum extends ModuleDescentDatum A B C where
  coaction_one : coaction 1 = 1
  coaction_mul (x y : C) : coaction (x * y) = coaction x * coaction y

end Datum

namespace AlgebraDescentDatum

variable {C : Type w} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (D : AlgebraDescentDatum A B C)

/-- The coaction as a homomorphism of `B`-algebras. -/
noncomputable def coactionAlgHom : C →ₐ[B] B ⊗[A] C :=
  AlgHom.ofLinearMap D.coaction D.coaction_one D.coaction_mul

/-- VIII.2: the invariants `{x | θ x = 1 ⊗ x}` form an `A`-subalgebra. -/
def invariantsSubalgebra : Subalgebra A C :=
  D.invariants.toSubalgebra
    (by
      change D.coaction 1 = 1 ⊗ₜ 1
      rw [D.coaction_one, Algebra.TensorProduct.one_def])
    fun x y hx hy ↦ by
      change D.coaction (x * y) = 1 ⊗ₜ (x * y)
      rw [D.coaction_mul, (D.mem_invariants).1 hx, (D.mem_invariants).1 hy,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]

lemma toSubmodule_invariantsSubalgebra :
    Subalgebra.toSubmodule D.invariantsSubalgebra = D.invariants :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- The canonical homomorphism of `B`-algebras `B ⊗_A C₀ → C` from the invariants. -/
noncomputable def descentAlgHom : B ⊗[A] D.invariantsSubalgebra →ₐ[B] C :=
  Algebra.TensorProduct.lift (Algebra.ofId B C) D.invariantsSubalgebra.val
    fun _ _ ↦ Commute.all _ _

@[simp]
lemma descentAlgHom_tmul (b : B) (x : D.invariantsSubalgebra) :
    D.descentAlgHom (b ⊗ₜ x) = b • (x : C) := by
  simp [descentAlgHom, Algebra.smul_def]

/-- VIII.2.1 (affine case), effectiveness: for flat `A → B`, every algebra descent datum is
effective: `B ⊗_A C₀ → C` is an isomorphism of `B`-algebras. -/
theorem descentAlgHom_bijective [Module.Flat A B] : Function.Bijective D.descentAlgHom := by
  let e : B ⊗[A] D.invariantsSubalgebra ≃ₗ[B] B ⊗[A] D.invariants :=
    AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (Subalgebra.toSubmoduleEquiv D.invariantsSubalgebra).symm
  have h : ⇑D.descentAlgHom = D.descentMap ∘ e := by
    ext y
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, Function.comp_apply] at hx hy ⊢; rw [hx, hy]
    | tmul b x => simp [e]; rfl
  rw [h]
  exact D.descentMap_bijective.comp e.bijective

/-- VIII.2.1 (affine case): `B ⊗_A C₀ ≃ C` as `B`-algebras. -/
noncomputable def descentAlgEquiv [Module.Flat A B] : B ⊗[A] D.invariantsSubalgebra ≃ₐ[B] C :=
  AlgEquiv.ofBijective D.descentAlgHom D.descentAlgHom_bijective

lemma coaction_descentAlgHom (y : B ⊗[A] D.invariantsSubalgebra) :
    D.coaction (D.descentAlgHom y) = (D.descentAlgHom.toLinearMap.restrictScalars A).lTensor B
      (LinearMap.baseChange B (TensorProduct.mk A B D.invariantsSubalgebra 1) y) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x =>
    have hx : D.coaction (x : C) = 1 ⊗ₜ (x : C) := x.2
    simp [hx, TensorProduct.smul_tmul']

end AlgebraDescentDatum

section Canonical

variable (A B) in
/-- The canonical algebra descent datum on `B ⊗_A C`, `θ (b ⊗ c) = b ⊗ 1 ⊗ c`. -/
noncomputable def AlgebraDescentDatum.canonical (C : Type w) [CommRing C] [Algebra A C] :
    AlgebraDescentDatum A B (B ⊗[A] C) where
  toModuleDescentDatum := ModuleDescentDatum.canonical A B C
  coaction_one := rfl
  coaction_mul x y := by
    have h : ⇑(ModuleDescentDatum.canonical A B C).coaction =
        ⇑(Algebra.TensorProduct.map (AlgHom.id B B)
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C))) := by
      ext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b c => simp
    rw [h, map_mul]

@[simp]
lemma AlgebraDescentDatum.canonical_coaction {C : Type w} [CommRing C] [Algebra A C] :
    (AlgebraDescentDatum.canonical A B C).coaction =
      (ModuleDescentDatum.canonical A B C).coaction := rfl

end Canonical

section Hom

variable {C : Type w} [CommRing C] [Algebra A C] {D : Type w} [CommRing D] [Algebra A D]

lemma toLinearMap_tensorProductMap_id (u : C →ₐ[A] D) :
    (Algebra.TensorProduct.map (AlgHom.id B B) u).toLinearMap = u.toLinearMap.baseChange B := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b c
  simp

/-- VIII.2.1 (affine case), full faithfulness: for a faithfully flat `A`-algebra `B`, a
homomorphism of `B`-algebras `u' : B ⊗_A C → B ⊗_A D` is of the form `B ⊗ u` for a homomorphism
of `A`-algebras `u` if and only if its two inverse images to `B ⊗_A B` agree (as in
`exists_baseChange_eq_iff`); `u` is then unique (`algHom_map_injective`). -/
theorem exists_algHom_map_eq_iff [Module.FaithfullyFlat A B] (u' : B ⊗[A] C →ₐ[B] B ⊗[A] D) :
    (∃ u : C →ₐ[A] D, Algebra.TensorProduct.map (AlgHom.id B B) u = u') ↔
      (TensorProduct.leftComm A B B D).toLinearMap ∘ₗ
          (u'.toLinearMap.restrictScalars A).lTensor B ∘ₗ
          (TensorProduct.leftComm A B B C).toLinearMap =
        (u'.toLinearMap.restrictScalars A).lTensor B := by
  rw [← exists_baseChange_eq_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.toLinearMap, (toLinearMap_tensorProductMap_id u).symm⟩
  · rintro ⟨v, hv⟩
    have hv' (x : C) : (1 : B) ⊗ₜ[A] v x = u' (1 ⊗ₜ x) := by
      rw [← LinearMap.baseChange_tmul, hv]
      rfl
    have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) D
    have h1 : v 1 = 1 := hinj (by
      simp only [TensorProduct.mk_apply]
      rw [hv', ← Algebra.TensorProduct.one_def, map_one, Algebra.TensorProduct.one_def])
    have hmul (x y : C) : v (x * y) = v x * v y := hinj (by
      simp only [TensorProduct.mk_apply]
      rw [hv', ← one_mul (1 : B), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, ← hv', ← hv',
        Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    refine ⟨AlgHom.ofLinearMap v h1 hmul, AlgHom.toLinearMap_injective ?_⟩
    rw [toLinearMap_tensorProductMap_id]
    exact hv

theorem algHom_map_injective [Module.FaithfullyFlat A B] :
    Function.Injective (fun u : C →ₐ[A] D ↦ Algebra.TensorProduct.map (AlgHom.id B B) u) := by
  intro u v h
  apply AlgHom.toLinearMap_injective
  apply baseChange_injective_of_faithfullyFlat (A := A) (B := B)
  simp only
  rw [← toLinearMap_tensorProductMap_id, ← toLinearMap_tensorProductMap_id]
  exact congrArg AlgHom.toLinearMap h

end Hom

section Category

variable (A B) in
/-- VIII.2: a `B`-algebra equipped with an algebra descent datum relative to `A → B`. For
`S = Spec A`, `S' = Spec B`, the opposite category is the category of affine `S'`-schemes
with descent data relative to `S' → S`. -/
structure DescentAlgebra where
  /-- The underlying type. -/
  carrier : Type w
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra B carrier]
  [isAlgebraBase : Algebra A carrier]
  [isScalarTower : IsScalarTower A B carrier]
  /-- The descent datum. -/
  datum : AlgebraDescentDatum A B carrier

namespace DescentAlgebra

attribute [instance] isCommRing isAlgebra isAlgebraBase isScalarTower

instance : CoeSort (DescentAlgebra.{u, v, w} A B) (Type w) := ⟨carrier⟩

/-- Morphisms of algebras with descent data. -/
@[ext]
structure Hom (C₁ C₂ : DescentAlgebra.{u, v, w} A B) where
  /-- The underlying homomorphism of `B`-algebras. -/
  toAlgHom : C₁ →ₐ[B] C₂
  comm (x : C₁) : C₂.datum.coaction (toAlgHom x) =
    (toAlgHom.toLinearMap.restrictScalars A).lTensor B (C₁.datum.coaction x)

instance : Category (DescentAlgebra.{u, v, w} A B) where
  Hom := Hom
  id C := ⟨AlgHom.id B C, fun x ↦ by
    rw [AlgHom.id_apply, AlgHom.toLinearMap_id, LinearMap.restrictScalars_id,
      LinearMap.lTensor_id, LinearMap.id_apply]⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom, fun x ↦ by
    rw [AlgHom.comp_apply, g.comm, f.comm, AlgHom.comp_toLinearMap,
      LinearMap.restrictScalars_comp, LinearMap.lTensor_comp_apply]⟩

@[ext]
lemma hom_ext {C₁ C₂ : DescentAlgebra.{u, v, w} A B} {f g : C₁ ⟶ C₂}
    (h : f.toAlgHom = g.toAlgHom) : f = g := Hom.ext h

@[simp]
lemma comp_toAlgHom {C₁ C₂ C₃ : DescentAlgebra.{u, v, w} A B} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

@[simp]
lemma id_toAlgHom (C : DescentAlgebra.{u, v, w} A B) :
    Hom.toAlgHom (𝟙 C) = AlgHom.id B C := rfl

/-- An isomorphism of algebras with descent data from an algebra isomorphism compatible with the
descent data. -/
@[simps]
def isoMk {C₁ C₂ : DescentAlgebra.{u, v, w} A B} (e : C₁ ≃ₐ[B] C₂)
    (comm : ∀ x, C₂.datum.coaction (e x) =
      (e.toLinearMap.restrictScalars A).lTensor B (C₁.datum.coaction x)) : C₁ ≅ C₂ where
  hom := ⟨e.toAlgHom, comm⟩
  inv := ⟨e.symm.toAlgHom, fun y ↦ by
    obtain ⟨x, rfl⟩ := e.surjective y
    change C₁.datum.coaction (e.symm (e x)) = _
    rw [e.symm_apply_apply, comm, ← LinearMap.lTensor_comp_apply]
    convert (LinearMap.id_apply (R := A) (C₁.datum.coaction x)).symm
    rw [← LinearMap.lTensor_id]
    congr 1
    ext z
    simp⟩
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

end DescentAlgebra

variable (A B) in
/-- VIII.2: the functor `C ↦ B ⊗_A C` from `A`-algebras to `B`-algebras with descent data
relative to `A → B` (the opposite of the inverse image functor on affine schemes). -/
@[simps]
noncomputable def toDescentAlgebra :
    CommAlgCat.{max v w} A ⥤ DescentAlgebra.{u, v, max v w} A B where
  obj C := ⟨B ⊗[A] C, AlgebraDescentDatum.canonical A B C⟩
  map u := ⟨Algebra.TensorProduct.map (AlgHom.id B B) u.hom, fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp⟩
  map_id C := by
    ext : 1
    refine AlgHom.ext fun x ↦ ?_
    change Algebra.TensorProduct.map (AlgHom.id B B) (AlgHom.id A C) x = x
    rw [Algebra.TensorProduct.map_id, AlgHom.id_apply]
  map_comp f g := by
    ext : 1
    change Algebra.TensorProduct.map (AlgHom.id B B) (g.hom.comp f.hom) =
      (Algebra.TensorProduct.map (AlgHom.id B B) g.hom).comp
        (Algebra.TensorProduct.map (AlgHom.id B B) f.hom)
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]

/-- VIII.2.1 (affine case), faithfulness. -/
instance [Module.FaithfullyFlat A B] : (toDescentAlgebra.{u, v, w} A B).Faithful where
  map_injective {C D} f g h := by
    ext : 1
    exact algHom_map_injective (A := A) (B := B) congr(($h).toAlgHom)

/-- VIII.2.1 (affine case), fullness. -/
instance [Module.FaithfullyFlat A B] : (toDescentAlgebra.{u, v, w} A B).Full where
  map_surjective {C D} f := by
    obtain ⟨u, hu⟩ := (exists_algHom_map_eq_iff (A := A) (B := B) f.toAlgHom).2 (by
      refine ((exists_baseChange_eq_iff _).1
        (exists_baseChange_eq_of_mem_invariants (A := A) (B := B) _ fun m ↦ ?_))
      rw [ModuleDescentDatum.mem_invariants]
      exact (f.comm (1 ⊗ₜ m)).trans rfl)
    exact ⟨CommAlgCat.ofHom u, by ext : 1; exact hu⟩

variable (A B) in
/-- VIII.2.1 (affine case): the descended algebra and the isomorphism `B ⊗_A C₀ ≅ C`. -/
noncomputable def descentAlgebraIso [Module.Flat A B] (C : DescentAlgebra.{u, v, max v w} A B) :
    (toDescentAlgebra.{u, v, w} A B).obj (CommAlgCat.of A C.datum.invariantsSubalgebra) ≅ C :=
  DescentAlgebra.isoMk C.datum.descentAlgEquiv fun y ↦ C.datum.coaction_descentAlgHom y

/-- VIII.2.1 (affine case), effectiveness: for flat `A → B` every algebra descent datum is
effective. -/
instance [Module.Flat A B] : (toDescentAlgebra.{u, v, w} A B).EssSurj where
  mem_essImage C := ⟨_, ⟨descentAlgebraIso A B C⟩⟩

/-- VIII.2.1 (affine case): for a faithfully flat `A`-algebra `B`, `C ↦ B ⊗_A C` is an
equivalence between `A`-algebras and `B`-algebras with descent data. Dually, `Spec B → Spec A`
is an effective descent morphism for the fibered category of affine morphisms, over affine
bases. -/
instance [Module.FaithfullyFlat A B] : (toDescentAlgebra.{u, v, w} A B).IsEquivalence where

end Category

end SGA.SGA1.ExposeVIII
