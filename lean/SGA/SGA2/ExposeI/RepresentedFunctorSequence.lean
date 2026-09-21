/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Exact sequences of genuine representing objects

An original short complex of represented additive-group-valued functors
determines morphisms of its representing objects in the reverse direction.
Left exactness on every coefficient proves the cokernel property. Surjectivity
on injectives proves the first representing morphism is a monomorphism.
-/

noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeI.RepresentedSequence

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A genuine representability isomorphism, evaluated as an additive equivalence. -/
def homEquiv {P : C ⥤ AddCommGrpCat.{v}} {A : C}
    (e : preadditiveCoyoneda.obj (op A) ≅ P) (G : C) : (A ⟶ G) ≃+ P.obj G :=
  (e.app G).addCommGroupIsoToAddEquiv

variable (S : ShortComplex (C ⥤ AddCommGrpCat.{v})) {A B D : C}
    (e₁ : preadditiveCoyoneda.obj (op A) ≅ S.X₁)
    (e₂ : preadditiveCoyoneda.obj (op B) ≅ S.X₂)
    (e₃ : preadditiveCoyoneda.obj (op D) ≅ S.X₃)

/-- The first source arrow is represented by the original second functor map. -/
def firstMap : D ⟶ B :=
  (preadditiveCoyoneda.preimage (e₂.hom ≫ S.g ≫ e₃.inv)).unop

/-- The second source arrow is represented by the original first functor map. -/
def secondMap : B ⟶ A :=
  (preadditiveCoyoneda.preimage (e₁.hom ≫ S.f ≫ e₂.inv)).unop

/-- Precomposition by the first representing arrow is the original functor map. -/
theorem firstMap_precomp {G : C} (f : B ⟶ G) :
    homEquiv e₃ G (firstMap S e₂ e₃ ≫ f) =
      (S.g.app G) (homEquiv e₂ G f) := by
  have h : preadditiveCoyoneda.map (firstMap S e₂ e₃).op ≫ e₃.hom = e₂.hom ≫ S.g := by
    dsimp only [firstMap]
    simp only [Quiver.Hom.op_unop]
    erw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{v})
    (congrArg (fun α ↦ α.app G) h) f

/-- Precomposition by the second representing arrow is the original functor map. -/
theorem secondMap_precomp {G : C} (f : A ⟶ G) :
    homEquiv e₂ G (secondMap S e₁ e₂ ≫ f) =
      (S.f.app G) (homEquiv e₁ G f) := by
  have h : preadditiveCoyoneda.map (secondMap S e₁ e₂).op ≫ e₂.hom = e₁.hom ≫ S.f := by
    dsimp only [secondMap]
    simp only [Quiver.Hom.op_unop]
    erw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{v})
    (congrArg (fun α ↦ α.app G) h) f

/-- The actual representing arrows have zero composite. -/
theorem comp : firstMap S e₂ e₃ ≫ secondMap S e₁ e₂ = 0 := by
  apply (homEquiv e₃ A).injective
  rw [firstMap_precomp, map_zero]
  have h := secondMap_precomp S e₁ e₂ (𝟙 A)
  rw [Category.comp_id] at h
  rw [h]
  exact ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app A) S.zero)
    (homEquiv e₁ A (𝟙 A))

/-- The genuine short complex of representing objects. -/
def shortComplex : ShortComplex C :=
  ShortComplex.mk (firstMap S e₂ e₃) (secondMap S e₁ e₂) (comp S e₁ e₂ e₃)

variable (hleft : ∀ G : C,
  (S.map ((evaluation C AddCommGrpCat.{v}).obj G)).Exact ∧ Mono (S.f.app G))

include hleft in
/-- Left exactness on all coefficients makes the second representing arrow epic. -/
theorem secondMap_epi : Epi (secondMap S e₁ e₂) where
  left_cancellation f g hfg := by
    apply (homEquiv e₁ _).injective
    apply (AddCommGrpCat.mono_iff_injective _).mp (hleft _).2
    rw [← secondMap_precomp, ← secondMap_precomp, hfg]

include hleft in
/-- The original functor exactness supplies the actual cokernel factorization. -/
theorem exists_desc {G : C} (f : B ⟶ G) (hf : firstMap S e₂ e₃ ≫ f = 0) :
    ∃ g : A ⟶ G, secondMap S e₁ e₂ ≫ g = f := by
  have hz : (S.g.app G) (homEquiv e₂ G f) = 0 := by
    rw [← firstMap_precomp, hf, map_zero]
  obtain ⟨s, hs⟩ := ((ShortComplex.ab_exact_iff_function_exact _).mp (hleft G).1
    (homEquiv e₂ G f)).mp hz
  refine ⟨(homEquiv e₁ G).symm s, ?_⟩
  apply (homEquiv e₂ G).injective
  rw [secondMap_precomp, AddEquiv.apply_symm_apply]
  exact hs

/-- The second representing arrow is a genuine cokernel of the first. -/
def isCokernel :
    IsColimit (CokernelCofork.ofπ (secondMap S e₁ e₂) (comp S e₁ e₂ e₃)) := by
  have := secondMap_epi S e₁ e₂ hleft
  exact CokernelCofork.IsColimit.ofπ' _ _ (fun f hf ↦
    ⟨(exists_desc S e₁ e₂ e₃ hleft f hf).choose,
      (exists_desc S e₁ e₂ e₃ hleft f hf).choose_spec⟩)

variable [EnoughInjectives C]
  (hright : ∀ (I : C) [Injective I], Epi (S.g.app I))

include hright in
/-- Surjectivity on actual injectives makes the first representing arrow monic. -/
theorem firstMap_mono : Mono (firstMap S e₂ e₃) := by
  let I := Injective.under D
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp (hright I)
    (homEquiv e₃ I (Injective.ι D))
  let g := (homEquiv e₂ I).symm s
  have hg : firstMap S e₂ e₃ ≫ g = Injective.ι D := by
    apply (homEquiv e₃ I).injective
    rw [firstMap_precomp]
    exact (congrArg (S.g.app I) ((homEquiv e₂ I).apply_symm_apply s)).trans hs
  have : Mono (firstMap S e₂ e₃ ≫ g) := by rw [hg]; infer_instance
  exact mono_of_mono (firstMap S e₂ e₃) g

include hleft hright in
/-- The actual representing-object sequence is short exact. -/
theorem shortExact : (shortComplex S e₁ e₂ e₃).ShortExact where
  exact := (shortComplex S e₁ e₂ e₃).exact_of_g_is_cokernel (isCokernel S e₁ e₂ e₃ hleft)
  mono_f := firstMap_mono S e₂ e₃ hright
  epi_g := secondMap_epi S e₁ e₂ hleft

end SGA.SGA2.ExposeI.RepresentedSequence
