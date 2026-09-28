/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # The actual adic completion as the limit of the original quotients

The diagram has terms `M / JⁿM` and the original quotient transition maps.
Its limiting cone consists of `AdicCompletion J M` and the actual evaluation
maps. The universal property is proved directly from compatible quotient
families, without noetherianity or finite-generation assumptions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite ModuleCat

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] (J : Ideal R) (M : ModuleCat.{u} R)

/-- The original inverse system of module quotients by powers of the ideal. -/
def adicQuotientDiagram : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (M ⧸ (J ^ n.unop • ⊤ : Submodule R M))
  map {m n} f := ModuleCat.ofHom (AdicCompletion.transitionMap J M (leOfHom f.unop))
  map_id n := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Every term is the actual original quotient, with its given module structure. -/
theorem adicQuotientDiagram_obj (n : ℕ) :
    (adicQuotientDiagram J M).obj (op n) =
      ModuleCat.of R (M ⧸ (J ^ n • ⊤ : Submodule R M)) := rfl

/-- The diagram uses the original `Submodule.factorPow` transition map. -/
theorem adicQuotientDiagram_map {m n : ℕ} (h : m ≤ n) :
    (adicQuotientDiagram J M).map (homOfLE h).op =
      ModuleCat.ofHom (Submodule.factorPow J M h) := rfl

/-- The original quotient projections, simultaneously at all powers. -/
def adicQuotientProjection : (Functor.const ℕᵒᵖ).obj M ⟶ adicQuotientDiagram J M where
  app n := ModuleCat.ofHom (Submodule.mkQ (J ^ n.unop • ⊤ : Submodule R M))
  naturality {m n} f := by
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The actual evaluation cone on the original adic completion. -/
def adicCompletionCone : Cone (adicQuotientDiagram J M) where
  pt := ModuleCat.of R (AdicCompletion J M)
  π :=
    { app n := ModuleCat.ofHom (AdicCompletion.eval J M n.unop)
      naturality {m n} f := by
        apply ModuleCat.hom_ext
        ext x
        exact (x.property (leOfHom f.unop)).symm }

/-- The cone projections are the existing actual completion evaluations. -/
theorem adicCompletionCone_π_app (n : ℕ) :
    (adicCompletionCone J M).π.app (op n) = ModuleCat.ofHom (AdicCompletion.eval J M n) := rfl

/-- Assemble an arbitrary compatible cone as its actual sequence of quotient values. -/
def adicCompletionConeLift (s : Cone (adicQuotientDiagram J M)) :
    s.pt ⟶ ModuleCat.of R (AdicCompletion J M) :=
  ModuleCat.ofHom
    { toFun x := ⟨fun n => s.π.app (op n) x, fun {m n} h =>
        ConcreteCategory.congr_hom (s.w (homOfLE h).op) x⟩
      map_add' x y := by
        apply AdicCompletion.ext
        intro n
        exact (s.π.app (op n)).hom.map_add x y
      map_smul' r x := by
        apply AdicCompletion.ext
        intro n
        exact (s.π.app (op n)).hom.map_smul r x }

/-- The universal lift's coordinates are precisely the original cone maps. -/
@[simp]
theorem adicCompletionConeLift_eval (s : Cone (adicQuotientDiagram J M))
    (n : ℕ) (x : s.pt) :
    AdicCompletion.eval J M n (adicCompletionConeLift J M s x) = s.π.app (op n) x := rfl

/-- The genuine inverse-limit property of the actual adic completion. -/
def adicCompletionConeIsLimit : IsLimit (adicCompletionCone J M) where
  lift s := adicCompletionConeLift J M s
  fac s n := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  uniq s f hf := by
    apply ModuleCat.hom_ext
    ext x
    apply AdicCompletion.ext
    intro n
    exact ConcreteCategory.congr_hom (hf (op n)) x

/-- The original map to the completion factors each original quotient projection. -/
@[reassoc]
theorem adicCompletion_of_π (n : ℕᵒᵖ) :
    ModuleCat.ofHom (AdicCompletion.of J M) ≫ (adicCompletionCone J M).π.app n =
      (adicQuotientProjection J M).app n := rfl

/-- The completion map is exactly the limit lift of the quotient-projection cone. -/
theorem adicCompletion_of_eq_limitLift :
    ModuleCat.ofHom (AdicCompletion.of J M) =
      (adicCompletionConeIsLimit J M).lift ⟨M, adicQuotientProjection J M⟩ := rfl

end SGA.SGA2.ExposeIV
