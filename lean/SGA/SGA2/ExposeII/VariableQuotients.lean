/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.EssentiallyZero
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# SGA 2, Exposé II, Lemma 11: quotients with varying coefficients

For an inverse sequence `F` and `f : R`, the quotients `F_n / f^n F_n`
form an inverse sequence. Their projections from `F` are a natural epimorphism,
so essential vanishing of `F` implies essential vanishing of these quotients.
These are the left-hand terms in the inductive exact sequence of II.11.
-/

universe u

open CategoryTheory Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]
variable (F : ℕᵒᵖ ⥤ ModuleCat.{u} R) (f : R)

/-- The submodule `f^n F_n`. -/
def powerImage (n : ℕᵒᵖ) : Submodule R (F.obj n) :=
  LinearMap.range (f ^ n.unop • (LinearMap.id : F.obj n →ₗ[R] F.obj n))

/-- The transitions of `F` respect the power-image submodules. -/
theorem powerImage_le_comap {m n : ℕᵒᵖ} (h : m ⟶ n) :
    powerImage F f m ≤ (powerImage F f n).comap (F.map h).hom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨f ^ (m.unop - n.unop) • F.map h x, ?_⟩
  change f ^ n.unop • (f ^ (m.unop - n.unop) • F.map h x) =
    F.map h (f ^ m.unop • x)
  rw [map_smul, ← mul_smul, ← pow_add, Nat.add_sub_of_le (leOfHom h.unop)]

/-- The inverse system of quotients `F_n / f^n F_n` in II.11. -/
def variableQuotientSystem : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (F.obj n ⧸ powerImage F f n)
  map {m n} h := ModuleCat.ofHom
    ((powerImage F f m).mapQ (powerImage F f n) (F.map h).hom
      (powerImage_le_comap F f h))
  map_id n := by
    ext x
    change Submodule.Quotient.mk (F.map (𝟙 n) x) = Submodule.Quotient.mk x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {l m n} h g := by
    ext x
    change Submodule.Quotient.mk (F.map (h ≫ g) x) =
      Submodule.Quotient.mk (F.map g (F.map h x))
    rw [Functor.map_comp]
    rfl

/-- The natural projection to the varying-coefficient quotient system. -/
def variableQuotientProjection : F ⟶ variableQuotientSystem F f where
  app n := ModuleCat.ofHom (powerImage F f n).mkQ

instance variableQuotientProjection_app_epi (n : ℕᵒᵖ) :
    Epi ((variableQuotientProjection F f).app n) :=
  (ModuleCat.epi_iff_surjective _).mpr (powerImage F f n).mkQ_surjective

/-- II.11: the quotient system inherits essential vanishing. -/
theorem variableQuotientSystem_isEssentiallyZero (hF : IsEssentiallyZero F) :
    IsEssentiallyZero (variableQuotientSystem F f) :=
  hF.of_epi (variableQuotientProjection F f)

end SGA.SGA2.ExposeII
