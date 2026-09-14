/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence

/-! # Actual module-cohomology representatives and the original boundary -/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- The morphism from the coefficient ring determined by an original element. -/
def moduleElementMap {M : ModuleCat.{u} R} (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp]
theorem moduleElementMap_apply {M : ModuleCat.{u} R} (x : M) (r : R) :
    moduleElementMap x r = r • x := rfl

@[simp]
theorem moduleElementMap_zero (M : ModuleCat.{u} R) : moduleElementMap (0 : M) = 0 := by
  ext
  simp [moduleElementMap]

@[simp]
theorem moduleElementMap_comp {M N : ModuleCat.{u} R} (x : M) (f : M ⟶ N) :
    moduleElementMap x ≫ f = moduleElementMap (f x) := by
  ext
  simp [moduleElementMap]

/-- An original cocycle as an element of the actual categorical cycles. -/
def moduleCocycleLift (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by
    change (K.d n ((ComplexShape.up ℕ).next n)).hom x = 0
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
    exact hx⟩

@[simp]
theorem moduleCocycleLift_iCycles (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    K.iCycles n (moduleCocycleLift K n x hx) = x :=
  ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles
    ⟨x, by
      change (K.d n ((ComplexShape.up ℕ).next n)).hom x = 0
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
      exact hx⟩

/-- The class of an original cocycle in actual module-valued cohomology. -/
def moduleCohomologyMk (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n (moduleCocycleLift K n x hx)

/-- Every actual homology element has an original cocycle representative. -/
theorem moduleCohomologyMk_surjective (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (z : K.homology n) : ∃ (x : K.X n) (hx : K.d n (n + 1) x = 0),
      moduleCohomologyMk K n x hx = z := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance z
  have hx : K.d n (n + 1) (K.iCycles n y) = 0 :=
    ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) y
  refine ⟨K.iCycles n y, hx, ?_⟩
  have he : moduleCocycleLift K n (K.iCycles n y) hx = y := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    exact moduleCocycleLift_iCycles K n _ hx
  simpa only [moduleCohomologyMk, he] using hy

/-- The categorical cycle lift of the element morphism gives exactly the
same original cycle, evaluated at one. -/
theorem moduleCocycleLift_eq_liftCycles (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    moduleCocycleLift K n x hx =
      K.liftCycles (moduleElementMap x) (n + 1) (by simp)
        (by simp only [moduleElementMap_comp, hx, moduleElementMap_zero]) (1 : R) := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
  rw [moduleCocycleLift_iCycles]
  symm
  exact (ConcreteCategory.congr_hom
    (K.liftCycles_i (moduleElementMap x) (n + 1) (by simp)
      (by simp only [moduleElementMap_comp, hx, moduleElementMap_zero])) (1 : R)).trans
        (one_smul R x)

/-- The actual connecting map is lift-and-differentiate on original
representatives in every degree, including zero. -/
theorem moduleCohomologyMk_δ (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ))
    (hS : S.ShortExact) (n : ℕ)
    (x₃ : S.X₃.X n) (hx₃ : S.X₃.d n (n + 1) x₃ = 0)
    (x₂ : S.X₂.X n) (hx₂ : S.g.f n x₂ = x₃)
    (x₁ : S.X₁.X (n + 1)) (hx₁ : S.f.f (n + 1) x₁ = S.X₂.d n (n + 1) x₂)
    (hz₁ : S.X₁.d (n + 1) (n + 1 + 1) x₁ = 0) :
    hS.δ n (n + 1) rfl (moduleCohomologyMk S.X₃ n x₃ hx₃) =
      moduleCohomologyMk S.X₁ (n + 1) x₁ hz₁ := by
  have ht := hS.δ_eq n (n + 1) rfl (moduleElementMap x₃) (by simp [hx₃])
    (moduleElementMap x₂) (by simp [hx₂])
    (moduleElementMap x₁) (by simp [hx₁]) (n + 1 + 1) (by simp)
  simpa only [moduleCohomologyMk, moduleCocycleLift_eq_liftCycles,
    ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom ht (1 : R)

end SGA.SGA2.ExposeV
