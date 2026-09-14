/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Coefficient maps on spectral-object terms and differentials -/

noncomputable section

open CategoryTheory Limits ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]
  {S T : Abelian.SpectralObject C ι} (φ : S ⟶ T)

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- A coefficient map on the actual kernel defining spectral-object cycles. -/
def cyclesMap : S.cycles f g n ⟶ T.cycles f g n :=
  kernel.map _ _ ((φ.hom n).app (mk₁ g)) ((φ.hom (n + 1)).app (mk₁ f))
    (φ.comm n (n + 1) rfl f g)

@[reassoc (attr := simp)]
lemma cyclesMap_i : cyclesMap φ f g n ≫ T.iCycles f g n =
    S.iCycles f g n ≫ (φ.hom n).app (mk₁ g) := by
  apply kernel.lift_ι

@[reassoc]
lemma toCycles_cyclesMap (fg : i ⟶ k) (hfg : f ≫ g = fg) :
    S.toCycles f g fg hfg n ≫ cyclesMap φ f g n =
      (φ.hom n).app (mk₁ fg) ≫ T.toCycles f g fg hfg n := by
  rw [← cancel_mono (T.iCycles f g n)]
  simp only [Category.assoc, cyclesMap_i, Abelian.SpectralObject.toCycles_i,
    Abelian.SpectralObject.toCycles_i_assoc]
  exact (φ.hom n).naturality _

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- A coefficient map of the actual short complexes defining every page term. -/
def shortComplexMap :
    S.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      T.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ where
  τ₁ := (φ.hom n₀).app (mk₁ f₃)
  τ₂ := (φ.hom n₁).app (mk₁ f₂)
  τ₃ := (φ.hom n₂).app (mk₁ f₁)
  comm₁₂ := (φ.comm n₀ n₁ hn₁ f₂ f₃).symm
  comm₂₃ := (φ.comm n₁ n₂ hn₂ f₁ f₂).symm

/-- The induced map on actual page terms, by functoriality of homology. -/
def EMap : S.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ T.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (shortComplexMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc]
lemma cyclesIso_inv_cyclesMap :
    (S.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
        ShortComplex.cyclesMap (shortComplexMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
      cyclesMap φ f₁ f₂ n₁ ≫ (T.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  rw [← cancel_mono (T.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles]
  simp [shortComplexMap]

@[reassoc]
lemma πE_EMap : S.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
    cyclesMap φ f₁ f₂ n₁ ≫ T.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp [Abelian.SpectralObject.πE, EMap, cyclesIso_inv_cyclesMap_assoc]

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- Coefficient and interval maps commute on every actual page term. -/
@[reassoc]
lemma EMap_map :
    EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        T.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      S.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap φ f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [EMap, Abelian.SpectralObject.map]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  ext <;> exact ((φ.hom _).naturality _).symm

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₃ : n₂ + 1 = n₃)

/-- Actual coefficient maps commute with every spectral-object differential. -/
@[reassoc]
lemma EMap_d : EMap φ f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      T.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
    S.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      EMap φ f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  rw [← cancel_epi (S.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (S.toCycles f₃ f₄ (f₃ ≫ f₄) rfl n₁)]
  rw [πE_EMap_assoc, toCycles_cyclesMap_assoc,
    T.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl n₀ n₁ n₂ n₃,
    S.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl n₀ n₁ n₂ n₃,
    πE_EMap, toCycles_cyclesMap_assoc]
  rw [φ.comm_assoc]

end

end SGA.SGA2.ExposeI.SpectralObjectCoefficientMaps
