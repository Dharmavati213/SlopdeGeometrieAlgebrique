/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveHorseshoeStep

/-! # Injectivity of split injective rows

The split row `J₁ ⟶ J₁ ⊞ J₃ ⟶ J₃` is injective as an object of
`ShortComplex C` when `J₁` and `J₃` are injective. Thus the horseshoe is an
injective resolution of the entire original short complex, allowing comparison
maps and homotopies that preserve both horizontal arrows at every degree.
-/

noncomputable section
universe v u
open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A split short exact row of injectives is injective in the abelian category
of short complexes, not just separately in its three components. -/
theorem injective_splitRow (J₁ J₃ : C) [Injective J₁] [Injective J₃] :
    Injective (ShortComplex.mk (biprod.inl : J₁ ⟶ J₁ ⊞ J₃) biprod.snd (by simp)) where
  factors {A B} g φ _ := by
    have : Mono φ.τ₂ := (inferInstance : Mono (ShortComplex.π₂.map φ))
    have : Mono φ.τ₃ := (inferInstance : Mono (ShortComplex.π₃.map φ))
    let a := Injective.factorThru (g.τ₂ ≫ biprod.fst) φ.τ₂
    let c := Injective.factorThru g.τ₃ φ.τ₃
    let h : B ⟶ ShortComplex.mk (biprod.inl : J₁ ⟶ J₁ ⊞ J₃) biprod.snd (by simp) :=
      { τ₁ := B.f ≫ a
        τ₂ := biprod.lift a (B.g ≫ c)
        τ₃ := c
        comm₁₂ := by ext <;> simp [Category.assoc]
        comm₂₃ := by simp }
    refine ⟨h, ?_⟩
    apply ShortComplex.Hom.ext
    · change φ.τ₁ ≫ B.f ≫ a = g.τ₁
      rw [φ.comm₁₂_assoc, Injective.comp_factorThru]
      simpa [Category.assoc] using (congrArg (fun f => f ≫ biprod.fst) g.comm₁₂).symm
    · change φ.τ₂ ≫ biprod.lift a (B.g ≫ c) = g.τ₂
      apply biprod.hom_ext
      · simp [a, Category.assoc]
      · simpa [c, Category.assoc, φ.comm₂₃_assoc] using g.comm₂₃.symm
    · exact Injective.comp_factorThru _ _

/-- Any short exact row with injective endpoints is injective as a short complex. -/
theorem injective_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₁] [Injective S.X₃] : Injective S := by
  let s := hS.splittingOfInjective
  let e : S ≅ ShortComplex.mk (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃) biprod.snd (by simp) :=
    ShortComplex.isoMk (Iso.refl _) s.isoBinaryBiproduct (Iso.refl _)
      (by ext <;> simp [s, Category.assoc]) (by simp)
  exact Injective.of_iso e.symm (injective_splitRow _ _)

namespace InjectiveHorseshoe

variable [EnoughInjectives C] (S : ShortComplex C)

instance injective_row : Injective (row S) := injective_splitRow _ _

end InjectiveHorseshoe
end SGA.SGA2.ExposeV
