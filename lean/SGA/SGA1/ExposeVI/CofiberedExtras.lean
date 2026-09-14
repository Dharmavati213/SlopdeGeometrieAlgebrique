/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cofibered
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# SGA 1, Exposé VI, VI.10.1

If a category over `E` is both prefibered and precofibered, then it is
fibered if and only if it is cofibered.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

set_option linter.style.haveILetI false

/-- In a fibered category, every cocartesian morphism is strongly cocartesian. -/
theorem isStronglyCocartesian_of_isCocartesian [IsFibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCocartesian p f φ] :
    IsStronglyCocartesian p f φ where
  universal_property' {b'} g ψ hψ := by
    -- `g : S ⟶ p.obj b'`; take a cartesian lift of `g` with target `b'`.
    let ha : p.obj b' = p.obj b' := rfl
    let β := IsPreFibered.pullbackMap (p := p) ha g
    haveI : IsCartesian p g β := IsPreFibered.pullbackMap.IsCartesian (p := p) ha g
    haveI : IsStronglyCartesian p g β := inferInstance
    let χ₀ : a ⟶ IsPreFibered.pullbackObj (p := p) ha g :=
      IsStronglyCartesian.map p g β (g := f) (f' := f ≫ g) rfl ψ
    haveI : IsHomLift p f χ₀ := inferInstance
    have hfac₀ : χ₀ ≫ β = ψ := IsStronglyCartesian.fac p g β (g := f) (f' := f ≫ g) rfl ψ
    let χ₁ : b ⟶ IsPreFibered.pullbackObj (p := p) ha g :=
      IsCocartesian.map p f φ χ₀
    haveI : IsHomLift p (𝟙 S) χ₁ := inferInstance
    refine ⟨χ₁ ≫ β, ⟨inferInstance, ?_⟩, ?_⟩
    · calc
        φ ≫ χ₁ ≫ β = (φ ≫ χ₁) ≫ β := by rw [Category.assoc]
        _ = χ₀ ≫ β := by rw [IsCocartesian.fac p f φ χ₀]
        _ = ψ := hfac₀
    · intro π ⟨hπ, hπfac⟩
      haveI : IsHomLift p g π := hπ
      let π₁ : b ⟶ IsPreFibered.pullbackObj (p := p) ha g :=
        IsStronglyCartesian.map p g β (g := 𝟙 S) (f' := g) (by simp) π
      haveI : IsHomLift p (𝟙 S) π₁ := inferInstance
      have hπfac' : π₁ ≫ β = π :=
        IsStronglyCartesian.fac p g β (g := 𝟙 S) (f' := g) (by simp) π
      have hcomp : φ ≫ π₁ = χ₀ := by
        refine IsStronglyCartesian.ext (p := p) (f := g) (φ := β) (g := f)
          (ψ := φ ≫ π₁) (ψ' := χ₀) ?_
        calc
          (φ ≫ π₁) ≫ β = φ ≫ π₁ ≫ β := by simp [Category.assoc]
          _ = φ ≫ π := by rw [hπfac']
          _ = ψ := hπfac
          _ = χ₀ ≫ β := hfac₀.symm
      have : π₁ = χ₁ := IsCocartesian.map_uniq p f φ χ₀ π₁ hcomp
      calc
        π = π₁ ≫ β := hπfac'.symm
        _ = χ₁ ≫ β := by rw [this]

/-- Under `IsCofibered`, every cocartesian morphism is strongly cocartesian
(dual of mathlib's fibered instance). -/
theorem isStronglyCocartesian_of_isCocartesian_of_isCofibered [IsCofibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCocartesian p f φ] :
    IsStronglyCocartesian p f φ where
  universal_property' {b'} g ψ hψ := by
    let hb := IsHomLift.codomain_eq (p := p) (f := f) (φ := φ)
    let γ := IsPreCofibered.pushforwardMap (p := p) hb g
    haveI : IsCocartesian p g γ :=
      IsPreCofibered.pushforwardMap.IsCocartesian (p := p) hb g
    haveI : IsCocartesian p (f ≫ g) (φ ≫ γ) := IsCofibered.comp f g φ γ
    haveI : IsHomLift p (f ≫ g) ψ := hψ
    let τ := IsCocartesian.map p (f ≫ g) (φ ≫ γ) ψ
    haveI : IsHomLift p (𝟙 (p.obj b')) τ :=
      IsCocartesian.map_isHomLift p (f ≫ g) (φ ≫ γ) ψ
    refine ⟨γ ≫ τ, ⟨inferInstance, ?_⟩, ?_⟩
    · calc
        φ ≫ γ ≫ τ = (φ ≫ γ) ≫ τ := by rw [Category.assoc]
        _ = ψ := IsCocartesian.fac p (f ≫ g) (φ ≫ γ) ψ
    · intro π ⟨hπ, hπfac⟩
      haveI : IsHomLift p g π := hπ
      let π₀ := IsCocartesian.map p g γ π
      haveI : IsHomLift p (𝟙 (p.obj b')) π₀ :=
        IsCocartesian.map_isHomLift p g γ π
      have hπ₀ : γ ≫ π₀ = π := IsCocartesian.fac p g γ π
      have : π₀ = τ :=
        IsCocartesian.map_uniq p (f ≫ g) (φ ≫ γ) ψ π₀ (by
          calc
            (φ ≫ γ) ≫ π₀ = φ ≫ γ ≫ π₀ := by simp [Category.assoc]
            _ = φ ≫ π := by rw [hπ₀]
            _ = ψ := hπfac)
      calc
        π = γ ≫ π₀ := hπ₀.symm
        _ = γ ≫ τ := by rw [this]

/-- VI.10.1 (⇒): fibered + precofibered ⇒ cofibered. -/
theorem isCofibered_of_isFibered [IsFibered p] [IsPreCofibered p] : IsCofibered p := by
  refine (isCofibered_iff_comp p).mpr ?_
  intro R S T f g a b c φ ψ hφ hψ
  haveI : IsCocartesian p f φ := hφ
  haveI : IsCocartesian p g ψ := hψ
  haveI : IsStronglyCocartesian p f φ := isStronglyCocartesian_of_isCocartesian p f φ
  haveI : IsStronglyCocartesian p g ψ := isStronglyCocartesian_of_isCocartesian p g ψ
  haveI : IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ) := inferInstance
  exact IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian
    (p := p) (f := f ≫ g) (φ := φ ≫ ψ)

/-- In a cofibered category, every cartesian morphism is strongly cartesian. -/
theorem isStronglyCartesian_of_isCartesian_of_isCofibered [IsCofibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCartesian p f φ] :
    IsStronglyCartesian p f φ where
  universal_property' {a'} g φ' hφ' := by
    -- `g : p.obj a' ⟶ R`
    let ha : p.obj a' = p.obj a' := rfl
    let α := IsPreCofibered.pushforwardMap (p := p) ha g
    haveI : IsCocartesian p g α :=
      IsPreCofibered.pushforwardMap.IsCocartesian (p := p) ha g
    haveI : IsStronglyCocartesian p g α :=
      isStronglyCocartesian_of_isCocartesian_of_isCofibered p g α
    haveI : IsHomLift p (g ≫ f) φ' := hφ'
    let ψ₀ : IsPreCofibered.pushforwardObj (p := p) ha g ⟶ b :=
      IsStronglyCocartesian.map p g α (f' := g ≫ f) rfl φ'
    haveI : IsHomLift p f ψ₀ := inferInstance
    have hψ₀ : α ≫ ψ₀ = φ' := IsStronglyCocartesian.fac p g α rfl φ'
    let χ₁ : IsPreCofibered.pushforwardObj (p := p) ha g ⟶ a :=
      IsCartesian.map p f φ ψ₀
    haveI : IsHomLift p (𝟙 R) χ₁ := inferInstance
    refine ⟨α ≫ χ₁, ⟨inferInstance, ?_⟩, ?_⟩
    · calc
        (α ≫ χ₁) ≫ φ = α ≫ χ₁ ≫ φ := by simp [Category.assoc]
        _ = α ≫ ψ₀ := by rw [IsCartesian.fac p f φ ψ₀]
        _ = φ' := hψ₀
    · intro π ⟨hπ, hπfac⟩
      haveI : IsHomLift p g π := hπ
      let π₁ : IsPreCofibered.pushforwardObj (p := p) ha g ⟶ a :=
        IsCocartesian.map p g α π
      haveI : IsHomLift p (𝟙 R) π₁ :=
        IsCocartesian.map_isHomLift p g α π
      have hπ₁ : α ≫ π₁ = π := IsCocartesian.fac p g α π
      have hcancel : π₁ ≫ φ = χ₁ ≫ φ := by
        refine IsStronglyCocartesian.ext (p := p) (f := g) (φ := α) (g := f)
          (ψ := π₁ ≫ φ) (ψ' := χ₁ ≫ φ) ?_
        calc
          α ≫ π₁ ≫ φ = (α ≫ π₁) ≫ φ := by simp [Category.assoc]
          _ = π ≫ φ := by rw [hπ₁]
          _ = φ' := hπfac
          _ = α ≫ ψ₀ := hψ₀.symm
          _ = α ≫ χ₁ ≫ φ := by rw [← IsCartesian.fac p f φ ψ₀]
          _ = α ≫ (χ₁ ≫ φ) := by simp [Category.assoc]
      have : π₁ = χ₁ :=
        IsCartesian.ext (p := p) (f := f) (φ := φ) π₁ χ₁ hcancel
      calc
        π = α ≫ π₁ := hπ₁.symm
        _ = α ≫ χ₁ := by rw [this]

/-- VI.10.1 (⇐): cofibered + prefibered ⇒ fibered. -/
theorem isFibered_of_isCofibered [IsCofibered p] [IsPreFibered p] : IsFibered p := by
  refine (isFibered_iff_cartesian_isStronglyCartesian (p := p)).mpr ?_
  intro R S f a b φ hφ
  haveI : IsCartesian p f φ := hφ
  exact isStronglyCartesian_of_isCartesian_of_isCofibered p f φ

/-- VI.10.1: prefibered + precofibered ⇒ fibered iff cofibered. -/
theorem isFibered_iff_isCofibered [IsPreFibered p] [IsPreCofibered p] :
    IsFibered p ↔ IsCofibered p :=
  ⟨fun _ => isCofibered_of_isFibered (p := p),
    fun _ => isFibered_of_isCofibered (p := p)⟩

end SGA.SGA1.ExposeVI
