/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.Fibered

/-!
# SGA 1, Exposé VI, VI.10: cofibered and bifibered categories

Cocartesian morphisms are mathlib's `IsCocartesian`. SGA defines them as the cartesian
morphisms of `𝒳ᵒᵖ` over `Eᵒᵖ`; we prove that this agrees (`isCocartesian_iff_op`), and
likewise for (pre)cofibered categories. Prefibered / fibered in the opposite direction are
`IsPreCofibered` / `IsCofibered`; a category that is both fibered and cofibered is
`IsBifibered`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Category IsHomLift

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

section Opposite

variable {p}

/-- VI.10: `φ` lies over `f` iff `φᵒᵖ` lies over `fᵒᵖ` for `pᵒᵖ : 𝒳ᵒᵖ ⥤ Eᵒᵖ`. -/
theorem isHomLift_op_iff {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) :
    IsHomLift p.op f.op φ.op ↔ IsHomLift p f φ := by
  constructor
  · intro h
    have ha : p.obj a = R := Opposite.op_injective (IsHomLift.codomain_eq p.op f.op φ.op)
    have hb : p.obj b = S := Opposite.op_injective (IsHomLift.domain_eq p.op f.op φ.op)
    have h' := congrArg Quiver.Hom.unop (IsHomLift.fac' p.op f.op φ.op)
    refine IsHomLift.of_fac' p f φ ha hb ?_
    simpa [eqToHom_unop] using h'
  · intro h
    subst_hom_lift p f φ
    exact IsHomLift.map p.op φ.op

/-- VI.10: SGA's definition — a morphism is cocartesian iff it is cartesian for
`𝒳ᵒᵖ` over `Eᵒᵖ`. -/
theorem isCocartesian_iff_op {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) :
    IsCocartesian p f φ ↔ IsCartesian p.op f.op φ.op := by
  constructor
  · intro h
    have : IsHomLift p.op f.op φ.op := (isHomLift_op_iff f φ).mpr inferInstance
    refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
    have : IsHomLift p f φ'.unop := (isHomLift_op_iff f φ'.unop).mp hφ'
    refine ⟨(IsCocartesian.map p f φ φ'.unop).op, ⟨(isHomLift_op_iff (𝟙 S) _).mpr
      inferInstance, Quiver.Hom.unop_inj (IsCocartesian.fac p f φ φ'.unop)⟩, ?_⟩
    rintro χ ⟨hχ, hfac⟩
    have : IsHomLift p (𝟙 S) χ.unop := (isHomLift_op_iff (𝟙 S) χ.unop).mp hχ
    exact Quiver.Hom.unop_inj
      (IsCocartesian.map_uniq p f φ φ'.unop χ.unop (congrArg Quiver.Hom.unop hfac))
  · intro h
    have : IsHomLift p f φ := (isHomLift_op_iff f φ).mp inferInstance
    refine ⟨fun {b'} φ' hφ' ↦ ?_⟩
    have : IsHomLift p.op f.op φ'.op := (isHomLift_op_iff f φ').mpr hφ'
    have hχ : IsHomLift p.op (𝟙 (Opposite.op S)) (IsCartesian.map p.op f.op φ.op φ'.op) :=
      inferInstance
    refine ⟨(IsCartesian.map p.op f.op φ.op φ'.op).unop,
      ⟨(isHomLift_op_iff (𝟙 S) _).mp hχ,
        Quiver.Hom.op_inj (IsCartesian.fac p.op f.op φ.op φ'.op)⟩, ?_⟩
    rintro χ ⟨hχ, hfac⟩
    have : IsHomLift p.op (𝟙 (Opposite.op S)) χ.op := (isHomLift_op_iff (𝟙 S) χ).mpr hχ
    exact Quiver.Hom.op_inj
      (IsCartesian.map_uniq p.op f.op φ.op φ'.op χ.op (congrArg Quiver.Hom.op hfac))

end Opposite

/-- VI.10, co-Fib I: direct images exist for every base arrow and source object. -/
class IsPreCofibered (p : C ⥤ E) : Prop where
  exists_isCocartesian' {a : C} {S : E} (f : p.obj a ⟶ S) :
    ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ

/-- Version of `exists_isCocartesian'` usable with non-definitional equalities. -/
protected lemma IsPreCofibered.exists_isCocartesian (p : C ⥤ E) [IsPreCofibered p]
    {a : C} {R S : E} (ha : p.obj a = R) (f : R ⟶ S) :
    ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ := by
  subst ha
  exact IsPreCofibered.exists_isCocartesian' f

/-- VI.10, co-Fib II. -/
class IsCofibered (p : C ⥤ E) : Prop extends IsPreCofibered p where
  comp {R S T : E} (f : R ⟶ S) (g : S ⟶ T) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ)

/-- VI.10: fibered and cofibered. -/
class IsBifibered (p : C ⥤ E) : Prop where
  [isFibered : IsFibered p]
  [isCofibered : IsCofibered p]

attribute [instance] IsBifibered.isFibered IsBifibered.isCofibered

instance (p : C ⥤ E) [IsFibered p] [IsCofibered p] : IsBifibered p where

instance (p : C ⥤ E) [IsCofibered p] {R S T : E} (f : R ⟶ S) (g : S ⟶ T)
    {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ) :=
  IsCofibered.comp f g φ ψ

/-- VI.10: `𝒳` is coprefibered over `E` iff `𝒳ᵒᵖ` is prefibered over `Eᵒᵖ`. -/
theorem isPreCofibered_iff_op : IsPreCofibered p ↔ IsPreFibered p.op := by
  constructor
  · intro h
    refine ⟨fun {a R} f ↦ ?_⟩
    obtain ⟨b, φ, hφ⟩ := IsPreCofibered.exists_isCocartesian' (p := p) (a := a.unop) f.unop
    exact ⟨Opposite.op b, φ.op, (isCocartesian_iff_op f.unop φ).mp hφ⟩
  · intro h
    refine ⟨fun {a S} f ↦ ?_⟩
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p.op) (a := Opposite.op a) f.op
    exact ⟨b.unop, φ.unop, (isCocartesian_iff_op f φ.unop).mpr hφ⟩

/-- VI.10, co-Fib I. -/
theorem isPreCofibered_iff : IsPreCofibered p ↔
    ∀ (a : C) (S : E) (f : p.obj a ⟶ S), ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ :=
  ⟨fun _ _ _ f ↦ IsPreCofibered.exists_isCocartesian' f,
    fun h ↦ ⟨fun {a S} f ↦ h a S f⟩⟩

/-- VI.10, co-Fib II, under co-Fib I. -/
theorem isCofibered_iff_comp [IsPreCofibered p] : IsCofibered p ↔
    ∀ {R S T : E} (f : R ⟶ S) (g : S ⟶ T) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c),
      IsCocartesian p f φ → IsCocartesian p g ψ → IsCocartesian p (f ≫ g) (φ ≫ ψ) := by
  constructor
  · intro h R S T f g a b c φ ψ hφ hψ
    infer_instance
  · intro h
    refine { comp := ?_ }
    intro R S T f g a b c φ ψ hφ hψ
    exact h f g φ ψ hφ hψ

/-- VI.10: `𝒳` is cofibered over `E` iff `𝒳ᵒᵖ` is fibered over `Eᵒᵖ`. -/
theorem isCofibered_iff_op : IsCofibered p ↔ IsFibered p.op := by
  constructor
  · intro h
    have := (isPreCofibered_iff_op p).mp inferInstance
    refine (isFibered_iff_comp p.op).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
    have := (isCocartesian_iff_op f.unop φ.unop).mpr hφ
    have := (isCocartesian_iff_op g.unop ψ.unop).mpr hψ
    exact (isCocartesian_iff_op (g.unop ≫ f.unop) (ψ.unop ≫ φ.unop)).mp inferInstance
  · intro h
    have := (isPreCofibered_iff_op p).mpr inferInstance
    refine (isCofibered_iff_comp p).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
    have := (isCocartesian_iff_op f φ).mp hφ
    have := (isCocartesian_iff_op g ψ).mp hψ
    exact (isCocartesian_iff_op (f ≫ g) (φ ≫ ψ)).mpr
      (inferInstance : IsCartesian p.op (g.op ≫ f.op) (ψ.op ≫ φ.op))

namespace IsPreCofibered

variable [IsPreCofibered p] {R S : E} {a : C} (ha : p.obj a = R) (f : R ⟶ S)

/-- Codomain of a chosen cocartesian lift of `f` starting at `a`. -/
noncomputable def pushforwardObj : C :=
  Classical.choose (IsPreCofibered.exists_isCocartesian p ha f)

/-- A chosen cocartesian lift of `f` starting at `a`. -/
noncomputable def pushforwardMap : a ⟶ pushforwardObj (p := p) ha f :=
  Classical.choose (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

instance pushforwardMap.IsCocartesian :
    IsCocartesian p f (pushforwardMap (p := p) ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

lemma pushforwardObj_proj : p.obj (pushforwardObj (p := p) ha f) = S :=
  codomain_eq p f (pushforwardMap (p := p) ha f)

end IsPreCofibered

/-- VI.10: composition with a cocartesian arrow, restricted to vertical morphisms. -/
def verticalPrecomp {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsHomLift p f φ] (b' : C) : HomOver p (𝟙 S) b b' → HomOver p f a b' :=
  fun u ↦ ⟨φ ≫ u.val, by have := u.property; infer_instance⟩

/-- VI.10: a cocartesian arrow represents `Hom_f(a,-)` on the fiber over `S`. -/
noncomputable def cocartesianHomEquiv {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsCocartesian p f φ] (b' : C) : HomOver p (𝟙 S) b b' ≃ HomOver p f a b' where
  toFun := verticalPrecomp p f φ b'
  invFun u := by
    have := u.property
    exact ⟨IsCocartesian.map p f φ u.val, inferInstance⟩
  left_inv u := by
    have := u.property
    apply Subtype.ext
    exact (IsCocartesian.map_uniq p f φ (φ ≫ u.val) u.val rfl).symm
  right_inv u := by
    have := u.property
    apply Subtype.ext
    exact IsCocartesian.fac p f φ u.val

/-- VI.10: for `f : R ⟶ S` and `η` over `R`, the functor `ξ ↦ Hom_f(η, ξ)` on the fiber
`𝒳_S`. -/
def homOverCofunctor {R S : E} (f : R ⟶ S) (η : Fiber p R) : Fiber p S ⥤ Type v₂ where
  obj ξ := HomOver p f η.val ξ.val
  map {ξ ξ'} u := TypeCat.ofHom fun φ ↦
    ⟨φ.val ≫ u.val, by have := u.property; have := φ.property; infer_instance⟩
  map_id ξ := by
    ext φ
    exact Category.comp_id φ.val
  map_comp u v := by
    ext φ
    exact (Category.assoc _ _ _).symm

/-- VI.10: a direct image of `η` by `f` exists iff the functor `ξ ↦ Hom_f(η, ξ)` on `𝒳_S` is
corepresentable; a corepresenting pair `(ξ, α)` is a direct image. -/
theorem exists_isCocartesian_iff_isCorepresentable {R S : E} (f : R ⟶ S) (η : Fiber p R) :
    (∃ (ξ : Fiber p S) (φ : η.val ⟶ ξ.val), IsCocartesian p f φ) ↔
      (homOverCofunctor p f η).IsCorepresentable := by
  constructor
  · rintro ⟨ξ, φ, hφ⟩
    exact ⟨ξ, ⟨{ homEquiv := cocartesianHomEquiv p f φ _
                 homEquiv_comp := fun u v ↦ Subtype.ext (Category.assoc _ _ _).symm }⟩⟩
  · rintro ⟨ξ, ⟨e⟩⟩
    have key : ∀ {ξ' : Fiber p S} (u : ξ ⟶ ξ'),
        (e.homEquiv u).val = (e.homEquiv (𝟙 ξ)).val ≫ u.val := by
      intro ξ' u
      rw [e.homEquiv_eq u]
      rfl
    have := (e.homEquiv (𝟙 ξ)).property
    refine ⟨ξ, (e.homEquiv (𝟙 ξ)).val, ⟨fun {b'} φ' hφ' ↦ ?_⟩⟩
    let ξ' : Fiber p S := ⟨b', IsHomLift.codomain_eq p f φ'⟩
    let x : HomOver p f η.val ξ'.val := ⟨φ', hφ'⟩
    have hu : e.homEquiv (Y := ξ') ((e.homEquiv (Y := ξ')).symm x) = x :=
      Equiv.apply_symm_apply _ _
    refine ⟨((e.homEquiv (Y := ξ')).symm x).val, ⟨((e.homEquiv (Y := ξ')).symm x).property,
      ?_⟩, ?_⟩
    · have := key ((e.homEquiv (Y := ξ')).symm x)
      rw [hu] at this
      exact this.symm
    · rintro χ ⟨hχ, hfac⟩
      have h : e.homEquiv (Y := ξ') ⟨χ, hχ⟩ = x := Subtype.ext ((key _).trans hfac)
      rw [← h, Equiv.symm_apply_apply]

end SGA.SGA1.ExposeVI
