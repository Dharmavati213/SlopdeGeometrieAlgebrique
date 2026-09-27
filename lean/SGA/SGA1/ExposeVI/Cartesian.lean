/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Yoneda

/-!
# SGA 1, Exposé VI, §5: cartesian morphisms

We use mathlib's `Functor.IsCartesian`, which is precisely VI.5.1 (the
factorization property for arrows over the *same* base arrow). `HomOver`
spells out SGA's `Hom_f`. The main addition is the bijection in VI.5.1(i),
including its converse, and uniqueness of inverse images as a unique
vertical isomorphism compatible with the structure maps.

Lean writes `u ≫ v` for SGA's `v ∘ u`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

/-- VI.2, VI.5.1: the set `Hom_f(a,b)` of morphisms lying over `f`.
`IsHomLift` includes the equalities identifying the endpoints with those of `f`. -/
abbrev HomOver {R S : E} (f : R ⟶ S) (a b : C) :=
  {φ : a ⟶ b // IsHomLift p f φ}

/-- VI.5.1(i): composition with `φ`, restricted to vertical morphisms. -/
def verticalPostcomp {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsHomLift p f φ] (a' : C) : HomOver p (𝟙 R) a' a → HomOver p f a' b :=
  fun u ↦ ⟨u.val ≫ φ, by have := u.property; infer_instance⟩

/-- VI.5.1(i): a cartesian arrow represents `Hom_f(-,b)` on the fiber over `R`. -/
noncomputable def cartesianHomEquiv {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsCartesian p f φ] (a' : C) : HomOver p (𝟙 R) a' a ≃ HomOver p f a' b where
  toFun := verticalPostcomp p f φ a'
  invFun u := by
    have := u.property
    exact ⟨IsCartesian.map p f φ u.val, inferInstance⟩
  left_inv u := by
    have := u.property
    apply Subtype.ext
    exact (IsCartesian.map_uniq p f φ (u.val ≫ φ) u.val rfl).symm
  right_inv u := by
    have := u.property
    apply Subtype.ext
    exact IsCartesian.fac p f φ u.val

/-- VI.5.1: the universal property is equivalent to bijectivity of composition.
Quantification over all `a'` is harmless: `HomOver` is empty off the required fiber. -/
theorem isCartesian_iff_bijective {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsHomLift p f φ] :
    IsCartesian p f φ ↔ ∀ a', Function.Bijective (verticalPostcomp p f φ a') := by
  constructor
  · intro h a'
    exact (cartesianHomEquiv p f φ a').bijective
  · intro h
    constructor
    intro a' φ' hφ'
    obtain ⟨u, hu⟩ := (h a').surjective ⟨φ', hφ'⟩
    refine ⟨u.val, ⟨u.property, congrArg Subtype.val hu⟩, ?_⟩
    rintro v ⟨hv, hvφ⟩
    exact congrArg Subtype.val ((h a').injective
      (show verticalPostcomp p f φ a' ⟨v, hv⟩ = verticalPostcomp p f φ a' u from
        (Subtype.ext hvφ).trans hu.symm))

/-- VI.5.1: for `f : R ⟶ S` and `ξ` over `S`, the functor `η ↦ Hom_f(η, ξ)` on the fiber
`𝒳_R`. -/
def homOverFunctor {R S : E} (f : R ⟶ S) (ξ : Fiber p S) : (Fiber p R)ᵒᵖ ⥤ Type v₂ where
  obj η := HomOver p f η.unop.val ξ.val
  map {η η'} u := TypeCat.ofHom fun φ ↦
    ⟨u.unop.val ≫ φ.val, by have := u.unop.property; have := φ.property; infer_instance⟩
  map_id η := by
    ext φ
    exact Category.id_comp φ.val
  map_comp u v := by
    ext φ
    exact Category.assoc _ _ _

@[simp]
theorem homOverFunctor_map_apply {R S : E} (f : R ⟶ S) (ξ : Fiber p S) {η η' : (Fiber p R)ᵒᵖ}
    (u : η ⟶ η') (φ : (homOverFunctor p f ξ).obj η) :
    ((homOverFunctor p f ξ).map u φ).val = u.unop.val ≫ φ.val := rfl

/-- VI.5.1: an inverse image of `ξ` by `f` exists iff the functor `η ↦ Hom_f(η, ξ)` on `𝒳_R`
is representable; a representing pair `(η, α)` is an inverse image. -/
theorem exists_isCartesian_iff_isRepresentable {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    (∃ (η : Fiber p R) (φ : η.val ⟶ ξ.val), IsCartesian p f φ) ↔
      (homOverFunctor p f ξ).IsRepresentable := by
  constructor
  · rintro ⟨η, φ, hφ⟩
    exact ⟨η, ⟨{ homEquiv := cartesianHomEquiv p f φ _
                 homEquiv_comp := fun u v ↦ Subtype.ext (Category.assoc _ _ _) }⟩⟩
  · rintro ⟨η, ⟨e⟩⟩
    have key : ∀ {η' : Fiber p R} (u : η' ⟶ η),
        (e.homEquiv u).val = u.val ≫ (e.homEquiv (𝟙 η)).val := by
      intro η' u
      rw [e.homEquiv_eq u]
      rfl
    have := (e.homEquiv (𝟙 η)).property
    refine ⟨η, (e.homEquiv (𝟙 η)).val, ⟨fun {a'} φ' hφ' ↦ ?_⟩⟩
    let η' : Fiber p R := ⟨a', IsHomLift.domain_eq p f φ'⟩
    let x : HomOver p f η'.val ξ.val := ⟨φ', hφ'⟩
    have hu : e.homEquiv (X := η') ((e.homEquiv (X := η')).symm x) = x :=
      Equiv.apply_symm_apply _ _
    refine ⟨((e.homEquiv (X := η')).symm x).val, ⟨((e.homEquiv (X := η')).symm x).property,
      ?_⟩, ?_⟩
    · have := key ((e.homEquiv (X := η')).symm x)
      rw [hu] at this
      exact this.symm
    · rintro χ ⟨hχ, hfac⟩
      have h : e.homEquiv (X := η') ⟨χ, hχ⟩ = x := Subtype.ext ((key _).trans hfac)
      rw [← h, Equiv.symm_apply_apply]

/-- VI.5.1: two inverse images are uniquely isomorphic *over the identity*,
with compatibility with their maps to the original object. -/
theorem inverseImage_existsUnique_iso {R S : E} (f : R ⟶ S) {a a' b : C}
    (φ : a ⟶ b) (φ' : a' ⟶ b) [IsCartesian p f φ] [IsCartesian p f φ'] :
    ∃! e : a' ≅ a, IsHomLift p (𝟙 R) e.hom ∧ e.hom ≫ φ = φ' := by
  refine ⟨IsCartesian.domainUniqueUpToIso p f φ φ', ⟨inferInstance, ?_⟩, ?_⟩
  · exact IsCartesian.fac p f φ φ'
  · rintro e ⟨he, hcomp⟩
    apply Iso.ext
    exact IsCartesian.map_uniq p f φ φ' e.hom hcomp

/-- VI.5.1, used in the remark after VI.6.1: a vertical cartesian arrow is
an isomorphism. This needs no prefiberedness assumption. -/
theorem isIso_of_vertical_isCartesian {S : E} {a b : C} (φ : a ⟶ b)
    [IsCartesian p (𝟙 S) φ] : IsIso φ := by
  have : IsHomLift p (𝟙 S) (𝟙 b) :=
    IsHomLift.id (IsHomLift.codomain_eq p (𝟙 S) φ)
  let e := IsCartesian.domainUniqueUpToIso p (𝟙 S) (𝟙 b) φ
  have he : e.hom = φ := by
    simpa [e, IsCartesian.domainUniqueUpToIso] using IsCartesian.fac p (𝟙 S) (𝟙 b) φ
  rw [← he]
  infer_instance

/-- VI.5.1: vertical cartesian morphisms are exactly vertical isomorphisms. -/
theorem vertical_isCartesian_iff_isIso {S : E} {a b : C} (φ : a ⟶ b)
    [IsHomLift p (𝟙 S) φ] : IsCartesian p (𝟙 S) φ ↔ IsIso φ := by
  constructor
  · intro h
    exact isIso_of_vertical_isCartesian p (S := S) φ
  · intro h
    infer_instance

/-- VI.5.1, remark before VI.5.2: in a commutative square whose vertical arrows
are isomorphisms over identities, one `f`-morphism is cartesian iff the other is. -/
theorem isCartesian_iff_of_vertical_iso {R S : E} (f : R ⟶ S) {a a' b b' : C}
    (φ : a ⟶ b) (φ' : a' ⟶ b') (μ : a ≅ a') (ν : b ≅ b')
    [IsHomLift p (𝟙 R) μ.hom] [IsHomLift p (𝟙 S) ν.hom]
    [IsHomLift p f φ] [IsHomLift p f φ']
    (h : μ.hom ≫ φ' = φ ≫ ν.hom) :
    IsCartesian p f φ ↔ IsCartesian p f φ' := by
  have : IsHomLift p (𝟙 R) μ.inv := IsHomLift.lift_id_inv p R μ
  have : IsHomLift p (𝟙 S) ν.inv := IsHomLift.lift_id_inv p S ν
  have hφ_eq : φ = μ.hom ≫ φ' ≫ ν.inv := by
    calc
      φ = (φ ≫ ν.hom) ≫ ν.inv := by simp
      _ = (μ.hom ≫ φ') ≫ ν.inv := by rw [h]
      _ = μ.hom ≫ φ' ≫ ν.inv := by rw [Category.assoc]
  constructor
  · intro hφ
    refine ⟨?_⟩
    intro x ψ hψ
    have : IsHomLift p f (ψ ≫ ν.inv) := IsHomLift.comp_lift_id_right p f ψ ν.inv
    obtain ⟨χ, ⟨hχ, hχφ⟩, huniq⟩ := hφ.universal_property (ψ ≫ ν.inv)
    refine ⟨χ ≫ μ.hom, ⟨inferInstance, ?_⟩, ?_⟩
    · calc
        (χ ≫ μ.hom) ≫ φ' = χ ≫ μ.hom ≫ φ' := by rw [Category.assoc]
        _ = χ ≫ φ ≫ ν.hom := by rw [h]
        _ = (χ ≫ φ) ≫ ν.hom := by rw [Category.assoc]
        _ = (ψ ≫ ν.inv) ≫ ν.hom := by rw [hχφ]
        _ = ψ := by simp
    · intro τ ⟨hτ, hτφ⟩
      have : τ ≫ μ.inv = χ :=
        huniq (τ ≫ μ.inv) ⟨inferInstance, by
          calc
            (τ ≫ μ.inv) ≫ φ = τ ≫ μ.inv ≫ φ := by rw [Category.assoc]
            _ = τ ≫ μ.inv ≫ μ.hom ≫ φ' ≫ ν.inv := by rw [hφ_eq]
            _ = τ ≫ φ' ≫ ν.inv := by simp
            _ = (τ ≫ φ') ≫ ν.inv := by rw [Category.assoc]
            _ = ψ ≫ ν.inv := by rw [hτφ]⟩
      calc
        τ = (τ ≫ μ.inv) ≫ μ.hom := by simp
        _ = χ ≫ μ.hom := by rw [this]
  · intro hφ'
    refine ⟨?_⟩
    intro x ψ hψ
    have : IsHomLift p f (ψ ≫ ν.hom) := IsHomLift.comp_lift_id_right p f ψ ν.hom
    obtain ⟨χ, ⟨hχ, hχφ⟩, huniq⟩ := hφ'.universal_property (ψ ≫ ν.hom)
    refine ⟨χ ≫ μ.inv, ⟨inferInstance, ?_⟩, ?_⟩
    · calc
        (χ ≫ μ.inv) ≫ φ = χ ≫ μ.inv ≫ φ := by rw [Category.assoc]
        _ = χ ≫ μ.inv ≫ μ.hom ≫ φ' ≫ ν.inv := by rw [hφ_eq]
        _ = χ ≫ φ' ≫ ν.inv := by simp
        _ = (χ ≫ φ') ≫ ν.inv := by rw [Category.assoc]
        _ = (ψ ≫ ν.hom) ≫ ν.inv := by rw [hχφ]
        _ = ψ := by simp
    · intro τ ⟨hτ, hτφ⟩
      have : τ ≫ μ.hom = χ :=
        huniq (τ ≫ μ.hom) ⟨inferInstance, by
          calc
            (τ ≫ μ.hom) ≫ φ' = τ ≫ μ.hom ≫ φ' := by rw [Category.assoc]
            _ = τ ≫ φ ≫ ν.hom := by rw [h]
            _ = (τ ≫ φ) ≫ ν.hom := by rw [Category.assoc]
            _ = ψ ≫ ν.hom := by rw [hτφ]⟩
      calc
        τ = (τ ≫ μ.hom) ≫ μ.inv := by simp
        _ = χ ≫ μ.inv := by rw [this]

end SGA.SGA1.ExposeVI
