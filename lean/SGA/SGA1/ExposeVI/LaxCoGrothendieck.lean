/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Cleavage
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.IsoCat

/-!
# SGA 1, Exposé VI, VI.8: the cloven category defined by a pseudofunctor `Eᵒᵖ → Cat`

SGA's *pseudofunctor* `Eᵒᵖ → Cat` (VI.8, "one should say, a normalized pseudofunctor") is the
datum a) of categories `𝒳(S)`, b) of functors `f^* : 𝒳(S) ⥤ 𝒳(T)` for `f : T ⟶ S`, and c) of
homomorphisms `c_{f,g} : g^* f^* ⟶ (fg)^*`, satisfying `A′)` and `B)`. The `c_{f,g}` are **not**
required to be invertible: the pseudofunctors of VI.8 are the normalized cloven categories, which
need not be fibered (VI.7.2). In mathlib's language this is a *strictly unitary lax functor*
`LocallyDiscrete Eᵒᵖ ⥤ᴸ Cat` (`mapComp` is `c`, and `mapId` is an identity); a lax functor
without the normalization corresponds to SGA's N.B. at the end of VI.7 (an extra datum
`(𝟙_S)^* ⟶ 𝟭` — here its inverse `𝟭 ⟶ (𝟙_S)^*`).

* `laxFunctorOfComponents` builds such a lax functor from the data a), b), c) and the relations
  A), B) written componentwise;
* `LaxCoGrothendieck F` is SGA's construction of VI.8: objects `(S, ξ)` with `ξ ∈ 𝒳(S)`, arrows
  `(T, η) ⟶ (S, ξ)` the pairs `(f, u : η ⟶ f^* ξ)`, composed by `u ∘ v = c_{f,g}(ξ) · g^*(u) · v`.
  Point 1) (associativity) uses `B)`, point 2) (units) uses `A)`; this works for every lax
  functor. For a strictly unitary `F` we prove 3) `h_f(η̄, ξ̄) ≃ Hom_f(η̄, ξ̄)`, 4) the fibers are
  isomorphic to the `𝒳(S)`, 5) the transports `(f, 𝟙)` form a normalized cleavage whose inverse
  image functors are the `f^*`, and 6) its comparison morphisms are the given `c_{f,g}`.
-/

universe w v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite Bicategory

variable {E : Type u₁} [Category.{v₁} E]

/-! ### Lax functors `Eᵒᵖ → Cat` from components -/

section Components

variable (obj : E → Cat.{v₂, u₂}) (map : ∀ {T S : E} (_ : T ⟶ S), obj S ⥤ obj T)
  (unit : ∀ S, 𝟭 (obj S) ⟶ map (𝟙 S))
  (comp : ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T), map f ⋙ map g ⟶ map (g ≫ f))

/-- VI.7–VI.8: a lax functor `Eᵒᵖ → Cat` given componentwise by the categories `obj S`, the
functors `f^* = map f`, the unit `𝟭 ⟶ (𝟙_S)^*` and the comparisons `c_{f,g} : g^* f^* ⟶ (fg)^*`,
subject to the unit relations (SGA's `A)`) and the cocycle relation `B)`. -/
@[reducible]
def laxFunctorOfComponents
    (unit_comp : ∀ {T S : E} (f : T ⟶ S) (ξ : obj S),
      (map f).map ((unit S).app ξ) ≫ (comp (𝟙 S) f).app ξ = eqToHom (by simp))
    (comp_unit : ∀ {T S : E} (f : T ⟶ S) (ξ : obj S),
      (unit T).app ((map f).obj ξ) ≫ (comp f (𝟙 T)).app ξ = eqToHom (by simp))
    (assoc : ∀ {V U T S : E} (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U) (ξ : obj S),
      (comp g h).app ((map f).obj ξ) ≫ (comp f (h ≫ g)).app ξ =
        (map h).map ((comp f g).app ξ) ≫ (comp (g ≫ f) h).app ξ ≫
          eqToHom (by rw [Category.assoc])) :
    LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂} where
  obj S := obj S.as.unop
  map φ := Cat.Hom.ofFunctor (map φ.as.unop)
  map₂ {a b φ ψ} η := eqToHom (by obtain rfl := LocallyDiscrete.eq_of_hom η; rfl)
  map₂_id _ := rfl
  map₂_comp _ _ := by simp
  mapId a := Cat.Hom₂.ofNatTrans (unit a.as.unop)
  mapComp φ ψ := Cat.Hom₂.ofNatTrans (comp φ.as.unop ψ.as.unop)
  mapComp_naturality_left η g := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    simp
  mapComp_naturality_right f _ _ η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    simp
  map₂_associator f g h := by
    ext ξ
    simpa [Cat.eqToHom_app] using (assoc f.as.unop g.as.unop h.as.unop ξ).symm
  map₂_leftUnitor f := by
    ext ξ
    simpa [Cat.eqToHom_app] using (unit_comp f.as.unop ξ).symm
  map₂_rightUnitor f := by
    ext ξ
    simpa [Cat.eqToHom_app] using (comp_unit f.as.unop ξ).symm

end Components

/-! ### Componentwise relations of a lax functor `Eᵒᵖ → Cat` -/

section LaxFunctor

variable (F : LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂})

/-- The inverse image functor `f^* : F(S) ⥤ F(T)` of a lax functor `Eᵒᵖ → Cat`. -/
abbrev laxPullback {T S : E} (f : T ⟶ S) : F.obj ⟨op S⟩ ⥤ F.obj ⟨op T⟩ :=
  (F.map f.op.toLoc).toFunctor

/-- The comparison `c_{f,g} : g^* f^* ⟶ (fg)^*` of a lax functor `Eᵒᵖ → Cat`. -/
abbrev laxComparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    laxPullback F f ⋙ laxPullback F g ⟶ laxPullback F (g ≫ f) :=
  (F.mapComp f.op.toLoc g.op.toLoc).toNatTrans

/-- The unit `𝟭 ⟶ (𝟙_S)^*` of a lax functor `Eᵒᵖ → Cat`. -/
abbrev laxUnit (S : E) : 𝟭 (F.obj ⟨op S⟩) ⟶ laxPullback F (𝟙 S) :=
  (F.mapId ⟨op S⟩).toNatTrans

theorem laxMap₂_app {a b : LocallyDiscrete Eᵒᵖ} {φ ψ : a ⟶ b} (η : φ ⟶ ψ) (ξ : F.obj a) :
    (F.map₂ η).toNatTrans.app ξ =
      eqToHom (by obtain rfl := LocallyDiscrete.eq_of_hom η; rfl) := by
  obtain rfl := LocallyDiscrete.eq_of_hom η
  obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
  simp

/-- `A)`, first relation: `f^*(ε_S(ξ)) ≫ c_{𝟙_S, f}(ξ)` is the identification
`f^* ξ = (f 𝟙)^* ξ`. -/
theorem laxUnit_comparison {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (laxPullback F f).map ((laxUnit F S).app ξ) ≫ (laxComparison F (𝟙 S) f).app ξ =
      eqToHom (by simp) := by
  have := F.map₂_leftUnitor_app f.op.toLoc ξ
  rw [laxMap₂_app] at this
  exact this.symm

/-- `A)`, second relation: `ε_T(f^* ξ) ≫ c_{f, 𝟙_T}(ξ)` is the identification
`f^* ξ = (𝟙 f)^* ξ`. -/
theorem laxUnit_comparison' {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (laxUnit F T).app ((laxPullback F f).obj ξ) ≫ (laxComparison F f (𝟙 T)).app ξ =
      eqToHom (by simp) := by
  have := F.map₂_rightUnitor_app f.op.toLoc ξ
  rw [laxMap₂_app] at this
  exact this.symm

/-- `B)`: the cocycle relation `c_{f,gh} · c_{g,h}(f^* ξ) = c_{fg,h} · h^*(c_{f,g}(ξ))`. -/
theorem laxComparison_assoc {V U T S : E} (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U)
    (ξ : F.obj ⟨op S⟩) :
    (laxComparison F g h).app ((laxPullback F f).obj ξ) ≫ (laxComparison F f (h ≫ g)).app ξ =
      (laxPullback F h).map ((laxComparison F f g).app ξ) ≫
        (laxComparison F (g ≫ f) h).app ξ ≫ eqToHom (by simp) := by
  have := F.mapComp_assoc_right_app f.op.toLoc g.op.toLoc h.op.toLoc ξ
  rw [laxMap₂_app] at this
  exact this

end LaxFunctor

/-! ### VI.8: the category defined by a lax functor -/

/-- VI.8: the objects `(S, ξ)`, `ξ ∈ F(S)`, of the category defined by a (lax) pseudofunctor
`F : Eᵒᵖ → Cat` (SGA's `𝒳_∘ = ∐_S Ob 𝒳(S)`). -/
@[ext]
structure LaxCoGrothendieck (F : LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}) where
  /-- The object `S` of `E`. -/
  base : E
  /-- The object `ξ` of `F(S)`. -/
  fiber : F.obj ⟨op base⟩

namespace LaxCoGrothendieck

variable {F : LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}}

/-- VI.8: an arrow `(T, η) ⟶ (S, ξ)` is an arrow `f : T ⟶ S` of `E` together with an element of
`h_f(η̄, ξ̄) = Hom_{F(T)}(η, f^* ξ)`. -/
structure Hom (X Y : LaxCoGrothendieck F) where
  /-- The arrow `f` of `E`. -/
  base : X.base ⟶ Y.base
  /-- The arrow `η ⟶ f^* ξ` of `F(T)`. -/
  fiber : X.fiber ⟶ (laxPullback F base).obj Y.fiber

/-- VI.8: identities are `(𝟙, ε)` and composition is `u ∘ v = c_{f,g}(ξ) · g^*(u) · v`. -/
@[simps! id_base id_fiber comp_base comp_fiber]
instance categoryStruct : CategoryStruct (LaxCoGrothendieck F) where
  Hom := Hom
  id X := ⟨𝟙 X.base, (laxUnit F X.base).app X.fiber⟩
  comp {_ _ Z} f g := ⟨f.base ≫ g.base,
    f.fiber ≫ (laxPullback F f.base).map g.fiber ≫ (laxComparison F g.base f.base).app Z.fiber⟩

@[ext (iff := false)]
theorem Hom.ext {X Y : LaxCoGrothendieck F} (f g : X ⟶ Y) (h₁ : f.base = g.base)
    (h₂ : f.fiber = g.fiber ≫ eqToHom (by rw [h₁])) : f = g := by
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  obtain rfl : fb = gb := h₁
  obtain rfl : ff = gf := by simpa using h₂
  rfl

/-- VI.8 1), 2): SGA's composition is associative and unital (using `B)` and `A)`), so the
construction defines a category. -/
instance category : Category (LaxCoGrothendieck F) where
  id_comp {X Y} f := by
    refine Hom.ext _ _ (Category.id_comp _) ?_
    simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber, categoryStruct_id_base]
    rw [← Category.assoc, ← (laxUnit F X.base).naturality f.fiber, Category.assoc,
      laxUnit_comparison']
    rfl
  comp_id {X Y} f := by
    refine Hom.ext _ _ (Category.comp_id _) ?_
    simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber, categoryStruct_id_base]
    rw [laxUnit_comparison]
  assoc {X Y Z W} f g h := by
    refine Hom.ext _ _ (Category.assoc _ _ _) ?_
    simp only [categoryStruct_comp_fiber, categoryStruct_comp_base, Functor.map_comp,
      Category.assoc]
    have hn := (laxComparison F g.base f.base).naturality_assoc h.fiber
      ((laxComparison F h.base (f.base ≫ g.base)).app W.fiber)
    simp only [Functor.comp_map] at hn
    rw [← hn, laxComparison_assoc]

variable (F) in
/-- VI.8 3): the projection `(S, ξ) ↦ S`. -/
@[simps]
abbrev forget : LaxCoGrothendieck F ⥤ E where
  obj X := X.base
  map f := f.base

end LaxCoGrothendieck

end SGA.SGA1.ExposeVI
