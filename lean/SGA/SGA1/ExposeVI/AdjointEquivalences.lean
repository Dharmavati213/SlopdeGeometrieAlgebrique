/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.LaxCoGrothendieck
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Opposites

/-!
# SGA 1, Exposé VI, VI.11 d): pairs of quasi-inverse adjoint functors; autodualities

Over the rigid connected groupoid `E` with two objects `a, b` (`Codiscrete Bool`, with
`f : a ⟶ b` and `g : b ⟶ a`), a normalized pseudofunctor is the same thing as two categories
`𝒳_a, 𝒳_b` with an adjoint equivalence `(G, F)`, `F = f^*`, `G = g^*`, `u = c_{g,f}` and
`v = c_{f,g}`; the triangle identities are the cocycle relation `B)` for `fgf` and `gfg`
(`Cleavage.IsNormalized.comparison_triangle`). Conversely (SGA: "it is easy to show that these
conditions suffice"), `laxFunctorOfEquivalence e` is the normalized pseudofunctor defined by an
equivalence `e : 𝒳_a ≌ 𝒳_b`: the relation `B)` for all sixteen composable triples reduces to the
triangle identities of `e`.

An *autoduality* of `𝒞` (`Autoduality`) is a functor `D : 𝒞 ⥤ 𝒞ᵒᵖ` with an isomorphism
`u : D°D ≅ 𝟭` such that `u` and `u°` make `(D, D°)` a pair of adjoint functors; SGA writes the
condition as `D(u(x)) = u(D(x))`, which (the two arrows pointing in opposite directions) means
that they are inverse to each other. `Autoduality.toEquivalence` is the resulting adjoint
equivalence `𝒞 ≌ 𝒞ᵒᵖ`, hence a normalized pseudofunctor with `𝒳_b = 𝒳_aᵒᵖ`.
-/

universe v u

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

namespace EquivalencePseudofunctor

variable {A B : Cat.{v, u}} (e : A ≌ B)

/-- The categories `𝒳_a = A` (over `false`) and `𝒳_b = B` (over `true`). -/
abbrev eqObj : Bool → Cat.{v, u}
  | false => A
  | true => B

/-- The inverse image functors: `f^* = e.inverse` for `f : a ⟶ b`, `g^* = e.functor` for
`g : b ⟶ a`, identities otherwise. -/
def eqMap : (T S : Bool) → eqObj (A := A) (B := B) S ⥤ eqObj (A := A) (B := B) T
  | false, false => 𝟭 A
  | true, true => 𝟭 B
  | false, true => e.inverse
  | true, false => e.functor

/-- The (identity) unit constraints. -/
def eqUnit : (S : Bool) → 𝟭 (eqObj (A := A) (B := B) S) ⟶ eqMap e S S
  | false => 𝟙 _
  | true => 𝟙 _

/-- The comparisons `c : map T S ⋙ map U T ⟶ map U S`: identities, except `u = e.unitInv` for
`fgf`-type and `v = e.counit` for `gfg`-type composites. -/
def eqComp : (U T S : Bool) → eqMap e T S ⋙ eqMap e U T ⟶ eqMap e U S
  | false, false, false => 𝟙 _
  | true, true, true => 𝟙 _
  | false, false, true => 𝟙 _
  | false, true, true => 𝟙 _
  | true, false, false => 𝟙 _
  | true, true, false => 𝟙 _
  | false, true, false => e.unitInv
  | true, false, true => e.counit

end EquivalencePseudofunctor

open EquivalencePseudofunctor in
/-- VI.11 d): the normalized pseudofunctor on the rigid connected groupoid with two objects defined
by an (adjoint) equivalence `e : 𝒳_a ≌ 𝒳_b`: `f^* = e.inverse`, `g^* = e.functor`,
`c_{g,f} = e.unitInv`, `c_{f,g} = e.counit`. -/
def laxFunctorOfEquivalence {A B : Cat.{v, u}} (e : A ≌ B) :
    LaxFunctor (LocallyDiscrete (Codiscrete Bool)ᵒᵖ) Cat.{v, u} :=
  laxFunctorOfComponents (fun S ↦ eqObj (A := A) (B := B) S.as)
    (fun {T S} _ ↦ eqMap e T.as S.as) (fun S ↦ eqUnit e S.as)
    (fun {U T S} _ _ ↦ eqComp e U.as T.as S.as)
    (fun {T S} _ ξ ↦ by
      obtain ⟨t⟩ := T
      obtain ⟨s⟩ := S
      cases t <;> cases s <;> simp [eqMap, eqUnit, eqComp] <;> rfl)
    (fun {T S} _ ξ ↦ by
      obtain ⟨t⟩ := T
      obtain ⟨s⟩ := S
      cases t <;> cases s <;> simp [eqMap, eqUnit, eqComp] <;> rfl)
    (fun {V U T S} _ _ _ ξ ↦ by
      obtain ⟨v⟩ := V
      obtain ⟨u⟩ := U
      obtain ⟨t⟩ := T
      obtain ⟨s⟩ := S
      cases v <;> cases u <;> cases t <;> cases s <;>
        simp [eqMap, eqComp, Equivalence.unitInv_app_inverse, Equivalence.counit_app_functor])

section

variable {A B : Cat.{v, u}} (e : A ≌ B)

/-- The arrow `f : a ⟶ b` of the two-object groupoid (`a = false`, `b = true`). -/
def codiscreteF : (⟨false⟩ : Codiscrete Bool) ⟶ ⟨true⟩ := ()

/-- The arrow `g : b ⟶ a` of the two-object groupoid. -/
def codiscreteG : (⟨true⟩ : Codiscrete Bool) ⟶ ⟨false⟩ := ()

/-- VI.11 d): `f^* = F` is the inverse of the equivalence. -/
theorem laxFunctorOfEquivalence_pullback_f :
    laxPullback (laxFunctorOfEquivalence e) codiscreteF = e.inverse := rfl

/-- VI.11 d): `g^* = G` is the functor of the equivalence. -/
theorem laxFunctorOfEquivalence_pullback_g :
    laxPullback (laxFunctorOfEquivalence e) codiscreteG = e.functor := rfl

/-- VI.11 d): `c_{g,f} : f^* g^* = FG ⟶ 𝟭` is `u = e.unitInv`. -/
theorem laxFunctorOfEquivalence_comparison_gf :
    laxComparison (laxFunctorOfEquivalence e) codiscreteG codiscreteF = e.unitInv := rfl

/-- VI.11 d): `c_{f,g} : g^* f^* = GF ⟶ 𝟭` is `v = e.counit`. -/
theorem laxFunctorOfEquivalence_comparison_fg :
    laxComparison (laxFunctorOfEquivalence e) codiscreteF codiscreteG = e.counit := rfl

/-- VI.11 d): the pseudofunctor defined by an equivalence is normalized (strictly unitary). -/
def strictlyUnitaryLaxFunctorOfEquivalence :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete (Codiscrete Bool)ᵒᵖ) Cat.{v, u} where
  toLaxFunctor := laxFunctorOfEquivalence e
  map_id S := by
    obtain ⟨⟨⟨s⟩⟩⟩ := S
    cases s <;> rfl
  mapId_eq_eqToHom S := by
    obtain ⟨⟨⟨s⟩⟩⟩ := S
    cases s <;> rfl

end

/-! ### Autodualities -/

/-- VI.11 d): an autoduality of `𝒞`: a functor `D : 𝒞 ⥤ 𝒞ᵒᵖ` and an isomorphism
`u : D°D ≅ 𝟭` (with `D° = D.leftOp`) such that `u` and `u°` make `(D, D°)` a pair of adjoint
functors. SGA writes the condition `D(u(x)) = u(D(x))`; the two arrows `D(u(x))` and
`u(D(x))°` point in opposite directions, and the condition means that they are inverse. -/
structure Autoduality (C : Type u) [Category.{v} C] where
  /-- The duality functor `D : 𝒞 ⥤ 𝒞ᵒᵖ`. -/
  D : C ⥤ Cᵒᵖ
  /-- The isomorphism `u : D°D ≅ 𝟭`. -/
  u : D ⋙ D.leftOp ≅ 𝟭 C
  compat (x : C) : (u.hom.app (unop (D.obj x))).op ≫ D.map (u.hom.app x) = 𝟙 (D.obj x)

namespace Autoduality

variable {C : Type u} [Category.{v} C] (A : Autoduality C)

/-- The counit `D D° ≅ 𝟭` of the autoduality, `u°`. -/
def counitIso : A.D.leftOp ⋙ A.D ≅ 𝟭 Cᵒᵖ :=
  NatIso.ofComponents (fun y ↦ (A.u.app (unop y)).op.symm)
    (fun {y y'} φ ↦ Quiver.Hom.unop_inj (by simpa using (A.u.inv.naturality φ.unop).symm))

theorem functor_unitIso_comp (x : C) :
    A.D.map (A.u.symm.hom.app x) ≫ A.counitIso.hom.app (A.D.obj x) = 𝟙 (A.D.obj x) := by
  have h := A.compat x
  have e₁ : A.D.map (A.u.inv.app x) = (A.u.hom.app (unop (A.D.obj x))).op := by
    rw [← cancel_mono (A.D.map (A.u.hom.app x)), ← A.D.map_comp, Iso.inv_hom_id_app,
      A.D.map_id, h]
    rfl
  have e₂ : (A.u.inv.app (unop (A.D.obj x))).op = A.D.map (A.u.hom.app x) := by
    rw [← cancel_epi ((A.u.hom.app (unop (A.D.obj x))).op), h, ← op_comp, Iso.inv_hom_id_app]
    rfl
  simp only [Iso.symm_hom, counitIso, NatIso.ofComponents_hom_app, Iso.op_inv, Iso.app_inv]
  rw [e₁, e₂]
  exact h

/-- VI.11 d): an autoduality is an adjoint equivalence `(D, D°) : 𝒞 ≌ 𝒞ᵒᵖ`. -/
def toEquivalence : C ≌ Cᵒᵖ :=
  CategoryTheory.Equivalence.mk' A.D A.D.leftOp A.u.symm A.counitIso A.functor_unitIso_comp

@[simp] theorem toEquivalence_functor : A.toEquivalence.functor = A.D := rfl

@[simp] theorem toEquivalence_inverse : A.toEquivalence.inverse = A.D.leftOp := rfl

/-- VI.11 d): an autoduality of `𝒞` defines a normalized pseudofunctor on the rigid connected
groupoid with two objects, with fibers `𝒞` and `𝒞ᵒᵖ`. -/
def strictlyUnitaryLaxFunctor :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete (Codiscrete Bool)ᵒᵖ) Cat.{v, u} :=
  strictlyUnitaryLaxFunctorOfEquivalence (A := Cat.of C) (B := Cat.of Cᵒᵖ) A.toEquivalence

end Autoduality

end SGA.SGA1.ExposeVI
