/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.Restrict
import SGA.Foundations.Differentials.SheafHom

/-!
# Derivations on an open subset

For a morphism of schemes `f : X ⟶ Y`, an `𝒪_X`-module `M` and an open `Z ⊆ X`,
`Scheme.Modules.DerivationOn M f Z` is the type of `f⁻¹ 𝒪_Y`-derivations of `𝒪_X|_Z` into
`M|_Z`, given as compatible families of derivations `Γ(X, V) → Γ(M, V)` for the opens `V ⊆ Z`.
These form a sheaf in `Z`: compatible local derivations glue (`DerivationOn.glue`), and
`DerivationOn M f ⊤` is `M.Derivation f` (`DerivationOn.topEquiv`). We also transport derivations
along open immersions (`DerivationOn.toOpenImmersion`, `DerivationOn.ofOpenImmersion`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (M : X.Modules) (f : X ⟶ Y)

/-- The `f⁻¹ 𝒪_Y`-derivations of `𝒪_X|_Z` into `M|_Z`, as compatible families of derivations
`Γ(X, V) → Γ(M, V)` for the opens `V ⊆ Z`. -/
@[ext]
structure DerivationOn (Z : X.Opens) where
  /-- The derivation on sections over `V ⊆ Z`. -/
  app (V : X.Opens) (hV : V ≤ Z) : Γ(X, V) →+ Γ(M, V)
  app_mul (V : X.Opens) (hV : V ≤ Z) (a b : Γ(X, V)) :
    app V hV (a * b) = a • app V hV b + b • app V hV a
  naturality {V W : X.Opens} (hWV : W ≤ V) (hV : V ≤ Z) (a : Γ(X, V)) :
    app W (hWV.trans hV) (X.presheaf.map (homOfLE hWV).op a) =
      M.presheaf.map (homOfLE hWV).op (app V hV a)
  app_appLE (T : Y.Opens) (s : Γ(Y, T)) (V : X.Opens) (hV : V ≤ Z) (e : V ≤ f ⁻¹ᵁ T) :
    app V hV (f.appLE T V e s) = 0

namespace DerivationOn

variable {M f} {Z : X.Opens}

/-- The restriction of a derivation on `Z` to an open `Z' ⊆ Z`. -/
@[simps]
def restrict (E : DerivationOn M f Z) {Z' : X.Opens} (h : Z' ≤ Z) : DerivationOn M f Z' where
  app V hV := E.app V (hV.trans h)
  app_mul V hV := E.app_mul V (hV.trans h)
  naturality hWV hV := E.naturality hWV (hV.trans h)
  app_appLE T s V hV := E.app_appLE T s V (hV.trans h)

/-- A derivation of `𝒪_X` gives a derivation on every open. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.Modules.Derivation.toDerivationOn (D : M.Derivation f)
    (Z : X.Opens) : DerivationOn M f Z where
  app V _ := D.app V
  app_mul V _ := D.app_mul V
  naturality hWV _ := D.app_map (homOfLE hWV)
  app_appLE _ s _ _ e := D.app_appLE e s

/-- A derivation on `⊤` is a derivation of `𝒪_X`. -/
@[simps]
def toDerivation (E : DerivationOn M f ⊤) : M.Derivation f where
  d {V} := E.app V.unop le_top
  d_mul {V} a b := E.app_mul V.unop le_top a b
  d_map {V W} i a := E.naturality i.unop.le le_top a
  d_app {T} s := by
    have := E.app_appLE T.unop s (f ⁻¹ᵁ T.unop) le_top le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this

/-- `DerivationOn M f ⊤` is `M.Derivation f`. -/
def topEquiv : DerivationOn M f ⊤ ≃ M.Derivation f where
  toFun E := E.toDerivation
  invFun D := D.toDerivationOn ⊤
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma toDerivation_app (E : DerivationOn M f ⊤) (V : X.Opens) (a : Γ(X, V)) :
    E.toDerivation.app V a = E.app V le_top a :=
  rfl

section glue

variable {ι : Type u} {U : ι → X.Opens} (E : ∀ i, DerivationOn M f (U i))
  (hE : ∀ i j, (E i).restrict (inf_le_left : U i ⊓ U j ≤ U i) =
    (E j).restrict (inf_le_right : U i ⊓ U j ≤ U j))

include hE in
lemma existsUnique_glue_app (V : X.Opens) (hV : V ≤ iSup U) (a : Γ(X, V)) :
    ∃! s : Γ(M, V), ∀ i, M.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s =
      (E i).app (V ⊓ U i) inf_le_right (X.presheaf.map (homOfLE inf_le_left).op a) := by
  refine existsUnique_gluing_inf U hV _ fun i j ↦ ?_
  rw [← (E i).naturality, ← (E j).naturality, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  have h := congr(DerivationOn.app $(hE i j) ((V ⊓ U i) ⊓ (V ⊓ U j))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
  exact congr($h (X.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op a))

/-- The glued section. -/
def glueApp (V : X.Opens) (hV : V ≤ iSup U) (a : Γ(X, V)) : Γ(M, V) :=
  (existsUnique_glue_app E hE V hV a).exists.choose

lemma glueApp_spec (V : X.Opens) (hV : V ≤ iSup U) (a : Γ(X, V)) (i : ι) :
    M.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (glueApp E hE V hV a) =
      (E i).app (V ⊓ U i) inf_le_right (X.presheaf.map (homOfLE inf_le_left).op a) :=
  (existsUnique_glue_app E hE V hV a).exists.choose_spec i

lemma glueApp_eq (V : X.Opens) (hV : V ≤ iSup U) (a : Γ(X, V)) (s : Γ(M, V))
    (hs : ∀ i, M.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s =
      (E i).app (V ⊓ U i) inf_le_right (X.presheaf.map (homOfLE inf_le_left).op a)) :
    glueApp E hE V hV a = s :=
  (existsUnique_glue_app E hE V hV a).unique (fun i ↦ glueApp_spec E hE V hV a i) hs

/-- Compatible derivations on the members of an open cover glue. -/
def glue : DerivationOn M f (iSup U) where
  app V hV :=
    { toFun := glueApp E hE V hV
      map_zero' := glueApp_eq E hE V hV _ _ fun i ↦ by rw [map_zero, map_zero, map_zero]
      map_add' a b := glueApp_eq E hE V hV _ _ fun i ↦ by
        rw [map_add, glueApp_spec, glueApp_spec, map_add, map_add] }
  app_mul V hV a b := by
    change glueApp E hE V hV (a * b) = a • glueApp E hE V hV b + b • glueApp E hE V hV a
    refine glueApp_eq E hE V hV _ _ fun i ↦ ?_
    rw [map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, glueApp_spec, glueApp_spec,
      map_mul, app_mul]
  naturality {V W} hWV hV a := by
    refine glueApp_eq E hE W (hWV.trans hV) _ _ fun i ↦ ?_
    change M.presheaf.map (homOfLE inf_le_left).op
      (M.presheaf.map (homOfLE hWV).op (glueApp E hE V hV a)) = _
    rw [presheaf_map_map M _ _ (homOfLE (inf_le_inf_right (U i) hWV)) (homOfLE inf_le_left),
      glueApp_spec, ← (E i).naturality (inf_le_inf_right (U i) hWV),
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  app_appLE T s V hV e := by
    refine (glueApp_eq E hE V hV _ 0 fun i ↦ ?_)
    rw [map_zero, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    exact ((E i).app_appLE T s _ _ _).symm

lemma glue_restrict (i : ι) : (glue E hE).restrict (le_iSup U i) = E i := by
  ext V hV a
  change glueApp E hE V (hV.trans (le_iSup U i)) a = _
  have e : V ⊓ U i = V := inf_eq_left.mpr hV
  apply presheaf_map_injective_of_eq M (homOfLE (inf_le_left : V ⊓ U i ≤ V)) e
  rw [glueApp_spec, ← (E i).naturality]

lemma eq_glue (F : DerivationOn M f (iSup U)) (hF : ∀ i, F.restrict (le_iSup U i) = E i) :
    F = glue E hE := by
  ext V hV a
  refine (glueApp_eq E hE V hV a _ fun i ↦ ?_).symm
  rw [← F.naturality, ← hF i]
  rfl

end glue

end DerivationOn

end AlgebraicGeometry.Scheme.Modules
