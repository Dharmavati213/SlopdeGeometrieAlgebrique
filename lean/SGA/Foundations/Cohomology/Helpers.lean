/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Small helper lemmas for the cohomology files

Lemmas about restriction maps of the structure sheaf and of `𝒪_X`-modules, kept in the namespace
`AlgebraicGeometry.CohomologyAux` to avoid clashes with other developments.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

lemma presheaf_map_map {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁)
    (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma presheaf_map_map' {V₁ V₂ V₃ V₂' : X.Opens}
    (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₁' : V₂' ≤ V₁) (h₂' : V₃ ≤ V₂') (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE h₂').op (X.presheaf.map (homOfLE h₁').op r) := by
  rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map]

@[simp]
lemma presheaf_map_self {V : X.Opens} (h : V ≤ V)
    (a : Γ(X, V)) : X.presheaf.map (homOfLE h).op a = a := by
  rw [show homOfLE h = 𝟙 V from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]

lemma presheaf_map_injective_of_eq {V W : X.Opens}
    (h : W = V) :
    Function.Injective (X.presheaf.map (homOfLE h.le).op) := by
  intro a b hab
  have := congrArg (X.presheaf.map (homOfLE h.ge).op) hab
  rwa [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map,
    CohomologyAux.presheaf_map_self, CohomologyAux.presheaf_map_self] at this

lemma modules_map_self (M : X.Modules) {V : X.Opens} (h : V ≤ V)
    (a : Γ(M, V)) : M.presheaf.map (homOfLE h).op a = a := by
  rw [show homOfLE h = 𝟙 V from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma modules_map_injective_of_eq (M : X.Modules) {V W : X.Opens}
    (h : W = V) : Function.Injective (M.presheaf.map (homOfLE h.le).op) := by
  intro a b hab
  have := congrArg (M.presheaf.map (homOfLE h.ge).op) hab
  rwa [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply,
    CohomologyAux.modules_map_self, CohomologyAux.modules_map_self] at this

lemma hom_app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V)
    (x : Γ(M, V)) : φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

end AlgebraicGeometry.CohomologyAux
