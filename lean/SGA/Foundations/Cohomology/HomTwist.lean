/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Serre

/-!
# Morphisms out of negative twists

* `CohomologyAux.unitHomAddEquiv`: `Hom(𝒪_X, G) ≅ Γ(X, G)`, `φ ↦ φ(1)`.
* `Scheme.LineBundle.homToModulesAddEquiv`: `Hom(L^{⊗-n}, F) ≅ Γ(X, F ⊗ L^{⊗n})` for a line bundle
  `L` (EGA 0_I 5.4.7; Hartshorne II.5.1 (b) and II.5.12). On `Proj A[xᵢ]` with `L = 𝒪(1)` this is
  `Hom(𝒪(-n), F) ≅ Γ(F(n))`, which turns global generation of `F(n)` into epimorphisms
  `⊕ 𝒪(-n) ↠ F` (EGA III 2.2.1 (i); Hartshorne II.5.18).
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

variable (X) in
/-- The global section `1` of `𝒪_X`, as a section of the module `𝒪_X`. -/
noncomputable def unitOne : Γ(unitModule X, ⊤) := (1 : Γ(X, ⊤))

/-- `Hom(𝒪_X, G) ≅ Γ(X, G)`, `φ ↦ φ(1)`, with inverse `homOfSection`. -/
noncomputable def unitHomAddEquiv (G : X.Modules) : (unitModule X ⟶ G) ≃+ Γ(G, ⊤) where
  toFun φ := φ.app ⊤ (unitOne X)
  invFun g := homOfSection G g
  left_inv φ := by
    refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
    ext r
    let r' : Γ(X, V) := r
    let one' : Γ(unitModule X, V) := (1 : Γ(X, V))
    have h1 : φ.app V ((unitModule X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (unitOne X)) =
        G.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.app ⊤ (unitOne X)) :=
      hom_app_presheaf_map φ (homOfLE le_top) (unitOne X)
    have h2 : (unitModule X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (unitOne X) = one' :=
      map_one (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
    have h3 : φ.app V (r' • one') = r' • φ.app V one' := Scheme.Modules.Hom.app_smul φ r' one'
    have h4 : r' • one' = r := mul_one r'
    change (homOfSection G (φ.app ⊤ (unitOne X))).app V r = φ.app V r
    refine (homOfSection_app G _ V r).trans ?_
    rw [h2] at h1
    rw [← h1]
    exact h3.symm.trans (congrArg _ h4)
  right_inv g := by
    change (homOfSection G g).app ⊤ (1 : Γ(X, ⊤)) = g
    rw [homOfSection_app, one_smul, modules_map_self]
  map_add' _ _ := rfl

lemma unitHomAddEquiv_apply (G : X.Modules) (φ : unitModule X ⟶ G) :
    unitHomAddEquiv G φ = φ.app ⊤ (unitOne X) :=
  rfl

lemma unitHomAddEquiv_symm_apply (G : X.Modules) (g : Γ(G, ⊤)) :
    (unitHomAddEquiv G).symm g = homOfSection G g :=
  rfl

/-- Composition with an isomorphism, as an additive equivalence of hom groups. -/
noncomputable def isoHomAddEquiv {M M' N : X.Modules} (e : M ≅ M') : (M ⟶ N) ≃+ (M' ⟶ N) where
  toFun φ := e.inv ≫ φ
  invFun ψ := e.hom ≫ ψ
  left_inv φ := by simp
  right_inv ψ := by simp
  map_add' φ ψ := Preadditive.comp_add _ _ _ _ _ _

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- Twisting by `L^{⊗n}` on hom groups, an additive equivalence (twisting is an equivalence of
categories). -/
noncomputable def twistHomAddEquiv (n : ℤ) (M N : X.Modules) :
    (M ⟶ N) ≃+ (L.twist M n ⟶ L.twist N n) where
  toFun φ := L.twistMap n φ
  invFun ψ := (twistFunctor X L n).preimage ψ
  left_inv φ := (twistFunctor X L n).preimage_map φ
  right_inv ψ := (twistFunctor X L n).map_preimage ψ
  map_add' φ ψ := L.twistMap_add n φ ψ

/-- `L^{⊗-n} ⊗ L^{⊗n} ≅ 𝒪_X`. -/
noncomputable def twistNegTwistIso (n : ℤ) :
    L.twist (L.toModules (-n)) n ≅ CohomologyAux.unitModule X :=
  L.twistTwistIso (CohomologyAux.unitModule X) (-n) n ≪≫
    eqToIso (congrArg (L.twist (CohomologyAux.unitModule X)) (neg_add_cancel n)) ≪≫
    (L.twistZeroIso (CohomologyAux.unitModule X)).symm

/-- **`Hom(L^{⊗-n}, F) ≅ Γ(X, F ⊗ L^{⊗n})`** (EGA 0_I 5.4.7; Hartshorne II.5.1 (b)): a morphism
`L^{⊗-n} ⟶ F` corresponds to the global section of `F ⊗ L^{⊗n}` image of `1` under its twist by
`L^{⊗n}`. On `Proj A[xᵢ]` with `L = 𝒪(1)`: `Hom(𝒪(-n), F) ≅ Γ(F(n))`. -/
noncomputable def homToModulesAddEquiv (F : X.Modules) (n : ℤ) :
    (L.toModules (-n) ⟶ F) ≃+ Γ(L.twist F n, ⊤) :=
  (L.twistHomAddEquiv n _ F).trans
    ((CohomologyAux.isoHomAddEquiv (L.twistNegTwistIso n)).trans
      (CohomologyAux.unitHomAddEquiv (L.twist F n)))

lemma homToModulesAddEquiv_apply (F : X.Modules) (n : ℤ) (φ : L.toModules (-n) ⟶ F) :
    L.homToModulesAddEquiv F n φ =
      ((L.twistNegTwistIso n).inv ≫ L.twistMap n φ).app ⊤ (CohomologyAux.unitOne X) :=
  rfl

end AlgebraicGeometry.Scheme.LineBundle

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

variable {σ : Type*} {A : Type u} [CommRing A]

/-- **`Hom(𝒪(-n), F) ≅ Γ(F(n))`** on `Proj A[xᵢ]` (EGA II 2.5.14 for the twists `𝒪(n)`;
Hartshorne II.5.12). -/
noncomputable def homTwistAddEquiv (F : (Proj (homogeneousSubmodule σ A)).Modules) (n : ℤ) :
    (twist σ A (-n) ⟶ F) ≃+ Γ((twistingBundle σ A).twist F n, ⊤) :=
  (twistingBundle σ A).homToModulesAddEquiv F n

end AlgebraicGeometry.projectiveSpace
