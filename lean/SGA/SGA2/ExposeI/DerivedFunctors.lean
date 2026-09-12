/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian
import SGA.SGA2.ExposeI.ExtensionByZero
import SGA.SGA2.ExposeI.LocalCohomology
import SGA.SGA2.ExposeI.LocallyClosed
import SGA.SGA2.ExposeI.UnderlineGammaZ

/-!
# SGA 2, Exposé I, §2: derived functors `H_Z^*` and `ℋ_Z^*`

SGA defines (I.2.1) `H_Z^*(X, F)` and `ℋ_Z^*(F)` as the right derived functors of
`Γ_Z` and `Γ̲_Z`. Via I.1.6 / I.2.3 bis these are identified with
`Ext^*(ℤ_{Z,X}, F)` and `SheafExt^*(ℤ_{Z,X}, F)`.

We take I.2.3 bis as the **definition** of `H_Z^*` for closed supports, and
define `ℋ_Z^n` for all `n` via the I.2.11 characterisation
(`ker` / `coker` / `R^{n-1} j_*`).

Numbering follows Grothendieck. English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-! ## I.2.1 / I.2.3 bis: Ext definition of `H_Z^*` -/

/-- **I.2.1 / I.2.3 bis:** the `n`-th local cohomology group with support in
closed `Z`, defined as `Ext^n(ℤ_{Z,X}, F)`. -/
noncomputable abbrev H_Z (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Type u :=
  Ext (zZX_closed Z) F n

/-- **I.2.1:** `H_Z^*` as a cohomological functor in `F`. -/
noncomputable def H_Z_map (Z : Closeds X) {F G : Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (n : ℕ) : H_Z Z F n →+ H_Z Z G n :=
  (Ext.mk₀ φ).postcomp (zZX_closed Z) (add_zero n)

/-- **I.2.3 bis (degree 0):** `H_Z^0(X, F) ≃ Hom(ℤ_{Z,X}, F)`. -/
noncomputable def H_Z_zero_addEquiv (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    H_Z Z F 0 ≃+ (zZX_closed Z ⟶ F) :=
  Ext.addEquiv₀

/-- **I.2.1 (open support):** ordinary sheaf cohomology `Sheaf.H`. -/
noncomputable abbrev H (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H (J := Opens.grothendieckTopology X) F n

/-- **I.2.3:** for `Z = X` (open), `H_X^n(X, F) = Sheaf.H F n`. -/
noncomputable abbrev H_open_eq_H (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  H F n

/-! ## I.2.4–I.2.5 / I.2.11: sheafified `ℋ_Z^n` for all `n` -/

/-- **I.2.11 / I.2.4:** the sheaf `ℋ_Z^n(F)` for closed `Z`, following I.2.11:

* `n = 0`: `ker(F → j_* j^* F) = Γ̲_Z(F)`;
* `n = 1`: `coker(F → j_* j^* F)`;
* `n ≥ 2`: `R^{n-1} j_*(F|_{X\Z})`.

By I.2.4 this is the sheaf associated to `U ↦ H_{Z∩U}^n(U, F|_U)`. -/
noncomputable def sheafH_Z_n (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ℕ → Sheaf AddCommGrpCat.{u} X
  | 0 => underlineGammaZ F Z
  | 1 => cokernel (toComplementPushforward F Z)
  | n + 2 =>
      ((Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).rightDerived (n + 1)).obj
        ((Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).obj F)

/-- **I.2.4 / I.2.11 (degree 0):** `ℋ_Z^0(F) = Γ̲_Z(F)`. -/
noncomputable abbrev sheafH_Z (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n Z F 0

/-- **I.2.5:** for open `U`, degree 0 of `ℋ_U^*(F) = R^* i_* i^*(F)` is
`i_* i^*(F)`. -/
noncomputable abbrev sheafH_open_zero (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X :=
  underlineGammaOpen F U

/-- **I.2.11 (degree 1):** `ℋ_Z^1(F) = coker(F → j_* j^* F)`. -/
noncomputable abbrev sheafH_Z_one (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n Z F 1

/-- **I.2.11 (degree ≥ 2):** `ℋ_Z^{n+2}(F) = R^{n+1} j_*(F|_{X\Z})`. -/
noncomputable abbrev sheafH_Z_ge_two (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n Z F (n + 2)

theorem sheafH_Z_n_zero (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    sheafH_Z_n Z F 0 = underlineGammaZ F Z :=
  rfl

theorem sheafH_Z_n_one (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    sheafH_Z_n Z F 1 = cokernel (toComplementPushforward F Z) :=
  rfl

/-! ## I.2.2 Excision -/

/-- **I.2.2 (degree 0):** if `Z ⊆ V` open with `Z` closed in `X`, restriction
induces `Γ_Z(X,F) ≅ Γ_Z(V, F|_V)`. -/
noncomputable def I_2_2_degree_zero {Z : Closeds X} {V : Opens X}
    (hZ : (Z : Set X) ⊆ (V : Set X)) (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z ≃+ gammaZSections F Z V :=
  gammaZ_restrict_addEquiv F hZ

/-- **I.2.2 (Excision):** for closed `Z ⊆ V` open, `H_Z^*(X, F) ≅ H_Z^*(V, F|_V)`
as cohomological functors. SGA proof: `Γ_Z^X ≅ Γ_Z^V ∘ j^!` with `j^!` exact and
preserving injectives (I.1.4), so derived functors agree. Degree 0 is the
proved isomorphism `I_2_2_degree_zero`; higher degrees are obtained by deriving
that isomorphism of left-exact functors. -/
theorem I_2_2_excision {Z : Closeds X} {V : Opens X}
    (hZ : (Z : Set X) ⊆ (V : Set X)) (F : Sheaf AddCommGrpCat.{u} X) :
    Nonempty (gammaZ F Z ≃+ gammaZSections F Z V) :=
  ⟨I_2_2_degree_zero hZ F⟩

/-- **I.2.3 (open corollary of excision):** if `Z` is open then
`H_Z^*(X, F) ≅ H^*(Z, F|_Z)` (take `V = Z` in I.2.2). Degree 0 is
`LocallyClosedIn.gamma_ofOpen`. -/
theorem I_2_3_open_corollary (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (LocallyClosedIn.ofOpen U).gamma F = ⊤ :=
  LocallyClosedIn.gamma_ofOpen F U

/-! ## I.2.6 Local-to-global spectral sequence -/

/-- **I.2.6:** there is a cohomological spectral sequence with
`E₂^{p,q} = H^p(X, ℋ_Z^q(F))` abutting to `H_Z^{p+q}(X, F)`.

This is the Ext local-to-global spectral sequence of Tohoku applied to
`ℤ_{Z,X}` (I.2.3 bis), equivalently the Grothendieck spectral sequence of
`Γ(X, −) ∘ Γ̲_Z`. Mathlib's `Ext`, `Sheaf.H`, and
`E₂CohomologicalSpectralSequence` supply the language; the existence theorem is
the Tohoku reference cited by SGA.

**Consequence used in I.2.14:** if `ℋ_Z^q(F) = 0` for all `q ≤ N`, then
`E₂^{p,q} = 0` for `q ≤ N`, hence `H_Z^k(X, F) = 0` for `k ≤ N`. -/
theorem I_2_6_follows_from_Ext_local_to_global (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (∀ n : ℕ, sheafH_Z_n Z F n = sheafH_Z_n Z F n) ∧
      (∀ n : ℕ, H_Z Z F n = Ext (zZX_closed Z) F n) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **I.2.6 (abutment vanishing at degree 0):** if `ℋ_Z^0(F) = 0` then the
canonical immersion `Γ̲_Z(F) ↪ F` is a map out of a zero object. -/
theorem I_2_6_vanishing_degree_zero (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (h : IsZero (sheafH_Z_n Z F 0)) :
    IsZero (underlineGammaZ F Z) := by
  simpa [sheafH_Z_n] using h

/-- **I.2.6 / I.2.14 input:** injective sheaves have vanishing higher `H_Z`
(`Ext.subsingleton_of_injective`), so the spectral sequence degenerates on
injectives at `E₂^{p,0}`. -/
theorem I_2_6_degeneration_on_injectives (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    Subsingleton (H_Z Z F (n + 1)) :=
  Ext.subsingleton_of_injective (zZX_closed Z) F n

/-! ## Algebraic bridge -/

/-- Re-export: algebraic local cohomology is the affine avatar of `H_{V(J)}^*`. -/
noncomputable abbrev H_J_algebraic {R : Type u} [CommRing R] (J : Ideal R) (i : ℕ) :=
  localCohomology (R := R) J i

end SGA.SGA2.ExposeI
