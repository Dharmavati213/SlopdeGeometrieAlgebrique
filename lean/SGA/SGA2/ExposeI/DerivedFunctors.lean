/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
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
define `ℋ_Z^n` for all `n` using the formulas in I.2.11
(`ker` / `coker` / `R^{n-1} j_*`). Their comparison with the right derived
functors of `Γ_Z` and `Γ̲_Z`, and with the sheafification of local Ext groups,
is not proved in this file. `SupportedCohomologyComparison.lean` now proves
the group-valued derived comparison, `SupportedSheafModel.lean` proves the
natural all-degree original-derived and sheafification comparisons for the
unchanged sheaf model, and `SupportedExcision.lean` proves all-degree
closed-support excision. The excision result below concerns degree zero.

For I.2.6 we define the proposed local-to-global `E₂` terms only. No spectral
sequence, differentials, convergence, or higher abutment vanishing is constructed.

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

/-- The morphism on the Ext-defined `H_Z^n` induced by a sheaf morphism. -/
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

/-! ## I.2.4–I.2.5 / I.2.11: sheafified `ℋ_Z^n` for all `n` -/

/-- **I.2.11 / I.2.4:** the sheaf `ℋ_Z^n(F)` for closed `Z`, following I.2.11:

* `n = 0`: `ker(F → j_* j^* F) = Γ̲_Z(F)`;
* `n = 1`: `coker(F → j_* j^* F)`;
* `n ≥ 2`: `R^{n-1} j_*(F|_{X\Z})`.

The comparison with the sheaf associated to `U ↦ H_{Z∩U}^n(U, F|_U)`
in I.2.4 is proved separately in `SupportedSheafModel.lean`. -/
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

/-- **I.2.2 (degree zero only):** an additive equivalence on supported sections
exists when the support lies in the open set. -/
theorem I_2_2_excision_degree_zero {Z : Closeds X} {V : Opens X}
    (hZ : (Z : Set X) ⊆ (V : Set X)) (F : Sheaf AddCommGrpCat.{u} X) :
    Nonempty (gammaZ F Z ≃+ gammaZSections F Z V) :=
  ⟨I_2_2_degree_zero hZ F⟩

/-- **I.2.3 (sections on an open support):** the supported subgroup on `U`
contains every section of `F(U)`. No higher cohomology comparison is asserted. -/
theorem I_2_3_open_sections (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (LocallyClosedIn.ofOpen U).gamma F = ⊤ :=
  LocallyClosedIn.gamma_ofOpen F U

/-! ## Terms proposed for I.2.6 and injective Ext vanishing -/

/-- The groups appearing in the proposed `E₂` page of I.2.6. This definition
does not supply a spectral sequence or a comparison with its abutment. -/
noncomputable abbrev localToGlobalE2Term (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (p q : ℕ) : Type u :=
  H (sheafH_Z_n Z F q) p

/-- Vanishing of the degree-zero sheaf is vanishing of the kernel sheaf,
by the definition of `sheafH_Z_n`. -/
theorem sheafH_Z_zero_isZero_iff (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero (sheafH_Z_n Z F 0) ↔ IsZero (underlineGammaZ F Z) :=
  Iff.rfl

/-- Positive Ext-defined local cohomology vanishes on injective sheaves.
This uses Ext directly and does not assert spectral-sequence degeneration. -/
theorem H_Z_pos_subsingleton_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    Subsingleton (H_Z Z F (n + 1)) :=
  Ext.subsingleton_of_injective (zZX_closed Z) F n

/-! ## Algebraic bridge -/

/-- Re-export of algebraic local cohomology. Its comparison with the
sheaf-theoretic construction on an affine scheme is not proved here. -/
noncomputable abbrev H_J_algebraic {R : Type u} [CommRing R] (J : Ideal R) (i : ℕ) :=
  localCohomology (R := R) J i

end SGA.SGA2.ExposeI
