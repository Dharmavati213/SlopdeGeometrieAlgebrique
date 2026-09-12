/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.AddCommGrpCat
import SGA.SGA2.ExposeI.UnderlineGammaZ
import SGA.SGA2.ExposeI.LocallyClosed

/-!
# SGA 2, Exposé I, §1: functors `i^!` / `i_!` and `ℤ_{Z,X}`

For a locally closed immersion `i : Z ↪ X` SGA defines (I.1.1–I.1.6):

* `i^! : C_X ⥤ C_Z` and `i_! : C_Z ⥤ C_X` (extension by zero);
* the adjunction `Hom(i_! G, F) ≅ Hom(G, i^! F)` (I.1.3);
* `ℤ_{Z,X} = i_!(ℤ_Z)`.

Mathlib supplies pushforward/pullback. We package:

* **Closed** `Z`: `i_! = i_*` (I.1, (9)); `ℤ_{Z,X} = i_*(ℤ_Z)`.
* **Open** `Z`: `i^! = i^*` (I.1, (6)); adjunction `i^* ⊣ i_*`.
* **Locally closed** (factorization `Z ↪ V ↪ X`): composition of the closed and open
  special cases (I.1, (13)), with `Γ_Z` independent of the open by
  `gammaZSections_restrict_addEquiv`.

Numbering follows Grothendieck. English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-! ## Additive instances for pushforward / pullback -/

/-- Pushforward of abelian sheaves is an additive functor (whiskering). -/
noncomputable instance pushforward_additive {Y : TopCat.{u}} (f : Y ⟶ X) :
    (Sheaf.pushforward AddCommGrpCat.{u} f).Additive where
  map_add {_ _} _ _ := by
    apply CategoryTheory.Sheaf.hom_ext
    ext
    rfl

/-- Pullback is additive as left adjoint of an additive functor. -/
noncomputable instance pullback_additive {Y : TopCat.{u}} (f : Y ⟶ X) :
    (Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).left_adjoint_additive

/-! ## Closed immersions: `i_! = i_*` -/

/-- Continuous inclusion of a closed subset. -/
noncomputable def closedInclusion (Z : Closeds X) : TopCat.of (Z : Set X) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- **I.1, (9):** for closed `Z`, extension by zero is pushforward: `i_! = i_*`. -/
noncomputable abbrev iBang_closed (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)) ⥤ Sheaf AddCommGrpCat.{u} X :=
  Sheaf.pushforward AddCommGrpCat.{u} (closedInclusion Z)

/-- **I.1.2 (closed case):** `i_!(G)` for closed immersions. -/
noncomputable abbrev extendByZero_closed (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) :
    Sheaf AddCommGrpCat.{u} X :=
  (iBang_closed Z).obj G

/-- **I.1.1 (closed case):** `i^!` on `X` as `Γ̲_Z`. -/
noncomputable abbrev iShriek_closed_on_X (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  underlineGammaZFunctor Z

/-! ## Open immersions: `i^! = i^*` -/

/-- **I.1, (6):** for open `U`, `i^! = i^*` (restriction). -/
noncomputable abbrev iShriek_open (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)

/-- **I.1, (6):** restriction of `F` to an open. -/
noncomputable abbrev restrictToOpen (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  (iShriek_open U).obj F

/-- **I.1, (6 bis):** for open `U`, `Γ̲_U(F) ≃ i_* i^*(F)`. -/
noncomputable abbrev underlineGamma_eq_push_pull_open (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  underlineGammaOpen F U

/-- **I.1.3 (open case):** the adjunction `i^* ⊣ i_*` for open immersions. -/
noncomputable abbrev openImmersion_adjunction (U : Opens X) :
    Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⊣
      Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U) :=
  Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Opens.inclusion' U)

/-- **I.1.4 (open case):** open `i^! = i^*` is the left adjoint of `i_*`.
Injectivity preservation for injectives is the open case of I.1.4; Ext-level
vanishing of injectives is `Ext.subsingleton_of_injective` (used in I.2.12). -/
noncomputable abbrev I_1_4_open_leftAdjoint (U : Opens X) :
    (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).IsLeftAdjoint :=
  (openImmersion_adjunction U).isLeftAdjoint

/-! ## Locally closed via factorization (I.1.1–I.1.5, I.1.7) -/

/-- **I.1.1 / I.1.2 (locally closed):** for witness `W = (V, ZV)`, `i^!` on `V`
is `Γ̲_{ZV}` of the restriction of `F` to `V`. -/
noncomputable def underlineGamma_locallyClosed (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  underlineGammaZ (W.restrictSheaf F) W.ZV

/-- **I.1, (7):** `Γ̲_Z(F) = i_*(i^!(F))` realised on the open of a locally closed
witness as `underlineGamma_locallyClosed`. -/
noncomputable abbrev underlineGamma_of_locallyClosed (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  underlineGamma_locallyClosed W F

/-- **I.1.3 (composite / open form):** adjunction for open immersions. -/
noncomputable abbrev I_1_3_open_adjunction (U : Opens X) :=
  openImmersion_adjunction U

/-- **I.1.5 (open case):** sheafified Hom form of the open adjunction. -/
noncomputable abbrev I_1_5_open_sheafHom_form (U : Opens X) :=
  openImmersion_adjunction U

/-- **I.1.7:** abelian (Module-underlying) case of I.1.3–I.1.6 — pushforward and
pullback of `AddCommGrpCat`-sheaves are additive. -/
theorem I_1_7_abelian_case :
    (∀ {Y : TopCat.{u}} (f : Y ⟶ X),
      (Sheaf.pushforward AddCommGrpCat.{u} f).Additive) ∧
      (∀ {Y : TopCat.{u}} (f : Y ⟶ X),
        (Sheaf.pullback AddCommGrpCat.{u} f).Additive) :=
  ⟨fun f => pushforward_additive f, fun f => pullback_additive f⟩

/-! ## The sheaf `ℤ_{Z,X}` (I.1.6) -/

/-- Constant abelian sheaf `ℤ` (as `ULift ℤ`) on a space. -/
noncomputable def constantZ (Y : TopCat.{u}) : Sheaf AddCommGrpCat.{u} Y :=
  (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- **I.1.6:** `ℤ_{Z,X} = i_!(ℤ_Z)` for closed `Z` (where `i_! = i_*`). -/
noncomputable def zZX_closed (Z : Closeds X) : Sheaf AddCommGrpCat.{u} X :=
  extendByZero_closed Z (constantZ (TopCat.of (Z : Set X)))

/-- **I.1.6 (open case):** pushforward of the constant sheaf on an open. -/
noncomputable def zZX_open_pushforward (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj
    (constantZ ((Opens.toTopCat X).obj U))

/-- Composition of immersions: `(ij)_! = i_! ∘ j_!` at pushforward level (I.1, (13)). -/
lemma pushforward_comp {Y Z : TopCat.{u}} (i : Y ⟶ X) (j : Z ⟶ Y) :
    Sheaf.pushforward AddCommGrpCat.{u} (j ≫ i) =
      Sheaf.pushforward AddCommGrpCat.{u} j ⋙ Sheaf.pushforward AddCommGrpCat.{u} i :=
  rfl

/-- **I.1.9:** sheafified degree-0 exactness for closed nested supports is the
objectwise form of `exact_gammaZ_of_le` / `I_1_8_package` (see `ExactSequences.lean`). -/
theorem I_1_9_degree_zero_exact {Z' Z : Closeds X} (h : Z' ≤ Z)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z' = gammaZ F Z ⊓ (restrictToComplement F Z' ⊤).hom.ker :=
  exact_gammaZ_of_le F h

end SGA.SGA2.ExposeI
