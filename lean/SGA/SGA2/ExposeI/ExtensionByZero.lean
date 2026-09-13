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
# SGA 2, Exposé I, §1: closed pushforward and open pullback

For a locally closed immersion `i : Z ↪ X` SGA defines (I.1.1–I.1.6):

* `i^! : C_X ⥤ C_Z` and `i_! : C_Z ⥤ C_X` (extension by zero);
* the adjunction `Hom(i_! G, F) ≅ Hom(G, i^! F)` (I.1.3);
* `ℤ_{Z,X} = i_!(ℤ_Z)`.

This file defines the closed-immersion model `i_! := i_*`, following I.1, (9),
and the corresponding object `ℤ_{Z,X}`. For an open immersion it defines
`i^! := i^*` and supplies the ordinary pullback-pushforward adjunction
`i^* ⊣ i_*`. Pushforward and pullback of abelian sheaves are additive.

The closed-support functor here takes values in sheaves on `X`; the functor
`i^!` taking values in sheaves on `Z` and its comparison with this endofunctor
are not constructed. The locally closed construction likewise produces a
support sheaf on a chosen open neighbourhood, without a sheaf-level comparison
between different neighbourhoods.

Open or general locally closed extension by zero, its adjunction of I.1.3,
injective preservation in I.1.4, internal-Hom comparison in I.1.5, and the
Hom representations in I.1.6 remain unproved in this file. The general
composition law (13) for extension by zero is also not established here;
`pushforward_comp` is the composition law for ordinary pushforward.

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

/-- Closed-immersion extension by zero, defined by pushforward as in I.1, (9). -/
noncomputable abbrev iBang_closed (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)) ⥤ Sheaf AddCommGrpCat.{u} X :=
  Sheaf.pushforward AddCommGrpCat.{u} (closedInclusion Z)

/-- The closed-immersion extension-by-zero object, using the pushforward model
of I.1, (9). The support characterization of I.1.2 is not asserted here. -/
noncomputable abbrev extendByZero_closed (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) :
    Sheaf AddCommGrpCat.{u} X :=
  (iBang_closed Z).obj G

/-- The closed-support endofunctor `Γ̲_Z` on sheaves on `X`. Its relation to
`i_* i^!` is I.1, (7); the functor `i^!` on sheaves on `Z` is not constructed here. -/
noncomputable abbrev closedSupportFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  underlineGammaZFunctor Z

/-! ## Open immersions: `i^! = i^*` -/

/-- Open-immersion shriek pullback, defined as ordinary pullback following
the identification with restriction in I.1, (6). -/
noncomputable abbrev iShriek_open (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)

/-- **I.1, (6):** restriction of `F` to an open. -/
noncomputable abbrev restrictToOpen (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U) :=
  (iShriek_open U).obj F

/-- The object `i_* i^*(F)` used as the open-support sheaf in I.1, (6 bis).
This is an object definition, not a comparison isomorphism. -/
noncomputable abbrev openSupportSheaf (F : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  underlineGammaOpen F U

/-- The ordinary pullback-pushforward adjunction `i^* ⊣ i_*` for an open immersion.
The extension-by-zero adjunction of I.1.3 instead has the form `i_! ⊣ i^!`. -/
noncomputable abbrev openImmersion_adjunction (U : Opens X) :
    Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U) ⊣
      Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U) :=
  Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Opens.inclusion' U)

/-- Open pullback is left adjoint to pushforward. This does not establish
preservation of injective objects under restriction, as required in I.1.4. -/
noncomputable abbrev openPullback_isLeftAdjoint (U : Opens X) :
    (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).IsLeftAdjoint :=
  (openImmersion_adjunction U).isLeftAdjoint

/-! ## A support sheaf on the open neighbourhood of a locally closed witness -/

/-- For a locally closed witness `W = (V, ZV)`, apply the closed-support
construction on `V` to the restriction of `F`. The result is a sheaf on `V`. -/
noncomputable def underlineGamma_locallyClosed (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  underlineGammaZ (W.restrictSheaf F) W.ZV

/-- The support sheaf on the chosen open neighbourhood of a locally closed
witness. No comparison with a sheaf on `X` or on the support is asserted. -/
noncomputable abbrev underlineGamma_of_locallyClosed (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  underlineGamma_locallyClosed W F

/-- Pushforward and pullback of abelian sheaves are additive. This does not
construct the extension to sheaves of modules on ringed spaces in I.1.7. -/
theorem pushforward_pullback_additive :
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

/-- The object `ℤ_{Z,X}` occurring in I.1.6, defined for closed `Z` using
`i_! := i_*`. The Hom comparison isomorphisms of I.1.6 are not asserted here. -/
noncomputable def zZX_closed (Z : Closeds X) : Sheaf AddCommGrpCat.{u} X :=
  extendByZero_closed Z (constantZ (TopCat.of (Z : Set X)))

/-- Ordinary pushforward of the constant integer sheaf on an open. This is
`i_*(ℤ_U)`; it is not in general the extension by zero `ℤ_{U,X}` of I.1.6. -/
noncomputable def openConstantZPushforward (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj
    (constantZ ((Opens.toTopCat X).obj U))

/-- Ordinary pushforward respects composition of continuous maps. -/
lemma pushforward_comp {Y Z : TopCat.{u}} (i : Y ⟶ X) (j : Z ⟶ Y) :
    Sheaf.pushforward AddCommGrpCat.{u} (j ≫ i) =
      Sheaf.pushforward AddCommGrpCat.{u} j ⋙ Sheaf.pushforward AddCommGrpCat.{u} i :=
  rfl

end SGA.SGA2.ExposeI
