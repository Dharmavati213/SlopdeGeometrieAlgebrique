/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.OpenExtensionByZero
import SGA.SGA2.ExposeI.ExtAdjunction
import SGA.SGA2.ExposeI.FlasqueCohomology

/-!
# Open support and ordinary cohomology

The actual open extension-by-zero object represents sections on the open.
In all degrees its Ext groups identify with the ordinary cohomology of the
restricted sheaf. The comparison is natural and respects coefficient boundaries.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false

/-- Global sections after ordinary open pullback are the original sections
on that open, using the actual pullback-to-naive-restriction isomorphism. -/
def restrictToOpenSectionsIso (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (restrictToOpen F U).obj.obj (op ⊤) ≅ F.obj.obj (op U) :=
  (((sheafToPresheaf _ _).mapIso
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).app F)).app (op ⊤)) ≪≫
      F.obj.mapIso (eqToIso (by simp))

/-- **I.1.6, open case:** actual open extension by zero represents sections. -/
def openSupportHomEquiv (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (zZX_open U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((openExtensionByZeroAdjunction U).homAddEquiv
    (constantZ ((Opens.toTopCat X).obj U)) F).trans
      (((constantSheafAdj _ AddCommGrpCat isTerminalTop).homAddEquiv
        (AddCommGrpCat.of (ULift ℤ)) (restrictToOpen F U)).trans
          ((AddCommGrpCat.uliftZMultiplesAddEquiv _).trans
            (restrictToOpenSectionsIso U F).addCommGroupIsoToAddEquiv))

/-- **I.2.3 / I.2.3 bis, open case:** Ext from actual open extension by zero
is the ordinary cohomology of the restricted sheaf, in every degree. -/
def openSupportExtEquiv (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Ext.{u} (zZX_open U) F n ≃+ H (restrictToOpen F U) n := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact adjunctionExtEquiv (openExtensionByZeroAdjunction U)
    (constantZ ((Opens.toTopCat X).obj U)) F n

/-- The open-support comparison is natural in the coefficient sheaf. -/
theorem openSupportExtEquiv_naturality (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : Ext.{u} (zZX_open U) F n) :
    openSupportExtEquiv U G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      CategoryTheory.Sheaf.H.map.{u} ((iShriek_open U).map f) n
        (openSupportExtEquiv U F n x) := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact adjunctionExtMap_naturality (openExtensionByZeroAdjunction U) _ f n x

/-- The degree-zero comparison is the actual Hom adjunction. -/
theorem openSupportExtEquiv_mk₀ (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (f : zZX_open U ⟶ F) :
    openSupportExtEquiv U F 0 (Ext.mk₀ f) =
      Ext.mk₀ ((openExtensionByZeroAdjunction U).homEquiv _ F f) := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact adjunctionExtMap_mk₀ (openExtensionByZeroAdjunction U) _ F f

/-- Restriction takes short exact coefficient sequences to short exact sequences. -/
theorem restrictToOpen_shortExact (U : Opens X)
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) :
    (S.map (iShriek_open U)).ShortExact := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact hS.map_of_exact (iShriek_open U)

/-- The open-support comparison commutes with the actual coefficient boundary maps. -/
theorem openSupportExtEquiv_boundary (U : Opens X)
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (n : ℕ) (x : Ext.{u} (zZX_open U) S.X₃ n) :
    openSupportExtEquiv U S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (openSupportExtEquiv U S.X₃ n x).comp
        (restrictToOpen_shortExact U hS).extClass rfl := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact adjunctionExtMap_boundary (openExtensionByZeroAdjunction U) _ hS n x

/-- Flasque coefficients have zero positive Ext from open extension by zero. -/
theorem openSupportExt_pos_subsingleton_of_isFlasque (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Sheaf.IsFlasque F] (n : ℕ) :
    Subsingleton (Ext.{u} (zZX_open U) F (n + 1)) := by
  have := H_pos_restrict_subsingleton_of_isFlasque F U n
  exact (openSupportExtEquiv U F (n + 1)).injective.subsingleton

end SGA.SGA2.ExposeI
