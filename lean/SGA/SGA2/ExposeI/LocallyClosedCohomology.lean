/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.OpenSupportCohomology
import SGA.SGA2.ExposeI.SupportedCohomologyComparison

/-!
# Cohomology with locally closed support

For an actual locally closed witness (an open neighbourhood with a closed
subset), extend the closed pushforward by genuine open extension by zero.
Its Hom represents the existing supported-section functor, so its Ext computes
the original derived functors. Exact restriction identifies these groups with
closed-support cohomology on the chosen neighbourhood.

This file works with a chosen witness. Independence of different witnesses is
a separate excision assertion, not a consequence of the definitions alone.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Extension by zero for a chosen locally closed factorization: closed
pushforward in the open neighbourhood, followed by open extension by zero. -/
def iBang_locallyClosed (W : LocallyClosedIn X) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) ⥤
      Sheaf AddCommGrpCat.{u} X :=
  iBang_closed (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙ iBang_open W.V

/-- The actual integer support sheaf for a chosen locally closed witness. -/
def zZX_locallyClosed (W : LocallyClosedIn X) : Sheaf AddCommGrpCat.{u} X :=
  (iBang_open W.V).obj (zZX_closed W.ZV)

/-- Supported sections on a locally closed witness, as an additive functor. -/
def gammaLocallyClosedFunctor (W : LocallyClosedIn X) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  iShriek_open W.V ⋙ gammaZSectionsFunctor W.ZV ⊤

instance (W : LocallyClosedIn X) : (gammaLocallyClosedFunctor W).Additive := by
  dsimp [gammaLocallyClosedFunctor]
  infer_instance

/-- **I.1.6:** genuine locally closed extension by zero represents supported
sections on the chosen open neighbourhood. -/
def locallyClosedSupportHomEquiv (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (zZX_locallyClosed W ⟶ F) ≃+ W.gamma F := by
  change ((iBang_open W.V).obj (zZX_closed W.ZV) ⟶ F) ≃+
    gammaZ (restrictToOpen F W.V) W.ZV
  exact ((openExtensionByZeroAdjunction W.V).homAddEquiv
    (zZX_closed (X := (Opens.toTopCat X).obj W.V) W.ZV) F).trans
    (closedSupportHomEquiv (X := (Opens.toTopCat X).obj W.V) W.ZV (restrictToOpen F W.V))

theorem locallyClosedSupportHomEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (φ : zZX_locallyClosed W ⟶ F) :
    locallyClosedSupportHomEquiv W G (φ ≫ f) =
      (gammaLocallyClosedFunctor W).map f (locallyClosedSupportHomEquiv W F φ) := by
  change closedSupportHomEquiv W.ZV (restrictToOpen G W.V)
      ((openExtensionByZeroAdjunction W.V).homEquiv (zZX_closed W.ZV) G (φ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact closedSupportHomEquiv_naturality (X := (Opens.toTopCat X).obj W.V)
    W.ZV ((iShriek_open W.V).map f)
    ((openExtensionByZeroAdjunction W.V).homEquiv (zZX_closed W.ZV) F φ)

/-- The Hom representation, naturally in coefficients. -/
def locallyClosedSupportHomFunctorIso (W : LocallyClosedIn X) :
    preadditiveCoyoneda.obj (op (zZX_locallyClosed W)) ≅ gammaLocallyClosedFunctor W :=
  NatIso.ofComponents (fun F => (locallyClosedSupportHomEquiv W F).toAddCommGrpIso)
    (fun f => by ext φ; exact locallyClosedSupportHomEquiv_naturality W f φ)

/-- The Ext presentation for a chosen locally closed support. -/
abbrev H_locallyClosed (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  Ext.{u} (zZX_locallyClosed W) F n

/-- The original right-derived locally closed supported-section functor. -/
def derivedGammaLocallyClosed (W : LocallyClosedIn X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (gammaLocallyClosedFunctor W).rightDerived n

/-- **I.2.1 / I.2.3 bis:** the original locally closed supported-section
derived functors naturally identify with Ext from the actual support sheaf. -/
def derivedGammaLocallyClosedIsoExt (W : LocallyClosedIn X) (n : ℕ) :
    derivedGammaLocallyClosed W n ≅ extFunctorObj (zZX_locallyClosed W) n :=
  (rightDerivedFunctorIso (locallyClosedSupportHomFunctorIso W) n).symm ≪≫
    rightDerivedCoyonedaNatIsoExt (zZX_locallyClosed W) n

/-- Locally closed support cohomology equals closed-support cohomology on
the chosen open neighbourhood, using the genuine Ext adjunction. -/
def locallyClosedSupportExtEquiv (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed W F n ≃+ H_Z W.ZV (restrictToOpen F W.V) n := by
  let := (openExtensionByZeroAdjunction W.V).isRightAdjoint
  exact adjunctionExtEquiv (openExtensionByZeroAdjunction W.V) (zZX_closed W.ZV) F n

/-- Naturality of reduction to closed support on the neighbourhood. -/
theorem locallyClosedSupportExtEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : H_locallyClosed W F n) :
    locallyClosedSupportExtEquiv W G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      H_Z_map W.ZV ((iShriek_open W.V).map f) n
        (locallyClosedSupportExtEquiv W F n x) := by
  let := (openExtensionByZeroAdjunction W.V).isRightAdjoint
  exact adjunctionExtMap_naturality (openExtensionByZeroAdjunction W.V) _ f n x

/-- **I.2.12, group-valued forward direction:** every chosen locally closed
support has zero positive cohomology on flasque sheaves. -/
theorem H_locallyClosed_pos_subsingleton_of_isFlasque (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    Subsingleton (H_locallyClosed W F (n + 1)) := by
  have := H_Z_pos_restrict_subsingleton_of_isFlasque F W.V W.ZV n
  exact (locallyClosedSupportExtEquiv W F (n + 1)).injective.subsingleton

/-- The original derived locally closed supported-section functors vanish
in positive degrees on flasque sheaves. -/
theorem derivedGammaLocallyClosed_isZero_of_isFlasque (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((derivedGammaLocallyClosed W (n + 1)).obj F) := by
  have := H_locallyClosed_pos_subsingleton_of_isFlasque W F n
  exact (AddCommGrpCat.isZero_iff_subsingleton.mpr this).of_iso
    ((derivedGammaLocallyClosedIsoExt W (n + 1)).app F)

end SGA.SGA2.ExposeI
