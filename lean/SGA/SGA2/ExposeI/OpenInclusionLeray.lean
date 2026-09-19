/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalSpectralSequence
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves
import SGA.SGA2.ExposeI.LocalToGlobalSpectralSequence

/-!
# I.2.6 as a named Grothendieck/Leray spectral sequence

The constructed local-to-global spectral sequence is the Grothendieck
spectral sequence of global sections after the supported-sheaf functor.
When the support is open, I.2.5 identifies the E₂ page with ordinary
cohomology of higher direct images, which is the Leray spectral sequence
of the open inclusion.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The Grothendieck spectral sequence of the closed supported-sheaf functor:
canonical truncations of `underlineGammaZ` applied to an injective resolution,
followed by derived Hom from the constant integer sheaf. This is exactly the
already constructed local-to-global sequence of I.2.6. -/
def grothendieckSpectralSequenceOfSupportedSheaf (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  supportedTruncationSpectralSequence Z I

theorem grothendieckSpectralSequenceOfSupportedSheaf_eq (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    grothendieckSpectralSequenceOfSupportedSheaf Z I =
      supportedTruncationSpectralSequence Z I :=
  rfl

/-- The Grothendieck spectral sequence of an arbitrary locally closed
supported-sheaf functor is the ambient locally closed sequence of I.2.6. -/
def grothendieckSpectralSequenceOfLocallyClosedSupport (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  locallyClosedTruncationSpectralSequence W I

theorem grothendieckSpectralSequenceOfLocallyClosedSupport_eq (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    grothendieckSpectralSequenceOfLocallyClosedSupport W I =
      locallyClosedTruncationSpectralSequence W I :=
  rfl

/-- Ordinary cohomology of a sheaf isomorphism. -/
def H_iso {F G : Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) (n : ℕ) :
    H F n ≃+ H G n :=
  (((extFunctor n).obj
      (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))))).mapIso e).addCommGroupIsoToAddEquiv

/-- **I.2.6, open support, Leray identification:** the E₂ page of the
constructed sequence is ordinary cohomology of the higher direct images of
actual restriction, i.e. the Leray spectral sequence of `i : U → X`. -/
def openInclusionLerayE2Equiv (U : Opens X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :
    ((locallyClosedTruncationSpectralSequence (LocallyClosedIn.ofOpen U) I).page 2).X
        ((p : ℤ), (q : ℤ)) ≃+
      H (((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').rightDerived q).obj
        (restrictToOpen F U)) p :=
  (locallyClosedTruncationSpectralSequenceE2Equiv (LocallyClosedIn.ofOpen U) I p q).trans
    (H_iso ((derivedUnderlineGammaOfOpenIso U q).app F) p)

/-- The same identification, named as the Grothendieck sequence of the
open-support functor. -/
def grothendieckSpectralSequenceOfOpenSupport (U : Opens X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  grothendieckSpectralSequenceOfLocallyClosedSupport (LocallyClosedIn.ofOpen U) I

end SGA.SGA2.ExposeI
