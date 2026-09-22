/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalSpectralSequence
import SGA.SGA2.ExposeI.OpenInclusionLeray
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-!
# Spectral-level independence of a locally closed witness

If two locally closed witnesses define the same subset, the E₂ pages of the
constructed I.2.6 sequences are isomorphic, because the original derived
supported sheaves are independent of the witness and ordinary cohomology
preserves that isomorphism.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- **I.2.6, spectral-level witness change:** the E₂ pages for two witnesses
of the same locally closed set are isomorphic, via independence of the
original derived supported sheaves. -/
def locallyClosedTruncationSpectralSequenceE2WitnessEquiv
    {W W' : LocallyClosedIn X} (h : W.asSet = W'.asSet)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :
    ((locallyClosedTruncationSpectralSequence W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ((locallyClosedTruncationSpectralSequence W' I).page 2).X ((p : ℤ), (q : ℤ)) :=
  (locallyClosedTruncationSpectralSequenceE2Equiv W I p q).trans
    ((H_iso ((derivedUnderlineGammaLocallyClosedIndependenceIso h q).app F) p).trans
      (locallyClosedTruncationSpectralSequenceE2Equiv W' I p q).symm)

end SGA.SGA2.ExposeI
