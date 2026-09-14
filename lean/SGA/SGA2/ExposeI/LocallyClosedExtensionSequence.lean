/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenClosedExtensionSequence

/-! # I.1, (17): arbitrary coefficients on a locally closed support

For a sheaf `G` on the actual support space of `W`, and a closed subset `T`
of that space, apply the proved exact functor `iBang_locallyClosed W` to the
canonical open–closed sequence on the support. The terms are literal
composite extensions by zero along these inclusions. No comparison with an
independently chosen single-factorization witness is assumed or asserted.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

instance iBang_locallyClosed_additive (W : LocallyClosedIn X) :
    (iBang_locallyClosed W).Additive :=
  inferInstanceAs (iBang_closed (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙
    iBang_open W.V).Additive

instance iBang_locallyClosed_isLeftAdjoint (W : LocallyClosedIn X) :
    (iBang_locallyClosed W).IsLeftAdjoint :=
  (locallyClosedSupportAdjunction W).isLeftAdjoint

instance iBang_locallyClosed_preservesMonomorphisms (W : LocallyClosedIn X) :
    (iBang_locallyClosed W).PreservesMonomorphisms :=
  inferInstanceAs (iBang_closed (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙
    iBang_open W.V).PreservesMonomorphisms

instance iBang_locallyClosed_preservesEpimorphisms (W : LocallyClosedIn X) :
    (iBang_locallyClosed W).PreservesEpimorphisms :=
  inferInstanceAs (iBang_closed (X := (Opens.toTopCat X).obj W.V) W.ZV ⋙
    iBang_open W.V).PreservesEpimorphisms

instance iBang_locallyClosed_preservesHomology (W : LocallyClosedIn X) :
    (iBang_locallyClosed W).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (iBang_locallyClosed W)

/-- The existing composite locally closed extension by zero is exact on
all coefficient sheaves, without finiteness or constancy assumptions. -/
theorem iBang_locallyClosed_shortExact (W : LocallyClosedIn X)
    (S : ShortComplex (Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))))
    (hS : S.ShortExact) : (S.map (iBang_locallyClosed W)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (iBang_locallyClosed W)

/-- The three actual composite extensions of the arbitrary restricted
coefficient sheaves on the closed part, support, and open difference. -/
def locallyClosedExtensionSequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  (openClosedExtensionSequence T G).map (iBang_locallyClosed W)

/-- **I.1, (17), arbitrary `G`:** the sequence of actual composite
extensions `0 → i_!k_!k^*G → i_!G → i_!j_*j^*G → 0` is short exact. -/
theorem locallyClosedExtensionSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedExtensionSequence W T G).ShortExact := by
  change ((openClosedExtensionSequence (X := TopCat.of (W.ZV : Set W.V)) T G).map
    (iBang_locallyClosed W)).ShortExact
  exact iBang_locallyClosed_shortExact W
    (openClosedExtensionSequence (X := TopCat.of (W.ZV : Set W.V)) T G)
    (openClosedExtensionSequence_shortExact (X := TopCat.of (W.ZV : Set W.V)) T G)

/-- The arbitrary-coefficient extension sequence is functorial in `G`,
using the actual restriction and extension maps in every term. -/
def locallyClosedExtensionSequenceFunctor (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) ⥤
      ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  openClosedExtensionSequenceFunctor T ⋙ (iBang_locallyClosed W).mapShortComplex

theorem locallyClosedExtensionSequence_X₁ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedExtensionSequence W T G).X₁ =
      (iBang_locallyClosed W).obj ((iBang_open T.compl).obj (restrictToOpen G T.compl)) := rfl

theorem locallyClosedExtensionSequence_X₂ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedExtensionSequence W T G).X₂ = (iBang_locallyClosed W).obj G := rfl

theorem locallyClosedExtensionSequence_X₃ (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedExtensionSequence W T G).X₃ =
      (iBang_locallyClosed W).obj ((iBang_closed T).obj
        ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion T)).obj G)) := rfl

end SGA.SGA2.ExposeI
