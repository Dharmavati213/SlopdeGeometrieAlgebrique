/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalTotalCohomology
import SGA.SGA2.ExposeI.SpectralObjectConvergence

/-!
# Convergence of the actual supported local-to-global spectral sequence

The actual total-interval group, already identified additively with original
`H_Z`, has its canonical finite image filtration. The filtration starts at
zero and ends at the whole group. Actual pages Eᵣ, for r ≥ n + 2 in total
degree n, are its genuine associated-graded cokernels.

The total object lives in the spectral construction's larger universe; the
proved additive equivalence identifies its underlying group with the original
smaller-universe `H_Z`, without a mathematical change to the abutment.
This file does not assert coefficient naturality of the spectral sequence.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The actual filtered abutment group is the original supported cohomology. -/
def supportedCohomologyAbutmentEquiv (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    ↥(SpectralObjectConvergence.total (C := AddCommGrpCat.{u + 1})
      (supportedLocalToGlobalAbelianSpectralObject Z I) n) ≃+
      H_Z Z F n :=
  supportedSpectralObjectTotalEquivH_Z Z I n

/-- The canonical finite filtration of actual supported total cohomology,
whose underlying group is original `H_Z` by `supportedCohomologyAbutmentEquiv`. -/
def supportedCohomologyFiniteFiltration (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    Fin (n + 2) →o Subobject
      (SpectralObjectConvergence.total (supportedLocalToGlobalAbelianSpectralObject Z I) n) :=
  SpectralObjectConvergence.finiteFiltration (supportedLocalToGlobalAbelianSpectralObject Z I) n

@[simp] theorem supportedCohomologyFiniteFiltration_zero (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    supportedCohomologyFiniteFiltration Z I n 0 = ⊥ :=
  SpectralObjectConvergence.finiteFiltration_zero _ n

@[simp] theorem supportedCohomologyFiniteFiltration_last (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    supportedCohomologyFiniteFiltration Z I n (Fin.last (n + 1)) = ⊤ :=
  SpectralObjectConvergence.finiteFiltration_last _ n

/-- The actual quotient of two consecutive terms in the finite abutment filtration. -/
def supportedCohomologyGradedPiece (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ)
    (q : Fin (n + 1)) : AddCommGrpCat.{u + 1} :=
  cokernel (Subobject.ofLE
    (supportedCohomologyFiniteFiltration Z I n q.castSucc)
    (supportedCohomologyFiniteFiltration Z I n q.succ)
    ((supportedCohomologyFiniteFiltration Z I n).monotone (by
      change q.val ≤ q.val + 1
      omega)))

/-- Equality of the named subobjects transports their actual quotient,
without rewriting a dependent inclusion morphism in place. -/
private def cokernelOfLEIsoOfEq {C : Type*} [Category* C] [Abelian C]
    {T : C} (A B A' B' : Subobject T) (h : A ≤ B) (h' : A' ≤ B')
    (hA : A = A') (hB : B = B') :
    cokernel (Subobject.ofLE A B h) ≅ cokernel (Subobject.ofLE A' B' h') := by
  subst A' B'
  exact Iso.refl _

/-- **I.2.6 convergence:** every sufficiently late actual page is the
associated graded of the canonical finite filtration of the total group,
which is additively identified with original `H_Z`. The bound is uniform
over all bidegrees of the fixed total degree. -/
def supportedLocalToGlobalStablePageIsoGraded (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ)
    (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((supportedTruncationSpectralSequence Z I).page r).X ((n : ℤ) - q, q) ≅
      supportedCohomologyGradedPiece Z I n q := by
  refine SpectralObjectConvergence.stablePageIsoGradedTotal
    (supportedLocalToGlobalAbelianSpectralObject Z I) n q r hr ≪≫ ?_
  unfold SpectralObjectConvergence.gradedPiece supportedCohomologyGradedPiece
  refine cokernelOfLEIsoOfEq _ _ _ _ _ _ rfl ?_
  dsimp only [supportedCohomologyFiniteFiltration, SpectralObjectConvergence.finiteFiltration,
    OrderHom.coe_mk, Fin.val_succ]
  rw [Nat.cast_add, Nat.cast_one]

end SGA.SGA2.ExposeI
