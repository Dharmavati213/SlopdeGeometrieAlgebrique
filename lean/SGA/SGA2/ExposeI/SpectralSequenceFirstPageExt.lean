/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Spectral-sequence morphisms are determined by their first page

The proof uses the original page-to-homology isomorphisms of mathlib's
`SpectralSequence`, and induction through every subsequent page. No page
comparison or convergence hypothesis is imposed.
-/

noncomputable section

open CategoryTheory

namespace SGA.SGA2.ExposeI

variable {C : Type*} [Category C] [Abelian C]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {E E' : SpectralSequence C c r₀} {f g : E ⟶ E'}

/-- Equality of spectral-sequence chain maps on one page propagates to
every later page through the genuine homology-to-next-page isomorphisms. -/
theorem spectralSequence_pageMap_eq_of_eq {s : ℤ} (hs : r₀ ≤ s)
    (h : f.hom s hs = g.hom s hs) (r : ℤ) (hsr : s ≤ r) :
    f.hom r (hs.trans hsr) = g.hom r (hs.trans hsr) := by
  induction r, hsr using Int.leInduction with
  | base => exact h
  | succ r hsr ih =>
    ext pq
    apply (cancel_epi (E.iso r (r + 1) pq rfl (hs.trans hsr)).hom).mp
    rw [← f.comm r (r + 1) pq rfl (hs.trans hsr),
      ← g.comm r (r + 1) pq rfl (hs.trans hsr), ih]

/-- Two actual spectral-sequence morphisms are equal if their chain maps
on the first page are equal. -/
theorem spectralSequence_hom_ext_firstPage (h : f.hom r₀ = g.hom r₀) : f = g := by
  apply SpectralSequence.hom_ext
  intro r hr
  exact spectralSequence_pageMap_eq_of_eq (le_refl r₀) h r hr

/-- It also suffices to compare all object maps on the first page. -/
theorem spectralSequence_hom_ext_firstPage_f
    (h : ∀ pq : κ, (f.hom r₀).f pq = (g.hom r₀).f pq) : f = g :=
  spectralSequence_hom_ext_firstPage (HomologicalComplex.Hom.ext (funext h))

/-- Evaluation on the first page of a spectral sequence is faithful. -/
instance spectralSequence_firstPageFunctor_faithful :
    (SpectralSequence.pageFunctor C c r₀ r₀).Faithful where
  map_injective := fun h => spectralSequence_hom_ext_firstPage h

end SGA.SGA2.ExposeI
