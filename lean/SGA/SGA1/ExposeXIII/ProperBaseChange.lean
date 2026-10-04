/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.CompleteLocal
import SGA.SGA1.ExposeIX.EtaleMorphismDescent
import SGA.SGA1.ExposeXIII.CohomologicalProperness

/-!
# SGA 1, Exposé XIII, 1.4: proper base change in degree `≤ 1` over a henselian base

XIII 1.4 says that for a proper morphism `f : X ⟶ Y` every sheaf of sets on `X` is
cohomologically proper for `f` in dimension `≤ 0`: the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is bijective for every base change `g : Y' ⟶ Y`
(`ProperBaseChangeStatement`). What is proved of it is elsewhere:

* the injectivity half, cohomological properness in dimension `≤ -1`, holds for every
  *universally closed* `f` and every `Y`, for sheaves of sets and of groups, with its
  consequences in dimension `≤ -1`: 1.8 for sheaves of sets, 1.9 for sheaves of sets and of groups
  (`isCohomologicallyProperLENegOne_of_universallyClosed`,
  `isCohomologicallyProperLENegOneGroup_of_universallyClosed`,
  `IsCohomologicallyProperLENegOne.comp_of_universallyClosed`,
  `isCohomologicallyProperLENegOne_pushforward_iff_of_isIntegralHom`,
  `isCohomologicallyProperLENegOneGroup_pushforward_iff_of_isIntegralHom`, in
  `SGA.SGA1.ExposeXIII.CohomologicalProperness`);
* bijectivity for every sheaf of sets when `Y` is locally noetherian
  (`SGA.SGA1.ExposeXIII.ProperBaseChangeNoetherian`, from Gabber's theorem); the case of sheaves
  represented by separated étale schemes, by a more elementary argument, is
  `SGA.SGA1.ExposeXIII.ProperBaseChangeRepresentable`.

The full `ProperBaseChangeStatement` (every `Y`) needs the reduction to a noetherian base
(EGA IV 8 and constructible sheaves), which is not done.

This file states the proper base change theorem in degree `≤ 1` for finite étale coverings over a
henselian local base (`HenselianEtaleCoveringsOfClosedFibreStatement`; SGA 4 XII 5.5,
Stacks 0A48), the form in which XIII 1.4 for torsors under finite groups is used. It contains
IX.1.10 (`etaleCoveringsOfClosedFibreStatement_of_henselian`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

section DegreeOne

/-- Proper base change in degree `≤ 1` for finite étale coverings over a henselian local base
(statement only; SGA 4 XII 5.5, Stacks 0A48): for a proper morphism `f : X ⟶ Spec A`, `A` a
henselian local ring, inverse image to the closed fibre `X₀ = X ×_A κ` is an equivalence between
the étale coverings of `X` and those of `X₀`.

This is IX.1.10 with the complete noetherian local ring replaced by an arbitrary henselian local
ring (`ExposeIX.EtaleCoveringsOfClosedFibreStatement` is the complete noetherian case). It is the
form of XIII 1.4 for torsors under finite groups that is used in XIII §§2–4: by XIII 1.5 b),
cohomological properness of `f` in dimension `≤ 1` for finite constant groups is a statement about
torsors over the strict localizations of `Y`, and over a strictly henselian base it says that
torsors on `X` and on its closed fibre correspond. SGA 1 XIII 1.4 (dimension `≤ 1` for ind-finite
sheaves of groups) is not stated in sheaf form here: its local form needs the comparison of
inverse images of sheaves of groups along composites, which is not formalized. The full
faithfulness half is proved for noetherian `A` in `SGA.SGA1.ExposeXIII.ProperBaseChangeHenselian`
(`full_pullback_closedFibre_of_henselianLocalRing`, `faithful_pullback_closedFibre_of_isLocalRing`);
essential surjectivity is open. -/
def HenselianEtaleCoveringsOfClosedFibreStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsProper f],
    (MorphismProperty.Over.pullback ExposeIX.etaleCovering ⊤
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).IsEquivalence

/-- IX.1.10 (`ExposeIX.EtaleCoveringsOfClosedFibreStatement`, complete noetherian local rings) is
the special case of `HenselianEtaleCoveringsOfClosedFibreStatement` where `A` is complete
(`ExposeIX.henselianLocalRing_of_isAdicComplete`). -/
theorem etaleCoveringsOfClosedFibreStatement_of_henselian
    (h : HenselianEtaleCoveringsOfClosedFibreStatement.{u}) :
    ExposeIX.EtaleCoveringsOfClosedFibreStatement.{u} := fun A _ _ _ _ X f _ ↦
  have := ExposeIX.henselianLocalRing_of_isAdicComplete A
  h A X f

end DegreeOne

end SGA.SGA1.ExposeXIII
