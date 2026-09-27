/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FiniteQuotient
import SGA.SGA1.ExposeV.FiniteQuotientProperties
import SGA.SGA1.ExposeV.QuotientResidueField
import SGA.SGA1.ExposeV.QuotientGluing
import SGA.SGA1.ExposeV.RelativeQuotient
import SGA.SGA1.ExposeV.FiniteQuotientBaseChange
import SGA.SGA1.ExposeV.QuotientBaseChange
import SGA.SGA1.ExposeV.QuotientDescent
import SGA.SGA1.ExposeV.SumOfCopies
import SGA.SGA1.ExposeV.DecompositionInertia
import SGA.SGA1.ExposeV.InertiaGroups
import SGA.SGA1.ExposeV.InertiaEtale
import SGA.SGA1.ExposeV.PrincipalCovering
import SGA.SGA1.ExposeV.QuotientPrincipal
import SGA.SGA1.ExposeV.QuotientEtale
import SGA.SGA1.ExposeV.QuotientComponents
import SGA.SGA1.ExposeV.QuotientFiniteEtale
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeV.EtaleCoveringAutomorphisms
import SGA.SGA1.ExposeV.GaloisAxioms
import SGA.SGA1.ExposeV.GaloisCategories
import SGA.SGA1.ExposeV.GaloisEquivalence
import SGA.SGA1.ExposeV.ExactFunctors
import SGA.SGA1.ExposeV.OverCategories
import SGA.SGA1.ExposeV.FiniteEtaleAlgebra
import SGA.SGA1.ExposeV.FiniteEtaleSpec
import SGA.SGA1.ExposeV.FiniteEtaleGalois
import SGA.SGA1.ExposeV.SchemeGaloisCategory
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality
import SGA.SGA1.ExposeV.FundamentalGroupCovering
import SGA.SGA1.ExposeV.FundamentalGroupArtinian
import SGA.SGA1.ExposeV.FundamentalGroupField
import SGA.SGA1.ExposeV.FundamentalGroupLimit
import SGA.SGA1.ExposeV.FundamentalGroupNormal
import SGA.SGA1.ExposeV.NormalBase
import SGA.SGA1.ExposeV.MultiGalois

/-!
# SGA 1, Exposé V — The fundamental group: generalities

English translation: `translation/SGA1/ExposeV/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §1, quotients by a finite group: `FiniteQuotient`, `FiniteQuotientProperties`,
  `QuotientResidueField`, `QuotientGluing`, `RelativeQuotient`, `FiniteQuotientBaseChange`,
  `QuotientBaseChange`, `QuotientDescent`, `SumOfCopies`;
* §2, decomposition and inertia groups, principal coverings: `DecompositionInertia`,
  `InertiaGroups`, `InertiaEtale`, `PrincipalCovering`, `QuotientPrincipal`;
* §3, quotients of étale coverings and their automorphisms: `QuotientEtale`,
  `QuotientComponents`, `QuotientFiniteEtale`, `QuotientHasQuotients`,
  `EtaleCoveringAutomorphisms`;
* §§4–6, Galois categories (built on mathlib's `PreGaloisCategory`): `GaloisAxioms`,
  `GaloisCategories`, `GaloisEquivalence`, `ExactFunctors`, `OverCategories`;
* §7, the fundamental group of a connected prescheme: `FiniteEtaleAlgebra`, `FiniteEtaleSpec`,
  `FiniteEtaleGalois`, `SchemeGaloisCategory`, `FundamentalGroup`, `FundamentalGroupBasePoint`,
  `FundamentalGroupFunctoriality`, `FundamentalGroupCovering`, `FundamentalGroupArtinian`;
* §8, fields and normal bases: `FundamentalGroupField`, `FundamentalGroupLimit`,
  `FundamentalGroupNormal`, `NormalBase`;
* §9, non-connected preschemes: `MultiGalois`.

No numbered statement of the exposé is left as a `…Statement`. Restrictions:
V.5.9 and V.5.11 are proved for a small Galois category, with the pro-group structure of `Π`
given by the group-valued functor it represents (`fundamentalProGroupRepresentableBy`); V.2.2 is
proved in ring form, for `B` noetherian.
-/
