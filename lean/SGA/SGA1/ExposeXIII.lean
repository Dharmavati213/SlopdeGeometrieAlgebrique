/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXIII.Stacks
import SGA.SGA1.ExposeXIII.EtaleBaseChange
import SGA.SGA1.ExposeXIII.EtaleRestriction
import SGA.SGA1.ExposeXIII.LocallyConstantSheaves
import SGA.SGA1.ExposeXIII.CohomologicalProperness
import SGA.SGA1.ExposeXIII.ExactDiagrams
import SGA.SGA1.ExposeXIII.TameRamification
import SGA.SGA1.ExposeXIII.NormalCrossings
import SGA.SGA1.ExposeXIII.ProLQuotient
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeXIII.ProperHomotopySequence
import SGA.SGA1.ExposeXIII.Coinvariants
import SGA.SGA1.ExposeXIII.ArtinSchreier
import SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP
import SGA.SGA1.ExposeXIII.RegularLocalRing
import SGA.SGA1.ExposeXIII.RootAdjunction
import SGA.SGA1.ExposeXIII.KummerCoverings
import SGA.SGA1.ExposeXIII.AbhyankarBasic
import SGA.SGA1.ExposeXIII.AbhyankarSmooth
import SGA.SGA1.ExposeXIII.AbhyankarPurity
import SGA.SGA1.ExposeXIII.AbhyankarDescent
import SGA.SGA1.ExposeXIII.Abhyankar
import SGA.SGA1.ExposeXIII.DirectImageFiniteness

/-!
# SGA 1, Exposé XIII — Cohomological properness of sheaves of sets and of non-commutative groups

English translation: `translation/SGA1/ExposeXIII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §0–§1, stacks, étale sheaves and cohomological properness: `Stacks`, `EtaleBaseChange`,
  `EtaleRestriction`, `LocallyConstantSheaves`, `CohomologicalProperness`, `ExactDiagrams`;
* §2, tame ramification and divisors with normal crossings: `TameRamification`,
  `NormalCrossings`, `ProLQuotient`;
* §4, homotopy exact sequences: `SchemeFundamentalGroup`, `HomotopySequence`,
  `ProperHomotopySequence`, `Coinvariants`;
* Remark 2.13, the affine line in characteristic `p`: `ArtinSchreier`,
  `AffineLineFundamentalGroup`, and the case `g = 0`, `n = 1` of XIII.2.12,
  `π₁^{p'}(𝔸¹_k) = 1`: `AffineLinePrimeToP`;
* Appendix I, Abhyankar's lemma: `RegularLocalRing`, `RootAdjunction`, `KummerCoverings`,
  `AbhyankarBasic`, `AbhyankarSmooth`, `AbhyankarPurity`, `AbhyankarDescent`, `Abhyankar`;
* Appendix II, finiteness of direct images of stacks: `DirectImageFiniteness`.

§3 (local acyclicity, SGA 4 XV) is not formalized. The items still stated as `…Statement` are
listed in `docs/formalization.md`.
-/
