/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.Geometry
import SGA.SGA1.ExposeXI.NonabelianCohomology
import SGA.SGA1.ExposeXI.CohomologySequence
import SGA.SGA1.ExposeXI.PrincipalCovering
import SGA.SGA1.ExposeXI.Kummer
import SGA.SGA1.ExposeXI.KummerSequence
import SGA.SGA1.ExposeXI.KummerTorsor
import SGA.SGA1.ExposeXI.ArtinSchreier
import SGA.SGA1.ExposeXI.AbelianH1
import SGA.SGA1.ExposeXI.GroupSheaves
import SGA.SGA1.ExposeXI.KummerCohomology
import SGA.SGA1.ExposeXI.ArtinSchreierCohomology
import SGA.SGA1.ExposeXI.PrincipalBundle
import SGA.SGA1.ExposeXI.GroupSchemeSequence
import SGA.SGA1.ExposeXI.ZariskiComparison
import SGA.SGA1.ExposeXI.PicardComparison
import SGA.SGA1.ExposeXI.FundamentalGroupCohomology
import SGA.SGA1.ExposeXI.AffineSheaves
import SGA.SGA1.ExposeXI.AdditiveTorsors
import SGA.SGA1.ExposeXI.MultiplicativeTorsors
import SGA.SGA1.ExposeXI.Representability
import SGA.SGA1.ExposeXI.AssociatedBundle
import SGA.SGA1.ExposeXI.KummerCovering
import SGA.SGA1.ExposeXI.TwistedPrincipal
import SGA.SGA1.ExposeXI.GeneralLinearTorsors
import SGA.SGA1.ExposeXI.FiniteEtaleGroups
import SGA.SGA1.ExposeXI.ContractedProduct
import SGA.SGA1.ExposeXI.ArtinSchreierScheme
import SGA.SGA1.ExposeXI.AbelianFundamentalGroup
import SGA.SGA1.ExposeXI.LatticeIndex
import SGA.SGA1.ExposeXI.EtaleDiscriminant
import SGA.SGA1.ExposeXI.ProjectiveLineAlgebra
import SGA.SGA1.ExposeXI.ProjectiveLine
import SGA.SGA1.ExposeXI.SimplyConnectedProduct
import SGA.SGA1.ExposeXI.ProjectiveLinePower
import SGA.SGA1.ExposeXI.BirationalTransfer
import SGA.SGA1.ExposeXI.GenericLine
import SGA.SGA1.ExposeXI.ProjectiveSpace
import SGA.SGA1.ExposeXI.ProjectiveSpaceSimplyConnected
import SGA.SGA1.ExposeXI.RationalVarieties
import SGA.SGA1.ExposeXI.UnirationalVarieties
import SGA.SGA1.ExposeXI.BirationalInvariance
import SGA.SGA1.ExposeXI.RamifiedLattice
import SGA.SGA1.ExposeXI.TameDiscriminant
import SGA.SGA1.ExposeXI.TameCovering
import SGA.SGA1.ExposeXI.TameGaloisCovering

/-!
# SGA 1, Exposé XI — Examples and complements

English translation: `translation/SGA1/ExposeXI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §1–§3 (projective spaces, unirational and abelian varieties, cones): statements, with
  `π₁ = 0` expressed through finite étale covers and "`π₁` finite" through the fundamental group
  of Exposé V, and the formal Eckmann–Hilton argument (`Geometry`). XI.1.1: `π₁(ℙʳ_k) = 1` for
  `k` algebraically closed and every `r` (`ProjectiveSpaceSimplyConnected`), by the Riemann–Roch
  inequality for a pair of lattices over `F[t]`, `F[t⁻¹]` (`LatticeIndex`,
  `ProjectiveLineAlgebra`) and the constancy of discriminants of étale algebras
  (`EtaleDiscriminant`), applied to `ℙ¹` (`ProjectiveLine`) and to the generic line through a
  point of `ℙʳ` (`GenericLine`, `ProjectiveSpace`); products of simply connected schemes, the
  powers `(ℙ¹)ʳ` and products of projective spaces (`SimplyConnectedProduct`,
  `ProjectiveLinePower`). XI.1.2: a proper normal rational variety is simply connected
  (`RationalVarieties`); XI.1.3: a proper normal unirational variety has finite fundamental group
  (`UnirationalVarieties`); both from purity X.3.3 and XI.1.1. For a given birational map between
  regular varieties, the same follows from X.3.4 (`BirationalTransfer`, `BirationalInvariance`).
  For XIII.2.12 (`g = 0`, `n = 1`): the lattice method for coverings of `ℙ¹` étale over `𝔸¹` and
  tamely ramified at `∞` (`RamifiedLattice`, `TameDiscriminant`, `TameCovering`), and the
  triviality of Galois coverings of `𝔸¹` of degree prime to `p` (`TameGaloisCovering`).
  XI.2, the fundamental group of a proper connected reduced monoid scheme (e.g. an abelian
  variety) over an algebraically closed field is commutative, by X.1.7
  (`AbelianFundamentalGroup`).
* §4 (principal homogeneous bundles): XI.4.1–XI.4.3 over an arbitrary base (`PrincipalBundle`);
  XI.4.4–XI.4.5 for group schemes and sheaves of groups, with the homomorphism properties of `∂`
  and of `H¹` (`GroupSchemeSequence`, `AbelianH1`); XI.4.7, locally trivial bundles and Zariski
  cohomology (`ZariskiComparison`); the group-theoretic sequence of XI.4.5/XI.4.9
  (`NonabelianCohomology`); representability of fpqc sheaves locally represented by affine
  schemes, by VIII.2.1 and Zariski gluing (`Representability`), hence of torsors under affine
  groups (footnote 296) and the associated bundles `P^(H)` (`AssociatedBundle`) and `E^(P)`
  (`ContractedProduct`).
* §5: `(*)` for constant groups, `H¹(S, 𝒢) ≅ Hom(π₁, 𝒢)/conj` (`FundamentalGroupCohomology`,
  group-theoretic side in `NonabelianCohomology`), for a finite `π₁`-group in a Galois category
  (`TwistedPrincipal`), and for a finite étale group scheme `G`,
  `H¹(S, G) ≅ H¹(π₁(S, s̄), G(s̄))` (`FiniteEtaleGroups`); XI.5.1 and
  XI.5.3 for `𝔾_a`, `𝔾_m` (Hilbert 90) and `GL_n` (`AdditiveTorsors`, `MultiplicativeTorsors`,
  `GeneralLinearTorsors`, `PicardComparison`), with the reduction to a faithfully flat affine
  covering in `AffineSheaves`; affine principal coverings (`PrincipalCovering`).
* §6 over affine bases: `Kummer`, `KummerSequence`, `KummerTorsor` (Kummer coverings are torsors
  under the Hopf algebra `R[ℤ/n]`), `ArtinSchreier`; over an arbitrary base, in fpqc cohomology:
  the sheaves `𝔾_a`, `𝔾_m` (`GroupSheaves`), exactness of the Kummer and Artin–Schreier sequences
  and XI.6.4–6.6, XI.6.8–6.10 (`KummerCohomology`, `ArtinSchreierCohomology`,
  `CohomologySequence`), with `Pic(S)` in `PicardComparison`; over an affine base, `∂ a` is the
  class of the Kummer covering `Spec Γ(S)[T]/(Tⁿ - a)` (`KummerCovering`); `(ℤ/p)_S` is the
  constant group scheme `ℤ/p = Spec Γ(S)[T]/(Tᵖ - T)` and, for `S` connected and affine,
  `Γ(S)/℘Γ(S) ≅ Hom_cont(π₁(S), ℤ/p)` (`ArtinSchreierScheme`).

Not formalized: the identification of `H¹(S_Zar, GL_n(𝒪_S))` with locally free Modules of rank
`n`; Serre's theorem XI.1.4 (Hodge theory) and the Serre–Lang theorem XI.2.1 (statements only).
-/
