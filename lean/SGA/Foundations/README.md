# Foundations

Prerequisites of the SGA 1 formalization that mathlib does not have. They are written as if for
mathlib: mathlib namespaces and naming, no SGA numbers in names, and module docstrings citing EGA,
SGA 4 or the Stacks Project. The barrel is `SGA.Foundations` (`SGA/Foundations.lean`), whose
docstring lists the areas covered.

## Out of scope

Some results of SGA 1 rest on theories that the seminar quotes from elsewhere and that this
project does not build: Hodge theory, abelian varieties, resolution of singularities, complex
analytic geometry beyond the local theory, triangulation, and the étale cohomology of SGA 4.
For each such result the Lean files keep the faithful statement as a `Prop`-valued `…Statement`
definition, and every consequence SGA draws from it is proved with the statement as a hypothesis.

Items in the order of the exposés:

| SGA 1 | Lean statement (file under `SGA/SGA1/`) | Missing input |
| --- | --- | --- |
| X.2.9: `π₁` of a proper connected variety is topologically finitely generated | `TopologicallyFiniteStatement` (`ExposeX/Semicontinuity.lean`) | The transcendental theorem X.2.6 for curves, which uses the Riemann existence theorem over `ℂ` (see XII.5.1 below) before specializing. |
| XI.1.4 (Serre): a smooth unirational variety in characteristic 0 is simply connected | `SerreUnirationalSimplyConnectedStatement` (`ExposeXI/Geometry.lean`) | Hodge theory in characteristic 0 (`h^{0,i} = h^{i,0}`, so no global forms gives `Hⁱ(𝒪_X) = 0`), and multiplicativity of `χ(𝒪)` in finite étale coverings (Riemann–Roch). XI.1.3 (finite `π₁`) is proved. |
| XI.2.1 (Serre–Lang): étale coverings of an abelian variety are dominated by multiplication by `n` | `SerreLangStatement` (`ExposeXI/Geometry.lean`) | The theory of abelian varieties: rigidity and the theorem of the cube, connected étale coverings of an abelian variety are isogenies, `[n]` is an isogeny. The commutativity of `π₁` of an abelian variety (XI.2) is proved. |
| XII.5.1, Riemann existence theorem | `RiemannExistenceStatement`, `SchemeRiemannExistenceStatement` (`ExposeXII/RiemannExistence.lean`) | GAGA (coherent analytic sheaves, Cartan's theorems A and B) and the Grauert–Remmert extension of finite analytic coverings. XII.5.2 is proved from it (`schemeFundamentalGroupComparison_of_smooth`, `schemeFundamentalGroupComparison`). |
| XII.5.2 for singular `X` | `LocallyContractibleStatement` (`ExposeXII/FundamentalGroup.lean`) | Triangulation of complex algebraic varieties (Łojasiewicz). The smooth case is proved (`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`). |
| XIII 1.4 for sheaves of sets | `ProperBaseChangeStatement` (`ExposeXIII/CohomologicalProperness.lean`) | The proper base change theorem (SGA 4 XII 5.1). XIII 1.9 is proved for finite morphisms without it. |
| XIII.4.3 and XIII.4.4, second and third parts | `ProperSmoothHomotopyExactSequenceStatement`, `NormalCrossingsHomotopyExactSequenceStatement`, `NormalCrossingsShortExactSequenceStatement` (`ExposeXIII/ProperHomotopySequence.lean`) | The local constancy of `R¹f_*` (XIII.1.16) and the cohomological properness of tamely ramified coverings (XIII.2.9), which rest on the proper base change theorem above. The first part of XIII.4.4 is proved. |
| XIII §3 (3.1–3.5) | not formalized | Local acyclicity of smooth morphisms (SGA 4 XV) and a resolution-of-singularities hypothesis. |
| XIII.4.6 (Künneth formula) in characteristic 0 | `KunnethCharZeroStatement` (`ExposeXIII/SchemeFundamentalGroup.lean`) | Resolution of singularities (Hironaka), which gives SGA's desingularization hypotheses. The proper case is proved for `π₁^L` (`bijective_proLMap_prod_of_isProper`), and X.1.7 is proved. |
| XIII.2.13: Abhyankar's conjecture for the affine line | `AbhyankarAffineLineStatement` (`ExposeXIII/SchemeFundamentalGroup.lean`) | Raynaud's theorem (1994), proved with rigid analytic geometry; SGA 1 only recalls it. The other assertions of XIII.2.13 do not need it and are proved: `not_isTopologicallyFG_fundamentalGroup_affineLine`, `affineLineArtinSchreier`, and the necessity half `sylowSup_eq_top_of_affineLine`. |

XIII.2.12 for general `g` and `n` (the tame fundamental group of a curve) is not formalized
either: SGA lifts the curve to characteristic 0 and applies Riemann existence. Its case `g = 0`,
`n = 1` (`π₁^{p'}(𝔸¹) = 1`) is proved by an algebraic argument instead
(`affineLinePrimeToPTrivialStatement`, from `SGA/SGA1/ExposeXI/TameCovering.lean` and
`TameGaloisCovering.lean`).

Every other `…Statement` that is still open is work in progress, not out of scope.
