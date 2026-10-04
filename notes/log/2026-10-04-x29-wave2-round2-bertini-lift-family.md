---
author: x29
date: 2026-10-04
area: SGA1 X, Foundations/Projective, sga1-oos-coord
kind: handoff
---

# X.2.9 wave 2 round 2: X.2.10 (Bertini), char 0 for every cardinality, the W(k) family

Wrapped up at the coordinator's request (16:45). Every module listed builds with `lake build`
(one at a time), is sorry-free, and `#print axioms` on the main declarations shows only
propext, Classical.choice, Quot.sound. Only new files of my patterns; outside them I edited only
my registry rows (A29, A53) and my now-note. The round was interrupted once; the first attempt's
work (items 1–3) builds and was checked at the start of the resumed attempt.

## Done

1. **Review fixes** of round 1 (duplicate `apply_genericPoint` replaced by
   `ExposeXI.genericPoint_eq_of_surjective`; `toMv`/`ofMv` replaced by
   `Polynomial.Bivariate.equivMvPolynomial`; A39 status; `BertiniField` namespace/universe).
2. **X.2.9 in characteristic 0, every cardinality** (universe 0):
   `SGA.SGA1.ExposeX.isTopologicallyFG_etaleFundamentalGroup_of_charZero` and X.2.12
   `finite_principalH1_of_charZero` (`SGA1/ExposeX/TopologicallyFiniteCharZeroDescent.lean`):
   descend to a countable algebraically closed `k₀` (ega4-8's
   `Scheme.exists_isPullback_of_isAlgClosed_countable`), properness by fpqc descent, X.1.8.
3. **X.2.10 (Bertini) in existence form, every characteristic, no projectivity**:
   `SGA.SGA1.ExposeX.exists_hyperplane_section`; hence `topologicallyFiniteStatement_of_curve`
   and **`topologicallyFiniteStatement_of_planeCurve`** (X.2.9 in universe `u` ⇐ π₁ of every
   plane curve `planeCurve k x y` of a plane model is t.f.g.) in
   `SGA1/ExposeX/TopologicallyFiniteBertini.lean`; pieces in
   `TopologicallyFiniteHyperplane{,Covers}.lean` and
   `Foundations/Projective/Bertini{Field,FieldLemma,Connected,Dimension,Covers}.lean`
   (field lemma `Bertini.mem_of_isAlgebraic`; registry A53 has the full list).
4. **The lifted plane curve as a family over a complete DVR** (new, registry A29 (a)):
   `R` a DVR, `π` uniformizer, `[IsAdicComplete (span {π}) R]`, `φ : R → k` onto the residue
   field, `G ∈ R[xᵢ]` homogeneous with `φ(G)` prime of the same total degree.
   - `Foundations/Projective/PlaneModelLift.lean`: **`IsAdicComplete.mem_range_algebraMap_of_aeval_eq_zero`**
     (`k` algebraically closed; `O` a domain, `π`-separated, `πO` prime: a root in `O` of a
     polynomial over `R` with nonzero reduction lies in `R`; an elementary π-adic iteration, no
     valuation theory), helper `Polynomial.exists_eq_C_pow_mul_of_ne_zero`.
   - `PlaneModelHypersurface.lean`: `ProjHypersurface.ideal`, `projHypersurface G hG`,
     `prime_of_prime_map` (UFD local `R`), `baseChangeEquiv` (`R' ⊗_R R[x]/(G) ≅ R'[x]/(G')`,
     graded: `baseChangeGradedHom`), `baseChangeProjIso`, **`isPullback_baseChange`** (fibres
     of `V₊(G)` are `V₊(G')`).
   - `PlaneModelFamily.lean`: `Proj.isClosedImmersion_map` (Proj of a surjective graded map),
     `Proj.isIntegral_of_isDomain`, `Proj.isReduced_of_isReduced`, `Proj.isDomain_away`,
     `HomogeneousIdeal.irrelevant_le_map_of_surjective`; `ProjHypersurface.embedding` into
     `ℙ(σ; Spec R)` (closed immersion, `embedding_over`), `isProper_toSpec`, `flat_toSpec`.
   - `PlaneModelLiftFamily.lean`: `isDomain_quotient`, `injective_algebraMap`,
     **`geometricallyReduced_toSpec`** (`R` char 0, `k` perfect; case split on the kernel of
     `R → K`), chart lemmas (`isDomain_chart`, `isPrime_span_chart`, `isNoetherianRing_chart`,
     `eq_zero_of_forall_mem_span_pow_chart`), **`bijective_appTop`** (`Γ(V₊(G), 𝒪) = R`,
     `k = k̄`, `σ` finite, `x_{i₀} ∉ (φ G)`), **`geometricallyConnected_toSpec`** (Zariski,
     `CohomologyAux.geometricallyConnected_of_isIso_app`).

## What was hard

- `Γ(V₊(G)) = R` without cohomology: the trick is that a global section restricted to the chart
  `B = A_(x_{i₀})` is integral over `R`, `B` is noetherian and `π`-separated (Krull), and
  `B ⧸ πB ≅ k ⊗_R B ≅ (k ⊗_R A)_(1 ⊗ x)` is the chart of `V₊(F)`, a domain
  (`quotIdealMapEquivTensorQuot`, `Proj.awayBaseChangeEquiv`). Then the π-adic iteration.
- `IsZariskiLocalAtSource @Flat` is not found by instance search in a scratch file without
  `-DmaxSynthPendingDepth=3`; in `flat_toSpec` I provide it with
  `HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)`.
- `Ideal.span {G}` vs `(ideal G hG).toIdeal`: defeq but `rw` fails across them; state all quotient
  rings with `(ideal G hG).toIdeal` (`baseChangeEquiv` takes `hG`).
- `f.app ⊤` lands in `Γ(X, f ⁻¹ᵁ ⊤)`: use `congrArg (fun z ↦ ι.hom z)` instead of `rw`.

## Next (exact plan for the char-p plane-curve case, then `TopologicallyFiniteStatement.{0}`)

New file `SGA1/ExposeX/CurveFiniteLift.lean` (or `TopologicallyFiniteCharP.lean`):
1. `R = WittVector p k` (`k = k̄`, char `p`): mathlib gives `IsDiscreteValuationRing`,
   `IsAdicComplete (span {p})`, `constantCoeff` with `ker = span {p}` (`ker_constantCoeff`,
   surjective). Prove `CharZero (𝕎 k)` (p-torsion free + `p ≠ 0` + `n` prime to `p` a unit).
2. Lift `F = homog d (equivMvPolynomial k f)` coefficientwise (section of `constantCoeff`, keep
   zero coefficients zero) to `G`, homogeneous of degree `d`, same total degree, `φ(G) = F`;
   `F` prime from `toIdeal_ideal_eq_span` + `isPrime_ideal`; `X 0 ∉ (F)` since `dehom F = f`
   has positive degree in `t`.
3. X.2.4: `ExposeX.exists_continuous_surjective_specialization_of_isClosedImmersion` with
   `κ = embedding G hG` (`Fin 3` finite), `IsSeparable = Flat + GeometricallyReduced`
   (`flat_toSpec`, `geometricallyReduced_toSpec`), `geometricallyConnected_toSpec`;
   `b₀ = Spec k → Spec R` (`φ`), `b₁ = Spec (AlgebraicClosure (FractionRing R)) → Spec R`
   (generic point specializes to the closed point of a local scheme).
4. Generic geometric fibre: proper (base change) and connected (geometrically connected), char 0,
   `Type` ⇒ `isTopologicallyFG_etaleFundamentalGroup_of_charZero`; transfer along the continuous
   surjection.
5. Special fibre `pullback f b₀ ≅ projHypersurface F ≅ planeCurve k x y`
   (`isPullback_baseChange` with `R' = k` via `φ.toAlgebra`; `ideal k x y = ideal F` by
   `toIdeal_ideal_eq_span` + `HomogeneousIdeal.ext`); t.f.g. along the iso
   (`ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_family`).
6. Char 0: `planeCurve` is proper and connected (integral), apply the char-0 theorem directly.
7. `topologicallyFiniteStatement_of_planeCurve` ⇒ `TopologicallyFiniteStatement.{0}`.
8. Universes above 0 remain: needs a universe transport of `π₁` (no tool in the repo).

## For the coordinator (sga1-oos-coord)

- Barrels: `SGA/SGA1/ExposeX.lean`: `CurveFinitePlaneModel`, `TopologicallyFiniteBertini`,
  `TopologicallyFiniteCharZeroDescent`, `TopologicallyFiniteHyperplane`,
  `TopologicallyFiniteHyperplaneCovers`. `SGA/Foundations.lean`:
  `NormalizationFiniteDimension`, `Projective.{PlaneModelCurve, PlaneModelEquation,
  PlaneModelLift, PlaneModelHypersurface, PlaneModelFamily, PlaneModelLiftFamily,
  BertiniConnected, BertiniField, BertiniFieldLemma, BertiniDimension, BertiniCovers}`.
- Rename at integration (reviewer's point): `Foundations/NormalizationFiniteDimension.lean` holds
  only `topologicalKrullDim_eq_trdeg_functionField` (Stacks 0A21); a better home is
  `Foundations/Dimension/FunctionField.lean`. `BertiniDimension.lean`'s two general lemmas could
  also move to `Foundations/Dimension`.
- Docs: X.2.9 row of `lean/SGA/Foundations/README.md`: X.2.10 proved
  (`exists_hyperplane_section`); X.2.9 ⇐ plane curves in every characteristic
  (`topologicallyFiniteStatement_of_planeCurve`); char 0 for every cardinality, universe 0
  (`isTopologicallyFG_etaleFundamentalGroup_of_charZero`); the W(k) family of a plane curve is
  proper, flat, geometrically reduced and connected (`PlaneModelLiftFamily`). Open: the final
  W(k) assembly (steps 1–7 above), universes above 0.
