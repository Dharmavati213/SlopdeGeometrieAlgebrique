# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1 and SGA 2.
Mathlib already has the language of the exposés; we import it and add
the statements that are still missing.

## Exposé I — Étale morphisms

Entry point: `lean/SGA/SGA1/ExposeI.lean`.

SGA works with locally noetherian schemes after no. I.2 and defines
étale as flat + unramified of finite type. Mathlib's `Etale` is
formally étale of finite presentation. On a locally noetherian base
these agree (`etale_of_flat_unramified_locallyNoetherian`).
Universally injective is SGA's radicial.

| SGA 1 I | Mathlib |
| --- | --- |
| I.1 `Ω¹_{X/Y}` | `Ω[S⁄R]`, `FormallyUnramified` |
| I.2 quasi-finite | `Algebra.QuasiFinite`, `LocallyQuasiFinite`, `QuasiFiniteAt` |
| I.3 net / unramified | `FormallyUnramified`, `Algebra.Unramified` |
| I.3.1 residue / `mS = n` | `FormallyUnramified.iff_map_maximalIdeal_eq` |
| I.3.4 graph | `pullback_lift_diagonal_isPullback` |
| I.4 étale | `Etale`, `Algebra.Etale` |
| I.4.9 covering | `IsFinite` + `Etale`, `CommAlgCat.FiniteEtale` |
| I.5.1 étale + radicial | `IsOpenImmersion.of_flat_of_mono` |
| I.5.5 uniqueness | `FormallyUnramified.hom_ext` |
| I.7 standard étale | `StandardEtalePair`, `IsStandardEtale` |
| I.7.6–I.7.8 | `IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, `IsEtaleAt.exists_isStandardEtale` |
| I.9.5 integral closure | `TensorProduct.toIntegralClosure_bijective_of_smooth` |
| I.10 normalisation | `Scheme.Hom.toNormalization` |

## Exposé VI — Fibered categories and descent

These are the names to import, not to redo.

| SGA 1 VI | Mathlib |
| --- | --- |
| VI.2 category over another | `BasedCategory`, `BasedFunctor`, `BasedNatTrans` |
| VI.4 fiber-category | `CategoryTheory.Functor.Fiber`, `HasFibers` |
| VI.5.1 cartesian morphism | `Functor.IsCartesian` |
| strongly cartesian | `Functor.IsStronglyCartesian` (Stacks 02XK) |
| VI.6.1 prefibered / fibered | `Functor.IsPreFibered`, `Functor.IsFibered` |
| VI.8 cloven / Grothendieck construction | `∫ᶜ`, `Pseudofunctor.CoGrothendieck.forget` |
| VI.9 split (1-functor) | `Functor.toPseudofunctor'` then `∫ᶜ` |
| VI.10 cocartesian | `Functor.IsCocartesian` |
| descent data, (pre)stack | `Pseudofunctor.DescentData`, `IsPrestack`, `IsStack` |

Entry point: `lean/SGA/SGA1/ExposeVI.lean`.

## Corrections relative to the English draft

- Both quasi-inverse identities are required for an equivalence of
  categories (VI.1). A one-sided `GF ≅ id` is not enough; see
  `Examples.selectFalse_not_isEquivalence`.
- The remark after VI.6.1 needs prefiberedness in (i). All morphisms
  cartesian does not imply lifts exist; see
  `Examples.oneToTwo_not_prefibered`.
- Ordinary equivalence is weaker than equivalence over the base
  (VI.4.2); see `Examples.oneToTwo_not_basedEquivalence`.

## Remaining gaps in Exposé I

- I.2.1(iii): quasi-finite local homomorphisms via finiteness of completions.
- I.3.7 / I.4.4: unramified (resp. étale) iff the map of completions is a
  quotient (resp. an isomorphism), when the residue extension is trivial.
- I.4.10: discriminant / trace pairing criterion for étale coverings.
- I.5.3–I.5.4 in full: a section of a connected unramified scheme is an
  isomorphism onto a connected component; two morphisms that agree
  geometrically at a point are equal. Open-and-closed immersions of the
  section are in `Fundamental.lean`; identification with a component uses
  locally noetherian connectedness.
- I.5.5 existence / I.8.3 essential surjectivity: étale schemes lift
  uniquely along nilpotent closed immersions; existence of the lift of
  the scheme (not just of morphisms) remains.
- I.6.1 over a complete local ring (the artinian case of I.6.2 is proved).
- I.8.4: étale coverings of a locally noetherian formal scheme.
- I.9.1 in general (regularity of local étale algebras); the identification
  `m_A S = m_S` is recorded.
- I.9.5(ii) and I.9.11: unramified + injective over a normal local ring
  is étale; dominant unramified over a normal base is étale.
- I.10.3, I.10.7–I.10.12: the equivalence with unramified extensions of
  the function field, and the counting of geometric fibre points.
- I.11: the examples, and étale descent along a universal homeomorphism
  (IX.4.10).

## Remaining gaps in Exposé VI

- VI.6.3–6.8, VI.6.10 (fiber products of cartesian arrows, fiberwise
  criterion for cartesian functors).
- VI.7.2 converse, VI.7.3–7.4 (normalized cleavages, associativity of
  `c_{f,g}`).
- VI.10.1 (prefibered + precofibered ⇒ fibered iff cofibered).
- VI.11(a)–(d), (f)–(g) beyond the discrete-base case.
- VI.12.1 as an isomorphism of functor categories (only the constraint
  data of a total functor is recorded).

## SGA 2, Exposé I — Local cohomological invariants

Entry point: `lean/SGA/SGA2/ExposeI.lean`.

Exposé I is topological (abelian sheaves on a space `X`, functors `Γ_Z`
and their derived functors `H_Z^*`). Mathlib supplies flasque sheaves,
pushforward/pullback, `Ext` on Grothendieck abelian sheaf categories, and
the *algebraic* local cohomology of modules. This repo defines topological
`H_Z^*` for closed supports as `Ext(ℤ_{Z,X}, −)` following I.2.3 bis.

| SGA 2 I | Mathlib / this repo |
| --- | --- |
| I.1 `Γ_Z` (closed `Z`) | `gammaZ`, `gammaZSections` (`GammaZ.lean`) |
| I.1 (8) `Γ̲_Z` sheaf | `underlineGammaZ` = `ker(F → j_* j^* F)` (`UnderlineGammaZ.lean`) |
| I.1 (3) locally closed | `LocallyClosedIn`, `LocallyClosedIn.gamma` |
| I.1 independence of open | `gammaZSections_restrict_addEquiv` |
| I.1 special cases | closed pushforward, open restriction, `underlineGamma_locallyClosed`; `zZX_closed` |
| I.1.8 degree 0 | `exact_gammaZ_of_le`, `I_1_8_package`; global flasque extension |
| I.2.1 / I.2.3 bis `H_Z^n` | `H_Z Z F n` := `Ext (zZX_closed Z) F n` |
| I.2.2 degree-zero excision | `I_2_2_degree_zero`, `I_2_2_excision_degree_zero` |
| I.2.11 model for `ℋ_Z^n` | `sheafH_Z_n` defined by ker / coker / `rightDerived` |
| I.2.6 candidate E₂ terms only | `localToGlobalE2Term`; no spectral sequence or convergence theorem |
| Homological input for I.2.8 | `ext_contravariant_exact`, assuming a supplied short exact sequence |
| Input for I.2.12 | `TopCat.Sheaf.IsFlasque`; higher Ext vanishing on injectives |
| I.2.13 degree 0 and 0–1 | kernel vanishing iff the unit is mono; kernel and cokernel vanishing iff it is an isomorphism |
| I.2.1 algebraic `H_J^i(M)` | `localCohomology` (`LocalCohomology.lean`) |
| III depth / Rees | `ModuleCat.exists_isRegular_tfae` |

### Remaining gaps in SGA 2 Exposé I

The modules compile without placeholders, but Exposé I remains partial.
Definitions chosen from later characterizations do not prove the comparison
with the original derived functors. In particular:

- I.1.1–I.1.7: general extension by zero and its adjunction with `i^!`,
  preservation of injectives, internal Hom identities, and the ringed-space
  versions. The existing open adjunction is `i^* ⊣ i_*`.
- I.1.9–I.1.10: construct the actual short exact sequence of sheaves for a
  closed/open decomposition; the existing nested-support equality is global.
- I.2.1–I.2.5: compare the Ext and ker/coker models with derived supported
  sections, higher-degree excision, and the sheafification comparison.
- I.2.6: construct the local-to-global spectral sequence and prove convergence.
- I.2.8–I.2.10: specialize the Ext sequence to the support decomposition and
  construct the corresponding sheaf sequence.
- I.2.12–I.2.14: flasque acyclicity and its converse, and higher-degree
  vanishing/restriction criteria.

## SGA 2, Exposé II — Algebraic foundations

Entry point: `lean/SGA/SGA2/ExposeII.lean`. This continues the Exposé I work
from [PR #11](https://github.com/Dharmavati213/SlopdeGeometrieAlgebrique/pull/11).
The source is `translation/SGA2/ExposeII/en-body.tex`.

| SGA 2 II | Proved algebraic content |
| --- | --- |
| (7.5), annihilator union | `powerTorsion I M`, with membership equivalent to annihilation by some `I^n` |
| (7.5), quotient Hom | `quotientHomEquivTorsionBySet`: evaluation at 1 identifies `Hom(R/I, M)` with the submodule annihilated by `I` |
| Support invariance | `powerTorsion_eq_of_radical_eq` for finitely generated ideals, and a noetherian-ring specialization |
| II.9(c) ⇒ (b), diagram step | `IsEssentiallyZero.isZero_hom_colimit`: the Hom colimit of an essentially zero inverse sequence is zero |
| II.11, system arguments | `IsEssentiallyZero.of_mono`, `.of_epi`, `.of_exact`: closure under subobjects, quotients, and extensions |
| II.11, one-generator annihilators | `exists_uniform_torsionTransition_eq_zero`, `principal_annihilator_system_essentially_zero` |
| II.9 / II.11 connection | `principalAnnihilatorSystem_isZero_hom_colimit` |

`Torsion.lean` supplies the degree-zero module algebra. `Principal.lean`
proves stabilization of the annihilators of `f^n` in a noetherian module,
including transition maps and naturality. `EssentiallyZero.lean` proves the
general diagram arguments, and `PrincipalSystem.lean` connects the two APIs.

### Remaining gaps in SGA 2 Exposé II

- II.1–II.4: quasi-coherence and the affine sheaf-cohomology sequences.
- II.5: comparison with Koszul cohomology.
- II.6–II.8: comparison of topological `H_{V(I)}^*(Spec R, M̃)` with the
  Ext colimit `localCohomology I i`, including the canonical comparison map.
- (7.5): identify the categorical Hom colimit with `powerTorsion` and then
  with degree-zero Koszul cohomology; the finite-stage Hom equivalence and
  annihilator union are proved.
- II.9: the full equivalence, including injective coefficients and the
  Koszul-Hom comparison; the generic colimit-vanishing step is proved.
- II.10: the flasque-sheaf criterion.
- II.11: identify the principal annihilator system with Koszul homology,
  prove higher-degree vanishing for one generator, and complete the induction
  on the number of generators.
