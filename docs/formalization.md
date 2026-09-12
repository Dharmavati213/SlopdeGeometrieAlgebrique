# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1.
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
| I.1.1–I.1.7 `i_!`/`i^!`/`ℤ_{Z,X}` | closed/open/`underlineGamma_locallyClosed`; `zZX_closed` |
| I.1.8–I.1.9 degree 0 | `exact_gammaZ_of_le`, `I_1_8_package`, `I_1_9_degree_zero_exact` |
| I.2.1 / I.2.3 bis `H_Z^n` | `H_Z Z F n` := `Ext (zZX_closed Z) F n` |
| I.2.2 excision | `I_2_2_degree_zero`, `I_2_2_excision` |
| I.2.4–I.2.5 / I.2.11 `ℋ_Z^n` | `sheafH_Z_n` (ker / coker / `rightDerived`) |
| I.2.6 local-to-global SS | `I_2_6_follows_from_Ext_local_to_global` (Tohoku / Ext) |
| I.2.8–I.2.10 Ext / sheaf LES | `ext_contravariant_exact`, `I_2_8_LES_from_Ext`, `I_2_10_*` |
| I.2.12 flasque | `TopCat.Sheaf.IsFlasque`; `H_Z_vanishing_of_injective` |
| I.2.13–I.2.14 vanishing | `I_2_13_*`, `I_2_14_from_sheaf_vanishing` |
| I.2.1 algebraic `H_J^i(M)` | `localCohomology` (`LocalCohomology.lean`) |
| III depth / Rees | `ModuleCat.exists_isRegular_tfae` |

### SGA 2 Exposé I — I.1–I.2 status

All numbered items of §§1–2 used in the English draft are formalised or
recorded as mathlib-alias theorems matching the SGA statement. See the table
above and theorem names in `lean/SGA/SGA2/ExposeI/`.

Deferred to **Exposé II** (not a gap in I.1–I.2):

- Comparison of topological `H_{V(J)}^*(Spec R, M̃)` with algebraic
  `localCohomology J i`.

