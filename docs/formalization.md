# Formalization notes

The Lean library in `lean/` follows Grothendieck's numbering of SGA 1,
Exposé VI. Mathlib already has the language of the exposé; we import it
and add the statements that are still missing.

## What mathlib already has

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

## Remaining gaps in this exposé

- VI.6.3–6.8, VI.6.10 (fiber products of cartesian arrows, fiberwise
  criterion for cartesian functors).
- VI.7.2 converse, VI.7.3–7.4 (normalized cleavages, associativity of
  `c_{f,g}`).
- VI.10.1 (prefibered + precofibered ⇒ fibered iff cofibered).
- VI.11(a)–(d), (f)–(g) beyond the discrete-base case.
- VI.12.1 as an isomorphism of functor categories (only the constraint
  data of a total functor is recorded).
