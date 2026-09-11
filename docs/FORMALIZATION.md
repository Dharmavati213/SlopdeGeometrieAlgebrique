# Formalization notes

The Lean library is a **scaffold**. Fill it exposé by exposé; do not
expect a complete formalization of SGA 1 VI in the first commit.

## What mathlib already has

These are the names to import, not to redo.

| SGA 1 VI | Mathlib |
| --- | --- |
| VI.2 category over another | a functor `p : 𝒳 ⥤ 𝒮` |
| VI.4 fiber-category | `CategoryTheory.Functor.Fiber`, `HasFibers` |
| VI.5.1 cartesian morphism | `Functor.IsCartesian` |
| strongly cartesian | `Functor.IsStronglyCartesian` (Stacks 02XK) |
| VI.6.1 prefibered / fibered | `Functor.IsPreFibered`, `Functor.IsFibered` |
| VI.8 cloven / Grothendieck construction | `∫ᶜ`, `Pseudofunctor.CoGrothendieck.forget` |
| VI.10 cocartesian | `Functor.IsCocartesian` |
| descent data, (pre)stack | `Pseudofunctor.DescentData`, `IsPrestack`, `IsStack` |

Entry point: `SGA/SGA1/ExposeVI.lean`.

## Suggested next lemmas (when someone sits down to formalize)

Not done. Natural first targets, matching the exposé:

1. Categories fibered in groupoids (remark after VI.6.1).
2. Cofibered / bifibered packages around `IsCocartesian` (VI.10).
3. Cartesian functors and the dictionary with cleavages (VI.12).

Put new files next to `ExposeVI.lean` (`SGA/SGA1/ExposeVI/…`) and import
them from the barrel module.
