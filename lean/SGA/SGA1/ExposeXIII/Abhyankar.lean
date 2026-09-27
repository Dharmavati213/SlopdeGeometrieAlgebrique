/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXIII.AbhyankarSmooth
import SGA.SGA1.ExposeXIII.AbhyankarDescent

/-!
# SGA 1, Exposé XIII, Appendix I: Abhyankar's lemma

Let `X = Spec A` be a regular local scheme, `D = Σ div fᵢ` with the `fᵢ` part of a regular system
of parameters, `U = X - Supp D = Spec A[1/∏ fᵢ]`, and `V = Spec B` an étale covering of `U`
tamely ramified along `D` (XIII.2.3 c), `IsTamelyRamifiedAlong`).

* XIII.5.2 (`AbsoluteAbhyankarStatement`): with `nᵢ` the l.c.m. of the ramification indices above
  `(fᵢ)`, the `nᵢ` are prime to the residue characteristic `p` and `V' = V ×_X X'` extends to an
  étale covering of `X' = X[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. The extension is proved for every `A`
  (`absoluteAbhyankar_extension`): by purity (Zariski–Nagata) it suffices to treat the maximal
  points of `V(∏ Tᵢ)` (`AbhyankarPurity`), where X.3.6 applies after a tame root adjunction
  (`AbhyankarDescent`). That the `nᵢ` are prime to `p` is proved when the `κ((fᵢ))` have
  characteristic `p` (e.g. `A` of equal characteristic, `absoluteAbhyankarAt_of_ringChar_eq`) and
  for `dim A = 1`; in mixed characteristic SGA's descent argument is formalized over strictly
  henselian `A` (5.3 below), but not the reduction of 5.2 to that case.
* XIII.5.3 (`TameCoveringsOfStrictlyLocalStatement`, proved in
  `tameCoveringsOfStrictlyLocalStatement`): over a strictly local `X`, every connected tamely
  ramified covering of `U` is a quotient of a Kummer covering `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` with the `nᵢ`
  prime to `p`: the extension over `X'` splits, and the descent along `X' → X₂`, radicial modulo
  `p`, removes the `p`-parts of the exponents
  (`exists_injective_kummerAlgebra_of_isStrictlyHenselian`).
  With XIII.5.3.0 (`KummerAlgebra.rootsOfUnityToAlgEquiv_bijective`) this is the computation
  `π₁^t(U) ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)^r`, whose formulation needs the tame fundamental group (not
  available).
* XIII.5.4 (`RootAdjunctionSmoothStatement`, proved in `rootAdjunctionSmoothStatement`); its étale
  part is `etale_localization_away_kummerAlgebra`.

XIII.5.5–5.7 (the relative Abhyankar lemma, the relative tame fundamental group and tame torsors)
need tame ramification relative to a base and étale cohomology, and are not formalized.

The proofs are in `AbhyankarBasic` (statements, discrete valuation rings, dimension one),
`AbhyankarSmooth` (5.4), `AbhyankarPurity` (purity, codimension one, equal characteristic) and
`AbhyankarDescent` (extension for all exponents, descent, 5.3).
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeXIII

/-- XIII.5.3 for strictly henselian regular local rings, in every characteristic:
`TameCoveringsOfStrictlyLocalAt A r`. -/
theorem tameCoveringsOfStrictlyLocalAt (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (r : ℕ) :
    TameCoveringsOfStrictlyLocalAt A r :=
  fun f hf B _ _ _ _ _ _ _ hB ↦ exists_injective_kummerAlgebra_of_isStrictlyHenselian A f hf B hB

/-- XIII.5.3 (`TameCoveringsOfStrictlyLocalStatement`): over a strictly local regular scheme, every
connected étale covering of `U = X - D` tamely ramified along the divisor with normal crossings
`D` is a quotient of a Kummer covering `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` with the `nᵢ` prime to `p`. -/
theorem tameCoveringsOfStrictlyLocalStatement : TameCoveringsOfStrictlyLocalStatement.{u} :=
  fun A _ _ _ _ r ↦ tameCoveringsOfStrictlyLocalAt A r

end SGA.SGA1.ExposeXIII
