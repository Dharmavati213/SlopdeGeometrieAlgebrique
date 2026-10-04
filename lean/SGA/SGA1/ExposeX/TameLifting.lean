/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TameSpecialization

/-!
# SGA 1, Exposé X, 3.7–3.8: the core of the tame specialization theorem

SGA proves X.3.8 by reducing it (X.3.7) to the case where the base is the spectrum of a complete
discrete valuation ring `R` with algebraically closed residue field, `y₀` the closed point and
`y₁` the generic point; there the specialization homomorphism is `π₁(X_η̄) → π₁(X)` (up to the
isomorphism `π₁(X₀) ≅ π₁(X)` of X.2.1), and X.3.8 says that every continuous homomorphism of
`π₁(X_η̄)` to a finite group of order prime to `p` factors through it. The argument then uses
Abhyankar's lemma X.3.6 at the generic point of the closed fibre of `X_{V'}` (`V'` the
normalization of `R` in a finite separable extension of its fraction field) and purity X.3.1.

`TameLiftingDVRStatement` records this core, for the actual map `π₁(X_η̄) → π₁(X)` (the existence
form `TameSpecializationStatement` cannot be used to identify the kernel of a given map), over a
complete discrete valuation ring whose residue field is only assumed separably closed (the
residue fields of the `V'` are then purely inseparable over it, and the closed fibres differ by a
universal homeomorphism). It is the input needed for the second part of XIII.4.4 over a regular
base, where the bases are completions of strict henselizations of discrete valuation rings.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeX

/-- X.3.8, the core (the case to which SGA reduces X.3.8 in X.3.7; proved as
`SGA.SGA1.ExposeX.tameLiftingDVRStatement` in `SGA.SGA1.ExposeX.TameLiftingProof`). Let `R` be a
complete discrete valuation ring with separably closed residue field `k` of characteristic
exponent `p`, `f : X ⟶ Spec R` proper and smooth with geometrically connected fibres, and
`η̄ : Spec Ω₁ ⟶ Spec R` a geometric generic point (`Ω₁` algebraically closed, `R → Ω₁`
injective). Then every continuous homomorphism of `π₁(X_η̄, a)` into a finite group of order prime
to `p` factors through the homomorphism `π₁(X_η̄, a) → π₁(X, a)` induced by `X_η̄ ⟶ X`.

With X.2.1 (`π₁(X₀) ≅ π₁(X)`) and the invariance of `π₁` of the closed fibre under the purely
inseparable extension `k̄ / k`, this is X.3.8 for `Y = Spec R`, `y₁` the generic and `y₀` the
closed point, the specialization homomorphism being `π₁(X_η̄) → π₁(X) ≅ π₁(X̄₀)`. -/
def TameLiftingDVRStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)] ⦃X : Scheme.{u}⦄
    (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (Ω₁ : Type u) [Field Ω₁] [IsAlgClosed Ω₁] [Algebra R Ω₁],
    Function.Injective (algebraMap R Ω₁) →
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (a : Spec (.of Ω) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Ω₁)))),
      FactorsPrimeTo
        (ExposeV.etaleFundamentalGroup.map Ω
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R Ω₁)))) a)
        (ringExpChar (ResidueField R))

end SGA.SGA1.ExposeX
