/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeX.Semicontinuity

/-!
# SGA 1, Exposé X, 3.8–3.9: specialization of the tame fundamental group

X.3.8 (for `f` proper and smooth with geometrically connected fibres, the specialization
homomorphism `π₁(X̄₁) → π₁(X̄₀)` is surjective and every continuous homomorphism of `π₁(X̄₁)` to a
finite group of order prime to the characteristic exponent `p` of `κ(y₀)` comes from `π₁(X̄₀)`)
needs X.2.1 (Grothendieck's existence theorem), the limit argument X.3.7, purity in dimension `2`
and Abhyankar's lemma X.3.6; it is recorded as `TameSpecializationStatement`. X.3.9 follows by
group theory (`Specialization`): the specialization homomorphism induces an isomorphism of the
largest prime-to-`p` quotients (`exists_primeToQuotientEquiv_of_tameSpecialization`), and is an
isomorphism in characteristic zero (`exists_bijective_of_tameSpecialization`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- X.3.8 (statement only). In the situation of X.2.4 with `f : X ⟶ Y` proper and smooth with
geometrically connected fibres, the specialization homomorphism `π₁(X̄₁, ā₁) → π₁(X̄₀, ā₀)` is
continuous and surjective, and every continuous homomorphism of `π₁(X̄₁, ā₁)` into a finite group
of order prime to the characteristic exponent `p` of `κ(y₀)` (that of `Ω₀`) factors through it.
As for X.2.4, the specialization homomorphism being defined only up to inner automorphism, we
state that a homomorphism with these properties exists. -/
def TameSpecializationStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] [Smooth f] [GeometricallyConnected f]
    [IsLocallyNoetherian Y] (Ω₀ Ω₁ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁]
    [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Y) (b₁ : Spec (.of Ω₁) ⟶ Y),
    b₁ (IsLocalRing.closedPoint Ω₁) ⤳ b₀ (IsLocalRing.closedPoint Ω₀) →
    ∀ (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁),
      ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
        Continuous sp ∧ Function.Surjective sp ∧ FactorsPrimeTo sp (ringExpChar Ω₀)

variable (h : TameSpecializationStatement.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
  [Smooth f] [GeometricallyConnected f] [IsLocallyNoetherian Y] (Ω₀ Ω₁ : Type u) [Field Ω₀]
  [IsAlgClosed Ω₀] [Field Ω₁] [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Y) (b₁ : Spec (.of Ω₁) ⟶ Y)
  (hb : b₁ (IsLocalRing.closedPoint Ω₁) ⤳ b₀ (IsLocalRing.closedPoint Ω₀))
  (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁)
include h hb

/-- X.3.9 (from X.3.8, in the existence form of `TameSpecializationStatement`). The
specialization homomorphism `sp : π₁(X̄₁) → π₁(X̄₀)` has kernel contained in the intersection of
the kernels of the continuous homomorphisms of `π₁(X̄₁)` to finite groups of order prime to `p`,
and induces an isomorphism `π₁(X̄₁)^(p) ≅ π₁(X̄₀)^(p)` of the largest prime-to-`p` quotients. -/
theorem exists_primeToQuotientEquiv_of_tameSpecialization :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Surjective sp ∧
        sp.ker ≤ primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₁ a₁) ∧
        ∃ e : ExposeV.etaleFundamentalGroup Ω₁ a₁ ⧸
            primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₁ a₁) ≃*
          ExposeV.etaleFundamentalGroup Ω₀ a₀ ⧸
            primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₀ a₀),
          ∀ x, e (QuotientGroup.mk x) = QuotientGroup.mk (sp x) := by
  obtain ⟨sp, hc, hs, hfac⟩ := h f Ω₀ Ω₁ b₀ b₁ hb a₀ a₁
  exact ⟨sp, hc, hs, ker_le_primeToKernel hc hs hfac, primeToQuotientEquiv hc hs hfac,
    primeToQuotientEquiv_mk hc hs hfac⟩

/-- X.3.9 (from X.3.8, in the existence form), characteristic zero: if `κ(y₀)` has
characteristic `0`, the specialization homomorphism `π₁(X̄₁) → π₁(X̄₀)` is an isomorphism. -/
theorem exists_bijective_of_tameSpecialization [CharZero Ω₀] :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Bijective sp := by
  obtain ⟨sp, hc, hs, hfac⟩ := h f Ω₀ Ω₁ b₀ b₁ hb a₀ a₁
  rw [ringExpChar.eq_one Ω₀] at hfac
  exact ⟨sp, hc, bijective_of_forall_factor hc hs hfac⟩

end SGA.SGA1.ExposeX
