/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.StrictLocalization
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeXIII.KummerCoverings
import SGA.SGA1.ExposeXIII.NormalCrossings

/-!
# SGA 1, Exposé XIII, 5.5: the relative Abhyankar lemma (statement)

Let `p : X ⟶ S` be a morphism and `D = ∑ div fᵢ` a divisor with strictly normal crossings
relative to `S` (XIII.5.4: `IsStrictNormalCrossings p f`), `Y = Supp D` and `U = X - Y`. Let `x̄`
be a geometric point of `X` over a point `x` of `Y`, `X₁` the strict localization of `X` at `x̄`,
`U₁ = U ×_X X₁` and `V₁` an étale covering of `U₁` which is tamely ramified on the geometric
fibres of `X₁` over the maximal points of `S`. XIII.5.5 says that after adjoining roots
`Tᵢ^{nᵢ} = fᵢ` (`i ∈ I(x)`, the indices with `fᵢ(x) = 0`, `nᵢ` prime to the characteristic of
`κ(x)`), the inverse image of `V₁` extends to an étale covering of
`X'₁ = X₁[Tᵢ]_{i ∈ I(x)}/(Tᵢ^{nᵢ} - fᵢ)`, uniquely up to unique isomorphism.

`RelativeAbhyankarStatement` records the existence part; the uniqueness (which SGA deduces from
`prof_et_{Y'₁}(X'₁) ≥ 2`, SGA 4 XVI 3.2 or SGA 2 XIV 1.19) is not part of the statement. SGA's
proof reduces to the maximal points of `Y'₁` by SGA 2 XIV 1.20 and applies X.3.6 there; the
`nᵢ` are prime to `p` by a descent argument along the radicial `X'₁ ⟶ X₁` over the closed point.
It is the input of XIII.2.3 a) (`TameRamificationAtMaximalPointsStatement`) and XIII.2.4 1)
(`TameBaseChangeStatement`), hence of the third part of XIII.4.4.

## Notation in the statement

For a geometric point `ξ : Spec Ω ⟶ X`, `ξ.strictLocalization` is `𝒪^{sh}_{X,x̄}` and
`ξ.fromSpecStrictLocalization : X₁ = Spec 𝒪^{sh}_{X,x̄} ⟶ X` the canonical morphism
(`SGA.Foundations.StrictLocalization`). `relativeAbhyankarRing ξ f I n` is
`𝒪^{sh}_{X,x̄}[Tᵢ]_{i ∈ I}/(Tᵢ^{nᵢ} - fᵢ)`, by definition the Kummer algebra
`KummerAlgebra n (fun i : I ↦ fᵢ)` of Appendix I (`SGA.SGA1.ExposeXIII.KummerCoverings`) over
`𝒪^{sh}_{X,x̄}`, so that its API (`KummerAlgebra.T_pow`, `KummerAlgebra.lift`, the étaleness of
XIII.5.1) applies to it.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXIII

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The image in the strict localization `𝒪^{sh}_{X,x̄}` of a global function on `X`. -/
noncomputable def toStrictLocalizationTop (ξ : Spec (.of Ω) ⟶ X) (g : Γ(X, ⊤)) :
    ξ.strictLocalization :=
  (Scheme.ΓSpecIso ξ.strictLocalization).hom (ξ.fromSpecStrictLocalization.appTop g)

/-- The ring `𝒪^{sh}_{X,x̄}[Tᵢ]_{i ∈ I}/(Tᵢ^{nᵢ} - fᵢ)` of XIII.5.5: the Kummer algebra
`KummerAlgebra n f` of Appendix I over `𝒪^{sh}_{X,x̄}`, for the images of the `fᵢ`, `i ∈ I`. -/
abbrev relativeAbhyankarRing (ξ : Spec (.of Ω) ⟶ X) {ι : Type} (f : ι → Γ(X, ⊤))
    (I : Set ι) (n : I → ℕ) : Type u :=
  KummerAlgebra n fun i : I ↦ toStrictLocalizationTop ξ (f i)

/-- XIII.5.5, the relative Abhyankar lemma, existence part (statement only). Let `p : X ⟶ S` be a
morphism of schemes and `f : ι → Γ(X, ⊤)` (finite `ι`) a family defining a divisor
`D = ∑ div fᵢ` with strictly normal crossings relative to `S` (XIII.5.4), `Y = Supp D`,
`U = X - Y = ⋂ D(fᵢ)`. Let `ξ : Spec Ω ⟶ X` be a geometric point (`Ω` separably closed) over a
point `x` of `Y`, `X₁ = Spec 𝒪^{sh}_{X,x̄}`, `U₁` the inverse image of `U` and `V₁` an étale
covering of `U₁` such that, at every geometric point of `S` over a maximal point of `S`, `V₁`
is tamely ramified along `Y₁` (XIII.2.1.1, `IsTamelyRamifiedSheafAt` for `X₁ ⟶ S`). Then there
are integers `nᵢ`, `i ∈ I(x) = {i | fᵢ(x) = 0}`, not divisible by the characteristic of `κ(x)`
(so nonzero), such that, with `X'₁ = Spec 𝒪^{sh}_{X,x̄}[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` and `U'₁` the
inverse image of `U₁`, the inverse image of `V₁` on `U'₁` is the restriction of an étale covering
of `X'₁`. (SGA also asserts the uniqueness of the extension, which is not recorded here.) -/
def RelativeAbhyankarStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (p : X ⟶ S) {ι : Type} [Finite ι] (f : ι → Γ(X, ⊤)),
    IsStrictNormalCrossings p f →
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X),
      ξ.imagePoint ∈ (⋃ i, X.zeroLocus {f i}) →
      ∀ V₁ : ExposeV.FEt ((ξ.fromSpecStrictLocalization ⁻¹ᵁ ⨅ i, X.basicOpen (f i) :
          (Spec ξ.strictLocalization).Opens) : Scheme.{u}),
        (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (s : Spec (.of Ω') ⟶ S),
          IsMaximalPointOf Set.univ (s (closedPoint Ω')) →
          haveI : Etale V₁.hom := V₁.prop.2
          IsTamelyRamifiedSheafAt (ξ.fromSpecStrictLocalization ≫ p)
            (ξ.fromSpecStrictLocalization ⁻¹' ⋃ i, X.zeroLocus {f i})
            (ξ.fromSpecStrictLocalization ⁻¹ᵁ ⨅ i, X.basicOpen (f i))
            ((Scheme.etaleYoneda _).obj (Scheme.Etale.mk V₁.hom)) Ω' s) →
        ∃ n : {i | ξ.imagePoint ∈ X.zeroLocus {f i}} → ℕ,
          (∀ i, ¬ ringChar (X.residueField ξ.imagePoint) ∣ n i) ∧
          ∃ E : ExposeV.FEt (Spec (.of (relativeAbhyankarRing ξ f _ n))),
            Nonempty ((ExposeV.FEt.pullback ((Spec.map (CommRingCat.ofHom (algebraMap
                ξ.strictLocalization (relativeAbhyankarRing ξ f _ n)))) ⁻¹ᵁ
                  (ξ.fromSpecStrictLocalization ⁻¹ᵁ ⨅ i, X.basicOpen (f i))).ι).obj E ≅
              (ExposeV.FEt.pullback (Spec.map (CommRingCat.ofHom (algebraMap ξ.strictLocalization
                (relativeAbhyankarRing ξ f _ n))) ∣_
                  (ξ.fromSpecStrictLocalization ⁻¹ᵁ ⨅ i, X.basicOpen (f i)))).obj V₁)

end SGA.SGA1.ExposeXIII
