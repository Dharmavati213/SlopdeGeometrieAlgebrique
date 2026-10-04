/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import SGA.Foundations.HenselizationNoetherian
import SGA.Foundations.StrictLocalizationFunctorial

/-!
# Flatness of the morphisms of strict localizations

Let `R` be a ring with a `K`-point and `R^sh = IsLocalRing.StrictHenselization R K`. An
`R^sh`-algebra `B` which is flat over `R` is flat over `R^sh`
(`IsLocalRing.StrictHenselization.flat_of_flat_restrictScalars`): `B` is flat over the local ring
of every étale neighbourhood, which is unramified over `R` (Iversen I.2.7,
`Algebra.FormallyUnramified.flat_of_restrictScalars`), hence over their colimit `R^sh`
(`IsLocalRing.StrictHenselization.flat_of_forall_flat`). Consequently, for a flat ring map
`R → R'`, every ring map `R^sh → R'^sh` over it is flat
(`IsLocalRing.StrictHenselization.flat_of_comp_algebraMap`; EGA IV 18.8 for the strict
henselizations of a flat local homomorphism).

For schemes: if `f : X ⟶ S` is flat, the morphism of strict localizations
`Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,f(x̄)}` (`AlgebraicGeometry.Scheme.Hom.strictLocalizationMap`)
is flat (`AlgebraicGeometry.Scheme.Hom.flat_strictLocalizationMap`).

## References

* [EGA IV, 18.8][ega4]
* [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*, I.2.7][iversen]
* [Stacks Project, Section 04GN (henselization and strict henselization)][stacks]
-/

universe u

open CategoryTheory IsLocalRing

noncomputable section

-- The carrier of `Spec R` is only defeq to `PrimeSpectrum R` beyond instance transparency (as in
-- `SGA.Foundations.StrictLocalizationFunctorial`).
set_option backward.isDefEq.respectTransparency false

namespace IsLocalRing.StrictHenselization

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

/-- An algebra `B` over the strict henselization `R^sh` which is flat over `R` is flat over `R^sh`:
it is flat over the local ring of every étale neighbourhood, which is unramified over `R`
(Iversen I.2.7), hence over their colimit. -/
theorem flat_of_flat_restrictScalars (B : Type*) [CommRing B]
    [Algebra (StrictHenselization R K) B] [Algebra R B]
    [IsScalarTower R (StrictHenselization R K) B] [Module.Flat R B] :
    Module.Flat (StrictHenselization R K) B :=
  flat_of_forall_flat B fun N ↦ by
    let : Algebra N.Stalk B :=
      ((algebraMap (StrictHenselization R K) B).comp (of N : N.Stalk →+* _)).toAlgebra
    have : IsScalarTower R N.Stalk B := .of_algebraMap_eq fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.FormallyUnramified.flat_of_restrictScalars R N.Stalk B

/-- **Strict henselization preserves flatness**: if `R → R'` is flat,
every ring map `R^sh → R'^sh` of strict henselizations over `R → R'` is flat (for any `K`-point of
`R` and `K'`-point of `R'`). -/
theorem flat_of_comp_algebraMap {R' : Type u} [CommRing R'] [Algebra R R'] {K' : Type u}
    [Field K'] [Algebra R' K'] (hf : (algebraMap R R').Flat)
    (φ : StrictHenselization R K →+* StrictHenselization R' K')
    (hφ : φ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) : φ.Flat := by
  let : Algebra R (StrictHenselization R' K') :=
    ((algebraMap R' (StrictHenselization R' K')).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' (StrictHenselization R' K') := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  have : Module.Flat R (StrictHenselization R' K') := .trans R R' _
  let : Algebra (StrictHenselization R K) (StrictHenselization R' K') := φ.toAlgebra
  have : IsScalarTower R (StrictHenselization R K) (StrictHenselization R' K') :=
    .of_algebraMap_eq fun r ↦ (DFunLike.congr_fun hφ r).symm
  exact flat_of_flat_restrictScalars (StrictHenselization R' K')

end IsLocalRing.StrictHenselization

namespace AlgebraicGeometry.Scheme.Hom

/-- A local ring map `c : 𝒪_{S,s} → 𝒪_{X,x}` over a flat morphism `f : X ⟶ S` (i.e. `Spec c` is
`f` on the local schemes) is flat: it is the stalk map of `f` at `x`. -/
lemma flat_of_SpecMap_fromSpecStalk {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] {x : X} {s : S}
    (c : S.presheaf.stalk s ⟶ X.presheaf.stalk x) [IsLocalHom c.hom]
    (hc : Spec.map c ≫ S.fromSpecStalk s = X.fromSpecStalk x ≫ f) : c.hom.Flat := by
  have hs : f x = s := by
    have := congrArg (fun g ↦ g (closedPoint (X.presheaf.stalk x))) hc
    dsimp only at this
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint, fromSpecStalk_closedPoint,
      fromSpecStalk_closedPoint] at this
    exact this.symm
  subst hs
  obtain rfl : c = f.stalkMap x :=
    SpecMap_comp_fromSpecStalk_injective (hc.trans (SpecMap_stalkMap_fromSpecStalk f).symm)
  exact Flat.stalkMap f x

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ S)

attribute [local instance] residueFieldAlgebra stalkAlgebra isScalarTower_stalkAlgebra

/-- For `f` flat, the morphism of strict localizations
`Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,f(x̄)}` is flat (EGA IV 18.8): it is `Spec` of
a map of strict henselizations over the flat stalk map `𝒪_{S,f(x)} → 𝒪_{X,x}`. -/
instance flat_strictLocalizationMap [Flat f] : Flat (f.strictLocalizationMap ξ) := by
  obtain ⟨c, hcl, hcf, -⟩ := ξ.exists_stalkMap_imagePoint f
  have hc : c.hom.Flat := flat_of_SpecMap_fromSpecStalk f c hcf
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (f.strictLocalizationMap ξ)
  -- `φ` lies over `c`
  have h₁ : (ξ ≫ f).toStrictLocalization ≫ φ = c ≫ ξ.toStrictLocalization := by
    apply Scheme.SpecMap_comp_fromSpecStalk_injective
    have := strictLocalizationMap_fromSpecStrictLocalization ξ f
    rw [← hφ, fromSpecStrictLocalization, fromSpecStrictLocalization, ← Category.assoc,
      ← Spec.map_comp, Category.assoc, ← hcf, ← Category.assoc, ← Spec.map_comp] at this
    rw [Spec.map_comp, Spec.map_comp, Category.assoc] at this ⊢
    exact this
  rw [← hφ, Flat.SpecMap_iff]
  algebraize [c.hom]
  exact StrictHenselization.flat_of_comp_algebraMap hc φ.hom (congrArg CommRingCat.Hom.hom h₁)

end AlgebraicGeometry.Scheme.Hom
