/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicityHenselian
import SGA.SGA1.ExposeXI.Geometry
import SGA.SGA1.ExposeXIII.LocalAcyclicityFieldStalks

/-!
# Morphisms to the spectrum of a field are locally `1`-aspherical

Let `f : X ⟶ Spec k`, `x̄` a geometric point of `X` and `t̄ : Spec K ⟶ S̃` an algebraic geometric
point of the strict localization `S̃` of `Spec k` at `f(x̄)`. Then `S̃` is the spectrum of a
separably closed field `L` and `K` is algebraic, hence purely inseparable, over `L`, so the Milnor
fibre `X̃ ×_{S̃} t̄ = X̃ ⊗_L K` is integral over the strictly local scheme
`X̃ = Spec 𝒪^{sh}_{X,x̄}`. It is connected (`SGA.SGA1.ExposeXIII.isLocallyZeroAcyclic_of_field`),
hence the spectrum of a strictly henselian local ring, and simply connected
(`AlgebraicGeometry.isIso_of_isFinite_of_etale_of_isIntegralHom`). So:

* `SGA.SGA1.ExposeXIII.isOneAspherical_of_isIntegralHom`: a connected scheme integral over a
  strictly henselian local ring is `1`-aspherical for every set of primes;
* `SGA.SGA1.ExposeXIII.isLocallyOneAspherical_of_field`: every morphism to the spectrum of a field
  is locally `1`-aspherical (SGA 4 XV 1.11, Milnor-fibre form) for every set of primes `L`.

This is the degree-`1` analogue of `isLocallyZeroAcyclic_of_field`. It is *not* the universal
version: universal local `1`-asphericity of smooth morphisms is SGA 4 XV 2.1
(`SGA.SGA1.ExposeXIII.LocalAsphericitySmoothStatement`), and over a field it needs every base change
`S' ⟶ Spec k`, not only `Spec k` itself.

## References

* [SGA 4, Exposé XV, 1.3, 1.11][sga4]
* [EGA IV, 18.8][ega4]
-/

universe u

open CategoryTheory Limits IsLocalRing AlgebraicGeometry

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

/-- An algebraic geometric point of the spectrum of a local ring which is a field (its residue map
is bijective) is an integral morphism. -/
lemma isIntegralHom_of_isAlgebraicPoint {R : CommRingCat.{u}} [IsLocalRing R]
    (hR : Function.Bijective (residue R)) {K : Type u} [Field K] (t : Spec (.of K) ⟶ Spec R)
    (ht : t.IsAlgebraicPoint) : IsIntegralHom t := by
  set x : Spec R := t.imagePoint
  -- the image point is the maximal ideal
  have hm : maximalIdeal R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    exact hR.1 (((residue_eq_zero_iff r).mpr hr).trans (map_zero _).symm)
  have hx : x.asIdeal.IsMaximal := by
    have hle : x.asIdeal ≤ maximalIdeal R := le_maximalIdeal x.2.ne_top
    rw [le_antisymm hle (hm ▸ bot_le)]
    infer_instance
  have h₁ : IsIntegralHom (Spec.map t.residueFieldEmbedding) := IsIntegralHom.SpecMap_iff.mpr ht
  have h₃ : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField))) := by
    rw [IsIntegralHom.SpecMap_iff]
    refine RingHom.isIntegral_of_surjective _ fun y ↦ ?_
    obtain ⟨z, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField x.asIdeal).2 y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨r, (IsScalarTower.algebraMap_apply R (R ⧸ x.asIdeal) _ r).symm⟩
  rw [← t.fromSpecResidueField_eq, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  infer_instance

/-- A connected scheme `M` integral over a strictly henselian local ring is `1`-aspherical for
every set of primes `L`: it is simply connected
(`AlgebraicGeometry.isIso_of_isFinite_of_etale_of_isIntegralHom`). -/
theorem isOneAspherical_of_isIntegralHom (L : Set ℕ) {A : CommRingCat.{u}} [IsStrictlyHenselian A]
    {M : Scheme.{u}} (p : M ⟶ Spec A) [IsIntegralHom p] [ConnectedSpace M] :
    IsOneAspherical L M := by
  refine ⟨inferInstance, fun Ω _ _ z ↦ ?_⟩
  have hsc : ExposeXI.IsSimplyConnected M :=
    ⟨inferInstance, fun Y q _ _ hY ↦ isIso_of_isFinite_of_etale_of_isIntegralHom p q⟩
  have : Subsingleton (FundamentalGroup z) :=
    (ExposeXI.isSimplyConnected_iff_subsingleton Ω z).mp hsc
  refine ⟨fun a b ↦ ?_⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  exact congrArg _ (Subsingleton.elim _ _)

variable {k : Type u} [Field k]

/-- Over a field, every morphism is locally `1`-aspherical for every set of primes `L` (SGA 4 XV
1.11 in degree `1`, Milnor-fibre form; not *universally*, which is SGA 4 XV 2.1 for smooth
morphisms): the Milnor fibres are connected and integral over the strictly local scheme
`Spec 𝒪^{sh}_{X,x̄}`, since the strict localization of `Spec k` is the spectrum of a separably
closed field over which the algebraic geometric points are integral. -/
theorem isLocallyOneAspherical_of_field (L : Set ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsLocallyOneAspherical L f := by
  intro Ω _ _ x K _ _ t ht
  have : ConnectedSpace ↥(pullback (f.strictLocalizationMap x) t : Scheme.{u}) :=
    isLocallyZeroAcyclic_of_field f Ω x K t ht
  have hbij := (x ≫ f).bijective_residue_strictLocalization
    (Scheme.isField_stalk_spec k (x ≫ f).imagePoint)
  have : IsIntegralHom t := isIntegralHom_of_isAlgebraicPoint hbij t ht
  exact isOneAspherical_of_isIntegralHom L (pullback.fst (f.strictLocalizationMap x) t)

end SGA.SGA1.ExposeXIII
