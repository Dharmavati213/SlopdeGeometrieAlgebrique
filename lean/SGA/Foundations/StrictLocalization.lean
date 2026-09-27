/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.StrictHenselization
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The strict localization of a scheme at a geometric point

Let `X` be a scheme and `x̄ : Spec Ω ⟶ X` a geometric point, with image `x ∈ X` and residue field
embedding `κ(x) → Ω` (`AlgebraicGeometry.Scheme.SpecToEquivOfField`). The *strict localization*
of `X` at `x̄` (EGA IV 18.8; SGA 4 VIII 4; Stacks 04HX) is the strict henselization of the local
ring `𝒪_{X,x}` with respect to `Ω`, i.e. the colimit of the local rings of the pointed étale
neighbourhoods of `Spec Ω → Spec 𝒪_{X,x}` (`IsLocalRing.StrictHenselization`). When `Ω` is
separably closed it is strictly henselian, with residue field the separable closure of `κ(x)` in
`Ω`. It comes with morphisms `Spec Ω ⟶ Spec 𝒪^{sh}_{X,x̄} ⟶ X` whose composite is `x̄`.

## Main definitions

For `ξ : Spec (.of Ω) ⟶ X`:
* `ξ.imagePoint`, `ξ.residueFieldEmbedding`: the image `x` and the embedding `κ(x) → Ω`;
* `ξ.stalkAlgebra`, `ξ.residueFieldAlgebra`: the induced algebra structures on `Ω` (not global
  instances; activate them with `attribute [local instance]` to use the ring-level API);
* `ξ.strictLocalization`: `𝒪^{sh}_{X,x̄}`, a henselian local ring, strictly henselian if `Ω` is
  separably closed, faithfully flat over `𝒪_{X,x}`;
* `ξ.strictLocalizationResidueFieldEquiv`: its residue field is the separable closure of `κ(x)`
  in `Ω`;
* `ξ.fromSpecStrictLocalization : Spec 𝒪^{sh}_{X,x̄} ⟶ X` and
  `ξ.toSpecStrictLocalization : Spec Ω ⟶ Spec 𝒪^{sh}_{X,x̄}`, with composite `ξ`
  (`toSpecStrictLocalization_fromSpecStrictLocalization`).

Over `𝒪^{sh}_{X,x̄}` with `Ω` separably closed, every finite étale algebra is split
(`IsStrictlyHenselian.exists_algEquiv_pi`), and the points of an étale `𝒪_{X,x}`-algebra with
values in `Ω` are its points with values in `𝒪^{sh}_{X,x̄}`
(`IsLocalRing.StrictHenselization.algHomEquivPoint`).

We do not compare `𝒪^{sh}_{X,x̄}` with the stalk at `x̄` of the structure sheaf of the small
étale site (`AlgebraicGeometry.Scheme.pointSmallEtale`): this needs that étale algebras over
`𝒪_{X,x}` spread out to étale neighbourhoods of `x` (EGA IV 8, 17.7.8).
-/

universe u

open CategoryTheory IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The point of `X` under a geometric point `x̄ : Spec Ω ⟶ X`. -/
def imagePoint : X := (SpecToEquivOfField Ω X ξ).1

/-- The embedding `κ(x) → Ω` of the residue field at the image of a geometric point. -/
def residueFieldEmbedding : X.residueField ξ.imagePoint ⟶ CommRingCat.of Ω :=
  (SpecToEquivOfField Ω X ξ).2

lemma fromSpecResidueField_eq :
    Spec.map ξ.residueFieldEmbedding ≫ X.fromSpecResidueField ξ.imagePoint = ξ :=
  (SpecToEquivOfField Ω X).symm_apply_apply ξ

/-- The residue field `κ(x)` of the stalk at the image of a geometric point acts on `Ω`. -/
@[reducible]
def residueFieldAlgebra : Algebra (ResidueField (X.presheaf.stalk ξ.imagePoint)) Ω :=
  ξ.residueFieldEmbedding.hom.toAlgebra

/-- The stalk `𝒪_{X,x}` at the image of a geometric point acts on `Ω`. -/
@[reducible]
def stalkAlgebra : Algebra (X.presheaf.stalk ξ.imagePoint) Ω :=
  (ξ.residueFieldEmbedding.hom.comp (IsLocalRing.residue (X.presheaf.stalk ξ.imagePoint))).toAlgebra

attribute [local instance] residueFieldAlgebra stalkAlgebra

lemma isScalarTower_stalkAlgebra :
    IsScalarTower (X.presheaf.stalk ξ.imagePoint)
      (ResidueField (X.presheaf.stalk ξ.imagePoint)) Ω :=
  .of_algebraMap_eq' rfl

attribute [local instance] isScalarTower_stalkAlgebra

/-- The strict localization `𝒪^{sh}_{X,x̄}` of a scheme at a geometric point (EGA IV 18.8,
Stacks 04HX): the strict henselization of `𝒪_{X,x}` with respect to `Ω`. -/
def strictLocalization : CommRingCat.{u} :=
  .of (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω)

instance : IsLocalRing ξ.strictLocalization :=
  inferInstanceAs (IsLocalRing (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω))

instance : HenselianLocalRing ξ.strictLocalization :=
  inferInstanceAs (HenselianLocalRing (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω))

/-- The strict localization at a geometric point with values in a separably closed field is
strictly henselian. -/
instance [IsSepClosed Ω] : IsStrictlyHenselian ξ.strictLocalization :=
  inferInstanceAs (IsStrictlyHenselian (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω))

instance : Algebra (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization :=
  inferInstanceAs (Algebra _ (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω))

instance : Module.FaithfullyFlat (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization :=
  haveI := isLocalHom_algebraMap_of_isScalarTower (R := X.presheaf.stalk ξ.imagePoint) (K := Ω)
  inferInstanceAs (Module.FaithfullyFlat _ (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω))

instance : IsLocalHom (algebraMap (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization) :=
  haveI := isLocalHom_algebraMap_of_isScalarTower (R := X.presheaf.stalk ξ.imagePoint) (K := Ω)
  inferInstanceAs (IsLocalHom (algebraMap (X.presheaf.stalk ξ.imagePoint)
    (StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω)))

/-- The residue field of the strict localization is the separable closure of `κ(x)` in `Ω`. -/
def strictLocalizationResidueFieldEquiv :
    ResidueField ξ.strictLocalization ≃+*
      separableClosure (ResidueField (X.presheaf.stalk ξ.imagePoint)) Ω :=
  StrictHenselization.residueFieldEquivSeparableClosure _ _

/-- The canonical map `𝒪_{X,x} → 𝒪^{sh}_{X,x̄}`. -/
def toStrictLocalization : X.presheaf.stalk ξ.imagePoint ⟶ ξ.strictLocalization :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization)

/-- The point `𝒪^{sh}_{X,x̄} → Ω` of the strict localization. -/
def strictLocalizationToField : ξ.strictLocalization ⟶ CommRingCat.of Ω :=
  CommRingCat.ofHom
    (StrictHenselization.pointHom : StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω →ₐ[_] Ω)

/-- The canonical morphism `Spec 𝒪^{sh}_{X,x̄} ⟶ X`. -/
def fromSpecStrictLocalization : Spec ξ.strictLocalization ⟶ X :=
  Spec.map ξ.toStrictLocalization ≫ X.fromSpecStalk ξ.imagePoint

instance : IsLocalHom ξ.toStrictLocalization.hom :=
  inferInstanceAs (IsLocalHom (algebraMap (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization))

-- The carrier of `Spec R` is only defeq to `PrimeSpectrum R` beyond instance transparency, as in
-- mathlib's `Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk`.
set_option backward.isDefEq.respectTransparency false in
/-- The closed point of `Spec 𝒪^{sh}_{X,x̄}` lies over the image of `x̄`. -/
lemma fromSpecStrictLocalization_closedPoint :
    ξ.fromSpecStrictLocalization (closedPoint ξ.strictLocalization) = ξ.imagePoint := by
  rw [fromSpecStrictLocalization, Scheme.Hom.comp_apply, Spec_closedPoint,
    fromSpecStalk_closedPoint]

/-- The geometric point `x̄` lifts to `Spec 𝒪^{sh}_{X,x̄}`. -/
def toSpecStrictLocalization : Spec (.of Ω) ⟶ Spec ξ.strictLocalization :=
  Spec.map ξ.strictLocalizationToField

lemma toStrictLocalization_strictLocalizationToField :
    ξ.toStrictLocalization ≫ ξ.strictLocalizationToField =
      X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
  ext s
  exact (StrictHenselization.pointHom :
    StrictHenselization (X.presheaf.stalk ξ.imagePoint) Ω →ₐ[_] Ω).commutes s

@[reassoc (attr := simp)]
theorem toSpecStrictLocalization_fromSpecStrictLocalization :
    ξ.toSpecStrictLocalization ≫ ξ.fromSpecStrictLocalization = ξ := by
  rw [toSpecStrictLocalization, fromSpecStrictLocalization, ← Category.assoc, ← Spec.map_comp,
    toStrictLocalization_strictLocalizationToField, Spec.map_comp, Category.assoc]
  exact ξ.fromSpecResidueField_eq

end AlgebraicGeometry.Scheme.Hom
