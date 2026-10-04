/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.SemistableReductionSmooth

/-!
# Semistable reduction of curves: the conclusion for one curve, and the good reduction case

`SemistableReductionStatement` (stated in `SGA.SGA1.ExposeXIII.AbhyankarAffineLine`, the input of
Raynaud's case B of XIII.2.13) quantifies over complete discrete valuation rings `R` and curves
`X` over `K = Frac R`. Here:

* `SGA.SGA1.ExposeXIII.HasSemistableReduction R K X f`: the conclusion of that statement for one
  curve `f : X ⟶ Spec K` (a finite extension `R ⊂ R'` of discrete valuation rings, a proper flat
  `R'`-scheme with generic fibre `X ⊗_K K'` over `K'` and semistable special fibre), copied
  verbatim; `SGA.SGA1.ExposeXIII.semistableReductionStatement_iff` checks (by `Iff.rfl`) that the
  statement is this conclusion for every `R` and `X` as in the statement;
* `SGA.SGA1.ExposeXIII.hasSemistableReduction_of_smooth_model`: the good reduction case. If `X`
  is the generic fibre of a proper scheme smooth of relative dimension `1` over a discrete valuation
  ring `R` with algebraically closed residue field, then `X` has semistable reduction, with
  `R' = R` (the special fibre is smooth, hence semistable by
  `SGA.SGA1.ExposeXIII.isSemistableCurve_of_smooth`). This case needs neither completeness of `R`
  nor any hypothesis on `X ⟶ Spec K`.

The general case (curves with bad reduction) is not proved; the plan (Artin–Winters after Stacks,
chapters 53–55) is in `notes/log/2026-10-04-semistable-route.md`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXIII

/-- The conclusion of the semistable reduction theorem (`SemistableReductionStatement`) for one
curve `f : X ⟶ Spec K` over the fraction field `K` of a discrete valuation ring `R`: there are a
finite extension `R ⊂ R'` of discrete valuation rings, with fraction field `K'` finite over `K`, and
a proper flat `R'`-scheme `𝒳` whose generic fibre is `X ⊗_K K'` (over `K'`) and whose special fibre
is a semistable curve (`IsSemistableCurve`). The body is copied verbatim from
`SemistableReductionStatement` (see `semistableReductionStatement_iff`). -/
def HasSemistableReduction (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
    (_ : Algebra R R') (_ : Module.Finite R R') (_ : FaithfulSMul R R')
    (K' : Type u) (_ : Field K') (_ : Algebra R' K') (_ : IsFractionRing R' K')
    (_ : Algebra K K') (_ : FiniteDimensional K K') (_ : Algebra R K')
    (_ : IsScalarTower R K K') (_ : IsScalarTower R R' K')
    (𝒳 : Scheme.{u}) (g : 𝒳 ⟶ Spec (.of R')) (_ : IsProper g) (_ : Flat g),
    (∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) ≅
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _) ∧
    IsSemistableCurve (IsLocalRing.ResidueField R')
      (pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R'))))

/-- `SemistableReductionStatement` says that every smooth proper geometrically connected curve over
the fraction field of a complete discrete valuation ring with algebraically closed residue field
has semistable reduction (`HasSemistableReduction`). -/
theorem semistableReductionStatement_iff : SemistableReductionStatement.{u} ↔
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
      [IsFractionRing R K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
      [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f],
      HasSemistableReduction R K X f :=
  Iff.rfl

/-- A `K`-scheme `X` is its own base change along `Spec K ⟶ Spec K` (the map induced by
`algebraMap K K = id`). -/
private noncomputable def pullbackSpecIdIso {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) :
    X ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact
    { hom := pullback.lift (𝟙 X) f (by rw [h1]; simp)
      inv := pullback.fst _ _
      hom_inv_id := pullback.lift_fst _ _ _
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, h1,
            Category.comp_id] }

private lemma pullbackSpecIdIso_hom_snd {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : (pullbackSpecIdIso f).hom ≫ pullback.snd _ _ = f :=
  pullback.lift_snd _ _ _

-- Instance search for `IsStableUnderBaseChangeAlong` from the local
-- `IsStableUnderBaseChange (@SmoothOfRelativeDimension 1)` fails under the default transparency
-- setting (as in `SGA1/ExposeXIII/NormalCrossings.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- The good reduction case of the semistable reduction theorem: let `R` be a discrete valuation
ring with algebraically closed residue field and fraction field `K`, and `g : 𝒳 ⟶ Spec R` proper
and smooth of relative dimension `1`. A `K`-scheme `f : X ⟶ Spec K` isomorphic over `K` to the
generic fibre of `g` has semistable reduction, with `R' = R` and model `𝒳`. -/
theorem hasSemistableReduction_of_smooth_model (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (𝒳 : Scheme.{u}) (g : 𝒳 ⟶ Spec (.of R)) [IsProper g]
    [SmoothOfRelativeDimension 1 g]
    (e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅ X)
    (he : e.hom ≫ f = pullback.snd _ _) :
    HasSemistableReduction R K X f := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have hsm : SmoothOfRelativeDimension 1
      (pullback.snd g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  refine ⟨R, inferInstance, inferInstance, inferInstance, Algebra.id R, inferInstance,
    inferInstance, K, inferInstance, inferInstance, inferInstance, Algebra.id K, inferInstance,
    inferInstance, inferInstance, inferInstance, 𝒳, g, inferInstance, inferInstance,
    ⟨e ≪≫ pullbackSpecIdIso f, ?_⟩, isSemistableCurve_of_smooth
      (pullback.snd g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))⟩
  rw [Iso.trans_hom, Category.assoc, pullbackSpecIdIso_hom_snd, he]

end SGA.SGA1.ExposeXIII
