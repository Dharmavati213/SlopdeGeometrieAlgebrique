/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.SpecializationGeometric
import SGA.SGA1.ExposeXIII.ProperHomotopySequence

/-!
# SGA 1, Exposé X, 2.4: surjectivity of the specialization homomorphism

Let `f : X ⟶ Y` be proper and separable with geometrically connected fibres, `Y` locally
noetherian, `y₀` a specialization of `y₁`, and `b₀`, `b₁` geometric points of `Y` at `y₀`, `y₁`
with algebraically closed values. As in SGA we replace `Y` by `Y' = Spec 𝒪̂_{Y,y₀}`: `b₀` lifts to
`Y'` at its closed point, `b₁` lifts to `Y'` after an algebraically closed extension of its field of
values (X.1.8 shows that this does not change the fundamental group of the geometric fibre), and
over `Y'` the specialization homomorphism is surjective (X.2.3,
`exists_continuous_surjective_specialization_of_completeLocal`). The only input which is not
proved in general is the essential surjectivity in IX.1.10 (Grothendieck's existence theorem),
used for the injectivity of `π₁(X̄₀) → π₁(X')` in X.2.2:
`specializationSurjectiveStatement_of_etaleCoveringsOfClosedFibreStatement`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory IsLocalRing
open scoped TensorProduct

namespace SGA.SGA1.ExposeX

section FundamentalGroupIso

/-- If base change of étale coverings along `g : X₁ ⟶ X₂` is an equivalence (for instance `g` an
isomorphism, or X.1.8), the fundamental groups of the connected schemes `X₁` and `X₂` at any
geometric points are isomorphic as topological groups (V.6.10 and a class of paths). -/
theorem nonempty_continuousMulEquiv_of_isEquivalence {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂)
    [(FEt.pullback g).IsEquivalence] [ConnectedSpace X₁] [ConnectedSpace X₂] (K₁ K₂ : Type u)
    [Field K₁] [IsSepClosed K₁] [Field K₂] [IsSepClosed K₂] (a₁ : Spec (.of K₁) ⟶ X₁)
    (a₂ : Spec (.of K₂) ⟶ X₂) :
    Nonempty (ExposeV.etaleFundamentalGroup K₁ a₁ ≃ₜ* ExposeV.etaleFundamentalGroup K₂ a₂) := by
  have : FiberFunctor (FEt.pullback g ⋙ ExposeV.FEt.fiber K₁ a₁) :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso K₁ g a₁).symm
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor
    (FEt.pullback g ⋙ ExposeV.FEt.fiber K₁ a₁) (ExposeV.FEt.fiber K₂ a₂)
  exact ⟨(ExposeIX.autMapEquiv (FEt.pullback g) (ExposeV.FEt.fiber K₁ a₁)).trans
    (ExposeV.conjAutContinuousMulEquiv φ)⟩

/-- A nonempty scheme has a geometric point with values in an algebraically closed field. -/
lemma exists_geometricPoint_of_nonempty (Z : Scheme.{u}) [Nonempty Z] :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K), Nonempty (Spec (.of K) ⟶ Z) := by
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  exact ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z)
      (AlgebraicClosure (Z.residueField z)))) ≫ Z.fromSpecResidueField z⟩⟩

end FundamentalGroupIso

section GeometricPoints

/-- Every geometric point `s : Spec Ω ⟶ S` with `Ω` algebraically closed is
`Spec Ω ⟶ Spec κ(y)ᵃˡᵍ ⟶ S` at its image `y = s(pt)` (`ExposeXIII.exists_eq_comp_geometricPoint`,
with the point identified). -/
lemma exists_eq_geometricPointOf {S : Scheme.{u}} (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ _ : Algebra (AlgebraicClosure (S.residueField (s (closedPoint Ω)))) Ω,
      s = geometricPointOf (s (closedPoint Ω)) Ω := by
  obtain ⟨y, inst, hs⟩ := ExposeXIII.exists_eq_comp_geometricPoint Ω s
  have hy : s (closedPoint Ω) = y := by
    obtain ⟨pt, hpt⟩ : ∃ pt : Spec (.of Ω), pt = closedPoint Ω := ⟨_, rfl⟩
    rw [← hpt, hs, geometricPoint, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  subst hy
  exact ⟨inst, hs⟩

/-- A morphism `Spec K ⟶ Y` factors through `Spec κ(y) ⟶ Y` at its image `y`. -/
lemma exists_eq_specMap_comp_fromSpecResidueField {Y : Scheme.{u}} (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ Y) :
    ∃ φ : Y.residueField (b (closedPoint K)) ⟶ .of K,
      b = Spec.map φ ≫ Y.fromSpecResidueField (b (closedPoint K)) := by
  obtain ⟨y, φ, hb⟩ : ∃ y φ, b = Spec.map φ ≫ Y.fromSpecResidueField y :=
    ⟨_, _, ((Scheme.SpecToEquivOfField K Y).symm_apply_apply b).symm⟩
  have hy : b (closedPoint K) = y := by
    obtain ⟨pt, hpt⟩ : ∃ pt : Spec (.of K), pt = closedPoint K := ⟨_, rfl⟩
    rw [← hpt, hb, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  subst hy
  exact ⟨φ, hb⟩

/-- Two field extensions of a field embed compatibly into an algebraically closed field. -/
lemma exists_isAlgClosed_amalgamation {k K₁ K₂ : Type u} [Field k] [Field K₁] [Field K₂]
    (i₁ : k →+* K₁) (i₂ : k →+* K₂) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (j₁ : K₁ →+* L) (j₂ : K₂ →+* L),
      j₁.comp i₁ = j₂.comp i₂ := by
  let := i₁.toAlgebra
  let := i₂.toAlgebra
  have : Nontrivial (K₁ ⊗[k] K₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K₁ K₂
      i₁.injective i₂.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K₁ ⊗[k] K₂)
  let := Ideal.Quotient.field M
  let q : K₁ ⊗[k] K₂ →+* AlgebraicClosure (K₁ ⊗[k] K₂ ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  refine ⟨AlgebraicClosure (K₁ ⊗[k] K₂ ⧸ M), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom,
    q.comp (Algebra.TensorProduct.includeRight (R := k) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  ext a
  change q (i₁ a ⊗ₜ 1) = q (1 ⊗ₜ i₂ a)
  congr 1
  change algebraMap k K₁ a ⊗ₜ[k] (1 : K₂) = (1 : K₁) ⊗ₜ algebraMap k K₂ a
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GeometricPoints

section CompletedStalk

variable {Y : Scheme.{u}}

/-- The completed local ring `𝒪̂_{Y,y}`. -/
noncomputable abbrev completedStalk (Y : Scheme.{u}) (y : Y) : Type u :=
  AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)

/-- The reduction `𝒪̂_{Y,y} ⟶ κ(y)`. -/
noncomputable def completedResidue (y : Y) :
    CommRingCat.of (completedStalk Y y) ⟶ Y.residueField y :=
  CommRingCat.ofHom
    ((Ideal.quotEquivOfEq (pow_one (maximalIdeal (Y.presheaf.stalk y)))).toRingHom.comp
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) 1).toRingHom)

lemma algebraMap_comp_completedResidue (y : Y) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) (completedStalk Y y)) ≫
      completedResidue y = Y.residue y := by
  ext x
  change (Ideal.quotEquivOfEq (pow_one (maximalIdeal (Y.presheaf.stalk y))))
    (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) 1
      (AdicCompletion.of _ (Y.presheaf.stalk y) x)) = IsLocalRing.residue _ x
  rw [AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk]
  rfl

lemma surjective_completedResidue (y : Y) : Function.Surjective (completedResidue y) := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  exact ⟨algebraMap _ _ x, congrArg (fun g ↦ g.hom x) (algebraMap_comp_completedResidue y)⟩

/-- `Spec κ(y) ⟶ Y` factors through `Spec 𝒪̂_{Y,y}`. -/
lemma specMap_completedResidue_comp (y : Y) :
    Spec.map (completedResidue y) ≫ ExposeIX.fromSpecCompletedStalk Y y =
      Y.fromSpecResidueField y := by
  rw [ExposeIX.fromSpecCompletedStalk, ← Category.assoc, ← Spec.map_comp,
    algebraMap_comp_completedResidue]
  rfl

/-- `Spec κ(y) ⟶ Spec 𝒪̂_{Y,y}` hits the closed point. -/
lemma specMap_completedResidue_apply [IsLocallyNoetherian Y] (y : Y) (K : Type u) [Field K]
    (φ : Y.residueField y ⟶ .of K) :
    (Spec.map φ ≫ Spec.map (completedResidue y)) (closedPoint K) =
      closedPoint (completedStalk Y y) := by
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (.of K), pt = closedPoint K := ⟨_, rfl⟩
  rw [← hpt]
  apply PrimeSpectrum.ext
  change Ideal.comap (completedResidue y).hom (Ideal.comap φ.hom pt.asIdeal) = _
  have h₀ : pt.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ pt.isPrime
  rw [h₀, Ideal.comap_bot_of_injective _ φ.hom.injective]
  exact IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (surjective_completedResidue y))

/-- A morphism `b : Spec K ⟶ Y` lifts to `Spec 𝒪̂_{Y,y}` at its closed point, `y = b(pt)`. -/
theorem exists_lift_fromSpecCompletedStalk [IsLocallyNoetherian Y] (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ Y) :
    ∃ b' : Spec (.of K) ⟶ Spec (.of (completedStalk Y (b (closedPoint K)))),
      b' ≫ ExposeIX.fromSpecCompletedStalk Y (b (closedPoint K)) = b ∧
        b' (closedPoint K) = closedPoint (completedStalk Y (b (closedPoint K))) := by
  obtain ⟨φ, hb⟩ := exists_eq_specMap_comp_fromSpecResidueField K b
  refine ⟨Spec.map φ ≫ Spec.map (completedResidue _), ?_,
    specMap_completedResidue_apply _ K φ⟩
  rw [Category.assoc, specMap_completedResidue_comp, ← hb]

lemma fromSpecResidueField_congr {X : Scheme.{u}} {x y : X} (e : x = y) :
    Spec.map (X.residueFieldCongr e).hom ≫ X.fromSpecResidueField x =
      X.fromSpecResidueField y := by
  subst e
  simp

/-- A morphism `b : Spec K ⟶ Y` whose image generalizes `y₀` lifts to `Spec 𝒪̂_{Y,y₀}` after an
algebraically closed extension of `K` (`Spec 𝒪̂_{Y,y₀} ⟶ Spec 𝒪_{Y,y₀}` is surjective). -/
theorem exists_lift_fromSpecCompletedStalk_of_specializes [IsLocallyNoetherian Y] (y₀ : Y)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y) (h : b (closedPoint K) ⤳ y₀) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : Algebra K L)
      (b' : Spec (.of L) ⟶ Spec (.of (completedStalk Y y₀))),
      b' ≫ ExposeIX.fromSpecCompletedStalk Y y₀ =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b := by
  obtain ⟨z, hz⟩ : b (closedPoint K) ∈ Set.range (Y.fromSpecStalk y₀) := by
    rw [Scheme.range_fromSpecStalk]
    exact h
  obtain ⟨w, hw⟩ := (ExposeIX.flat_and_surjective_specMap_completion y₀).2.surj z
  have hcw : b (closedPoint K) = ExposeIX.fromSpecCompletedStalk Y y₀ w := by
    rw [← hz, ← hw]
    exact (Scheme.Hom.comp_apply _ _ w).symm
  obtain ⟨φ, hb⟩ := exists_eq_specMap_comp_fromSpecResidueField K b
  let ρ := (Y.residueFieldCongr hcw).hom ≫
    (ExposeIX.fromSpecCompletedStalk Y y₀).residueFieldMap w
  have hρ : ρ = (Y.residueFieldCongr hcw).hom ≫
    (ExposeIX.fromSpecCompletedStalk Y y₀).residueFieldMap w := rfl
  obtain ⟨L, _, _, j₁, j₂, hj⟩ := exists_isAlgClosed_amalgamation φ.hom ρ.hom
  let _ : Algebra K L := j₁.toAlgebra
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom j₂) ≫ (Spec (.of (completedStalk Y y₀))).fromSpecResidueField w,
    ?_⟩
  have hj' : φ ≫ CommRingCat.ofHom j₁ = ρ ≫ CommRingCat.ofHom j₂ := by
    ext x
    exact congrArg (fun g ↦ g x) hj
  have e₁ : (Spec.map (CommRingCat.ofHom j₂) ≫
      (Spec (.of (completedStalk Y y₀))).fromSpecResidueField w) ≫
        ExposeIX.fromSpecCompletedStalk Y y₀ =
      Spec.map (ρ ≫ CommRingCat.ofHom j₂) ≫ Y.fromSpecResidueField (b (closedPoint K)) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← fromSpecResidueField_congr hcw, Spec.map_comp ρ (CommRingCat.ofHom j₂), hρ,
      Spec.map_comp, Category.assoc, Category.assoc]
    rfl
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b =
      Spec.map (φ ≫ CommRingCat.ofHom j₁) ≫ Y.fromSpecResidueField (b (closedPoint K)) := by
    conv_lhs => rw [hb]
    rw [Spec.map_comp φ (CommRingCat.ofHom j₁), Category.assoc]
  rw [e₁, e₂, hj']

end CompletedStalk

section Statement

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.4**, given the lifting of étale coverings from the closed fibre of the base change of `f`
to the completed local ring at the specialization (IX.1.10). Let `f : X ⟶ Y` be proper and
separable with geometrically connected fibres, `Y` locally noetherian, `b₀`, `b₁` geometric points
of `Y` with algebraically closed values such that the image of `b₁` specializes to that `y₀` of
`b₀`, and `a₀`, `a₁` geometric points of the geometric fibres `X_{b₀}`, `X_{b₁}`. Then there is a
continuous surjective homomorphism `π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)` (the specialization
homomorphism). As in SGA we pass to `Y' = Spec 𝒪̂_{Y,y₀}`, where X.2.3 applies. -/
theorem exists_continuous_surjective_specialization {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsSeparable f] [GeometricallyConnected f] [IsLocallyNoetherian Y] (Ω₀ Ω₁ : Type u)
    [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁] [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Y)
    (b₁ : Spec (.of Ω₁) ⟶ Y) (hsp : b₁ (closedPoint Ω₁) ⤳ b₀ (closedPoint Ω₀))
    (hlift : ExposeIX.LiftsFiniteEtale
      ((pullback.snd f (ExposeIX.fromSpecCompletedStalk Y (b₀ (closedPoint Ω₀)))).fiberι
        (closedPoint (completedStalk Y (b₀ (closedPoint Ω₀))))))
    (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁) :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Surjective sp := by
  -- the complete local base `S' = Spec 𝒪̂_{Y,y₀}` and `f' : X ×_Y S' ⟶ S'`
  set y₀ := b₀ (closedPoint Ω₀)
  let c := ExposeIX.fromSpecCompletedStalk Y y₀
  let f' := pullback.snd f c
  have : GeometricallyConnected f' := MorphismProperty.pullback_snd _ _ inferInstance
  have hf' := ExposeXIII.isIso_app_of_geometricallyConnected f'
  -- the geometric points of `S'`
  obtain ⟨b₀', hb₀', hb₀pt⟩ := exists_lift_fromSpecCompletedStalk Ω₀ b₀
  obtain ⟨L, _, _, _, b₁', hb₁'⟩ := exists_lift_fromSpecCompletedStalk_of_specializes y₀ Ω₁ b₁ hsp
  obtain ⟨inst₀, hdec₀⟩ := exists_eq_geometricPointOf Ω₀ b₀'
  generalize hp : b₀' (closedPoint Ω₀) = p at inst₀ hdec₀
  obtain rfl : p = closedPt (completedStalk Y y₀) := hp.symm.trans hb₀pt
  obtain ⟨inst₁, hdec₁⟩ := exists_eq_geometricPointOf L b₁'
  generalize b₁' (closedPoint L) = y₁ at inst₁ hdec₁
  subst hdec₀ hdec₁
  -- connectedness
  have : ConnectedSpace ↥(pullback f b₀) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) b₀ _ _
      (IsPullback.of_hasPullback f b₀)
  have : ConnectedSpace ↥(pullback f b₁) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) b₁ _ _
      (IsPullback.of_hasPullback f b₁)
  have : ConnectedSpace ↥(pullback f' (closedGeometricPoint (completedStalk Y y₀) Ω₀)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') _ _ _
      (IsPullback.of_hasPullback f' _)
  have : ConnectedSpace ↥(pullback f' (geometricPointOf y₁ L)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') _ _ _
      (IsPullback.of_hasPullback f' _)
  obtain ⟨K₀, _, _, ⟨a₀'⟩⟩ := exists_geometricPoint_of_nonempty
    (pullback f' (closedGeometricPoint (completedStalk Y y₀) Ω₀))
  obtain ⟨K₁, _, _, ⟨a₁'⟩⟩ := exists_geometricPoint_of_nonempty
    (pullback f' (geometricPointOf y₁ L))
  -- X.2.3 over `S'`
  obtain ⟨sp, hsp_cont, hsp_surj⟩ :=
    exists_continuous_surjective_specialization_of_completeLocal (completedStalk Y y₀) f' hf'
      hlift Ω₀ y₁ L K₀ K₁ a₀' a₁'
  -- `X'_{b₀'} ≅ X_{b₀}`
  let j₀ : pullback f' (closedGeometricPoint (completedStalk Y y₀) Ω₀) ≅ pullback f b₀ :=
    pullbackLeftPullbackSndIso f c _ ≪≫ pullback.congrHom rfl hb₀'
  obtain ⟨e₀⟩ := nonempty_continuousMulEquiv_of_isEquivalence j₀.hom K₀ Ω₀ a₀' a₀
  -- `X'_{b₁'} ≅ X_{b₁} ⊗ L`, and X.1.8
  let σ := Spec.map (CommRingCat.ofHom (algebraMap Ω₁ L))
  have := baseChangeAlgClosedStatement Ω₁ L (pullback.snd f b₁)
  let j₁ : pullback f' (geometricPointOf y₁ L) ≅
      pullback (pullback.snd f b₁) σ :=
    pullbackLeftPullbackSndIso f c _ ≪≫ pullback.congrHom rfl hb₁' ≪≫
      (pullbackLeftPullbackSndIso f b₁ σ).symm
  have : (FEt.pullback (j₁.hom ≫ pullback.fst (pullback.snd f b₁) σ)).IsEquivalence :=
    ExposeV.FEt.isEquivalence_pullback_comp _ _
  obtain ⟨e₁⟩ := nonempty_continuousMulEquiv_of_isEquivalence
    (j₁.hom ≫ pullback.fst (pullback.snd f b₁) σ) K₁ Ω₁ a₁' a₁
  exact ⟨e₀.toMonoidHom.comp (sp.comp e₁.symm.toMonoidHom),
    e₀.continuous.comp (hsp_cont.comp e₁.symm.continuous),
    e₀.surjective.comp (hsp_surj.comp e₁.symm.surjective)⟩

/-- **X.2.4** from IX.1.10 (`ExposeIX.EtaleCoveringsOfClosedFibreStatement`): the essential
surjectivity in IX.1.10, for proper schemes over complete noetherian local rings, is the only
input of the specialization theorem which is not proved in general. -/
theorem specializationSurjectiveStatement_of_etaleCoveringsOfClosedFibreStatement
    (h : ExposeIX.EtaleCoveringsOfClosedFibreStatement.{u}) :
    SpecializationSurjectiveStatement.{u} := by
  intro X Y f _ _ _ _ Ω₀ Ω₁ _ _ _ _ b₀ b₁ hsp a₀ a₁
  exact exists_continuous_surjective_specialization f Ω₀ Ω₁ b₀ b₁ hsp
    (ExposeIX.liftsFiniteEtale_fiberι_closedPoint_of_statement _ _ h) a₀ a₁

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.4 for `X` projective over `Y`** (a closed subscheme of `ℙ(τ; Y)`, `τ` finite):
unconditional, since IX.1.10 holds for projective schemes over complete noetherian local rings
(Grothendieck's existence theorem in the foundations). Let `f : X ⟶ Y` be separable with
geometrically connected fibres, `Y` locally noetherian, `b₀`, `b₁` geometric points of `Y` with
algebraically closed values such that the image of `b₁` specializes to that of `b₀`, and `a₀`,
`a₁` geometric points of `X_{b₀}`, `X_{b₁}`. Then there is a continuous surjective homomorphism
`π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)`. -/
theorem exists_continuous_surjective_specialization_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsSeparable f] [GeometricallyConnected f] [IsLocallyNoetherian Y]
    {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Y)) [IsClosedImmersion κ] (hf : f = κ ≫ ℙ(τ; Y) ↘ Y)
    (Ω₀ Ω₁ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁] [IsAlgClosed Ω₁]
    (b₀ : Spec (.of Ω₀) ⟶ Y) (b₁ : Spec (.of Ω₁) ⟶ Y)
    (hsp : b₁ (closedPoint Ω₁) ⤳ b₀ (closedPoint Ω₀))
    (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁) :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Surjective sp := by
  refine exists_continuous_surjective_specialization f Ω₀ Ω₁ b₀ b₁ hsp ?_ a₀ a₁
  set c := ExposeIX.fromSpecCompletedStalk Y (b₀ (closedPoint Ω₀))
  -- the closed immersion `X ×_Y S' ⟶ ℙ(τ; S')`
  have hmap := ProjectiveSpace.isPullback_map (σ := τ) c
  have hw : (pullback.fst f c ≫ κ) ≫ ℙ(τ; Y) ↘ Y = pullback.snd f c ≫ c := by
    rw [Category.assoc, ← hf, pullback.condition]
  let κ' := hmap.lift _ _ hw
  have hκ'₁ : κ' ≫ ProjectiveSpace.map Y c = pullback.fst f c ≫ κ := hmap.lift_fst _ _ _
  have hκ'₂ : κ' ≫ ℙ(τ; _) ↘ _ = pullback.snd f c := hmap.lift_snd _ _ _
  have hsq : IsPullback (pullback.fst f c) κ' κ (ProjectiveSpace.map Y c) := by
    refine IsPullback.of_bot ?_ hκ'₁.symm hmap
    rw [hκ'₂, ← hf]
    exact IsPullback.of_hasPullback f c
  have : IsClosedImmersion κ' := MorphismProperty.of_isPullback hsq ‹_›
  exact ExposeIX.liftsFiniteEtale_fiberι_closedPoint_of_isClosedImmersion _ _ κ' hκ'₂.symm

end Statement

end SGA.SGA1.ExposeX
