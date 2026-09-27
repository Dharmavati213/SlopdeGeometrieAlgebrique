/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.FiniteEtaleLimit
import SGA.SGA1.ExposeIX.ProperEffectiveDescent

/-!
# SGA 1, Exposé IX, 6.1 over a complete local base (X.2.2)

The proof of IX.6.1 (`e → π₁(X̄₀) → π₁(X) → π₁(S)`) uses two properties of the one-point base
`S`: finite étale coverings of the fibre `X_s` lift to `X`, and morphisms to étale coverings extend
from the fibres `(X ×_S S') ⊗ κ(s)` to `X ×_S S'` (both are I.8.3 / IX.1.7 for nil-immersions).
When `S = Spec R` with `R` a complete noetherian local ring, `s` the closed point and `f : X ⟶ S`
proper, the second property is the full faithfulness in IX.1.10, which does not use the existence
theorem, and the first one is the essential surjectivity in IX.1.10 (proved in
`EtaleCoveringsClosedFibre` for `X` projective). This is the exact sequence X.2.2:

* `exactSequence_of_completeLocal`: injectivity and exactness at `π₁(X)`, given the lifting of
  étale coverings from the closed fibre (IX.1.10, essential surjectivity);
* `exactSequence_of_completeLocal_of_isClosedImmersion`: the same for `X` projective over `R`,
  unconditionally;
* `exactSequence_of_completeLocal_of_statement`: the same for every proper `X`, from IX.1.10
  (`EtaleCoveringsOfClosedFibreStatement`);
* `ker_le_range_of_completeLocal`: the inclusion `ker ⊆ im`, which needs only the full faithfulness;
* IX.6.7–IX.6.8 over a complete local base, the essential image: an étale covering of `X` comes
  from `Spec R` iff its restriction to the closed fibre is geometrically trivial
  (`mem_essImage_iff_isGeometricallyTrivial_closedFibre`,
  `mem_essImage_iff_forall_isGeometricallyTrivial_of_completeLocal`);
* IX.6.11 over a complete local base (`ker_autMap_eq_geometricFibres_of_completeLocal`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty PreGaloisCategory IsLocalRing

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)

section ClosedPoint

variable (R : Type u) [CommRing R] [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
/-- For a local ring `R`, the morphism `Spec κ(𝔪) ⟶ Spec R` from the residue field of the scheme
`Spec R` at its closed point is `Spec (R ⧸ 𝔪) ⟶ Spec R` up to isomorphism. -/
lemma exists_iso_fromSpecResidueField_closedPoint :
    ∃ e : Spec ((Spec (.of R)).residueField (closedPoint R)) ≅ Spec (.of (R ⧸ maximalIdeal R)),
      e.hom ≫ specQuotient (maximalIdeal R) =
        (Spec (.of R)).fromSpecResidueField (closedPoint R) := by
  let e₂ : CommRingCat.of (R ⧸ maximalIdeal R) ≅ .of (maximalIdeal R).ResidueField :=
    (RingEquiv.ofBijective _
      (maximalIdeal R).bijective_algebraMap_quotient_residueField).toCommRingCatIso
  let e₁ := Scheme.Spec.residueFieldIso (.of R) (closedPoint R)
  refine ⟨asIso (Spec.map e₁.inv ≫ Spec.map e₂.hom), ?_⟩
  rw [asIso_hom, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Category.assoc,
    ← Spec.map_comp]
  congr 2

/-- The pullback along `u.hom ≫ g'`, `u` an isomorphism, as a pullback along `g'`. -/
lemma isPullback_fst_comp_iso {X Y Y' Z : Scheme.{u}} (f : X ⟶ Z) (g' : Y' ⟶ Z) (u : Y ≅ Y') :
    IsPullback (pullback.fst f (u.hom ≫ g')) (pullback.snd f (u.hom ≫ g') ≫ u.hom) f g' :=
  (IsPullback.of_hasPullback f (u.hom ≫ g')).of_iso (Iso.refl _) (Iso.refl _) u (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

variable [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.7 for a complete local ring `R` (henselian): base change along `Spec κ(𝔪) ⟶ Spec R` is
an equivalence of the categories of étale coverings (I.8.4). -/
theorem isEquivalence_pullback_fromSpecResidueField_closedPoint :
    (MorphismProperty.Over.pullback FEt ⊤
      ((Spec (.of R)).fromSpecResidueField (closedPoint R))).IsEquivalence := by
  let A := CommRingCat.of R
  let x := closedPoint R
  have : x.asIdeal.IsMaximal := inferInstanceAs (maximalIdeal R).IsMaximal
  have hsurj : Function.Surjective (algebraMap A x.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have : IsNoetherianRing A := ‹IsNoetherianRing R›
  have : IsAdicComplete (RingHom.ker (algebraMap A x.asIdeal.ResidueField)) A := by
    rw [Ideal.ker_algebraMap_residueField]
    exact ‹IsAdicComplete (maximalIdeal R) R›
  have : (CommAlgCat.FiniteEtale.baseChange.{u} A
      (CommRingCat.of x.asIdeal.ResidueField)).IsEquivalence :=
    CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective hsurj
  have : (ExposeV.FEt.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A x.asIdeal.ResidueField)))).IsEquivalence :=
    Scheme.FiniteEtale.isEquivalence_pullback_spec A (CommRingCat.of x.asIdeal.ResidueField)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  exact ExposeV.FEt.isEquivalence_pullback_comp _ _

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10, full faithfulness, in the form used in IX.6.1: for `W` proper over `Spec R`, `R`
complete noetherian local, morphisms to étale coverings extend from the closed fibre
`W ×_{Spec R} Spec κ(𝔪)` to `W`. -/
theorem extendsEtaleHoms_closedFibre {W : Scheme.{u}} (p : W ⟶ Spec (.of R)) [IsProper p] :
    ExtendsEtaleHoms (pullback.fst p ((Spec (.of R)).fromSpecResidueField (closedPoint R))) := by
  obtain ⟨e, he⟩ := exists_iso_fromSpecResidueField_closedPoint R
  rw [← he]
  have h := isPullback_fst_comp_iso p (specQuotient (maximalIdeal R)) e
  have : (MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst p (e.hom ≫ specQuotient (maximalIdeal R)))).Full :=
    (full_and_faithful_pullback_of_isPullback h).1
  exact extendsEtaleHoms_of_full _

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10, essential surjectivity, transported to the closed fibre `X ×_{Spec R} Spec κ(𝔪)`:
if every étale covering of `X ×_{Spec R} Spec (R ⧸ 𝔪)` comes from `X`, so does every étale covering
of the scheme-theoretic fibre of `X` at the closed point. -/
theorem liftsFiniteEtale_fiberι_closedPoint {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [(MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst f (specQuotient (maximalIdeal R)))).EssSurj] :
    LiftsFiniteEtale (f.fiberι (closedPoint R)) := by
  obtain ⟨e, he⟩ := exists_iso_fromSpecResidueField_closedPoint R
  have h₀ := liftsFiniteEtale_of_essSurj (pullback.fst f (specQuotient (maximalIdeal R)))
  have h := isPullback_fst_comp_iso f (specQuotient (maximalIdeal R)) e
  have h₁ := h₀.iso_comp h.isoPullback
  rw [h.isoPullback_hom_fst, he] at h₁
  exact h₁

end ClosedPoint

section ExactSequence

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- IX.6.1 over a complete local base, exactness at `π₁(X)`, the inclusion `ker ⊆ im`: this part
only uses the full faithfulness in IX.1.10 (no lifting of étale coverings from the closed fibre
is needed). -/
theorem ker_le_range_of_completeLocal
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f (closedPoint R)) ⥤ FintypeCat.{u})
    [FiberFunctor F'']
    [FiberFunctor
      (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')).ker ≤
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)))
        F'').range := by
  have : IsProper (f.fiberToSpecResidueField (closedPoint R)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiSeparatedSpace (f.fiber (closedPoint R)) :=
    quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField (closedPoint R))
  have := isEquivalence_pullback_fromSpecResidueField_closedPoint R
  refine ker_le_range_of_extendsEtaleHoms f _ (fun Z ↦ ?_) F''
  have : IsFinite Z.hom := Z.prop.1
  exact extendsEtaleHoms_closedFibre R (pullback.snd Z.hom f ≫ f)

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.2** (IX.6.1 over a complete local base), given the lifting of étale coverings from the
closed fibre (IX.1.10, essential surjectivity): let `R` be a complete noetherian local ring,
`f : X ⟶ Spec R` proper with geometrically connected closed fibre `X₀`, and `X̄₀` the geometric
closed fibre. Then `e → π₁(X̄₀) → π₁(X) → π₁(Spec R)` is exact at `π₁(X̄₀)` and `π₁(X)`, for any
Galois structures and compatible fibre functors. As SGA remarks, no flatness or separability of
`f` is needed, and the injectivity of `π₁(X̄₀) → π₁(X)` is the important complement. -/
theorem exactSequence_of_completeLocal (hlift : LiftsFiniteEtale (f.fiberι (closedPoint R)))
    (hg : GeometricallyConnected (f.fiberToSpecResidueField (closedPoint R)))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f (closedPoint R)) ⥤ FintypeCat.{u})
    [FiberFunctor F'']
    [FiberFunctor
      (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')] :
    Function.Injective
        (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R))) F'') ∧
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)))
          F'').range =
        (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
          (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙
            F'')).ker := by
  have : IsProper (f.fiberToSpecResidueField (closedPoint R)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiSeparatedSpace (f.fiber (closedPoint R)) :=
    quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField (closedPoint R))
  have := isEquivalence_pullback_fromSpecResidueField_closedPoint R
  refine ⟨injective_autMap_geometricFiberι_of_lift f _ hlift F'',
    le_antisymm (range_le_ker_geometricFiber f _ hg F'')
      (ker_le_range_of_extendsEtaleHoms f _ (fun Z ↦ ?_) F'')⟩
  have : IsFinite Z.hom := Z.prop.1
  exact extendsEtaleHoms_closedFibre R (pullback.snd Z.hom f ≫ f)

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10 (as `EtaleCoveringsOfClosedFibreStatement`) gives the lifting of étale coverings from
the closed fibre used in X.2.2. -/
theorem liftsFiniteEtale_fiberι_closedPoint_of_statement
    (h : EtaleCoveringsOfClosedFibreStatement.{u}) : LiftsFiniteEtale (f.fiberι (closedPoint R)) :=
  have : (MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst f (specQuotient (maximalIdeal R)))).IsEquivalence := h R X f
  liftsFiniteEtale_fiberι_closedPoint R f

omit [IsProper f] in
set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10 for `X` projective over `R` gives the lifting of étale coverings from the closed fibre
used in X.2.2. -/
theorem liftsFiniteEtale_fiberι_closedPoint_of_isClosedImmersion {τ : Type u} [Finite τ]
    (κ : X ⟶ ℙ(τ; Spec (.of R))) [IsClosedImmersion κ]
    (hf : f = κ ≫ ℙ(τ; Spec (.of R)) ↘ Spec (.of R)) :
    LiftsFiniteEtale (f.fiberι (closedPoint R)) :=
  have : (MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst f (specQuotient (maximalIdeal R)))).IsEquivalence :=
    isEquivalence_pullback_closedFibre_of_isClosedImmersion R κ f hf
  liftsFiniteEtale_fiberι_closedPoint R f

/-- **X.2.2 for `X` projective over `R`**: let `R` be a complete noetherian local ring and `X` a
closed subscheme of `ℙ(τ; Spec R)`, `τ` finite, with geometrically connected closed fibre. Then
`e → π₁(X̄₀) → π₁(X) → π₁(Spec R)` is exact at `π₁(X̄₀)` and `π₁(X)`. -/
theorem exactSequence_of_completeLocal_of_isClosedImmersion {τ : Type u} [Finite τ]
    (κ : X ⟶ ℙ(τ; Spec (.of R))) [IsClosedImmersion κ]
    (hf : f = κ ≫ ℙ(τ; Spec (.of R)) ↘ Spec (.of R))
    (hg : GeometricallyConnected (f.fiberToSpecResidueField (closedPoint R)))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f (closedPoint R)) ⥤ FintypeCat.{u})
    [FiberFunctor F'']
    [FiberFunctor
      (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')] :
    Function.Injective
        (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R))) F'') ∧
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)))
          F'').range =
        (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
          (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')).ker :=
  exactSequence_of_completeLocal R f
    (liftsFiniteEtale_fiberι_closedPoint_of_isClosedImmersion R f κ hf) hg F''

/-- **X.2.2** for every proper `X`, from IX.1.10 (`EtaleCoveringsOfClosedFibreStatement`). -/
theorem exactSequence_of_completeLocal_of_statement (h : EtaleCoveringsOfClosedFibreStatement.{u})
    (hg : GeometricallyConnected (f.fiberToSpecResidueField (closedPoint R)))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f (closedPoint R)) ⥤ FintypeCat.{u})
    [FiberFunctor F'']
    [FiberFunctor
      (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')] :
    Function.Injective
        (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R))) F'') ∧
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)))
          F'').range =
        (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
          (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f (closedPoint R)) ⋙ F'')).ker :=
  exactSequence_of_completeLocal R f (liftsFiniteEtale_fiberι_closedPoint_of_statement R f h) hg
    F''

end ExactSequence

section EssentialImage

/-- IX.6.8, necessity of the condition on the fibres: the inverse image `f^* W` of an étale
covering `W` of `S` induces on every fibre `X_s` a geometrically trivial covering. -/
theorem isGeometricallyTrivial_of_mem_essImage {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    {Y : MorphismProperty.Over FEt ⊤ X} (hY : (MorphismProperty.Over.pullback FEt ⊤ f).essImage Y) :
    IsGeometricallyTrivial (f.fiberToSpecResidueField s)
      ((MorphismProperty.Over.pullback FEt ⊤ (f.fiberι s)).obj Y) := by
  obtain ⟨W, ⟨e⟩⟩ := hY
  exact ⟨(MorphismProperty.Over.pullback FEt ⊤ (S.fromSpecResidueField s)).obj W,
    ⟨((fetPullbackCompCongr f (f.fiberι s) (S.fromSpecResidueField s)
      (f.fiberToSpecResidueField s) pullback.condition).app W).symm ≪≫
        (MorphismProperty.Over.pullback FEt ⊤ (f.fiberι s)).mapIso e⟩⟩

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10, full faithfulness, for the scheme-theoretic closed fibre `X_s ⟶ X`. -/
theorem full_and_faithful_pullback_fiberι_closedPoint :
    (MorphismProperty.Over.pullback FEt ⊤ (f.fiberι (closedPoint R))).Full ∧
      (MorphismProperty.Over.pullback FEt ⊤ (f.fiberι (closedPoint R))).Faithful := by
  obtain ⟨e, he⟩ := exists_iso_fromSpecResidueField_closedPoint R
  have h := full_and_faithful_pullback_of_isPullback
    (isPullback_fst_comp_iso f (specQuotient (maximalIdeal R)) e)
  change (MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst f ((Spec (.of R)).fromSpecResidueField (closedPoint R)))).Full ∧
    (MorphismProperty.Over.pullback FEt ⊤
      (pullback.fst f ((Spec (.of R)).fromSpecResidueField (closedPoint R)))).Faithful
  rw [← he]
  exact h

/-- **IX.6.7–IX.6.8 over a complete local base** (the essential image): let `R` be a complete
noetherian local ring and `f : X ⟶ Spec R` proper. An étale covering `Y` of `X` is isomorphic to
`X ×_R W` for an étale covering `W` of `Spec R` iff its restriction to the closed fibre `X₀` is
geometrically trivial. (SGA: the covering of `X₀` is `X₀ ⊗ L`, `L` lifts to an étale `R`-algebra
since `R` is henselian, and the full faithfulness in IX.1.10 identifies `Y` with `X ⊗_R W`.) -/
theorem mem_essImage_iff_isGeometricallyTrivial_closedFibre (Y : MorphismProperty.Over FEt ⊤ X) :
    (MorphismProperty.Over.pullback FEt ⊤ f).essImage Y ↔
      IsGeometricallyTrivial (f.fiberToSpecResidueField (closedPoint R))
        ((MorphismProperty.Over.pullback FEt ⊤ (f.fiberι (closedPoint R))).obj Y) := by
  refine ⟨isGeometricallyTrivial_of_mem_essImage f _, fun ⟨L, ⟨eL⟩⟩ ↦ ?_⟩
  have := isEquivalence_pullback_fromSpecResidueField_closedPoint R
  obtain ⟨hfull, hfaith⟩ := full_and_faithful_pullback_fiberι_closedPoint R f
  let j := (Spec (.of R)).fromSpecResidueField (closedPoint R)
  let W := (MorphismProperty.Over.pullback FEt ⊤ j).objPreimage L
  let eW := (MorphismProperty.Over.pullback FEt ⊤ j).objObjPreimageIso L
  refine ⟨W, ⟨(MorphismProperty.Over.pullback FEt ⊤ (f.fiberι (closedPoint R))).preimageIso ?_⟩⟩
  exact (fetPullbackCompCongr f (f.fiberι _) j (f.fiberToSpecResidueField _)
    pullback.condition).app W ≪≫
      (MorphismProperty.Over.pullback FEt ⊤ (f.fiberToSpecResidueField _)).mapIso eW ≪≫ eL

/-- IX.6.8, the essential image, over a complete local base: an étale covering of `X` comes from
`Spec R` iff it induces a geometrically trivial covering on every fibre (the fourth part of
`ProperDescentStatement`). -/
theorem mem_essImage_iff_forall_isGeometricallyTrivial_of_completeLocal
    (Y : MorphismProperty.Over FEt ⊤ X) :
    (MorphismProperty.Over.pullback FEt ⊤ f).essImage Y ↔
      ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s)
        ((MorphismProperty.Over.pullback FEt ⊤ (f.fiberι s)).obj Y) :=
  ⟨fun h s ↦ isGeometricallyTrivial_of_mem_essImage f s h,
    fun h ↦ (mem_essImage_iff_isGeometricallyTrivial_closedFibre R f Y).mpr (h _)⟩

end EssentialImage

section KernelCompleteLocal

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- **IX.6.11 over a complete local base** (`GeometricFibresStatement` for `S = Spec R`, `R`
complete noetherian local): the kernel of `π₁(X) → π₁(Spec R)` is the closed normal subgroup
generated by the images of the `π₁(X̄_s)`; in fact it is the image of `π₁(X̄₀)` for the closed
point alone (X.2.2). Only the full faithfulness in IX.1.10 is used. -/
theorem ker_autMap_eq_geometricFibres_of_completeLocal [GeometricallyConnected f]
    (F' : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{u}) [FiberFunctor F']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F')]
    (G : ∀ s, MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u})
    [∀ s, FiberFunctor (G s)]
    (d : ∀ s, MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ G s ≅ F') :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F').ker =
      (Subgroup.normalClosure (⋃ s, Set.range (pathMap F'
        (fun s ↦ MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) G d s))
        ).topologicalClosure := by
  refine le_antisymm ?_ (normalClosure_le_ker_geometricFibres f F' G d)
  let s₀ : Spec (.of R) := closedPoint R
  have : FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s₀) ⋙ G s₀) :=
    SGA.SGA1.ExposeV.fiberFunctor_of_iso (d s₀).symm
  have : FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s₀) ⋙ G s₀) :=
    SGA.SGA1.ExposeV.fiberFunctor_of_iso
      (Functor.isoWhiskerLeft (MorphismProperty.Over.pullback FEt ⊤ f) (d s₀)).symm
  intro σ hσ
  have hker := ker_le_range_of_completeLocal R f (G s₀)
  obtain ⟨g, hg⟩ := hker (x := (d s₀).symm.conjAut σ) (by
    rw [MonoidHom.mem_ker] at hσ ⊢
    apply Iso.ext
    refine NatTrans.ext (funext fun Z ↦ ?_)
    have h₁ := congrArg (fun τ : Aut (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F') ↦
      τ.hom.app Z) hσ
    simp only [autMap_hom_app] at h₁ ⊢
    change (d s₀).hom.app _ ≫ σ.hom.app _ ≫ (d s₀).inv.app _ = 𝟙 _
    rw [h₁]
    exact (d s₀).hom_inv_id_app _)
  refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨_, ⟨s₀, rfl⟩, g, ?_⟩)
  change (d s₀).conjAut (autMap _ (G s₀) g) = σ
  rw [hg]
  apply Iso.ext
  refine NatTrans.ext (funext fun Z ↦ ?_)
  simp [Iso.conjAut_apply]

end KernelCompleteLocal

end SGA.SGA1.ExposeIX
