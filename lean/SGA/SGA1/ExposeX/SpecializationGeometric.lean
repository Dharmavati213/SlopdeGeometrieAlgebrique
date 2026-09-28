/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.Semicontinuity
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeIX.ExactSequenceCompleteLocal
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeV.QuotientHasQuotients

/-!
# SGA 1, Exposé X, 2.2–2.3: the exact sequence and specialization over a complete local base

Let `R` be a complete noetherian local ring and `f : X ⟶ Spec R` proper with geometrically
connected fibres. The exact sequence X.2.2 is proved in `ExposeIX.ExactSequenceCompleteLocal` for
the geometric fibre `X̄₀ = X₀ ⊗ κ̄` of IX.6.1 and arbitrary fibre functors. Here we pass to the
fundamental groups of Exposé V at arbitrary geometric points `b : Spec Ω ⟶ Spec R` with `Ω`
algebraically closed: `X ×_R Ω = X̄₀ ⊗_κ̄ Ω` and base change along `Ω/κ̄` is an equivalence on étale
coverings (X.1.8), so the criteria V.6.8 and V.6.11 (which only involve the categories of étale
coverings) transfer from `X̄₀` to `X ×_R Ω`.

* `exists_isEquivalence_geometricPoint`, `exists_isEquivalence_geometricFiberι`: `X ×_S Ω ⟶ X`
  factors through `X ×_S κ(s)ᵃˡᵍ ⟶ X` (and through `X̄_s ⟶ X`) by a morphism along which base change
  of étale coverings is an equivalence (X.1.8);
* `injective_map_closedFibre_of_completeLocal`, `range_map_eq_ker_map_closedFibre_of_completeLocal`:
  X.2.2 for the fundamental groups of Exposé V (the injectivity given the lifting of étale
  coverings from the closed fibre, IX.1.10; the exactness unconditionally);
* `ker_map_le_range_map_geometricPointOf`: X.1.4 at geometric points with arbitrary algebraically
  closed values;
* `exists_continuous_surjective_specialization_of_completeLocal`: X.2.3 over a complete local base,
  the specialization homomorphism being obtained from X.2.2, X.1.4 and a class of paths
  (`SpecializationDiagram`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory IsLocalRing

namespace SGA.SGA1.ExposeX

section Transfer

variable {X X₀ X₁ : Scheme.{u}} (ι₀ : X₀ ⟶ X) (m : X₁ ⟶ X₀)
  [(FEt.pullback m).IsEquivalence]

/-- If every étale covering of `X₀` embeds into the inverse image of an étale covering of `X`, the
same holds over `X₁` when base change along `m : X₁ ⟶ X₀` is an equivalence. -/
lemma exists_mono_pullback_comp_of_isEquivalence
    (h : ∀ Y : FEt X₀, ∃ (Z : FEt X) (i : Y ⟶ (FEt.pullback ι₀).obj Z), Mono i) (Y : FEt X₁) :
    ∃ (Z : FEt X) (i : Y ⟶ (FEt.pullback (m ≫ ι₀)).obj Z), Mono i := by
  obtain ⟨Z, i, hi⟩ := h ((FEt.pullback m).objPreimage Y)
  exact ⟨Z, ((FEt.pullback m).objObjPreimageIso Y).inv ≫ (FEt.pullback m).map i ≫
    (MorphismProperty.Over.pullbackComp m ι₀).inv.app Z, inferInstance⟩

/-- Sections over `X₁` of inverse images of étale coverings of `X` come from sections over `X₀`
when base change along `m : X₁ ⟶ X₀` is an equivalence. -/
lemma nonempty_section_of_isEquivalence (Z : FEt X)
    (h : Nonempty (⊤_ (FEt X₁) ⟶ (FEt.pullback (m ≫ ι₀)).obj Z)) :
    Nonempty (⊤_ (FEt X₀) ⟶ (FEt.pullback ι₀).obj Z) := by
  obtain ⟨t⟩ := h
  exact ⟨(FEt.pullback m).preimage (terminal.from _ ≫ t ≫
    (MorphismProperty.Over.pullbackComp m ι₀).hom.app Z)⟩

end Transfer

section GeometricFibre

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The geometric point `Spec Ω ⟶ Spec κ(s)ᵃˡᵍ ⟶ S` at `s` defined by an embedding
`κ(s)ᵃˡᵍ → Ω`. Every geometric point with algebraically closed values is of this form
(`ExposeXIII.exists_eq_comp_geometricPoint`). -/
noncomputable abbrev geometricPointOf (s : S) (Ω : Type u) [Field Ω]
    [Algebra (AlgebraicClosure (S.residueField s)) Ω] : Spec (.of Ω) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (S.residueField s)) Ω)) ≫
    geometricPoint S s

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8 for the geometric fibres: for `f` proper with geometrically connected fibres and a
geometric point `b : Spec Ω ⟶ Spec κ(s)ᵃˡᵍ ⟶ S`, the projection `X ×_S Ω ⟶ X` factors through
`X ×_S κ(s)ᵃˡᵍ ⟶ X` by a morphism along which base change of étale coverings is an equivalence
(`X ×_S Ω ≅ (X ×_S κ(s)ᵃˡᵍ) ⊗ Ω`). -/
theorem exists_isEquivalence_geometricPoint [IsProper f] [GeometricallyConnected f] (s : S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (AlgebraicClosure (S.residueField s)) Ω] :
    ∃ m : pullback f (geometricPointOf s Ω) ⟶ pullback f (geometricPoint S s),
      (FEt.pullback m).IsEquivalence ∧
        pullback.fst f (geometricPointOf s Ω) = m ≫ pullback.fst f (geometricPoint S s) := by
  set yb := geometricPoint S s
  set σ := Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (S.residueField s)) Ω))
  have : ConnectedSpace ↥(pullback f yb) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) yb _ _
      (IsPullback.of_hasPullback f yb)
  have := baseChangeAlgClosedStatement (AlgebraicClosure (S.residueField s)) Ω
    (pullback.snd f yb)
  let e := pullbackLeftPullbackSndIso f yb σ
  refine ⟨e.inv ≫ pullback.fst (pullback.snd f yb) σ,
    ExposeV.FEt.isEquivalence_pullback_comp _ _, ?_⟩
  change pullback.fst f (σ ≫ yb) = _
  simp [e]

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8 for the geometric fibres, with the geometric fibre `X̄_s = X_s ⊗ κ(s)ᵃˡᵍ` of IX.6.1:
the projection `X ×_S Ω ⟶ X` factors through `X̄_s ⟶ X` by a morphism along which base change of
étale coverings is an equivalence. -/
theorem exists_isEquivalence_geometricFiberι [IsProper f] [GeometricallyConnected f] (s : S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra (AlgebraicClosure (S.residueField s)) Ω] :
    ∃ m : pullback f (geometricPointOf s Ω) ⟶ ExposeIX.geometricFiber f s,
      (FEt.pullback m).IsEquivalence ∧
        pullback.fst f (geometricPointOf s Ω) = m ≫ ExposeIX.geometricFiberι f s := by
  obtain ⟨m₁, hm₁, hfac₁⟩ := exists_isEquivalence_geometricPoint f s Ω
  let e' : ExposeIX.geometricFiber f s ≅ pullback f (geometricPoint S s) :=
    pullbackLeftPullbackSndIso f (S.fromSpecResidueField s)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
        (AlgebraicClosure (S.residueField s)))))
  have he' : e'.hom ≫ pullback.fst f (geometricPoint S s) = ExposeIX.geometricFiberι f s :=
    pullbackLeftPullbackSndIso_hom_fst _ _ _
  clear_value e'
  refine ⟨m₁ ≫ e'.inv, ExposeV.FEt.isEquivalence_pullback_comp _ _, hfac₁.trans ?_⟩
  rw [Category.assoc, ← he', Iso.inv_hom_id_assoc]

end GeometricFibre

/-- The spectrum of a local ring is connected. -/
instance connectedSpace_primeSpectrum_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) := by
  refine (ExposeV.connectedSpace_primeSpectrum_iff R).mpr ⟨inferInstance, fun e he ↦ ?_⟩
  have h₀ : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (sub_eq_zero.mp (h.mul_right_eq_zero.mp h₀)).symm
  · exact Or.inl (h.mul_left_eq_zero.mp h₀)

/-- The spectrum of a local ring is connected. -/
instance connectedSpace_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (Spec (.of R)) :=
  inferInstanceAs (ConnectedSpace (PrimeSpectrum R))

/-- The closed point of `Spec R`, `R` local, as a point of the scheme `Spec R`. -/
noncomputable abbrev closedPt (R : Type u) [CommRing R] [IsLocalRing R] : Spec (.of R) :=
  closedPoint R

section ClosedFibre

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
  [GeometricallyConnected f] (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
  [Algebra (AlgebraicClosure ((Spec (.of R)).residueField (closedPt R))) Ω₀]

/-- A geometric point `Spec Ω₀ ⟶ Spec R` at the closed point, `Ω₀` algebraically closed. -/
noncomputable abbrev closedGeometricPoint : Spec (.of Ω₀) ⟶ Spec (.of R) :=
  geometricPointOf (closedPt R) Ω₀

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
set_option backward.isDefEq.respectTransparency false in
/-- **X.2.2, injectivity** (for the fundamental groups of Exposé V at a geometric point
`b : Spec Ω₀ ⟶ Spec R` over the closed point, `Ω₀` algebraically closed): let `R` be a complete
noetherian local ring and `f : X ⟶ Spec R` proper with geometrically connected fibres, such that
the étale coverings of the closed fibre lift to `X` (IX.1.10). Then `π₁(X_b, a) → π₁(X, a)` is
injective. -/
theorem injective_map_closedFibre_of_completeLocal
    (hlift : ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint R))) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (closedGeometricPoint R Ω₀)) :
    Function.Injective (ExposeV.etaleFundamentalGroup.map Ω
      (pullback.fst f (closedGeometricPoint R Ω₀)) a) := by
  obtain ⟨m, hm, hfac⟩ := exists_isEquivalence_geometricFiberι f (closedPt R) Ω₀
  have : ConnectedSpace ↥(pullback f (closedGeometricPoint R Ω₀)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (closedGeometricPoint R Ω₀) _ _
      (IsPullback.of_hasPullback f _)
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : IsProper (f.fiberToSpecResidueField (closedPoint R)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiSeparatedSpace (f.fiber (closedPoint R)) :=
    quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField (closedPoint R))
  have : PreGaloisCategory.FiberFunctor
      (FEt.pullback (pullback.fst f (closedGeometricPoint R Ω₀)) ⋙ ExposeV.FEt.fiber Ω a) :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω _ a).symm
  rw [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom]
  refine (MulEquiv.injective _).comp ?_
  refine (ExposeV.injective_autWhiskerLeft_iff
    (FEt.pullback (pullback.fst f (closedGeometricPoint R Ω₀))) (ExposeV.FEt.fiber Ω a)).mpr
    fun Y hY ↦ ?_
  obtain ⟨Z, i, hi⟩ := exists_mono_pullback_comp_of_isEquivalence
    (ExposeIX.geometricFiberι f (closedPoint R)) m
    (ExposeIX.exists_mono_pullback_geometricFiberι_of_lift f _ hlift) Y
  rw [hfac]
  exact ⟨Z, Y, i, 𝟙 Y, hY, hi⟩

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [IsProper f]
  [GeometricallyConnected f] in
/-- `π₁(X_b, a) → π₁(X, a) → π₁(Spec R, a)` is trivial. -/
theorem map_comp_map_closedFibre_eq_one (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f (closedGeometricPoint R Ω₀)) :
    (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (closedGeometricPoint R Ω₀))).comp
      (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (closedGeometricPoint R Ω₀)) a) = 1 :=
  ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω _ f (pullback.snd _ _) _
    pullback.condition a (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω Ω₀ _)

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [IsProper f]
  [GeometricallyConnected f] in
/-- `autHom` along the identity isomorphism is `autMap`. -/
lemma autHom_refl {C C' : Type*} [Category C] [Category C'] (H : C ⥤ C')
    (F : C' ⥤ FintypeCat.{u}) :
    ExposeXIII.autHom H (Iso.refl (H ⋙ F)) = ExposeIX.autMap H F := by
  ext σ : 1
  apply Iso.ext
  refine NatTrans.ext (funext fun Y ↦ ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The geometric form of the inclusion `ker ⊆ im` of X.2.2 (V.6.11): a connected étale covering of
`X` which has a section over the geometric closed fibre `X̄₀` embeds into the inverse image of an
étale covering of `Spec R`. This only uses the full faithfulness in IX.1.10. -/
theorem exists_mono_pullback_of_section_geometricFiber (X' : FEt X)
    [PreGaloisCategory.IsConnected X']
    (hs : Nonempty (⊤_ (FEt (ExposeIX.geometricFiber f (closedPt R))) ⟶
      (FEt.pullback (ExposeIX.geometricFiberι f (closedPt R))).obj X')) :
    ∃ (W : FEt (Spec (.of R))) (i : X' ⟶ (FEt.pullback f).obj W), Mono i := by
  set ι₀ := ExposeIX.geometricFiberι f (closedPt R)
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : GeometricallyConnected (f.fiberToSpecResidueField (closedPt R)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : ConnectedSpace ↥(ExposeIX.geometricFiber f (closedPt R)) :=
    GeometricallyConnected.geometrically_connectedSpace
      (f := f.fiberToSpecResidueField (closedPt R)) _ _ _ (IsPullback.of_hasPullback _ _)
  obtain ⟨x⟩ : Nonempty ↥(ExposeIX.geometricFiber f (closedPt R)) := inferInstance
  let K := AlgebraicClosure ((ExposeIX.geometricFiber f (closedPt R)).residueField x)
  let a₀ : Spec (.of K) ⟶ ExposeIX.geometricFiber f (closedPt R) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((ExposeIX.geometricFiber f (closedPt R)).residueField x) K)) ≫
      (ExposeIX.geometricFiber f (closedPt R)).fromSpecResidueField x
  let F'' := ExposeV.FEt.fiber K a₀
  let e₁ := ExposeV.FEt.pullbackFiberIso K ι₀ a₀
  have : PreGaloisCategory.FiberFunctor (FEt.pullback ι₀ ⋙ F'') :=
    ExposeV.fiberFunctor_of_iso e₁.symm
  have : PreGaloisCategory.FiberFunctor (FEt.pullback f ⋙ FEt.pullback ι₀ ⋙ F'') :=
    ExposeV.fiberFunctor_of_iso (Functor.isoWhiskerLeft (FEt.pullback f) e₁ ≪≫
      ExposeV.FEt.pullbackFiberIso K f (a₀ ≫ ι₀)).symm
  have hIX := ExposeIX.ker_le_range_of_completeLocal R f F''
  rw [← autHom_refl, ← autHom_refl] at hIX
  exact (ExposeXIII.ker_autHom_le_range_iff (FEt.pullback f)
    (Iso.refl (FEt.pullback f ⋙ FEt.pullback ι₀ ⋙ F'')) (FEt.pullback ι₀)
    (Iso.refl (FEt.pullback ι₀ ⋙ F''))).mp hIX X' inferInstance hs

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.2, exactness at `π₁(X)`** (for the fundamental groups of Exposé V at a geometric point
`b : Spec Ω₀ ⟶ Spec R` over the closed point, `Ω₀` algebraically closed): for `R` complete
noetherian local and `f : X ⟶ Spec R` proper with geometrically connected fibres, the image of
`π₁(X_b, a) → π₁(X, a)` is the kernel of `π₁(X, a) → π₁(Spec R, a)`. This uses only the full
faithfulness in IX.1.10. -/
theorem range_map_eq_ker_map_closedFibre_of_completeLocal (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f (closedGeometricPoint R Ω₀)) :
    (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (closedGeometricPoint R Ω₀)) a).range =
      (ExposeV.etaleFundamentalGroup.map Ω f
        (a ≫ pullback.fst f (closedGeometricPoint R Ω₀))).ker := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, map_comp_map_closedFibre_eq_one]
    rfl
  obtain ⟨m, hm, hfac⟩ := exists_isEquivalence_geometricFiberι f (closedPt R) Ω₀
  have : ConnectedSpace ↥(pullback f (closedGeometricPoint R Ω₀)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (closedGeometricPoint R Ω₀) _ _
      (IsPullback.of_hasPullback f _)
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  refine (ExposeXIII.ker_autHom_le_range_iff (FEt.pullback f)
    (ExposeV.FEt.pullbackFiberIso Ω f (a ≫ pullback.fst f (closedGeometricPoint R Ω₀)))
    (FEt.pullback (pullback.fst f (closedGeometricPoint R Ω₀)))
    (ExposeV.FEt.pullbackFiberIso Ω _ a)).mpr fun X' hX' hs ↦ ?_
  rw [hfac] at hs
  exact exists_mono_pullback_of_section_geometricFiber R f X'
    (nonempty_section_of_isEquivalence _ m X' hs)

end ClosedFibre

section HomotopySequence

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
  [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U))

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- X.1.4 at a geometric point `b : Spec Ω₁ ⟶ Spec κ(y)ᵃˡᵍ ⟶ Y` with `Ω₁` algebraically closed
(X.1.4 is proved at `Spec κ(y)ᵃˡᵍ`; the passage to `Ω₁` is X.1.8): the kernel of
`π₁(X, a) → π₁(Y, a)` is contained in the image of `π₁(X_b, a) → π₁(X, a)`. -/
theorem ker_map_le_range_map_geometricPointOf (y : Y) (Ω₁ : Type u) [Field Ω₁] [IsAlgClosed Ω₁]
    [Algebra (AlgebraicClosure (Y.residueField y)) Ω₁] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f (geometricPointOf y Ω₁)) :
    (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPointOf y Ω₁))).ker ≤
      (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPointOf y Ω₁)) a).range := by
  have : GeometricallyConnected f := CohomologyAux.geometricallyConnected_of_isIso_app f hf
  obtain ⟨m, hm, hfac⟩ := exists_isEquivalence_geometricPoint f y Ω₁
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : ConnectedSpace ↥(pullback f (geometricPointOf y Ω₁)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (geometricPointOf y Ω₁) _ _
      (IsPullback.of_hasPullback f _)
  have : ConnectedSpace ↥(pullback f (geometricPoint Y y)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (geometricPoint Y y) _ _
      (IsPullback.of_hasPullback f _)
  -- X.1.4 at `Spec κ(y)ᵃˡᵍ`, in the form V.6.11
  have key : ∀ X' : FEt X, PreGaloisCategory.IsConnected X' →
      Nonempty (⊤_ (FEt (pullback f (geometricPoint Y y))) ⟶
        (FEt.pullback (pullback.fst f (geometricPoint Y y))).obj X') →
      ∃ (W : FEt Y) (i : X' ⟶ (FEt.pullback f).obj W), Mono i := by
    obtain ⟨x⟩ : Nonempty ↥(pullback f (geometricPoint Y y)) := inferInstance
    let K := AlgebraicClosure ((pullback f (geometricPoint Y y)).residueField x)
    let a' : Spec (.of K) ⟶ pullback f (geometricPoint Y y) :=
      Spec.map (CommRingCat.ofHom
        (algebraMap ((pullback f (geometricPoint Y y)).residueField x) K)) ≫
        (pullback f (geometricPoint Y y)).fromSpecResidueField x
    have h14 := (range_map_eq_ker_map_and_surjective f hf y K a').1
    exact (ExposeXIII.ker_autHom_le_range_iff (FEt.pullback f)
      (ExposeV.FEt.pullbackFiberIso K f (a' ≫ pullback.fst f (geometricPoint Y y)))
      (FEt.pullback (pullback.fst f (geometricPoint Y y)))
      (ExposeV.FEt.pullbackFiberIso K _ a')).mp h14.symm.le
  refine (ExposeXIII.ker_autHom_le_range_iff (FEt.pullback f)
    (ExposeV.FEt.pullbackFiberIso Ω f (a ≫ pullback.fst f (geometricPointOf y Ω₁)))
    (FEt.pullback (pullback.fst f (geometricPointOf y Ω₁)))
    (ExposeV.FEt.pullbackFiberIso Ω _ a)).mpr fun X' hX' hs ↦ ?_
  rw [hfac] at hs
  exact key X' hX' (nonempty_section_of_isEquivalence _ m X' hs)

end HomotopySequence

section Specialization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
  [IsSeparable f]

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.3** (over a complete local base, for the fundamental groups of Exposé V). Let `R` be a
complete noetherian local ring, `f : X ⟶ Spec R` proper and separable with `f_* 𝒪_X = 𝒪_{Spec R}`
(X.1.2: equivalently, geometrically connected fibres), such that the étale coverings of the closed
fibre lift to `X` (IX.1.10). Let `b₀` be a geometric point at the closed point and `b₁` one at an
arbitrary point `y₁`, with algebraically closed values, and `a₀`, `a₁` geometric points of the
geometric fibres `X_{b₀}`, `X_{b₁}`. Then there is a continuous surjective homomorphism
`π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)`: the specialization homomorphism, obtained from the exact
sequences X.2.2 (at `b₀`) and X.1.4 (at `b₁`) and a class of paths from `a₁` to `a₀` in `X`. -/
theorem exists_continuous_surjective_specialization_of_completeLocal
    (hf : ∀ U : (Spec (.of R)).Opens, IsIso (f.app U))
    (hlift : ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint R)))
    (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    [Algebra (AlgebraicClosure ((Spec (.of R)).residueField (closedPt R))) Ω₀]
    (y₁ : Spec (.of R)) (Ω₁ : Type u) [Field Ω₁] [IsAlgClosed Ω₁]
    [Algebra (AlgebraicClosure ((Spec (.of R)).residueField y₁)) Ω₁]
    (Ω₀' Ω₁' : Type u) [Field Ω₀'] [IsSepClosed Ω₀'] [Field Ω₁'] [IsSepClosed Ω₁']
    (a₀ : Spec (.of Ω₀') ⟶ pullback f (closedGeometricPoint R Ω₀))
    (a₁ : Spec (.of Ω₁') ⟶ pullback f (geometricPointOf y₁ Ω₁)) :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁' a₁ →* ExposeV.etaleFundamentalGroup Ω₀' a₀,
      Continuous sp ∧ Function.Surjective sp := by
  have : GeometricallyConnected f := CohomologyAux.geometricallyConnected_of_isIso_app f hf
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : ConnectedSpace ↥(pullback f (closedGeometricPoint R Ω₀)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (closedGeometricPoint R Ω₀) _ _
      (IsPullback.of_hasPullback f _)
  have : ConnectedSpace ↥(pullback f (geometricPointOf y₁ Ω₁)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (geometricPointOf y₁ Ω₁) _ _
      (IsPullback.of_hasPullback f _)
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor
    (ExposeV.FEt.fiber Ω₁' (a₁ ≫ pullback.fst f (geometricPointOf y₁ Ω₁)))
    (ExposeV.FEt.fiber Ω₀' (a₀ ≫ pullback.fst f (closedGeometricPoint R Ω₀)))
  let ψ := (ExposeV.FEt.pullbackFiberIso Ω₁' f
      (a₁ ≫ pullback.fst f (geometricPointOf y₁ Ω₁))).symm ≪≫
    Functor.isoWhiskerLeft (FEt.pullback f) φ ≪≫
      ExposeV.FEt.pullbackFiberIso Ω₀' f (a₀ ≫ pullback.fst f (closedGeometricPoint R Ω₀))
  have hD : SpecializationDiagram
      (ExposeV.etaleFundamentalGroup.map Ω₀' (pullback.fst f (closedGeometricPoint R Ω₀)) a₀)
      (ExposeV.etaleFundamentalGroup.map Ω₀' f (a₀ ≫ pullback.fst f (closedGeometricPoint R Ω₀)))
      (ExposeV.etaleFundamentalGroup.map Ω₁' (pullback.fst f (geometricPointOf y₁ Ω₁)) a₁)
      (ExposeV.etaleFundamentalGroup.map Ω₁' f (a₁ ≫ pullback.fst f (geometricPointOf y₁ Ω₁)))
      φ.conjAut.toMonoidHom ψ.conjAut.toMonoidHom :=
    { injective_i₀ := injective_map_closedFibre_of_completeLocal R f Ω₀ hlift Ω₀' a₀
      range_i₀ := range_map_eq_ker_map_closedFibre_of_completeLocal R f Ω₀ Ω₀' a₀
      comm := by
        ext σ : 1
        apply Iso.ext
        refine NatTrans.ext (funext fun W ↦ ?_)
        simp [ψ, ExposeV.etaleFundamentalGroup.map, ExposeV.autMap_hom_app, Iso.conjAut_apply]
      comp_eq_one := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω₁' _ f
        (pullback.snd _ _) _ pullback.condition a₁
        (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω₁' Ω₁ _) }
  refine ⟨hD.specializationHom, ?_, hD.specializationHom_surjective φ.conjAut.surjective
    ψ.conjAut.injective (ker_map_le_range_map_geometricPointOf f hf y₁ Ω₁ Ω₁' a₁)⟩
  exact hD.continuous_specializationHom
    ((ExposeV.etaleFundamentalGroup.continuous_map _ _ _).isClosedEmbedding
      hD.injective_i₀).isEmbedding
    (ExposeV.etaleFundamentalGroup.continuous_map _ _ _) (ExposeV.continuous_conjAut φ)

end Specialization

end SGA.SGA1.ExposeX
