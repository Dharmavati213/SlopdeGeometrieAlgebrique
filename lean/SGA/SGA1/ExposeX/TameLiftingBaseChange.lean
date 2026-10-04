/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Smooth.GeometricallyReduced
import SGA.SGA1.ExposeIX.FundamentalGroupDescent
import SGA.SGA1.ExposeX.NormalCompleteLocalBase

/-!
# SGA 1, Exposé X, 3.7: base change of étale coverings between complete local bases

In X.3.7 SGA uses that for a finite extension `V → V'` of complete discrete valuation rings with
(purely inseparable, in our generality) residue field extension, `X_{V'} ⟶ X_V` induces an
equivalence of the categories of étale coverings: both are equivalent to those of the closed
fibres (X.2.1), which differ by a universal homeomorphism (IX.4.10). We prove:

* `FEt.isEquivalence_pullback_right_of_comp`: if base change of étale coverings along `f ≫ g` and
  `f` are equivalences, so is base change along `g`;
* `isEquivalence_pullback_of_isFinite_of_universallyInjective`: IX.4.10 for étale coverings
  (`ExposeIX.essSurj_fetPullback_of_isFinite`) packaged with full faithfulness as an equivalence;
* `isEquivalence_pullback_baseChange_of_isPurelyInseparable`: for a local homomorphism `R → R'`
  of complete noetherian local rings with finite purely inseparable residue extension and `X`
  proper over `R` with geometrically connected fibres, `X` and `X_{R'}` integral and normal, base
  change along `X_{R'} ⟶ X` is an equivalence of the categories of étale coverings;
  `isEquivalence_pullback_baseChange_of_smooth`: the same for `X` smooth over complete regular
  local rings (then `X` and `X_{R'}` are regular, hence normal, and connected, hence integral:
  `isIntegral_and_isNormalScheme_of_smooth`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeX

/-- If base change of étale coverings along `f ≫ g` and along `f` are equivalences, so is base
change along `g` (`g^* ⋙ f^* ≅ (f ≫ g)^*`). This is the other cancellation property next to
`SGA.SGA1.ExposeV.FEt.isEquivalence_pullback_of_comp`, which concludes for `f`. -/
theorem FEt.isEquivalence_pullback_right_of_comp {S T R : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ R)
    [(FEt.pullback (f ≫ g)).IsEquivalence] [(FEt.pullback f).IsEquivalence] :
    (FEt.pullback g).IsEquivalence :=
  have : (FEt.pullback g ⋙ FEt.pullback f).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp f g)
  Functor.isEquivalence_of_comp_right (FEt.pullback g) (FEt.pullback f)

/-- IX.4.10 for étale coverings, packaged as an equivalence: base change along a finite,
radicial, surjective morphism of finite presentation `g : S' ⟶ S`, `S` connected, is an
equivalence of the categories of étale coverings. This only assembles the existing
`ExposeIX.full_etalePullback` (fullness), `ExposeIX.faithful_of_fiberFunctor` and
`ExposeIX.essSurj_fetPullback_of_isFinite` (IX.4.10 itself). -/
theorem isEquivalence_pullback_of_isFinite_of_universallyInjective {S S' : Scheme.{u}}
    (g : S' ⟶ S) [ConnectedSpace S] [IsFinite g] [UniversallyInjective g] [Surjective g]
    [LocallyOfFinitePresentation g] : (FEt.pullback g).IsEquivalence := by
  have hg := ExposeIX.universally_isHomeomorph_of_universallyClosed g
  have := ExposeIX.geometricallyConnected_of_universally_isHomeomorph g hg
  have hq := ExposeIX.universally_isQuotientMap_of_universally_isHomeomorph g hg
  have := ExposeIX.connectedSpace_of_universally_isQuotientMap g hq
  have : (FEt.pullback g).Full := ExposeIX.full_etalePullback g hq
  obtain ⟨x⟩ : Nonempty S' := inferInstance
  let s' := ExposeV.geometricPointAt S' x
  have : FiberFunctor (FEt.pullback g ⋙ ExposeV.FEt.fiber _ s') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso _ g s').symm
  have : (FEt.pullback g).Faithful :=
    ExposeIX.faithful_of_fiberFunctor (FEt.pullback g) (ExposeV.FEt.fiber _ s')
  have : (FEt.pullback g).EssSurj := ExposeIX.essSurj_fetPullback_of_isFinite g
  exact { }

open IsLocalRing in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison `π₁(X_{V'}) ≅ π₁(X_V)` of the paragraph before X.3.7: let `R → R'` be a local
homomorphism of complete noetherian local rings whose residue field extension `k → k'` is finite and
purely inseparable, `f : X ⟶ Spec R` proper with geometrically connected fibres, and assume `X` and
`X' = X ×_R R'` integral and normal. Then base change along `X' ⟶ X` is an equivalence of the
categories of étale coverings: both are equivalent to those of the closed fibres (X.2.1 for normal
schemes), and `X'₀ = X₀ ⊗_k k' ⟶ X₀` is a universal homeomorphism (IX.4.10). -/
theorem isEquivalence_pullback_baseChange_of_isPurelyInseparable (R R' : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing R']
    [IsLocalRing R'] [IsNoetherianRing R'] [IsAdicComplete (maximalIdeal R') R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Module.Finite (ResidueField R) (ResidueField R')]
    [IsPurelyInseparable (ResidueField R) (ResidueField R')] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [GeometricallyConnected f] [IsIntegral X]
    (hX : IsNormalScheme X)
    [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))]
    (hX' : IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))) :
    (FEt.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).IsEquivalence
    := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let f' := pullback.snd f φ
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  let ρ' := Spec.map (CommRingCat.ofHom (algebraMap R' (ResidueField R')))
  let σ := Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) (ResidueField R')))
  have hres : ρ' ≫ φ = σ ≫ ρ := by
    simp only [ρ', φ, σ, ρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  -- the closed fibres and the map `g₀ : X'₀ ⟶ X₀`
  have t : IsPullback (pullback.fst f ρ) (pullback.snd f ρ) f ρ := IsPullback.of_hasPullback f ρ
  have s : IsPullback (pullback.fst f' ρ' ≫ pullback.fst f φ) (pullback.snd f' ρ') f (σ ≫ ρ) := by
    rw [← hres]
    exact (IsPullback.of_hasPullback f' ρ').paste_horiz (IsPullback.of_hasPullback f φ)
  have sq := IsPullback.of_right' s t
  set g₀ := t.lift (pullback.fst f' ρ' ≫ pullback.fst f φ) (pullback.snd f' ρ' ≫ σ)
    (by rw [s.w, Category.assoc])
  have h : pullback.fst f' ρ' ≫ pullback.fst f φ = g₀ ≫ pullback.fst f ρ := (t.lift_fst _ _ _).symm
  -- base change along the closed fibres
  have : (FEt.pullback (pullback.fst f ρ)).IsEquivalence :=
    isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme R f hX
  have : (FEt.pullback (pullback.fst f' ρ')).IsEquivalence :=
    isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme R' f' hX'
  -- `X'₀ ⟶ X₀` is a universal homeomorphism
  have : IsFinite σ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : UniversallyInjective σ :=
    ExposeIX.universallyInjective_specMap_of_isPurelyInseparable (ResidueField R) (ResidueField R')
  have : Surjective σ := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : LocallyOfFinitePresentation σ := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    have : Algebra.FinitePresentation (ResidueField R) (ResidueField R') :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : IsFinite g₀ := MorphismProperty.of_isPullback sq.flip ‹_›
  have : UniversallyInjective g₀ := MorphismProperty.of_isPullback sq.flip ‹_›
  have : Surjective g₀ := MorphismProperty.of_isPullback sq.flip ‹_›
  have : LocallyOfFinitePresentation g₀ := MorphismProperty.of_isPullback sq.flip ‹_›
  have : ConnectedSpace ↥(pullback f ρ) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) ρ _ _ t
  have : (FEt.pullback g₀).IsEquivalence :=
    isEquivalence_pullback_of_isFinite_of_universallyInjective g₀
  have : (FEt.pullback (pullback.fst f' ρ' ≫ pullback.fst f φ)).IsEquivalence := by
    rw [h]; exact ExposeV.FEt.isEquivalence_pullback_comp g₀ (pullback.fst f ρ)
  exact FEt.isEquivalence_pullback_right_of_comp (pullback.fst f' ρ') (pullback.fst f φ)

open IsLocalRing in
/-- The comparison `π₁(X_{V'}) ≅ π₁(X_V)` of the paragraph before X.3.7, for smooth `X`: let
`R → R'` be a local homomorphism of complete regular local rings whose residue field extension is
finite and purely inseparable, and `f : X ⟶ Spec R` proper and smooth with geometrically connected
fibres. Then base change along `X_{R'} ⟶ X` is an equivalence of the categories of étale
coverings. -/
theorem isEquivalence_pullback_baseChange_of_smooth (R R' : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing R']
    [IsRegularLocalRing R'] [IsAdicComplete (maximalIdeal R') R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Module.Finite (ResidueField R) (ResidueField R')]
    [IsPurelyInseparable (ResidueField R) (ResidueField R')] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    (FEt.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).IsEquivalence
    := by
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  let f' := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap f'
      (ExposeIX.universally_isQuotientMap_of_universallyClosed f')
  obtain ⟨_, hX⟩ := isIntegral_and_isNormalScheme_of_smooth R f
  obtain ⟨_, hX'⟩ := isIntegral_and_isNormalScheme_of_smooth R' f'
  exact isEquivalence_pullback_baseChange_of_isPurelyInseparable R R' f hX hX'

end SGA.SGA1.ExposeX
