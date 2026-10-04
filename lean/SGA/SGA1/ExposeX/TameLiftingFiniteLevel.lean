/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.ExactSequence
import SGA.SGA1.ExposeV.FundamentalGroupLimit
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeX.TameLiftingBaseChange
import SGA.SGA1.ExposeX.TameLiftingDescent
import SGA.SGA1.ExposeX.TameLiftingGalois

/-!
# SGA 1, Exposé X, 3.8: a Galois covering of `X_Ω` is defined over a finite separable extension

In the proof of X.3.8 (before X.3.7), a principal covering of the geometric generic fibre with
group `G` is the inverse image of a principal covering with group `G` of `X_{K'}`, for some finite
separable extension `K'` of `K`. We prove this for `f : X ⟶ Spec R` proper and smooth with
geometrically connected fibres, `K` any field over `R` and `Ω` any algebraically closed field over
`K` (`exists_isGalois_finiteDimensional_of_isGalois`):

* X.1.8 (`baseChangeAlgClosedStatement`) replaces `Ω` by an algebraic closure `K̄ ⊆ Ω` of `K`;
* the limit theorem for étale coverings, with the automorphisms
  (`exists_liftsEndos_of_isLimit`, over the finite subextensions `L` of `K̄/K`), descends the
  covering to some `X_L`;
* IX.4.10 (`isEquivalence_pullback_of_isFinite_of_universallyInjective`) descends it along the
  radicial `X_L ⟶ X_{K₀}`, `K₀` the separable closure of `K` in `L` (as in
  `SGA.SGA1.ExposeIX.exists_mono_pullback_geometricFiberι_of_lift`);
* the descended covering is Galois with the same group (`isGalois_of_liftsEndos`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeX

variable (R : Type u) [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The morphism `X ×_R Ω ⟶ X ×_R K₀` induced by an `R`-algebra map `K₀ → Ω`. -/
noncomputable def pullbackMapOfIsScalarTower (K₀ Ω : Type u) [CommRing K₀] [CommRing Ω]
    [Algebra R K₀] [Algebra R Ω] [Algebra K₀ Ω] [IsScalarTower R K₀ Ω] :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

@[reassoc (attr := simp)]
lemma pullbackMapOfIsScalarTower_fst (K₀ Ω : Type u) [CommRing K₀] [CommRing Ω]
    [Algebra R K₀] [Algebra R Ω] [Algebra K₀ Ω] [IsScalarTower R K₀ Ω] :
    pullbackMapOfIsScalarTower R f K₀ Ω ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [pullbackMapOfIsScalarTower, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma pullbackMapOfIsScalarTower_snd (K₀ Ω : Type u) [CommRing K₀] [CommRing Ω]
    [Algebra R K₀] [Algebra R Ω] [Algebra K₀ Ω] [IsScalarTower R K₀ Ω] :
    pullbackMapOfIsScalarTower R f K₀ Ω ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K₀ Ω)) := by
  rw [pullbackMapOfIsScalarTower, pullback.map, pullback.lift_snd]

variable (K : Type u) [Field K] [Algebra R K] [IsProper f] [Smooth f] [GeometricallyConnected f]
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

set_option backward.isDefEq.respectTransparency false in
/-- A step of the proof of X.3.8 (before X.3.7; the core statement is `TameLiftingDVRStatement`):
let `f : X ⟶ Spec R` be proper and smooth with geometrically connected fibres, `K` a field over
`R` and `Ω` an algebraically closed field over `K`. Every Galois étale covering `Z` of
`X_Ω = X ×_R Ω` is the inverse image, along `X_Ω ⟶ X_{K₀} = X ×_R K₀`, of a Galois étale covering
`Y₀` of `X_{K₀}` with as many automorphisms, for some finite separable extension `K₀` of `K` and
some `R`-embedding `K₀ → Ω`. (X.1.8 for `Ω` over an algebraic closure of `K`, the limit theorem
for étale coverings and their endomorphisms, and IX.4.10 for the radicial part.) -/
theorem exists_isGalois_finiteDimensional_of_isGalois
    (Z : FEt (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) [IsGalois Z] :
    ∃ (K₀ : Type u) (_ : Field K₀) (_ : Algebra K K₀) (_ : Algebra R K₀) (_ : Algebra K₀ Ω)
      (_ : IsScalarTower R K K₀) (_ : IsScalarTower R K₀ Ω) (_ : FiniteDimensional K K₀)
      (_ : Algebra.IsSeparable K K₀)
      (Y₀ : FEt (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀))))),
      IsGalois Y₀ ∧ Nat.card (Aut Y₀) = Nat.card (Aut Z) ∧
        Nonempty ((FEt.pullback (pullbackMapOfIsScalarTower R f K₀ Ω)).obj Y₀ ≅ Z) := by
  classical
  let s := Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  let σK : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let h : pullback f σK ⟶ Spec (.of K) := pullback.snd f σK
  have : IsProper h := MorphismProperty.pullback_snd _ _ inferInstance
  have : Smooth h := MorphismProperty.pullback_snd _ _ inferInstance
  have : GeometricallyConnected h := MorphismProperty.pullback_snd _ _ inferInstance
  have : CompactSpace ↥(pullback f σK) := QuasiCompact.compactSpace_of_compactSpace h
  have : QuasiSeparatedSpace ↥(pullback f σK) := quasiSeparatedSpace_of_quasiSeparated h
  -- an algebraic closure `Kb` of `K` inside `Ω`
  let Kb := AlgebraicClosure K
  let ι : Kb →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra Kb Ω := ι.toRingHom.toAlgebra
  have : IsScalarTower K Kb Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  let tKb : Spec (.of Kb) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  let tΩ : Spec (.of Ω) ⟶ Spec (.of Kb) := Spec.map (CommRingCat.ofHom (algebraMap Kb Ω))
  have hs : s = tΩ ≫ tKb ≫ σK := by
    simp only [s, tΩ, tKb, σK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply K Kb Ω, ← IsScalarTower.algebraMap_apply R K Ω]
  let hb : pullback h tKb ⟶ Spec (.of Kb) := pullback.snd h tKb
  have : IsProper hb := MorphismProperty.pullback_snd _ _ inferInstance
  -- X.1.8: `m : X_Ω ⟶ X_{Kb}`
  let m₁ : pullback f s ⟶ pullback f σK :=
    pullback.lift (pullback.fst f s) (pullback.snd f s ≫ tΩ ≫ tKb)
      ((pullback.condition).trans ((congrArg (pullback.snd f s ≫ ·) hs).trans
        (by simp only [Category.assoc])))
  let m : pullback f s ⟶ pullback h tKb :=
    pullback.lift m₁ (pullback.snd f s ≫ tΩ) (by simp [m₁, h])
  have hm₁ : m ≫ pullback.fst h tKb = m₁ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd h tKb = pullback.snd f s ≫ tΩ := pullback.lift_snd _ _ _
  have hm : IsPullback m (pullback.snd f s) hb tΩ := by
    have t : IsPullback (pullback.fst h tKb ≫ pullback.fst f σK) hb f (tKb ≫ σK) :=
      (IsPullback.of_hasPullback h tKb).paste_horiz (IsPullback.of_hasPullback f σK)
    have o : IsPullback (m ≫ pullback.fst h tKb ≫ pullback.fst f σK) (pullback.snd f s) f
        (tΩ ≫ tKb ≫ σK) := by
      have : m ≫ pullback.fst h tKb ≫ pullback.fst f σK = pullback.fst f s := by
        rw [reassoc_of% hm₁]
        exact pullback.lift_fst _ _ _
      rw [this, ← hs]
      exact IsPullback.of_hasPullback f s
    exact IsPullback.of_right o hm₂ t
  have : (FEt.pullback (pullback.fst hb tΩ)).IsEquivalence :=
    baseChangeAlgClosedStatement Kb Ω hb
  have : (FEt.pullback m).IsEquivalence := by
    have hmeq : m = hm.isoPullback.hom ≫ pullback.fst hb tΩ := hm.isoPullback_hom_fst.symm
    rw [hmeq]
    exact ExposeV.FEt.isEquivalence_pullback_comp _ _
  -- fibre functors
  obtain ⟨x⟩ : Nonempty ↥(pullback f s) := inferInstance
  let a := ExposeV.geometricPointAt (pullback f s) x
  let Ω' := AlgebraicClosure ((pullback f s).residueField x)
  let F' := ExposeV.FEt.fiber Ω' a
  -- `Z` comes from a connected covering `Zb` of `X_{Kb}`
  let Zb := (FEt.pullback m).objPreimage Z
  let iZ : (FEt.pullback m).obj Zb ≅ Z := (FEt.pullback m).objObjPreimageIso Z
  have : IsConnected ((FEt.pullback m).obj Zb) := ExposeV.isConnected_of_iso iZ.symm
  have : IsConnected Zb :=
    isConnected_of_isConnected_obj (FEt.pullback m) (ExposeV.FEt.pullbackFiberIso Ω' m a) Zb
  have : Finite (Zb ⟶ Zb) := by
    obtain ⟨z⟩ := nonempty_fiber_of_isConnected (ExposeV.FEt.fiber Ω' (a ≫ m)) Zb
    exact Finite.of_injective _
      (evaluation_injective_of_isConnected (ExposeV.FEt.fiber Ω' (a ≫ m)) Zb Zb z)
  -- the limit over the finite subextensions of `Kb / K`
  obtain ⟨j, Yj, ⟨iY⟩, hlift⟩ :=
    exists_liftsEndos_of_isLimit (ExposeV.isLimitBaseChangeCone (E := Kb) h) Zb
  let c := ExposeV.baseChangeCone (E := Kb) h
  -- the separable closure `K₀` of `K` in `L` and the radicial `g : X_L ⟶ X_{K₀}` (IX.4.10)
  let L : ExposeV.FiniteSubext K Kb := j.unop
  have := L.2
  let K₀ := separableClosure K L.1
  have : Algebra.IsSeparable K K₀ := separableClosure.isSeparable K L.1
  have : IsPurelyInseparable K₀ L.1 := separableClosure.isPurelyInseparable K L.1
  have : FiniteDimensional K K₀ := inferInstance
  have : Module.Finite K₀ L.1 := Module.Finite.right K K₀ L.1
  let ιL := ExposeV.specFiniteSubextι K Kb L
  let ιK : Spec (.of K₀) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K₀))
  let ρ : Spec (.of L.1) ⟶ Spec (.of K₀) := Spec.map (CommRingCat.ofHom (algebraMap K₀ L.1))
  have hρ : ρ ≫ ιK = ιL := by
    rw [← Spec.map_comp]
    rfl
  let g : pullback h ιL ⟶ pullback h ιK :=
    pullback.map h ιL h ιK (𝟙 _) ρ (𝟙 _) (by simp) (by simp [hρ])
  have hg : IsPullback g (pullback.snd h ιL) (pullback.snd h ιK) ρ :=
    ExposeV.isPullback_pullbackMap h ιL ιK ρ hρ
  have : IsFinite ρ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : UniversallyInjective ρ :=
    ExposeIX.universallyInjective_specMap_of_isPurelyInseparable K₀ L.1
  have : Surjective ρ := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : LocallyOfFinitePresentation ρ := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    have : Algebra.FinitePresentation K₀ L.1 :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : IsFinite g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : UniversallyInjective g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : Surjective g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : LocallyOfFinitePresentation g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : (FEt.pullback g).IsEquivalence :=
    isEquivalence_pullback_of_isFinite_of_universallyInjective g
  let Y₁ := (FEt.pullback g).objPreimage Yj
  let iY₁ : (FEt.pullback g).obj Y₁ ≅ Yj := (FEt.pullback g).objObjPreimageIso Yj
  -- the embedding `K₀ → Ω`
  let φ : K₀ →+* Ω := (algebraMap Kb Ω).comp ((algebraMap L.1 Kb).comp (algebraMap K₀ L.1))
  let : Algebra K₀ Ω := φ.toAlgebra
  have : IsScalarTower R K₀ Ω := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Ω r =
      algebraMap Kb Ω (algebraMap L.1 Kb (algebraMap K₀ L.1 (algebraMap R K₀ r)))
    rw [IsScalarTower.algebraMap_apply R K K₀, ← IsScalarTower.algebraMap_apply K K₀ L.1,
      ← IsScalarTower.algebraMap_apply K L.1 Kb, ← IsScalarTower.algebraMap_apply K Kb Ω,
      ← IsScalarTower.algebraMap_apply R K Ω]
  -- `X_{K₀}` as `X ×_R K₀`
  let tK₀ : Spec (.of K₀) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K₀))
  have htK₀ : ιK ≫ σK = tK₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have sq₀ : IsPullback (pullback.fst h ιK ≫ pullback.fst f σK) (pullback.snd h ιK) f tK₀ := by
    rw [← htK₀]
    exact (IsPullback.of_hasPullback h ιK).paste_horiz (IsPullback.of_hasPullback f σK)
  let w : pullback f tK₀ ⟶ pullback h ιK := sq₀.isoPullback.inv
  let Y₀ : FEt (pullback f tK₀) := (FEt.pullback w).obj Y₁
  let α := pullbackMapOfIsScalarTower R f K₀ Ω
  have hα : α ≫ w = m ≫ c.π.app j ≫ g := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [pullbackMapOfIsScalarTower_fst, Category.assoc, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst]
      simp only [g, c, pullback.map, pullback.lift_fst_assoc, Category.comp_id,
        ExposeV.baseChangeConeπ]
      erw [pullback.lift_fst_assoc]
      rw [reassoc_of% hm₁]
      exact (pullback.lift_fst _ _ _).symm
    · rw [pullbackMapOfIsScalarTower_snd, Category.assoc, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_snd]
      simp only [g, c, pullback.map, pullback.lift_snd, ExposeV.baseChangeConeπ]
      erw [pullback.lift_snd_assoc]
      rw [Category.assoc, reassoc_of% hm₂]
      simp only [tΩ, ρ, ← Spec.map_comp]
      rfl
  -- every endomorphism of `α^* Y₀` comes from `Y₀`
  have hH : LiftsEndos (FEt.pullback g ⋙ FEt.pullback (c.π.app j) ⋙ FEt.pullback m) Y₁ :=
    (LiftsEndos.of_full _ _).comp ((hlift.of_iso iY₁.symm).comp (LiftsEndos.of_full _ _))
  let ρH : (FEt.pullback g ⋙ FEt.pullback (c.π.app j) ⋙ FEt.pullback m) ≅
      FEt.pullback w ⋙ FEt.pullback α :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp (c.π.app j) g).symm _ ≪≫
      (MorphismProperty.Over.pullbackComp m (c.π.app j ≫ g)).symm ≪≫
      MorphismProperty.Over.pullbackCongr hα.symm ≪≫ MorphismProperty.Over.pullbackComp α w
  have hLE : LiftsEndos (FEt.pullback α) Y₀ := (hH.of_natIso ρH).of_comp
  -- the isomorphism `α^* Y₀ ≅ Z`
  let iα : (FEt.pullback α).obj Y₀ ≅ Z := (ρH.app Y₁).symm ≪≫
    (FEt.pullback m).mapIso ((FEt.pullback (c.π.app j)).mapIso iY₁ ≪≫ iY) ≪≫ iZ
  have : IsGalois ((FEt.pullback α).obj Y₀) := isGalois_of_iso F' iα.symm
  have hgal : IsGalois Y₀ :=
    isGalois_of_liftsEndos (FEt.pullback α) (ExposeV.FEt.pullbackFiberIso Ω' α a) Y₀ hLE
  refine ⟨K₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Y₀, hgal, ?_, ⟨iα⟩⟩
  rw [natCard_aut_eq_of_isGalois (FEt.pullback α) (ExposeV.FEt.pullbackFiberIso Ω' α a) Y₀]
  exact Nat.card_congr iα.conjAut.toEquiv

end SGA.SGA1.ExposeX
