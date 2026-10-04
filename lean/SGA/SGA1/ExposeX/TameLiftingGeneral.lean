/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TameLiftingSpecialization
import SGA.SGA1.ExposeX.TameLiftingDomination
import SGA.SGA1.ExposeX.SpecializationSurjective
import SGA.SGA1.ExposeX.TameSpecialization
import SGA.Foundations.CommAlg.DominatingDVR

/-!
# SGA 1, Exposé X, 3.8 over a locally noetherian base

X.3.8 (`TameSpecializationStatement`) is proved over a complete discrete valuation ring with
separably closed residue field, for `y₀` the closed and `y₁` the generic point
(`exists_tameSpecialization_of_isDiscreteValuationRing`). Here, as in SGA (proof of X.3.8, and
X.3.7), we deduce it for an arbitrary locally noetherian base `Y` and any specialization
`y₁ ⤳ y₀`: `tameSpecializationStatement`. The reduction is
`tameSpecializationStatement_of_exists_isDiscreteValuationRing`, which takes EGA II 7.1.7 as a
hypothesis in the following form: every noetherian local domain that is not a field is dominated
by a discrete valuation ring, i.e. there is an injective local homomorphism to one. That
hypothesis is `IsLocalRing.exists_isDiscreteValuationRing_dominating`
(`SGA.Foundations.CommAlg.DominatingDVR`). X.3.9 for these bases follows by
`exists_primeToQuotientEquiv_of_tameSpecialization` and `exists_bijective_of_tameSpecialization`.

The steps:

* if `y₁ ≠ y₀`, the local ring `𝒪_{Y,y₀}/𝔭_{y₁}` of the closure of `y₁` at `y₀` is a noetherian
  local domain and not a field. It is dominated by a discrete valuation ring (the hypothesis),
  and that one by a complete discrete valuation ring `R` with separably closed residue field
  (`exists_isAdicComplete_isDiscreteValuationRing`; SGA uses EGA 0_III 10.3.1 to get an
  algebraically closed residue field, which the core does not need). This gives
  `g : Spec R ⟶ Y` sending the closed point to `y₀` and the generic point to `y₁`
  (`exists_isDiscreteValuationRing_of_specializes`);
* the geometric points `b₀`, `b₁` lift to `Spec R` after algebraically closed extensions of their
  fields of values (`exists_lift_of_apply_eq`);
* the fundamental group of a geometric fibre does not change under such an extension (X.1.8,
  `nonempty_continuousMulEquiv_of_eq_comp`). Hence the geometric fibres of `f` at `b₀`, `b₁` have
  the fundamental groups of those of `X ×_Y Spec R` at the lifted points;
* `FactorsPrimeTo` is invariant under isomorphisms of topological groups
  (`FactorsPrimeTo.comp_continuousMulEquiv`);
* if `y₁ = y₀`, the specialization homomorphism is the isomorphism of X.1.8 between the two
  geometric fibres (`nonempty_continuousMulEquiv_of_apply_eq`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeX

section FactorsPrimeTo

variable {G₁ G₁' : Type u} {G₀ G₀' : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₁']
  [TopologicalSpace G₁'] [Group G₀] [TopologicalSpace G₀] [Group G₀'] [TopologicalSpace G₀']

/-- `FactorsPrimeTo` is invariant under isomorphisms of topological groups on both sides: if
every continuous homomorphism of `G₁` into a finite group of order prime to `q` factors
continuously through `sp : G₁ → G₀`, the same holds for `e₀ ∘ sp ∘ e₁ : G₁' → G₀'`. -/
theorem FactorsPrimeTo.comp_continuousMulEquiv {sp : G₁ →* G₀} {q : ℕ}
    (h : FactorsPrimeTo sp q) (e₁ : G₁' ≃ₜ* G₁) (e₀ : G₀ ≃ₜ* G₀') :
    FactorsPrimeTo ((e₀.toMonoidHom.comp sp).comp e₁.toMonoidHom) q := by
  intro Q _ _ _ _ hQ ψ hψ
  obtain ⟨g, hg, hgsp⟩ := h Q hQ (ψ.comp e₁.symm.toMonoidHom) (hψ.comp e₁.symm.continuous)
  refine ⟨g.comp e₀.symm.toMonoidHom, hg.comp e₀.symm.continuous, ?_⟩
  ext x
  have := DFunLike.congr_fun hgsp (e₁ x)
  change g (sp (e₁ x)) = ψ (e₁.symm (e₁ x)) at this
  rw [ContinuousMulEquiv.symm_apply_apply] at this
  change g (e₀.symm (e₀ (sp (e₁ x)))) = ψ x
  rw [ContinuousMulEquiv.symm_apply_apply, this]

/-- An isomorphism of topological groups satisfies `FactorsPrimeTo` for every `q`. -/
theorem factorsPrimeTo_continuousMulEquiv (e : G₁ ≃ₜ* G₀) (q : ℕ) :
    FactorsPrimeTo e.toMonoidHom q := by
  intro Q _ _ _ _ _ ψ hψ
  refine ⟨ψ.comp e.symm.toMonoidHom, hψ.comp e.symm.continuous, ?_⟩
  ext x
  change ψ (e.symm (e x)) = ψ x
  rw [ContinuousMulEquiv.symm_apply_apply]

end FactorsPrimeTo

/-- A point `b : Spec K ⟶ Y` lifts along `c : S ⟶ Y` through any `w` with `c w = b(pt)`, after
an algebraically closed extension `L` of `K`: there is `b' : Spec L ⟶ S` with `b'(pt) = w` and
`b' ≫ c = (Spec L ⟶ Spec K) ≫ b`. (Embed `κ(w)` and `K` over `κ(b(pt))` into an algebraically
closed field, `exists_isAlgClosed_amalgamation`.) -/
theorem exists_lift_of_apply_eq {S Y : Scheme.{u}} (c : S ⟶ Y) (w : S) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ Y) (h : b (closedPoint K) = c w) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : Algebra K L) (b' : Spec (.of L) ⟶ S),
      b' ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b ∧ b' (closedPoint L) = w := by
  obtain ⟨φ, hb⟩ := exists_eq_specMap_comp_fromSpecResidueField K b
  let ρ := (Y.residueFieldCongr h).hom ≫ c.residueFieldMap w
  have hρ : ρ = (Y.residueFieldCongr h).hom ≫ c.residueFieldMap w := rfl
  obtain ⟨L, _, _, j₁, j₂, hj⟩ := exists_isAlgClosed_amalgamation φ.hom ρ.hom
  let _ : Algebra K L := j₁.toAlgebra
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom j₂) ≫ S.fromSpecResidueField w, ?_, ?_⟩
  · have hj' : φ ≫ CommRingCat.ofHom j₁ = ρ ≫ CommRingCat.ofHom j₂ := by
      ext x
      exact congrArg (fun g ↦ g x) hj
    have e₁ : (Spec.map (CommRingCat.ofHom j₂) ≫ S.fromSpecResidueField w) ≫ c =
        Spec.map (ρ ≫ CommRingCat.ofHom j₂) ≫ Y.fromSpecResidueField (b (closedPoint K)) := by
      rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← fromSpecResidueField_congr h, Spec.map_comp ρ (CommRingCat.ofHom j₂), hρ,
        Spec.map_comp, Category.assoc, Category.assoc]
      rfl
    have e₂ : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b =
        Spec.map (φ ≫ CommRingCat.ofHom j₁) ≫ Y.fromSpecResidueField (b (closedPoint K)) := by
      conv_lhs => rw [hb]
      rw [Spec.map_comp φ (CommRingCat.ofHom j₁), Category.assoc]
    rw [e₁, e₂, hj']
  · obtain ⟨pt, hpt⟩ : ∃ pt : Spec (.of L), pt = closedPoint L := ⟨_, rfl⟩
    rw [← hpt, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]


section GeometricFibres

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [GeometricallyConnected f]

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8 for a geometric fibre: let `f` be proper with geometrically connected fibres,
`b : Spec Ω ⟶ Y` with `Ω` algebraically closed, `L` an algebraically closed extension of `Ω` and
`b' = (Spec L ⟶ Spec Ω) ≫ b`. Then `π₁(X_{b'}, a') ≅ π₁(X_b, a)` as topological groups, for any
geometric points `a`, `a'` with separably closed values: `X_{b'} = X_b ⊗_Ω L`, and base change of
étale coverings along `X_b ⊗_Ω L ⟶ X_b` is an equivalence (`baseChangeAlgClosedStatement`). -/
theorem nonempty_continuousMulEquiv_of_eq_comp (Ω L : Type u) [Field Ω] [IsAlgClosed Ω]
    [Field L] [IsAlgClosed L] [Algebra Ω L] (b : Spec (.of Ω) ⟶ Y) (b' : Spec (.of L) ⟶ Y)
    (hb : b' = Spec.map (CommRingCat.ofHom (algebraMap Ω L)) ≫ b) (K K' : Type u) [Field K]
    [IsSepClosed K] [Field K'] [IsSepClosed K'] (a : Spec (.of K) ⟶ pullback f b)
    (a' : Spec (.of K') ⟶ pullback f b') :
    Nonempty (ExposeV.etaleFundamentalGroup K' a' ≃ₜ* ExposeV.etaleFundamentalGroup K a) := by
  subst hb
  have : ConnectedSpace ↥(pullback f b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) b _ _
      (IsPullback.of_hasPullback f b)
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap Ω L)) ≫ b)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback f _)
  have : IsProper (pullback.snd f b) := MorphismProperty.pullback_snd _ _ inferInstance
  have := baseChangeAlgClosedStatement Ω L (pullback.snd f b)
  let σ := Spec.map (CommRingCat.ofHom (algebraMap Ω L))
  have : (FEt.pullback ((pullbackLeftPullbackSndIso f b σ).inv ≫
      pullback.fst (pullback.snd f b) σ)).IsEquivalence :=
    ExposeV.FEt.isEquivalence_pullback_comp _ _
  exact nonempty_continuousMulEquiv_of_isEquivalence
    ((pullbackLeftPullbackSndIso f b σ).inv ≫ pullback.fst (pullback.snd f b) σ) K' K a' a

/-- The fundamental group of a geometric fibre depends only on the image point (X.1.8): let `f`
be proper with geometrically connected fibres and `b : Spec Ω ⟶ Y`, `b' : Spec Ω' ⟶ Y` with
`Ω`, `Ω'` algebraically closed and the same image point. Then `π₁(X_b, a) ≅ π₁(X_{b'}, a')` as
topological groups, for any geometric points `a`, `a'` with separably closed values. -/
theorem nonempty_continuousMulEquiv_of_apply_eq (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω]
    [Field Ω'] [IsAlgClosed Ω'] (b : Spec (.of Ω) ⟶ Y) (b' : Spec (.of Ω') ⟶ Y)
    (h : b (closedPoint Ω) = b' (closedPoint Ω')) (K K' : Type u) [Field K] [IsSepClosed K]
    [Field K'] [IsSepClosed K'] (a : Spec (.of K) ⟶ pullback f b)
    (a' : Spec (.of K') ⟶ pullback f b') :
    Nonempty (ExposeV.etaleFundamentalGroup K a ≃ₜ* ExposeV.etaleFundamentalGroup K' a') := by
  obtain ⟨L, _, _, _, t, ht, -⟩ := exists_lift_of_apply_eq b' (closedPoint Ω') Ω b h
  obtain ⟨ψ, rfl⟩ : ∃ ψ : CommRingCat.of Ω' ⟶ CommRingCat.of L, t = Spec.map ψ :=
    ⟨Spec.preimage t, (Spec.map_preimage t).symm⟩
  let : Algebra Ω' L := ψ.hom.toAlgebra
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap Ω L)) ≫ b)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback f _)
  obtain ⟨M, _, _, ⟨c⟩⟩ := exists_geometricPoint_of_nonempty
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap Ω L)) ≫ b))
  obtain ⟨e⟩ := nonempty_continuousMulEquiv_of_eq_comp f Ω L b _ rfl K M a c
  obtain ⟨e'⟩ := nonempty_continuousMulEquiv_of_eq_comp f Ω' L b'
    (Spec.map (CommRingCat.ofHom (algebraMap Ω L)) ≫ b) ht.symm K' M a' c
  exact ⟨e.symm.trans e'⟩

end GeometricFibres


section Domination

/-- The reduction of X.3.8 to a complete discrete valuation ring (proof of X.3.8, X.3.7), given
EGA II 7.1.7 as the hypothesis `hdom` (every noetherian local domain that is not a field is
dominated by a discrete valuation ring). Let `Y` be locally noetherian and `y₁ ⤳ y₀` with
`y₁ ≠ y₀`. Then there are a complete discrete valuation ring `R` with separably closed residue
field and `g : Spec R ⟶ Y` sending the closed point to `y₀` and the generic point to `y₁`:
dominate `𝒪_{Y,y₀}/𝔭_{y₁}` by a discrete valuation ring (`hdom`), and that one by the completion
of its strict henselization (`exists_isAdicComplete_isDiscreteValuationRing`). -/
theorem exists_isDiscreteValuationRing_of_specializes
    (hdom : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A],
      ¬ IsField A → ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R) (φ : A →+* R), Function.Injective φ ∧ IsLocalHom φ)
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] {y₀ y₁ : Y} (h : y₁ ⤳ y₀) (hne : y₁ ≠ y₀) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (maximalIdeal R) R) (_ : IsSepClosed (ResidueField R))
      (g : Spec (.of R) ⟶ Y), g (closedPoint R) = y₀ ∧
        ∀ w : Spec (.of R), w.asIdeal = ⊥ → g w = y₁ := by
  obtain ⟨z, hz⟩ : y₁ ∈ Set.range (Y.fromSpecStalk y₀) := by
    rw [Scheme.range_fromSpecStalk]
    exact h
  let O := Y.presheaf.stalk y₀
  let P : Ideal O := z.asIdeal
  let A := O ⧸ P
  have : P.IsPrime := z.isPrime
  have : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective
  have hA : ¬ IsField A := by
    intro hA
    have hP : P.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr hA
    have hz' : z = closedPoint O :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hP)
    apply hne
    rw [← hz, hz', Scheme.fromSpecStalk_closedPoint]
  obtain ⟨R₁, _, _, _, φ, hφ, _⟩ := hdom A hA
  obtain ⟨R, _, _, _, _, _, ψ, hψ, _⟩ := exists_isAdicComplete_isDiscreteValuationRing R₁
  have : IsLocalHom (Ideal.Quotient.mk P) := .of_surjective _ Ideal.Quotient.mk_surjective
  let θ : O →+* R := ψ.comp (φ.comp (Ideal.Quotient.mk P))
  have : IsLocalHom (CommRingCat.ofHom θ).hom := by
    change IsLocalHom (ψ.comp (φ.comp (Ideal.Quotient.mk P)))
    infer_instance
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk y₀, ?_, fun w hw ↦ ?_⟩
  · change (Y.fromSpecStalk y₀) ((Spec.map (CommRingCat.ofHom θ)) (closedPoint R)) = y₀
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  · have : (Spec.map (CommRingCat.ofHom θ)) w = z := by
      apply PrimeSpectrum.ext
      change Ideal.comap θ w.asIdeal = P
      rw [hw, ← RingHom.ker_eq_comap_bot]
      ext x
      simp only [θ, RingHom.mem_ker, RingHom.comp_apply]
      rw [map_eq_zero_iff ψ hψ, map_eq_zero_iff φ hφ, Ideal.Quotient.eq_zero_iff_mem]
    rw [Scheme.Hom.comp_apply, this, hz]

end Domination


section Statement

set_option backward.isDefEq.respectTransparency false in
/-- **X.3.8 over a locally noetherian base, given EGA II 7.1.7** (`hdom`: every noetherian local
domain that is not a field is dominated by a discrete valuation ring in the same universe; proved
as `IsLocalRing.exists_isDiscreteValuationRing_dominating`, which gives
`tameSpecializationStatement`). Let `f : X ⟶ Y` be proper and smooth with geometrically connected
fibres, `Y` locally noetherian, `b₀`, `b₁` geometric points of `Y` with algebraically closed values
such that `y₁ = b₁(pt)` specializes to `y₀ = b₀(pt)`, and `a₀`, `a₁` geometric points of `X_{b₀}`,
`X_{b₁}`. Then there is a continuous surjective homomorphism `π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)`
through which every continuous homomorphism of `π₁(X_{b₁}, a₁)` into a finite group of order prime
to the characteristic exponent of `κ(y₀)` factors. As in SGA, `f` is pulled back to a complete
discrete valuation ring through `y₀` and `y₁` (`exists_isDiscreteValuationRing_of_specializes`),
where the core of X.3.8 holds (`exists_tameSpecialization_of_isDiscreteValuationRing`). -/
theorem tameSpecializationStatement_of_exists_isDiscreteValuationRing
    (hdom : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A],
      ¬ IsField A → ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
        (_ : IsDiscreteValuationRing R) (φ : A →+* R), Function.Injective φ ∧ IsLocalHom φ) :
    TameSpecializationStatement.{u} := by
  intro X Y f _ _ _ _ Ω₀ Ω₁ _ _ _ _ b₀ b₁ hsp a₀ a₁
  have : ConnectedSpace ↥(pullback f b₀) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) b₀ _ _
      (IsPullback.of_hasPullback f b₀)
  have : ConnectedSpace ↥(pullback f b₁) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) b₁ _ _
      (IsPullback.of_hasPullback f b₁)
  by_cases hne : b₁ (closedPoint Ω₁) = b₀ (closedPoint Ω₀)
  · -- `y₁ = y₀`: the two geometric fibres have isomorphic fundamental groups (X.1.8)
    obtain ⟨e⟩ := nonempty_continuousMulEquiv_of_apply_eq f Ω₁ Ω₀ b₁ b₀ hne Ω₁ Ω₀ a₁ a₀
    exact ⟨e.toMonoidHom, e.continuous, e.surjective, factorsPrimeTo_continuousMulEquiv e _⟩
  -- a complete discrete valuation ring `R` with `g : Spec R ⟶ Y` through `y₀` and `y₁`
  obtain ⟨R, _, _, _, _, _, g, hg₀, hg₁⟩ :=
    exists_isDiscreteValuationRing_of_specializes hdom hsp hne
  let w₁ : Spec (.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨L₀, _, _, _, c₀, hc₀, hc₀pt⟩ := exists_lift_of_apply_eq g (closedPoint R) Ω₀ b₀ hg₀.symm
  obtain ⟨L₁, _, _, _, c₁, hc₁, hc₁pt⟩ :=
    exists_lift_of_apply_eq g w₁ Ω₁ b₁ (hg₁ w₁ rfl).symm
  -- the base change `f' : X' ⟶ Spec R`
  let f' := pullback.snd f g
  have : IsProper f' := MorphismProperty.pullback_snd _ _ inferInstance
  have : Smooth f' := MorphismProperty.pullback_snd _ _ inferInstance
  have : GeometricallyConnected f' := MorphismProperty.pullback_snd _ _ inferInstance
  have hb₀ : ∀ x, c₀.base x = closedPoint R := by
    intro x
    have hx : x = closedPoint L₀ :=
      PrimeSpectrum.ext ((@Ideal.eq_bot_of_prime _ _ _ x.isPrime).trans
        (IsLocalRing.maximalIdeal_eq_bot (R := L₀)).symm)
    rw [hx]
    exact hc₀pt
  have hb₁ : Function.Injective (Spec.preimage c₁).hom := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    have h := congrArg PrimeSpectrum.asIdeal hc₁pt
    rw [← Spec.map_preimage c₁] at h
    have h₀ : (closedPoint L₁).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    change Ideal.comap (Spec.preimage c₁).hom (closedPoint L₁).asIdeal = ⊥ at h
    rwa [h₀] at h
  -- rational points of the geometric fibres of `f'`
  have : ConnectedSpace ↥(pullback f' c₀) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') c₀ _ _
      (IsPullback.of_hasPullback f' c₀)
  have : ConnectedSpace ↥(pullback f' c₁) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') c₁ _ _
      (IsPullback.of_hasPullback f' c₁)
  have : IsProper (pullback.snd f' c₀) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsProper (pullback.snd f' c₁) := MorphismProperty.pullback_snd _ _ inferInstance
  have : CompactSpace ↥(pullback f' c₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f' c₀)
  have : CompactSpace ↥(pullback f' c₁) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f' c₁)
  obtain ⟨a₀', -⟩ := exists_comp_eq_id (pullback.snd f' c₀)
  obtain ⟨a₁', -⟩ := exists_comp_eq_id (pullback.snd f' c₁)
  -- the core of X.3.8 over `R`
  obtain ⟨sp', hc, hs, hfac⟩ :=
    exists_tameSpecialization_of_isDiscreteValuationRing R f' L₀ L₁ c₀ hb₀ c₁ hb₁ a₀' a₁'
  -- the geometric fibres of `f'` and of `f`
  have : ConnectedSpace ↥(pullback f (c₀ ≫ g)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback f _)
  have : ConnectedSpace ↥(pullback f (c₁ ≫ g)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) _ _ _
      (IsPullback.of_hasPullback f _)
  obtain ⟨i₀⟩ := nonempty_continuousMulEquiv_of_isEquivalence
    (pullbackLeftPullbackSndIso f g c₀).hom L₀ L₀ a₀'
    (a₀' ≫ (pullbackLeftPullbackSndIso f g c₀).hom)
  obtain ⟨i₁⟩ := nonempty_continuousMulEquiv_of_isEquivalence
    (pullbackLeftPullbackSndIso f g c₁).hom L₁ L₁ a₁'
    (a₁' ≫ (pullbackLeftPullbackSndIso f g c₁).hom)
  obtain ⟨j₀⟩ := nonempty_continuousMulEquiv_of_eq_comp f Ω₀ L₀ b₀ (c₀ ≫ g) hc₀ Ω₀ L₀ a₀
    (a₀' ≫ (pullbackLeftPullbackSndIso f g c₀).hom)
  obtain ⟨j₁⟩ := nonempty_continuousMulEquiv_of_eq_comp f Ω₁ L₁ b₁ (c₁ ≫ g) hc₁ Ω₁ L₁ a₁
    (a₁' ≫ (pullbackLeftPullbackSndIso f g c₁).hom)
  let e₀ := i₀.trans j₀
  let e₁ := i₁.trans j₁
  refine ⟨(e₀.toMonoidHom.comp sp').comp e₁.symm.toMonoidHom,
    e₀.continuous.comp (hc.comp e₁.symm.continuous),
    e₀.surjective.comp (hs.comp e₁.symm.surjective), ?_⟩
  rw [ringExpChar_eq_of_ringHom (algebraMap Ω₀ L₀)]
  exact hfac.comp_continuousMulEquiv e₁.symm e₀

/-- **X.3.8.** Let `f : X ⟶ Y` be proper and smooth with geometrically connected fibres, `Y`
locally noetherian, `b₀`, `b₁` geometric points of `Y` with algebraically closed values such that
`y₁ = b₁(pt)` specializes to `y₀ = b₀(pt)`, and `a₀`, `a₁` geometric points of `X_{b₀}`, `X_{b₁}`
(with values in the same fields). Then there is a continuous surjective homomorphism
`π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)` through which every continuous homomorphism of `π₁(X_{b₁}, a₁)`
into a finite group of order prime to the characteristic exponent of `κ(y₀)` factors. Like
`TameSpecializationStatement`, this is the existence form: up to an inner automorphism, the
homomorphism constructed is SGA's specialization homomorphism (the inverse of the isomorphism
`π₁(X_{b₀}) ≅ π₁(X_R)` of X.2.1 composed with `π₁(X_{b₁}) → π₁(X_R)`, after pulling back to a
complete discrete valuation ring `R`; the X.1.8 isomorphisms used to return to `b₀`, `b₁` are
chosen, each with a path, so only the conjugacy class is canonical, as in SGA), but the statement
does not record this. This is
`tameSpecializationStatement_of_exists_isDiscreteValuationRing` with EGA II 7.1.7
(`IsLocalRing.exists_isDiscreteValuationRing_dominating`). -/
theorem tameSpecializationStatement : TameSpecializationStatement.{u} :=
  tameSpecializationStatement_of_exists_isDiscreteValuationRing fun A _ _ _ _ hA ↦
    IsLocalRing.exists_isDiscreteValuationRing_dominating A hA

end Statement

end SGA.SGA1.ExposeX
