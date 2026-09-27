/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.HenselianQuasiFinite
import SGA.Foundations.StrictlyHenselianFinite
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent
import SGA.SGA1.ExposeIX.StrictlyLocalDescent

/-!
# SGA 1, Exposé IX, 4.7 over an arbitrary base

IX.4.7: a finite surjective morphism of finite presentation `g : S' ⟶ S` is an effective descent
morphism for étale separated schemes of finite type
(`isEffectiveDescentMorphism_of_isFinite_of_locallyOfFinitePresentation`).

SGA reduces to a noetherian base by the limit methods of EGA IV 8 and then argues by induction on
the dimension over complete local rings (as in `SGA.SGA1.ExposeIX.FiniteEffectiveDescent`). We
avoid the noetherian reduction: complete local rings are replaced by strict henselizations, and
the induction on the dimension by the choice of a generic point of an irreducible component of
the (closed) set of points near which the datum is not effective.

* Over a strictly henselian local ring `R`
  (`DescentDatum.isEffective_of_isFinite_of_isStrictlyHenselian`): the generizations of the
  closed fibre of `X'` form an open and closed subset `O`, finite over `S'` and stable
  (`exists_opens_forall_specializes_isFinite_of_henselian`, a form of Zariski's main theorem over
  henselian rings, Stacks 04GJ). On `O` the datum is effective by the finite étale case
  (`DescentDatum.isEffective_finiteEtale_of_isStrictlyHenselian`: descent over the closed point by
  IX.4.1, then lifting to `R`, since finite étale `R`-algebras are split and maps from them to
  finite `R`-algebras lift from the closed fibre,
  `IsStrictlyHenselian.bijective_comp_includeRight_of_finite`). The complement lies over the
  punctured spectrum, where effectiveness is assumed.
* Over any `S` (`DescentDatum.isEffective_of_isFinite_of_locallyOfFinitePresentation`): by IX.4.4
  the set `Z` of points `x` over whose local ring the datum is not effective is closed. If it is
  not empty, let `η` be a generic point of an irreducible component of `Z`; the datum is effective
  over the local rings at all proper generizations of `η`. Pulling back to the strict
  henselization `𝒪^{sh}_{S,η}` (faithfully flat, IX.4.2), whose punctured spectrum maps to these
  generizations, the previous step shows that it is effective at `η`, a contradiction. IX.4.5
  concludes.
-/

universe u

open CategoryTheory Limits MorphismProperty IsLocalRing Topology

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-- In a quasi-sober `T₀` space, a nonempty closed set `Z` contains a point `η` which has no proper
generization in `Z` (a generic point of an irreducible component of `Z`). -/
lemma exists_mem_forall_specializes_eq {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {Z : Set X} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ η ∈ Z, ∀ y ∈ Z, y ⤳ η → y = η := by
  obtain ⟨z, hz⟩ := hne
  have : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  let C : Set Z := irreducibleComponent ⟨z, hz⟩
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCc : IsClosed C := isClosed_irreducibleComponent
  let η' : Z := hC.genericPoint
  have hη' : closure {η'} = C := by
    rw [hC.isGenericPoint_genericPoint_closure.def, hCc.closure_eq]
  refine ⟨η'.1, η'.2, fun y hy hyη ↦ ?_⟩
  let y' : Z := ⟨y, hy⟩
  have h1 : y' ⤳ η' := Topology.IsInducing.subtypeVal.specializes_iff.mp hyη
  have hsub : C ⊆ closure {y'} := by
    rw [← hη']
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h1))
      isClosed_closure
  have h2 : closure {y'} = C :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  have : y' = η' := (inseparable_iff_closure_eq.mpr (h2.trans hη'.symm)).eq
  exact congrArg Subtype.val this

/-! ### The finite étale case over a strictly henselian local ring -/

section StrictlyHenselian

variable {R : Type u} [CommRing R] [IsStrictlyHenselian R]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7, finite étale case over a strictly henselian local base: along a finite surjective
`g : S' ⟶ Spec R`, every descent datum on a finite étale `S'`-scheme is effective, with a finite
étale descended scheme. -/
theorem DescentDatum.isEffective_finiteEtale_of_isStrictlyHenselian {S' Y : Scheme.{u}}
    {g : S' ⟶ Spec (.of R)} [IsFinite g] [Surjective g] {a : Y ⟶ S'} [IsFinite a] [Etale a]
    (D : DescentDatum g a) : D.IsEffective (@IsFinite ⊓ @Etale) :=
  D.isEffective_of_isFinite_of_lift
    (fun C _ inst _ inst' ↦ @IsLocalRing.exists_finite_etale_lift R _ _ C _ inst inst')
    (fun B _ _ _ _ T _ _ _ ↦ IsStrictlyHenselian.bijective_comp_includeRight_of_finite B T)

end StrictlyHenselian

/-! ### Effectiveness near the points of the image of a morphism -/

section Local

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

/-- For `t : T ⟶ S` and `u ∈ T`, if a descent datum is effective over `Spec 𝒪_{S,t(u)}`, its base
change to `T` is effective over `Spec 𝒪_{T,u}`. -/
lemma DescentDatum.isEffective_baseChange_fromSpecStalk {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (D : DescentDatum g a) {T : Scheme.{u}} (t : T ⟶ S) (u : T)
    (h : (D.baseChange (S.fromSpecStalk (t u))).IsEffective P) :
    ((D.baseChange t).baseChange (T.fromSpecStalk u)).IsEffective P := by
  rw [DescentDatum.isEffective_baseChange_baseChange_iff, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← DescentDatum.isEffective_baseChange_baseChange_iff]
  exact h.baseChange _

variable [UniversallySubmersive g] [LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g]

set_option backward.isDefEq.respectTransparency false in
/-- Under the hypotheses of IX.4.4: if a descent datum is effective over `Spec 𝒪_{S,t(u)}` for every
point `u` of `T`, its base change along `t : T ⟶ S` is effective (by IX.4.5). -/
theorem DescentDatum.isEffective_baseChange_of_forall_fromSpecStalk (D : DescentDatum g a)
    (ha : etaleFinitePresentation a) {T : Scheme.{u}} (t : T ⟶ S)
    (h : ∀ u : T, (D.baseChange (S.fromSpecStalk (t u))).IsEffective etaleFinitePresentation) :
    (D.baseChange t).IsEffective etaleFinitePresentation := by
  rw [(D.baseChange t).isEffective_iff_forall_fromSpecStalk (MorphismProperty.pullback_snd _ _ ha)]
  exact fun u ↦ D.isEffective_baseChange_fromSpecStalk t u (h u)

end Local

/-! ### The local step over a strictly henselian base -/

section StrictlyHenselianStep

variable {R : Type u} [CommRing R] [IsStrictlyHenselian R]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7 over a strictly henselian local base `Spec R`, given effectiveness over the punctured
spectrum: let `g : S' ⟶ Spec R` be finite, surjective and of finite presentation, and `X'` étale,
separated and of finite type over `S'` with a descent datum which is effective over
`Spec 𝒪_{Spec R, u}` for every non-closed point `u`. Then the datum is effective. -/
theorem DescentDatum.isEffective_of_isFinite_of_isStrictlyHenselian {S' X' : Scheme.{u}}
    {g : S' ⟶ Spec (.of R)} [IsFinite g] [Surjective g] [LocallyOfFinitePresentation g]
    {a : X' ⟶ S'} [Etale a] [IsSeparated a] [QuasiCompact a] (D : DescentDatum g a)
    (hU : ∀ u : Spec (.of R), u ≠ closedPoint R →
      (D.baseChange ((Spec (.of R)).fromSpecStalk u)).IsEffective etaleFinitePresentation) :
    D.IsEffective @Etale := by
  have : LocallyQuasiFinite a := locallyQuasiFinite_of_formallyUnramified a
  have ha : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨O, hOcl, hOst, hOfin, hOs⟩ := D.exists_isStable_isFinite_of_forall fun y hy ↦
    exists_opens_forall_specializes_isFinite_of_henselian (a ≫ g) hy
      ((a ≫ g).finite_preimage_singleton _)
  let O₂ : X'.Opens := ⟨(O : Set X')ᶜ, hOcl.isOpen_compl⟩
  have hO₂st : D.IsStable O₂ := by
    ext z
    have := SetLike.ext_iff.mp hOst z
    change z ∈ D.act ⁻¹ᵁ O ↔ z ∈ pullback.fst (a ≫ g) g ⁻¹ᵁ O at this
    change D.act z ∉ O ↔ pullback.fst (a ≫ g) g z ∉ O
    exact not_congr this
  -- the finite part
  have hE₁ : (D.restrict O hOst).IsEffective @Etale :=
    (D.restrict O hOst).isEffective_finiteEtale_of_isStrictlyHenselian.of_le fun _ _ _ h ↦ h.2
  -- the part over the punctured spectrum
  have hE₂ : (D.restrict O₂ hO₂st).IsEffective @Etale := by
    let U : (Spec (.of R)).Opens :=
      ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩
    have hO₂U : O₂ ≤ (a ≫ g) ⁻¹ᵁ U := fun x hx hxs ↦ hx (hOs x hxs)
    have hst : D.IsStable ((a ≫ g) ⁻¹ᵁ U) := D.isStable_preimage U
    have hEU : (D.restrict ((a ≫ g) ⁻¹ᵁ U) hst).IsEffective @Etale := by
      have := D.isEffective_baseChange_of_forall_fromSpecStalk ha U.ι fun u ↦ hU _ u.2
      exact DescentDatum.isEffective_restrict_of_isEffective_baseChange rfl
        (this.of_le fun _ _ _ h ↦ h.1.1)
    obtain ⟨EU⟩ := (DescentDatum.isEffective_iff_nonempty_descent etale).mp hEU
    exact (DescentDatum.isEffective_iff_nonempty_descent etale).mpr
      ⟨EU.restrictLE hO₂st hst hO₂U⟩
  refine D.isEffective_of_iSup_eq_top (fun b : Bool ↦ if b then O else O₂) ?_
    (fun b ↦ by cases b <;> simpa) (fun b ↦ by cases b <;> simp [hE₁, hE₂])
  refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_cases hx : x ∈ O
  · exact ⟨true, by simpa using hx⟩
  · exact ⟨false, by simp only [Bool.false_eq_true, ite_false]; exact hx⟩

end StrictlyHenselianStep

/-! ### IX.4.7 over an arbitrary base -/

section General

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}
  [IsFinite g] [Surjective g] [LocallyOfFinitePresentation g]

/-- Every point of `Spec 𝒪^{sh}_{S,x}` maps to a generization of `x`. -/
lemma fromSpecStrictLocalRing_specializes (x : S) (u : Spec (.of (strictLocalRing S x))) :
    fromSpecStrictLocalRing S x u ⤳ x := by
  let c : Spec (.of (strictLocalRing S x)) := closedPoint (strictLocalRing S x)
  have h : fromSpecStrictLocalRing S x u ⤳ fromSpecStrictLocalRing S x c :=
    (specializes_closedPoint u).map (fromSpecStrictLocalRing S x).continuous
  have h₁ : specStrictLocalRingMap S x c = closedPoint (S.presheaf.stalk x) :=
    IsLocalRing.comap_closedPoint (algebraMap (S.presheaf.stalk x) (strictLocalRing S x))
  have hc : fromSpecStrictLocalRing S x c = x := by
    rw [fromSpecStrictLocalRing, Scheme.Hom.comp_apply, h₁, Scheme.fromSpecStalk_closedPoint]
  rwa [hc] at h

/-- The preimage of `x` under `Spec 𝒪^{sh}_{S,x} ⟶ S` is the closed point. -/
lemma eq_closedPoint_of_fromSpecStrictLocalRing_eq (x : S) (u : Spec (.of (strictLocalRing S x)))
    (hu : fromSpecStrictLocalRing S x u = x) : u = closedPoint (strictLocalRing S x) := by
  have h₁ : specStrictLocalRingMap S x u = closedPoint (S.presheaf.stalk x) := by
    apply (S.fromSpecStalk x).isEmbedding.injective
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hu
  have h₂ : u.asIdeal.comap (algebraMap (S.presheaf.stalk x) (strictLocalRing S x)) =
      maximalIdeal (S.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal h₁
  have hle : maximalIdeal (strictLocalRing S x) ≤ u.asIdeal := by
    rw [← StrictHenselization.map_maximalIdeal, Ideal.map_le_iff_le_comap, h₂]
  exact PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le u.isPrime.ne_top hle).symm

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7, key step: under the hypotheses of IX.4.7, if a descent datum is effective over the local
rings at all proper generizations of `x ∈ S`, it is effective over `Spec 𝒪_{S,x}`. The proof
passes to the strict henselization of `𝒪_{S,x}` (IX.4.2), whose punctured spectrum maps to proper
generizations of `x`. -/
theorem DescentDatum.isEffective_fromSpecStalk_of_forall_generalization [Etale a]
    [IsSeparated a] [QuasiCompact a] (D : DescentDatum g a) (x : S)
    (h : ∀ y, y ⤳ x → y ≠ x →
      (D.baseChange (S.fromSpecStalk y)).IsEffective etaleFinitePresentation) :
    (D.baseChange (S.fromSpecStalk x)).IsEffective etaleFinitePresentation := by
  have ha : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  refine DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated
    (D.baseChange (S.fromSpecStalk x)) (MorphismProperty.pullback_snd _ _ ha)
    (specStrictLocalRingMap S x) ?_
  rw [DescentDatum.isEffective_baseChange_baseChange_iff]
  change (D.baseChange (fromSpecStrictLocalRing S x)).IsEffective etaleFinitePresentation
  refine (D.baseChange (fromSpecStrictLocalRing S x)).isEffective_etaleFinitePresentation_of_etale
    (MorphismProperty.pullback_snd _ _ ha) ?_
  refine (D.baseChange (fromSpecStrictLocalRing S x)).isEffective_of_isFinite_of_isStrictlyHenselian
    fun u hu ↦ D.isEffective_baseChange_fromSpecStalk _ u (h _
      (fromSpecStrictLocalRing_specializes x u)
      fun he ↦ hu (eq_closedPoint_of_fromSpecStrictLocalRing_eq x u he))

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7: let `g : S' ⟶ S` be finite, surjective and of finite presentation. Every descent datum
relative to `g` on an étale, separated `S'`-scheme of finite type is effective. -/
theorem DescentDatum.isEffective_of_isFinite_of_locallyOfFinitePresentation
    (D : DescentDatum g a) (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ha
  have : Etale a := h₁
  have : IsSeparated a := h₂
  have : QuasiCompact a := h₃
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecStalk ha']
    by_contra hne
    simp only [not_forall] at hne
    let Z : Set S :=
      {x | ¬ (D.baseChange (S.fromSpecStalk x)).IsEffective etaleFinitePresentation}
    have hZ : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨U, hxU, hU⟩ := (D.exists_isEffective_baseChange_iff x ha').mpr (not_not.mp hx)
      exact ⟨U, fun y hy ↦ not_not.mpr ((D.exists_isEffective_baseChange_iff y ha').mp
        ⟨U, hy, hU⟩), U.2, hxU⟩
    obtain ⟨η, hηZ, hmin⟩ := exists_mem_forall_specializes_eq hZ hne
    exact hηZ (D.isEffective_fromSpecStalk_of_forall_generalization η fun y hy hne' ↦
      by_contra fun h ↦ hne' (hmin y h hy))
  exact D.isEffective_etaleSeparatedFiniteType_of_etale ⟨⟨h₁, h₂⟩, h₃⟩
    (hfp.of_le fun _ _ _ h ↦ h.1.1)

variable (g) in
/-- IX.4.7: a finite surjective morphism of finite presentation is an effective descent morphism
for étale separated schemes of finite type. -/
theorem isEffectiveDescentMorphism_of_isFinite_of_locallyOfFinitePresentation :
    IsEffectiveDescentMorphism g etaleSeparatedFiniteType :=
  ⟨isDescentMorphism_of_isFinite (g := g), fun _ _ D ha ↦
    D.isEffective_of_isFinite_of_locallyOfFinitePresentation ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7 for étale coverings: along a finite surjective `g : S' ⟶ S` of finite presentation,
every descent datum on a finite étale `S'`-scheme is effective, with a finite étale descended
scheme. -/
theorem DescentDatum.isEffective_etaleCovering_of_isFinite_of_locallyOfFinitePresentation
    [IsFinite a] [Etale a] (D : DescentDatum g a) : D.IsEffective etaleCovering := by
  obtain ⟨X, b, v, hb, hv, hact⟩ := D.isEffective_of_isFinite_of_locallyOfFinitePresentation
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : Etale b := hb.1.1
  have : IsProper b := (isProper_iff_of_isPullback hv.flip).mp inferInstance
  have : LocallyQuasiFinite b := locallyQuasiFinite_of_formallyUnramified b
  exact ⟨X, b, v, ⟨.of_isProper_of_locallyQuasiFinite b, inferInstance⟩, hv, hact⟩

end General

end SGA.SGA1.ExposeIX
