/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import SGA.Foundations.HenselizationNoetherian
import SGA.Foundations.Formal.CompletionNoetherian
import SGA.SGA1.ExposeIX.CompletedLocalRings

/-!
# SGA 1, Exposé IX, 4.6: effectiveness over strictly local rings

IX.4.6 reduces the effectiveness of a descent datum on an étale `S'`-scheme to the case where the
base is the spectrum of a complete noetherian local ring with algebraically closed residue field.
As in SGA the proof combines IX.4.5 (effectiveness over the local rings `𝒪_{S,x}`) with IX.4.2
(faithfully flat base change). SGA takes, for each `x`, a flat local extension of `𝒪̂_{S,x}` with
algebraically closed residue field (EGA 0_III 10.3.1). We use instead the completion of the strict
henselization `𝒪^{sh}_{S,x}` of `𝒪_{S,x}` with respect to an algebraic closure of `κ(x)`. It is a
complete noetherian local ring (Stacks 06LJ, `IsLocalRing.StrictHenselization.isNoetherianRing`),
faithfully flat over `𝒪_{S,x}`, and its residue field is the separable closure of `κ(x)`. For
étale descent a separably closed residue field is enough, so we prove:

* `DescentDatum.isEffective_iff_forall_fromSpecStrictLocalRing`: over any `S`, a datum is
  effective iff it is effective over every strict henselization `Spec 𝒪^{sh}_{S,x}`;
* `DescentDatum.isEffective_iff_forall_fromSpecCompletedStrictLocalRing`: over a locally
  noetherian `S`, iff it is effective over every `Spec (𝒪^{sh}_{S,x})^`;
* `DescentDatum.isEffective_iff_forall_isSepClosed` (IX.4.6 with separably closed residue
  fields): iff it is effective after base change to every complete noetherian local ring with
  separably closed residue field;
* `DescentDatum.isEffective_iff_forall_isAlgClosed` (IX.4.6 as stated in SGA, when the residue
  fields of `S` are perfect, e.g. in characteristic zero): there the separable closure is an
  algebraic closure.

SGA's statement for arbitrary residue fields (`IsEffectiveIffStrictlyLocalStatement`) asks for
effectiveness only over rings with algebraically closed residue field, a weaker hypothesis when
the residue fields are imperfect. Deducing it from the version here needs a flat local extension
of a complete local ring realizing a purely inseparable residue field extension (EGA 0_III
10.3.1), which we do not have.
-/

universe u

open CategoryTheory Limits MorphismProperty IsLocalRing

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

section StrictLocalRings

variable (S : Scheme.{u}) (x : S)

/-- The strict henselization `𝒪^{sh}_{S,x}` of the local ring of `S` at `x`, with respect to an
algebraic closure of the residue field `κ(x)` (EGA IV 18.8). It is a strictly henselian local
ring, faithfully flat over `𝒪_{S,x}`, and noetherian if `𝒪_{S,x}` is (Stacks 06LJ). -/
abbrev strictLocalRing : Type u :=
  StrictHenselization (S.presheaf.stalk x) (AlgebraicClosure (ResidueField (S.presheaf.stalk x)))

instance : IsLocalHom (algebraMap (S.presheaf.stalk x)
    (AlgebraicClosure (ResidueField (S.presheaf.stalk x)))) :=
  isLocalHom_algebraMap_of_isScalarTower

/-- The morphism `Spec 𝒪^{sh}_{S,x} ⟶ Spec 𝒪_{S,x}`. -/
noncomputable abbrev specStrictLocalRingMap :
    Spec (.of (strictLocalRing S x)) ⟶ Spec (S.presheaf.stalk x) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x) (strictLocalRing S x)))

/-- The morphism `Spec 𝒪^{sh}_{S,x} ⟶ S`. -/
noncomputable def fromSpecStrictLocalRing : Spec (.of (strictLocalRing S x)) ⟶ S :=
  specStrictLocalRingMap S x ≫ S.fromSpecStalk x

/-- The completion `(𝒪^{sh}_{S,x})^` of the strict henselization. -/
abbrev completedStrictLocalRing : Type u :=
  AdicCompletion (maximalIdeal (strictLocalRing S x)) (strictLocalRing S x)

/-- The morphism `Spec (𝒪^{sh}_{S,x})^ ⟶ Spec 𝒪^{sh}_{S,x}`. -/
noncomputable abbrev specCompletedStrictLocalRingMap :
    Spec (.of (completedStrictLocalRing S x)) ⟶ Spec (.of (strictLocalRing S x)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (strictLocalRing S x) (completedStrictLocalRing S x)))

/-- The morphism `Spec (𝒪^{sh}_{S,x})^ ⟶ S`. -/
noncomputable def fromSpecCompletedStrictLocalRing :
    Spec (.of (completedStrictLocalRing S x)) ⟶ S :=
  specCompletedStrictLocalRingMap S x ≫ fromSpecStrictLocalRing S x

lemma flat_and_surjective_specStrictLocalRingMap :
    Flat (specStrictLocalRingMap S x) ∧ Surjective (specStrictLocalRingMap S x) :=
  (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

instance : Flat (specStrictLocalRingMap S x) := (flat_and_surjective_specStrictLocalRingMap S x).1

instance : Surjective (specStrictLocalRingMap S x) :=
  (flat_and_surjective_specStrictLocalRingMap S x).2

lemma flat_and_surjective_specCompletedStrictLocalRingMap [IsLocallyNoetherian S] :
    Flat (specCompletedStrictLocalRingMap S x) ∧
      Surjective (specCompletedStrictLocalRingMap S x) := by
  have : Module.FaithfullyFlat (strictLocalRing S x) (completedStrictLocalRing S x) :=
    .of_flat_of_isLocalHom
  exact (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›)

/-- The residue field of the completion of a noetherian local ring is that of the ring. -/
noncomputable def residueFieldCompletionEquiv (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ResidueField R ≃+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
  RingEquiv.ofBijective _
    (AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing)

instance [IsLocallyNoetherian S] : IsSepClosed (ResidueField (completedStrictLocalRing S x)) :=
  IsSepClosed.of_ringEquiv (residueFieldCompletionEquiv (strictLocalRing S x))

/-- If `κ(x)` is perfect, the residue field of `(𝒪^{sh}_{S,x})^` is algebraically closed. -/
lemma isAlgClosed_residueField_completedStrictLocalRing [IsLocallyNoetherian S]
    [PerfectField (ResidueField (S.presheaf.stalk x))] :
    IsAlgClosed (ResidueField (completedStrictLocalRing S x)) :=
  IsAlgClosed.of_ringEquiv _ _ ((StrictHenselization.residueFieldEquiv (S.presheaf.stalk x)
    (AlgebraicClosure (ResidueField (S.presheaf.stalk x)))).toRingEquiv.symm.trans
      (residueFieldCompletionEquiv (strictLocalRing S x)))

end StrictLocalRings

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.2 in the form used for IX.4.6: for `g` universally submersive and quasi-compact and `X'`
étale, separated and of finite presentation over `S'`, a descent datum is effective as soon as its
base change along a faithfully flat quasi-compact `t : T ⟶ S` is. -/
lemma DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated
    [UniversallySubmersive g] [QuasiCompact g] (D : DescentDatum g a)
    (ha : etaleFinitePresentation a) [IsSeparated a] {T : Scheme.{u}} (t : T ⟶ S) [Flat t]
    [QuasiCompact t] [Surjective t] (h : (D.baseChange t).IsEffective etaleFinitePresentation) :
    D.IsEffective etaleFinitePresentation := by
  have hax : etaleSeparatedFiniteType a := ⟨⟨ha.1.1, ‹_›⟩, ha.1.2⟩
  have h' := (D.baseChange t).isEffective_etaleSeparatedFiniteType_of_etale
    (MorphismProperty.pullback_snd _ _ hax) (h.of_le fun _ _ _ h ↦ h.1.1)
  exact D.isEffective_etaleFinitePresentation_of_etale ha
    ((D.isEffective_of_isEffective_baseChange_of_flat t hax h').of_le
      etaleSeparatedFiniteType_le_etale)

variable [UniversallySubmersive g] [LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.6, first form (any base): under the hypotheses of IX.4.4, with `X'` separated over `S'`,
a descent datum is effective iff it is effective over the strict henselization `Spec 𝒪^{sh}_{S,x}`
of every local ring of `S`. -/
theorem DescentDatum.isEffective_iff_forall_fromSpecStrictLocalRing (D : DescentDatum g a)
    (ha : etaleFinitePresentation a) [IsSeparated a] :
    D.IsEffective etaleFinitePresentation ↔
      ∀ x : S, (D.baseChange (fromSpecStrictLocalRing S x)).IsEffective
        etaleFinitePresentation := by
  refine ⟨fun h x ↦ h.baseChange _, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_fromSpecStalk ha]
  intro x
  have hx : ((D.baseChange (S.fromSpecStalk x)).baseChange
      (specStrictLocalRingMap S x)).IsEffective etaleFinitePresentation :=
    (DescentDatum.isEffective_baseChange_baseChange_iff D _ _).mpr (h x)
  exact DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated
    (D.baseChange (S.fromSpecStalk x)) (MorphismProperty.pullback_snd _ _ ha)
    (specStrictLocalRingMap S x) hx

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.6, second form (locally noetherian base): under the hypotheses of IX.4.4, with `S` locally
noetherian and `X'` separated over `S'`, a descent datum is effective iff it is effective over
`Spec (𝒪^{sh}_{S,x})^` for every `x ∈ S`. These are complete noetherian local rings with
separably closed residue fields; SGA uses complete local rings with algebraically closed residue
fields instead (see the module docstring). -/
theorem DescentDatum.isEffective_iff_forall_fromSpecCompletedStrictLocalRing
    [IsLocallyNoetherian S] (D : DescentDatum g a) (ha : etaleFinitePresentation a)
    [IsSeparated a] :
    D.IsEffective etaleFinitePresentation ↔
      ∀ x : S, (D.baseChange (fromSpecCompletedStrictLocalRing S x)).IsEffective
        etaleFinitePresentation := by
  refine ⟨fun h x ↦ h.baseChange _, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_fromSpecStrictLocalRing ha]
  intro x
  obtain ⟨hflat, hsurj⟩ := flat_and_surjective_specCompletedStrictLocalRingMap S x
  have hx : ((D.baseChange (fromSpecStrictLocalRing S x)).baseChange
      (specCompletedStrictLocalRingMap S x)).IsEffective etaleFinitePresentation :=
    (DescentDatum.isEffective_baseChange_baseChange_iff D _ _).mpr (h x)
  exact DescentDatum.isEffective_of_isEffective_baseChange_of_flat_of_isSeparated
    (D.baseChange (fromSpecStrictLocalRing S x)) (MorphismProperty.pullback_snd _ _ ha)
    (specCompletedStrictLocalRingMap S x) hx

/-- IX.4.6 with separably closed residue fields: under the hypotheses of IX.4.4, with `S` locally
noetherian and `X'` separated over `S'`, a descent datum is effective iff it is effective after
base change to the spectrum of every complete noetherian local ring with separably closed residue
field. (SGA asks for algebraically closed residue fields; for étale descent the separable closure
suffices, see the module docstring and `DescentDatum.isEffective_iff_forall_isAlgClosed`.) -/
theorem DescentDatum.isEffective_iff_forall_isSepClosed [IsLocallyNoetherian S]
    (D : DescentDatum g a) (ha : etaleFinitePresentation a) [IsSeparated a] :
    D.IsEffective etaleFinitePresentation ↔
      ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
        [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
        (t : Spec (.of R) ⟶ S), (D.baseChange t).IsEffective etaleFinitePresentation := by
  refine ⟨fun h R _ _ _ _ _ t ↦ h.baseChange t, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_fromSpecCompletedStrictLocalRing ha]
  exact fun x ↦ h _ _

/-- IX.4.6 as stated in SGA, for a base whose residue fields are perfect (e.g. of characteristic
zero): under the hypotheses of IX.4.4, with `S` locally noetherian and `X'` separated over `S'`, a
descent datum is effective iff it is effective after base change to the spectrum of every complete
noetherian local ring with algebraically closed residue field. -/
theorem DescentDatum.isEffective_iff_forall_isAlgClosed [IsLocallyNoetherian S]
    (hS : ∀ x : S, PerfectField (ResidueField (S.presheaf.stalk x)))
    (D : DescentDatum g a) (ha : etaleFinitePresentation a) [IsSeparated a] :
    D.IsEffective etaleFinitePresentation ↔
      ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
        [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
        (t : Spec (.of R) ⟶ S), (D.baseChange t).IsEffective etaleFinitePresentation := by
  refine ⟨fun h R _ _ _ _ _ t ↦ h.baseChange t, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_fromSpecCompletedStrictLocalRing ha]
  intro x
  have := hS x
  have := isAlgClosed_residueField_completedStrictLocalRing S x
  exact h _ _

end SGA.SGA1.ExposeIX
