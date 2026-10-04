/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import SGA.Foundations.ConstructibleNoetherian
import SGA.Foundations.Limits.FibrePropertiesDescent
import SGA.Foundations.Limits.SpreadingOutGluing
import SGA.Foundations.Limits.SpreadingOutNoetherian

/-!
# Constructibility of fibre properties: reduction to a generic statement

The first step of the proof of EGA IV 9.7.7. Let `Φ f s` be a property of the fibre of
`f : X ⟶ S` at `s ∈ S` which is invariant under base change (`Scheme.IsFibrePropertyInvariant`:
for a cartesian square `P = X ×_S T` and `t ∈ T`, `Φ (P ⟶ T) t ↔ Φ f (g t)`); for instance
"the fibre is geometrically connected", which only depends on the fibre up to extension of the
residue field. Assume the *generic* statement: for every noetherian domain `A` and every
`X ⟶ Spec A` of finite type, `Φ` is constant on a nonempty open subset of `Spec A`. Then for
every `f` of finite presentation the set `{s | Φ f s}` is locally constructible
(`AlgebraicGeometry.Scheme.isLocallyConstructible_setOf_of_generic`).

The proof (EGA IV 9.7.7, 9.2.3; Stacks 05F7):

* over a noetherian affine base `Spec B`, by the constructibility criterion EGA 0_III 9.2.3
  (`Topology.IsConstructible.of_noetherianSpace_of_genericPoint`): for an irreducible closed
  `Z = V(𝔭)`, base change to the noetherian domain `B / 𝔭` and apply the generic statement
  (`Scheme.isConstructible_setOf_of_isNoetherianRing`);
* over an affine base `Spec R`, by absolute noetherian approximation: `f` is the base change of
  some `X₀ ⟶ Spec B` with `B ⊆ R` of finite type over `ℤ` (EGA IV 8.8.2), and the set for `f` is the
  preimage of the set for `X₀ ⟶ Spec B` (`Scheme.isConstructible_setOf_of_affine`);
* in general, on an affine open cover.

## References

* [EGA IV₃, 9.2.3, 9.7.7][EGA4]
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- A property `Φ f s` of the fibre of `f : X ⟶ S` at `s ∈ S` is *invariant under base change*
if for every cartesian square `P = X ×_S T` (with `q : P ⟶ T`, `g : T ⟶ S`) and `t ∈ T`,
`Φ q t ↔ Φ f (g t)`: the fibre of `q` at `t` is the base change of the fibre of `f` at `g t` along
the field extension `κ(g t) ⟶ κ(t)`. -/
def Scheme.IsFibrePropertyInvariant (Φ : ∀ ⦃X S : Scheme.{u}⦄, (X ⟶ S) → S → Prop) : Prop :=
  ∀ ⦃X S T P : Scheme.{u}⦄ ⦃f : X ⟶ S⦄ ⦃g : T ⟶ S⦄ ⦃e : P ⟶ X⦄ ⦃q : P ⟶ T⦄,
    IsPullback e q f g → ∀ t : T, Φ q t ↔ Φ f (g t)

/-- Geometric connectedness of the fibres is invariant under base change. -/
theorem Scheme.isFibrePropertyInvariant_geometricallyConnected :
    Scheme.IsFibrePropertyInvariant.{u}
      fun _ _ f s ↦ GeometricallyConnected (f.fiberToSpecResidueField s) :=
  fun _ _ _ _ _ _ _ _ h t ↦ geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback h t

variable {Φ : ∀ ⦃X S : Scheme.{u}⦄, (X ⟶ S) → S → Prop}

/-- A set of points of a scheme is locally constructible if its preimages in the members of the
affine open cover are constructible. -/
lemma Scheme.isLocallyConstructible_of_affineCover {S : Scheme.{u}} {T : Set S}
    (H : ∀ i : S.affineCover.I₀, IsConstructible ((S.affineCover.f i) ⁻¹' T)) :
    IsLocallyConstructible T := by
  refine .of_isOpenCover S.affineCover.isOpenCover_opensRange fun i ↦ ?_
  have := ((H i).preimage_of_isOpenEmbedding
    (S.affineCover.f i).isoOpensRange.inv.isOpenEmbedding).isLocallyConstructible
  have key (y : (S.affineCover.f i).opensRange.toScheme) :
      (S.affineCover.f i) ((S.affineCover.f i).isoOpensRange.inv y) =
        (S.affineCover.f i).opensRange.ι y := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_inv_comp]
  convert! this
  ext x
  exact (iff_of_eq (congrArg (· ∈ T) (key x))).symm

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 9.7.7, noetherian affine case of the reduction: over a noetherian ring `B`, if `Φ` is
invariant under base change and constant on a nonempty open subset of the base for every scheme
of finite type over a noetherian domain, then `{s | Φ f s}` is constructible. -/
theorem Scheme.isConstructible_setOf_of_isNoetherianRing (hΦ : Scheme.IsFibrePropertyInvariant Φ)
    (H : ∀ ⦃A : CommRingCat.{u}⦄ [IsNoetherianRing A] [IsDomain A] ⦃X : Scheme.{u}⦄
      (f : X ⟶ Spec A) [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ U : Set (Spec A), IsOpen U ∧ U.Nonempty ∧ ((∀ s ∈ U, Φ f s) ∨ (∀ s ∈ U, ¬ Φ f s)))
    {B : CommRingCat.{u}} [IsNoetherianRing B] {X : Scheme.{u}} (f : X ⟶ Spec B)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    IsConstructible {s | Φ f s} := by
  -- on every irreducible closed `Z`, `Φ` is constant near the generic point of `Z`
  have key (Z : Set (Spec B)) (hZ : IsClosed Z) (hZi : IsIrreducible Z) :
      ∃ U : Set (Spec B), IsOpen U ∧ (U ∩ Z).Nonempty ∧
        ∀ z ∈ U ∩ Z, (Φ f z ↔ Φ f hZi.genericPoint) := by
    let η : Spec B := hZi.genericPoint
    let 𝔭 : Ideal B := η.asIdeal
    let φ : B ⟶ CommRingCat.of (B ⧸ 𝔭) := CommRingCat.ofHom (Ideal.Quotient.mk 𝔭)
    let ι : Spec (CommRingCat.of (B ⧸ 𝔭)) ⟶ Spec B := Spec.map φ
    have hφ : Function.Surjective φ.hom := Ideal.Quotient.mk_surjective
    have hι : IsClosedEmbedding ι := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hφ
    have hrange : Set.range ι = Z := by
      have hker : RingHom.ker φ.hom = 𝔭 := Ideal.mk_ker
      change Set.range (PrimeSpectrum.comap φ.hom) = Z
      rw [range_comap_of_surjective _ _ hφ, hker, ← hZi.closure_genericPoint hZ,
        PrimeSpectrum.closure_singleton]
    -- the generic point of `Spec (B / 𝔭)` maps to `η`
    let η' : Spec (CommRingCat.of (B ⧸ 𝔭)) := ⟨⊥, Ideal.isPrime_bot⟩
    have hη' : ι η' = η := by
      change PrimeSpectrum.comap φ.hom η' = η
      ext1
      change Ideal.comap (Ideal.Quotient.mk 𝔭) ⊥ = 𝔭
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    have hgen (s : Spec (CommRingCat.of (B ⧸ 𝔭))) : η' ⤳ s :=
      (PrimeSpectrum.le_iff_specializes η' s).mp bot_le
    obtain ⟨U', hU'o, ⟨s₀, hs₀⟩, hU'⟩ := H (pullback.snd f ι)
    have hη'U : η' ∈ U' := (hgen s₀).mem_open hU'o hs₀
    obtain ⟨U, hUo, rfl⟩ := hι.isInducing.isOpen_iff.mp hU'o
    have hΦ' (x : Spec (CommRingCat.of (B ⧸ 𝔭))) :
        Φ (pullback.snd f ι) x ↔ Φ f (ι x) :=
      hΦ (IsPullback.of_hasPullback f ι) x
    have hconst (x : Spec (CommRingCat.of (B ⧸ 𝔭))) (hx : x ∈ ι ⁻¹' U) :
        (Φ (pullback.snd f ι) x ↔ Φ (pullback.snd f ι) η') := by
      rcases hU' with h | h
      · exact iff_of_true (h x hx) (h η' hη'U)
      · exact iff_of_false (h x hx) (h η' hη'U)
    refine ⟨U, hUo, ⟨η, ?_, ?_⟩, ?_⟩
    · rw [← hη']
      exact hη'U
    · rw [← hrange, ← hη']
      exact Set.mem_range_self _
    · rintro z ⟨hzU, hzZ⟩
      rw [← hrange] at hzZ
      obtain ⟨x, rfl⟩ := hzZ
      rw [← hΦ' x, hconst x hzU, hΦ' η', hη']
  refine IsConstructible.of_noetherianSpace_of_genericPoint (fun Z hZ hZi hη ↦ ?_)
    (fun Z hZ hZi hη ↦ ?_)
  · obtain ⟨U, hUo, hne, hU⟩ := key Z hZ hZi
    exact ⟨U, hUo, hne, fun z hz ↦ (hU z hz).mpr hη⟩
  · obtain ⟨U, hUo, hne, hU⟩ := key Z hZ hZi
    exact ⟨U, hUo, hne, fun z hz hzΦ ↦ hη ((hU z hz).mp hzΦ)⟩

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 9.7.7, affine case of the reduction: over any affine base `Spec R`, under the
hypotheses of `Scheme.isConstructible_setOf_of_isNoetherianRing`, `{s | Φ f s}` is constructible
for `f` of finite presentation. By noetherian approximation `f` comes from some `X₀ ⟶ Spec B`,
`B ⊆ R` of finite type over `ℤ`, and the set is the preimage of the set for `X₀ ⟶ Spec B`. -/
theorem Scheme.isConstructible_setOf_of_affine (hΦ : Scheme.IsFibrePropertyInvariant Φ)
    (H : ∀ ⦃A : CommRingCat.{u}⦄ [IsNoetherianRing A] [IsDomain A] ⦃X : Scheme.{u}⦄
      (f : X ⟶ Spec A) [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ U : Set (Spec A), IsOpen U ∧ U.Nonempty ∧ ((∀ s ∈ U, Φ f s) ∨ (∀ s ∈ U, ¬ Φ f s)))
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] :
    IsConstructible {s | Φ f s} := by
  let cD := Algebra.FGSubalgebra.specCone ℤ R
  have hcD : IsLimit cD := Algebra.FGSubalgebra.isLimitSpecCone ℤ R
  let f' : X ⟶ cD.pt := f
  have : LocallyOfFinitePresentation f' := ‹LocallyOfFinitePresentation f›
  have : QuasiCompact f' := ‹QuasiCompact f›
  have : QuasiSeparated f' := ‹QuasiSeparated f›
  obtain ⟨B₀, X₀, f₀, e₀, _, _, _, h₀⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation hcD f'
  have : IsNoetherianRing (CommRingCat.of B₀.unop.1) :=
    inferInstanceAs (IsNoetherianRing B₀.unop.1)
  let f₁ : X₀ ⟶ Spec (CommRingCat.of B₀.unop.1) := f₀
  have : LocallyOfFiniteType f₁ := inferInstanceAs (LocallyOfFiniteType f₀)
  have : QuasiCompact f₁ := inferInstanceAs (QuasiCompact f₀)
  have h₁ := Scheme.isConstructible_setOf_of_isNoetherianRing hΦ H f₁
  have e : {s | Φ f s} = (cD.π.app B₀) ⁻¹' {s | Φ f₁ s} := by
    ext s
    exact hΦ h₀ s
  rw [e]
  exact (cD.π.app B₀).isConstructible_preimage h₁

/-- `Scheme.isConstructible_setOf_of_affine` for an affine base `Y` instead of `Spec R`. -/
theorem Scheme.isConstructible_setOf_of_isAffine (hΦ : Scheme.IsFibrePropertyInvariant Φ)
    (H : ∀ ⦃A : CommRingCat.{u}⦄ [IsNoetherianRing A] [IsDomain A] ⦃X : Scheme.{u}⦄
      (f : X ⟶ Spec A) [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ U : Set (Spec A), IsOpen U ∧ U.Nonempty ∧ ((∀ s ∈ U, Φ f s) ∨ (∀ s ∈ U, ¬ Φ f s)))
    {Y X : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] :
    IsConstructible {s | Φ f s} := by
  have h := Scheme.isConstructible_setOf_of_affine hΦ H (f ≫ Y.isoSpec.hom)
  have e : {s | Φ f s} = Y.isoSpec.hom ⁻¹' {t | Φ (f ≫ Y.isoSpec.hom) t} := by
    ext s
    exact hΦ (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := f) (f := f ≫ Y.isoSpec.hom)
      (g := Y.isoSpec.hom) ⟨by simp⟩) s
  rw [e]
  exact Y.isoSpec.hom.isConstructible_preimage h

/-- **EGA IV 9.7.7, reduction to the generic case** (Stacks 05F7): let `Φ` be a property of
fibres invariant under base change (`Scheme.IsFibrePropertyInvariant`), such that for every
scheme `X` of finite type over a noetherian domain `A`, `Φ` is constant on a nonempty open subset
of `Spec A`. Then for every morphism `f : X ⟶ S` of finite presentation (locally of finite
presentation, quasi-compact and quasi-separated), the set `{s | Φ f s}` is locally constructible
in `S`. -/
theorem Scheme.isLocallyConstructible_setOf_of_generic (hΦ : Scheme.IsFibrePropertyInvariant Φ)
    (H : ∀ ⦃A : CommRingCat.{u}⦄ [IsNoetherianRing A] [IsDomain A] ⦃X : Scheme.{u}⦄
      (f : X ⟶ Spec A) [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ U : Set (Spec A), IsOpen U ∧ U.Nonempty ∧ ((∀ s ∈ U, Φ f s) ∨ (∀ s ∈ U, ¬ Φ f s)))
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] :
    IsLocallyConstructible {s | Φ f s} := by
  refine Scheme.isLocallyConstructible_of_affineCover fun i ↦ ?_
  have e : (S.affineCover.f i) ⁻¹' {s | Φ f s} =
      {t | Φ (pullback.snd f (S.affineCover.f i)) t} := by
    ext t
    exact (hΦ (IsPullback.of_hasPullback f (S.affineCover.f i)) t).symm
  rw [e]
  exact Scheme.isConstructible_setOf_of_isAffine hΦ H (pullback.snd f (S.affineCover.f i))

end AlgebraicGeometry
