/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import SGA.SGA1.ExposeVIII.MorphismDescent

/-!
# SGA 1, Exposé VIII, §6: application to finite and quasi-finite morphisms

SGA proves VIII.6.1 (a proper morphism with finite fibers is finite) and VIII.6.2 (a quasi-finite
separated morphism is quasi-affine) over a locally noetherian base, by descent to a complete local
base. Mathlib proves Zariski's Main Theorem in Grothendieck's form without noetherian hypotheses:
for `f` quasi-finite and separated, `X ⟶ f.normalization` is an open immersion and
`f.normalization ⟶ Y` is integral. We deduce VIII.6.1 and VIII.6.2 from it, with no noetherian or
finite presentation hypothesis; this also covers VIII.6.6.

* VIII.6.2 is proved in the form "quasi-affine morphism" (`isQuasiAffineHom_of_quasiFinite`),
  hence quasi-projective.
* VIII.6.4 is proved over an affine base (`exists_isOpenImmersion_isFinite_of_isAffine`, no
  noetherian hypothesis), and in general with "integral" in place of "finite"; the statement for a
  noetherian base is recorded as `QuasiFiniteOpenInFiniteStatement` and proved in
  `SGA.SGA1.ExposeVIII.QuasiFiniteOpenInFinite` (`quasiFiniteOpenInFiniteStatement`).
* VIII.6.5 is stated, for the property "finite", as `IsFiniteSpreadingOutStatement`; the
  direction from a neighbourhood to the local scheme is proved here, and the converse (EGA IV
  8.10.5) in `SGA.SGA1.ExposeVIII.FiniteSpreadingOut` (`isFiniteSpreadingOutStatement`).
* "Quasi-finite" is taken in SGA's sense: of finite type with finite fibers. In mathlib terms this
  is `LocallyOfFiniteType`, `QuasiCompact` and `LocallyQuasiFinite`.
-/

universe u

namespace SGA.SGA1.ExposeVIII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

section FiniteSubalgebra

/-- Let `B` be integral over `A`, and `s` a finite subset of `B` such that each localization
`B_b`, `b ∈ s`, is of finite type over `A`. Then there is a finite `A`-subalgebra `B'` of `B`
containing `s` such that `B'_b = B_b` for every `b ∈ s`. -/
lemma exists_finite_subalgebra_isLocalization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) (L : B → Type u)
    [∀ b, CommRing (L b)] [∀ b, Algebra B (L b)] [∀ b, IsLocalization.Away b (L b)]
    [∀ b, Algebra A (L b)] [∀ b, IsScalarTower A B (L b)]
    (hL : ∀ b ∈ s, Algebra.FiniteType A (L b)) :
    ∃ B' : Subalgebra A B, Module.Finite A B' ∧ ∃ hs : ∀ b ∈ s, b ∈ B',
      ∀ b (hb : b ∈ s), IsLocalization.Away (⟨b, hs b hb⟩ : B') (L b) := by
  classical
  choose G hG using fun b (hb : b ∈ s) ↦ (hL b hb).out
  choose n c hc using fun (b : B) (z : L b) ↦ IsLocalization.Away.surj b z
  let T : Set B := (s : Set B) ∪ ⋃ (b) (hb : b ∈ s), (fun z ↦ c b z) '' (G b hb : Set (L b))
  have hT : T.Finite := (s.finite_toSet).union <| s.finite_toSet.biUnion' fun b hb ↦
    (G b hb).finite_toSet.image _
  refine ⟨Algebra.adjoin A T, ?_, fun b hb ↦ Algebra.subset_adjoin (Or.inl hb), fun b hb ↦ ?_⟩
  · exact Module.Finite.iff_fg.mpr
      (fg_adjoin_of_finite hT fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  set B' := Algebra.adjoin A T
  have hb' : b ∈ B' := Algebra.subset_adjoin (Or.inl hb)
  have halg (x : B') : algebraMap B' (L b) x = algebraMap B (L b) x.1 := rfl
  -- every element of `L b` is of the form `c / bⁿ` with `c ∈ B'`
  have key : ∀ z : L b, ∃ (m : ℕ) (d : B'),
      z * algebraMap B (L b) b ^ m = algebraMap B (L b) d := by
    intro z
    have hz : z ∈ Algebra.adjoin A (G b hb : Set (L b)) := by rw [hG b hb]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      refine ⟨n b z, ⟨c b z, Algebra.subset_adjoin (Or.inr ?_)⟩, hc b z⟩
      exact Set.mem_iUnion₂.mpr ⟨b, hb, z, hz, rfl⟩
    | algebraMap a =>
      refine ⟨0, algebraMap A B' a, ?_⟩
      simp [IsScalarTower.algebraMap_apply A B (L b)]
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, d₁, e₁⟩ := h₁
      obtain ⟨m₂, d₂, e₂⟩ := h₂
      refine ⟨m₁ + m₂, d₁ * ⟨b, hb'⟩ ^ m₂ + d₂ * ⟨b, hb'⟩ ^ m₁, ?_⟩
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, map_add, map_mul,
        map_pow, ← e₁, ← e₂]
      ring
    | mul z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, d₁, e₁⟩ := h₁
      obtain ⟨m₂, d₂, e₂⟩ := h₂
      refine ⟨m₁ + m₂, d₁ * d₂, ?_⟩
      simp only [Subalgebra.coe_mul, map_mul, ← e₁, ← e₂]
      ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    rw [halg]
    exact IsLocalization.map_units (L b) (⟨b ^ m, m, rfl⟩ : Submonoid.powers b)
  · intro z
    obtain ⟨m, d, e⟩ := key z
    refine ⟨⟨d, ⟨⟨b, hb'⟩ ^ m, m, rfl⟩⟩, ?_⟩
    change z * algebraMap B (L b) (b ^ m) = algebraMap B (L b) d
    rw [map_pow]
    exact e
  · intro x y e
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) e
    exact ⟨⟨⟨b, hb'⟩ ^ m, m, rfl⟩, Subtype.ext hm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Let `p : N ⟶ Y` be an integral morphism of affine schemes and `U` a quasi-compact open subset
of `N` such that `U ⟶ Y` is locally of finite type. Then `p` factors as `N ⟶ Z ⟶ Y` with
`Z ⟶ Y` finite and `U ⟶ Z` an open immersion. -/
lemma exists_isFinite_isOpenImmersion_of_isIntegralHom {N Y : Scheme.{u}} [IsAffine N]
    [IsAffine Y] (p : N ⟶ Y) [IsIntegralHom p] (U : N.Opens) (hU : IsCompact (U : Set N))
    [LocallyOfFiniteType (U.ι ≫ p)] :
    ∃ (Z : Scheme.{u}) (ψ : N ⟶ Z) (q : Z ⟶ Y), IsFinite q ∧ ψ ≫ q = p ∧
      IsOpenImmersion (U.ι ≫ ψ) := by
  let : Algebra Γ(Y, ⊤) Γ(N, ⊤) := p.appTop.hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, ⊤) Γ(N, ⊤) :=
    ⟨((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp ‹_›).2⟩
  -- a finite covering of `U` by basic open subsets of `N` contained in `U`
  obtain ⟨s, hsU, hUs⟩ : ∃ s : Finset Γ(N, ⊤), (∀ b ∈ s, N.basicOpen b ≤ U) ∧
      (U : Set N) ⊆ ⋃ b ∈ s, (N.basicOpen b : Set N) := by
    have H : ∀ x ∈ (U : Set N), ∃ b : Γ(N, ⊤), x ∈ N.basicOpen b ∧ N.basicOpen b ≤ U :=
      fun x hx ↦ by
        obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hxb, hbU⟩ :=
          (isBasis_basicOpen N).exists_subset_of_mem_open hx U.2
        exact ⟨b, hxb, hbU⟩
    choose! b hb hbU using H
    obtain ⟨t, htU, ht⟩ := hU.elim_nhds_subcover (fun x ↦ (N.basicOpen (b x) : Set N))
      fun x hx ↦ (N.basicOpen (b x)).2.mem_nhds (hb x hx)
    classical
    refine ⟨t.image b, fun c hc ↦ ?_, fun x hx ↦ ?_⟩
    · obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.mp hc
      exact hbU _ (htU x hxt)
    · obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact Set.mem_biUnion (Finset.mem_image_of_mem _ hyt) hxy
  -- the localizations `Γ(N, N_b)`, `b ∈ s`, are of finite type over `Γ(Y, ⊤)`
  let L : Γ(N, ⊤) → Type u := fun b ↦ Γ(N, N.basicOpen b)
  let _ (b : Γ(N, ⊤)) : Algebra Γ(Y, ⊤) (L b) :=
    ((algebraMap Γ(N, ⊤) (L b)).comp (algebraMap Γ(Y, ⊤) Γ(N, ⊤))).toAlgebra
  have _ (b : Γ(N, ⊤)) : IsScalarTower Γ(Y, ⊤) Γ(N, ⊤) (L b) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hL (b) (hb : b ∈ s) : Algebra.FiniteType Γ(Y, ⊤) (L b) := by
    have hbU := hsU b hb
    have hV : IsAffineOpen (U.ι ⁻¹ᵁ N.basicOpen b) := by
      rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, inf_eq_right.mpr hbU]
      exact (isAffineOpen_top N).basicOpen b
    have hft := (U.ι ≫ p).finiteType_appLE (isAffineOpen_top Y) hV le_top
    have : IsIso (U.ι.app (N.basicOpen b)) := U.ι.isIso_app _ (by simpa using hbU)
    have e : (U.ι ≫ p).appLE ⊤ (U.ι ⁻¹ᵁ N.basicOpen b) le_top =
        (p.appTop ≫ N.presheaf.map (homOfLE le_top).op) ≫ U.ι.app (N.basicOpen b) := by
      rw [Scheme.Hom.comp_appLE, U.ι.app_eq_appLE, Category.assoc, Scheme.Hom.map_appLE]
      rfl
    rw [e] at hft
    have := (RingHom.FiniteType.of_surjective (inv (U.ι.app (N.basicOpen b))).hom
      fun y ↦ ⟨(U.ι.app (N.basicOpen b)).hom y, by
        rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]⟩).comp hft
    rw [← CommRingCat.hom_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this
    exact this
  obtain ⟨B', hfin, hs', hloc⟩ := exists_finite_subalgebra_isLocalization s L hL
  let ι' : CommRingCat.of B' ⟶ Γ(N, ⊤) := CommRingCat.ofHom B'.val.toRingHom
  refine ⟨Spec (CommRingCat.of B'), N.isoSpec.hom ≫ Spec.map ι',
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B')) ≫ Y.isoSpec.inv, ?_, ?_, ?_⟩
  · have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B'))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
    infer_instance
  · have : CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B') ≫ ι' = p.appTop := by ext; rfl
    rw [Category.assoc, ← Spec.map_comp_assoc, this, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  -- `U ⟶ Spec B'` is an open immersion on each `N_b`, `b ∈ s`, and injective
  have key (b) (hb : b ∈ s) :
      IsOpenImmersion ((N.basicOpen b).ι ≫ N.isoSpec.hom ≫ Spec.map ι') := by
    have := hloc b hb
    have hba : IsAffineOpen (N.basicOpen b) := (isAffineOpen_top N).basicOpen b
    have e : (N.basicOpen b).ι ≫ N.isoSpec.hom ≫ Spec.map ι' =
        hba.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B' (L b))) := by
      rw [Scheme.isoSpec_hom, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc,
        IsAffineOpen.isoSpec_hom, ← Spec.map_comp]
      rfl
    rw [e]
    have := IsOpenImmersion.of_isLocalization (S := L b) (⟨b, hs' b hb⟩ : B')
    infer_instance
  have hpre (b) (hb : b ∈ s) :
      (N.isoSpec.hom ≫ Spec.map ι') ⁻¹ᵁ PrimeSpectrum.basicOpen (⟨b, hs' b hb⟩ : B') =
        N.basicOpen b := by
    rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
      Scheme.map_PrimeSpectrum_basicOpen_of_affine]
    rfl
  refine IsOpenImmersion.of_forall_source_exists _ (fun x y e ↦ ?_) fun x ↦ ?_
  · obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hUs x.2)
    have hpre' (z : N) : (N.isoSpec.hom ≫ Spec.map ι') z ∈
        PrimeSpectrum.basicOpen (⟨b, hs' b hb⟩ : B') ↔ z ∈ N.basicOpen b := by
      rw [← hpre b hb]
      rfl
    have hyb : U.ι y ∈ N.basicOpen b := by
      refine (hpre' _).mp ?_
      rw [← Scheme.Hom.comp_apply, ← e, Scheme.Hom.comp_apply]
      exact (hpre' _).mpr hxb
    have := key b hb
    have := ((N.basicOpen b).ι ≫ N.isoSpec.hom ≫ Spec.map ι').isOpenEmbedding.injective
      (a₁ := ⟨x.1, hxb⟩) (a₂ := ⟨y.1, hyb⟩) (by simp only [Scheme.Hom.comp_apply]; exact e)
    exact Subtype.ext (Subtype.mk.inj this)
  · obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hUs x.2)
    refine ⟨N.basicOpen b, N.homOfLE (hsU b hb), inferInstance,
      ⟨⟨x.1, hxb⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩, ?_⟩
    rw [Scheme.homOfLE_ι_assoc]
    exact key b hb

end FiniteSubalgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- VIII.6.1 (and VIII.6.6): a proper morphism with finite fibers is finite. No noetherian
hypothesis is needed (mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_of_isProper_of_finite_preimage_singleton [IsProper f]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) : IsFinite f :=
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton f hf
  .of_isProper_of_locallyQuasiFinite f

variable [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f]

/-- VIII.6.4 with "integral" for "finite" (Zariski's Main Theorem, mathlib): a quasi-finite
separated morphism `f : X ⟶ Y` factors as an open immersion `X ⟶ Z` followed by an integral
morphism `Z ⟶ Y`. No noetherian hypothesis is needed. -/
theorem exists_isOpenImmersion_isIntegralHom :
    ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), IsOpenImmersion i ∧ IsIntegralHom p ∧ i ≫ p = f :=
  ⟨_, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    f.toNormalization_fromNormalization⟩

set_option backward.isDefEq.respectTransparency.types false in
include f in
/-- VIII.6.2 over an affine base: a quasi-finite separated morphism to an affine scheme has a
quasi-affine source. -/
theorem isQuasiAffine_of_quasiFinite [IsAffine Y] : X.IsQuasiAffine := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  exact .of_isImmersion f.toNormalization

set_option backward.isDefEq.respectTransparency.types false in
/-- For a quasi-finite separated morphism `f : X ⟶ Y`, the inverse image of every affine open
subset of `Y` is quasi-affine. -/
theorem isQuasiAffine_preimage_of_quasiFinite {V : Y.Opens} (hV : IsAffineOpen V) :
    (f ⁻¹ᵁ V).toScheme.IsQuasiAffine :=
  have : IsAffine V := hV
  isQuasiAffine_of_quasiFinite (f ∣_ V)

/-- VIII.6.2 (and VIII.6.6): a quasi-finite separated morphism is quasi-affine. No noetherian
hypothesis is needed. -/
theorem isQuasiAffineHom_of_quasiFinite : IsQuasiAffineHom f :=
  ⟨fun _ hV ↦ isQuasiAffine_preimage_of_quasiFinite f hV⟩

/-- VIII.6.2: a quasi-finite separated morphism is quasi-affine, "a fortiori quasi-projective". -/
theorem isQuasiProjective_of_quasiFinite : IsQuasiProjective f :=
  have := isQuasiAffineHom_of_quasiFinite f
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- VIII.6.4 over an affine base: a quasi-finite separated morphism `f : X ⟶ Y` with `Y` affine
factors as an open immersion followed by a finite morphism. No noetherian hypothesis is needed.
By Zariski's Main Theorem (mathlib), `X` is an open subscheme of the normalization `N` of `Y` in
`X`, which is integral over `Y`; `X` is then also open in `Spec B'` for a finite subalgebra `B'`
of `Γ(N, 𝒪_N)` (`exists_isFinite_isOpenImmersion_of_isIntegralHom`). -/
theorem exists_isOpenImmersion_isFinite_of_isAffine [IsAffine Y] :
    ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), IsOpenImmersion i ∧ IsFinite p ∧ i ≫ p = f := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let U := f.toNormalization.opensRange
  have hU : IsCompact (U : Set f.normalization) := by
    simpa [U] using isCompact_range f.toNormalization.continuous
  have : LocallyOfFiniteType (U.ι ≫ f.fromNormalization) := by
    rw [← f.toNormalization.isoOpensRange_inv_comp, Category.assoc,
      f.toNormalization_fromNormalization]
    infer_instance
  obtain ⟨Z, ψ, q, hq, hψq, hψ⟩ :=
    exists_isFinite_isOpenImmersion_of_isIntegralHom f.fromNormalization U hU
  refine ⟨Z, f.toNormalization ≫ ψ, q, ?_, hq, by
    rw [Category.assoc, hψq, f.toNormalization_fromNormalization]⟩
  rw [← f.toNormalization.isoOpensRange_hom_ι, Category.assoc]
  infer_instance

/-- VIII.6.4: a quasi-finite separated morphism `f : X ⟶ Y` with `Y` noetherian factors as an
open immersion followed by a finite morphism. SGA deduces it from VIII.6.2 and the global form of
Zariski's Main Theorem (EGA III 4.4.3). The case of an affine `Y` (without noetherian hypothesis)
is `exists_isOpenImmersion_isFinite_of_isAffine`; the general case glues the finite subalgebras
chosen over the members of an affine covering of `Y` into a finite quasi-coherent subalgebra of the
normalization (EGA I 9.4.7). Proved in `SGA.SGA1.ExposeVIII.quasiFiniteOpenInFiniteStatement`. -/
def QuasiFiniteOpenInFiniteStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyQuasiFinite f] [IsSeparated f],
    ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), IsOpenImmersion i ∧ IsFinite p ∧ i ≫ p = f

omit [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f]

/-- VIII.6.5, for the property "finite": for `X` of finite type over a locally noetherian `Y` and
`y ∈ Y`, `X` is finite over a neighbourhood of `y` iff `X ×_Y Spec 𝒪_{Y,y}` is finite over
`Spec 𝒪_{Y,y}` (EGA IV 8). Proved in `SGA.SGA1.ExposeVIII.isFiniteSpreadingOutStatement`. -/
def IsFiniteSpreadingOutStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [QuasiCompact f] (y : Y),
    (∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U)) ↔ IsFinite (pullback.snd f (Y.fromSpecStalk y))

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.6.5, the easy direction: if `X` is finite over a neighbourhood `U` of `y`, then
`X ×_Y Spec 𝒪_{Y,y}` is finite over `Spec 𝒪_{Y,y}`. -/
theorem isFinite_pullback_fromSpecStalk {y : Y} {U : Y.Opens} (hy : y ∈ U)
    [IsFinite (f ∣_ U)] : IsFinite (pullback.snd f (Y.fromSpecStalk y)) := by
  have hsub : Set.range (Y.fromSpecStalk y) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun z hz ↦ hz.mem_open U.isOpen hy
  let k := IsOpenImmersion.lift U.ι (Y.fromSpecStalk y) hsub
  have hk : k ≫ U.ι = Y.fromSpecStalk y := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (pullback.fst f (Y.fromSpecStalk y)) (pullback.snd f (Y.fromSpecStalk y))
      f (k ≫ U.ι) := hk ▸ IsPullback.of_hasPullback f _
  have R := isPullback_morphismRestrict f U
  let l := R.lift (pullback.snd f (Y.fromSpecStalk y) ≫ k) (pullback.fst f (Y.fromSpecStalk y))
    (by simpa using sq.w.symm)
  have sq' : IsPullback l (pullback.snd f (Y.fromSpecStalk y)) (f ∣_ U) k :=
    IsPullback.of_right (by rw [R.lift_snd]; exact sq) (R.lift_fst _ _ _) R.flip
  exact MorphismProperty.of_isPullback sq' ‹_›

end SGA.SGA1.ExposeVIII
