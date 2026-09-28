/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.HenselianDegree
import SGA.Foundations.HenselianFinite
import SGA.Foundations.Limits.BaseChange
import SGA.Foundations.Limits.GeometricFiberCard
import SGA.Foundations.Limits.SpecFibre
import SGA.Foundations.StrictLocalization
import SGA.SGA1.ExposeI.NormalCoverings
import SGA.SGA1.ExposeI.SeparableDegreeFibre
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeVIII.MorphismDescent

/-!
# SGA 1, Exposé I, I.10.7–I.10.12: the geometric number of points

SGA's `n(y)` (`geometricFiberCard`) is the sum of the separable degrees `[κ(x) : κ(y)]_s` over the
fibre, i.e. the number of points of the geometric fibre
(`AlgebraicGeometry.Scheme.Hom.natCard_pointsOver`). EGA IV 15.5.1 is proved in
`SGA.Foundations.Limits.GeometricFiberCard` by induction on `n`, passing from `X ⟶ Y` to the
complement of the diagonal `X ×_Y X ∖ Δ ⟶ X`, whose geometric number of points is `n - 1`. This
gives I.10.7 (lower semicontinuity, and finiteness where `n` is locally constant), I.10.9 and
I.10.10.

I.10.8, I.10.11 and I.10.12 are proved through the strict localization `Spec 𝒪^{sh}_{Y,ȳ}`, a
domain when `Y` is geometrically unibranch at `y` (`isDomain_strictHenselization`) and a normal
domain when `Y` is normal there (`isDomain_and_isIntegrallyClosed_strictHenselization`, EGA IV
18.8.12). Over it, a quasi-finite scheme splits around the closed fibre into clopen pieces with
one point over the closed point (Stacks 04GG, 04GJ,
`AlgebraicGeometry.exists_isClopen_of_locallyQuasiFinite`):
* I.10.8 (`disjoint_irreducibleComponents`), for which SGA gives no proof: counting the points of
  the pieces over the generic point;
* I.10.12 (`separableDegree_fiber_le`), for any residue field: over `𝒪^{sh}`, the pieces of
  `𝒪^{sh} ⊗ B` of rank one are `𝒪^{sh}` (`IsLocalRing.card_algHom_eq_finrank_iff_etale`), instead
  of SGA's reduction to an infinite residue field through `A(t)`;
* I.10.11 (`geometricFiberCard_le_fiberDegree_and_iff`): `n(y) ≤ n(z) ≤ n` for the generic point
  `z` (which replaces Chevalley's criterion for universal openness), and if `n(y) = n` then `X`
  is finite over `Spec 𝒪_{Y,y}` (faithfully flat descent) and étale by I.10.12; the limit theorem
  for étale coverings spreads this out to a neighbourhood of `y`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma geometricFiberCard_eq (y : Y) : geometricFiberCard f y = f.geometricFiberCard y := rfl

/-- I.10.7, first assertion (lower semicontinuity; see
`geometricFiberCard_upperSemicontinuous_Statement` for the direction): for `f` separated,
universally open and quasi-finite, every `y` has a neighbourhood on which `n(y) ≤ n(y')`. -/
theorem exists_le_geometricFiberCard [LocallyQuasiFinite f] [QuasiCompact f] [IsSeparated f]
    [UniversallyOpen f] (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y ≤ geometricFiberCard f y' :=
  ⟨⟨_, f.isOpen_setOf_le_geometricFiberCard (f.geometricFiberCard y)
    f.finite_preimage_singleton⟩, (le_refl (f.geometricFiberCard y) :), fun _ h ↦ h⟩

/-- I.10.7, second assertion: if `n` is constant near `y`, then `f` is finite over a neighbourhood
of `y`. -/
theorem exists_isFinite_morphismRestrict_of_geometricFiberCard [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f] [UniversallyOpen f] (y : Y)
    (h : ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y' = geometricFiberCard f y) :
    ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) := by
  obtain ⟨U, hyU, hU⟩ := h
  exact ⟨U, hyU, f.isFinite_morphismRestrict_of_geometricFiberCard_eq U _ hU⟩

/-- I.10.7 (EGA IV 15.5.1). -/
theorem geometricFiberCard_upperSemicontinuous_Statement_holds :
    geometricFiberCard_upperSemicontinuous_Statement.{u} := fun _ _ f _ _ _ _ _ ↦
  ⟨exists_le_geometricFiberCard f, exists_isFinite_morphismRestrict_of_geometricFiberCard f⟩

/-- I.10.9: for a separated étale quasi-compact `f`, `n` is constant near `y` iff `f` is an étale
covering (finite) over a neighbourhood of `y`. -/
theorem exists_geometricFiberCard_eq_iff [Etale f] [IsSeparated f] [QuasiCompact f] (y : Y) :
    (∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y' = geometricFiberCard f y) ↔
      ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) := by
  refine ⟨exists_isFinite_morphismRestrict_of_geometricFiberCard f y, ?_⟩
  rintro ⟨U, hyU, hU⟩
  have hc := (f ∣_ U).isLocallyConstant_geometricFiberCard
  have ho : IsOpen ((f ∣_ U).geometricFiberCard ⁻¹' {(f ∣_ U).geometricFiberCard ⟨y, hyU⟩}) :=
    hc.isOpen_fiber _
  refine ⟨⟨U.ι '' _, U.ι.isOpenMap _ ho⟩, ⟨⟨y, hyU⟩, rfl, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  have e := f.geometricFiberCard_morphismRestrict f.finite_preimage_singleton U
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy'
  rw [geometricFiberCard_eq, geometricFiberCard_eq]
  change f.geometricFiberCard y'.1 = _
  rw [← e y', hy', e]

/-- I.10.9 (EGA IV 15.5.1). -/
theorem geometricFiberCard_etale_Statement_holds : geometricFiberCard_etale_Statement.{u} :=
  fun _ _ f _ _ _ ↦ ⟨exists_le_geometricFiberCard f, exists_geometricFiberCard_eq_iff f⟩

/-- I.10.10: a separated étale quasi-compact morphism to a connected scheme is finite iff all its
fibres have the same geometric number of points. -/
theorem isFinite_iff_geometricFiberCard_eq [Etale f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace Y] :
    IsFinite f ↔ ∀ y y', geometricFiberCard f y = geometricFiberCard f y' := by
  refine ⟨fun _ y y' ↦ f.isLocallyConstant_geometricFiberCard.apply_eq_of_preconnectedSpace y y',
    fun h ↦ ?_⟩
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  exact f.isFinite_of_geometricFiberCard_eq (f.geometricFiberCard y₀) fun y ↦ h y y₀

/-- I.10.10. -/
theorem isFinite_iff_geometricFiberCard_const_Statement_holds :
    isFinite_iff_geometricFiberCard_const_Statement.{u} :=
  fun _ _ f _ _ _ _ ↦ isFinite_iff_geometricFiberCard_eq f

section StrictHenselization

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R] (K : Type u) [Field K]
  [Algebra R K] [IsLocalHom (algebraMap R K)]

/-- I.11 (EGA IV 18.8.15): the strict henselization of a geometrically unibranch local domain is
a domain. It is the filtered colimit of the local rings of étale `R`-algebras at points over the
maximal ideal, which are domains (EGA IV 18.10,
`isDomain_localization_of_etale_of_isGeometricallyUnibranch`). -/
theorem isDomain_strictHenselization (hR : IsGeometricallyUnibranch R) :
    IsDomain (StrictHenselization R K) := by
  have hdom (N : EtaleNbhd R K) : IsDomain N.Stalk := by
    refine isDomain_localization_of_etale_of_isGeometricallyUnibranch hR N.pair.Ring N.prime ?_
    ext r
    rw [Ideal.mem_comap, EtaleNbhd.mem_prime, AlgHom.commutes]
    constructor
    · intro h
      by_contra hr
      have hu : IsUnit r := (IsLocalRing.notMem_maximalIdeal).mp hr
      exact (hu.map (algebraMap R K)).ne_zero h
    · intro hr
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal r).mp hr
        (isUnit_of_map_unit (algebraMap R K) r (isUnit_iff_ne_zero.mpr h))
  exact StrictHenselization.isDomain_of_forall hdom

omit [IsLocalRing R] [IsLocalHom (algebraMap R K)] in
/-- EGA IV 18.8.12: the strict henselization of an integrally closed local domain is an
integrally closed domain: it is a filtered colimit of local rings of étale algebras, which are
integrally closed domains (I.9.5(i), `isDomain_and_isIntegrallyClosed_localization_of_etale`). -/
theorem isDomain_and_isIntegrallyClosed_strictHenselization [IsIntegrallyClosed R] :
    IsDomain (StrictHenselization R K) ∧ IsIntegrallyClosed (StrictHenselization R K) := by
  have h (N : EtaleNbhd R K) : IsDomain N.Stalk ∧ IsIntegrallyClosed N.Stalk :=
    isDomain_and_isIntegrallyClosed_localization_of_etale (A := R) (B := N.pair.Ring) N.prime
  exact ⟨StrictHenselization.isDomain_of_forall fun N ↦ (h N).1,
    StrictHenselization.isIntegrallyClosed_of_forall h⟩

end StrictHenselization

section Disjoint

open IsLocalRing Limits

set_option backward.isDefEq.respectTransparency false in
/-- The residue field of the spectrum of a strictly henselian local ring at its closed point is
separably closed. -/
lemma isSepClosed_residueField_closedPoint (A : CommRingCat.{u}) [IsStrictlyHenselian A]
    (w : Spec A) (hw : w = closedPoint A) : IsSepClosed ((Spec A).residueField w) := by
  subst hw
  have e₁ : ResidueField A ≃+* (maximalIdeal A).ResidueField :=
    RingEquiv.ofBijective (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  have : IsSepClosed (maximalIdeal A).ResidueField := IsSepClosed.of_ringEquiv e₁
  let e₂ : (maximalIdeal A).ResidueField ≃+* (Spec A).residueField (closedPoint A) :=
    (Scheme.Spec.residueFieldIso A (closedPoint A)).commRingCatIsoToRingEquiv.symm
  exact IsSepClosed.of_ringEquiv e₂

set_option backward.isDefEq.respectTransparency false in
/-- **I.10.8**: let `f : X ⟶ Y` be quasi-finite, separated, universally open and of finite type,
with `Y` geometrically unibranch and `n(y)` constant. Then the irreducible components of `X` are
pairwise disjoint.

SGA gives no proof. By I.10.7 `f` is finite. If two components meet at `x` over `y`, pass to the
strict localization `Y' = Spec 𝒪^{sh}_{Y,ȳ}`, a domain as `Y` is geometrically unibranch. Over the
henselian `Y'`, `X' = X ×_Y Y'` is a disjoint union of clopen pieces, each with a single point
over the closed point `y'` (`AlgebraicGeometry.exists_isClopen_of_isFinite`); each piece maps
onto `Y'` (the map is open), and since `n(y') = n(η')` for the generic point `η'` each piece has a
single point over `η'`. Lifting the generic points of the two components through the flat
`X' ⟶ X` into the piece through a point over `x` shows that they are both specializations of the
image of this single point, hence equal. -/
theorem disjoint_irreducibleComponents {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f] [UniversallyOpen f]
    (hY : IsGeometricallyUnibranchScheme Y)
    (hn : ∀ y y', geometricFiberCard f y = geometricFiberCard f y') {Z₁ Z₂ : Set X}
    (hZ₁ : Z₁ ∈ irreducibleComponents X) (hZ₂ : Z₂ ∈ irreducibleComponents X) (hne : Z₁ ≠ Z₂) :
    Disjoint Z₁ Z₂ := by
  rw [Set.disjoint_iff]
  rintro x ⟨hx₁, hx₂⟩
  let y := f x
  have : IsFinite f := f.isFinite_of_geometricFiberCard_eq (f.geometricFiberCard y) fun y' ↦ hn y' y
  -- the strict localization of `Y` at `y`
  let ξ := Y.fromSpecAlgClosure y
  have hξ : ξ.imagePoint = y := Scheme.fromSpecAlgClosure_apply Y y
  obtain ⟨_, hunib⟩ := hY ξ.imagePoint
  let A' := ξ.strictLocalization
  let := ξ.residueFieldAlgebra
  let := ξ.stalkAlgebra
  have := ξ.isScalarTower_stalkAlgebra
  have := isLocalHom_algebraMap_of_isScalarTower (R := Y.presheaf.stalk ξ.imagePoint)
    (K := AlgebraicClosure (Y.residueField y))
  have : IsDomain A' := isDomain_strictHenselization _ hunib
  let g := ξ.fromSpecStrictLocalization
  have : Flat g := by
    have : Flat (Spec.map ξ.toStrictLocalization) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.mpr
        (inferInstance : Module.Flat (Y.presheaf.stalk ξ.imagePoint) A')
    exact inferInstanceAs (Flat (Spec.map ξ.toStrictLocalization ≫ Y.fromSpecStalk ξ.imagePoint))
  let y' := closedPoint A'
  have hgy' : g y' = y := (ξ.fromSpecStrictLocalization_closedPoint).trans hξ
  let η' := genericPoint (Spec A')
  -- the base change `f' : X' ⟶ Y'`
  let f' := pullback.snd f g
  let g' := pullback.fst f g
  have hpb := IsPullback.of_hasPullback f g
  have : Flat g' := MorphismProperty.pullback_fst _ _ ‹Flat g›
  have hn' (w : Spec A') : f'.geometricFiberCard w = f.geometricFiberCard y := by
    rw [Scheme.Hom.geometricFiberCard_of_isPullback f f.finite_preimage_singleton hpb]
    exact hn _ _
  have hfin (w : Spec A') : (f' ⁻¹' {w}).Finite := f'.finite_preimage_singleton w
  -- the pieces of `X'` over `y'`
  let F' := f' ⁻¹' {y'}
  have hU (a : F') : ∃ U : Set ↥(pullback f g), IsClopen U ∧ a.1 ∈ U ∧
      ∀ z ∈ U, f' z = y' → z = a.1 :=
    exists_isClopen_of_isFinite f' a.1 a.2
  choose U hUc haU hUF using hU
  have hdisj (a b : F') (z : ↥(pullback f g)) (hza : z ∈ U a) (hzb : z ∈ U b) : a = b := by
    have hC : IsClosed (f' '' (U a ∩ U b)) := f'.isClosedMap _ ((hUc a).1.inter (hUc b).1)
    obtain ⟨c, ⟨hca, hcb⟩, hc⟩ : y' ∈ f' '' (U a ∩ U b) :=
      (specializes_closedPoint (f' z)).mem_closed hC ⟨z, ⟨hza, hzb⟩, rfl⟩
    exact Subtype.ext ((hUF a c hca hc).symm.trans (hUF b c hcb hc))
  have hgen (a : F') : ∃ w ∈ U a, f' w = η' := by
    have ho : IsOpen (f' '' U a) := f'.isOpenMap _ (hUc a).2
    obtain ⟨w, hw, hw'⟩ := (genericPoint_specializes (f' a.1)).mem_open ho ⟨a.1, haU a, rfl⟩
    exact ⟨w, hw, hw'⟩
  choose w hwU hwη using hgen
  -- each piece has a single point over `η'`
  have huniq (a : F') (w₁ w₂ : ↥(pullback f g)) (h₁ : w₁ ∈ U a) (h₂ : w₂ ∈ U a) (e₁ : f' w₁ = η')
      (e₂ : f' w₂ = η') : w₁ = w₂ := by
    by_contra hne
    obtain ⟨v, hv, hvη, hvne⟩ : ∃ v ∈ U a, f' v = η' ∧ v ≠ w a := by
      by_cases h : w₁ = w a
      · exact ⟨w₂, h₂, e₂, fun h' ↦ hne (h.trans h'.symm)⟩
      · exact ⟨w₁, h₁, e₁, h⟩
    let ι : F' → f' ⁻¹' {η'} := fun b ↦ ⟨w b, hwη b⟩
    have hinj : Function.Injective ι := fun b c hbc ↦
      hdisj b c (w b) (hwU b) (by rw [show w b = w c from congrArg Subtype.val hbc]; exact hwU c)
    have hnot : (⟨v, hvη⟩ : f' ⁻¹' {η'}) ∉ Set.range ι := by
      rintro ⟨b, hb⟩
      have hb' : w b = v := congrArg Subtype.val hb
      obtain rfl := hdisj b a v (hb' ▸ hwU b) hv
      exact hvne hb'.symm
    have : Fintype (f' ⁻¹' {η'}) := (hfin η').fintype
    have : Fintype F' := (hfin y').fintype
    have hlt := Fintype.card_lt_of_injective_of_notMem ι hinj hnot
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hlt
    have : IsStrictlyHenselian A' := inferInstance
    have : IsSepClosed ((Spec A').residueField y') :=
      isSepClosed_residueField_closedPoint A' y' rfl
    have h₁ := f'.geometricFiberCard_eq_natCard y' (hfin y')
    have h₂ := f'.natCard_preimage_le_geometricFiberCard η' (hfin η')
    rw [hn'] at h₁ h₂
    change Nat.card ↑(f' ⁻¹' {y'}) < _ at hlt
    omega
  -- lift the generic points of `Z₁`, `Z₂` to the piece through a point over `x`
  obtain ⟨x', hx'x, hx'y⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' hgy'.symm
  let a : F' := ⟨x', hx'y⟩
  have key (Z : Set X) (hZ : Z ∈ irreducibleComponents X) (hxZ : x ∈ Z) :
      ∃ s ∈ U a, f' s = η' ∧ g' s ⤳ hZ.1.genericPoint := by
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgp : IsGenericPoint hZ.1.genericPoint Z := by
      simpa [hZc.closure_eq] using hZ.1.isGenericPoint_genericPoint_closure
    obtain ⟨ζ', hζ', hgζ'⟩ := Flat.generalizingMap g' (hx'x ▸ hgp.specializes hxZ)
    have hζU : ζ' ∈ U a := hζ'.mem_open (hUc a).2 (haU a)
    obtain ⟨s, hsU, hsη, hsζ⟩ := f'.isOpenMap.exists_specializes_of_finite (hUc a).2 hζU
      (genericPoint_specializes (f' ζ')) ((hfin η').subset Set.inter_subset_right)
    exact ⟨s, hsU, hsη, hgζ' ▸ hsζ.map g'.continuous⟩
  obtain ⟨s₁, hs₁U, hs₁η, hs₁⟩ := key Z₁ hZ₁ hx₁
  obtain ⟨s₂, hs₂U, hs₂η, hs₂⟩ := key Z₂ hZ₂ hx₂
  obtain rfl := huniq a s₁ s₂ hs₁U hs₂U hs₁η hs₂η
  -- both components are the closure of `g' s₁`
  have hcomp (Z : Set X) (hZ : Z ∈ irreducibleComponents X) (h : g' s₁ ⤳ hZ.1.genericPoint) :
      Z = closure {g' s₁} := by
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgp : IsGenericPoint hZ.1.genericPoint Z := by
      simpa [hZc.closure_eq] using hZ.1.isGenericPoint_genericPoint_closure
    have hsub : Z ⊆ closure {g' s₁} := by
      rw [← hgp.def]
      exact specializes_iff_closure_subset.mp h
    exact hsub.antisymm (hZ.2 isIrreducible_singleton.closure hsub)
  exact hne ((hcomp Z₁ hZ₁ hs₁).trans (hcomp Z₂ hZ₂ hs₂).symm)

/-- I.10.8. -/
theorem disjoint_irreducibleComponents_Statement_holds :
    disjoint_irreducibleComponents_Statement.{u} :=
  fun _ _ f _ _ _ _ _ hY hn _ hZ₁ _ hZ₂ hne ↦ disjoint_irreducibleComponents f hY hn hZ₁ hZ₂ hne

end Disjoint

section Degree

/-- At every point, `n(y)` is at most the degree `∑ [κ(x) : κ(y)]` of the fibre. -/
lemma geometricFiberCard_le_fiberDegree {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (y : Y) (hy : (f ⁻¹' {y}).Finite) : geometricFiberCard f y ≤ fiberDegree f y := by
  have : Fintype (f ⁻¹' {y}) := hy.fintype
  rw [geometricFiberCard, fiberDegree, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  let := (f.residueFieldMap x.1).hom.toAlgebra
  have := f.finiteDimensional_residueField x.1
  exact Field.finSepDegree_le_finrank _ _

/-- I.10.11, first assertion, when `f` is universally open: for `Y` irreducible, `n(y) ≤ n`, the
degree of the generic fibre. SGA deduces the universal openness of `f` near `y` from the normality
of `Y` at `y` and the dominance of the components of `X` (Chevalley's criterion, EGA IV 14.4.4);
then `n(y) ≤ n(z) ≤ n` by I.10.7 for the generic point `z`. -/
theorem geometricFiberCard_le_fiberDegree_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [QuasiCompact f] [IsSeparated f] [UniversallyOpen f]
    [IrreducibleSpace Y] (y : Y) :
    geometricFiberCard f y ≤ fiberDegree f (genericPoint Y) := by
  obtain ⟨U, hyU, hU⟩ := exists_le_geometricFiberCard f y
  have hz : genericPoint Y ∈ U := (genericPoint_specializes y).mem_open U.2 hyU
  exact (hU _ hz).trans
    (geometricFiberCard_le_fiberDegree f _ (f.finite_preimage_singleton _))

end Degree

section SeparableDegree

open IsLocalRing TensorProduct

variable {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] (B : Subalgebra A L) [Module.Finite A B]
  [IsFractionRing B L]

omit [IsLocalRing A] [IsIntegrallyClosed A] [Module.Finite A B] in
/-- For `B ⊆ L` with fraction field `L`, `K ⊗_A B = L`: the `K`-algebra map `K ⊗_A B → L` is
injective (localization) and surjective (its image is a subfield containing `B`). -/
lemma bijective_tensorProduct_lift :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId K L) B.val
      (fun _ _ ↦ .all _ _) : K ⊗[A] B →ₐ[K] L) := by
  let φ : K ⊗[A] B →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L) B.val
    (fun _ _ ↦ .all _ _)
  have hφ (b : B) : φ (1 ⊗ₜ b) = b := by simp [φ]
  refine ⟨(injective_iff_map_eq_zero φ).mpr fun t ht ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨⟨b, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors A) (TensorProduct.mk A K B 1) t
    have hs' : algebraMap A K s • t = 1 ⊗ₜ b := by
      rw [algebraMap_smul]
      exact hs
    have hb : (b : L) = 0 := by
      rw [← hφ, ← hs', map_smul, ht, smul_zero]
    have hb0 : b = 0 := Subtype.ext hb
    have hs0 : algebraMap A K s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero s.2)
    rw [hb0, TensorProduct.tmul_zero] at hs'
    rw [← inv_smul_smul₀ hs0 t, hs', smul_zero]
  · obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    have hmem (b : B) : (b : L) ∈ φ.range := ⟨1 ⊗ₜ b, hφ b⟩
    have hinv : ((algebraMap B L b₂)⁻¹ : L) ∈ φ.range :=
      Subalgebra.inv_mem_of_algebraic (A := φ.range) (x := ⟨_, hmem b₂⟩)
        (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨t, ht⟩ := φ.range.mul_mem (hmem b₁) hinv
    exact ⟨t, by rw [div_eq_mul_inv]; exact ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- **I.10.12**: let `A` be an integrally closed local domain with fraction field `K`, `L` a
finite extension of `K` and `B ⊆ L` a finite `A`-subalgebra with fraction field `L`. The number
`n'` of geometric points `B → k̄` of the closed fibre satisfies `n' ≤ [L : K]_s`, and
`n' = [L : K]` iff `B` is étale over `A`. SGA reduces the case of a finite residue field to the
infinite one through `A(t)`; we pass instead to the strict henselization `A^{sh}`, an integrally
closed domain (EGA IV 18.8.12), over which `A^{sh} ⊗_A B` splits into local pieces
(`IsLocalRing.card_algHom_le_finrank`, `IsLocalRing.card_algHom_eq_finrank_iff_etale`). The
noetherian hypothesis of SGA is not needed. -/
theorem separableDegree_fiber_le :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) ≤ Field.finSepDegree K L ∧
      (Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K L ↔
        Algebra.Etale A B) := by
  let Ω := AlgebraicClosure (ResidueField A)
  have : IsLocalHom (algebraMap A Ω) := isLocalHom_algebraMap_of_isScalarTower (R := A) (K := Ω)
  obtain ⟨hdom, hint⟩ := isDomain_and_isIntegrallyClosed_strictHenselization (R := A) Ω
  let A' := StrictHenselization A Ω
  let Ω' := AlgebraicClosure (FractionRing A')
  -- `B` is torsion-free
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A L := Module.isTorsionFree_iff_algebraMap_injective.mpr hAL
  have : Module.IsTorsionFree A B :=
    Function.Injective.moduleIsTorsionFree (B.val : B → L) Subtype.val_injective fun _ _ ↦ rfl
  -- `K ⊗_A B = L`
  let e : K ⊗[A] B ≃ₐ[K] L := AlgEquiv.ofBijective _ (bijective_tensorProduct_lift B)
  have hn : Module.finrank K (K ⊗[A] B) = Module.finrank K L := e.toLinearEquiv.finrank_eq
  -- the `A`-algebra maps `B → Ω'` are the `K`-embeddings of `L`
  have hinj : Function.Injective (algebraMap A Ω') := by
    rw [IsScalarTower.algebraMap_eq A A' Ω', IsScalarTower.algebraMap_eq A' (FractionRing A') Ω']
    exact (algebraMap (FractionRing A') Ω').injective.comp
      ((IsFractionRing.injective A' (FractionRing A')).comp
        (FaithfulSMul.algebraMap_injective A A'))
  let : Algebra K Ω' := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower A K Ω' :=
    .of_algebraMap_eq fun a ↦ (IsFractionRing.lift_algebraMap hinj a).symm
  have hs : Nat.card (B →ₐ[A] Ω') = Field.finSepDegree K L := by
    rw [Field.finSepDegree_eq_of_isAlgClosed K L Ω',
      Nat.card_congr (Algebra.TensorProduct.liftEquivRight (R := A) (S := K) (B := B) Ω')]
    exact Nat.card_congr (e.arrowCongr (AlgEquiv.refl))
  have h1 := card_algHom_le_finrank (A := A) K B
  have h2 := card_algHom_eq_finrank_iff_etale (A := A) K B
  refine ⟨hs ▸ h1.1, ?_⟩
  rw [← hn]
  exact h2

/-- I.10.12. -/
theorem separableDegree_fiber_le_Statement_holds : separableDegree_fiber_le_Statement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B _ _ ↦ separableDegree_fiber_le B

end SeparableDegree

section NormalPoint

open IsLocalRing Limits TensorProduct

/-- Every point of a scheme is a specialization of a point whose closure is an irreducible
component. -/
lemma exists_specializes_closure_mem_irreducibleComponents {X : Scheme.{u}} (x : X) :
    ∃ ξ : X, ξ ⤳ x ∧ closure {ξ} ∈ irreducibleComponents X := by
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hZc := isClosed_of_mem_irreducibleComponents _ hZ
  refine ⟨hZ.1.genericPoint, (hZ.1.isGenericPoint_genericPoint hZc).specializes
    mem_irreducibleComponent, ?_⟩
  rw [hZ.1.closure_genericPoint hZc]
  exact hZ

/-- A continuous generalizing map sends points whose closure is an irreducible component to
points with the same property. -/
lemma closure_apply_mem_irreducibleComponents {X' X : Type*} [TopologicalSpace X']
    [TopologicalSpace X] [QuasiSober X] {g : X' → X} (hg : GeneralizingMap g) (hc : Continuous g)
    {ξ : X'} (hξ : closure {ξ} ∈ irreducibleComponents X') :
    closure {g ξ} ∈ irreducibleComponents X := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hsub ↦ ?_⟩
  have ht := hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hgt : hT.closure.genericPoint ⤳ g ξ :=
    ht.specializes (subset_closure (hsub (subset_closure (Set.mem_singleton _))))
  obtain ⟨ξ'', hξ'', hg''⟩ := hg hgt
  have h1 : closure {ξ} ⊆ closure {ξ''} := specializes_iff_closure_subset.mp hξ''
  have h2 : closure {ξ''} ⊆ closure {ξ} := hξ.2 isIrreducible_singleton.closure h1
  have hmem : ξ ⤳ ξ'' := specializes_iff_mem_closure.mpr (h2 (subset_closure rfl))
  have hgmem : hT.closure.genericPoint ∈ closure {g ξ} := by
    rw [← hg'']
    exact specializes_iff_mem_closure.mp (hmem.map hc)
  calc T ⊆ closure T := subset_closure
    _ = closure {hT.closure.genericPoint} := ht.def.symm
    _ ⊆ closure {g ξ} := closure_minimal (Set.singleton_subset_iff.mpr hgmem) isClosed_closure

/-- If every irreducible component of `X` dominates `Y`, a point of `X` whose closure is an
irreducible component lies over the generic point of `Y`. -/
lemma apply_eq_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    (hdom : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z)) {ξ : X}
    (hξ : closure {ξ} ∈ irreducibleComponents X) : f ξ = genericPoint Y := by
  have hsub : f '' closure {ξ} ⊆ closure {f ξ} := by
    rw [← Set.image_singleton]
    exact image_closure_subset_closure_image f.continuous
  have hcl : closure {f ξ} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hdom _ hξ).closure_eq]
    exact closure_minimal hsub isClosed_closure
  exact (isGenericPoint_def.mpr hcl).eq (genericPoint_spec Y)

/-- The generic point of `Spec 𝒪_{Y,s}` (`𝒪_{Y,s}` a domain) maps to the generic point of the
irreducible scheme `Y`. -/
lemma fromSpecStalk_bot {Y : Scheme.{u}} [IrreducibleSpace Y] (s : Y)
    [IsDomain (Y.presheaf.stalk s)] :
    Y.fromSpecStalk s ⟨⊥, Ideal.isPrime_bot⟩ = genericPoint Y := by
  obtain ⟨p₀, -, hp₀⟩ := Flat.generalizingMap (Y.fromSpecStalk s)
    (genericPoint_specializes (Y.fromSpecStalk s (closedPoint (Y.presheaf.stalk s))))
  have h : (⟨⊥, Ideal.isPrime_bot⟩ : Spec (Y.presheaf.stalk s)) ⤳ p₀ :=
    (PrimeSpectrum.le_iff_specializes _ p₀).mp bot_le
  have h' := h.map (Y.fromSpecStalk s).continuous
  rw [hp₀] at h'
  refine (isGenericPoint_def.mpr (Set.eq_univ_of_univ_subset ?_)).eq (genericPoint_spec Y)
  rw [← (genericPoint_spec Y).def]
  exact specializes_iff_closure_subset.mp h'

/-- A point with no proper generization is the generic point of an irreducible component. -/
lemma closure_mem_irreducibleComponents_of_forall {X : Type*} [TopologicalSpace X] [QuasiSober X]
    {x : X} (h : ∀ v, v ⤳ x → v = x) : closure {x} ∈ irreducibleComponents X := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hsub ↦ ?_⟩
  have ht := hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hx := h _ (ht.specializes (subset_closure (hsub (subset_closure rfl))))
  calc T ⊆ closure T := subset_closure
    _ = closure {hT.closure.genericPoint} := ht.def.symm
    _ = closure {x} := by rw [hx]

set_option backward.isDefEq.respectTransparency false in
/-- Over an irreducible `Y` whose local ring at `ȳ` is a domain with domain strict
henselization, the generic point of the strict localization `Spec 𝒪^{sh}_{Y,ȳ}` is the only point
over the generic point of `Y`. -/
lemma eq_genericPoint_of_fromSpecStrictLocalization {Y : Scheme.{u}} [IrreducibleSpace Y]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ Y) [IsDomain (Y.presheaf.stalk ξ.imagePoint)]
    [IsDomain ξ.strictLocalization] (w : Spec ξ.strictLocalization)
    (hw : ξ.fromSpecStrictLocalization w = genericPoint Y) :
    w = genericPoint (Spec ξ.strictLocalization) := by
  let s := Y.presheaf.stalk ξ.imagePoint
  let A' := ξ.strictLocalization
  let := ξ.stalkAlgebra
  have : IsDomain (StrictHenselization s Ω) := inferInstanceAs (IsDomain A')
  let bot : Spec s := ⟨⊥, Ideal.isPrime_bot⟩
  have hbot : Y.fromSpecStalk ξ.imagePoint bot = genericPoint Y := fromSpecStalk_bot _
  have hp : Spec.map ξ.toStrictLocalization w = bot :=
    (Y.fromSpecStalk ξ.imagePoint).isEmbedding.injective (hw.trans hbot.symm)
  have hcomap : w.asIdeal.comap (algebraMap s A') = ⊥ := congrArg PrimeSpectrum.asIdeal hp
  have hw' : w.asIdeal = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun a ha ↦ by_contra fun ha0 ↦ ?_
    obtain ⟨r, hr0, hr⟩ := StrictHenselization.exists_dvd_algebraMap (R := s)
      (K := Ω) (z := a) ha0
    have hrw : r ∈ w.asIdeal.comap (algebraMap s A') :=
      Ideal.mem_comap.mpr (Ideal.mem_of_dvd w.asIdeal hr ha)
    rw [hcomap] at hrw
    exact hr0 hrw
  have hgen : IsGenericPoint w ⊤ := by
    rw [isGenericPoint_def, PrimeSpectrum.closure_singleton, hw', PrimeSpectrum.zeroLocus_bot]
    rfl
  exact hgen.eq (genericPoint_spec _)

set_option backward.isDefEq.respectTransparency false in
/-- I.10.11, main step. Let `f : X ⟶ Y` be quasi-finite, separated, quasi-compact and of finite
type, with `Y` irreducible and every irreducible component of `X` dominating `Y`, and let `y` be a
point where `Y` is normal. Then `n(y) ≤ n(z)` for the generic point `z` of `Y` (so `f` behaves as
if it were universally open near `y`, which is Chevalley's criterion in SGA), and if equality holds
then `X` becomes finite over the strict localization `Spec 𝒪^{sh}_{Y,ȳ}`.

Over `Y' = Spec 𝒪^{sh}_{Y,ȳ}`, a normal domain whose generic point is the only point over `z`, each
point `x'` of `X'` over the closed point has a clopen neighbourhood `U` meeting the closed fibre
only in `x'` (Stacks 04GJ, `AlgebraicGeometry.exists_isClopen_of_locallyQuasiFinite`); by the
dominance hypothesis `U` contains a point over the generic point of `Y'`. -/
theorem geometricFiberCard_le_genericPoint_and_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f]
    [IrreducibleSpace Y] (hdom : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z)) (y : Y)
    [IsDomain (Y.presheaf.stalk y)] [IsIntegrallyClosed (Y.presheaf.stalk y)] :
    f.geometricFiberCard y ≤ f.geometricFiberCard (genericPoint Y) ∧
      (f.geometricFiberCard (genericPoint Y) ≤ f.geometricFiberCard y →
        IsFinite (pullback.snd f (Y.fromSpecAlgClosure y).fromSpecStrictLocalization)) := by
  classical
  let ξ := Y.fromSpecAlgClosure y
  have hξ : ξ.imagePoint = y := Scheme.fromSpecAlgClosure_apply Y y
  have : IsDomain (Y.presheaf.stalk ξ.imagePoint) := by rw [hξ]; infer_instance
  have : IsIntegrallyClosed (Y.presheaf.stalk ξ.imagePoint) := by rw [hξ]; infer_instance
  let A' := ξ.strictLocalization
  let := ξ.residueFieldAlgebra
  let := ξ.stalkAlgebra
  have := ξ.isScalarTower_stalkAlgebra
  have := isLocalHom_algebraMap_of_isScalarTower (R := Y.presheaf.stalk ξ.imagePoint)
    (K := AlgebraicClosure (Y.residueField y))
  have : IsDomain A' := (isDomain_and_isIntegrallyClosed_strictHenselization
    (R := Y.presheaf.stalk ξ.imagePoint) (AlgebraicClosure (Y.residueField y))).1
  let g := ξ.fromSpecStrictLocalization
  have : Flat g := by
    have : Flat (Spec.map ξ.toStrictLocalization) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.mpr
        (inferInstance : Module.Flat (Y.presheaf.stalk ξ.imagePoint) A')
    exact inferInstanceAs (Flat (Spec.map ξ.toStrictLocalization ≫ Y.fromSpecStalk ξ.imagePoint))
  let y' := closedPoint A'
  have hgy' : g y' = y := (ξ.fromSpecStrictLocalization_closedPoint).trans hξ
  let η' := genericPoint (Spec A')
  have hgη : g η' = genericPoint Y := by
    obtain ⟨w, -, hw⟩ := Flat.generalizingMap g
      (show genericPoint Y ⤳ g y' by rw [hgy']; exact genericPoint_specializes y)
    have hwη : w = η' := eq_genericPoint_of_fromSpecStrictLocalization ξ w hw
    rw [← hwη]
    exact hw
  -- the base change `f' : X' ⟶ Y'`
  let f' := pullback.snd f g
  let g' := pullback.fst f g
  have hpb := IsPullback.of_hasPullback f g
  have : Flat g' := MorphismProperty.pullback_fst _ _ ‹Flat g›
  have hfin (w : Spec A') : (f' ⁻¹' {w}).Finite := f'.finite_preimage_singleton w
  -- every point of `X'` is a specialization of a point over the generic point of `Y'`
  have hmax (x' : ↥(pullback f g)) : ∃ ξ' : ↥(pullback f g), ξ' ⤳ x' ∧ f' ξ' = η' := by
    obtain ⟨ξ', hξ', hcl⟩ := exists_specializes_closure_mem_irreducibleComponents x'
    have hcl' := closure_apply_mem_irreducibleComponents (Flat.generalizingMap g')
      g'.continuous hcl
    have h1 := apply_eq_genericPoint f hdom hcl'
    have h2 : g (f' ξ') = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact h1
    exact ⟨ξ', hξ', eq_genericPoint_of_fromSpecStrictLocalization ξ _ h2⟩
  -- the pieces around the points of `X'` over the closed point of `Y'`
  let F' := f' ⁻¹' {y'}
  let ι := f'.toNormalization
  let π := f'.fromNormalization
  have hπι (z : ↥(pullback f g)) : π (ι z) = f' z := by
    rw [← Scheme.Hom.comp_apply, f'.toNormalization_fromNormalization]
  have hU (a : F') := exists_isClopen_of_locallyQuasiFinite f' a.1 a.2
  choose U hUc haU hUF hUcl using hU
  have hdisj (a b : F') (z : ↥(pullback f g)) (hza : z ∈ U a) (hzb : z ∈ U b) : a = b := by
    have hC : IsClosed (f' '' (U a ∩ U b)) := by
      have : f' '' (U a ∩ U b) = π '' (ι '' U a ∩ ι '' U b) := by
        rw [← Set.image_inter ι.isOpenEmbedding.injective, Set.image_image]
        simp_rw [hπι]
      rw [this]
      exact π.isClosedMap _ ((hUcl a).inter (hUcl b))
    obtain ⟨c, ⟨hca, hcb⟩, hc⟩ : y' ∈ f' '' (U a ∩ U b) :=
      (specializes_closedPoint (f' z)).mem_closed hC ⟨z, ⟨hza, hzb⟩, rfl⟩
    exact Subtype.ext ((hUF a c hca hc).symm.trans (hUF b c hcb hc))
  have hgen (a : F') : ∃ w ∈ U a, f' w = η' := by
    obtain ⟨ξ', hξ', h⟩ := hmax a.1
    exact ⟨ξ', hξ'.mem_open (hUc a).2 (haU a), h⟩
  choose w hwU hwη using hgen
  let ι₀ : F' → f' ⁻¹' {η'} := fun b ↦ ⟨w b, hwη b⟩
  have hinj : Function.Injective ι₀ := fun b c hbc ↦
    hdisj b c (w b) (hwU b) (by rw [show w b = w c from congrArg Subtype.val hbc]; exact hwU c)
  have : Fintype (f' ⁻¹' {η'}) := (hfin η').fintype
  have : Fintype F' := (hfin y').fintype
  have hcard := Fintype.card_le_of_injective ι₀ hinj
  -- the counts
  have : IsSepClosed ((Spec A').residueField y') := isSepClosed_residueField_closedPoint A' y' rfl
  have h₁ := f'.geometricFiberCard_eq_natCard y' (hfin y')
  have h₂ := f'.natCard_preimage_le_geometricFiberCard η' (hfin η')
  have hy : f'.geometricFiberCard y' = f.geometricFiberCard y := by
    rw [Scheme.Hom.geometricFiberCard_of_isPullback f f.finite_preimage_singleton hpb, hgy']
  have hz : f'.geometricFiberCard η' = f.geometricFiberCard (genericPoint Y) := by
    rw [Scheme.Hom.geometricFiberCard_of_isPullback f f.finite_preimage_singleton hpb, hgη]
  rw [Nat.card_eq_fintype_card] at h₁ h₂
  refine ⟨?_, fun heq ↦ ?_⟩
  · rw [← hy, ← hz, h₁]
    exact hcard.trans h₂
  -- equality: the pieces cover `X'`, which is then finite over `Y'`
  have hcard' : Fintype.card (f' ⁻¹' {η'}) = Fintype.card F' := by
    rw [← hy, ← hz, h₁] at heq
    exact le_antisymm (h₂.trans heq) hcard
  have hsurj : Function.Surjective ι₀ :=
    ((Fintype.bijective_iff_injective_and_card ι₀).mpr ⟨hinj, hcard'.symm⟩).2
  have hcover (x' : ↥(pullback f g)) : ∃ a : F', x' ∈ U a := by
    obtain ⟨ξ', hξ', h⟩ := hmax x'
    obtain ⟨a, ha⟩ := hsurj ⟨ξ', h⟩
    have hwa : w a = ξ' := congrArg Subtype.val ha
    exact ⟨a, hξ'.mem_closed (hUc a).1 (hwa ▸ hwU a)⟩
  have hrange : Set.range ι = ⋃ a : F', ι '' U a := by
    ext z
    simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image]
    refine ⟨fun ⟨x', hx'⟩ ↦ ?_, fun ⟨a, x', _, hx'⟩ ↦ ⟨x', hx'⟩⟩
    obtain ⟨a, ha⟩ := hcover x'
    exact ⟨a, x', ha, hx'⟩
  have hclosed : IsClosed (Set.range ι) := hrange ▸ isClosed_iUnion_of_finite fun a ↦ hUcl a
  have : IsClosedImmersion ι := .of_isPreimmersion ι hclosed
  have : IsIntegralHom f' := by
    rw [← f'.toNormalization_fromNormalization]
    infer_instance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f').mpr ⟨inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- I.10.11, the equality case over the local ring: let `f` be as in I.10.11 with `X` reduced, and
`s` a point where `Y` is normal. If `X ×_Y Spec 𝒪_{Y,s}` is finite over `Spec 𝒪_{Y,s}` and
`n(s) = n`, the degree of the generic fibre, then `X ×_Y Spec 𝒪_{Y,s}` is étale over
`Spec 𝒪_{Y,s}`. Its ring `B` is finite, reduced and torsion-free over `A = 𝒪_{Y,s}`, `n(s)` is
the number of geometric points of `B` over the closed point and `n = [K ⊗_A B : K]`; apply
I.10.12 in the form `IsLocalRing.card_algHom_eq_finrank_iff_etale`. -/
theorem etale_pullback_fromSpecStalk {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f] [IrreducibleSpace Y] [IsReduced X]
    (hdom : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z)) (s : Y)
    [IsDomain (Y.presheaf.stalk s)] [IsIntegrallyClosed (Y.presheaf.stalk s)]
    [IsFinite (pullback.snd f (Y.fromSpecStalk s))]
    (heq : f.geometricFiberCard s = f.fiberDegree (genericPoint Y)) :
    Etale (pullback.snd f (Y.fromSpecStalk s)) := by
  let A := Y.presheaf.stalk s
  let q := pullback.snd f (Y.fromSpecStalk s)
  let g' := pullback.fst f (Y.fromSpecStalk s)
  have hpb := IsPullback.of_hasPullback f (Y.fromSpecStalk s)
  let XA := pullback f (Y.fromSpecStalk s)
  have : IsAffine XA := isAffine_of_isAffineHom q
  let B := Γ(XA, ⊤)
  let φ : A ⟶ B := (Scheme.ΓSpecIso A).inv ≫ q.appTop
  have hq : q = XA.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra A B := φ.hom.toAlgebra
  have hφ : φ = CommRingCat.ofHom (algebraMap A B) := rfl
  have hSφ : Spec.map φ = XA.isoSpec.inv ≫ q := by rw [hq, Iso.inv_hom_id_assoc]
  have : IsFinite (Spec.map φ) := by rw [hSφ]; infer_instance
  have : Module.Finite A B := (IsFinite.SpecMap_iff _).mp ‹_›
  have hsq : IsPullback XA.isoSpec.hom q (Spec.map φ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [hq, Category.comp_id]⟩
  -- `B` is reduced and torsion-free
  have : Flat g' := MorphismProperty.pullback_fst _ _ (inferInstance : Flat (Y.fromSpecStalk s))
  have : IsReduced XA := isReduced_of_flat_of_isPreimmersion g'
  have hbot := fromSpecStalk_bot (Y := Y) s
  have hminimal (P₀ : Ideal B) (hP₀ : P₀ ∈ minimalPrimes B) :
      P₀.comap (algebraMap A B) = ⊥ := by
    have : P₀.IsPrime := hP₀.1.1
    let p₀ : Spec B := ⟨P₀, this⟩
    let w := XA.isoSpec.inv p₀
    have hw : XA.isoSpec.hom w = p₀ := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hmax : ∀ v, v ⤳ w → v = w := by
      intro v hv
      have hv' := hv.map XA.isoSpec.hom.continuous
      rw [hw] at hv'
      have hle : (XA.isoSpec.hom v).asIdeal ≤ P₀ := (PrimeSpectrum.le_iff_specializes _ _).mpr hv'
      have heq' : XA.isoSpec.hom v = p₀ :=
        PrimeSpectrum.ext ((hP₀.2 ⟨(XA.isoSpec.hom v).2, bot_le⟩ hle).antisymm hle).symm
      have := congrArg XA.isoSpec.inv (heq'.trans hw.symm)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at this
      simpa using this
    have hcl := closure_apply_mem_irreducibleComponents (Flat.generalizingMap g') g'.continuous
      (closure_mem_irreducibleComponents_of_forall hmax)
    have h1 := apply_eq_genericPoint f hdom hcl
    have h2 : Y.fromSpecStalk s (q w) = Y.fromSpecStalk s ⟨⊥, Ideal.isPrime_bot⟩ := by
      rw [hbot, ← h1, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    have h3 := (Y.fromSpecStalk s).isEmbedding.injective h2
    rw [hq, Scheme.Hom.comp_apply, hw] at h3
    exact congrArg PrimeSpectrum.asIdeal h3
  have : Module.IsTorsionFree A B := by
    refine .of_smul_eq_zero fun a b hab ↦ or_iff_not_imp_left.mpr fun ha ↦ ?_
    refine IsReduced.eq_zero b (nilpotent_iff_mem_prime.mpr fun P hP ↦ ?_)
    obtain ⟨P₀, hP₀, hle⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal B) ≤ P from bot_le)
    have : P₀.IsPrime := hP₀.1.1
    have hP₀' : P₀ ∈ minimalPrimes B := hP₀
    have haP₀ : algebraMap A B a ∉ P₀ := fun h ↦ ha (by
      have : a ∈ P₀.comap (algebraMap A B) := h
      rwa [hminimal P₀ hP₀', Ideal.mem_bot] at this)
    have hmem : algebraMap A B a * b ∈ P₀ := by
      rw [← Algebra.smul_def, hab]
      exact zero_mem _
    exact hle ((this.mem_or_mem hmem).resolve_left haP₀)
  let K := FractionRing A
  have : _root_.IsReduced (K ⊗[A] B) := isReduced_tensorProduct_of_isTorsionFree K
  -- the number of geometric points of the closed fibre
  let Ω := AlgebraicClosure (ResidueField A)
  have : IsLocalHom (algebraMap A Ω) := isLocalHom_algebraMap_of_isScalarTower (R := A) (K := Ω)
  have hΩ : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) (closedPoint Ω) = closedPoint A :=
    comap_closedPoint (algebraMap A Ω)
  have hn' : Nat.card (B →ₐ[A] Ω) = f.geometricFiberCard s := by
    have h₁ := Scheme.Hom.geometricFiberCard_of_isPullback f f.finite_preimage_singleton hpb
      (closedPoint A)
    rw [Scheme.fromSpecStalk_closedPoint] at h₁
    have h₂ : q.geometricFiberCard (closedPoint A) =
        (Spec.map φ).geometricFiberCard (closedPoint A) :=
      Scheme.Hom.geometricFiberCard_of_isPullback (Spec.map φ)
        (Spec.map φ).finite_preimage_singleton hsq (closedPoint A)
    rw [← h₁, h₂, ← hΩ]
    exact (Scheme.geometricFiberCard_specMap Ω (by
      rw [hΩ]
      exact (Spec.map φ).finite_preimage_singleton _)).symm
  -- the degree of the generic fibre
  have hdeg : Module.finrank K (K ⊗[A] B) = f.fiberDegree (genericPoint Y) := by
    have h₁ := Scheme.Hom.fiberDegree_of_isPullback f hpb ⟨⊥, Ideal.isPrime_bot⟩
    rw [hbot] at h₁
    have h₂ : q.fiberDegree ⟨⊥, Ideal.isPrime_bot⟩ =
        (Spec.map φ).fiberDegree ⟨⊥, Ideal.isPrime_bot⟩ :=
      Scheme.Hom.fiberDegree_of_isPullback (Spec.map φ) hsq ⟨⊥, Ideal.isPrime_bot⟩
    rw [← h₁, h₂]
    exact (Scheme.fiberDegree_specMap_bot K).symm
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_strictHenselization (R := A) Ω
  have hE : Algebra.Etale A B :=
    (IsLocalRing.card_algHom_eq_finrank_iff_etale (A := A) K B).mp (by rw [hn', hdeg]; exact heq)
  have : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hE)
  have h : Etale (XA.isoSpec.hom ≫ Spec.map φ) := inferInstance
  rw [← hq] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **I.10.11**: let `f : X ⟶ Y` be quasi-finite, separated, quasi-compact and of finite type,
with `Y` locally noetherian and irreducible, `X` reduced and every irreducible component of `X`
dominating `Y`, and let `n` be the degree of `X` over `Y` (at the generic point `z`). Let `y` be a
point where `Y` is normal. Then `n(y) ≤ n`, with equality iff `f` is an étale covering over a
neighbourhood of `y`.

SGA uses I.10.7 (with Chevalley's criterion for universal openness), I.10.8 and I.10.12. Here:
`n(y) ≤ n(z) ≤ n`, the first inequality over the strict localization at `y`
(`geometricFiberCard_le_genericPoint_and_isFinite`). If `n(y) = n`, `X` is finite over the strict
localization, hence (faithfully flat descent) over `Spec 𝒪_{Y,y}`, where I.10.12 shows it is étale
(`etale_pullback_fromSpecStalk`); the limit theorem for étale coverings spreads this out to a
neighbourhood of `y`. Conversely, over a connected neighbourhood where `f` is finite étale, `n` is
constant and equals the degree at `z` (the residue field extensions are separable). -/
theorem geometricFiberCard_le_fiberDegree_and_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f]
    [IrreducibleSpace Y] [IsReduced X] [IsLocallyNoetherian Y]
    (hdom : ∀ Z ∈ irreducibleComponents X, Dense (f '' Z)) (y : Y)
    [IsDomain (Y.presheaf.stalk y)] [IsIntegrallyClosed (Y.presheaf.stalk y)] :
    geometricFiberCard f y ≤ fiberDegree f (genericPoint Y) ∧
      (geometricFiberCard f y = fiberDegree f (genericPoint Y) ↔
        ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U)) := by
  obtain ⟨hle, hfin⟩ := geometricFiberCard_le_genericPoint_and_isFinite f hdom y
  have hle2 : f.geometricFiberCard (genericPoint Y) ≤ f.fiberDegree (genericPoint Y) :=
    geometricFiberCard_le_fiberDegree f _ (f.finite_preimage_singleton _)
  refine ⟨hle.trans hle2, ⟨fun heq ↦ ?_, ?_⟩⟩
  · -- `n(y) = n`: `f` is an étale covering near `y`
    have heq₀ : f.geometricFiberCard y = f.fiberDegree (genericPoint Y) := heq
    have hfin' := hfin (by omega)
    let ξ := Y.fromSpecAlgClosure y
    have hξ : ξ.imagePoint = y := Scheme.fromSpecAlgClosure_apply Y y
    have : IsDomain (Y.presheaf.stalk ξ.imagePoint) := by rw [hξ]; infer_instance
    have : IsIntegrallyClosed (Y.presheaf.stalk ξ.imagePoint) := by rw [hξ]; infer_instance
    let := ξ.residueFieldAlgebra
    let := ξ.stalkAlgebra
    have := ξ.isScalarTower_stalkAlgebra
    have := isLocalHom_algebraMap_of_isScalarTower (R := Y.presheaf.stalk ξ.imagePoint)
      (K := AlgebraicClosure (Y.residueField y))
    let q := pullback.snd f (Y.fromSpecStalk ξ.imagePoint)
    have hpaste := IsPullback.of_right' (h₂₁ := Spec.map ξ.toStrictLocalization)
      (h₂₂ := Y.fromSpecStalk ξ.imagePoint) (IsPullback.of_hasPullback f
        ξ.fromSpecStrictLocalization) (IsPullback.of_hasPullback f (Y.fromSpecStalk ξ.imagePoint))
    have : Surjective (Spec.map ξ.toStrictLocalization) :=
      ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
    have : Flat (Spec.map ξ.toStrictLocalization) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.mpr
        (inferInstance : Module.Flat (Y.presheaf.stalk ξ.imagePoint) ξ.strictLocalization)
    have : IsFinite q :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpaste.flip
        ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfin'
    have heqs : f.geometricFiberCard ξ.imagePoint = f.fiberDegree (genericPoint Y) := by
      rw [hξ]
      exact heq₀
    have : Etale q := etale_pullback_fromSpecStalk f hdom ξ.imagePoint heqs
    have : LocallyOfFinitePresentation f :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    obtain ⟨U, hU, hUf, hUe⟩ := Scheme.exists_isFinite_etale_morphismRestrict ξ.imagePoint f
    exact ⟨U, hξ ▸ hU, hUf, hUe⟩
  · -- over a neighbourhood where `f` is an étale covering, `n` is constant, equal to `n`
    rintro ⟨U, hyU, hUf, hUe⟩
    have hzU : genericPoint Y ∈ U := (genericPoint_specializes y).mem_open U.2 hyU
    have hU : IsPreirreducible (U : Set Y) :=
      (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.2 (Set.subset_univ _)
    have : PreconnectedSpace U := Subtype.preconnectedSpace hU.isPreconnected
    have h1 := (f ∣_ U).isLocallyConstant_geometricFiberCard.apply_eq_of_preconnectedSpace
      (⟨y, hyU⟩ : U) ⟨genericPoint Y, hzU⟩
    rw [f.geometricFiberCard_morphismRestrict f.finite_preimage_singleton,
      f.geometricFiberCard_morphismRestrict f.finite_preimage_singleton] at h1
    have h2 : (f ∣_ U).geometricFiberCard ⟨genericPoint Y, hzU⟩ =
        (f ∣_ U).fiberDegree ⟨genericPoint Y, hzU⟩ := by
      rw [Scheme.Hom.geometricFiberCard, Scheme.Hom.fiberDegree]
      refine finsum_congr fun x ↦ ?_
      let := ((f ∣_ U).residueFieldMap x.1).hom.toAlgebra
      have := (f ∣_ U).finiteDimensional_residueField x.1
      exact Field.finSepDegree_eq_finrank_of_isSeparable _ _
    have h3 : (f ∣_ U).fiberDegree ⟨genericPoint Y, hzU⟩ = f.fiberDegree (genericPoint Y) :=
      Scheme.Hom.fiberDegree_of_isPullback f (isPullback_morphismRestrict f U).flip _
    change f.geometricFiberCard y = f.fiberDegree (genericPoint Y)
    rw [h1, ← h3, ← h2, f.geometricFiberCard_morphismRestrict f.finite_preimage_singleton]

/-- I.10.11. -/
theorem geometricFiberCard_le_degree_Statement_holds :
    geometricFiberCard_le_degree_Statement.{u} := by
  intro X Y f _ _ _ _ _ _ _ hdom y hd hi
  exact geometricFiberCard_le_fiberDegree_and_iff f hdom y

end NormalPoint

end SGA.SGA1.ExposeI
