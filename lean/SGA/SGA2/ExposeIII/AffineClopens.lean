/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Connected.Clopen

/-!
# Clopen subsets and actual affine structure-sheaf sections

Locally constant ring-valued functions on an affine open define actual
structure-sheaf sections. In particular, a clopen subset defines its
idempotent characteristic section.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

variable {R : CommRingCat.{u}}

/-- A locally constant function gives an actual structure-sheaf section by
localizing its value at each point. -/
def locallyConstantAffineSection (U : Opens (PrimeSpectrum.Top R))
    (f : LocallyConstant U R) : (Spec.structureSheaf R).presheaf.obj (op U) := by
  refine ⟨fun x => algebraMap R (StructureSheaf.Localizations R x.1) (f x), ?_⟩
  intro x
  let V : Opens U := ⟨f ⁻¹' {f x}, f.isLocallyConstant _⟩
  let W := U.isOpenEmbedding.functor.obj V
  have hWU : W ≤ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.2
  refine ⟨W, ⟨x, rfl, rfl⟩, homOfLE hWU, f x, 1, ?_⟩
  intro y
  refine ⟨by simp [Ideal.IsPrime.one_notMem], ?_⟩
  have hy : f ⟨y.1, hWU y.2⟩ = f x := by
    obtain ⟨z, hz, he⟩ := y.2
    change f z = f x at hz
    have : z = ⟨y.1, hWU y.2⟩ := Subtype.ext he
    simpa only [← this] using hz
  change algebraMap R (StructureSheaf.Localizations R y.1) (f ⟨y.1, hWU y.2⟩) = _
  rw [hy]
  rfl

/-- The characteristic function of a clopen is an actual section. -/
def affineClopenSection (U : Opens (PrimeSpectrum.Top R)) (s : Set U) (hs : IsClopen s) :
    (Spec.structureSheaf R).presheaf.obj (op U) :=
  locallyConstantAffineSection U (LocallyConstant.charFn R hs)

open Classical in
theorem affineClopenSection_apply (U : Opens (PrimeSpectrum.Top R))
    (s : Set U) (hs : IsClopen s) (x : U) :
    (affineClopenSection U s hs).1 x = if x ∈ s then 1 else 0 := by
  classical
  change algebraMap R _ (LocallyConstant.charFn R hs x) = _
  by_cases h : x ∈ s <;> simp [LocallyConstant.charFn, Set.indicator, h]

theorem affineClopenSection_idempotent (U : Opens (PrimeSpectrum.Top R))
    (s : Set U) (hs : IsClopen s) : IsIdempotentElem (affineClopenSection U s hs) := by
  classical
  apply Subtype.ext
  funext x
  change (affineClopenSection U s hs).1 x * (affineClopenSection U s hs).1 x = _
  rw [affineClopenSection_apply]
  split_ifs <;> simp

@[simp] theorem affineClopenSection_empty (U : Opens (PrimeSpectrum.Top R)) :
    affineClopenSection U ∅ isClopen_empty = 0 := by
  apply Subtype.ext
  funext x
  change (affineClopenSection U ∅ isClopen_empty).1 x = (0 : StructureSheaf.Localizations R x.1)
  simp [affineClopenSection_apply]

@[simp] theorem affineClopenSection_univ (U : Opens (PrimeSpectrum.Top R)) :
    affineClopenSection U Set.univ isClopen_univ = 1 := by
  apply Subtype.ext
  funext x
  change (affineClopenSection U Set.univ isClopen_univ).1 x =
    (1 : StructureSheaf.Localizations R x.1)
  simp [affineClopenSection_apply]

theorem affineClopenSection_eq_zero_iff (U : Opens (PrimeSpectrum.Top R))
    (s : Set U) (hs : IsClopen s) : affineClopenSection U s hs = 0 ↔ s = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let := IsLocalization.AtPrime.nontrivial (StructureSheaf.Localizations R x.1) x.1.asIdeal
    have he := congrArg (fun t => t.1 x) h
    change (affineClopenSection U s hs).1 x = (0 : StructureSheaf.Localizations R x.1) at he
    simp [affineClopenSection_apply, hx] at he
  · rintro rfl
    exact affineClopenSection_empty U

theorem affineClopenSection_eq_one_iff (U : Opens (PrimeSpectrum.Top R))
    (s : Set U) (hs : IsClopen s) : affineClopenSection U s hs = 1 ↔ s = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_contra hx
    let := IsLocalization.AtPrime.nontrivial (StructureSheaf.Localizations R x.1) x.1.asIdeal
    have he := congrArg (fun t => t.1 x) h
    change (affineClopenSection U s hs).1 x = (1 : StructureSheaf.Localizations R x.1) at he
    simp [affineClopenSection_apply, hx] at he
  · rintro rfl
    exact affineClopenSection_univ U

/-- Characteristic sections commute with actual open restriction. -/
theorem affineClopenSection_restrict {U V : Opens (PrimeSpectrum.Top R)} (h : U ≤ V)
    (s : Set V) (hs : IsClopen s) :
    (Spec.structureSheaf R).presheaf.map (homOfLE h).op (affineClopenSection V s hs) =
      affineClopenSection U (Opens.inclusion h ⁻¹' s)
        (hs.preimage (by fun_prop)) := by
  apply Subtype.ext
  funext x
  change (affineClopenSection V s hs).1 (Opens.inclusion h x) = _
  rw [affineClopenSection_apply, affineClopenSection_apply]
  rfl

/-- On a preconnected prime spectrum every ring idempotent is trivial. -/
theorem idempotent_eq_zero_or_one_of_preconnected_spectrum
    [PreconnectedSpace (PrimeSpectrum R)] (e : R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  obtain h | h := preconnectedSpace_iff_clopen.mp inferInstance _ hc
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero
    apply Opens.ext
    simpa using h
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one
    apply Opens.ext
    simpa using h

/-- A bijective actual ring restriction from an affine scheme preserves
preconnectedness in the forward direction. -/
theorem preconnected_affine_open_of_restriction_bijective
    (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) [PreconnectedSpace (PrimeSpectrum R)] :
    PreconnectedSpace U := by
  let e : R ≃+* (Spec.structureSheaf R).presheaf.obj (op U) :=
    (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective ((Spec.structureSheaf R).presheaf.map
        (homOfLE le_top : U ⟶ ⊤).op).hom h)
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  have hid := (affineClopenSection_idempotent U s hs).map e.symm
  obtain hz | ho := idempotent_eq_zero_or_one_of_preconnected_spectrum _ hid
  · left
    apply (affineClopenSection_eq_zero_iff U s hs).mp
    simpa using congrArg e hz
  · right
    apply (affineClopenSection_eq_one_iff U s hs).mp
    simpa using congrArg e ho

/-- Injectivity of actual global restriction reflects preconnectedness.
This direction uses characteristic sections and does not need surjectivity. -/
theorem preconnected_spectrum_of_restriction_injective
    (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Injective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) [PreconnectedSpace U] :
    PreconnectedSpace (PrimeSpectrum R) := by
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  let t : Set (⊤ : Opens (PrimeSpectrum.Top R)) := Subtype.val ⁻¹' s
  have ht : IsClopen t := hs.preimage continuous_subtype_val
  let v : Set U := Opens.inclusion (show U ≤ ⊤ from le_top) ⁻¹' t
  have hv : IsClopen v := ht.preimage (by fun_prop)
  obtain hz | ho := preconnectedSpace_iff_clopen.mp inferInstance v hv
  · have hc : affineClopenSection ⊤ t ht = 0 := by
      apply h
      rw [affineClopenSection_restrict]
      change affineClopenSection U v hv = _
      rw [(affineClopenSection_eq_zero_iff U v hv).mpr hz]
      exact (map_zero _).symm
    have ht0 := (affineClopenSection_eq_zero_iff ⊤ t ht).mp hc
    left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : (⟨x, trivial⟩ : (⊤ : Opens (PrimeSpectrum.Top R))) ∈ t := hx
    simp [ht0] at this
  · have hc : affineClopenSection ⊤ t ht = 1 := by
      apply h
      rw [affineClopenSection_restrict]
      change affineClopenSection U v hv = _
      rw [(affineClopenSection_eq_one_iff U v hv).mpr ho]
      exact (map_one _).symm
    have ht1 := (affineClopenSection_eq_one_iff ⊤ t ht).mp hc
    right
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have : (⟨x, trivial⟩ : (⊤ : Opens (PrimeSpectrum.Top R))) ∈ t := by simp [ht1]
    exact this

/-- Bijective actual affine global restriction preserves and reflects
preconnectedness, including empty schemes. -/
theorem preconnected_spectrum_iff_of_restriction_bijective
    (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) :
    PreconnectedSpace (PrimeSpectrum R) ↔ PreconnectedSpace U := by
  constructor
  · intro hX
    exact preconnected_affine_open_of_restriction_bijective U h
  · intro hU
    exact preconnected_spectrum_of_restriction_injective U h.1

/-- An injective actual global restriction cannot remove every point of
a nonempty affine scheme. -/
theorem nonempty_affine_open_of_restriction_injective
    (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Injective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) [Nonempty (PrimeSpectrum R)] : Nonempty U := by
  by_contra hn
  have : IsEmpty U := not_nonempty_iff.mp hn
  have he : (0 : (Spec.structureSheaf R).presheaf.obj (op ⊤)) = 1 := by
    apply h
    apply Subtype.ext
    funext x
    exact isEmptyElim x
  let p : PrimeSpectrum R := Classical.choice inferInstance
  let := IsLocalization.AtPrime.nontrivial (StructureSheaf.Localizations R p) p.asIdeal
  have hp := congrArg (fun t => t.1 ⟨p, trivial⟩) he
  exact zero_ne_one hp

/-- The actual affine ring restriction, when bijective, preserves and
reflects connectedness. No noetherian hypothesis is needed for this bridge. -/
theorem connected_spectrum_iff_of_restriction_bijective
    (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) :
    ConnectedSpace (PrimeSpectrum R) ↔ ConnectedSpace U := by
  constructor
  · intro hX
    have := preconnected_affine_open_of_restriction_bijective U h
    have := nonempty_affine_open_of_restriction_injective U h.1
    exact ⟨inferInstance⟩
  · intro hU
    have := preconnected_spectrum_of_restriction_injective U h.1
    have : Nonempty (PrimeSpectrum R) := ⟨(Classical.choice (inferInstance : Nonempty U)).1⟩
    exact ⟨inferInstance⟩

end SGA.SGA2.ExposeIII
