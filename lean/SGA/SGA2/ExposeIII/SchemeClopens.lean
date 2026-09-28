/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Ring.Idempotent

/-!
# Genuine global structure idempotents and scheme clopens

Characteristic sections are constructed by actual sheaf gluing on a
clopen partition. The comparison works for arbitrary schemes.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- An idempotent in a local ring is zero or one. -/
theorem localRing_idempotent_eq_zero_or_one {A : Type u} [CommRing A] [IsLocalRing A]
    (a : A) (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hu : IsUnit a ∨ IsUnit (1 - a) :=
    IsLocalRing.isUnit_or_isUnit_of_isUnit_add (by simp)
  obtain hu | hu := hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · left
    have h := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub
    exact sub_eq_self.mp h

variable (X : Scheme.{u})

/-- The basic open of an actual idempotent global structure section is clopen. -/
theorem isClopen_basicOpen_of_idempotent (a : Γ(X, ⊤)) (ha : IsIdempotentElem a) :
    IsClopen (X.basicOpen a : Set X) := by
  have hmul : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha.eq, sub_self]
  have hadd : a + (1 - a) = 1 := by ring
  have hc : (⊤ : X.Opens) ≤ X.basicOpen a ⊔ X.basicOpen (1 - a) := by
    simpa only [hadd, X.basicOpen_one] using X.basicOpen_add_le a (1 - a)
  have hd : X.basicOpen a ⊓ X.basicOpen (1 - a) = ⊥ := by
    rw [← X.basicOpen_mul, hmul, X.basicOpen_zero]
  exact isClopen_of_disjoint_cover_open hc (X.basicOpen a).isOpen
    (X.basicOpen (1 - a)).isOpen (by
      apply Set.disjoint_iff_inter_eq_empty.mpr
      exact congrArg (fun U : X.Opens => (U : Set X)) hd)

/-- Every clopen of a scheme is the basic open of an actual idempotent
global section, constructed by gluing one and zero. -/
theorem exists_idempotent_basicOpen_eq_of_isClopen (s : Set X) (hs : IsClopen s) :
    ∃ a : Γ(X, ⊤), IsIdempotentElem a ∧ (X.basicOpen a : Set X) = s := by
  let U : Bool → X.Opens := fun b => if b then ⟨s, hs.isOpen⟩ else ⟨sᶜ, hs.compl.isOpen⟩
  let sf : ∀ b, Γ(X, U b) := fun b => if b then 1 else 0
  have hcover : (⊤ : X.Opens) ≤ ⨆ b, U b := by
    intro x _
    by_cases hx : x ∈ s
    · exact Opens.mem_iSup.mpr ⟨true, hx⟩
    · exact Opens.mem_iSup.mpr ⟨false, hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
    intro i j
    cases i <;> cases j <;> simp only [sf, Bool.false_eq_true, ↓reduceIte, map_zero, map_one]
    · apply TopCat.Presheaf.section_ext X.sheaf
      intro x hx
      exact False.elim (hx.1 hx.2)
    · apply TopCat.Presheaf.section_ext X.sheaf
      intro x hx
      exact False.elim (hx.2 hx.1)
  obtain ⟨a, ha, huniq⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  refine ⟨a, ?_, ?_⟩
  · apply huniq
    intro b
    rw [map_mul, ha]
    cases b <;> simp [sf]
  · have hp := congrArg (fun a => X.basicOpen a) (ha true)
    have hn := congrArg (fun a => X.basicOpen a) (ha false)
    change X.basicOpen (X.presheaf.map (homOfLE le_top : U true ⟶ ⊤).op a) =
      X.basicOpen (1 : Γ(X, U true)) at hp
    change X.basicOpen (X.presheaf.map (homOfLE le_top : U false ⟶ ⊤).op a) =
      X.basicOpen (0 : Γ(X, U false)) at hn
    rw [X.basicOpen_res, X.basicOpen_one] at hp
    rw [X.basicOpen_res, X.basicOpen_zero] at hn
    ext x
    constructor
    · intro hx
      by_contra hxs
      have : x ∈ (⊥ : X.Opens) := hn ▸ (show x ∈ U false ⊓ X.basicOpen a from ⟨hxs, hx⟩)
      exact this
    · intro hx
      exact (inf_eq_left.mp hp) hx

/-- Actual global idempotents are determined by their basic open. -/
theorem basicOpen_injective_on_idempotents (a b : Γ(X, ⊤))
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : X.basicOpen a = X.basicOpen b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x _
  let f := X.presheaf.germ ⊤ x trivial
  have hu : IsUnit (f a) ↔ IsUnit (f b) := by
    rw [← X.mem_basicOpen_top a x, ← X.mem_basicOpen_top b x, h]
  obtain ha0 | ha1 := localRing_idempotent_eq_zero_or_one (f a) (ha.map f.hom)
  · obtain hb0 | hb1 := localRing_idempotent_eq_zero_or_one (f b) (hb.map f.hom)
    · exact ha0.trans hb0.symm
    · exfalso
      simp only [ha0, hb1, isUnit_one, iff_true, not_isUnit_zero] at hu
  · obtain hb0 | hb1 := localRing_idempotent_eq_zero_or_one (f b) (hb.map f.hom)
    · exfalso
      simp only [ha1, hb0, isUnit_one, true_iff, not_isUnit_zero] at hu
    · exact ha1.trans hb1.symm

/-- A global idempotent vanishes exactly when its genuine basic open is empty. -/
theorem idempotent_eq_zero_iff_basicOpen_eq_bot (a : Γ(X, ⊤)) (ha : IsIdempotentElem a) :
    a = 0 ↔ X.basicOpen a = ⊥ := by
  constructor
  · rintro rfl
    exact X.basicOpen_zero ⊤
  · intro h
    exact basicOpen_injective_on_idempotents X a 0 ha .zero (h.trans (X.basicOpen_zero ⊤).symm)

/-- The genuine equivalence between global structure idempotents and scheme clopens. -/
def schemeIdempotentsEquivClopens :
    {a : Γ(X, ⊤) // IsIdempotentElem a} ≃ Clopens X :=
  Equiv.ofBijective (fun a => ⟨X.basicOpen a.1, isClopen_basicOpen_of_idempotent X a.1 a.2⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply basicOpen_injective_on_idempotents X a.1 b.1 a.2 b.2
      exact Opens.ext (congrArg (fun s : Clopens X => (s : Set X)) h)
    · intro s
      obtain ⟨a, ha, h⟩ := exists_idempotent_basicOpen_eq_of_isClopen X s s.isClopen
      exact ⟨⟨a, ha⟩, SetLike.coe_injective h⟩)

variable {X} {Y : Scheme.{u}}

/-- A scheme morphism bijective on actual global structure sections extends
every clopen of its source to a clopen of its target. -/
theorem exists_scheme_clopen_extension (f : Y ⟶ X)
    (h : Function.Bijective f.appTop) (s : Set Y) (hs : IsClopen s) :
    ∃ t : Set X, IsClopen t ∧ f ⁻¹' t = s := by
  obtain ⟨b, hb, hbs⟩ := exists_idempotent_basicOpen_eq_of_isClopen Y s hs
  let e := RingEquiv.ofBijective f.appTop.hom h
  let a := e.symm b
  have ha : IsIdempotentElem a := hb.map e.symm
  refine ⟨X.basicOpen a, isClopen_basicOpen_of_idempotent X a ha, ?_⟩
  have hab : f.appTop a = b := e.apply_symm_apply b
  have he := Scheme.preimage_basicOpen_top f a
  rw [hab] at he
  exact (congrArg (fun U : Y.Opens => (U : Set Y)) he).trans hbs

/-- Injectivity on actual global structure sections detects whether a
clopen has empty inverse image. -/
theorem scheme_clopen_preimage_eq_empty_iff (f : Y ⟶ X)
    (h : Function.Injective f.appTop) (s : Set X) (hs : IsClopen s) :
    f ⁻¹' s = ∅ ↔ s = ∅ := by
  constructor
  · intro h0
    obtain ⟨a, ha, has⟩ := exists_idempotent_basicOpen_eq_of_isClopen X s hs
    have hba : Y.basicOpen (f.appTop a) = ⊥ := by
      apply Opens.ext
      rw [← Scheme.preimage_basicOpen_top]
      change f ⁻¹' (X.basicOpen a : Set X) = ∅
      rwa [has]
    have hfa := (idempotent_eq_zero_iff_basicOpen_eq_bot Y _ (ha.map f.appTop.hom)).mpr hba
    have ha0 : a = 0 := h (hfa.trans (map_zero f.appTop.hom).symm)
    rw [← has, ha0, X.basicOpen_zero]
    rfl
  · rintro rfl
    rfl

end SGA.SGA2.ExposeIII
