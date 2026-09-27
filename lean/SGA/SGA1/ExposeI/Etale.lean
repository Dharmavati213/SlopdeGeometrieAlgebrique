/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SGA.SGA1.ExposeI.Completion
import SGA.SGA1.ExposeI.Unramified

/-!
# SGA 1, Exposé I, §4: étale morphisms and étale coverings

SGA defines étale as flat and unramified, for morphisms of finite type.
Mathlib's `Etale` is formally étale and of finite presentation, equivalently
flat, formally unramified, and locally of finite presentation. Over a locally
noetherian base the finite-type and finite-presentation conditions agree, so
the two definitions match the exposé's standing locally noetherian hypothesis.

For local homomorphisms SGA's definition b) is `IsEtaleLocalHom` (flat and
unramified in the sense of I.3.2 b)). Corollary I.4.4 is proved here in the direction
"étale ⇒ `Â ≅ B̂`" in the equivalent form that every `A/𝔪ⁿ → B/𝔪_Bⁿ` is bijective; the
completed forms of I.3.7, I.4.2 and I.4.4 are in `CompletionCriteria`. For
schemes, the set of points where a morphism locally of finite presentation is étale
is open (I.4.5, `etaleLocusOpens`).
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry Algebra CategoryTheory CategoryTheory.Limits

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.4.1: an algebra is étale iff it is formally étale of finite presentation. -/
theorem etale_iff : Etale R S ↔ FormallyEtale R S ∧ FinitePresentation R S :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- I.4.1: étale is equivalent to flat, formally unramified, and of finite presentation. -/
theorem etale_iff_flat_unramified_finitePresentation :
    Etale R S ↔ Module.Flat R S ∧ FormallyUnramified R S ∧ FinitePresentation R S :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ ↦ .of_formallyUnramified_of_flat⟩

/-- I.4.1, over a field: étale algebras are finite products of finite separable extensions. -/
theorem etale_over_field_iff {K : Type u} [Field K] [Algebra K S] :
    Etale K S ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : S ≃ₐ[K] ∀ i, Ai i),
        ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := S)

/-- I.4.1 b): a local homomorphism `A → B` is étale if `B` is flat over `A` and
unramified in the sense of I.3.2 b). -/
def IsEtaleLocalHom (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] : Prop :=
  Module.Flat R S ∧ IsUnramifiedLocalHom R S

section Local

open IsLocalRing

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- I.4.4, necessity, with completions replaced by their truncations: if `A → B` is étale
with trivial residue field extension (or `k(A)` algebraically closed), every
`A/𝔪_Aⁿ → B/𝔪_Bⁿ` is bijective, i.e. `Â → B̂` is an isomorphism. -/
theorem bijective_quotientMap_pow_of_isEtaleLocalHom (h : IsEtaleLocalHom R S)
    (hk : Function.Bijective (ResidueField.map (algebraMap R S)) ∨ IsAlgClosed (ResidueField R))
    (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal S ^ n) (algebraMap R S)
      (maximalIdeal_pow_le_comap R S n)) := by
  obtain ⟨hflat, hm, hfin, -⟩ := h
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := R) (B := S)
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← hm, ← Ideal.map_pow,
      ← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    have hsurj : Function.Surjective (ResidueField.map (algebraMap R S)) := by
      rcases hk with hk | hk
      · exact hk.2
      · exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
    obtain ⟨r, hr⟩ := surjective_quotient_pow_of_map_maximalIdeal hm hsurj n y
    exact ⟨Ideal.Quotient.mk _ r, by rw [Ideal.quotientMap_mk]; exact hr⟩

/-- I.3.7, sufficiency, completed form: if `Â → B̂` is surjective (`B` noetherian), then
`A → B` is unramified with trivial residue field extension. -/
theorem isUnramifiedLocalHom_of_surjective_completionMap [IsNoetherianRing S]
    (h : Function.Surjective (completionMap R S)) :
    IsUnramifiedLocalHom R S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) := by
  have H := surjective_quotient_pow_of_surjective_completionMap R S h
  have hk : Function.Bijective (ResidueField.map (algebraMap R S)) :=
    ⟨RingHom.injective _, (map_maximalIdeal_of_surjective_quotient_pow H).2⟩
  exact ⟨(isUnramifiedLocalHom_iff_forall_surjective (Or.inl hk)).mpr H, hk⟩

end Local

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.4.3: whether `f` is étale at `x` only depends on the local homomorphism
`𝒪_{f(x)} → 𝒪_x`: for `f` locally of finite presentation, `f` is étale in a neighbourhood
of `x` iff this map is formally étale. -/
lemma setOf_formallyEtale_stalkMap_eq [LocallyOfFinitePresentation f] :
    {x | (f.stalkMap x).hom.FormallyEtale} =
      (f.smoothLocus : Set X) ∩ (unramifiedLocusOpens f : Set X) := by
  ext x
  let := (f.stalkMap x).hom.toAlgebra
  exact (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth
    (R := Y.presheaf.stalk (f x)) (A := X.presheaf.stalk x)).trans and_comm

/-- I.4.5: the set of points where a morphism locally of finite presentation is étale is
open. -/
def etaleLocusOpens [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{x | (f.stalkMap x).hom.FormallyEtale}, by
    rw [setOf_formallyEtale_stalkMap_eq]
    exact (f.smoothLocus ⊓ unramifiedLocusOpens f).2⟩

/-- I.4.1: a morphism is étale iff it is flat, formally unramified, and
locally of finite presentation. -/
theorem etale_iff_flat_and_formallyUnramified :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f :=
  Etale.iff_flat_and_formallyUnramified

/-- I.4.5: the étale locus of a finitely presented algebra is open. -/
theorem isOpen_etaleLocus [FinitePresentation R S] : IsOpen (etaleLocus R S) :=
  Algebra.isOpen_etaleLocus

/-- I.4.6(i): an open immersion is étale. -/
instance (priority := 900) etale_of_isOpenImmersion [IsOpenImmersion f] : Etale f :=
  inferInstance

/-- I.4.6(ii): the composite of étale morphisms is étale. -/
instance etale_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g] : Etale (f ≫ g) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- I.4.6(iii): étale is stable under base change. -/
instance etale_fst {X' : Scheme.{u}} (g : X' ⟶ Y) [Etale g] : Etale (pullback.fst f g) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- I.4.7, special case: base change along the other projection. SGA's cartesian product
`X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂` of two étale morphisms is not stated here; it follows from I.4.6 (ii)
and (iii). -/
instance etale_snd {X' : Scheme.{u}} (g : X' ⟶ Y) [Etale f] : Etale (pullback.snd f g) :=
  inferInstance

/-- I.4.8: if `X'` is unramified over `Y` and `X` is étale over `Y`, then a
`Y`-morphism `X ⟶ X'` is étale. -/
theorem etale_of_comp_unramified {Z : Scheme.{u}} (g : Y ⟶ Z)
    [Etale (f ≫ g)] [LocallyOfFiniteType g] [FormallyUnramified g] : Etale f :=
  Etale.of_comp f g

/-- I.4.1, under the exposé's locally noetherian hypothesis: finite type plus
formally unramified and flat implies étale. -/
theorem etale_of_flat_unramified_locallyNoetherian [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] : Etale f :=
  Etale.of_formallyUnramified_of_flat f

/-- I.4.9: an étale covering is a finite étale morphism. -/
abbrev IsEtaleCovering : Prop := IsFinite f ∧ Etale f

/-- I.4.9: finite étale algebras, in the affine language of the exposé. -/
abbrev FiniteEtaleAlgebra : Prop := Module.Finite R S ∧ Etale R S

end SGA.SGA1.ExposeI
