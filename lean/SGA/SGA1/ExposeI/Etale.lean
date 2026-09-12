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
import SGA.SGA1.ExposeI.Unramified

/-!
# SGA 1, Exposé I, §4: étale morphisms and étale coverings

SGA defines étale as flat and unramified, for morphisms of finite type.
Mathlib's `Etale` is formally étale and of finite presentation, equivalently
flat, formally unramified, and locally of finite presentation. Over a locally
noetherian base the finite-type and finite-presentation conditions agree, so
the two definitions match the exposé's standing locally noetherian hypothesis.
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

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
/-- I.4.7: a fibre product of étale morphisms is étale. -/
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
