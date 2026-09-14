/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Trace.Basic
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


/-! ## I.4.4 and I.4.10 -/

open IsLocalRing AdicCompletion

/-- I.4.4: if `B/A` is finite étale with surjective residue-field map, the algebra map
is surjective (I.3.7). -/
theorem algebraMap_surjective_of_etale
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [EssFiniteType R S] [Etale R S] [Module.Finite R S]
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Surjective (algebraMap R S) :=
  algebraMap_surjective_of_formallyUnramified hres

/-- I.4.4: the map of `m`-adic completions is surjective under the same hypotheses. -/
theorem adicCompletion_surjective_of_etale
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [EssFiniteType R S] [Etale R S] [Module.Finite R S]
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Surjective (AdicCompletion.map (maximalIdeal R) (Algebra.linearMap R S)) :=
  adicCompletion_surjective_of_formallyUnramified hres

/-- I.4.4, isomorphism form: injective + finite étale + surjective residue ⇒ isomorphism. -/
theorem algebraMap_bijective_of_etale_of_injective
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [EssFiniteType R S] [Etale R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Bijective (algebraMap R S) :=
  ⟨hinj, algebraMap_surjective_of_etale hres⟩

/-- I.4.4: a bijective algebra map induces a bijective map of completions. -/
theorem adicCompletion_bijective_of_bijective_algebraMap
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S]
    (hbij : Function.Bijective (algebraMap R S)) :
    Function.Bijective (AdicCompletion.map (maximalIdeal R) (Algebra.linearMap R S)) :=
  ⟨AdicCompletion.map_injective _ hbij.1, AdicCompletion.map_surjective _ hbij.2⟩

/-- I.4.10, over a field: a finite field extension is étale iff it is separable. -/
theorem etale_iff_isSeparable_of_field {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] :
    Etale K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ (Algebra.FormallyEtale.iff_isSeparable K L).mp inferInstance,
    fun h ↦ by
      have : FormallyEtale K L := (Algebra.FormallyEtale.iff_isSeparable K L).mpr h
      have : IsNoetherianRing K := inferInstance
      have : FiniteType K L := inferInstance
      have : FinitePresentation K L :=
        (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp ‹_›
      exact ⟨inferInstance, inferInstance⟩⟩

/-- I.4.10: for a finite étale field extension, the discriminant of any basis is a unit. -/
theorem discr_isUnit_of_etale_field {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Etale K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : IsUnit (Algebra.discr K (b : ι → L)) := by
  have : Algebra.IsSeparable K L := (etale_iff_isSeparable_of_field (K := K) (L := L)).mp ‹_›
  exact Algebra.discr_isUnit_of_basis (K := K) (L := L) b

/-- I.4.10: separability characterises étaleness of finite field extensions; combined with
`Algebra.discr_isUnit_of_basis` this is the discriminant / trace-pairing criterion. -/
theorem etale_of_isSeparable_field {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : Algebra.IsSeparable K L) : Etale K L :=
  (etale_iff_isSeparable_of_field (K := K) (L := L)).mpr h

/-- I.4.10 on a general base: the coherent discriminant section of a finite locally
free algebra is the determinant of its trace pairing on local frames. Mathlib
has `Algebra.discr` for free families and the field-case unit criterion above,
but not the sheafified discriminant on an arbitrary base scheme. -/
theorem discr_isUnit_of_etale_of_basis_field {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Etale K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : IsUnit (Algebra.discr K (b : ι → L)) :=
  discr_isUnit_of_etale_field (K := K) (L := L) b

end SGA.SGA1.ExposeI
