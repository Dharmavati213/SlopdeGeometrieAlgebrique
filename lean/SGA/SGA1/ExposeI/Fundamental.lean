/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.Topology.Connected.Clopen
import SGA.SGA1.ExposeI.Etale

/-!
# SGA 1, Exposé I, §5: the fundamental property of étale morphisms

The main theorem I.5.1 is that an étale radicial morphism is an open immersion.
Mathlib calls radicial morphisms `UniversallyInjective` (injective with purely
inseparable residue extensions, Stacks 01S4). The argument recorded here is:
the diagonal of an étale morphism is an open immersion, a radicial morphism has
surjective diagonal, so the diagonal is an isomorphism and the morphism is a
monomorphism; a flat monomorphism of finite presentation is an open immersion.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.1, sufficiency: an étale universally injective morphism is an open immersion. -/
theorem isOpenImmersion_of_etale_of_universallyInjective [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, (UniversallyInjective.iff_diagonal f).mp inferInstance⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f

/-- I.5.1, necessity: an open immersion is étale and radicial. -/
theorem etale_and_universallyInjective_of_isOpenImmersion [IsOpenImmersion f] :
    Etale f ∧ UniversallyInjective f :=
  ⟨inferInstance, inferInstance⟩

/-- I.5.1: étale and radicial if and only if an open immersion. -/
theorem isOpenImmersion_iff_etale_and_universallyInjective :
    IsOpenImmersion f ↔ Etale f ∧ UniversallyInjective f :=
  ⟨fun _ ↦ etale_and_universallyInjective_of_isOpenImmersion f,
    fun ⟨_, _⟩ ↦ isOpenImmersion_of_etale_of_universallyInjective f⟩

/-- I.5.2, first step: a closed immersion which is étale is an open immersion. -/
theorem isOpenImmersion_of_isClosedImmersion_of_etale [IsClosedImmersion f] [Etale f] :
    IsOpenImmersion f :=
  isOpenImmersion_of_etale_of_universallyInjective f

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y) [IsSeparated f] :
    IsClosedImmersion s := by
  have : IsIso (s ≫ f) := hs.symm ▸ inferInstance
  have : IsClosedImmersion (s ≫ f) := inferInstance
  exact IsClosedImmersion.of_comp s f

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of an unramified morphism is étale. -/
theorem etale_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : Etale s := by
  have : Etale (s ≫ f) := hs.symm ▸ (inferInstance : Etale (𝟙 Y))
  exact Etale.of_comp s f

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of a separated unramified morphism is an open immersion. -/
theorem isOpenImmersion_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f] : IsOpenImmersion s := by
  have := isClosedImmersion_of_section f hs
  have := etale_of_section f hs
  exact isOpenImmersion_of_isClosedImmersion_of_etale s

/-- I.5.5, uniqueness: morphisms into an étale (or merely formally unramified) scheme
over a nilpotent closed immersion are unique. This is the uniqueness half of the
infinitesimal lifting property. -/
theorem hom_ext_of_formallyUnramified {Z' Z : Scheme.{u}} (i : Z' ⟶ Z)
    (hi : IsNilpotent i.ker) [IsClosedImmersion i] {g₁ g₂ : Z ⟶ X}
    (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) [FormallyUnramified f] : g₁ = g₂ :=
  FormallyUnramified.hom_ext i hi f hig hgf

/-- I.5.6: uniqueness of an extension of a lifting across a bijective closed immersion. -/
theorem unique_lifting {Z' Z : Scheme.{u}} (i : Z' ⟶ Z) (hi : IsNilpotent i.ker)
    [IsClosedImmersion i] (g : Z ⟶ Y) (h : Z' ⟶ X) (_w : h ≫ f = i ≫ g)
    [FormallyUnramified f] (g₁ g₂ : Z ⟶ X) (hg₁ : i ≫ g₁ = h) (hg₂ : i ≫ g₂ = h)
    (hgf₁ : g₁ ≫ f = g) (hgf₂ : g₂ ≫ f = g) : g₁ = g₂ :=
  hom_ext_of_formallyUnramified f i hi (hg₁.trans hg₂.symm) (hgf₁.trans hgf₂.symm)


set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: a section of a separated unramified morphism is an open immersion and a
closed immersion. -/
theorem isOpenImmersion_and_isClosedImmersion_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion s ∧ IsClosedImmersion s :=
  ⟨isOpenImmersion_of_section f hs, isClosedImmersion_of_section f hs⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- I.5.3: the image of a section is clopen. -/
theorem isClopen_range_of_section {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsClopen (Set.range s.base) := by
  have hopen : IsOpenImmersion s := isOpenImmersion_of_section f hs
  have hclosed : IsClosedImmersion s := isClosedImmersion_of_section f hs
  exact ⟨(Scheme.Hom.isClosedEmbedding s).isClosed_range,
    (Scheme.Hom.isOpenEmbedding s).isOpen_range⟩

/-- I.5.4: morphisms into a formally unramified target that agree after a nilpotent
closed immersion are equal. Geometric agreement at a point of a connected source
reduces to this after viewing the two morphisms as sections of `X ×_S Y → Y`
(I.5.3). -/
theorem eq_of_comp_eq_of_formallyUnramified {Z' Z : Scheme.{u}} (i : Z' ⟶ Z)
    (hi : IsNilpotent i.ker) [IsClosedImmersion i] {g₁ g₂ : Z ⟶ X}
    (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) [FormallyUnramified f] :
    g₁ = g₂ :=
  hom_ext_of_formallyUnramified f i hi hig hgf

end SGA.SGA1.ExposeI
