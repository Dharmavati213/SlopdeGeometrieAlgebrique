/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.QuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Unramified morphisms and `Ω_{X/Y}`

A morphism of schemes `f : X ⟶ Y` is formally unramified if and only if `Ω_{X/Y} = 0`
(`Scheme.Hom.isZero_relativeDifferentials_iff`; EGA IV 17.4.2, Stacks Project, Tag 02GE for the
locally of finite type case). In particular `Ω_{X/Y} = 0` for étale `f`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry


namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma subsingleton_kaehlerDifferential_iff {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    Subsingleton (CommRingCat.KaehlerDifferential φ) ↔ φ.hom.FormallyUnramified := by
  let := φ.hom.toAlgebra
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.subsingleton_kaehlerDifferential⟩

/-- `Ω_{X/Y} = 0` if and only if `f` is formally unramified (EGA IV 17.4.2; Stacks Project,
Tag 02GE). -/
theorem isZero_relativeDifferentials_iff :
    IsZero f.relativeDifferentials ↔ FormallyUnramified f := by
  rw [Scheme.Modules.isZero_iff_forall_subsingleton, formallyUnramified_iff]
  constructor
  · intro h V hV U hU e
    rw [← subsingleton_kaehlerDifferential_iff]
    exact (f.relativeDifferentialsAppEquiv hU hV e).symm.toEquiv.subsingleton
  · intro h W
    refine ⟨fun s t ↦ ?_⟩
    rw [← sub_eq_zero]
    refine Scheme.Modules.eq_zero_of_locally _ fun x hx ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V ⊓ W from ⟨hxV, hx⟩) (f ⁻¹ᵁ V ⊓ W).2
    refine ⟨U, hUV.trans inf_le_right, hxU, ?_⟩
    have : Subsingleton (CommRingCat.KaehlerDifferential (f.appLE V U (hUV.trans inf_le_left))) :=
      (subsingleton_kaehlerDifferential_iff _).mpr (h hV hU _)
    have := (f.relativeDifferentialsAppEquiv hU hV (hUV.trans inf_le_left)).toEquiv.subsingleton
    exact Subsingleton.elim _ _

/-- `Ω_{X/Y} = 0` for a formally unramified morphism. -/
theorem isZero_relativeDifferentials [FormallyUnramified f] : IsZero f.relativeDifferentials :=
  (f.isZero_relativeDifferentials_iff).mpr ‹_›

/-- `Ω_{X/Y} = 0` for an étale morphism. -/
theorem isZero_relativeDifferentials_of_etale [Etale f] : IsZero f.relativeDifferentials :=
  f.isZero_relativeDifferentials

end Scheme.Hom

end AlgebraicGeometry
