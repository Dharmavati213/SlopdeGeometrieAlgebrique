/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.QuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# `Ω_{X/Y}` of a smooth morphism

If `f : X ⟶ Y` is smooth of relative dimension `n`, then `Ω_{X/Y}` is locally free of rank `n`:
every point has an affine open neighbourhood `U` with `Ω_{X/Y}|_U ≅ 𝒪_U^n`
(`Scheme.Hom.exists_relativeDifferentials_restrict_iso_free`; EGA IV 17.2.3, Stacks Project,
Tag 02G1). For a smooth `f`, `Ω_{X/Y}` is locally free
(`Scheme.Hom.isLocallyFree_relativeDifferentials`) and `Γ(U, Ω_{X/Y})` is a projective
`Γ(X, U)`-module for affine opens `U ⊆ f⁻¹ V`.
-/

universe u

open CategoryTheory Limits TopologicalSpace

section Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is standard smooth of relative dimension `n` over `R`, then `Ω_{S/R} ≅ S^n`. -/
lemma Algebra.IsStandardSmoothOfRelativeDimension.nonempty_kaehlerDifferential_equiv (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n R S] : Nonempty (Ω[S⁄R] ≃ₗ[S] (Fin n →₀ S)) := by
  cases subsingleton_or_nontrivial S
  · have : Subsingleton Ω[S⁄R] := Module.subsingleton S _
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hr := IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := S) n
  have : Module.Finite S Ω[S⁄R] := Module.finite_of_rank_eq_nat hr
  exact ⟨(Module.finBasisOfFinrankEq S Ω[S⁄R] (Module.finrank_eq_of_rank_eq hr)).repr⟩

end Algebra

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `tilde` sends isomorphic modules to isomorphic sheaves. -/
noncomputable def _root_.AlgebraicGeometry.tildeMapIso {A : CommRingCat.{u}} {M N : ModuleCat A}
    (e : M ≅ N) : tilde M ≅ tilde N where
  hom := tilde.map e.hom
  inv := tilde.map e.inv
  hom_inv_id := by rw [← tilde.map_comp, e.hom_inv_id, tilde.map_id]
  inv_hom_id := by rw [← tilde.map_comp, e.inv_hom_id, tilde.map_id]

/-- If `f` is smooth of relative dimension `n`, then `Ω_{X/Y}` is free of rank `n` on an affine
open neighbourhood of every point (EGA IV 17.2.3; Stacks Project, Tag 02G1). -/
theorem exists_relativeDifferentials_restrict_iso_free (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) : ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      Nonempty (f.relativeDifferentials.restrict hU.fromSpec ≅
        SheafOfModules.free (ULift.{u} (Fin n))) := by
  obtain ⟨V, hV, U, hU, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  let φ := f.appLE V U e
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, V) Γ(X, U) := h
  obtain ⟨l⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_kaehlerDifferential_equiv
      (R := Γ(Y, V)) (S := Γ(X, U)) n
  refine ⟨U, hU, hx, ⟨?_⟩⟩
  let l' : CommRingCat.KaehlerDifferential φ ≅
      ModuleCat.of Γ(X, U) (ULift.{u} (Fin n) →₀ Γ(X, U)) :=
    (l.trans (Finsupp.domLCongr Equiv.ulift.symm)).toModuleIso
  exact f.relativeDifferentialsFromSpecIso hU hV e ≪≫ tildeMapIso l' ≪≫ tildeFinsupp _

/-- If `f` is smooth, then `Ω_{X/Y}` is free of finite rank on an affine open neighbourhood of
every point (Stacks Project, Tag 02G1). -/
theorem exists_relativeDifferentials_restrict_iso_free_of_smooth [Smooth f] (x : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (ι : Type u), x ∈ U ∧ Finite ι ∧
      Nonempty (f.relativeDifferentials.restrict hU.fromSpec ≅ SheafOfModules.free ι) := by
  obtain ⟨V, hV, U, hU, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let φ := f.appLE V U e
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, V) Γ(X, U) := h
  let ι := Module.Free.ChooseBasisIndex Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)]
  let l : CommRingCat.KaehlerDifferential φ ≅ ModuleCat.of Γ(X, U) (ι →₀ Γ(X, U)) :=
    (Module.Free.chooseBasis Γ(X, U) Ω[Γ(X, U)⁄Γ(Y, V)]).repr.toModuleIso
  exact ⟨U, hU, ι, hx, inferInstance,
    ⟨f.relativeDifferentialsFromSpecIso hU hV e ≪≫ tildeMapIso l ≪≫ tildeFinsupp _⟩⟩

open Scheme.Modules in
/-- The sheaf of differentials of a smooth morphism is locally free (Stacks Project, Tag 02G1). -/
instance isLocallyFree_relativeDifferentials [Smooth f] :
    f.relativeDifferentials.IsLocallyFree := by
  choose U hU ι hx _ e using f.exists_relativeDifferentials_restrict_iso_free_of_smooth
  refine isLocallyFree_of_forall_pullback (fun x ↦ (hU x).fromSpec)
    (fun x ↦ ⟨x, by rw [(hU x).range_fromSpec]; exact hx x⟩) fun x ↦ ?_
  exact isLocallyFree_of_iso ((e x).some.symm ≪≫ (restrictFunctorIsoPullback _).app _)

end Scheme.Hom

end AlgebraicGeometry
