/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Analysis.RCLike.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.Topology.LocallyContractible
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.FiniteLimits
import SGA.SGA1.ExposeXII.SchemePoints

/-!
# SGA 1, Exposé XII: points of smooth schemes

For `X` smooth over `𝕜 = ℝ` or `ℂ`, the space `X(𝕜)` is locally homeomorphic to `𝕜ⁿ`: near
every point, `X` is étale over an affine space
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`), and étale maps give local
homeomorphisms (`Points.isLocalHomeomorph_proj_of_isStandardEtale`).
Hence `X(𝕜)` is strongly locally contractible (`Points.stronglyLocallyContractibleSpace_of_smooth`,
`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`), so it is locally path-connected and
semilocally simply connected, and its finite coverings are classified by `π₁` (XII.5.2).

In SGA (XII.2.1, XII.3.1), `X^an` is smooth when `X` is. The proof of XII.5.2 uses, without
comment and for arbitrary `X`, that every finite covering of `X^an` is a quotient of the universal
covering, which holds because `X^an` is locally path-connected and semilocally simply connected.
This file covers the smooth case; the general case is proved without triangulation in
`LocalTopologyLPC.lean` (`locallyPathConnectedStatement`) and `LocalTopologySLSC.lean`
(`semilocallySimplyConnectedStatement`).
-/

noncomputable section

universe u v

open Topology Set

namespace SGA.SGA1.ExposeXII

namespace Points

variable {𝕜 : Type u} [RCLike 𝕜] {A : Type v} [CommRing A] [Algebra 𝕜 A]

/-- XII.2.1, smooth case: for `A` smooth over `𝕜 = ℝ` or `ℂ`, every point of `X(𝕜)` has an open
neighbourhood `V(𝕜)`, `V` a basic open, together with a local homeomorphism `V(𝕜) → 𝕜ⁿ`. -/
theorem exists_isOpenEmbedding_isLocalHomeomorph_of_smooth [Algebra.Smooth 𝕜 A]
    (φ : Points 𝕜 A) : ∃ (B : Type v) (_ : CommRing B) (_ : Algebra 𝕜 B)
      (ι : Points 𝕜 B → Points 𝕜 A) (n : ℕ) (π : Points 𝕜 B → (Fin n → 𝕜)),
      IsOpenEmbedding ι ∧ φ ∈ range ι ∧ IsLocalHomeomorph π := by
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hfQ, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := 𝕜) (p := Q)
  refine ⟨Localization.Away f, inferInstance, inferInstance,
    map (IsScalarTower.toAlgHom 𝕜 A (Localization.Away f)), n,
    homeomorphMvPolynomial (Fin n) ∘ proj (MvPolynomial (Fin n) 𝕜) (Localization.Away f),
    isOpenEmbedding_map_of_isLocalizationAway f, ?_,
    (homeomorphMvPolynomial (Fin n)).isLocalHomeomorph.comp
      (isLocalHomeomorph_proj_of_isStandardEtale (𝕜 := 𝕜) (A := MvPolynomial (Fin n) 𝕜)
        (B := Localization.Away f))⟩
  rw [range_map_of_isLocalizationAway f]
  exact hfQ

/-- XII.2.1, smooth case: for `A` smooth over `𝕜 = ℝ` or `ℂ`, `X(𝕜)` is strongly locally
contractible (being locally homeomorphic to `𝕜ⁿ`). -/
theorem stronglyLocallyContractibleSpace_of_smooth [Algebra.Smooth 𝕜 A] :
    StronglyLocallyContractibleSpace (Points 𝕜 A) := by
  refine .of_isOpen_cover fun φ ↦ ?_
  obtain ⟨B, _, _, ι, n, π, hι, hφ, hπ⟩ := exists_isOpenEmbedding_isLocalHomeomorph_of_smooth φ
  have := hπ.stronglyLocallyContractibleSpace
  exact ⟨range ι, hι.isOpen_range, hφ,
    hι.toHomeomorph.symm.isLocalHomeomorph.stronglyLocallyContractibleSpace⟩

end Points

namespace SchemePoints

open AlgebraicGeometry CategoryTheory

attribute [local instance] sectionsAlgebra

/-- The sections over an affine open of a smooth `K`-scheme form a smooth `K`-algebra. -/
lemma smooth_sections {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [Smooth (X ↘ Spec (.of K))] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.Smooth K Γ(X, U) := by
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_)
    (HasRingHomProperty.appLE @Smooth (X ↘ Spec (.of K)) ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (le_top.trans_eq (Scheme.Hom.preimage_top _).symm))
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv

/-- XII.2.1, smooth case: for `X` smooth over `𝕜 = ℝ` or `ℂ`, `X(𝕜)` is strongly locally
contractible (being locally homeomorphic to `𝕜ⁿ`); in particular it is locally path-connected
and semilocally simply connected. -/
theorem stronglyLocallyContractibleSpace_of_smooth {𝕜 : Type u} [RCLike 𝕜] (X : Scheme.{u})
    [X.Over (Spec (.of 𝕜))] [Smooth (X ↘ Spec (.of 𝕜))] :
    StronglyLocallyContractibleSpace (SchemePoints 𝕜 X) := by
  refine .of_isOpen_cover fun p ↦ ?_
  obtain ⟨U, hU, hpU⟩ := exists_isAffineOpen_mem p
  have := smooth_sections (K := 𝕜) hU
  have := Points.stronglyLocallyContractibleSpace_of_smooth (𝕜 := 𝕜) (A := Γ(X, U))
  have hc := isOpenEmbedding_chart (K := 𝕜) hU
  refine ⟨range (chart hU), hc.isOpen_range, ?_,
    hc.toHomeomorph.symm.isLocalHomeomorph.stronglyLocallyContractibleSpace⟩
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hpU
  exact mem_range_self φ

end SchemePoints

end SGA.SGA1.ExposeXII
