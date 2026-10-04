/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.KrullDimension
import SGA.Foundations.Topology.PathConnectedHelpers
import SGA.SGA1.ExposeXII.BranchedCover
import SGA.SGA1.ExposeXII.LocalTopology

/-!
# SGA 1, Exposé XII, 5.2: `X(ℂ)` is locally path-connected

For `X` locally of finite type over `ℂ`, the space `X(ℂ)` is locally path-connected
(`SchemePoints.locallyPathConnectedSpace`, an instance, so `LocallyPathConnectedStatement` holds:
`locallyPathConnectedStatement`). This is half of the topological input of XII.5.2, which SGA uses
implicitly ("every finite étale covering of `X^an` is a quotient of the universal covering").
Consequently XII.5.2 follows from the Riemann existence theorem XII.5.1 and the semilocal simple
connectedness of `X(ℂ)` (`schemeFundamentalGroupComparison_of_semilocallySimplyConnected`,
and pointwise in `X`: `schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace`).
The semilocal simple connectedness is proved in `LocalTopologySLSC.lean`
(`semilocallySimplyConnectedStatement`), so XII.5.2 follows from XII.5.1 alone
(`schemeFundamentalGroupComparison_of_riemannExistence`, which supersedes the first theorem).

The proof avoids triangulation: for `X = Spec B`, `B` a domain, `X(ℂ)` is a branched covering of
`ℂˢ` (`Points.locallyPathConnectedSpace_of_isDomain`, `BranchedCover.lean`); in general `X(ℂ)` is
the finite union of the closed subsets `V(𝔭)(ℂ)`, `𝔭` a minimal prime
(`Points.exists_mem_minimalPrimes_mem_range`), and local path-connectedness is local on `X`
(`SchemePoints.exists_isOpenEmbedding_points`: `X(ℂ)` is covered by open subsets `Spec(A)(ℂ)`).
-/

universe u

open Topology Set AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace Points

section MinimalPrimes

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]

/-- The `K`-points of `V(I) ⊆ Spec A` are the points whose kernel contains `I`. -/
lemma mem_range_map_quotient_iff {I : Ideal A} {φ : Points K A} :
    φ ∈ range (Points.map (K := K) (Ideal.Quotient.mkₐ K I)) ↔ I ≤ ker φ := by
  rw [range_map_of_surjective (Ideal.Quotient.mkₐ_surjective K I)]
  simp only [mem_ofPred_eq, RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h a ha ↦ mem_ker.mpr (h a ha), fun h a ha ↦ mem_ker.mp (h ha)⟩

/-- Every `K`-point of `Spec A` lies on an irreducible component: in `V(𝔭)(K)` for a minimal
prime `𝔭`. -/
lemma exists_mem_minimalPrimes_mem_range (φ : Points K A) :
    ∃ p ∈ minimalPrimes A, φ ∈ range (Points.map (K := K) (Ideal.Quotient.mkₐ K p)) := by
  obtain ⟨p, hp, hpφ⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ ker φ)
  exact ⟨p, hp, mem_range_map_quotient_iff.mpr hpφ⟩

end MinimalPrimes

/-- Reduction of a property of `Spec(A)(ℂ)`, `A` of finite type over `ℂ`, to the case of a
quotient `A' = ℂ[z₁, …, zₙ]/I` of a polynomial ring, which lives in `Type` (needed by
`Points.exists_branchedCover`). -/
lemma exists_algEquiv_quotient (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
      Nonempty ((MvPolynomial (Fin n) ℂ ⧸ I) ≃ₐ[ℂ] A) := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  exact ⟨n, RingHom.ker q, ⟨Ideal.quotientKerAlgEquivOfSurjective hq⟩⟩

/-- XII.5.2, topological input, affine case: for `A` of finite type over `ℂ`, the space `X(ℂ)`
of `X = Spec A` is locally path-connected. -/
instance locallyPathConnectedSpace (A : Type u) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : LocallyPathConnectedSpace (Points ℂ A) := by
  -- reduce to `A` in `Type`
  obtain ⟨n, I, ⟨e⟩⟩ := exists_algEquiv_quotient A
  let A' := MvPolynomial (Fin n) ℂ ⧸ I
  suffices LocallyPathConnectedSpace (Points ℂ A') from
    (Points.homeomorph e).symm.locallyPathConnectedSpace
  -- the irreducible components `V(𝔭)(ℂ)` form a finite closed cover
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing ℂ A'
  have : Finite (minimalPrimes A') := (minimalPrimes.finite_of_isNoetherianRing A').to_subtype
  have hemb (p : minimalPrimes A') :
      IsClosedEmbedding (Points.map (K := ℂ) (Ideal.Quotient.mkₐ ℂ (p : Ideal A'))) :=
    isClosedEmbedding_map_of_surjective (Ideal.Quotient.mkₐ_surjective ℂ _)
  refine .of_finite_isClosed_cover (fun p ↦ (hemb p).isClosed_range) (fun φ ↦ ?_) fun p ↦ ?_
  · obtain ⟨p, hp, hφ⟩ := exists_mem_minimalPrimes_mem_range φ
    exact ⟨⟨p, hp⟩, hφ⟩
  · have : (p : Ideal A').IsPrime := p.2.1.1
    have := locallyPathConnectedSpace_of_isDomain (A' ⧸ (p : Ideal A'))
    exact (hemb p).isEmbedding.toHomeomorph.locallyPathConnectedSpace

end Points

namespace SchemePoints

attribute [local instance] sectionsAlgebra

/-- `X(ℂ)` is covered by open subsets `Spec(A)(ℂ)`, `A = Γ(X, U)` of finite type over `ℂ` for
affine opens `U ⊆ X`, with `dim A ≤ dim X`. Properties of `X(ℂ)` which are local (for open covers)
and invariant under homeomorphisms reduce to the affine case this way. -/
theorem exists_isOpenEmbedding_points (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (p : SchemePoints ℂ X) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℂ A) (_ : Algebra.FiniteType ℂ A)
      (f : Points ℂ A → SchemePoints ℂ X), IsOpenEmbedding f ∧ p ∈ range f ∧
      ringKrullDim A ≤ topologicalKrullDim X := by
  obtain ⟨U, hU, hpU⟩ := exists_isAffineOpen_mem p
  have := finiteType_sections (K := ℂ) hU
  refine ⟨Γ(X, U), inferInstance, inferInstance, inferInstance, chart hU,
    isOpenEmbedding_chart (K := ℂ) hU, ?_, ?_⟩
  · obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hpU
    exact mem_range_self φ
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    change topologicalKrullDim (Spec Γ(X, U)) ≤ _
    rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
    exact topologicalKrullDim_subspace_le X U

/-- XII.5.2, topological input: for `X` locally of finite type over `ℂ`, the space `X(ℂ)` is
locally path-connected. -/
instance locallyPathConnectedSpace (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] : LocallyPathConnectedSpace (SchemePoints ℂ X) := by
  refine .of_isOpen_cover fun p ↦ ?_
  obtain ⟨A, _, _, _, f, hf, hp, -⟩ := exists_isOpenEmbedding_points X p
  exact ⟨range f, hf.isOpen_range, hp, hf.isEmbedding.toHomeomorph.locallyPathConnectedSpace⟩

end SchemePoints

/-- XII.5.2, topological input: `X(ℂ)` is locally path-connected for every `X` locally of finite
type over `ℂ`. -/
theorem locallyPathConnectedStatement : LocallyPathConnectedStatement :=
  fun X _ _ ↦ SchemePoints.locallyPathConnectedSpace X

/-- XII.5.2 for one `X`, from the Riemann existence theorem XII.5.1 and the semilocal simple
connectedness of `X(ℂ)`: for `X` connected and locally of finite type over `ℂ`, `π₁(X, x)` is the
profinite completion of `π₁(X(ℂ), x)`. (`X(ℂ)` is locally path-connected by
`SchemePoints.locallyPathConnectedSpace`, and connected by XII.2.4.) -/
theorem schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace
    (H : SchemeRiemannExistenceStatement) (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]
    (hc : ConnectedSpace X) (x : SchemePoints ℂ X) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x))) :=
  have := SchemePoints.connectedComparison X hc
  have := H X
  nonempty_etaleFundamentalGroup_continuousMulEquiv ℂ x

/-- XII.5.2 from the Riemann existence theorem XII.5.1 and the semilocal simple connectedness of
`X(ℂ)`: for `X` connected and locally of finite type over `ℂ`, `π₁(X, x)` is the profinite
completion of `π₁(X(ℂ), x)`. (The local path-connectedness of `X(ℂ)`, the other half of the
topological input, is `locallyPathConnectedStatement`.) The hypothesis `Hs` is proved
(`semilocallySimplyConnectedStatement`), so this is superseded by
`schemeFundamentalGroupComparison_of_riemannExistence` (`LocalTopologySLSC.lean`). -/
theorem schemeFundamentalGroupComparison_of_semilocallySimplyConnected
    (H : SchemeRiemannExistenceStatement) (Hs : SemilocallySimplyConnectedStatement) :
    SchemeFundamentalGroupComparisonStatement := fun X _ _ hX x ↦
  have := Hs X
  schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace H X hX x

end SGA.SGA1.ExposeXII
