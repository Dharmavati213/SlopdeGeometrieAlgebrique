/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalConvergence
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalCoefficientFunctor
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalTotalNaturality
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# Naturality of locally closed ambient support local-to-global convergence

The original spectral-object coefficient morphisms preserve the actual finite
filtration of the total group. Their induced maps on the genuine cokernel
quotients commute with the original stable-page comparisons, while the total
map corresponds to the existing `H_locallyClosed_map` under the original abutment equivalence.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

open SpectralObjectConvergence

variable {X : TopCat.{u}} (W : LocallyClosedIn X)

attribute [local instance] supportedE2_hasDerivedCategory

/-- The actual ambient total group is the original locally closed Ext support group. -/
def locallyClosedCohomologyAbutmentEquiv (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    ↥(total (C := AddCommGrpCat.{u + 1})
      (locallyClosedLocalToGlobalAbelianSpectralObject W I) n) ≃+ H_locallyClosed W F n :=
  locallyClosedSpectralObjectTotalEquiv W I n

/-- The map induced on an actual term of the finite abutment filtration. -/
def locallyClosedCohomologyFiniteFiltrationMap
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    (locallyClosedCohomologyFiniteFiltration W I n q : AddCommGrpCat.{u + 1}) ⟶
      (locallyClosedCohomologyFiniteFiltration W J n q : AddCommGrpCat.{u + 1}) :=
  filtrationSubobjectMap (locallyClosedAbelianSpectralObjectMap W φ) n (q.1 : ℤ)

@[reassoc (attr := simp)]
theorem locallyClosedCohomologyFiniteFiltrationMap_arrow
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    locallyClosedCohomologyFiniteFiltrationMap W φ n q ≫
        (locallyClosedCohomologyFiniteFiltration W J n q).arrow =
      (locallyClosedCohomologyFiniteFiltration W I n q).arrow ≫
        totalMap (locallyClosedAbelianSpectralObjectMap W φ) n :=
  filtrationSubobjectMap_arrow _ _ _

/-- The actual coefficient map of total cohomology preserves its original
finite convergence filtration. -/
theorem locallyClosedTotalMap_preserves_finiteFiltration
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    imageSubobject ((locallyClosedCohomologyFiniteFiltration W I n q).arrow ≫
      totalMap (locallyClosedAbelianSpectralObjectMap W φ) n) ≤
        locallyClosedCohomologyFiniteFiltration W J n q :=
  totalMap_preserves_filtration _ _ _

/-- The genuine associated graded of the original total image filtration. -/
def locallyClosedCohomologyGradedPiece (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 1)) : AddCommGrpCat.{u + 1} :=
  gradedPiece (locallyClosedLocalToGlobalAbelianSpectralObject W I) n q

/-- The actual induced map on the associated-graded cokernels. -/
def locallyClosedCohomologyGradedPieceMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1)) :
    locallyClosedCohomologyGradedPiece W I n q ⟶ locallyClosedCohomologyGradedPiece W J n q :=
  gradedPieceMap (locallyClosedAbelianSpectralObjectMap W φ) n q

/-- The actual coefficient maps commute with the original stable-page to
associated-graded isomorphism of the finite supported-cohomology filtration. -/
@[reassoc]
theorem locallyClosedLocalToGlobalStablePageIsoGraded_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1))
    (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((locallyClosedTruncationSpectralSequenceMap W φ).hom r (by lia)).f ((n : ℤ) - q, q) ≫
        (locallyClosedLocalToGlobalStablePageIsoGraded W J n q r hr).hom =
      (locallyClosedLocalToGlobalStablePageIsoGraded W I n q r hr).hom ≫
        locallyClosedCohomologyGradedPieceMap W φ n q :=
  stablePageIsoGradedTotal_naturality _ n q r hr

/-- The same original stable comparison is natural for the already
constructed coefficient functor, without a supplied resolution lift. -/
@[reassoc]
theorem locallyClosedLocalToGlobalStablePageIsoGraded_coefficient_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((locallyClosedTruncationSpectralSequenceCoefficientMap W f I J).hom r (by lia)).f
        ((n : ℤ) - q, q) ≫ (locallyClosedLocalToGlobalStablePageIsoGraded W J n q r hr).hom =
      (locallyClosedLocalToGlobalStablePageIsoGraded W I n q r hr).hom ≫
        locallyClosedCohomologyGradedPieceMap W (InjectiveResolution.desc f J I) n q := by
  rw [locallyClosedTruncationSpectralSequenceCoefficientMap_eq]
  exact locallyClosedLocalToGlobalStablePageIsoGraded_naturality W _ n q r hr

/-- The filtration-preserving total morphism is the original supported
cohomology coefficient map under the original abutment equivalence. -/
theorem locallyClosedCohomologyAbutmentEquiv_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : ↥(total (C := AddCommGrpCat.{u + 1})
      (locallyClosedLocalToGlobalAbelianSpectralObject W I) n)) :
    locallyClosedCohomologyAbutmentEquiv W J n
        (totalMap (locallyClosedAbelianSpectralObjectMap W φ) n x) =
      H_locallyClosed_map W f n (locallyClosedCohomologyAbutmentEquiv W I n x) :=
  locallyClosedSpectralObjectTotalEquiv_naturality W f I J φ hφ n x

/-- Compatible resolution lifts give identical actual total maps. -/
theorem locallyClosedTotalMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    totalMap (locallyClosedAbelianSpectralObjectMap W φ) n =
      totalMap (locallyClosedAbelianSpectralObjectMap W ψ) n := by
  ext x
  apply (locallyClosedCohomologyAbutmentEquiv W J n).injective
  rw [locallyClosedCohomologyAbutmentEquiv_naturality W f I J φ hφ,
    locallyClosedCohomologyAbutmentEquiv_naturality W f I J ψ hψ]

/-- The actual finite-filtration maps are independent of the resolution lift. -/
theorem locallyClosedCohomologyFiniteFiltrationMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) (q : Fin (n + 2)) :
    locallyClosedCohomologyFiniteFiltrationMap W φ n q =
      locallyClosedCohomologyFiniteFiltrationMap W ψ n q :=
  filtrationSubobjectMap_eq_of_totalMap_eq _ _ _
    (locallyClosedTotalMap_eq_of_lifts W f I J φ ψ hφ hψ n)

/-- The genuine associated-graded coefficient maps also do not depend on
the lift of the coefficient morphism to resolutions. -/
theorem locallyClosedCohomologyGradedPieceMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) (q : Fin (n + 1)) :
    locallyClosedCohomologyGradedPieceMap W φ n q =
      locallyClosedCohomologyGradedPieceMap W ψ n q := by
  rw [← cancel_epi (locallyClosedLocalToGlobalStablePageIsoGraded W I n q
    ((n : ℤ) + 2) le_rfl).hom]
  rw [← locallyClosedLocalToGlobalStablePageIsoGraded_naturality,
    ← locallyClosedLocalToGlobalStablePageIsoGraded_naturality,
    locallyClosedTruncationSpectralSequenceMap_eq_of_lifts W f I J φ ψ hφ hψ]

/-- The original convergence filtration transported along its already
proved abutment equivalence to the original, small-universe `H_locallyClosed`. -/
def locallyClosedCohomologyFiltrationOnExt
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 2)) : AddSubgroup (H_locallyClosed W F n) :=
  ((locallyClosedCohomologyAbutmentEquiv W I n).toAddMonoidHom.comp
    (locallyClosedCohomologyFiniteFiltration W I n q).arrow.hom).range

private lemma addCommGrp_comm_apply {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (i : A ⟶ C) (j : B ⟶ D)
    (h : f ≫ j = i ≫ g) (x : A) : j (f x) = g (i x) :=
  ConcreteCategory.congr_hom h x

/-- Original `H_locallyClosed_map` preserves the original convergence filtration,
transported by its actual abutment equivalence. -/
theorem H_locallyClosed_map_mem_locallyClosedCohomologyFiltration
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (n : ℕ) (q : Fin (n + 2)) {y : H_locallyClosed W F n}
    (hy : y ∈ locallyClosedCohomologyFiltrationOnExt W I n q) :
    H_locallyClosed_map W f n y ∈ locallyClosedCohomologyFiltrationOnExt W J n q := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨locallyClosedCohomologyFiniteFiltrationMap W φ n q x, ?_⟩
  change locallyClosedCohomologyAbutmentEquiv W J n
      ((locallyClosedCohomologyFiniteFiltration W J n q).arrow
        (locallyClosedCohomologyFiniteFiltrationMap W φ n q x)) =
    H_locallyClosed_map W f n (locallyClosedCohomologyAbutmentEquiv W I n
      ((locallyClosedCohomologyFiniteFiltration W I n q).arrow x))
  calc
    _ = locallyClosedCohomologyAbutmentEquiv W J n
        (totalMap (locallyClosedAbelianSpectralObjectMap W φ) n
          ((locallyClosedCohomologyFiniteFiltration W I n q).arrow x)) :=
      congrArg (locallyClosedCohomologyAbutmentEquiv W J n)
        (addCommGrp_comm_apply _ _ _ _ (locallyClosedCohomologyFiniteFiltrationMap_arrow W φ n q) x)
    _ = _ := locallyClosedCohomologyAbutmentEquiv_naturality W f I J φ hφ n _

/-- Filtration preservation for every actual sheaf morphism, with the
resolution comparison constructed rather than assumed. -/
theorem H_locallyClosed_map_mem_locallyClosedCohomologyFiltration_of_mem
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (q : Fin (n + 2)) {y : H_locallyClosed W F n}
    (hy : y ∈ locallyClosedCohomologyFiltrationOnExt W I n q) :
    H_locallyClosed_map W f n y ∈ locallyClosedCohomologyFiltrationOnExt W J n q :=
  H_locallyClosed_map_mem_locallyClosedCohomologyFiltration W f I J
    (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) n q hy

/-- The actual filtration on original `H_locallyClosed` is independent of the chosen
injective resolution, as equality of additive subgroups. -/
theorem locallyClosedCohomologyFiltrationOnExt_independent
    {F : Sheaf AddCommGrpCat.{u} X} (I J : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 2)) :
    locallyClosedCohomologyFiltrationOnExt W I n q =
      locallyClosedCohomologyFiltrationOnExt W J n q := by
  suffices h : ∀ I J : InjectiveResolution F,
      locallyClosedCohomologyFiltrationOnExt W I n q ≤
        locallyClosedCohomologyFiltrationOnExt W J n q from
    le_antisymm (h I J) (h J I)
  intro I J y hy
  have h := H_locallyClosed_map_mem_locallyClosedCohomologyFiltration W (𝟙 F) I J
    (InjectiveResolution.desc (𝟙 F) J I)
    (InjectiveResolution.desc_commutes_zero (𝟙 F) J I) n q hy
  have hi : H_locallyClosed_map W (𝟙 F) n y = y := by
    exact CategoryTheory.Abelian.Ext.comp_mk₀_id y
  rwa [hi] at h

end SGA.SGA2.ExposeI
