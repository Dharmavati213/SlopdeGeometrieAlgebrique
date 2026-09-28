/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalConvergence
import SGA.SGA2.ExposeI.LocalToGlobalCoefficientFunctor
import SGA.SGA2.ExposeI.LocalToGlobalTotalNaturality
import SGA.SGA2.ExposeI.SpectralObjectConvergenceNaturality

/-!
# Naturality of closed-support local-to-global convergence

The original spectral-object coefficient morphisms preserve the actual finite
filtration of the total group. Their induced maps on the genuine cokernel
quotients commute with the original stable-page comparisons, while the total
map corresponds to the existing `H_Z_map` under the original abutment equivalence.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

open SpectralObjectConvergence

variable {X : TopCat.{u}} (Z : Closeds X)

attribute [local instance] supportedE2_hasDerivedCategory

/-- The map induced on an actual term of the finite abutment filtration. -/
def supportedCohomologyFiniteFiltrationMap
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    (supportedCohomologyFiniteFiltration Z I n q : AddCommGrpCat.{u + 1}) ⟶
      (supportedCohomologyFiniteFiltration Z J n q : AddCommGrpCat.{u + 1}) :=
  filtrationSubobjectMap (supportedAbelianSpectralObjectMap Z φ) n (q.1 : ℤ)

@[reassoc (attr := simp)]
theorem supportedCohomologyFiniteFiltrationMap_arrow
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    supportedCohomologyFiniteFiltrationMap Z φ n q ≫
        (supportedCohomologyFiniteFiltration Z J n q).arrow =
      (supportedCohomologyFiniteFiltration Z I n q).arrow ≫
        totalMap (supportedAbelianSpectralObjectMap Z φ) n :=
  filtrationSubobjectMap_arrow _ _ _

/-- The actual coefficient map of total cohomology preserves its original
finite convergence filtration. -/
theorem supportedTotalMap_preserves_finiteFiltration
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 2)) :
    imageSubobject ((supportedCohomologyFiniteFiltration Z I n q).arrow ≫
      totalMap (supportedAbelianSpectralObjectMap Z φ) n) ≤
        supportedCohomologyFiniteFiltration Z J n q :=
  totalMap_preserves_filtration _ _ _

/-- The actual cokernel map on consecutive terms of the finite filtration. -/
def supportedCohomologyGradedPieceMap
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1)) :
    supportedCohomologyGradedPiece Z I n q ⟶ supportedCohomologyGradedPiece Z J n q :=
  filtrationQuotientMap (supportedAbelianSpectralObjectMap Z φ) n
    (q.castSucc.val : ℤ) (q.succ.val : ℤ) (by simp)

/-- The quotient-index transport already present in the original stable-page
comparison, exposed separately to prove its naturality. -/
def supportedCohomologyGradedPieceIso
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 1)) :
    gradedPiece (supportedLocalToGlobalAbelianSpectralObject Z I) n q ≅
      supportedCohomologyGradedPiece Z I n q :=
  filtrationQuotientIsoOfEq (supportedLocalToGlobalAbelianSpectralObject Z I) n
    (q.val : ℤ) ((q.val : ℤ) + 1 : ℤ) (q.castSucc.val : ℤ) (q.succ.val : ℤ)
    (by simp) (by simp) rfl (by simp)

@[reassoc]
theorem supportedCohomologyGradedPieceIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1)) :
    gradedPieceMap (supportedAbelianSpectralObjectMap Z φ) n q ≫
        (supportedCohomologyGradedPieceIso Z J n q).hom =
      (supportedCohomologyGradedPieceIso Z I n q).hom ≫
        supportedCohomologyGradedPieceMap Z φ n q :=
  filtrationQuotientIsoOfEq_naturality _ _ _ _ _ _ _ _ _ _

lemma supportedLocalToGlobalStablePageIsoGraded_eq
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    supportedLocalToGlobalStablePageIsoGraded Z I n q r hr =
      stablePageIsoGradedTotal (supportedLocalToGlobalAbelianSpectralObject Z I) n q r hr ≪≫
        supportedCohomologyGradedPieceIso Z I n q := rfl

/-- The actual coefficient maps commute with the original stable-page to
associated-graded isomorphism of the finite supported-cohomology filtration. -/
@[reassoc]
theorem supportedLocalToGlobalStablePageIsoGraded_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (q : Fin (n + 1))
    (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((supportedTruncationSpectralSequenceMap Z φ).hom r (by lia)).f ((n : ℤ) - q, q) ≫
        (supportedLocalToGlobalStablePageIsoGraded Z J n q r hr).hom =
      (supportedLocalToGlobalStablePageIsoGraded Z I n q r hr).hom ≫
        supportedCohomologyGradedPieceMap Z φ n q := by
  rw [supportedLocalToGlobalStablePageIsoGraded_eq,
    supportedLocalToGlobalStablePageIsoGraded_eq]
  dsimp only [Iso.trans_hom]
  erw [stablePageIsoGradedTotal_naturality_assoc,
    supportedCohomologyGradedPieceIso_naturality]
  simp only [Category.assoc]

/-- The same original stable comparison is natural for the already
constructed coefficient functor, without a supplied resolution lift. -/
@[reassoc]
theorem supportedLocalToGlobalStablePageIsoGraded_coefficient_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((supportedTruncationSpectralSequenceCoefficientMap Z f I J).hom r (by lia)).f
        ((n : ℤ) - q, q) ≫ (supportedLocalToGlobalStablePageIsoGraded Z J n q r hr).hom =
      (supportedLocalToGlobalStablePageIsoGraded Z I n q r hr).hom ≫
        supportedCohomologyGradedPieceMap Z (InjectiveResolution.desc f J I) n q := by
  rw [supportedTruncationSpectralSequenceCoefficientMap_eq]
  exact supportedLocalToGlobalStablePageIsoGraded_naturality Z _ n q r hr

/-- The filtration-preserving total morphism is the original supported
cohomology coefficient map under the original abutment equivalence. -/
theorem supportedCohomologyAbutmentEquiv_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : ↥(total (C := AddCommGrpCat.{u + 1})
      (supportedLocalToGlobalAbelianSpectralObject Z I) n)) :
    supportedCohomologyAbutmentEquiv Z J n
        (totalMap (supportedAbelianSpectralObjectMap Z φ) n x) =
      H_Z_map Z f n (supportedCohomologyAbutmentEquiv Z I n x) :=
  supportedSpectralObjectTotalEquivH_Z_naturality Z f I J φ hφ n x

/-- Compatible resolution lifts give identical actual total maps. -/
theorem supportedTotalMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    totalMap (supportedAbelianSpectralObjectMap Z φ) n =
      totalMap (supportedAbelianSpectralObjectMap Z ψ) n := by
  ext x
  apply (supportedCohomologyAbutmentEquiv Z J n).injective
  rw [supportedCohomologyAbutmentEquiv_naturality Z f I J φ hφ,
    supportedCohomologyAbutmentEquiv_naturality Z f I J ψ hψ]

/-- The actual finite-filtration maps are independent of the resolution lift. -/
theorem supportedCohomologyFiniteFiltrationMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) (q : Fin (n + 2)) :
    supportedCohomologyFiniteFiltrationMap Z φ n q =
      supportedCohomologyFiniteFiltrationMap Z ψ n q :=
  filtrationSubobjectMap_eq_of_totalMap_eq _ _ _
    (supportedTotalMap_eq_of_lifts Z f I J φ ψ hφ hψ n)

/-- The genuine associated-graded coefficient maps also do not depend on
the lift of the coefficient morphism to resolutions. -/
theorem supportedCohomologyGradedPieceMap_eq_of_lifts
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℕ) (q : Fin (n + 1)) :
    supportedCohomologyGradedPieceMap Z φ n q =
      supportedCohomologyGradedPieceMap Z ψ n q := by
  rw [← cancel_epi (supportedLocalToGlobalStablePageIsoGraded Z I n q
    ((n : ℤ) + 2) le_rfl).hom]
  rw [← supportedLocalToGlobalStablePageIsoGraded_naturality,
    ← supportedLocalToGlobalStablePageIsoGraded_naturality,
    supportedTruncationSpectralSequenceMap_eq_of_lifts Z f I J φ ψ hφ hψ]

/-- The original convergence filtration transported along its already
proved abutment equivalence to the original, small-universe `H_Z`. -/
def supportedCohomologyFiltrationOnH_Z
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 2)) : AddSubgroup (H_Z Z F n) :=
  ((supportedCohomologyAbutmentEquiv Z I n).toAddMonoidHom.comp
    (supportedCohomologyFiniteFiltration Z I n q).arrow.hom).range

private lemma addCommGrp_comm_apply {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (i : A ⟶ C) (j : B ⟶ D)
    (h : f ≫ j = i ≫ g) (x : A) : j (f x) = g (i x) :=
  ConcreteCategory.congr_hom h x

/-- Original `H_Z_map` preserves the original convergence filtration,
transported by its actual abutment equivalence. -/
theorem H_Z_map_mem_supportedCohomologyFiltration
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (n : ℕ) (q : Fin (n + 2)) {y : H_Z Z F n}
    (hy : y ∈ supportedCohomologyFiltrationOnH_Z Z I n q) :
    H_Z_map Z f n y ∈ supportedCohomologyFiltrationOnH_Z Z J n q := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨supportedCohomologyFiniteFiltrationMap Z φ n q x, ?_⟩
  change supportedCohomologyAbutmentEquiv Z J n
      ((supportedCohomologyFiniteFiltration Z J n q).arrow
        (supportedCohomologyFiniteFiltrationMap Z φ n q x)) =
    H_Z_map Z f n (supportedCohomologyAbutmentEquiv Z I n
      ((supportedCohomologyFiniteFiltration Z I n q).arrow x))
  calc
    _ = supportedCohomologyAbutmentEquiv Z J n
        (totalMap (supportedAbelianSpectralObjectMap Z φ) n
          ((supportedCohomologyFiniteFiltration Z I n q).arrow x)) :=
      congrArg (supportedCohomologyAbutmentEquiv Z J n)
        (addCommGrp_comm_apply _ _ _ _ (supportedCohomologyFiniteFiltrationMap_arrow Z φ n q) x)
    _ = _ := supportedCohomologyAbutmentEquiv_naturality Z f I J φ hφ n _

/-- Filtration preservation for every actual sheaf morphism, with the
resolution comparison constructed rather than assumed. -/
theorem H_Z_map_mem_supportedCohomologyFiltration_of_mem
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (n : ℕ) (q : Fin (n + 2)) {y : H_Z Z F n}
    (hy : y ∈ supportedCohomologyFiltrationOnH_Z Z I n q) :
    H_Z_map Z f n y ∈ supportedCohomologyFiltrationOnH_Z Z J n q :=
  H_Z_map_mem_supportedCohomologyFiltration Z f I J
    (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) n q hy

/-- The actual filtration on original `H_Z` is independent of the chosen
injective resolution, as equality of additive subgroups. -/
theorem supportedCohomologyFiltrationOnH_Z_independent
    {F : Sheaf AddCommGrpCat.{u} X} (I J : InjectiveResolution F)
    (n : ℕ) (q : Fin (n + 2)) :
    supportedCohomologyFiltrationOnH_Z Z I n q =
      supportedCohomologyFiltrationOnH_Z Z J n q := by
  suffices h : ∀ I J : InjectiveResolution F,
      supportedCohomologyFiltrationOnH_Z Z I n q ≤
        supportedCohomologyFiltrationOnH_Z Z J n q from
    le_antisymm (h I J) (h J I)
  intro I J y hy
  have h := H_Z_map_mem_supportedCohomologyFiltration Z (𝟙 F) I J
    (InjectiveResolution.desc (𝟙 F) J I)
    (InjectiveResolution.desc_commutes_zero (𝟙 F) J I) n q hy
  have hi : H_Z_map Z (𝟙 F) n y = y := by
    exact CategoryTheory.Abelian.Ext.comp_mk₀_id y
  rwa [hi] at h

end SGA.SGA2.ExposeI
