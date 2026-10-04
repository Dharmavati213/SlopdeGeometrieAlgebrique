/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeX.EtaleCoverings

/-!
# SGA 1, Exposé X, 1.7–1.8: proper schemes over an algebraically closed field

Let `X` be proper and connected over an algebraically closed field `k`. Then:

* `Γ(X, 𝒪_X)` is a finite `k`-algebra (`finite_specStructureRingHom`), equal to `k` when `X` is
  reduced (`isIso_app_of_isProper`, used in X.1.7);
* `X ⊗ₖ K` is connected for every field `K ⊇ k` (`connectedSpace_pullback_of_isAlgClosed`);
* the surjectivity half of X.1.8, which SGA calls immediate: `π₁(X ⊗ₖ K) → π₁(X)` is surjective
  (`surjective_map_pullback_of_isAlgClosed`), since connected étale coverings of `X` stay
  connected over `K` (V.6.9).

The last two hold without properness, for every connected `X`
(`surjective_map_pullback_fst_of_isAlgClosed`): they are cases of the geometric connectedness of
connected schemes over `k` (`AlgebraicGeometry.geometricallyConnected_of_isAlgClosed`,
`AlgebraicGeometry.connectedSpace_pullback_of_isAlgClosed_of_connectedSpace` and, for algebras,
`AlgebraicGeometry.CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`, in
`SGA.Foundations.Fields.GeometricallyConnected`), from which they are derived here.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped TensorProduct

namespace SGA.SGA1.ExposeX

variable {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))

/-- For `X` proper over a field `k`, `Γ(X, 𝒪_X)` is a finite `k`-algebra (EGA III 3.2.1). -/
theorem finite_specStructureRingHom [IsProper s] : s.specStructureRingHom.Finite :=
  (CohomologyAux.finite_app_of_isProper s (isAffineOpen_top (Spec (.of k)))).comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

variable [IsAlgClosed k]

/-- A finite reduced algebra over an algebraically closed field `k` without non-trivial
idempotents is `k`. -/
theorem bijective_algebraMap_of_trivialIdempotents (R : Type*) [CommRing R] [Algebra k R]
    [Module.Finite k R] [IsReduced R] [Nontrivial R] (h : CohomologyAux.TrivialIdempotents R) :
    Function.Bijective (algebraMap k R) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  have : IsLocalRing R := CohomologyAux.isLocalRing_of_trivialIdempotents h
  have : IsDomain R := (IsArtinianRing.isField_of_isReduced_of_isLocalRing R).isDomain
  exact IsAlgClosed.ringHom_bijective_of_isIntegral _ fun x ↦ Algebra.IsIntegral.isIntegral x

/-- A finite algebra `B` over an algebraically closed field `k` without non-trivial idempotents
keeps this property after any field extension `K ⊇ k`. (A case of
`CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`, which needs no finiteness.) -/
theorem trivialIdempotents_tensor_of_isAlgClosed (B : Type*) [CommRing B] [Algebra k B]
    [Module.Finite k B] [Nontrivial B] (h : CohomologyAux.TrivialIdempotents B) (K : Type*)
    [Field K] [Algebra k K] : CohomologyAux.TrivialIdempotents (B ⊗[k] K) :=
  CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed h fun _ he ↦
    IsIdempotentElem.iff_eq_zero_or_one.mp he

/-- A proper, connected and reduced scheme `X` over an algebraically closed field `k` has
`Γ(X, 𝒪_X) = k` (used in X.1.7): `k → Γ(X, 𝒪_X)` is bijective, since `Γ(X, 𝒪_X)` is finite
(EGA III 3.2.1), reduced and without non-trivial idempotents. -/
theorem isIso_app_of_isProper [IsProper s] [IsReduced X] [ConnectedSpace X]
    (U : (Spec (.of k)).Opens) : IsIso (s.app U) := by
  refine CohomologyAux.isIso_app_of_basis s (fun V y hy ↦ ⟨⊤, trivial, fun z _ ↦ ?_, ?_⟩) U
  · rwa [Subsingleton.elim z y]
  let _ := s.specStructureRingHom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) := finite_specStructureRingHom s
  have : Nonempty ↥(⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have hbij := bijective_algebraMap_of_trivialIdempotents (k := k) Γ(X, ⊤)
    (CohomologyAux.trivialIdempotents_of_connectedSpace X)
  have hs : Function.Bijective (s.app ⊤) := by
    have h' : s.app ⊤ = (Scheme.ΓSpecIso (.of k)).hom ≫
        CommRingCat.ofHom s.specStructureRingHom :=
      (Iso.hom_inv_id_assoc _ _).symm
    have := hbij.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom)
    rw [h']
    exact this
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hs

/-- A proper connected scheme `X` over an algebraically closed field `k` stays connected after any
extension `K` of `k` (a case of EGA IV 4.5.1). Properness is not needed: this is a case of
`connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`. -/
theorem connectedSpace_pullback_of_isAlgClosed [IsProper s] [ConnectedSpace X] (K : Type u)
    [Field K] [Algebra k K] :
    ConnectedSpace ↥(pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  (geometricallyConnected_of_isAlgClosed s).geometrically_connectedSpace _ _ _
    (IsPullback.of_hasPullback s (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- **X.1.8, surjectivity**, without properness (for any field `K ⊇ k`): let `X` be connected over
an algebraically closed field `k`. Then `π₁(X ⊗ₖ K, t) → π₁(X, t)` is surjective for every
geometric point `t` of `X ⊗ₖ K`, since a connected étale covering of `X` is geometrically connected
over `k` (`geometricallyConnected_of_isAlgClosed`), so stays connected over `K` (V.6.9). -/
theorem surjective_map_pullback_fst_of_isAlgClosed [ConnectedSpace X] (K : Type u) [Field K]
    [Algebra k K] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) t) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : ConnectedSpace ↥(pullback s ρ) :=
    (geometricallyConnected_of_isAlgClosed s).geometrically_connectedSpace ρ _ _
      (IsPullback.of_hasPullback s ρ)
  refine ExposeV.autMap_surjective _ _ fun E hE ↦ ?_
  have : ConnectedSpace ↥((𝟭 Scheme).obj E.left) := ExposeV.FEt.connectedSpace_of_isConnected E
  rw [ExposeV.FEt.isConnected_iff_connectedSpace]
  have hsq := (IsPullback.of_hasPullback E.hom (pullback.fst s ρ)).paste_vert
    (IsPullback.of_hasPullback s ρ)
  exact (geometricallyConnected_of_isAlgClosed (E.hom ≫ s)).geometrically_connectedSpace
    ρ _ _ hsq

/-- **X.1.8, surjectivity** (for any extension `K` of `k`). Let `X` be proper and connected over
an algebraically closed field `k` and `K ⊇ k` a field. Then `π₁(X ⊗ₖ K, t̄) → π₁(X, t̄)` is
surjective for every geometric point `t̄` of `X ⊗ₖ K`: a connected étale covering `X'` of `X`
stays connected over `K` (V.6.9). Properness is not needed
(`surjective_map_pullback_fst_of_isAlgClosed`). -/
theorem surjective_map_pullback_of_isAlgClosed [IsProper s] [ConnectedSpace X] (K : Type u)
    [Field K] [Algebra k K] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) t) :=
  surjective_map_pullback_fst_of_isAlgClosed s K Ω t

end SGA.SGA1.ExposeX
