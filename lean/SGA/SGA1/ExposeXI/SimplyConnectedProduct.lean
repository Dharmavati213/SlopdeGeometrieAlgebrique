/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeXI.Geometry

/-!
# Products of simply connected schemes (XI.1)

By the Künneth formula X.1.7 (`ExposeX.bijective_map_prod`), the product over an algebraically
closed field `k` of a proper, connected and reduced `k`-scheme `X` with a connected `k`-scheme `T`
of finite type has fundamental group `π₁(X) × π₁(T)`. In particular a product of simply
connected schemes is simply connected (`isSimplyConnected_pullback`), which gives
`π₁((ℙ¹)ʳ) = 1` from `π₁(ℙ¹) = 1` (used in SGA's second proof of XI.1.1, via X.3.4).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] [IsAlgClosed k] {X T : Scheme.{u}} (s : X ⟶ Spec (.of k))
  (sT : T ⟶ Spec (.of k))

/-- The product over an algebraically closed field of a proper, connected and reduced scheme with
a connected locally noetherian scheme is connected. -/
theorem connectedSpace_pullback [IsProper s] [IsReduced X] [ConnectedSpace X] [ConnectedSpace T]
    [IsLocallyNoetherian T] :
    ConnectedSpace ↥(pullback s sT) := by
  have : GeometricallyConnected (pullback.snd s sT) :=
    CohomologyAux.geometricallyConnected_of_isIso_app _ (ExposeX.isIso_app_snd s sT)
  exact ExposeIX.connectedSpace_of_universally_isQuotientMap (pullback.snd s sT)
    (ExposeIX.universally_isQuotientMap_of_universallyClosed _)

/-- XI.1 (with X.1.7): over an algebraically closed field `k`, the product of a proper, reduced,
simply connected `k`-scheme `X` with a simply connected quasi-compact `k`-scheme `T` of finite
type is simply connected. -/
theorem isSimplyConnected_pullback [IsProper s] [IsReduced X] [IsLocallyNoetherian T]
    [CompactSpace T] [LocallyOfFiniteType sT] (hX : IsSimplyConnected X)
    (hT : IsSimplyConnected T) : IsSimplyConnected (pullback s sT) := by
  have := hX.1
  have := hT.1
  have := connectedSpace_pullback s sT
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨x₀, hx₀⟩ := ExposeX.exists_comp_eq_id s
  obtain ⟨t₀, ht₀⟩ := ExposeX.exists_comp_eq_id sT
  let z : Spec (.of k) ⟶ pullback s sT := pullback.lift x₀ t₀ (by rw [hx₀, ht₀])
  have hX' := (isSimplyConnected_iff_subsingleton k (z ≫ pullback.fst s sT)).1 hX
  have hT' := (isSimplyConnected_iff_subsingleton k (z ≫ pullback.snd s sT)).1 hT
  have key : ∀ τ : ExposeV.etaleFundamentalGroup k z, τ = 1 := fun τ ↦
    ExposeX.eq_one_of_hom_app_pullback_eq_id s sT k z τ
      (fun E ↦ ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id k _ z τ
        (Subsingleton.elim _ _) E)
      (fun W ↦ ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id k _ z τ
        (Subsingleton.elim _ _) W)
  exact (isSimplyConnected_iff_subsingleton k z).2 ⟨fun a b ↦ by rw [key a, key b]⟩

end SGA.SGA1.ExposeXI
