/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFiniteCharZero
import SGA.SGA1.ExposeX.TopologicallyFiniteBaseChange
import SGA.SGA1.ExposeIX.Submersive
import SGA.SGA1.ExposeIX.DescentFiniteGeneration
import SGA.Foundations.Limits.SpreadingOutSubfield

/-!
# SGA 1, Exposé X, 2.9 and 2.12 in characteristic `0`

X.2.9 says that the fundamental group of a proper connected scheme over an algebraically closed
field is topologically finitely generated. For fields of characteristic `0` and cardinality
`≤ 𝔠` this is `SGA.SGA1.ExposeX.isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`
(comparison with `X(ℂ)`). Here the cardinality hypothesis is removed: a proper `k`-scheme `X`
(`k` algebraically closed) is `X₀ ⊗_{k₀} k` for a proper scheme `X₀` over a countable
algebraically closed subfield `k₀ ⊆ k` (EGA IV 8.8.2,
`AlgebraicGeometry.Scheme.exists_isPullback_of_isAlgClosed_countable`; properness descends along
the fpqc morphism `Spec k ⟶ Spec k₀`, `SGA.SGA1.ExposeIX.isProper_of_isPullback`), `X₀` is
connected, `π₁(X₀)` is topologically finitely generated because `k₀` embeds into `ℂ`, and
`π₁(X) ≅ π₁(X₀)` (X.1.8, `isTopologicallyFG_etaleFundamentalGroup_pullback_of_isTopologicallyFG`).

* `isTopologicallyFG_etaleFundamentalGroup_of_charZero`: **X.2.9 in characteristic `0`**, every
  algebraically closed `k : Type` of characteristic `0`, every proper connected `X`, every
  geometric point;
* `finite_principalH1_of_charZero`: **X.2.12** (Lang–Serre) in characteristic `0`.

Deviations from SGA: characteristic `0`, and universe `0` (the comparison with `X(ℂ)` is for
`Scheme.{0}`). Characteristic `p` is open (`TopologicallyFiniteStatement`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Cardinal

namespace SGA.SGA1.ExposeX

/-- **X.2.9 in characteristic `0`**: let `k : Type` be an algebraically closed field of
characteristic `0` and `X` a proper connected `k`-scheme. Then `π₁(X, x)` is topologically
finitely generated, at every geometric point `x`. Universe `0`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_charZero (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  obtain ⟨k₀, X₀, q₀, e, hk₀, hc, hq₀, -, -, h⟩ :=
    Scheme.exists_isPullback_of_isAlgClosed_countable k s
  have : IsAlgClosed k₀ := hk₀
  let ρ : Spec (.of k) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have : Flat ρ := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  have : Surjective ρ := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have : ExposeIX.UniversallySubmersive ρ := inferInstance
  have h' : IsPullback e s q₀ ρ := h
  have : IsProper q₀ := ExposeIX.isProper_of_isPullback h'.flip ‹_›
  -- `X₀` is connected
  have he : Surjective e := MorphismProperty.of_isPullback h'.flip ‹Surjective ρ›
  have : ConnectedSpace X₀ := he.surj.connectedSpace e.continuous
  -- `π₁(X₀)`, `k₀` countable
  have hk₀c : #k₀ ≤ 𝔠 :=
    (Cardinal.mk_le_aleph0_iff.mpr hc).trans Cardinal.aleph0_le_continuum
  have h₀ := isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum k₀ hk₀c q₀ Ω (x ≫ e)
  -- `π₁(X₀ ⊗_{k₀} k)`
  have h₁ := isTopologicallyFG_etaleFundamentalGroup_pullback_of_isTopologicallyFG k₀ k q₀
    (x ≫ e) h₀ Ω (x ≫ h'.isoPullback.hom)
  -- `π₁(X)`, along the isomorphism `X₀ ⊗_{k₀} k ≅ X`
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian s,
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace s }
  have : ConnectedSpace ↥(pullback q₀ ρ) :=
    h'.isoPullback.hom.surjective.connectedSpace h'.isoPullback.hom.continuous
  exact ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_family (ι := Unit)
    (fun _ ↦ h'.isoPullback.inv) (fun y ↦ ⟨(), h'.isoPullback.inv.surjective y⟩)
    (fun _ ↦ ⟨Ω, inferInstance, inferInstance, _, h₁⟩) Ω x

/-- **X.2.12 in characteristic `0`** (Lang–Serre): a proper connected scheme over an
algebraically closed field `k : Type` of characteristic `0` has, for every finite group `G`,
only finitely many principal coverings with group `G` up to isomorphism. Universe `0`. -/
theorem finite_principalH1_of_charZero (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X] (Ω : Type)
    [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) (G : Type) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] :
    Finite (ExposeXI.PrincipalH1 (ExposeV.FEt.fiber Ω x) G) :=
  finite_principalH1_of_isTopologicallyFG Ω x
    (isTopologicallyFG_etaleFundamentalGroup_of_charZero k s Ω x) G

end SGA.SGA1.ExposeX
