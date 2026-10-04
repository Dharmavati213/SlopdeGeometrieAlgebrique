/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFiniteComplex
import SGA.SGA1.ExposeXII.LocalTopologySLSC

/-!
# SGA 1, Exposé X, 2.9 and 2.12 in characteristic `0`, for fields of cardinality `≤ 𝔠`

X.2.9 says that the fundamental group of a proper connected scheme over an algebraically closed
field is topologically finitely generated. Over `ℂ`, `π₁(X)` is a continuous quotient of the
profinite completion of `π₁(X(ℂ))` (the easy half of XII.5.2), which is finitely generated as soon
as `X(ℂ)` is semilocally simply connected
(`isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected`). That `X(ℂ)` is
semilocally simply connected for every `X` locally of finite type over `ℂ` is
`ExposeXII.semilocallySimplyConnectedStatement`. Together:

* `isTopologicallyFG_etaleFundamentalGroup_complex`: **X.2.9 over `ℂ`**, for every proper
  connected `X` (no smoothness or dimension hypothesis), at every geometric point;
* `isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`: **X.2.9 over every algebraically
  closed field `k : Type` of characteristic `0` and cardinality `≤ 𝔠`** (e.g. `k = ℚ̄`), through an
  embedding `k ↪ ℂ` and X.1.8;
* `finite_principalH1_complex`, `finite_principalH1_of_mk_le_continuum`: **X.2.12** (Lang–Serre) in
  the same two cases: finitely many principal coverings with a given finite group.

Neither SGA's reduction to curves (Chow, normalization, Bertini) nor the Riemann existence theorem
is used. Deviations from SGA's X.2.9: characteristic `0`, `#k ≤ 𝔠`, and universe `0` (the
comparison with `X(ℂ)` is for `Scheme.{0}`). Fields of characteristic `0` of larger cardinality
need the descent of `X` to a countable subfield (EGA IV 8, not formalized); characteristic `p` is
open (`TopologicallyFiniteStatement`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Cardinal

namespace SGA.SGA1.ExposeX

/-- **X.2.9 over `ℂ`**: for `X` proper and connected over `ℂ` (with arbitrary singularities), the
fundamental group `π₁(X, x)` is topologically finitely generated, at every geometric point `x`.
Universe `0`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_complex (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))] [ConnectedSpace X] (Ω : Type) [Field Ω]
    [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected X
    ExposeXII.semilocallySimplyConnectedStatement Ω x

/-- **X.2.9 in characteristic `0`, for fields of cardinality `≤ 𝔠`**: let `k : Type` be an
algebraically closed field of characteristic `0` with `#k ≤ 𝔠` (e.g. `ℚ̄` or `ℂ`), and `X` a
proper connected `k`-scheme. Then `π₁(X, x)` is topologically finitely generated, at every
geometric point `x`. Universe `0`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] (hk : #k ≤ 𝔠) {X : Scheme.{0}} (s : X ⟶ Spec (.of k))
    [IsProper s] [ConnectedSpace X] (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected_of_mk_le_continuum k hk s
    ExposeXII.semilocallySimplyConnectedStatement Ω x

/-- **X.2.12 over `ℂ`** (Lang–Serre): a proper connected scheme `X` over `ℂ` has, for every finite
group `G`, only finitely many principal coverings with group `G` up to isomorphism. Universe
`0`. -/
theorem finite_principalH1_complex (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] [ConnectedSpace X] (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : Type) [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] :
    Finite (ExposeXI.PrincipalH1 (ExposeV.FEt.fiber Ω x) G) :=
  finite_principalH1_of_isTopologicallyFG Ω x
    (isTopologicallyFG_etaleFundamentalGroup_complex X Ω x) G

/-- **X.2.12 in characteristic `0`, for fields of cardinality `≤ 𝔠`** (Lang–Serre): a proper
connected scheme over an algebraically closed field `k : Type` of characteristic `0` with
`#k ≤ 𝔠` has, for every finite group `G`, only finitely many principal coverings with group `G`
up to isomorphism. Universe `0`. -/
theorem finite_principalH1_of_mk_le_continuum (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (hk : #k ≤ 𝔠) {X : Scheme.{0}} (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) (G : Type) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] :
    Finite (ExposeXI.PrincipalH1 (ExposeV.FEt.fiber Ω x) G) :=
  finite_principalH1_of_isTopologicallyFG Ω x
    (isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum k hk s Ω x) G

end SGA.SGA1.ExposeX
