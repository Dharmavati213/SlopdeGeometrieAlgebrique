/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.FundamentalGroupFG
import SGA.SGA1.ExposeX.TopologicallyFinite
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeXII.LocalTopology
import SGA.SGA1.ExposeXII.LocalTopologyLPC
import SGA.SGA1.ExposeXII.LocalTopologyCurves
import SGA.SGA1.ExposeXII.Proper
import SGA.SGA1.ExposeXII.Smooth
import SGA.SGA1.ExposeXII.Separated
import SGA.Foundations.Fields.ComplexEmbedding
import SGA.Foundations.Fields.GeometricallyConnected

/-!
# SGA 1, Exposé X, 2.9 and 2.12 over `ℂ`

X.2.9 says that the fundamental group of a proper connected scheme over an algebraically closed
field is topologically finitely generated. SGA deduces it from X.2.6, whose proof for curves
uses Riemann's existence theorem. Over `ℂ` only the easy half of XII.5.2 is needed: `π₁(X, x)` is
a continuous quotient of the profinite completion of `π₁(X(ℂ), x)`
(`ExposeXII.surjective_autWhiskerLeft_schemePointsFunctor`, from XII.2.4 and V.6.9), and
`π₁(X(ℂ), x)` is finitely generated because `X(ℂ)` is compact, Hausdorff, locally path-connected
and semilocally simply connected (`FundamentalGroup.fg_of_compactSpace`). `X(ℂ)` is always locally
path-connected (`ExposeXII.SchemePoints.locallyPathConnectedSpace`); it is semilocally simply
connected for every `X` locally of finite type over `ℂ`
(`ExposeXII.semilocallySimplyConnectedStatement`); for `X` smooth and for `dim X ≤ 1` it also
follows from strong local contractibility, which is what the first two theorems below use.

* `isTopologicallyFG_etaleFundamentalGroup_of_smooth`: X.2.9 for `X` smooth, proper and connected
  over `ℂ`, at every geometric point; unconditional.
* `isTopologicallyFG_etaleFundamentalGroup_of_topologicalKrullDim_le_one`: X.2.9 for every proper
  connected curve over `ℂ` (any singularities); unconditional.
* `isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected`: X.2.9 for every proper
  connected `X` over `ℂ`, assuming `ExposeXII.SemilocallySimplyConnectedStatement`; with
  `ExposeXII.semilocallySimplyConnectedStatement` this gives the unconditional
  `isTopologicallyFG_etaleFundamentalGroup_complex` (in
  `SGA.SGA1.ExposeX.TopologicallyFiniteCharZero`).

X.2.12 (Lang–Serre) follows in each case from `finite_principalH1_of_isTopologicallyFG`
(finitely many principal coverings with a given finite group).

Since `π₁(X)` depends only on the scheme `X`, the curve case holds over every algebraically closed
field `k : Type` of characteristic `0` and cardinality `𝔠` (such a field is isomorphic to `ℂ`,
`Complex.nonempty_ringEquiv_of_mk_eq_continuum`):
`isTopologicallyFG_etaleFundamentalGroup_of_topologicalKrullDim_le_one_of_mk_eq_continuum`.

For an algebraically closed field `k` of characteristic `0` and cardinality `≤ 𝔠`, which embeds
into `ℂ` (`Complex.nonempty_ringHom_of_mk_le_continuum`), X.1.8 (`π₁(X ⊗ₖ ℂ) ≅ π₁(X)`,
`isTopologicallyFG_etaleFundamentalGroup_of_pullback`) gives the smooth case and the conditional
general case:
`isTopologicallyFG_etaleFundamentalGroup_of_smooth_of_mk_le_continuum`,
`isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected_of_mk_le_continuum`.

All of this is in universe `0`. The smooth and curve cases above are special cases of the
theorems of `SGA.SGA1.ExposeX.TopologicallyFiniteCharZero`. In characteristic `p`, for
`#k > 𝔠` and in other universes, X.2.9 is open (`TopologicallyFiniteStatement`).
-/

open CategoryTheory AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeX

open ExposeXII

section Complex

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))] [ConnectedSpace X]

/-- The profinite completion of `π₁(X(ℂ), x)`, i.e. the automorphism group of the fibre functor
of finite coverings of `X(ℂ)` at `x`, is topologically finitely generated when `X(ℂ)` is
semilocally simply connected and `X` is proper over `ℂ`. -/
private lemma isTopologicallyFG_autFiber [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]
    (x : SchemePoints ℂ X) :
    haveI : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
    ExposeXIII.IsTopologicallyFG
      (Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (SchemePoints ℂ X)) x)) := by
  have : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
  have := SchemePoints.locallyPathConnectedSpace X
  have : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
  have : CompactSpace (SchemePoints ℂ X) := SchemePoints.compactSpace_of_isProper
  have : T2Space (SchemePoints ℂ X) := SchemePoints.t2Space ℂ X
  have : Group.FG (FundamentalGroup (SchemePoints ℂ X) x) := FundamentalGroup.fg_of_compactSpace x
  obtain ⟨t, ht⟩ := ProfiniteGrp.ProfiniteCompletion.exists_finset_dense_closure
    (G := GrpCat.of (FundamentalGroup (TopCat.of (SchemePoints ℂ X)) x))
  exact (isTopologicallyFG_congr (TopCat.FiniteCovering.autFiberEquiv
    (X := TopCat.of (SchemePoints ℂ X)) x)).mpr ⟨t, ht⟩

/-- X.2.9 over `ℂ` when `X(ℂ)` is semilocally simply connected. -/
private lemma isTopologicallyFG_of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  have : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
  have := SchemePoints.locallyPathConnectedSpace X
  let p : SchemePoints ℂ X := Classical.arbitrary _
  refine (isTopologicallyFG_etaleFundamentalGroup_iff ℂ Ω p.1 x).mp ?_
  exact (isTopologicallyFG_autFiber X p).of_surjective _ (continuous_autWhiskerLeft _ _)
    (surjective_autWhiskerLeft_schemePointsFunctor X p)

/-- X.2.9 over `ℂ`, smooth case: for `X` smooth, proper and connected over `ℂ`, the fundamental
group `π₁(X, x)` is topologically finitely generated, at every geometric point `x`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_smooth [Smooth (X ↘ Spec (.of ℂ))]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  have := SchemePoints.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) X
  isTopologicallyFG_of_semilocallySimplyConnectedSpace X Ω x

/-- X.2.9 over `ℂ` for curves: for `X` proper and connected over `ℂ` of dimension `≤ 1` (with
arbitrary singularities), the fundamental group `π₁(X, x)` is topologically finitely generated,
at every geometric point `x`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_topologicalKrullDim_le_one
    (hX : topologicalKrullDim X ≤ 1) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  have := SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one X hX
  isTopologicallyFG_of_semilocallySimplyConnectedSpace X Ω x

/-- X.2.9 over `ℂ`, for every proper connected `X`, from the semilocal simple connectedness of
`Y(ℂ)` for `Y` locally of finite type over `ℂ` (`SemilocallySimplyConnectedStatement`, part of
the topological input of XII.5.2, proved as `ExposeXII.semilocallySimplyConnectedStatement`): the
fundamental group `π₁(X, x)` of a proper connected `ℂ`-scheme `X` is topologically finitely
generated, at every geometric point `x`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected
    (hS : SemilocallySimplyConnectedStatement) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  have := hS X
  isTopologicallyFG_of_semilocallySimplyConnectedSpace X Ω x

end Complex

section Continuum

open Cardinal

variable {X : Scheme.{0}} [ConnectedSpace X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
  (hk : #k = 𝔠) (s : X ⟶ Spec (.of k)) [IsProper s]

include hk s in
/-- X.2.9 for proper connected curves (dimension `≤ 1`, arbitrary singularities) over an
algebraically closed field `k : Type` of characteristic `0` and cardinality `𝔠`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_topologicalKrullDim_le_one_of_mk_eq_continuum
    (hX : topologicalKrullDim X ≤ 1) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  obtain ⟨e⟩ := Complex.nonempty_ringEquiv_of_mk_eq_continuum k hk
  let _ : X.Over (Spec (.of ℂ)) := ⟨s ≫ Spec.map e.symm.toCommRingCatIso.hom⟩
  have : IsProper (X ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (s ≫ Spec.map e.symm.toCommRingCatIso.hom))
  exact isTopologicallyFG_etaleFundamentalGroup_of_topologicalKrullDim_le_one X hX Ω x

end Continuum

section SmallFields

open Cardinal CategoryTheory.Limits

variable {X : Scheme.{0}} [ConnectedSpace X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
  (hk : #k ≤ 𝔠) (s : X ⟶ Spec (.of k)) [IsProper s]

include hk in
/-- Transport of X.2.9 from `X ⊗ₖ ℂ` to `X` along an embedding `k ↪ ℂ` (X.1.8): if `π₁(X ⊗ₖ ℂ)`
is topologically finitely generated whenever `X ⊗ₖ ℂ` is proper over `ℂ` and connected and
satisfies `P` (a property of the structure morphism), so is `π₁(X)`. -/
private lemma isTopologicallyFG_of_baseChange_complex
    (P : ∀ {Y : Scheme.{0}}, (Y ⟶ Spec (.of ℂ)) → Prop)
    (hP : ∀ (Y : Scheme.{0}) [Y.Over (Spec (.of ℂ))] [IsProper (Y ↘ Spec (.of ℂ))]
      [ConnectedSpace Y], P (Y ↘ Spec (.of ℂ)) → ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (y : Spec (.of Ω) ⟶ Y), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω y))
    (hs : ∀ (_ : Algebra k ℂ), P (pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap k ℂ)))))
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  obtain ⟨φ⟩ := Complex.nonempty_ringHom_of_mk_le_continuum k hk
  let _ : Algebra k ℂ := φ.toAlgebra
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k ℂ))
  have : GeometricallyConnected s := geometricallyConnected_of_isAlgClosed s
  have : ConnectedSpace ↥(pullback s ρ) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd s ρ)
  let _ : (pullback s ρ).Over (Spec (.of ℂ)) := ⟨pullback.snd s ρ⟩
  have : IsProper (pullback s ρ ↘ Spec (.of ℂ)) := inferInstanceAs (IsProper (pullback.snd s ρ))
  obtain ⟨y⟩ : Nonempty ↥(pullback s ρ) := inferInstance
  let t := ExposeV.geometricPointAt _ y
  exact isTopologicallyFG_etaleFundamentalGroup_of_pullback k ℂ s t
    (hP (pullback s ρ) (hs _) _ t) Ω x

include hk in
/-- X.2.9 for `X` smooth, proper and connected over an algebraically closed field `k : Type` of
characteristic `0` and cardinality `≤ 𝔠` (for instance `k = ℚ̄`): `k` embeds into `ℂ`,
`X ⊗ₖ ℂ` is smooth, proper and connected, and `π₁(X ⊗ₖ ℂ) ≅ π₁(X)` (X.1.8). -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_smooth_of_mk_le_continuum [Smooth s]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  isTopologicallyFG_of_baseChange_complex k hk s (fun f ↦ Smooth f)
    (fun Y _ _ _ h ↦ have : Smooth (Y ↘ Spec (.of ℂ)) := h
      isTopologicallyFG_etaleFundamentalGroup_of_smooth Y)
    (fun _ ↦ inferInstance) Ω x

include hk s in
/-- X.2.9 for every proper connected `X` over an algebraically closed field `k : Type` of
characteristic `0` and cardinality `≤ 𝔠`, from `SemilocallySimplyConnectedStatement`. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected_of_mk_le_continuum
    (hS : SemilocallySimplyConnectedStatement) (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  isTopologicallyFG_of_baseChange_complex k hk s (fun _ ↦ True)
    (fun Y _ _ _ _ ↦ isTopologicallyFG_etaleFundamentalGroup_of_semilocallySimplyConnected Y hS)
    (fun _ ↦ trivial) Ω x

end SmallFields

end SGA.SGA1.ExposeX
