/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFinite
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeIX.DescentFiniteGeneration
import SGA.Foundations.Projective.Chow
import SGA.SGA1.ExposeI.Permanence
import SGA.Foundations.NormalizationFinite

/-!
# SGA 1, Exposé X, 2.9: the reduction to curves

The first step of SGA's proof of X.2.9: by Chow's lemma, passage to the reduced irreducible
components and descent (IX.5.2), it suffices to prove that `π₁` is topologically finitely
generated for integral schemes projective over an algebraically closed field.

* `isTopologicallyFG_of_isClosedImmersion_of_surjective`: `π₁` is invariant under surjective
  closed immersions, e.g. `X_red ⟶ X` (from IX.1.7,
  `ExposeIX.bijective_etaleFundamentalGroup_map_of_isClosedImmersion`), in the form used here;
* `topologicallyFiniteStatement_of_isIntegral`: X.2.9 from the integral case (irreducible
  components with their reduced structure, IX.5.2 for the finite family of components);
* `topologicallyFiniteStatement_of_isHProjective`: X.2.9 from the integral, H-projective case
  (Chow's lemma `AlgebraicGeometry.exists_isHProjective_of_isProper` and IX.5.2);
* `isTopologicallyFG_of_curve_of_hyperplane_of_model`: SGA's argument (induction on the
  dimension, X.1.8 for the change of algebraically closed field), run inside a class of
  algebraically closed fields (e.g. those of characteristic `0` and cardinality `≤ 𝔠`) which the
  hyperplane step does not leave, from three inputs: the curve case for normal integral curves
  (X.2.6, weak form: such a curve is smooth), Chow's lemma with normalization, and the hyperplane
  step X.2.10 in an existence form that both SGA's special hyperplane and the generic hyperplane
  provide;
* `isTopologicallyFG_of_curve_of_hyperplane`, `topologicallyFiniteStatement_of_curve_of_hyperplane`:
  the same with H-projective models (Chow's lemma with normalization as a hypothesis);
* `exists_isNormalScheme_isFinite_projectiveSpace`: **Chow's lemma with normalization**, proved:
  a normal integral `X'` with a proper surjection onto `X`, of no larger dimension, with a finite
  morphism to projective space (normalization of the Chow cover; E. Noether's finiteness,
  `AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint`);
* `isTopologicallyFG_of_curve_of_hyperplane_of_isFinite`,
  `topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`: X.2.9 from the two remaining
  inputs, the curve case (for normal proper curves) and the hyperplane step (for normal integral
  proper `X` with a finite morphism to projective space).

The two remaining inputs are not formalized in general. Bertini's theorem (the hyperplane step) is
missing. The curve case is known in characteristic `0` for fields of cardinality `≤ 𝔠`, in
universe `0`, as a special case of X.2.9 itself, which is proved there for every proper connected
`X` without this reduction (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`, in
`SGA.SGA1.ExposeX.TopologicallyFiniteCharZero`). So the reduction would only matter where both
inputs are open: characteristic `p`, `#k > 𝔠`, universes other than `0`. For the curve case in
characteristic `p`, SGA proves X.2.6 by lifting the smooth curve to `W(k)` (III.7.4) and applying
X.2.3; this formalization plans another route, through a plane model and pinching
(`SGA.SGA1.ExposeIX.PinchingCurve`), which is not finished.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- If `i : Y₀ ⟶ Y` is a surjective closed immersion (e.g. `Y_red ⟶ Y`) and `Y` is connected,
then `π₁(Y)` is topologically finitely generated as soon as `π₁(Y₀)` is (at any geometric
points). From IX.1.7 (`ExposeIX.bijective_etaleFundamentalGroup_map_of_isClosedImmersion`). -/
theorem isTopologicallyFG_of_isClosedImmersion_of_surjective {Y₀ Y : Scheme.{u}} (i : Y₀ ⟶ Y)
    [IsClosedImmersion i] [Surjective i] [ConnectedSpace Y] {Ω₀ : Type u} [Field Ω₀]
    [IsSepClosed Ω₀] (y₀ : Spec (.of Ω₀) ⟶ Y₀)
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ y₀))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω y) :=
  (isTopologicallyFG_etaleFundamentalGroup_iff Ω₀ Ω (y₀ ≫ i) y).mp <|
    h.of_surjective _ (ExposeV.etaleFundamentalGroup.continuous_map Ω₀ i y₀)
      (ExposeIX.bijective_etaleFundamentalGroup_map_of_isClosedImmersion i Ω₀ y₀).2

/-- A scheme of finite type over a noetherian scheme by a quasi-compact morphism is noetherian. -/
private lemma isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y]
    [QuasiCompact f] [LocallyOfFiniteType f] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  { }

/-- The reduced closed subscheme on an irreducible closed subset of `X` is irreducible. -/
private lemma irreducibleSpace_subscheme {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z)
    (hirr : IsIrreducible Z) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme := by
  let ι := (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subschemeι
  have hrange : Set.range ι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IrreducibleSpace (Set.range ι) := Subtype.irreducibleSpace (by rw [hrange]; exact hirr)
  exact (Homeomorph.irreducibleSpace_iff ι.isClosedEmbedding.isEmbedding.toHomeomorph).mpr this

/-- X.2.9 for one proper connected `X` reduces to integral schemes of no larger dimension: if
`π₁` of every integral scheme `Z`, proper over the algebraically closed field `k`, with
`dim Z ≤ dim X`, is topologically finitely generated, so is `π₁(X)`. The reduced irreducible
components `X_i` of `X` form a finite family of proper connected schemes covering `X` (IX.5.2),
and `π₁(X_i)` does not change on passing to the reduced structure (IX.1.7). -/
theorem isTopologicallyFG_of_forall_isIntegral (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X]
    (h : ∀ ⦃Z : Scheme.{u}⦄ (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [IsIntegral Z],
      topologicalKrullDim Z ≤ topologicalKrullDim X → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (z : Spec (.of Ω) ⟶ Z), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω z))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  -- first the irreducible case, by passing to the reduced structure
  have hirr (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) [IsProper sY] [IrreducibleSpace Y]
      (hY : topologicalKrullDim Y ≤ topologicalKrullDim X) (Ω : Type u) [Field Ω]
      [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
      ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω y) := by
    let i := Y.nilradical.subschemeι
    have : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
    have hi : IsHomeomorph i :=
      isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩
    have : IrreducibleSpace Y.nilradical.subscheme :=
      (Homeomorph.irreducibleSpace_iff (hi.homeomorph i)).mpr inferInstance
    have : IsIntegral Y.nilradical.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hdim : topologicalKrullDim Y.nilradical.subscheme ≤ topologicalKrullDim X :=
      (i.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hY
    obtain ⟨y₀⟩ : Nonempty Y.nilradical.subscheme := inferInstance
    let t := ExposeV.geometricPointAt _ y₀
    exact isTopologicallyFG_of_isClosedImmersion_of_surjective i t (h (i ≫ sY) hdim _ t) Ω y
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType s
  let ι := irreducibleComponents X
  have : Finite ι := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  let I (c : ι) := Scheme.IdealSheafData.vanishingIdeal
    ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  let g (c : ι) := (I c).subschemeι
  have hrange (c : ι) : Set.range (g c) = c.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hirrc (c : ι) : IrreducibleSpace (I c).subscheme :=
    irreducibleSpace_subscheme _ _ c.2.1
  refine ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_family g (fun x ↦ ?_)
    (fun c ↦ ?_) Ω x
  · obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({x} : Set X) isIrreducible_singleton
    exact ⟨⟨Z, hZ⟩, by rw [hrange]; exact hxZ rfl⟩
  · obtain ⟨y₀⟩ : Nonempty (I c).subscheme := inferInstance
    let t := ExposeV.geometricPointAt _ y₀
    exact ⟨_, _, inferInstance, t, hirr _ (g c ≫ s)
      (g c).isClosedEmbedding.isInducing.topologicalKrullDim_le _ t⟩

/-- X.2.9 reduces to integral schemes: if `π₁` of every integral scheme proper over an
algebraically closed field is topologically finitely generated, then
`TopologicallyFiniteStatement` holds (`isTopologicallyFG_of_forall_isIntegral`). -/
theorem topologicallyFiniteStatement_of_isIntegral
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsProper s] [IsIntegral X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x)) :
    TopologicallyFiniteStatement.{u} := by
  rw [topologicallyFiniteStatement_iff]
  intro k _ _ X s _ _ Ω _ _ x
  exact isTopologicallyFG_of_forall_isIntegral k s (fun _ sZ _ _ _ ↦ h k sZ) Ω x

/-- X.2.9 reduces to integral projective schemes: if `π₁` of every integral scheme H-projective
over an algebraically closed field is topologically finitely generated, then
`TopologicallyFiniteStatement` holds (Chow's lemma and IX.5.2). -/
theorem topologicallyFiniteStatement_of_isHProjective
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsHProjective s] [IsIntegral X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x)) :
    TopologicallyFiniteStatement.{u} := by
  refine topologicallyFiniteStatement_of_isIntegral fun k _ _ X s _ _ Ω _ _ x ↦ ?_
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType s
  obtain ⟨X', π, -, hπ, hsurj, hπs, -, -, hX'⟩ := exists_isHProjective_of_isProper s
  have : IsProper π := inferInstance
  refine ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_family (ι := Unit)
    (fun _ ↦ π) (fun x ↦ ⟨(), hsurj.surj x⟩) (fun _ ↦ ?_) Ω x
  obtain ⟨y₀⟩ : Nonempty X' := inferInstance
  let t := ExposeV.geometricPointAt _ y₀
  exact ⟨_, _, inferInstance, t, h k (π ≫ s) _ t⟩

private lemma le_one_or_two_le (x : WithBot ℕ∞) : x ≤ 1 ∨ 2 ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact Or.inr (WithBot.coe_le_coe.mpr le_top)
    | coe m =>
      rcases Nat.lt_or_ge m 2 with h | h
      · exact Or.inl (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (by omega)))
      · exact Or.inr (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr h))

/-- **SGA's proof of X.2.9, by induction on the dimension**, in its most general form: run
inside a class `P` of algebraically closed fields, with a class `Q` of "good models" (proper
schemes over `k` with extra structure, e.g. H-projective ones). If
* `hC` (X.2.6, weak form): for `k` with `P k`, `π₁` of a normal integral curve (`dim ≤ 1`) which
  is a good model over `k` is topologically finitely generated (a normal curve over `k = k̄` is
  smooth, so this is X.2.6 for smooth curves);
* `hN` (Chow's lemma and normalization): for `k` with `P k`, every integral scheme proper over
  `k` is dominated, by a proper surjective morphism, by a normal integral good model of no larger
  dimension;
* `hH` (X.2.10, in existence form): for `k` with `P k` and `X` a normal integral good model over
  `k` with `dim X ≥ 2`, there are an algebraically closed extension `K` of `k` with `P K` and a
  proper connected `K`-scheme `Y` of smaller dimension with a morphism `Y ⟶ X_K` surjective on
  `π₁` (at some geometric point);

then `π₁(X)` is topologically finitely generated for every proper connected `X` over a field `k`
with `P k`, at every geometric point.

The form of `hH` is weaker than SGA's X.2.10 (which takes `K = k` and `Y` a hyperplane section)
and is also what the generic hyperplane over `K = k(u)‾` gives (Bertini; `k(u)‾` has the same
characteristic and, for `k` infinite, the same cardinality as `k`); X.1.8
(`isTopologicallyFG_etaleFundamentalGroup_of_pullback`) brings the induction back from `K` to
`k`. -/
theorem isTopologicallyFG_of_curve_of_hyperplane_of_model (P : ∀ (k : Type u) [Field k], Prop)
    (Q : ∀ (k : Type u) [Field k] ⦃X : Scheme.{u}⦄, (X ⟶ Spec (.of k)) → Prop)
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X], Q k s → ExposeI.IsNormalScheme X →
      topologicalKrullDim X ≤ 1 → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x))
    (hN : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X],
      ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (s' : X' ⟶ Spec (.of k)),
        IsProper π ∧ Surjective π ∧ IsProper s' ∧ Q k s' ∧ IsIntegral X' ∧
          ExposeI.IsNormalScheme X' ∧ topologicalKrullDim X' ≤ topologicalKrullDim X)
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X], Q k s → ExposeI.IsNormalScheme X →
      2 ≤ topologicalKrullDim X →
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : P K) (_ : Algebra k K)
        (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of K))
        (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
          Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y))
    (k : Type u) [Field k] [IsAlgClosed k] (hk : P k) ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
    [IsProper s] [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  suffices H : ∀ d : WithBot ℕ∞, ∀ (k : Type u) [Field k] [IsAlgClosed k], P k →
      ∀ ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X],
      topologicalKrullDim X ≤ d → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) from
    H _ k hk s le_rfl Ω x
  intro d
  induction d using WellFoundedLT.induction with
  | _ d IH =>
  intro k _ _ hk X s _ _ hXd Ω _ _ x
  refine isTopologicallyFG_of_forall_isIntegral k s (fun Z sZ _ _ hZ Ω' _ _ z ↦ ?_) Ω x
  obtain ⟨Z', π, s', hπ, hsurj, hs', hQ, hZ', hnorm, hdim⟩ := hN k hk sZ
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType sZ
  refine ExposeIX.isTopologicallyFG_etaleFundamentalGroup_of_family (ι := Unit) (fun _ ↦ π)
    (fun z ↦ ⟨(), hsurj.surj z⟩) (fun _ ↦ ?_) Ω' z
  obtain ⟨w⟩ : Nonempty Z' := inferInstance
  let t := ExposeV.geometricPointAt _ w
  refine ⟨_, _, inferInstance, t, ?_⟩
  rcases le_one_or_two_le (topologicalKrullDim Z') with h1 | h2
  · exact hC k hk s' hQ hnorm h1 _ t
  · obtain ⟨K, _, _, hK, _, Y, sY, i, hsY, hY, hYdim, Ω₀, _, _, y, hsurjY⟩ :=
      hH k hk s' hQ hnorm h2
    have hlt : topologicalKrullDim Y < d := hYdim.trans_le (hdim.trans (hZ.trans hXd))
    have hYfg := IH _ hlt K hK sY le_rfl Ω₀ y
    have hZK := hYfg.of_surjective _ (ExposeV.etaleFundamentalGroup.continuous_map Ω₀ i y)
      hsurjY
    exact isTopologicallyFG_etaleFundamentalGroup_of_pullback k K s' (y ≫ i) hZK _ t

/-- SGA's induction (`isTopologicallyFG_of_curve_of_hyperplane_of_model`) with H-projective
models: inside a class `P` of algebraically closed fields, `π₁` is topologically finitely
generated as soon as `hC` (X.2.6 for normal, hence smooth, projective curves), `hN` (Chow's lemma
and normalization, with an H-projective normalization) and `hH` (X.2.10 in existence form, for
normal integral H-projective `X`) hold. The version without `hN` is
`isTopologicallyFG_of_curve_of_hyperplane_of_isFinite`. -/
theorem isTopologicallyFG_of_curve_of_hyperplane (P : ∀ (k : Type u) [Field k], Prop)
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsHProjective s] [IsIntegral X], ExposeI.IsNormalScheme X →
      topologicalKrullDim X ≤ 1 → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x))
    (hN : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X],
      ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (s' : X' ⟶ Spec (.of k)),
        IsProper π ∧ Surjective π ∧ IsHProjective s' ∧ IsIntegral X' ∧
          ExposeI.IsNormalScheme X' ∧ topologicalKrullDim X' ≤ topologicalKrullDim X)
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsHProjective s] [IsIntegral X], ExposeI.IsNormalScheme X →
      2 ≤ topologicalKrullDim X →
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : P K) (_ : Algebra k K)
        (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of K))
        (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
          Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y))
    (k : Type u) [Field k] [IsAlgClosed k] (hk : P k) ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
    [IsProper s] [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  refine isTopologicallyFG_of_curve_of_hyperplane_of_model P (fun _ _ _ s ↦ IsHProjective s)
    (fun k _ _ hk X s _ _ hQ ↦ have := hQ; hC k hk s) (fun k _ _ hk X s _ _ ↦ ?_)
    (fun k _ _ hk X s _ _ hQ ↦ have := hQ; hH k hk s) k hk s Ω x
  obtain ⟨X', π, s', h₁, h₂, h₃, h₄⟩ := hN k hk s
  exact ⟨X', π, s', h₁, h₂, (have := h₃; inferInstance), h₃, h₄⟩

/-- **X.2.9 from its three inputs** (`isTopologicallyFG_of_curve_of_hyperplane` for the class of
all algebraically closed fields): `TopologicallyFiniteStatement` holds as soon as `hC` (X.2.6
for normal, i.e. smooth, projective curves), `hN` (Chow and normalization) and `hH` (X.2.10 in
existence form) do, over all algebraically closed fields. Without `hN`:
`topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`. -/
theorem topologicallyFiniteStatement_of_curve_of_hyperplane
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsHProjective s] [IsIntegral X], ExposeI.IsNormalScheme X → topologicalKrullDim X ≤ 1 →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x))
    (hN : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsProper s] [IsIntegral X], ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (s' : X' ⟶ Spec (.of k)),
        IsProper π ∧ Surjective π ∧ IsHProjective s' ∧ IsIntegral X' ∧
          ExposeI.IsNormalScheme X' ∧ topologicalKrullDim X' ≤ topologicalKrullDim X)
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsHProjective s] [IsIntegral X], ExposeI.IsNormalScheme X → 2 ≤ topologicalKrullDim X →
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K) (Y : Scheme.{u})
        (sY : Y ⟶ Spec (.of K))
        (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
          Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y)) :
    TopologicallyFiniteStatement.{u} := by
  rw [topologicallyFiniteStatement_iff]
  intro k _ _ X s _ _ Ω _ _ x
  refine isTopologicallyFG_of_curve_of_hyperplane (fun _ _ ↦ True)
    (fun k _ _ _ ↦ hC k) (fun k _ _ _ ↦ hN k) (fun k _ _ _ X s _ _ hn h2 ↦ ?_) k trivial s Ω x
  obtain ⟨K, hF, hA, hAlg, Y, sY, i, h⟩ := hH k s hn h2
  exact ⟨K, hF, hA, trivial, hAlg, Y, sY, i, h⟩

/-- **Chow's lemma with normalization** (the input `hN` of SGA's proof of X.2.9): every integral
scheme `X` proper over an algebraically closed (more generally, perfect) field `k` is dominated,
by a proper surjective morphism `π : X' ⟶ X`, by a normal integral `k`-scheme `X'` of no larger
dimension which admits a finite morphism `g : X' ⟶ ℙ(σ; k)` over `k`. (`X'` is the
normalization, `AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint`, of
the H-projective cover `X''` of Chow's lemma; `g` is `X' ⟶ X'' ⟶ ℙ(σ; k)`; `X'` is not shown
H-projective, a finite morphism to projective space is what the hyperplane step uses.) -/
theorem exists_isNormalScheme_isFinite_projectiveSpace (k : Type u) [Field k] [PerfectField k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (σ : Type u) (_ : Finite σ)
      (g : X' ⟶ ℙ(σ; Spec (.of k))), IsProper π ∧ Surjective π ∧ IsFinite g ∧
        g ≫ ℙ(σ; Spec (.of k)) ↘ Spec (.of k) = π ≫ s ∧ IsIntegral X' ∧
          ExposeI.IsNormalScheme X' ∧ topologicalKrullDim X' ≤ topologicalKrullDim X := by
  obtain ⟨X'', π'', U, hπ'', hsurj'', hX''s, hU, hiso, hX''⟩ := exists_isHProjective_of_isProper s
  obtain ⟨σ, _, i, hi, his⟩ := hX''s.exists_isClosedImmersion
  have : LocallyOfFiniteType (π'' ≫ s) := inferInstance
  let ν := (X''.fromSpecStalk (genericPoint X'')).fromNormalization
  have : IsFinite ν := isFinite_fromNormalization_fromSpecStalk_genericPoint (π'' ≫ s)
  have : Surjective (π'' ≫ s) := inferInstance
  refine ⟨_, ν ≫ π'', σ, inferInstance, ν ≫ i, inferInstance, inferInstance, inferInstance,
    by rw [Category.assoc, his, Category.assoc], inferInstance,
    fun x ↦ ⟨inferInstance, isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint x⟩,
    ?_⟩
  calc topologicalKrullDim _ ≤ topologicalKrullDim X'' :=
        Scheme.Hom.topologicalKrullDim_le_of_locallyQuasiFinite ν
    _ = topologicalKrullDim X := topologicalKrullDim_eq_of_isIso_morphismRestrict s (π'' ≫ s) π'' hU

/-- **SGA's proof of X.2.9 with Chow's lemma and normalization done**, inside a class `P` of
algebraically closed fields: `π₁(X)` is topologically finitely generated for every proper
connected `X` over `k` with `P k`, at every geometric point, as soon as
* `hC` (X.2.6, weak form): `π₁` of a normal integral proper curve over a field `k` with `P k` is
  topologically finitely generated (such a curve is smooth,
  `smooth_of_isNormalScheme_of_topologicalKrullDim_le_one`);
* `hH` (X.2.10, existence form): for `k` with `P k` and `X` normal, integral, proper over `k`,
  with a finite morphism to some `ℙ(σ; k)` over `k` and `dim X ≥ 2`, there are an algebraically
  closed `K ⊇ k` with `P K` and a proper connected `K`-scheme `Y` of smaller dimension with a
  morphism `Y ⟶ X_K` surjective on `π₁`.

The remaining input of SGA's reduction, Chow's lemma with normalization, is
`exists_isNormalScheme_isFinite_projectiveSpace`. -/
theorem isTopologicallyFG_of_curve_of_hyperplane_of_isFinite (P : ∀ (k : Type u) [Field k], Prop)
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X], ExposeI.IsNormalScheme X →
      topologicalKrullDim X ≤ 1 → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x))
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k], P k → ∀ ⦃X : Scheme.{u}⦄
      (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X], ExposeI.IsNormalScheme X →
      (∃ (σ : Type u) (_ : Finite σ) (g : X ⟶ ℙ(σ; Spec (.of k))),
        IsFinite g ∧ g ≫ ℙ(σ; Spec (.of k)) ↘ Spec (.of k) = s) →
      2 ≤ topologicalKrullDim X →
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : P K) (_ : Algebra k K)
        (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of K))
        (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
          Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y))
    (k : Type u) [Field k] [IsAlgClosed k] (hk : P k) ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
    [IsProper s] [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  refine isTopologicallyFG_of_curve_of_hyperplane_of_model P
    (fun k _ X s ↦ ∃ (σ : Type u) (_ : Finite σ) (g : X ⟶ ℙ(σ; Spec (.of k))),
      IsFinite g ∧ g ≫ ℙ(σ; Spec (.of k)) ↘ Spec (.of k) = s)
    (fun k _ _ hk X s _ _ _ ↦ hC k hk s) (fun k _ _ hk X s _ _ ↦ ?_)
    (fun k _ _ hk X s _ _ hQ hn ↦ hH k hk s hn hQ) k hk s Ω x
  obtain ⟨X', π, σ, _, g, hπ, hsurj, hg, hgs, hX', hnorm, hdim⟩ :=
    exists_isNormalScheme_isFinite_projectiveSpace k s
  exact ⟨X', π, π ≫ s, hπ, hsurj, inferInstance, ⟨σ, inferInstance, g, hg, hgs⟩, hX', hnorm,
    hdim⟩

/-- **X.2.9 from the curve case and the hyperplane step** (Chow's lemma and normalization being
proved, `exists_isNormalScheme_isFinite_projectiveSpace`): `TopologicallyFiniteStatement` holds
as soon as `hC` (X.2.6, weak form, for normal proper curves) and `hH` (X.2.10 in existence form,
for normal integral proper `X` with a finite morphism to projective space) hold over all
algebraically closed fields. -/
theorem topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsProper s] [IsIntegral X], ExposeI.IsNormalScheme X → topologicalKrullDim X ≤ 1 →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x))
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsProper s] [IsIntegral X], ExposeI.IsNormalScheme X →
      (∃ (σ : Type u) (_ : Finite σ) (g : X ⟶ ℙ(σ; Spec (.of k))),
        IsFinite g ∧ g ≫ ℙ(σ; Spec (.of k)) ↘ Spec (.of k) = s) →
      2 ≤ topologicalKrullDim X →
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K) (Y : Scheme.{u})
        (sY : Y ⟶ Spec (.of K))
        (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
          Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y)) :
    TopologicallyFiniteStatement.{u} := by
  rw [topologicallyFiniteStatement_iff]
  intro k _ _ X s _ _ Ω _ _ x
  refine isTopologicallyFG_of_curve_of_hyperplane_of_isFinite (fun _ _ ↦ True)
    (fun k _ _ _ ↦ hC k) (fun k _ _ _ X s _ _ hn hg h2 ↦ ?_) k trivial s Ω x
  obtain ⟨K, hF, hA, hAlg, Y, sY, i, h⟩ := hH k s hn hg h2
  exact ⟨K, hF, hA, trivial, hAlg, Y, sY, i, h⟩

end SGA.SGA1.ExposeX
