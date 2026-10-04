/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFiniteHyperplaneCovers
import SGA.SGA1.ExposeX.TopologicallyFiniteReduction
import SGA.SGA1.ExposeX.CurveFinitePlaneModel

/-!
# SGA 1, Exposé X, 2.9 from the curve case

SGA proves X.2.9 by induction on the dimension: Chow's lemma and normalization reduce to a normal
integral `X` with a finite morphism to projective space, and X.2.10 (Bertini) gives a connected
hyperplane section `Y` over an algebraically closed extension `K ⊇ k`, of smaller dimension, with
`π₁(Y) ↠ π₁(X_K)`. Here X.2.10 is proved in existence form
(`exists_hyperplane_section`, in every characteristic, from the generic hyperplane section of
`SGA.SGA1.ExposeX.TopologicallyFiniteHyperplane` and the Bertini field lemma
`Bertini.mem_of_isAlgebraic`), so that:

* `topologicallyFiniteStatement_of_curve`: **X.2.9 follows from the curve case** (X.2.6 for
  normal proper curves, `hC`);
* `topologicallyFiniteStatement_of_planeCurve`: **X.2.9 follows from the case of plane curves**
  (the fundamental group of the plane curve `planeCurve k x y` of a plane model of a function
  field of transcendence degree `1` is topologically finitely generated).

The curve case in characteristic `p` is not proved yet (it is the remaining input of X.2.9).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- A cardinal at least `2` (as an element of `ℕ∞` through `toENat`) is at least `2`. -/
private lemma two_le_of_two_le_toENat {c : Cardinal.{u}} (h : (2 : WithBot ℕ∞) ≤ c.toENat) :
    2 ≤ c := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.mp (hc.trans Cardinal.ofNat_lt_aleph0)
  have hn : n < 2 := by exact_mod_cast hc
  rw [Cardinal.toENat_nat] at h
  have : (2 : ℕ∞) ≤ n := WithBot.coe_le_coe.mp h
  exact absurd (by exact_mod_cast this : 2 ≤ n) (by omega)

/-- **X.2.10, existence form** (SGA 1 X.2.10–2.11 in the form used for X.2.9): let `X` be a
normal integral scheme, proper over an algebraically closed field `k`, of dimension `≥ 2`. There
are an algebraically closed field `K ⊇ k` and a proper connected `K`-scheme `Y` of smaller
dimension, with a morphism `i : Y ⟶ X_K` such that `π₁(Y) → π₁(X_K)` is surjective (at a
geometric point). `Y` is the generic hyperplane section of `X` (`Hyperplane.Y`). SGA asks for `X`
projective; no projectivity is needed here. -/
theorem exists_hyperplane_section (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsProper s] [IsIntegral X] (hX : ExposeI.IsNormalScheme X)
    (h2 : 2 ≤ topologicalKrullDim X) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K) (Y : Scheme.{u})
      (sY : Y ⟶ Spec (.of K))
      (i : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      IsProper sY ∧ ConnectedSpace Y ∧ topologicalKrullDim Y < topologicalKrullDim X ∧
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (y : Spec (.of Ω) ⟶ Y),
        Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω i y) := by
  let _ : Algebra k X.functionField := (ExposeXI.functionFieldMap s).toAlgebra
  have hk : algebraMap k X.functionField = ExposeXI.functionFieldMap s := rfl
  -- two algebraically independent functions
  have htr : 2 ≤ Algebra.trdeg k X.functionField := by
    rw [topologicalKrullDim_eq_trdeg_functionField s hk] at h2
    exact two_le_of_two_le_toENat h2
  obtain ⟨ι, b, hb⟩ := exists_isTranscendenceBasis' k X.functionField
  rw [← hb.cardinalMk_eq_trdeg, Cardinal.two_le_iff] at htr
  obtain ⟨i, j, hij⟩ := htr
  have hxy : AlgebraicIndependent k ![b i, b j] := by
    have h := hb.1.comp ![i, j] (by
      intro a c hac
      fin_cases a <;> fin_cases c <;> simp_all [eq_comm])
    convert h using 1
    ext a
    fin_cases a <;> rfl
  -- the generic hyperplane section
  have : ConnectedSpace (Hyperplane.Y s hk hxy) := Hyperplane.connectedSpace_Y s hk hxy
  obtain ⟨w⟩ : Nonempty (Hyperplane.Y s hk hxy) := inferInstance
  exact ⟨Hyperplane.K k, inferInstance, inferInstance, inferInstance, Hyperplane.Y s hk hxy,
    pullback.snd _ _, Hyperplane.toXK s hk hxy, inferInstance, inferInstance,
    Hyperplane.topologicalKrullDim_Y_lt s hk hxy, _, inferInstance, inferInstance,
    ExposeV.geometricPointAt _ w, Hyperplane.surjective_map_toXK s hk hxy hX _ _⟩

/-- **X.2.9 from the curve case**: `TopologicallyFiniteStatement` holds (in universe `u`) as soon
as the fundamental group of every normal integral proper curve over an algebraically closed field
is topologically finitely generated (X.2.6, weak form). Chow's lemma and normalization
(`exists_isNormalScheme_isFinite_projectiveSpace`) and X.2.10 (`exists_hyperplane_section`) are
proved. -/
theorem topologicallyFiniteStatement_of_curve
    (hC : ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
      [IsProper s] [IsIntegral X], ExposeI.IsNormalScheme X → topologicalKrullDim X ≤ 1 →
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x)) :
    TopologicallyFiniteStatement.{u} :=
  topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite hC
    fun k _ _ _ s _ _ hX _ h2 ↦ exists_hyperplane_section k s hX h2

/-- **X.2.9 from the case of plane curves**: `TopologicallyFiniteStatement` holds (in universe
`u`) as soon as, for every algebraically closed field `k` and every plane model `(x, y, f)` of a
finitely generated extension `K/k` of transcendence degree `1` (`K = k(x, y)`, `x` transcendental,
`ker(k[s][t] → K) = (f)` with `f` monic irreducible of positive degree), the fundamental group of
the plane curve `planeCurve k x y` is topologically finitely generated at some geometric point.
In characteristic `0` (universe `0`) this hypothesis holds by
`isTopologicallyFG_etaleFundamentalGroup_of_charZero`; in characteristic `p` it is open. -/
theorem topologicallyFiniteStatement_of_planeCurve
    (hP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K]
      [Algebra.EssFiniteType k K] (x y : K),
      Algebra.trdeg k K = 1 → Transcendental k x → IntermediateField.adjoin k {x, y} = ⊤ →
      (∃ f : Polynomial (Polynomial k), f.Monic ∧ Irreducible f ∧ 0 < f.natDegree ∧
        RingHom.ker (Polynomial.eval₂RingHom (Polynomial.aeval x).toRingHom y) =
          Ideal.span {f}) →
      ∃ (Ω₀ : Type u) (_ : Field Ω₀) (_ : IsSepClosed Ω₀) (s₀ : Spec (.of Ω₀) ⟶ planeCurve k x y),
        ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ s₀)) :
    TopologicallyFiniteStatement.{u} :=
  topologicallyFiniteStatement_of_curve fun k _ _ _ s _ _ _ hdim Ω _ _ x ↦
    isTopologicallyFG_of_forall_planeCurve_of_le_one s (hP k) hdim Ω x

end SGA.SGA1.ExposeX
