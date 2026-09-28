/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.Purity
import SGA.SGA1.ExposeXI.Geometry

/-!
# Birational invariance of `π₁ = 0` and of `π₁` finite (XI.1.2, XI.1.3, from X.3.4)

XI.1.2 and XI.1.3 follow from the birational invariance of the fundamental group (X.3.4,
`ExposeX.BirationalInvarianceStatement`, proved as `ExposeX.birationalInvariance`; the
unconditional forms are in `BirationalInvariance`): a proper regular variety birational to
a simply connected one is simply connected (`isSimplyConnected_of_partialIso`), and one
birational to a variety with finite fundamental group has finite fundamental group
(`hasFiniteFundamentalGroup_of_partialIso`). The formal part is that both properties are
invariant under an equivalence of the categories of étale coverings
(`isSimplyConnected_of_equivalence`), compatible with fibre functors in the second case.

SGA then applies this with `Y = ℙʳ` (or a quotient `ℙʳ/G`); for `Y = ℙʳ` this is
`ProjectiveSpace.isSimplyConnected_of_partialIso_projectiveSpace`. XI.1.2 and XI.1.3 in SGA's form
(for normal varieties, with the rationality hypotheses on the function field) are proved in
`RationalVarieties` and `UnirationalVarieties`, directly from purity X.3.3.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

/-- A connected scheme is simply connected if and only if every connected étale covering is
trivial (its structure morphism is an isomorphism). -/
lemma isSimplyConnected_iff_forall_isConnected {X : Scheme.{u}} [ConnectedSpace X] :
    IsSimplyConnected X ↔
      ∀ Z : ExposeV.FEt X, IsConnected Z → IsIso (Z.hom : Z.left ⟶ X) := by
  constructor
  · rintro ⟨-, h⟩ Z hZ
    have := ExposeV.FEt.connectedSpace_of_isConnected Z
    have : IsFinite (Z.hom : Z.left ⟶ X) := Z.prop.1
    have : Etale (Z.hom : Z.left ⟶ X) := Z.prop.2
    exact h _ ‹_›
  · intro h
    refine ⟨inferInstance, fun Y f _ _ hY ↦ ?_⟩
    let Z : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
    have : ConnectedSpace Z.left := hY
    exact h Z (ExposeV.FEt.isConnected_of_connectedSpace Z)

/-- Simple connectedness is invariant under an equivalence of the categories of étale
coverings. -/
lemma isSimplyConnected_of_equivalence {X Y : Scheme.{u}} [ConnectedSpace X]
    (E : ExposeV.FEt X ≌ ExposeV.FEt Y) (hY : IsSimplyConnected Y) : IsSimplyConnected X := by
  have := hY.1
  rw [isSimplyConnected_iff_forall_isConnected] at hY ⊢
  intro Z hZ
  have hZ' : IsConnected (E.functor.obj Z) := (ExposeV.isConnected_functor_obj_iff E Z).2 hZ
  have := hY _ hZ'
  have ht : IsTerminal Z :=
    IsTerminal.isTerminalOfObj E.functor Z (ExposeV.FEt.isTerminalOfIsIso _)
  let T : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  have : IsIso (T.hom : T.left ⟶ X) := inferInstanceAs (IsIso (𝟙 X))
  let i : Z ≅ T := ht.uniqueUpToIso (ExposeV.FEt.isTerminalOfIsIso T)
  let g := (MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).map i.hom
  have hg : IsIso g := inferInstance
  have hw : g ≫ (T.hom : T.left ⟶ X) = Z.hom :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ X).map i.hom)
  rw [← hw]
  exact IsIso.comp_isIso' hg ‹_›

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
  [IsProper sX] [IsProper sY] [IsIntegral X] [IsIntegral Y]

/-- XI.1.2, from X.3.4 (given as the hypothesis `hB`; see
`isSimplyConnected_of_partialIso_of_isRegularScheme` for the unconditional form): a proper,
integral, regular `k`-scheme birational to a simply connected one (e.g. to `ℙʳ`, XI.1.1) is simply
connected. SGA states XI.1.2 for normal varieties whose function field is purely transcendental
(`rationalSimplyConnectedStatement`); here the birational map is given. -/
theorem isSimplyConnected_of_partialIso (hB : ExposeX.BirationalInvarianceStatement.{u})
    (hX : ExposeX.IsRegularScheme X) (hY : ExposeX.IsRegularScheme Y) (φ : X.PartialIso Y)
    (hφ : φ.IsOver sX sY) (h : IsSimplyConnected Y) : IsSimplyConnected X := by
  obtain ⟨E, -⟩ := hB k sX sY hX hY φ hφ
  exact isSimplyConnected_of_equivalence E h

/-- XI.1.3, from X.3.4 (given as the hypothesis `hB`; see
`hasFiniteFundamentalGroup_of_partialIso_of_isRegularScheme` for the unconditional form): a proper,
integral, regular `k`-scheme birational to one with finite fundamental group has finite
fundamental group. -/
theorem hasFiniteFundamentalGroup_of_partialIso (hB : ExposeX.BirationalInvarianceStatement.{u})
    (hX : ExposeX.IsRegularScheme X) (hY : ExposeX.IsRegularScheme Y) (φ : X.PartialIso Y)
    (hφ : φ.IsOver sX sY) (h : HasFiniteFundamentalGroup Y) : HasFiniteFundamentalGroup X := by
  obtain ⟨E, ⟨β⟩⟩ := hB k sX sY hX hY φ hφ
  -- a geometric point of the common open subset
  obtain ⟨x, hx⟩ : (φ.source : Set X).Nonempty := φ.dense_source.nonempty
  let u₀ : φ.source.toScheme := ⟨x, hx⟩
  let K := φ.source.toScheme.residueField u₀
  let Ω := AlgebraicClosure K
  let u : Spec (.of Ω) ⟶ φ.source.toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ φ.source.toScheme.fromSpecResidueField u₀
  let ψ := φ.iso.hom ≫ φ.target.ι
  let e : E.functor ⋙ ExposeV.FEt.fiber Ω (u ≫ ψ) ≅ ExposeV.FEt.fiber Ω (u ≫ φ.source.ι) :=
    Functor.isoWhiskerLeft E.functor (ExposeV.FEt.pullbackFiberIso Ω ψ u).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight β (ExposeV.FEt.fiber Ω u) ≪≫
      ExposeV.FEt.pullbackFiberIso Ω φ.source.ι u
  have := h.2 Ω (u ≫ ψ)
  have hfin : Finite (ExposeV.etaleFundamentalGroup Ω (u ≫ φ.source.ι)) :=
    Finite.of_surjective _ (ExposeV.autMap_bijective E.functor e).2
  exact (hasFiniteFundamentalGroup_iff_exists).2 ⟨Ω, inferInstance, inferInstance, _, hfin⟩

end SGA.SGA1.ExposeXI
