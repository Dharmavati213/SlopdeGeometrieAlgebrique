/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.ArithmeticSurface.ModelStatements
import SGA.Foundations.Semistable.CurveStatements
import SGA.Foundations.Semistable.NumericalTypeBound
import SGA.SGA1.ExposeX.TameLiftingNormalization
import SGA.SGA1.ExposeXIII.SemistableReductionGood
import SGA.SGA1.ExposeXIII.SemistableReductionRationalPoint

/-!
# The semistable reduction theorem from its geometric inputs

`SemistableReductionStatement` (the input of Raynaud's case B of XIII.2.13, stated in
`SGA.SGA1.ExposeXIII.AbhyankarAffineLine`) is deduced here from interface statements for the
geometric inputs of the proof of Artin–Winters in the form of Stacks, Sections 0CDK, 0CEG and
0CEI, together with the bound on the Picard group of a minimal numerical type proved in
`SGA.Foundations.Semistable.NumericalTypeBound`
(`SGA.SGA1.ExposeXIII.semistableReductionStatement_of_inputs`). **This is a conditional result:**
the inputs are open (registry rows A21, A50, A51, A61 of `notes/topics/out-of-scope-plan.md`),
except `AlgebraicGeometry.RationalPointModelStatement` (Stacks, Tag 0CE8 (1), (2)), which is proved
(`SGA.SGA1.ExposeXIII.rationalPointModelStatement`) and used directly.

The inputs:

* curves over a field: `AlgebraicGeometry.TorsionBecomesVisibleStatement` (Stacks, Tag 0CDU),
  `AlgebraicGeometry.GenusBaseChangeStatement` (Stacks, Tag 02KH),
  `AlgebraicGeometry.GenusZeroSmoothModelStatement` (Stacks, Section 0CDK),
  `AlgebraicGeometry.PicTorsionReducedCurveStatement` (Stacks, Tag 0C20);
* regular models: `AlgebraicGeometry.MinimalModelStatement` (Tags 0C2W, 0CA6),
  `NumericalTypeOfModelStatement` (Tags 0CA4, 0CA3), `PicTorsionModelStatement` (Tags 0CAD,
  0CAE), `GenusReducedFibreUpperStatement` (Tags 0CE9, 0CE8), `GenusReducedFibreLowerStatement`
  (Tag 0CEA), `ClosedFibreDimensionStatement` (Tag 0D4J);
* the last step, `SGA.SGA1.ExposeXIII.SemistableOfMulticrossStatement`: if all multiplicities of
  the closed fibre of a regular model are `1` and its reduction has only multicross singularities,
  then the closed fibre is a semistable curve (`X_k` is a Cartier divisor in a regular scheme, so
  it has no embedded points and is planar; a planar multicross singularity is a node; Stacks,
  Tags 0C5Z, 0C60, 0CDZ).

## The argument (Stacks, Sections 0CEG and 0CEI, with `k` algebraically closed)

Genus `0` is `GenusZeroSmoothModelStatement` with the good reduction case
(`hasSemistableReduction_of_smooth_model`). For genus `g ≥ 1` choose a prime `ℓ` invertible in `k`
with `ℓ > 2⁹ · 6g` and `ℓ > 2¹⁰`, and a finite separable extension `K'/K` over which `C` has a
rational point and `Pic(C)[ℓ] ≅ (ℤ/ℓ)^{2g}` (Tag 0CDU); the normalization `R'` of `R` in `K'` is
again a complete discrete valuation ring with algebraically closed residue field
(`SGA.SGA1.ExposeX.isDiscreteValuationRing_integralClosure`). Over `R'`, take a minimal model `X`
with numerical type `T` (minimal, genus `g`, some `mᵢ = 1`) and `Y = (X_k)_red`. Then

`ℓ^{2g} = |Pic(C)[ℓ]| ≤ |Pic(T)[ℓ]| · |Pic(Y)[ℓ]| ≤ ℓ^{g_top} · ℓ^{h¹(Y) + g_geom(Y)}`

(Tags 0CAD/0CAE, `AlgebraicGeometry.NumericalType.card_torsionBy_pic_le_of_isMinimal` and its
genus-one analogue, Tag 0C20) and `g_top + g_geom(Y) ≤ h¹(Y) ≤ g` (Tags 0CEA, 0CE9). So all these
inequalities are equalities: `h¹(Y) = g`, hence all `mᵢ = 1` (Tag 0CE9), and
`|Pic(Y)[ℓ]| = ℓ^{h¹(Y) + g_geom(Y)}`, hence `Y` has only multicross singularities (Tag 0C20), and
the closed fibre is semistable (`SemistableOfMulticrossStatement`).

Unlike Stacks (Section 0CEG), the genus-one case uses the same argument as genus `≥ 2`, through
`AlgebraicGeometry.NumericalType.card_torsionBy_pic_le_of_genus_eq_one`, instead of the
classification of minimal numerical types of genus one (Tag 0C8T).

## Main results

* `SGA.SGA1.ExposeXIII.SemistableOfMulticrossStatement` (statement);
* `SGA.SGA1.ExposeXIII.exists_semistable_model_of_picTorsion`: the main step, for a curve of genus
  `≥ 1` with a rational point and `Pic(C)[ℓ] ≅ (ℤ/ℓ)^{2g}` (conditional on the model inputs);
* `SGA.SGA1.ExposeXIII.semistableReductionStatement_of_inputs`: `SemistableReductionStatement`
  from all the inputs (conditional);
* `SGA.SGA1.ExposeXIII.isAlgClosed_residueField_integralClosure`: the residue field of the
  normalization of a complete discrete valuation ring with algebraically closed residue field in a
  finite separable extension is algebraically closed.

## References

* [M. Artin, G. Winters, *Degenerate fibres and stable reduction of curves*, Topology 10 (1971)]
* [Stacks Project, Chapter 55 (Semistable Reduction), Sections 0CDK, 0CEG, 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXIII

open ExposeX

section ResidueField

variable (R K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

include K in
/-- The residue field of the normalization of a complete discrete valuation ring with
algebraically closed residue field in a finite separable extension of its fraction field is
algebraically closed (it is a finite extension of the residue field of `R`). -/
theorem isAlgClosed_residueField_integralClosure [IsAlgClosed (ResidueField R)] :
    letI := isLocalRing_integralClosure R K L
    IsAlgClosed (ResidueField (integralClosure R L)) := by
  let := isLocalRing_integralClosure R K L
  let := isLocalHom_integralClosure R K L
  have := finite_residueField_integralClosure R K L
  exact IsAlgClosed.of_ringEquiv (ResidueField R) _
    (RingEquiv.ofBijective _ (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField R)
      (K := ResidueField (integralClosure R L))))

end ResidueField

/-- The last step of the semistable reduction theorem (statement; Stacks, Tags 0C5Z, 0C60, 0CDZ,
in the proofs of Sections 0CEG and 0CEI): let `X` be a regular proper model of a smooth proper
geometrically connected curve over the fraction field of a discrete valuation ring with
algebraically closed residue field `k`. If every irreducible component of `X_k` has multiplicity
`1` and every closed point of `(X_k)_red` is a regular point or a multicross singularity, then
`X_k` is a semistable curve.

Stacks argues: `X_k` is a Cartier divisor in the regular scheme `X`, hence Cohen–Macaulay, so it is
reduced once all `mᵢ = 1`; it is Gorenstein (Tag 0C60), and a Gorenstein multicross singularity is a
node (Tag 0CDZ). (An alternative to Gorenstein: the local rings of `X_k` at closed points have
embedding dimension `≤ 2`, and a multicross singularity with `n` branches has embedding
dimension `n`.) -/
def SemistableOfMulticrossStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] (X : Scheme.{u})
    (g : X ⟶ Spec (.of R)), IsRegularProperModel g f →
    ∀ [Fintype (irreducibleComponents (closedFibre g))],
      (∀ Z : irreducibleComponents (closedFibre g), Scheme.componentMultiplicity Z = 1) →
      (∀ y : (closedFibre g).reduction, IsClosed ({y} : Set (closedFibre g).reduction) →
        IsRegularLocalRing ((closedFibre g).reduction.presheaf.stalk y) ∨
          Scheme.IsMulticrossPoint (IsLocalRing.ResidueField R) y) →
      IsSemistableCurve (IsLocalRing.ResidueField R) (closedFibre g)


section MainStep

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
  (g : X ⟶ Spec (.of R)) [IsProper g]

/-- The reduced closed fibre of a proper scheme over a discrete valuation ring is proper over the
residue field. -/
instance isProper_reductionι_comp_closedFibreHom :
    IsProper ((closedFibre g).reductionι ≫ closedFibreHom g) := by
  infer_instance

/-- The reduced closed fibre of a proper scheme over a discrete valuation ring is noetherian. -/
lemma isNoetherian_reduction_closedFibre : IsNoetherian (closedFibre g).reduction := by
  have : IsLocallyNoetherian (closedFibre g).reduction :=
    LocallyOfFiniteType.isLocallyNoetherian ((closedFibre g).reductionι ≫ closedFibreHom g)
  have : CompactSpace (closedFibre g).reduction :=
    QuasiCompact.compactSpace_of_compactSpace ((closedFibre g).reductionι ≫ closedFibreHom g)
  exact ⟨⟩

/-- The main step of the semistable reduction theorem in genus `g ≥ 1` (Stacks, Sections 0CEG and
0CEI, conditional on the inputs listed in the module docstring): let `R` be a discrete valuation
ring with algebraically closed residue field `k`, and `C` a smooth proper geometrically connected
curve of genus `g ≥ 1` over `K = Frac R` with a `K`-rational point. Let `ℓ` be a prime invertible
in `k` with `ℓ > 2¹⁰ · 3g`, such that `Pic(C)[ℓ] ≅ (ℤ/ℓ)^{2g}`. Then the closed fibre of a minimal
model of `C` is a semistable curve. -/
theorem exists_semistable_model_of_picTorsion
    (hM : MinimalModelStatement.{u}) (hN : NumericalTypeOfModelStatement.{u})
    (hP : PicTorsionModelStatement.{u})
    (hG1 : GenusReducedFibreUpperStatement.{u}) (hG2 : GenusReducedFibreLowerStatement.{u})
    (hD : ClosedFibreDimensionStatement.{u}) (hB : PicTorsionReducedCurveStatement.{u})
    (hL : SemistableOfMulticrossStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAlgClosed (ResidueField R)] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (C : Scheme.{u}) (f : C ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (hgenus : 1 ≤ f.genus) (hpt : ∃ s : Spec (.of K) ⟶ C, s ≫ f = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓk : (ℓ : ResidueField R) ≠ 0) (hℓ : 2 ^ 10 * (3 * f.genus) < ℓ)
    (hpic : Nonempty ((powMonoidHom ℓ : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod ℓ))) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (.of R)), IsRegularProperModel g f ∧
      IsSemistableCurve (ResidueField R) (closedFibre g) := by
  classical
  obtain ⟨X, g, hX, hmin⟩ := hM R K C f
  have : IsProper g := hX.1
  have : Flat g := hX.2.1
  have := finite_irreducibleComponents_closedFibre g
  let _ : Fintype (irreducibleComponents (closedFibre g)) := Fintype.ofFinite _
  obtain ⟨T, hTm, hTa, hTg, hTgenus⟩ := hN R K C f X g hX
  obtain ⟨x, Z₀, hxc, -, -, hxreg, hm₀⟩ := rationalPointModelStatement R K C f X g hX hpt
  have hTmin : T.IsMinimal := by
    rintro Z ⟨h1, h2⟩
    refine hmin Z ⟨?_, ?_⟩
    · have := hTg Z
      rw [h1] at this
      exact_mod_cast this.symm
    · rw [← hTa]
      exact h2
  have hTm₀ : T.m Z₀ = 1 := by rw [hTm, hm₀, Nat.cast_one]
  -- the reduced closed fibre `Y = (X_k)_red`
  have := isNoetherian_reduction_closedFibre g
  have : Finite (irreducibleComponents (closedFibre g).reduction) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let _ : Fintype (irreducibleComponents (closedFibre g).reduction) := Fintype.ofFinite _
  have hdim : ∀ y : (closedFibre g).reduction,
      ringKrullDim ((closedFibre g).reduction.presheaf.stalk y) ≤ 1 := fun y ↦
    (Scheme.ringKrullDim_stalk_reduction_le _ y).trans (hD R K C f X g hX.2.2.2 _)
  obtain ⟨hB1, hB2⟩ := hB (ResidueField R) (closedFibre g).reduction
    ((closedFibre g).reductionι ≫ closedFibreHom g) hdim ℓ hℓk
  have hG2' := hG2 R K C f X g hX ⟨x, hxc, hxreg⟩
  obtain ⟨hG1a, hG1b⟩ := hG1 R K C f X g hX hpt hmin
  have hP' := hP R K C f X g hX ℓ hℓk
    ⟨Z₀, by rw [hm₀]; exact (Fact.out : ℓ.Prime).not_dvd_one⟩
  -- the bound on `Pic(T)[ℓ]`
  let _ : LinearOrder (irreducibleComponents (closedFibre g)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have : Nonempty (irreducibleComponents (closedFibre g)) := ⟨Z₀⟩
  have hTg1 : 1 ≤ T.genus := by rw [hTgenus]; exact_mod_cast hgenus
  have hbound : Nat.card (Submodule.torsionBy ℤ T.Pic (ℓ : ℤ)) ≤ ℓ ^ T.topGenus.toNat := by
    rcases (show T.genus = 1 ∨ 2 ≤ T.genus by omega) with h1 | h2
    · rcases Nat.lt_or_ge 1 (Fintype.card (irreducibleComponents (closedFibre g))) with hn | hn
      · refine NumericalType.card_torsionBy_pic_le_of_genus_eq_one hTmin hn h1 hTm₀ ℓ ?_
        have : (1 : ℤ) ≤ f.genus := by exact_mod_cast hgenus
        have : ((2 ^ 10 * (3 * f.genus) : ℕ) : ℤ) < ℓ := by exact_mod_cast hℓ
        push_cast at this
        omega
      · exact (NumericalType.card_torsionBy_pic_le_one_of_card_eq_one (T := T)
          (le_antisymm hn Fintype.card_pos) ℓ).trans
          (Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos)
    · refine NumericalType.card_torsionBy_pic_le_of_isMinimal hTmin h2 ℓ ?_
      have : ((2 ^ 10 * (3 * f.genus) : ℕ) : ℤ) < ℓ := by exact_mod_cast hℓ
      push_cast at this
      rw [hTgenus]
      omega
  have hcT : Nat.card (Submodule.torsionBy ℤ ((irreducibleComponents (closedFibre g) → ℤ) ⧸
      LinearMap.range (Scheme.intersectionMatrix (closedFibreHom g)).mulVecLin) (ℓ : ℤ)) ≤
        ℓ ^ T.topGenus.toNat := by
    rw [← hTa]
    exact hbound
  have htop : (Scheme.intersectionMatrix (closedFibreHom g)).topGenus = T.topGenus := by
    rw [← hTa, T.topGenus_eq_matrix_topGenus]
  have htop0 := T.topGenus_nonneg
  -- `|Pic(C)[ℓ]| = ℓ^{2g}`
  have hcC : Nat.card (powMonoidHom ℓ : C.Pic →* C.Pic).ker = ℓ ^ (2 * f.genus) := by
    rw [Nat.card_congr hpic.some.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- the numerical argument
  set t := T.topGenus.toNat with ht
  set h := ((closedFibre g).reductionι ≫ closedFibreHom g).genus with hh
  set γ := Scheme.geometricGenus ((closedFibre g).reductionι ≫ closedFibreHom g) with hγ
  set cY := Nat.card (powMonoidHom ℓ : (closedFibre g).reduction.Pic →*
    (closedFibre g).reduction.Pic).ker with hcY
  have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hG2'' : t + γ ≤ h := by
    rw [htop] at hG2'
    omega
  have hchain : ℓ ^ (2 * f.genus) ≤ ℓ ^ t * cY := by
    rw [← hcC]
    exact hP'.trans (Nat.mul_le_mul_right _ hcT)
  have hle : 2 * f.genus ≤ t + (h + γ) := by
    have := hchain.trans (Nat.mul_le_mul_left _ hB1)
    rw [← pow_add] at this
    exact (Nat.pow_le_pow_iff_right hℓ2).mp this
  have hhg : h = f.genus := by omega
  have hm : ∀ Z : irreducibleComponents (closedFibre g), Scheme.componentMultiplicity Z = 1 := by
    by_contra hcon
    push Not at hcon
    have := hG1b hcon
    omega
  have hcY : cY = ℓ ^ (h + γ) := by
    refine le_antisymm hB1 ?_
    have h2g : 2 * f.genus = t + (h + γ) := by omega
    rw [h2g, pow_add] at hchain
    exact Nat.le_of_mul_le_mul_left hchain (pow_pos (by omega) _)
  exact ⟨X, g, hX, hL R K C f X g hX hm (hB2.mp hcY)⟩

end MainStep

section Assembly

/-- A prime `ℓ > N` invertible in a field `k`. -/
private lemma exists_prime_gt_ne_zero (k : Type*) [Field k] (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ (ℓ : k) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (max N (ringChar k) + 1)
  refine ⟨ℓ, hℓ, by omega, fun h0 ↦ ?_⟩
  have hdvd : ringChar k ∣ ℓ := (CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp h0
  rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

-- Instance search for `IsStableUnderBaseChangeAlong` from the local
-- `IsStableUnderBaseChange (@SmoothOfRelativeDimension 1)` fails under the default transparency
-- setting (as in `SGA1/ExposeXIII/SemistableReductionGood.lean`).
set_option backward.isDefEq.respectTransparency.types false in
/-- **The semistable reduction theorem from its geometric inputs** (conditional; Stacks, Theorem
0CDN for complete `R` with algebraically closed residue field, following Sections 0CDK, 0CEG and
0CEI): `SemistableReductionStatement` follows from the interface statements listed in the module
docstring. -/
theorem semistableReductionStatement_of_inputs
    (hV : TorsionBecomesVisibleStatement.{u}) (hGB : GenusBaseChangeStatement.{u})
    (h0 : GenusZeroSmoothModelStatement.{u}) (hB : PicTorsionReducedCurveStatement.{u})
    (hM : MinimalModelStatement.{u}) (hN : NumericalTypeOfModelStatement.{u})
    (hP : PicTorsionModelStatement.{u})
    (hG1 : GenusReducedFibreUpperStatement.{u}) (hG2 : GenusReducedFibreLowerStatement.{u})
    (hD : ClosedFibreDimensionStatement.{u}) (hL : SemistableOfMulticrossStatement.{u}) :
    SemistableReductionStatement.{u} := by
  rw [semistableReductionStatement_iff]
  intro R _ _ _ _ _ K _ _ _ C f _ _ _
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  -- the extensions `K'/K` used below and the normalization of `R` in them
  suffices H : ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'), ∀ [Algebra R K'] [IsScalarTower R K K']
      [IsDiscreteValuationRing (integralClosure R K')] [IsFractionRing (integralClosure R K') K']
      [IsAlgClosed (ResidueField (integralClosure R K'))],
      ∃ (𝒳 : Scheme.{u}) (g : 𝒳 ⟶ Spec (.of (integralClosure R K'))), IsProper g ∧ Flat g ∧
        (∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K'))) ≅
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
          e.hom ≫ pullback.snd _ _ = pullback.snd _ _) ∧
        IsSemistableCurve (ResidueField (integralClosure R K')) (closedFibre g) by
    obtain ⟨K', _, _, _, _, H⟩ := H
    let _ : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
    have : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have := ExposeX.isDiscreteValuationRing_integralClosure R K K'
    have : IsFractionRing (integralClosure R K') K' :=
      integralClosure.isFractionRing_of_finite_extension K K'
    have := isAlgClosed_residueField_integralClosure R K K'
    have := integralClosure.finite R K K'
    have : FaithfulSMul R (integralClosure R K') :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr
        (integralClosure.algebraMap_injective_of_isFractionRing R K K')
    obtain ⟨𝒳, g, hg, hfl, he, hs⟩ := H
    exact ⟨integralClosure R K', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, K', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, 𝒳, g, hg, hfl, he, hs⟩
  by_cases hg0 : f.genus = 0
  · -- genus `0`: a smooth model after a finite separable extension
    obtain ⟨K', _, _, _, _, hmodel⟩ := h0 K C f hg0
    refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro _ _ _ _ _
    obtain ⟨𝒳, g, hg, hgs, e, he⟩ := hmodel (integralClosure R K')
    have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
    have hsm : SmoothOfRelativeDimension 1 (closedFibreHom g) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ hgs
    exact ⟨𝒳, g, hg, inferInstance, ⟨e, he⟩, isSemistableCurve_of_smooth (closedFibreHom g)⟩
  -- genus `g ≥ 1`: choose `ℓ`, make the `ℓ`-torsion of `Pic` rational, and take a minimal model
  have hgenus : 1 ≤ f.genus := Nat.one_le_iff_ne_zero.mpr hg0
  obtain ⟨ℓ, hℓp, hℓ, hℓk⟩ := exists_prime_gt_ne_zero (ResidueField R) (2 ^ 10 * (3 * f.genus))
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓR : IsUnit (ℓ : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact hℓk
  have hℓK : (ℓ : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K)]
    exact (hℓR.map (algebraMap R K)).ne_zero
  obtain ⟨K', _, _, _, _, hpt, hpic⟩ := hV K C f hgenus ℓ hℓK
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro _ _ _ _ _
  -- the curve `C' = C ⊗_K K'` over `K'`
  have hsm' : SmoothOfRelativeDimension 1
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hgen := hGB K C f K'
  have hℓk' : (ℓ : ResidueField (integralClosure R K')) ≠ 0 := by
    rw [← map_natCast (IsLocalRing.residue (integralClosure R K')),
      IsLocalRing.residue_ne_zero_iff_isUnit, ← map_natCast (algebraMap R (integralClosure R K'))]
    exact hℓR.map _
  obtain ⟨X, g, hX, hs⟩ := exists_semistable_model_of_picTorsion hM hN hP hG1 hG2 hD hB hL
    (integralClosure R K') K' _ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (by rw [hgen]; exact hgenus) hpt ℓ hℓk' (by rw [hgen]; exact hℓ) (by rw [hgen]; exact hpic)
  obtain ⟨hgp, hgf, -, e, he⟩ := hX
  exact ⟨X, g, hgp, hgf, ⟨e, he⟩, hs⟩

end Assembly

end SGA.SGA1.ExposeXIII
