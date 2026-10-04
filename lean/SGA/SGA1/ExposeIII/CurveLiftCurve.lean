/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftBase
import SGA.SGA1.ExposeX.CurveFinitePlaneModel
import SGA.SGA1.ExposeX.ConstantFamily
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeXIII.DesingularizationCurvesStrong
import SGA.SGA1.ExposeXI.UnirationalCurves
import SGA.Foundations.Desingularization

/-!
# Smooth proper curves over a field are finite and flat over `ℙ¹`

This file proves `AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement`
(`smoothProperCurveFiniteFlatStatement`): a smooth proper curve `X` over a field `k` has a finite
flat `k`-morphism `X ⟶ ℙ¹_k` (Hartshorne II.6.8, III.9.7). With
`SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement` this
proves SGA 1 III.7.4 (`SGA.SGA1.ExposeIII.smoothProperCurveLiftStatement`).

The proof, for an integral `X` (`CurveLift.exists_finite_flat_of_isIntegral`):

* `X` has dimension `1` and its local rings are regular of dimension `≤ 1`, hence valuation rings
  (`CurveLift.valuationRing_stalk`);
* the function field `K(X)` contains an element `τ` transcendental over `k`
  (`CurveLift.exists_transcendental`: otherwise the sections over an affine open would be a field);
* `(1 : τ) : Spec K(X) ⟶ ℙ¹_k` extends to `g : X ⟶ ℙ¹_k` by the valuative criterion
  (`SGA.SGA1.ExposeX.CurvePlaneModel.exists_hom_of_valuationRing`);
* `g` maps the generic point to a non-closed point, so its fibres are finite (they consist of
  closed points, or of the generic point alone); being proper, `g` is finite by Zariski's main
  theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`);
* on the charts `D₊(xᵢ) ≅ Spec k[t]`, `Γ(D₊(xᵢ)) → Γ(g⁻¹ D₊(xᵢ))` is injective into a domain,
  hence flat (`k[t]` is a principal ideal domain).

A general `X` is the disjoint union of its connected components, which are integral; the morphisms
on the components glue (`smoothProperCurveFiniteFlatStatement`).

## References

* [Hartshorne, *Algebraic Geometry*, I.6.7, II.6.8, III.9.7]; [EGA II, 7.4]; [EGA III, 4.4.2].
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.AmpleLift MvPolynomial Topology

namespace SGA.SGA1.ExposeIII.CurveLift

section Dimension

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A scheme proper over a field is noetherian. -/
lemma isNoetherian_of_isProper [IsProper f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

/-- An integral curve smooth and proper over a field has dimension `≤ 1`. -/
lemma topologicalKrullDim_le_one [IsIntegral X] [SmoothOfRelativeDimension 1 f] [IsProper f] :
    topologicalKrullDim X ≤ 1 := by
  have := isNoetherian_of_isProper f
  have h := topologicalKrullDim_eq_of_mem_irreducibleComponents_of_smoothOfRelativeDimension
    (Field.toIsField k) f 1 (C := Set.univ) (by rw [irreducibleComponents_eq_singleton]; rfl)
  rw [← (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, h]
  rfl

/-- The local rings of an integral curve smooth and proper over a field are valuation rings. -/
lemma valuationRing_stalk [IsIntegral X] [SmoothOfRelativeDimension 1 f] [IsProper f] (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hn := ExposeX.isNormalScheme_of_isRegularScheme
    (fun y ↦ ExposeII.isRegularLocalRing_stalk_of_smooth_field k f y) x
  have : IsDomain (X.presheaf.stalk x) := hn.1
  have : IsIntegrallyClosed (X.presheaf.stalk x) := hn.2
  have := IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one
    ((ExposeX.ringKrullDim_stalk_le_topologicalKrullDim x).trans (topologicalKrullDim_le_one f))
  infer_instance

/-- The structure homomorphism `k → Γ(X, U)`. -/
noncomputable abbrev sectionsMap (U : X.Opens) : k →+* Γ(X, U) :=
  (f.appLE ⊤ U (le_top.trans_eq f.preimage_top.symm)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- On an integral curve smooth over a field, the sections over a nonempty affine open contain an
element transcendental over `k`: otherwise they would form a field and the open subset would be a
point, of dimension `0`. -/
lemma exists_transcendental_section [IsIntegral X] [SmoothOfRelativeDimension 1 f] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    ∃ r : Γ(X, U), letI := (sectionsMap f U).toAlgebra; Transcendental k r := by
  let := (sectionsMap f U).toAlgebra
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  by_contra! h
  have : Algebra.IsAlgebraic k Γ(X, U) := ⟨fun r ↦ by simpa [Transcendental] using h r⟩
  have : Algebra.IsIntegral k Γ(X, U) := inferInstance
  have hfield : IsField Γ(X, U) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k Γ(X, U)).injective).mp
      (Field.toIsField k)
  have h1 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (Field.toIsField k) f 1 x
  rw [hU.topologicalKrullDimAt_eq hx] at h1
  have h2 := topologicalKrullDimAt_le_topologicalKrullDim (hU.primeIdealOf ⟨x, hx⟩)
  rw [h1, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField hfield]
    at h2
  exact absurd h2 (by decide)

/-- **The function field of an integral curve smooth over a field is not algebraic**: it contains
an element transcendental over `k` (for the `k`-algebra structure `ExposeXI.functionFieldMap f`). -/
theorem exists_transcendental [IsIntegral X] [SmoothOfRelativeDimension 1 f] :
    ∃ τ : X.functionField,
      letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  obtain ⟨r, hr⟩ := exists_transcendental_section f hU hηU
  let := (sectionsMap f U).toAlgebra
  let := (ExposeXI.functionFieldMap f).toAlgebra
  let germ : Γ(X, U) →ₐ[k] X.functionField :=
    { (X.presheaf.germ U (genericPoint X) hηU).hom with
      commutes' := fun a ↦ by
        change (X.presheaf.germ U (genericPoint X) hηU).hom
          ((X.presheaf.map (homOfLE le_top).op).hom (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))
            = _
        rw [← CommRingCat.comp_apply, X.presheaf.germ_res]
        rfl }
  refine ⟨germ r, ?_⟩
  rw [Transcendental, isAlgebraic_algHom_iff germ (germ_injective_of_isIntegral X _ hηU)]
  exact hr

end Dimension

section Algebra

/-- For `τ` transcendental over a field `k`, `k[t] → A`, `t ↦ τ`, is injective (one variable,
indexed by a type with one element). -/
lemma injective_eval₂Hom_of_transcendental {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
    [Unique ι] {τ : A} (h : Transcendental k τ) :
    Function.Injective (eval₂Hom (algebraMap k A) (fun _ : ι ↦ τ)) := by
  have he : eval₂Hom (algebraMap k A) (fun _ : ι ↦ τ) =
      (Polynomial.aeval τ).toRingHom.comp
        (MvPolynomial.uniqueAlgEquiv k ι).toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp
    · simp
  rw [he]
  exact (transcendental_iff_injective.mp h).comp (MvPolynomial.uniqueAlgEquiv k ι).injective

/-- A polynomial ring in one variable is not a field. -/
lemma not_isField_mvPolynomial {k ι : Type*} [Field k] [Unique ι] :
    ¬ IsField (MvPolynomial ι k) := fun h ↦
  Polynomial.not_isField k (MulEquiv.isField h (MvPolynomial.uniqueAlgEquiv k ι).symm.toMulEquiv)

end Algebra

section Morphism

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X]

/-- The chart data on `Spec K(X)` of the morphism `(1 : τ) : Spec K(X) ⟶ ℙ¹_k` for `τ ≠ 0`. -/
noncomputable def genericChartData (τ : X.functionField) (hτ : τ ≠ 0) :
    TwoChartData (Spec X.functionField) k where
  c := (Scheme.ΓSpecIso X.functionField).inv.hom.comp (ExposeXI.functionFieldMap f)
  U₀ := ⊤
  U₁ := ⊤
  sup_eq_top := sup_idem _
  τ := (Scheme.ΓSpecIso X.functionField).inv τ
  σ := (Scheme.ΓSpecIso X.functionField).inv τ⁻¹
  mul_eq_one := by
    rw [show (homOfLE inf_le_right : (⊤ : (Spec X.functionField).Opens) ⊓ ⊤ ⟶ ⊤) =
      homOfLE inf_le_left from Subsingleton.elim _ _, ← map_mul, ← map_mul,
      mul_inv_cancel₀ hτ, map_one, map_one]
  basicOpen_τ_le := le_top
  basicOpen_σ_le := le_top

variable {f}

lemma genericChartData_toProj_projToSpec (τ : X.functionField) (hτ : τ ≠ 0) :
    (genericChartData f τ hτ).toProj ≫ projToSpec Two.{u} k =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [TwoChartData.toProj_projToSpec, ExposeXI.fromSpecStalk_comp_eq_SpecMap]
  change _ ≫ Spec.map (CommRingCat.ofHom (ExposeXI.functionFieldMap f) ≫
    (Scheme.ΓSpecIso X.functionField).inv) = _
  rw [Spec.map_comp, ← Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- The ring homomorphism `k[t] ≅ k[x₀, x₁]_(x₀) → K(X)` of `genericChartData` on `D₊(x₀)` is
injective for transcendental `τ`. -/
lemma injective_genericChartHom_zero (τ : X.functionField) (hτ : τ ≠ 0)
    (htr : letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ) :
    Function.Injective ((eval₂Hom (genericChartData f τ hτ).c₀
      (fun _ ↦ (genericChartData f τ hτ).τ)).comp
        (awayEquiv (t := (MvPolynomial.X Two.zero : MvPolynomial Two.{u} k)) Two.zero
          rfl).toRingHom) := by
  let D := genericChartData f τ hτ
  let := (ExposeXI.functionFieldMap f).toAlgebra
  let := uniqueNeZero.{u}
  have hc (p : MvPolynomial {j : Two.{u} // j ≠ Two.zero} k) :
      eval₂Hom D.c₀ (fun _ ↦ D.τ) p = (Scheme.ΓSpecIso X.functionField).inv
        (eval₂Hom (algebraMap k X.functionField) (fun _ ↦ τ) p) := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂Hom_C, eval₂Hom_C]
      change (Spec X.functionField).presheaf.map (homOfLE le_top : (⊤ : (Spec _).Opens) ⟶ ⊤).op
        (D.c a) = _
      rw [show (homOfLE le_top : (⊤ : (Spec X.functionField).Opens) ⟶ ⊤) = 𝟙 _ from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
      rfl
    | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add]
      rfl
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, eval₂Hom_X', eval₂Hom_X', map_mul]
      rfl
  have hinj1 : Function.Injective (eval₂Hom D.c₀ (fun _ ↦ D.τ)) := fun p q hpq ↦ by
    rw [hc, hc] at hpq
    exact injective_eval₂Hom_of_transcendental htr
      ((Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.symm.injective hpq)
  exact hinj1.comp (RingEquiv.injective _)

/-- `Γ(D₊(x₀)) → Γ(Spec K(X))` of `genericChartData` is injective for transcendental `τ`. -/
lemma injective_genericChartData_zero (τ : X.functionField) (hτ : τ ≠ 0)
    (htr : letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ) :
    Function.Injective ((genericChartData f τ hτ).toProj.appLE (lineChart₀ k) ⊤
      (genericChartData f τ hτ).toProj_preimage_basicOpen_zero.ge) := by
  have hinj := injective_genericChartHom_zero τ hτ htr
  rw [← CommRingCat.hom_ofHom ((eval₂Hom _ _).comp _),
    ← (genericChartData f τ hτ).awayToSection_comp_appLE_zero] at hinj
  intro a b hab
  obtain ⟨a', rfl⟩ := (bijective_awayToSection k (X_mem_grading Two.zero)).2 a
  obtain ⟨b', rfl⟩ := (bijective_awayToSection k (X_mem_grading Two.zero)).2 b
  exact congrArg _ (hinj hab)

/-- The ring homomorphism `k[t] ≅ k[x₀, x₁]_(x₁) → K(X)` of `genericChartData` on `D₊(x₁)` is
injective for transcendental `τ`. -/
lemma injective_genericChartHom_one (τ : X.functionField) (hτ : τ ≠ 0)
    (htr : letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ) :
    Function.Injective ((eval₂Hom (genericChartData f τ hτ).c₁
      (fun _ ↦ (genericChartData f τ hτ).σ)).comp
        (awayEquiv (t := (MvPolynomial.X Two.one : MvPolynomial Two.{u} k)) Two.one
          rfl).toRingHom) := by
  let D := genericChartData f τ hτ
  let := (ExposeXI.functionFieldMap f).toAlgebra
  let := uniqueNeOne.{u}
  have htr' : Transcendental k τ⁻¹ := by
    rw [Transcendental, IsAlgebraic.inv_iff]
    exact htr
  have hc (p : MvPolynomial {j : Two.{u} // j ≠ Two.one} k) :
      eval₂Hom D.c₁ (fun _ ↦ D.σ) p = (Scheme.ΓSpecIso X.functionField).inv
        (eval₂Hom (algebraMap k X.functionField) (fun _ ↦ τ⁻¹) p) := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂Hom_C, eval₂Hom_C]
      change (Spec X.functionField).presheaf.map (homOfLE le_top : (⊤ : (Spec _).Opens) ⟶ ⊤).op
        (D.c a) = _
      rw [show (homOfLE le_top : (⊤ : (Spec X.functionField).Opens) ⟶ ⊤) = 𝟙 _ from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
      rfl
    | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add]
      rfl
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, eval₂Hom_X', eval₂Hom_X', map_mul]
      rfl
  have hinj1 : Function.Injective (eval₂Hom D.c₁ (fun _ ↦ D.σ)) := fun p q hpq ↦ by
    rw [hc, hc] at hpq
    exact injective_eval₂Hom_of_transcendental htr'
      ((Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.symm.injective hpq)
  exact hinj1.comp (RingEquiv.injective _)

/-- `Γ(D₊(x₁)) → Γ(Spec K(X))` of `genericChartData` is injective for transcendental `τ`. -/
lemma injective_genericChartData_one (τ : X.functionField) (hτ : τ ≠ 0)
    (htr : letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ) :
    Function.Injective ((genericChartData f τ hτ).toProj.appLE (lineChart₁ k) ⊤
      (genericChartData f τ hτ).toProj_preimage_basicOpen_one.ge) := by
  have hinj := injective_genericChartHom_one τ hτ htr
  rw [← CommRingCat.hom_ofHom ((eval₂Hom _ _).comp _),
    ← (genericChartData f τ hτ).awayToSection_comp_appLE_one] at hinj
  intro a b hab
  obtain ⟨a', rfl⟩ := (bijective_awayToSection k (X_mem_grading Two.one)).2 a
  obtain ⟨b', rfl⟩ := (bijective_awayToSection k (X_mem_grading Two.one)).2 b
  exact congrArg _ (hinj hab)

lemma genericChartData_toProj_mem (τ : X.functionField) (hτ : τ ≠ 0) (pt : Spec X.functionField) :
    (genericChartData f τ hτ).toProj pt ∈ lineChart₀ k ∧
      (genericChartData f τ hτ).toProj pt ∈ lineChart₁ k := by
  constructor
  · have : pt ∈ (genericChartData f τ hτ).toProj ⁻¹ᵁ lineChart₀ k := by
      rw [TwoChartData.toProj_preimage_basicOpen_zero]
      trivial
    exact this
  · have : pt ∈ (genericChartData f τ hτ).toProj ⁻¹ᵁ lineChart₁ k := by
      rw [TwoChartData.toProj_preimage_basicOpen_one]
      trivial
    exact this

/-- **`(1 : τ)` is not constant**: for transcendental `τ`, the point of `Spec K(X)` is mapped to a
non-closed point of `ℙ¹_k` (the generic point of `D₊(x₀) ≅ Spec k[t]`). -/
lemma not_isClosed_genericChartData_toProj (τ : X.functionField) (hτ : τ ≠ 0)
    (htr : letI := (ExposeXI.functionFieldMap f).toAlgebra; Transcendental k τ)
    (pt : Spec X.functionField) :
    ¬ IsClosed {(genericChartData f τ hτ).toProj pt} := by
  intro hcl
  let D := genericChartData f τ hτ
  let ψ := (eval₂Hom D.c₀ (fun _ ↦ D.τ)).comp
    (awayEquiv (t := (MvPolynomial.X Two.zero : MvPolynomial Two.{u} k)) Two.zero rfl).toRingHom
  have hpt : D.toProj pt = Proj.awayι (grading Two.{u} k) (MvPolynomial.X Two.zero)
      (X_mem_grading Two.zero) one_pos
        (Spec.map (CommRingCat.ofHom ψ) (D.U₀.toSpecΓ ⟨pt, trivial⟩)) := by
    have := congrArg (fun φ ↦ φ ⟨pt, trivial⟩) D.ι_toProj_zero
    exact this
  have hfield : IsField Γ(Spec X.functionField, D.U₀) :=
    MulEquiv.isField (Field.toIsField X.functionField)
      (Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.toMulEquiv
  set q := D.U₀.toSpecΓ ⟨pt, trivial⟩
  have hq : q.asIdeal = ⊥ := by
    let := hfield.toField
    exact (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.2.ne_top
  have hp₀ : (Spec.map (CommRingCat.ofHom ψ) q).asIdeal = ⊥ := by
    change Ideal.comap ψ q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot ψ).mp (injective_genericChartHom_zero τ hτ htr)
  change IsClosed {D.toProj pt} at hcl
  rw [hpt] at hcl
  have hcl' := hcl.preimage (Proj.awayι (grading Two.{u} k) (MvPolynomial.X Two.zero)
    (X_mem_grading Two.zero) one_pos).continuous
  rw [← Set.image_singleton, (Proj.awayι (grading Two.{u} k) (MvPolynomial.X Two.zero)
    (X_mem_grading Two.zero) one_pos).isOpenEmbedding.injective.preimage_image] at hcl'
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcl'
  rw [hp₀] at hmax
  let := uniqueNeZero.{u}
  have : Nontrivial (HomogeneousLocalization.Away (grading Two.{u} k)
      (MvPolynomial.X Two.zero)) :=
    (awayEquiv (t := (MvPolynomial.X Two.zero : MvPolynomial Two.{u} k)) Two.zero
      rfl).toEquiv.nontrivial
  exact not_isField_mvPolynomial (MulEquiv.isField (Ring.isField_iff_maximal_bot.mpr hmax)
    (awayEquiv (t := (MvPolynomial.X Two.zero : MvPolynomial Two.{u} k)) Two.zero
      rfl).symm.toMulEquiv)

end Morphism

section Integral

/-- If `a ≫ g = φ` and `φ^*` is injective on sections, so is `g^*`. -/
lemma injective_app_of_comp_eq {T X Y : Scheme.{u}} (a : T ⟶ X) (g : X ⟶ Y) (φ : T ⟶ Y)
    (h : a ≫ g = φ) (U : Y.Opens) (V : T.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hinj : Function.Injective (φ.appLE U V e)) : Function.Injective (g.app U) := by
  subst h
  rw [Scheme.Hom.comp_appLE] at hinj
  intro x y hxy
  apply hinj
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hxy]

/-- A ring homomorphism to a domain is flat if its composite with a bijection from a Dedekind
domain is injective. -/
lemma flat_of_injective_comp_bijective {P A B : Type*} [CommRing P] [CommRing A] [CommRing B]
    [IsDedekindDomain P] [IsDomain B] (E : P →+* A) (hE : Function.Bijective E) (φ : A →+* B)
    (hφ : Function.Injective (φ.comp E)) : φ.Flat := by
  have h := flat_of_injective_of_isDedekindDomain (φ.comp E) hφ
  have he : φ = (φ.comp E).comp (RingEquiv.ofBijective E hE).symm.toRingHom := by
    ext y
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [← RingEquiv.ofBijective_apply E hE, RingEquiv.apply_symm_apply]
  rw [he]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (RingEquiv.bijective _)) h

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The fibres of a non-constant morphism from a curve are finite**: let `X` be an integral
noetherian scheme of dimension `≤ 1` and `g : X ⟶ Y` universally closed, mapping the generic point
to a non-closed point. Then the fibres of `g` are finite. -/
lemma finite_preimage_singleton_of_not_isClosed [IsIntegral X] [TopologicalSpace.NoetherianSpace X]
    {Y : Scheme.{u}} (g : X ⟶ Y) [UniversallyClosed g] (hX : topologicalKrullDim X ≤ 1)
    (hη : ¬ IsClosed {g (genericPoint X)}) (y : Y) : (g ⁻¹' {y}).Finite := by
  have hcl (x : X) (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) :=
    ExposeXIII.isClosed_singleton_of_ne_genericPoint hX hx
  have himg (x : X) (hx : x ≠ genericPoint X) : IsClosed ({g x} : Set Y) := by
    have := g.isClosedMap _ (hcl x hx)
    rwa [Set.image_singleton] at this
  by_cases hy : g (genericPoint X) = y
  · refine (Set.finite_singleton (genericPoint X)).subset fun x hx ↦ ?_
    by_contra hne
    have := himg x hne
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [hx, ← hy] at this
    exact hη this
  · by_cases hne : (g ⁻¹' {y}).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx₀
      have hx₀η : x₀ ≠ genericPoint X := fun h ↦ hy (h ▸ hx₀)
      have hycl : IsClosed ({y} : Set Y) := by
        have := himg x₀ hx₀η
        rwa [hx₀] at this
      refine TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton
        (hycl.preimage g.continuous) fun x hx ↦ hcl x ?_
      rintro rfl
      exact hy hx
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty

set_option backward.isDefEq.respectTransparency.types false in
/-- **An integral smooth proper curve over a field is finite and flat over `ℙ¹`** (Hartshorne
II.6.8, III.9.7): there is a finite flat `k`-morphism `g : X ⟶ ℙ¹_k`. -/
theorem exists_finite_flat_of_isIntegral [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    [IsProper f] :
    ∃ g : X ⟶ Proj (grading Two.{u} k), IsFinite g ∧ Flat g ∧ g ≫ projToSpec Two.{u} k = f := by
  have := isNoetherian_of_isProper f
  have : IsProper (projToSpec Two.{u} k) := isProper_projToSpec Two.{u} k
  obtain ⟨τ, htr⟩ := exists_transcendental f
  have hτ : τ ≠ 0 := by
    rintro rfl
    let := (ExposeXI.functionFieldMap f).toAlgebra
    exact htr isAlgebraic_zero
  obtain ⟨g, hgη, hgf⟩ := ExposeX.CurvePlaneModel.exists_hom_of_valuationRing f
    (projToSpec Two.{u} k) (valuationRing_stalk f) (genericChartData f τ hτ).toProj
    (genericChartData_toProj_projToSpec τ hτ)
  have hgpt : g (genericPoint X) =
      (genericChartData f τ hτ).toProj (IsLocalRing.closedPoint X.functionField) := by
    have h1 := congrArg (fun φ : Spec X.functionField ⟶ _ ↦
      φ (IsLocalRing.closedPoint X.functionField)) hgη
    refine Eq.trans ?_ h1
    exact (congrArg g (Scheme.fromSpecStalk_closedPoint (x := genericPoint X))).symm
  -- finiteness
  have : IsProper (g ≫ projToSpec Two.{u} k) := hgf ▸ inferInstance
  have : IsProper g := IsProper.of_comp g (projToSpec Two.{u} k)
  have : LocallyOfFiniteType (g ≫ projToSpec Two.{u} k) := hgf ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (projToSpec Two.{u} k)
  have : LocallyQuasiFinite g := LocallyQuasiFinite.of_finite_preimage_singleton g fun y ↦
    finite_preimage_singleton_of_not_isClosed g (topologicalKrullDim_le_one f)
      (by rw [hgpt]; exact not_isClosed_genericChartData_toProj τ hτ htr _) y
  have hfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  refine ⟨g, hfin, ?_, hgf⟩
  -- flatness, chart by chart
  have hmem := genericChartData_toProj_mem (f := f) τ hτ (IsLocalRing.closedPoint X.functionField)
  rw [← hgpt] at hmem
  have hinj₀ := injective_app_of_comp_eq _ g _ hgη _ _ _ (injective_genericChartData_zero τ hτ htr)
  have hinj₁ := injective_app_of_comp_eq _ g _ hgη _ _ _ (injective_genericChartData_one τ hτ htr)
  have hflat₀ : (g.app (lineChart₀ k)).hom.Flat := by
    have : Nonempty (g ⁻¹ᵁ lineChart₀ k) := ⟨⟨_, hmem.1⟩⟩
    let := uniqueNeZero.{u}
    have hE := (bijective_eval₂Hom_lineCoord₀ k).comp
      (MvPolynomial.uniqueAlgEquiv k {j : Two.{u} // j ≠ Two.zero}).symm.bijective
    exact flat_of_injective_comp_bijective
      ((eval₂Hom (lineC k (lineChart₀ k)) (fun _ ↦ lineCoord₀ k)).comp
        (MvPolynomial.uniqueAlgEquiv k {j : Two.{u} // j ≠ Two.zero}).symm.toRingEquiv.toRingHom)
      hE _ (hinj₀.comp hE.1)
  have hflat₁ : (g.app (lineChart₁ k)).hom.Flat := by
    have : Nonempty (g ⁻¹ᵁ lineChart₁ k) := ⟨⟨_, hmem.2⟩⟩
    let := uniqueNeOne.{u}
    have hE := (bijective_eval₂Hom_lineCoord₁ k).comp
      (MvPolynomial.uniqueAlgEquiv k {j : Two.{u} // j ≠ Two.one}).symm.bijective
    exact flat_of_injective_comp_bijective
      ((eval₂Hom (lineC k (lineChart₁ k)) (fun _ ↦ lineCoord₁ k)).comp
        (MvPolynomial.uniqueAlgEquiv k {j : Two.{u} // j ≠ Two.one}).symm.toRingEquiv.toRingHom)
      hE _ (hinj₁.comp hE.1)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : Two.{u} ↦ Proj.basicOpen (grading Two.{u} k) (MvPolynomial.X i))
    (iSup_basicOpen_X Two.{u} k) fun ⟨i⟩ ↦ ?_
  fin_cases i
  · refine flat_morphismRestrict_of_appLE g isAffineOpen_lineChart₀ rfl
      (isAffineOpen_lineChart₀.preimage g) ?_
    rw [Scheme.Hom.appLE_eq_app]
    exact hflat₀
  · refine flat_morphismRestrict_of_appLE g isAffineOpen_lineChart₁ rfl
      (isAffineOpen_lineChart₁.preimage g) ?_
    rw [Scheme.Hom.appLE_eq_app]
    exact hflat₁

end Integral

section Glue

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

set_option backward.isDefEq.respectTransparency.types false in
/-- **A smooth proper curve over a field is finite and flat over `ℙ¹`** (Hartshorne II.6.8,
III.9.7): for `f : X ⟶ Spec k` smooth of relative dimension `1` and proper, there is a finite flat
`g : X ⟶ ℙ¹_k` over `k`. `X` need not be connected: the morphisms on the connected components
(`exists_finite_flat_of_isIntegral`) glue. -/
theorem exists_finite_flat [SmoothOfRelativeDimension 1 f] [IsProper f] :
    ∃ g : X ⟶ Proj (grading Two.{u} k), IsFinite g ∧ Flat g ∧ g ≫ projToSpec Two.{u} k = f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyConnectedSpace X := ExposeX.locallyConnectedSpace_of_isLocallyNoetherian X
  let U := ExposeX.componentOpens X
  have hcomp (c : _root_.ConnectedComponents X) : ∃ g : (U c).toScheme ⟶ Proj (grading Two.{u} k),
      IsFinite g ∧ Flat g ∧ g ≫ projToSpec Two.{u} k = (U c).ι ≫ f := by
    have : SmoothOfRelativeDimension 1 ((U c).ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
    have : Smooth ((U c).ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
    have : IsProper ((U c).ι ≫ f) := inferInstance
    obtain ⟨_, -⟩ := ExposeX.isIntegral_and_isNormalScheme_of_smooth k ((U c).ι ≫ f)
    exact exists_finite_flat_of_isIntegral _
  choose g hgfin hgfl hgf using hcomp
  let 𝒰 := X.openCoverOfIsOpenCover U (ExposeX.iSup_componentOpens X)
  have hcompat : ∀ c d : _root_.ConnectedComponents X, pullback.fst (𝒰.f c) (𝒰.f d) ≫ g c =
      pullback.snd (𝒰.f c) (𝒰.f d) ≫ g d := by
    intro c d
    by_cases hcd : c = d
    · subst hcd
      rw [(cancel_mono (𝒰.f c)).1 pullback.condition]
    · have : IsEmpty ↥(pullback (𝒰.f c) (𝒰.f d) : Scheme.{u}) := by
        refine ⟨fun z ↦ ?_⟩
        have h1 : (pullback.fst (𝒰.f c) (𝒰.f d) ≫ 𝒰.f c) z ∈ U c :=
          ((pullback.fst (𝒰.f c) (𝒰.f d)) z).2
        have h2 : (pullback.snd (𝒰.f c) (𝒰.f d) ≫ 𝒰.f d) z ∈ U d :=
          ((pullback.snd (𝒰.f c) (𝒰.f d)) z).2
        rw [← pullback.condition] at h2
        have := (ExposeX.pairwise_disjoint_componentOpens X hcd).le_bot ⟨h1, h2⟩
        exact this
      exact isInitialOfIsEmpty.hom_ext _ _
  let G := 𝒰.glueMorphisms g hcompat
  have hG (c : _root_.ConnectedComponents X) : (U c).ι ≫ G = g c :=
    𝒰.ι_glueMorphisms g hcompat c
  have hGf : G ≫ projToSpec Two.{u} k = f := by
    refine 𝒰.hom_ext _ _ fun c ↦ ?_
    change (U c).ι ≫ G ≫ projToSpec Two.{u} k = (U c).ι ≫ f
    rw [← Category.assoc, hG, hgf]
  have : Flat G := IsZariskiLocalAtSource.of_iSup_eq_top U (ExposeX.iSup_componentOpens X)
    fun c ↦ by rw [hG]; exact hgfl c
  have : LocallyQuasiFinite G := IsZariskiLocalAtSource.of_iSup_eq_top U
    (ExposeX.iSup_componentOpens X) fun c ↦ by rw [hG]; have := hgfin c; infer_instance
  have : IsProper (G ≫ projToSpec Two.{u} k) := hGf ▸ inferInstance
  have : IsProper G := IsProper.of_comp G (projToSpec Two.{u} k)
  exact ⟨G, IsFinite.of_isProper_of_locallyQuasiFinite G, inferInstance, hGf⟩

end Glue

end SGA.SGA1.ExposeIII.CurveLift

namespace AlgebraicGeometry

/-- **A smooth proper curve over a field is finite and flat over `ℙ¹`**
(`SmoothProperCurveFiniteFlatStatement`; Hartshorne II.6.8, III.9.7). -/
theorem smoothProperCurveFiniteFlatStatement : SmoothProperCurveFiniteFlatStatement.{u} :=
  fun _ _ _ f _ _ ↦ SGA.SGA1.ExposeIII.CurveLift.exists_finite_flat f

end AlgebraicGeometry

namespace SGA.SGA1.ExposeIII

/-- **SGA 1 III.7.4**: let `A` be a complete noetherian local ring with residue field `κ` and
`X₀` a smooth proper curve over `κ` (smooth of relative dimension `1` and proper, not necessarily
connected). Then `X₀` is the closed fibre of a smooth proper curve over `A`: there are `X` and
`f : X ⟶ Spec A`, smooth of relative dimension `1` and proper, with `X ×_A κ ≅ X₀` over `κ`.
The proof goes through a finite flat morphism `X₀ ⟶ ℙ¹_κ`
(`AlgebraicGeometry.smoothProperCurveFiniteFlatStatement`) instead of an ample line bundle; see
`SGA.SGA1.ExposeIII.CurveLiftStage`. -/
theorem smoothProperCurveLiftStatement : SmoothProperCurveLiftStatement.{u} :=
  smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement
    AlgebraicGeometry.smoothProperCurveFiniteFlatStatement

end SGA.SGA1.ExposeIII
