/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeX.EtaleCoverings
import SGA.SGA1.ExposeX.GaloisFunctors
import SGA.SGA1.ExposeX.Specialization
import Mathlib.RingTheory.AdicCompletion.Basic
import SGA.Foundations.Formal.AdicRing
import SGA.Foundations.Formal.FiniteEtale
import SGA.Foundations.Formal.FiniteEtaleSpec
import SGA.SGA1.ExposeIX.EtaleMorphismDescent
import SGA.SGA1.ExposeIX.EtaleCoveringsClosedFibre
import SGA.SGA1.ExposeIX.GaloisFunctors

/-!
# SGA 1, Exposé X, §2: semicontinuity of the fundamental groups of the fibres

X.2.1 (`π₁(X₀) ≅ π₁(X)` for `X` proper over a complete noetherian local ring) is the
translation of IX.1.10, which rests on Grothendieck's existence theorem; X.2.9 (the fundamental
group of a proper connected scheme over an algebraically closed field is topologically finitely
generated) uses the transcendental theorem X.2.6 for curves. Both are recorded as statements,
and their formal consequences are proved:

* X.2.1 for `X` projective over `A` (closed in some `ℙ(τ; Spec A)`), from the existence theorem in
  the foundations: `isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion`,
  `bijective_map_of_isClosedImmersion`;
* X.2.1, full faithfulness and surjectivity of `π₁(X₀) → π₁(X)`, for every proper `X`:
  `full_pullback_closedFibreInclusion`, `faithful_pullback_closedFibreInclusion`,
  `surjective_autWhiskerLeft_of_completeLocal`;
* X.2.1 from IX.1.10: `bijective_autWhiskerLeft_of_completeLocal` (via V.6.10), and
  `bijective_map_of_completeLocal` for the fundamental groups of Exposé V;
* X.2.1 when `X` is finite over `Y`, i.e. `X = Spec B` with `B` a finite `A`-algebra: proved
  (`isEquivalence_pullback_spec_closedFibre`, `bijective_map_spec_closedFibre`), since `B` is
  complete for `𝔪_A B` and étale coverings of `Spf B` are those of `Spec (B ⊗_A k)`; the case
  `X = Y` is `bijective_map_spec_residueField_of_isAdicComplete` (in `Henselian`);
* X.2.2–X.2.4: the group theory is `exact_of_bijective` and `SpecializationDiagram` (in
  `Specialization`). X.2.2 over a complete local base is proved in
  `ExposeIX.ExactSequenceCompleteLocal` (IX.6.1 with the lifting of étale coverings from the closed
  fibre as hypothesis: unconditional for `X` projective, from IX.1.10 in general) and, for the
  fundamental groups of Exposé V at arbitrary geometric points, in `SpecializationGeometric`, with
  X.2.3 over a complete local base (`exists_continuous_surjective_specialization_of_completeLocal`);
  X.2.4 (`SpecializationSurjectiveStatement`) is proved in `SpecializationSurjective`, for `X`
  projective over `Y` unconditionally and for `X` proper from IX.1.10
  (`specializationSurjectiveStatement_of_etaleCoveringsOfClosedFibreStatement`);
* X.2.10 from X.2.11 is V.6.9 (`autWhiskerLeft_surjective_iff`);
* X.2.12 from X.2.9: `finite_setOf_continuous_monoidHom_of_statement`.

Not formalized: X.2.5–X.2.8 (examples; the transcendental computation X.2.6 of `π₁` of a curve,
which needs the comparison with the topological fundamental group), X.2.10–X.2.11 themselves
(Bertini's theorem, Zariski's connectedness theorem, projective space), X.2.13, X.2.14.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.PreGaloisCategory

namespace SGA.SGA1.ExposeX

/-- The closed fibre `X₀ = X ⊗_A k → X` of a scheme `X` over a local ring `A`. -/
noncomputable abbrev closedFibreInclusion (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))) ⟶ X :=
  pullback.fst _ _

/-- X.2.1, in the form IX.1.10 (statement only; Grothendieck's existence theorem). Let `A` be a
complete noetherian local ring, `X` proper over `Y = Spec A` and `X₀` the closed fibre. Then
`X' ↦ X' ×_X X₀` is an equivalence from the étale coverings of `X` to those of `X₀`; by V.6.10
this is the assertion that `π₁(X₀) → π₁(X)` is an isomorphism. -/
def CompleteLocalBaseStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of A))
    [IsProper f], (FEt.pullback (closedFibreInclusion A f)).IsEquivalence

/-- `CompleteLocalBaseStatement` is IX.1.10 as recorded in Exposé IX
(`ExposeIX.EtaleCoveringsOfClosedFibreStatement`). -/
theorem completeLocalBaseStatement_iff :
    CompleteLocalBaseStatement.{u} ↔ ExposeIX.EtaleCoveringsOfClosedFibreStatement.{u} :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- **X.2.1 for `X` projective over `A`** (IX.1.10, Grothendieck's existence theorem): let `A` be a
complete noetherian local ring and `X` a closed subscheme of `ℙ(τ; Spec A)`, `τ` finite, with
closed fibre `X₀`. Then `X' ↦ X' ×_X X₀` is an equivalence from the étale coverings of `X` to
those of `X₀`. -/
theorem isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec (.of A))) [IsClosedImmersion κ]
    (f : X ⟶ Spec (.of A)) (hf : f = κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A)) :
    (FEt.pullback (closedFibreInclusion A f)).IsEquivalence :=
  ExposeIX.isEquivalence_pullback_closedFibre_of_isClosedImmersion A κ f hf

/-- X.2.1 for `X` projective over `A`: for every geometric point `t` of the closed fibre `X₀`,
`π₁(X₀, t) → π₁(X, t)` is bijective. -/
theorem bijective_map_of_isClosedImmersion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec (.of A))) [IsClosedImmersion κ]
    (f : X ⟶ Spec (.of A)) (hf : f = κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A)) (Ω : Type u)
    [Field Ω] (t : Spec (.of Ω) ⟶ pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A (IsLocalRing.ResidueField A))))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω (closedFibreInclusion A f) t) :=
  have := isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion A κ f hf
  ExposeV.autMap_bijective _ _

set_option backward.isDefEq.respectTransparency false in
/-- X.2.1, full faithfulness, for every proper `X` over a complete noetherian local ring (the half
of IX.1.10 which does not use the existence theorem): base change to the closed fibre is fully
faithful on étale coverings. -/
theorem full_pullback_closedFibreInclusion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] : (FEt.pullback (closedFibreInclusion A f)).Full :=
  ExposeIX.full_pullback_closedFibre A f

set_option backward.isDefEq.respectTransparency false in
/-- X.2.1, faithfulness, for every proper `X` over a complete noetherian local ring. -/
theorem faithful_pullback_closedFibreInclusion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] : (FEt.pullback (closedFibreInclusion A f)).Faithful :=
  ExposeIX.faithful_pullback_closedFibre A f

/-- X.2.1 (from IX.1.10). For compatible fibre functors on the étale coverings of `X` and of its
closed fibre `X₀` (Exposé V), `π₁(X₀) → π₁(X)` is bijective. -/
theorem bijective_autWhiskerLeft_of_completeLocal (h : CompleteLocalBaseStatement.{u}) (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] {F : FEt X ⥤ FintypeCat.{u}} {F₀ : FEt (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A (IsLocalRing.ResidueField A))))) ⥤ FintypeCat.{u}}
    [FiberFunctor F] [FiberFunctor F₀] (e : FEt.pullback (closedFibreInclusion A f) ⋙ F₀ ≅ F) :
    Function.Bijective (autWhiskerLeft _ e) :=
  have := ExposeV.galoisCategory_of_fiberFunctor F
  have := ExposeV.galoisCategory_of_fiberFunctor F₀
  have := h A f
  autWhiskerLeft_bijective_of_isEquivalence _ e

/-- X.2.1, surjectivity, for every proper `X` over a complete noetherian local ring (from the full
faithfulness in IX.1.10, which does not use the existence theorem, and V.6.9): for compatible
fibre functors on the étale coverings of `X` and of its closed fibre `X₀`, `π₁(X₀) → π₁(X)` is
surjective. -/
theorem surjective_autWhiskerLeft_of_completeLocal (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] {F : FEt X ⥤ FintypeCat.{u}}
    {F₀ : FEt (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A (IsLocalRing.ResidueField A))))) ⥤ FintypeCat.{u}}
    [FiberFunctor F] [FiberFunctor F₀] (e : FEt.pullback (closedFibreInclusion A f) ⋙ F₀ ≅ F) :
    Function.Surjective (autWhiskerLeft _ e) := by
  have := ExposeV.galoisCategory_of_fiberFunctor F
  have := ExposeV.galoisCategory_of_fiberFunctor F₀
  have := full_pullback_closedFibreInclusion A f
  have : FiberFunctor (FEt.pullback (closedFibreInclusion A f) ⋙ F₀) :=
    ExposeV.fiberFunctor_of_natIso e.symm
  have := ExposeIX.preservesIsConnected_of_full (FEt.pullback (closedFibreInclusion A f)) F₀
  exact (autWhiskerLeft_surjective_iff _ e).mpr fun _ _ ↦ PreservesIsConnected.preserves

/-- X.2.1 (from IX.1.10), for the fundamental groups of Exposé V: for every geometric point `t` of
the closed fibre `X₀`, `π₁(X₀, t) → π₁(X, t)` is bijective (V.6.10; no connectedness is
needed). -/
theorem bijective_map_of_completeLocal (h : CompleteLocalBaseStatement.{u}) (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] (Ω : Type u) [Field Ω] (t : Spec (.of Ω) ⟶ pullback f (Spec.map
      (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω (closedFibreInclusion A f) t) :=
  have := h A f
  ExposeV.autMap_bijective _ _

open IsLocalRing TensorProduct in
/-- X.2.1 when `X` is finite over `Y`: let `A` be a complete noetherian local ring with residue
field `k` and `X = Spec B` for a finite `A`-algebra `B`, with closed fibre `X₀ = Spec (B ⊗_A k)`.
Then `X' ↦ X' ×_X X₀` is an equivalence from the étale coverings of `X` to those of `X₀`: `B` is
noetherian and complete for `𝔪_A B = Ker (B → B ⊗_A k)` (EGA 0_I 7.3.6), and over such a ring
reduction modulo the ideal is an equivalence on finite étale algebras (I.8.4, EGA IV 18.3.2). -/
theorem isEquivalence_pullback_spec_closedFibre (A B : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [CommRing B] [Algebra A B]
    [Module.Finite A B] :
    (FEt.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap B (B ⊗[A] ResidueField A))))).IsEquivalence := by
  have : IsNoetherianRing B := isNoetherianRing_iff.mpr (isNoetherian_of_tower A inferInstance)
  have hS : Function.Surjective (algebraMap B (B ⊗[A] ResidueField A)) :=
    Algebra.TensorProduct.includeLeft_surjective (S := B) (A := B) residue_surjective
  have hker : RingHom.ker (algebraMap B (B ⊗[A] ResidueField A)) =
      (maximalIdeal A).map (algebraMap A B) := by
    let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)
    ext b
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← e.map_eq_zero_iff]
    change b ⊗ₜ[A] (1 : A ⧸ maximalIdeal A) = 0 ↔ e (Ideal.Quotient.mk _ b) = 0
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  have : IsAdicComplete (RingHom.ker (algebraMap B (B ⊗[A] ResidueField A))) B := by
    rw [hker]
    exact (IsAdicComplete.map_algebraMap_iff ..).mpr (IsAdicComplete.of_finite _ B)
  have : (CommAlgCat.FiniteEtale.baseChange.{u} (CommRingCat.of B)
      (CommRingCat.of (B ⊗[A] ResidueField A))).IsEquivalence :=
    CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective hS
  exact Scheme.FiniteEtale.isEquivalence_pullback_spec (CommRingCat.of B)
    (CommRingCat.of (B ⊗[A] ResidueField A))

open IsLocalRing TensorProduct in
/-- X.2.1 when `X = Spec B` is finite over `Y = Spec A`, `A` complete noetherian local: for every
geometric point `t` of the closed fibre `X₀ = Spec (B ⊗_A k)`, `π₁(X₀, t) → π₁(X, t)` is
bijective. -/
theorem bijective_map_spec_closedFibre (A B : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (Ω : Type u) [Field Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of (B ⊗[A] ResidueField A))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω
      (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] ResidueField A)))) t) :=
  have := isEquivalence_pullback_spec_closedFibre A B
  ExposeV.autMap_bijective _ _

/-- X.2.4 (from X.2.1 and X.1.4; proved from IX.1.10 in `SpecializationSurjective`, and for `X`
projective over `Y` unconditionally). Let `f : X ⟶ Y` be proper and separable with
geometrically connected fibres, `Y` locally noetherian, `y₀` in the closure of `y₁`, `b₀`, `b₁`
geometric points of `Y` at `y₀`, `y₁` with algebraically closed values, and `ā₀`, `ā₁` geometric
points of the geometric fibres `X̄₀ = X ×_Y b₀`, `X̄₁ = X ×_Y b₁`. The specialization homomorphism
`π₁(X̄₁, ā₁) → π₁(X̄₀, ā₀)` (Exposé V), defined up to inner automorphism, is continuous and
surjective; we state that a continuous surjective homomorphism exists. -/
def SpecializationSurjectiveStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] [IsSeparable f] [GeometricallyConnected f]
    [IsLocallyNoetherian Y] (Ω₀ Ω₁ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁]
    [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Y) (b₁ : Spec (.of Ω₁) ⟶ Y),
    b₁ (IsLocalRing.closedPoint Ω₁) ⤳ b₀ (IsLocalRing.closedPoint Ω₀) →
    ∀ (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁),
      ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
        Continuous sp ∧ Function.Surjective sp

/-- X.2.9 (statement only). If `X` is proper and connected over an algebraically closed field,
its fundamental group is topologically finitely generated: for every geometric point `x` of `X`,
`π₁(X, x)` (Exposé V) has a finite subset generating a dense subgroup. -/
def TopologicallyFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k)) [IsProper s]
    [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
    ∃ S : Set (ExposeV.etaleFundamentalGroup Ω x), S.Finite ∧
      (Subgroup.closure S).topologicalClosure = ⊤

/-- X.2.12 (Lang–Serre), from X.2.9: for a finite group `Q`, there are only finitely many
continuous homomorphisms `π₁(X) → Q`, hence only finitely many principal coverings of `X` with
group `Q` up to isomorphism. -/
theorem finite_setOf_continuous_monoidHom_of_statement (h : TopologicallyFiniteStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s]
    [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Q : Type*) [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q] :
    {f : ExposeV.etaleFundamentalGroup Ω x →* Q | Continuous f}.Finite := by
  obtain ⟨S, hS, hdense⟩ := h k s Ω x
  exact finite_setOf_continuous_monoidHom hS hdense

end SGA.SGA1.ExposeX
