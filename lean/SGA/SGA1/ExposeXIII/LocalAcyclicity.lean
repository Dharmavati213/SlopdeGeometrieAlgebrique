/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicity
import SGA.SGA1.ExposeV.GaloisEquivalence
import SGA.SGA1.ExposeXIII.Desingularization
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup

/-!
# SGA 1, Exposé XIII, §3: cohomological properness and generic local acyclicity

§3 proves that, generically on the base, morphisms of finite presentation are cohomologically
proper (3.1, 3.2) and universally locally `1`-aspherical (3.3, 3.4), and deduces the generic
bijectivity of the specialization maps of the prime-to-`p` fundamental groups (3.5). The statements
involving sheaves of groups need the desingularization hypotheses of
`SGA.SGA1.ExposeXIII.Desingularization`, which are part of SGA's statements. SGA's proofs use the
proper base change theorem (XIII.1.4, `ProperBaseChangeStatement`), the local acyclicity of
smooth morphisms (SGA 4 XV 2.1) and of flat morphisms with geometrically reduced fibres
(SGA 4 XV 4.1), and, for 3.1 2) and 3.5, the tame cohomological properness XIII.2.7.

This file defines `1`-asphericity for a set `L` of primes (`IsOneAspherical L`: connected,
nonempty, with trivial `π₁^L` at every geometric point; SGA 4 XV 1.3 in degree `1`, non-abelian)
and the corresponding local notions (`IsLocallyOneAspherical`, `IsUniversallyLocallyOneAspherical`,
Milnor-fibre form of SGA 4 XV 1.11 with algebraic geometric points, from
`SGA.Foundations.Etale.LocalAcyclicity`), and records:

* the inputs SGA 4 XV 2.1 (`LocalAsphericitySmoothStatement`) and SGA 4 XV 4.1
  (`LocalAcyclicityFlatReducedStatement`), statements only;
* XIII.3.1 1) a) (`GenericCohomologicalPropernessStatement`), 3.1 1) b)
  (`GenericCohomologicalPropernessConstructibleStatement`), 3.3
  (`GenericLocalAsphericityStatement`), 3.4 (`FieldLocalAsphericityStatement`) and 3.5
  (`GenericSpecializationStatement`), statements only;
* XIII.3.2 1) (`FieldCohomologicalPropernessStatement`), **proved** for every field and every base
  change in `SGA.SGA1.ExposeXIII.LocalAcyclicityFieldStalks`
  (`SGA.SGA1.ExposeXIII.fieldCohomologicalPropernessStatement`);
* the cases proved here: étale morphisms are universally locally `1`-aspherical for every `L`
  (`isUniversallyLocallyOneAspherical_of_etale`), which gives 3.3 and 3.4 for étale `f`
  (`exists_isUniversallyLocallyOneAspherical_of_etale`); 3.3 and 3.4 for smooth `f`, given
  SGA 4 XV 2.1 (`exists_isUniversallyLocallyOneAspherical_of_smooth`). For `f` finite, the
  cohomological-properness half of 3.1 1) holds with `S' = S` for every sheaf of sets
  (`isCohomologicallyProperLEZero_of_isFinite` and `IsCohomologicallyProperLEZero.of_id`, in
  `SGA.SGA1.ExposeXIII.CohomologicalProperness`); the constructibility of `f_* F` is not proved.
  3.3 and 3.4 for relative curves follow from the statements without their desingularization
  hypothesis (`SGA.SGA1.ExposeXIII.DesingularizationCurves`).

Not stated: 3.1 2), 3.1.1–3.1.3 and 3.2 2), which need cohomological properness in dimension
`≤ 1` for sheaves of groups and `1`-constructibility of stacks (neither is defined in the
repository; see `SGA.SGA1.ExposeXIII.CohomologicalProperness`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

section OneAspherical

/-- SGA 4 XV 1.3 in degree `1`, non-abelian: a scheme `Z` is *`1`-aspherical for* a set `L` of
primes if it is `0`-acyclic (nonempty and connected) and every torsor under a finite constant
`L`-group is trivial, i.e. the maximal pro-`L` quotient `π₁^L(Z, z)` of the fundamental group is
trivial at every geometric point `z`. -/
def IsOneAspherical (L : Set ℕ) : ObjectProperty Scheme.{u} := fun Z ↦
  ConnectedSpace Z ∧ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Z),
    Subsingleton (ProLQuotient L (FundamentalGroup z))

variable {L : Set ℕ}

instance : (IsOneAspherical.{u} L).IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e h := by
    refine ⟨ObjectProperty.prop_of_iso (fun Z : Scheme.{u} ↦ ConnectedSpace Z) e h.1,
      fun Ω _ _ z ↦ ?_⟩
    have := h.2 Ω (z ≫ e.inv)
    have hz : (z ≫ e.inv) ≫ e.hom = z := by simp
    rw [← hz]
    exact subsingleton_proLQuotient_of_surjective (FundamentalGroup.map e.hom (z ≫ e.inv))
      (FundamentalGroup.continuous_map _ _)
      (ExposeV.autMap_bijective (ExposeV.FEt.pullback e.hom) _).2

/-- The spectrum of a separably closed field is `1`-aspherical for every set of primes: it is a
point, with trivial fundamental group. -/
lemma isOneAspherical_spec (K : Type u) [Field K] [IsSepClosed K] :
    IsOneAspherical L (Spec (.of K)) :=
  ⟨inferInstance, fun Ω _ _ z ↦ by
    have : Subsingleton (FundamentalGroup z) :=
      inferInstanceAs (Subsingleton (ExposeV.etaleFundamentalGroup Ω z))
    refine ⟨fun a b ↦ ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact congrArg _ (Subsingleton.elim _ _)⟩

/-- A `1`-aspherical scheme is `0`-acyclic. -/
lemma IsOneAspherical.connectedSpace {Z : Scheme.{u}} (h : IsOneAspherical L Z) :
    ConnectedSpace Z :=
  h.1

end OneAspherical

section Local

variable {X S : Scheme.{u}} (L : Set ℕ) (f : X ⟶ S)

/-- SGA 4 XV 1.11, `n = 1`, non-abelian: `f` is *locally `1`-aspherical for* `L` if its Milnor
fibres `X̃_{x̄} ×_{S̃} t̄` (at algebraic geometric points `t̄` of the strict localization `S̃`) are
`1`-aspherical for `L`. -/
abbrev IsLocallyOneAspherical : Prop :=
  f.IsLocallyAcyclicFor (IsOneAspherical L)

/-- SGA 4 XV 1.11: `f` is *universally locally `1`-aspherical for* `L` if every base change of `f`
is locally `1`-aspherical for `L`. -/
abbrev IsUniversallyLocallyOneAspherical : Prop :=
  f.IsUniversallyLocallyAcyclicFor (IsOneAspherical L)

/-- Locally `1`-aspherical morphisms are locally `0`-acyclic. -/
lemma IsLocallyOneAspherical.isLocallyZeroAcyclic {L : Set ℕ} {f : X ⟶ S}
    (h : IsLocallyOneAspherical L f) : f.IsLocallyZeroAcyclic :=
  h.of_le fun _ hZ ↦ hZ.1

/-- Universally locally `1`-aspherical morphisms are universally locally `0`-acyclic. -/
lemma IsUniversallyLocallyOneAspherical.isUniversallyLocallyZeroAcyclic {L : Set ℕ} {f : X ⟶ S}
    (h : IsUniversallyLocallyOneAspherical L f) : f.IsUniversallyLocallyZeroAcyclic :=
  h.of_le fun _ hZ ↦ hZ.1

/-- Étale morphisms are universally locally `1`-aspherical for every set of primes `L`: their
Milnor fibres are the spectra of separably closed fields
(`AlgebraicGeometry.Scheme.Hom.isUniversallyLocallyAcyclicFor_of_etale`). -/
theorem isUniversallyLocallyOneAspherical_of_etale [Etale f] :
    IsUniversallyLocallyOneAspherical L f :=
  f.isUniversallyLocallyAcyclicFor_of_etale _ fun K _ _ ↦ isOneAspherical_spec K

end Local

section Statements

/-- SGA 4 XV 2.1 in degrees `≤ 1` (statement only; input of XIII.1.17, 3.3 and 3.5): a smooth
morphism `f : X ⟶ S` is universally locally `1`-aspherical for the set of primes invertible on
`S`. -/
def LocalAsphericitySmoothStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [Smooth f],
    IsUniversallyLocallyOneAspherical (primesInvertibleOn S) f

/-- SGA 4 XV 4.1 (statement only; input of XIII.3.3 and, for `f` locally of finite presentation,
of XIII.1.17): a flat morphism locally of finite presentation with geometrically reduced
(separable) fibres is universally locally `0`-acyclic. This is the form quoted in the proof of
XIII.3.3. XIII.1.17 quotes the non-universal form for `f` flat with separable fibres between
locally noetherian `X` and `S`, *without* a finite-presentation hypothesis; this statement covers
1.17 only for `f` locally of finite presentation. The base change form
(`AlgebraicGeometry.Scheme.Hom.IsUniversallyZeroAcyclicBaseChange`) under the hypotheses of this
statement is Stacks 0EYS. -/
def LocalAcyclicityFlatReducedStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f], f.IsUniversallyLocallyZeroAcyclic

/-- XIII.3.1 1) a) (statement only): let `S` be irreducible, `X` and `Y` two `S`-schemes of finite
presentation and `f : X ⟶ Y` an `S`-morphism. There is a nonempty open `S'` of `S` such that, with
`X' = X ×_S S'`, `Y' = Y ×_S S'` and `f' : X' ⟶ Y'`, for every finite constant sheaf of sets `F'`
on `X'`, `f'_* F'` is constructible and `(F', f')` is cohomologically proper relative to `S'` in
dimension `≤ 0`. -/
def GenericCohomologicalPropernessStatement : Prop :=
  ∀ ⦃S X Y : Scheme.{u}⦄ [IrreducibleSpace S] (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFinitePresentation pX] [QuasiCompact pX] [QuasiSeparated pX]
    [LocallyOfFinitePresentation pY] [QuasiCompact pY] [QuasiSeparated pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX),
    ∃ S' : S.Opens, (S' : Set S).Nonempty ∧
      ∀ (E : Type u) [Finite E],
        let f' : pullback pX S'.ι ⟶ pullback pY S'.ι :=
          pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [hf]) (by simp)
        let F' := (constantSheaf (pullback pX S'.ι).smallEtaleTopology (Type u)).obj E
        Scheme.IsConstructibleSheaf ((Scheme.etalePushforward f').obj F') ∧
          IsCohomologicallyProperLEZero (pullback.snd pY S'.ι) f' F'

/-- XIII.3.1 1) b) (statement only): in the situation of 3.1 1) a), for a constructible sheaf of
sets `F` on `X` there is a nonempty open `S'` of `S` (depending on `F`) such that, with `F'` the
inverse image of `F` on `X'`, `f'_* F'` is constructible and `(F', f')` is cohomologically proper
relative to `S'` in dimension `≤ 0`. -/
def GenericCohomologicalPropernessConstructibleStatement : Prop :=
  ∀ ⦃S X Y : Scheme.{u}⦄ [IrreducibleSpace S] (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFinitePresentation pX] [QuasiCompact pX] [QuasiSeparated pX]
    [LocallyOfFinitePresentation pY] [QuasiCompact pY] [QuasiSeparated pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (F : Sheaf X.smallEtaleTopology (Type u)),
    Scheme.IsConstructibleSheaf F →
    ∃ S' : S.Opens, (S' : Set S).Nonempty ∧
      let f' : pullback pX S'.ι ⟶ pullback pY S'.ι :=
        pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [hf]) (by simp)
      let F' := (Scheme.etalePullback (pullback.fst pX S'.ι)).obj F
      Scheme.IsConstructibleSheaf ((Scheme.etalePushforward f').obj F') ∧
        IsCohomologicallyProperLEZero (pullback.snd pY S'.ι) f' F'

/-- XIII.3.2 1): for a coherent (quasi-compact and quasi-separated) morphism
`f : X ⟶ Spec k` to the spectrum of a field, every sheaf of sets `F` on `X` is cohomologically
proper for `f` in dimension `≤ 0`: the formation of `f_* F` commutes with every change of base
`S' ⟶ Spec k`. Part 2) (sheaves of ind-`p'`-groups, dimension `≤ 1`) is not stated. Proved:
`SGA.SGA1.ExposeXIII.fieldCohomologicalPropernessStatement`
(`SGA.SGA1.ExposeXIII.LocalAcyclicityFieldStalks`). -/
def FieldCohomologicalPropernessStatement : Prop :=
  ∀ (k : Type u) [Field k] ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of k)) [QuasiCompact f]
    [QuasiSeparated f] (F : Sheaf X.smallEtaleTopology (Type u)),
    IsCohomologicallyProperLEZero (𝟙 _) f F

/-- XIII.3.3 (statement only): let `S` be irreducible with generic point `s` and `f : X ⟶ S` of
finite presentation. Suppose that the schemes of finite type over an algebraic closure `k̄` of
`κ(s)` of dimension `≤ dim X_s` are desingularizable (EGA IV 7.9.1). Then, with `L` the set of
primes invertible on `S`, there is a nonempty open `S₁` of `S` such that `f|S₁` is universally
locally `1`-aspherical for `L`. -/
def GenericLocalAsphericityStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f],
    DesingularizableUpTo (AlgebraicClosure (S.residueField (genericPoint S)))
      (topologicalKrullDim
        ↥(pullback f (S.fromSpecResidueField (genericPoint S)) : Scheme.{u})) →
    ∃ S₁ : S.Opens, (S₁ : Set S).Nonempty ∧
      IsUniversallyLocallyOneAspherical (primesInvertibleOn S) (pullback.snd f S₁.ι)

/-- XIII.3.4 (statement only): let `k` be a field of characteristic `p ≥ 0`, `p'` the set of
primes different from `p` (the primes invertible on `Spec k`) and `f : X ⟶ Spec k` coherent.
Suppose that either a) `f` is of finite type and the schemes of finite type of dimension
`≤ dim X` over an algebraic closure of `k` are desingularizable, or b) all schemes of finite type
over an algebraic closure of `k` are desingularizable. Then `f` is universally locally
`1`-aspherical for `p'`. -/
def FieldLocalAsphericityStatement : Prop :=
  ∀ (k : Type u) [Field k] ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of k)) [QuasiCompact f]
    [QuasiSeparated f],
    (LocallyOfFiniteType f ∧ DesingularizableUpTo (AlgebraicClosure k) (topologicalKrullDim X)) ∨
      DesingularizableUpTo (AlgebraicClosure k) ⊤ →
    IsUniversallyLocallyOneAspherical (primesInvertibleOn (Spec (.of k))) f

/-- XIII.3.5 (statement only): let `S` be irreducible with generic point `s`, `f : X ⟶ S` of
finite presentation, and suppose that the schemes of finite type of dimension `≤ dim X_s` over an
algebraic closure of `κ(s)` are strongly desingularizable (SGA 5 I 3.1.5). With `L` the set of
primes invertible on `S`, there is a nonempty open `S₁` of `S` such that for every specialization
`s̄₁ → s̄₂` of geometric points of `S₁` the specialization morphism
`π₁^L(X_{s̄₁}) → π₁^L(X_{s̄₂})` (XIII.2.10) is bijective.

A specialization `s̄₁ → s̄₂` is a geometric point `s̄₁` of the strict localization `S̄` of `S₁` at
`s̄₂`. SGA defines the specialization morphism as `π = π₂⁻¹ π₁₂ π₁`, where
`π₁ : π₁^L(X_{s̄₁}, a₁) → π₁^L(X ×_S S̄, a₁)` and `π₂ : π₁^L(X_{s̄₂}, a₂) → π₁^L(X ×_S S̄, a₂)` are
induced by the inclusions of the fibres (`π₂` being an isomorphism) and `π₁₂` is given by a class
of paths. So `π` is bijective if and only if `π₁` and `π₂` are, which is what we state, at all
geometric points `a₁`, `a₂` (for fibres which are not geometrically connected this is the
statement for each connected component). The closed fibre `X_{s̄₂}` is written as the fibre over
`Spec Ω₂ ⟶ S̄ ⟶ S₁`. -/
def GenericSpecializationStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f],
    StronglyDesingularizableUpTo (AlgebraicClosure (S.residueField (genericPoint S)))
      (topologicalKrullDim
        ↥(pullback f (S.fromSpecResidueField (genericPoint S)) : Scheme.{u})) →
    ∃ S₁ : S.Opens, (S₁ : Set S).Nonempty ∧
      ∀ (Ω₂ : Type u) [Field Ω₂] [IsSepClosed Ω₂] (s₂ : Spec (.of Ω₂) ⟶ S₁)
        (Ω₁ : Type u) [Field Ω₁] [IsSepClosed Ω₁] (s₁ : Spec (.of Ω₁) ⟶ Spec s₂.strictLocalization)
        (Ω : Type u) [Field Ω] [IsSepClosed Ω],
        let f₁ := pullback.snd f S₁.ι
        (∀ a₁ : Spec (.of Ω) ⟶ pullback f₁ (s₁ ≫ s₂.fromSpecStrictLocalization),
          Function.Bijective (proLMap (primesInvertibleOn S)
            (FundamentalGroup.map (pullback.map f₁ (s₁ ≫ s₂.fromSpecStrictLocalization) f₁
              s₂.fromSpecStrictLocalization (𝟙 _) s₁ (𝟙 _) (by simp) (by simp)) a₁)
            (FundamentalGroup.continuous_map _ _))) ∧
        ∀ a₂ : Spec (.of Ω) ⟶ pullback f₁
            (s₂.toSpecStrictLocalization ≫ s₂.fromSpecStrictLocalization),
          Function.Bijective (proLMap (primesInvertibleOn S)
            (FundamentalGroup.map (pullback.map f₁
              (s₂.toSpecStrictLocalization ≫ s₂.fromSpecStrictLocalization) f₁
              s₂.fromSpecStrictLocalization (𝟙 _) s₂.toSpecStrictLocalization (𝟙 _) (by simp)
              (by simp)) a₂)
            (FundamentalGroup.continuous_map _ _))

end Statements

section Cases

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- XIII.3.3 and 3.4 for `f` étale, unconditionally and with `S₁ = S`: étale morphisms are
universally locally `1`-aspherical for every set of primes. -/
theorem exists_isUniversallyLocallyOneAspherical_of_etale [Nonempty S] (L : Set ℕ) [Etale f] :
    ∃ S₁ : S.Opens, (S₁ : Set S).Nonempty ∧
      IsUniversallyLocallyOneAspherical L (pullback.snd f S₁.ι) :=
  ⟨⊤, Set.univ_nonempty, (isUniversallyLocallyOneAspherical_of_etale L f).of_isPullback
    (IsPullback.of_hasPullback f (⊤ : S.Opens).ι)⟩

/-- XIII.3.3 and 3.4 for `f` smooth, with `S₁ = S`, given SGA 4 XV 2.1
(`LocalAsphericitySmoothStatement`); no desingularization hypothesis is needed. -/
theorem exists_isUniversallyLocallyOneAspherical_of_smooth [Nonempty S]
    (h : LocalAsphericitySmoothStatement.{u}) [Smooth f] :
    ∃ S₁ : S.Opens, (S₁ : Set S).Nonempty ∧
      IsUniversallyLocallyOneAspherical (primesInvertibleOn S) (pullback.snd f S₁.ι) :=
  ⟨⊤, Set.univ_nonempty, (h f).of_isPullback
    (IsPullback.of_hasPullback f (⊤ : S.Opens).ι)⟩

end Cases

end SGA.SGA1.ExposeXIII
