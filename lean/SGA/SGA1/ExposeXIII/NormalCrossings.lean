/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Etale.LocallyConstant
import SGA.Foundations.HenselizationNoetherian
import SGA.Foundations.StrictHenselization
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeII.RelativeDimension
import SGA.SGA1.ExposeIX.Unramified
import SGA.SGA1.ExposeXIII.CohomologicalProperness
import SGA.SGA1.ExposeXIII.LocallyConstantSheaves
import SGA.SGA1.ExposeXIII.Stacks
import SGA.SGA1.ExposeXIII.TameRamification

/-!
# SGA 1, Exposé XIII, §2: divisors with normal crossings and tame ramification

§2 of Exposé XIII shows that the complement `U = X - Y` of a divisor with normal crossings
relative to `S` is cohomologically proper over `X` for tamely ramified locally constant sheaves
(Theorem 2.4). This file records the notions of §2 and the statement of 2.4 for sheaves of sets:

* 2.0: the notions `IsTameExtension`, `IsTameAlgebra`, the structure of inertia groups, the
  comparison with the classical definition, 2.0.1 and the first two parts of 2.0.3 are in
  `SGA.SGA1.ExposeXIII.TameRamification`; here is the statement of 2.0.2
  (`TameBaseChangeDVRStatement`) and its proof (`tameBaseChangeDVRStatement`), and its case of
  the strict localization `R → R^{sh}` (`isTameAlgebra_iff_strictHenselization`; the strict
  henselization of a discrete valuation ring is one, `isDiscreteValuationRing_strictHenselization`).
* 2.1: `IsStrictNormalCrossings`, `IsNormalCrossingsSupport`; the local rings of the geometric
  fibres at the maximal points of `Y_s̄` are discrete valuation rings
  (`normalCrossingsLocalRingStatement`: étale locally the local ring is regular of dimension
  `n - trdeg κ(y) ≥ 1` with maximal ideal minimal over one `fᵢ`); the tameness of a sheaf of
  sets on `U` (2.1.1, `IsTamelyRamifiedSheaf`, pointwise `IsTamelyRamifiedSheafAt`; for étale
  coverings `IsTamelyRamifiedCovering`), `H1Tame` (2.1.2).
* 2.3 a): a locally constant constructible sheaf is represented by an étale covering
  (`IsLocallyConstantConstructible.exists_etaleYoneda_iso`, from SGA 4 IX 2.2 in
  `SGA.SGA1.ExposeXIII.LocallyConstantSheaves`), so the locally constant constructible tamely
  ramified sheaves are those represented by tamely ramified étale coverings
  (`isLocallyConstantConstructible_and_isTamelyRamifiedSheaf_iff`); the reduction of tameness to
  the maximal points of `S` is `TameRamificationAtMaximalPointsStatement` (statement only, it
  needs the relative Abhyankar lemma XIII.5.5).
* 2.4 1) for sheaves of sets: `TameBaseChangeStatement`.

The results of §2 depend on Abhyankar's lemma (Appendix I) and on étale cohomology (the sheaves
`R¹_tame i_* F`, specialization maps, constructibility) and are recorded as statements. The
items on sheaves of groups and stacks (2.1.3–2.1.6, 2.2, 2.3 b), 2.5–2.9) are not formalized.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

section TameAlgebras

/-- XIII 2.0.2: let `R ⟶ R'` be a local homomorphism of discrete valuation rings sending a
uniformizer to a uniformizer, with separable residue field extension. An étale algebra `L` over
the fraction field `K` of `R` is tamely ramified over `R` if and only if `L ⊗_K K'` is tamely
ramified over `R'`. Proved in `tameBaseChangeDVRStatement`. -/
def TameBaseChangeDVRStatement : Prop :=
  ∀ (R R' K K' L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
    [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [Algebra.IsSeparable (ResidueField R) (ResidueField R')] [CommRing L] [Algebra K L]
    [Algebra.Etale K L] [Algebra R L] [IsScalarTower R K L],
    (∀ π : R, Irreducible π → Irreducible (algebraMap R R' π)) →
    (IsTameAlgebra R (K := K) L ↔ IsTameAlgebra R' (K := K') (TensorProduct K K' L))

/-- XIII 2.0.2 (`IsTameAlgebra.baseChange`, `IsTameAlgebra.of_baseChange`). -/
theorem tameBaseChangeDVRStatement : TameBaseChangeDVRStatement.{u} := by
  intro R R' K K' L
  intros
  rename_i hπ
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := by
    obtain ⟨π, hπ'⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ', Ideal.map_span,
      Set.image_singleton,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (hπ π hπ')]
  exact ⟨IsTameAlgebra.baseChange, IsTameAlgebra.of_baseChange hm⟩

end TameAlgebras

section StrictLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (k' : Type u) [Field k'] [Algebra R k'] [Algebra (ResidueField R) k']
  [IsScalarTower R (ResidueField R) k']

attribute [local instance] isLocalHom_algebraMap_of_isScalarTower

/-- The (strict) henselization of a discrete valuation ring `R` with respect to a separable
extension `k'` of its residue field (e.g. a separable closure, giving the strict localization
`R^{sh}`) is a regular local ring. -/
instance isRegularLocalRing_strictHenselization :
    IsRegularLocalRing (StrictHenselization R k') :=
  (SGA.SGA1.ExposeI.isRegularLocalRing_iff_of_flat StrictHenselization.map_maximalIdeal).mp
    inferInstance

/-- The (strict) henselization of a discrete valuation ring with respect to a separable extension
of its residue field is a discrete valuation ring. -/
instance isDiscreteValuationRing_strictHenselization :
    IsDiscreteValuationRing (StrictHenselization R k') := by
  refine IsRegularLocalRing.isDiscreteValuationRing ?_
  rw [← SGA.SGA1.ExposeI.ringKrullDim_eq_of_flat_of_map_maximalIdeal
    StrictHenselization.map_maximalIdeal, IsDiscreteValuationRing.ringKrullDim_eq_one]

variable [Algebra.IsSeparable (ResidueField R) k']

/-- The residue field of the (strict) henselization of `R` with respect to a separable extension
`k'` of the residue field `k` of `R` is separable over `k`. -/
instance isSeparable_residueField_strictHenselization :
    Algebra.IsSeparable (ResidueField R) (ResidueField (StrictHenselization R k')) := by
  let e := StrictHenselization.residueFieldEquiv R k'
  refine Algebra.IsSeparable.of_algHom _ k'
    { toRingHom := (e : ResidueField (StrictHenselization R k') →+* k'), commutes' := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := residue_surjective x
  change e (algebraMap (ResidueField R) (ResidueField (StrictHenselization R k')) (residue R r)) = _
  rw [ResidueField.algebraMap_residue, ← ResidueField.algebraMap_eq, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact e.commutes r

variable {R} {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (K' : Type*) [Field K'] [Algebra (StrictHenselization R k') K']
  [IsFractionRing (StrictHenselization R k') K'] [Algebra K K'] [Algebra R K']
  [IsScalarTower R K K'] [IsScalarTower R (StrictHenselization R k') K']

/-- XIII 2.0.2 for the strict localization: let `R^{sh}` be the strict henselization of the
discrete valuation ring `R` (the case `k'` a separable closure of the residue field `k`; more
generally `k'` any separable extension of `k`) and `K'` its field of fractions. An étale
`K`-algebra `L` is tamely ramified over `R` iff `K' ⊗_K L` is tamely ramified over `R^{sh}`. -/
theorem isTameAlgebra_iff_strictHenselization (L : Type*) [CommRing L] [Algebra K L]
    [Algebra.Etale K L] [Algebra R L] [IsScalarTower R K L] :
    IsTameAlgebra R (K := K) L ↔
      IsTameAlgebra (StrictHenselization R k') (K := K') (TensorProduct K K' L) :=
  ⟨IsTameAlgebra.baseChange, IsTameAlgebra.of_baseChange StrictHenselization.map_maximalIdeal⟩

end StrictLocalization

section Divisors

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- `X` is smooth of relative dimension `n` over `S` in a neighbourhood of `x`. -/
def IsSmoothOfRelativeDimensionAt (n : ℕ) (x : X) : Prop :=
  ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ p)

/-- The closed subscheme `V((f i)_{i ∈ I})` of `X` cut out by global functions. -/
noncomputable def zeroSubscheme {ι : Type*} (f : ι → Γ(X, ⊤)) (I : Set ι) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span (f '' I))

/-- XIII (2.1.0): the family `(f i)` of global functions defines a divisor `D = ∑ div(f i)` with
strictly normal crossings relative to `S`: at every point `x` of `Supp D`, `X` is smooth over `S`,
and `V((f i)_{i ∈ I(x)})`, where `I(x)` is the set of `i` with `f i (x) = 0`, is smooth over `S`
of codimension `card I(x)` in `X` at `x` (codimension is measured by relative dimensions). -/
def IsStrictNormalCrossings {ι : Type*} [Finite ι] (f : ι → Γ(X, ⊤)) : Prop :=
  ∀ x ∈ ⋃ i, X.zeroLocus {f i},
    ∃ n m : ℕ, IsSmoothOfRelativeDimensionAt p n x ∧
      m + Nat.card {i | x ∈ X.zeroLocus {f i}} = n ∧
      ∃ v : (zeroSubscheme f {i | x ∈ X.zeroLocus {f i}}).subscheme,
        (zeroSubscheme f {i | x ∈ X.zeroLocus {f i}}).subschemeι v = x ∧
        IsSmoothOfRelativeDimensionAt
          ((zeroSubscheme f {i | x ∈ X.zeroLocus {f i}}).subschemeι ≫ p) m v

/-- XIII 2.1: the closed subset `Y` of `X` is the support of a divisor with normal crossings
relative to `S`: étale locally on `X`, it is the support of a divisor with strictly normal
crossings. (Only the support `Y = Supp D` is used in §2, so the multiplicities of `D` are not
recorded.) -/
def IsNormalCrossingsSupport (Y : Set X) : Prop :=
  ∃ (α : Type u) (W : α → Scheme.{u}) (e : ∀ a, W a ⟶ X), (∀ a, Etale (e a)) ∧
    (⋃ a, Set.range (e a)) = Set.univ ∧
    ∀ a, ∃ (ι : Type) (_ : Finite ι) (f : ι → Γ(W a, ⊤)),
      IsStrictNormalCrossings (e a ≫ p) f ∧ (e a) ⁻¹' Y = ⋃ i, (W a).zeroLocus {f i}

/-- XIII 2.1: if `Y` is the support of a divisor with normal crossings relative to `S`, then for
every geometric point `s̄` of `S` and every maximal point `y` of the geometric fiber `Y_s̄`, the
local ring `O_{X_s̄, y}` is a discrete valuation ring. Proved in
`normalCrossingsLocalRingStatement`. -/
def NormalCrossingsLocalRingStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (p : X ⟶ S) (Y : Set X), IsNormalCrossingsSupport p Y →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (y : ↥(pullback p s)),
      y ∈ (pullback.fst p s) ⁻¹' Y → (∀ z ∈ (pullback.fst p s) ⁻¹' Y, z ⤳ y → z = y) →
      ∃ _ : IsDomain ((pullback p s).presheaf.stalk y),
        IsDiscreteValuationRing ((pullback p s).presheaf.stalk y)

end Divisors

section NormalCrossingsLocalRing

/-! ### XIII 2.1: the local rings at the maximal points of `Y_s̄` -/

/-- Discrete valuation rings descend along flat local homomorphisms `O → O'` with
`𝔪_O O' = 𝔪_{O'}`: `O` is noetherian (faithfully flat descent), regular and of dimension one. -/
theorem isDiscreteValuationRing_of_flat_of_map_maximalIdeal {O O' : Type u} [CommRing O]
    [IsLocalRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [IsLocalHom (algebraMap O O')] [Module.Flat O O']
    (hm : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O') :
    ∃ _ : IsDomain O, IsDiscreteValuationRing O := by
  have : Module.FaithfullyFlat O O' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsNoetherianRing O := IsNoetherianRing.of_faithfullyFlat (B := O')
  have : IsRegularLocalRing O :=
    (SGA.SGA1.ExposeI.isRegularLocalRing_iff_of_flat hm).mpr inferInstance
  refine ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing ?_⟩
  rw [SGA.SGA1.ExposeI.ringKrullDim_eq_of_flat_of_map_maximalIdeal hm,
    IsDiscreteValuationRing.ringKrullDim_eq_one]

/-- If `f : X' ⟶ X` is étale and the local ring of `X'` at `x'` is a discrete valuation ring, so
is the local ring of `X` at `f x'`. -/
theorem isDiscreteValuationRing_stalk_of_etale {X X' : Scheme.{u}} (f : X' ⟶ X) [Etale f]
    (x' : X') [IsDomain (X'.presheaf.stalk x')] [IsDiscreteValuationRing (X'.presheaf.stalk x')] :
    ∃ _ : IsDomain (X.presheaf.stalk (f x')),
      IsDiscreteValuationRing (X.presheaf.stalk (f x')) := by
  have h₁ := Flat.stalkMap f x'
  have h₂ := FormallyUnramified.stalkMap f x'
  have h₃ := LocallyOfFiniteType.stalkMap f x'
  algebraize [(f.stalkMap x').hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f x')) (X'.presheaf.stalk x')) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x').hom)
  exact isDiscreteValuationRing_of_flat_of_map_maximalIdeal
    (Algebra.FormallyUnramified.map_maximalIdeal (S := X'.presheaf.stalk x'))

/-- The local ring of the spectrum of a field has dimension zero. -/
lemma ringKrullDim_stalk_spec_field {Ω : Type u} [Field Ω] (x : Spec (.of Ω)) :
    ringKrullDim ((Spec (.of Ω)).presheaf.stalk x) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight,
    Order.coheight_eq_zero.mpr fun b _ ↦ (Subsingleton.elim b x).le]
  rfl

/-- On a scheme smooth of relative dimension `m` over a field, `trdeg κ(x) ≤ m`. -/
lemma residueFieldTrdeg_le_of_smooth {Ω : Type u} [Field Ω] {U : Scheme.{u}}
    (q : U ⟶ Spec (.of Ω)) (m : ℕ) [SmoothOfRelativeDimension m q] (x : U) :
    (q.residueFieldTrdeg x).toENat ≤ m := by
  have hdim := SGA.SGA1.ExposeII.ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_smooth q m x
  rw [ringKrullDim_stalk_spec_field, zero_add] at hdim
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (U.presheaf.stalk x) = d :=
    (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.coe_ne_bot
      ringKrullDim_nonneg_of_nontrivial)).imp fun _ h ↦ h.symm
  rw [hd] at hdim
  have : d + (q.residueFieldTrdeg x).toENat = m := by exact_mod_cast hdim
  rw [← this]
  exact le_add_self

/-- Let `U` be smooth of relative dimension `n` over a field, `g` a global function and `u` a
point of the zero locus of `g` which is maximal in it (no strict generization of `u` lies on
`g = 0`), with `trdeg κ(u) < n`. Then `𝒪_{U,u}` is a discrete valuation ring: it is regular
(II.5.3), of dimension `n - trdeg κ(u) ≥ 1` (II.1.5), and `𝔪_u` is minimal over the germ of `g`,
so has height `≤ 1` (Krull). -/
theorem isDiscreteValuationRing_stalk_of_smooth_of_zeroLocus {Ω : Type u} [Field Ω]
    {U : Scheme.{u}} (q : U ⟶ Spec (.of Ω)) (n : ℕ) [SmoothOfRelativeDimension n q]
    (g : Γ(U, ⊤)) (u : U) (hu : u ∈ U.zeroLocus {g})
    (hmin : ∀ z ∈ U.zeroLocus {g}, z ⤳ u → z = u)
    (htr : (q.residueFieldTrdeg u).toENat < n) :
    ∃ _ : IsDomain (U.presheaf.stalk u), IsDiscreteValuationRing (U.presheaf.stalk u) := by
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : IsRegularLocalRing (U.presheaf.stalk u) :=
    SGA.SGA1.ExposeII.isRegularLocalRing_stalk_of_smooth_field Ω q u
  -- the dimension is `≥ 1`
  have hdim := SGA.SGA1.ExposeII.ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_smooth q n u
  have h0 : ringKrullDim ((Spec (.of Ω)).presheaf.stalk (q u)) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight,
      Order.coheight_eq_zero.mpr fun b _ ↦ (Subsingleton.elim b (q u)).le]
    rfl
  rw [h0, zero_add] at hdim
  -- `𝔪_u` is minimal over the germ of `g`
  set t := U.presheaf.germ ⊤ u trivial g
  have htm : t ∈ maximalIdeal (U.presheaf.stalk u) := by
    rw [Scheme.mem_zeroLocus_iff] at hu
    have := hu g rfl
    rw [Scheme.mem_basicOpen U g u trivial] at this
    exact this
  have hminP : maximalIdeal (U.presheaf.stalk u) ∈ (Ideal.span {t}).minimalPrimes := by
    refine ⟨⟨inferInstance, by rw [Ideal.span_le, Set.singleton_subset_iff]; exact htm⟩,
      fun P ⟨hP, htP⟩ hPm ↦ ?_⟩
    let pt : Spec (U.presheaf.stalk u) := ⟨P, hP⟩
    have hz : U.fromSpecStalk u pt ⤳ u := by
      have : U.fromSpecStalk u pt ∈ Set.range (U.fromSpecStalk u) := ⟨pt, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hzg : U.fromSpecStalk u pt ∈ U.zeroLocus {g} := by
      rw [← Scheme.toSpecΓ_preimage_zeroLocus]
      change U.toSpecΓ (U.fromSpecStalk u pt) ∈ PrimeSpectrum.zeroLocus {g}
      rw [← Scheme.Hom.comp_apply, Scheme.fromSpecStalk_toSpecΓ]
      change PrimeSpectrum.comap (U.presheaf.germ ⊤ u trivial).hom pt ∈
        PrimeSpectrum.zeroLocus {g}
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact htP (Ideal.subset_span rfl)
    have h2 : U.fromSpecStalk u pt = U.fromSpecStalk u (closedPoint _) :=
      (hmin _ hzg hz).trans Scheme.fromSpecStalk_closedPoint.symm
    have hpt := (U.fromSpecStalk u).isEmbedding.injective h2
    have : P = maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hpt
    exact this.ge
  have hht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {t}) _ hminP
  have hle : ringKrullDim (U.presheaf.stalk u) ≤ 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hht
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (U.presheaf.stalk u) = d :=
    (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.coe_ne_bot
      ringKrullDim_nonneg_of_nontrivial)).imp fun _ h ↦ h.symm
  rw [hd] at hdim hle
  have hdim' : d + (q.residueFieldTrdeg u).toENat = n := by exact_mod_cast hdim
  have hd1 : d = 1 := by
    have hle' : d ≤ 1 := by exact_mod_cast hle
    by_cases h0 : d = 0
    · rw [h0, zero_add] at hdim'
      exact absurd hdim' htr.ne
    · exact le_antisymm hle' (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h0))
  refine ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing ?_⟩
  rw [hd, hd1]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Base change to a fibre: if `t ≫ e ≫ p` is smooth of relative dimension `k`, so is the
composite `T ×_W (W ×_X (X ×_S Z)) ⟶ Z`. -/
lemma smoothOfRelativeDimension_pullback_snd {W X S T Z : Scheme.{u}} (e : W ⟶ X) (p : X ⟶ S)
    (s : Z ⟶ S) (t : T ⟶ W) (k : ℕ) (h : SmoothOfRelativeDimension k (t ≫ e ≫ p)) :
    SmoothOfRelativeDimension k (pullback.snd t (pullback.fst e (pullback.fst p s)) ≫
      pullback.snd e (pullback.fst p s) ≫ pullback.snd p s) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := k)
  have h' : SmoothOfRelativeDimension k (pullback.snd ((t ≫ e) ≫ p) s) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension k) _ _
      (by rwa [Category.assoc])
  have heq : (pullbackRightPullbackFstIso e (pullback.fst p s) t).hom ≫
      (pullbackRightPullbackFstIso p s (t ≫ e)).hom ≫ pullback.snd ((t ≫ e) ≫ p) s =
      pullback.snd t (pullback.fst e (pullback.fst p s)) ≫ pullback.snd e (pullback.fst p s) ≫
        pullback.snd p s := by
    simp
  rw [← heq]
  exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension k) _ _
    (MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension k) _ _ h')

/-- The zero locus of the pull-back of a global function is the preimage of its zero locus. -/
lemma zeroLocus_appTop {U W : Scheme.{u}} (h : U ⟶ W) (f : Γ(W, ⊤)) :
    U.zeroLocus {h.appTop f} = h ⁻¹' W.zeroLocus {f} := by
  rw [Scheme.zeroLocus_singleton, Scheme.zeroLocus_singleton, ← Scheme.preimage_basicOpen_top]
  rfl

/-- The fibres of a locally quasi-finite morphism are discrete: two points of a fibre, one
specializing to the other, are equal. -/
lemma eq_of_specializes_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {z u : X} (h : z ⤳ u) (he : f z = f u) : z = u := by
  have hd := (f.isDiscrete_preimage_singleton (f u)).to_subtype
  have hs : (⟨z, he⟩ : f ⁻¹' {f u}) ⤳ ⟨u, rfl⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val (specializes_iff_eq.mp hs)

set_option backward.isDefEq.respectTransparency.types false in
/-- XIII 2.1: if `Y` is the support of a divisor with normal crossings relative to `S`, then for
every geometric point `s̄` of `S` and every maximal point `y` of the geometric fibre `Y_s̄`, the
local ring `𝒪_{X_s̄, y}` is a discrete valuation ring. Étale locally, `X` is smooth of relative
dimension `n` over `S` and `Y = ⋃ V(fᵢ)` with `V(f_I)` smooth of relative dimension `n - |I|`; on
the geometric fibre the local ring at `y` is regular, of dimension `n - trdeg κ(y) ≥ |I| ≥ 1`
(as `trdeg κ(y) ≤ n - |I|`), and its maximal ideal is minimal over one `fᵢ` (`y` is maximal in
`Y_s̄`), so has height `≤ 1` (`isDiscreteValuationRing_stalk_of_smooth_of_zeroLocus`); étale
maps preserve this (`isDiscreteValuationRing_stalk_of_etale`). -/
theorem normalCrossingsLocalRingStatement : NormalCrossingsLocalRingStatement.{u} := by
  intro X S p Y hY Ω _ _ s y hyY hmax
  obtain ⟨α, W, e, he, hcov, hloc⟩ := hY
  -- a chart through the image of `y`
  have hx : pullback.fst p s y ∈ ⋃ a, Set.range (e a) := by rw [hcov]; trivial
  obtain ⟨a, w₀, hw₀⟩ := Set.mem_iUnion.mp hx
  have := he a
  obtain ⟨ι, _, f, hSNC, hYa⟩ := hloc a
  have hw₀Y : w₀ ∈ ⋃ i, (W a).zeroLocus {f i} := by
    rw [← hYa]
    change e a w₀ ∈ Y
    rw [hw₀]
    exact hyY
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hw₀Y
  obtain ⟨n, m, ⟨V, hw₀V, hV⟩, hnm, v, hv, ⟨V₁, hvV₁, hV₁⟩⟩ := hSNC w₀ hw₀Y
  -- the geometric fibre `U'` of `W a`, and the points `u'` over `(w₀, y)`, `u ∈ V ×_{W a} U'`
  obtain ⟨u', hu'1, hu'2⟩ := Scheme.Pullback.exists_preimage_pullback (f := e a)
    (g := pullback.fst p s) w₀ y hw₀
  obtain ⟨u, hu1, hu2⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι)
    (g := pullback.fst (e a) (pullback.fst p s)) ⟨w₀, hw₀V⟩ u' (by rw [hu'1]; rfl)
  -- the étale map `U ⟶ X_s̄` and the smooth structure of `U` over `Ω`
  have hsmU := smoothOfRelativeDimension_pullback_snd (e a) p s V.ι n hV
  have hπu : (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.snd (e a) (pullback.fst p s)) u = y := by
    rw [Scheme.Hom.comp_apply, hu2, hu'2]
  have hφu : (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.fst (e a) (pullback.fst p s)) u = w₀ := by
    rw [Scheme.Hom.comp_apply, hu2, hu'1]
  have : LocallyQuasiFinite (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.snd (e a) (pullback.fst p s)) :=
    SGA.SGA1.ExposeIX.locallyQuasiFinite_of_formallyUnramified _
  -- the pulled back function `g`
  have hzl := zeroLocus_appTop (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.fst (e a) (pullback.fst p s)) (f i₀)
  have hu : u ∈ (pullback V.ι (pullback.fst (e a) (pullback.fst p s))).zeroLocus (U := ⊤)
      {(pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
        pullback.fst (e a) (pullback.fst p s)).appTop (f i₀)} := by
    rw [hzl, Set.mem_preimage, hφu]
    exact hi₀
  have hmin : ∀ z ∈ (pullback V.ι (pullback.fst (e a) (pullback.fst p s))).zeroLocus (U := ⊤)
      {(pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
        pullback.fst (e a) (pullback.fst p s)).appTop (f i₀)}, z ⤳ u → z = u := by
    intro z hz hzu
    rw [hzl] at hz
    have hzY : (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
        pullback.snd (e a) (pullback.fst p s)) z ∈ (pullback.fst p s) ⁻¹' Y := by
      change pullback.fst p s ((pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
        pullback.snd (e a) (pullback.fst p s)) z) ∈ Y
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← pullback.condition, ← Category.assoc,
        Scheme.Hom.comp_apply]
      have : (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
          pullback.fst (e a) (pullback.fst p s)) z ∈ (e a) ⁻¹' Y := by
        rw [hYa]
        exact Set.mem_iUnion.mpr ⟨i₀, hz⟩
      exact this
    have h1 := hmax _ hzY (by rw [← hπu]; exact hzu.map (Scheme.Hom.continuous _))
    exact eq_of_specializes_of_locallyQuasiFinite _ hzu (h1.trans hπu.symm)
  -- `trdeg κ(u) ≤ m < n`, computed at a point of `V(f_I)_s̄` over `u'`
  obtain ⟨v', hv'1, hv'2⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := V₁.ι ≫ (zeroSubscheme f {i | w₀ ∈ (W a).zeroLocus {f i}}).subschemeι)
    (g := pullback.fst (e a) (pullback.fst p s)) ⟨v, hvV₁⟩ u' (by
      rw [Scheme.Hom.comp_apply, hu'1]
      exact hv)
  have hV₁' : SmoothOfRelativeDimension m ((V₁.ι ≫
      (zeroSubscheme f {i | w₀ ∈ (W a).zeroLocus {f i}}).subschemeι) ≫ e a ≫ p) := by
    rwa [Category.assoc]
  have hsmV := smoothOfRelativeDimension_pullback_snd (e a) p s _ m hV₁'
  have htrV := residueFieldTrdeg_le_of_smooth (pullback.snd (V₁.ι ≫
    (zeroSubscheme f {i | w₀ ∈ (W a).zeroLocus {f i}}).subschemeι)
    (pullback.fst (e a) (pullback.fst p s)) ≫ pullback.snd (e a) (pullback.fst p s) ≫
      pullback.snd p s) m v'
  rw [Scheme.Hom.residueFieldTrdeg_comp, hv'2,
    Scheme.Hom.residueFieldTrdeg_eq_zero_of_surjective (pullback.snd (V₁.ι ≫
      (zeroSubscheme f {i | w₀ ∈ (W a).zeroLocus {f i}}).subschemeι)
      (pullback.fst (e a) (pullback.fst p s))) v' (Scheme.Hom.residueFieldMap_surjective _ _),
    add_zero] at htrV
  have htrU : ((pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.snd (e a) (pullback.fst p s) ≫ pullback.snd p s).residueFieldTrdeg u).toENat <
        n := by
    rw [Scheme.Hom.residueFieldTrdeg_comp, hu2,
      Scheme.Hom.residueFieldTrdeg_eq_zero_of_surjective
        (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s))) u
        (Scheme.Hom.residueFieldMap_surjective _ _), add_zero]
    refine htrV.trans_lt ?_
    have : Nonempty {i | w₀ ∈ (W a).zeroLocus {f i}} := ⟨⟨i₀, hi₀⟩⟩
    have hcard : 0 < Nat.card {i | w₀ ∈ (W a).zeroLocus {f i}} := Nat.card_pos
    exact_mod_cast (by omega : m < n)
  -- conclusion
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_of_smooth_of_zeroLocus _ n _ u hu hmin htrU
  exact hπu ▸ isDiscreteValuationRing_stalk_of_etale
    (pullback.snd V.ι (pullback.fst (e a) (pullback.fst p s)) ≫
      pullback.snd (e a) (pullback.fst p s)) u

end NormalCrossingsLocalRing

section TameSheaves

/-- `y` is a maximal point of the subset `T`: it lies in `T` and has no strict generization in
`T`. -/
def IsMaximalPointOf {Z : Type*} [TopologicalSpace Z] (T : Set Z) (y : Z) : Prop :=
  y ∈ T ∧ ∀ z ∈ T, z ⤳ y → z = y

/-- The étale `K`-scheme `Spec L` for an étale `K`-algebra `L`, as an object of the étale site
of `Spec K`. -/
noncomputable def etaleSpec (K L : Type u) [Field K] [CommRing L] [Algebra K L]
    [Algebra.Etale K L] : (Spec (.of K)).Etale :=
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

variable {X S : Scheme.{u}} (p : X ⟶ S) (Y : Set X) (U : X.Opens)

/-- XIII 2.1.1 at a geometric point `s̄` of `S`: for every maximal point `y` of the geometric
fiber `Y_s̄`, the restriction of `F` to the field of fractions `K` of the local ring `O_{X_s̄, y}`
is represented by `Spec L` for an étale `K`-algebra `L` tamely ramified over `O_{X_s̄, y}`.
(The morphism `Spec K ⟶ X` factors through `U` in a unique way; the condition is stated for
every such factorization.) -/
def IsTamelyRamifiedSheafAt (F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)) (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) : Prop :=
  ∀ (y : ↥(pullback p s)), IsMaximalPointOf ((pullback.fst p s) ⁻¹' Y) y →
    ∀ (K : Type u) [Field K] [Algebra ((pullback p s).presheaf.stalk y) K]
      [IsFractionRing ((pullback p s).presheaf.stalk y) K] (κ : Spec (.of K) ⟶ U),
      κ ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap ((pullback p s).presheaf.stalk y) K)) ≫
        (pullback p s).fromSpecStalk y ≫ pullback.fst p s →
      ∃ (L : Type u) (_ : CommRing L) (_ : Algebra K L) (_ : Algebra.Etale K L)
        (_ : Algebra ((pullback p s).presheaf.stalk y) L)
        (_ : IsScalarTower ((pullback p s).presheaf.stalk y) K L),
        IsTameAlgebra ((pullback p s).presheaf.stalk y) (K := K) L ∧
        Nonempty (((Scheme.etalePullback κ).obj F).obj ≅ yoneda.obj (etaleSpec K L))

/-- XIII 2.1.1: a sheaf of sets `F` on `U = X - Y` is tamely ramified along `Y` relative to `S`
if it satisfies `IsTamelyRamifiedSheafAt` at every geometric point `s̄` of `S`: for every maximal
point `y` of the geometric fiber `Y_s̄`, the restriction of `F` to the field of fractions `K` of
the local ring `O_{X_s̄, y}` is represented by `Spec L` for an étale `K`-algebra `L` tamely
ramified over `O_{X_s̄, y}`. -/
def IsTamelyRamifiedSheaf (F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
    IsTamelyRamifiedSheafAt p Y U F Ω s

variable {p Y U} in
/-- The condition of XIII 2.1.1 at a geometric point is invariant under isomorphisms of
sheaves. -/
theorem IsTamelyRamifiedSheafAt.of_iso {F G : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)}
    (e : F ≅ G) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (h : IsTamelyRamifiedSheafAt p Y U F Ω s) : IsTamelyRamifiedSheafAt p Y U G Ω s := by
  intro y hy K _ _ _ κ hκ
  obtain ⟨L, _, _, _, _, _, hL, ⟨i⟩⟩ := h y hy K κ hκ
  exact ⟨L, _, _, _, _, _, hL,
    ⟨(sheafToPresheaf _ _).mapIso ((Scheme.etalePullback κ).mapIso e.symm) ≪≫ i⟩⟩

variable {p Y U} in
/-- Tame ramification (XIII 2.1.1) is invariant under isomorphisms of sheaves. -/
theorem IsTamelyRamifiedSheaf.of_iso {F G : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)}
    (e : F ≅ G) (h : IsTamelyRamifiedSheaf p Y U F) : IsTamelyRamifiedSheaf p Y U G :=
  fun Ω _ _ s ↦ (h Ω s).of_iso e

/-- XIII 2.1.1 for an étale covering `V` of `U`: `V` is tamely ramified along `Y` relative to `S`
if the sheaf it represents is. -/
def IsTamelyRamifiedCovering (V : (U : Scheme.{u}).Etale) : Prop :=
  IsTamelyRamifiedSheaf p Y U ((Scheme.etaleYoneda U).obj V)

/-- XIII 2.1.2: for a sheaf of groups `G` on `U`, `H¹_tame(U, G)` is the subset of `H¹(U, G)`
formed by the classes of torsors under `G` which are tamely ramified along `Y` relative to `S`. -/
def H1Tame (G : (U : Scheme.{u}).Etaleᵒᵖ ⥤ GrpCat.{u}) :
    Set (H1 (U : Scheme.{u}).smallEtaleTopology G) :=
  {c | ∃ P : Torsor (U : Scheme.{u}).smallEtaleTopology G,
    P.class = c ∧ IsTamelyRamifiedSheaf p Y U P.toSheaf}

/-- A sheaf of sets on the étale site is locally constant constructible (SGA 4 IX 2.3): étale
locally it is isomorphic to a constant sheaf with finite value. This is
`AlgebraicGeometry.Scheme.IsLocallyConstantFiniteSheaf`. -/
alias IsLocallyConstantConstructible := Scheme.IsLocallyConstantFiniteSheaf

/-- `IsLocallyConstantConstructible` in terms of an étale covering family. -/
lemma isLocallyConstantConstructible_iff {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (Type u)) :
    IsLocallyConstantConstructible F ↔
      ∃ (α : Type u) (W : α → Scheme.{u}) (e : ∀ a, W a ⟶ Z), (∀ a, Etale (e a)) ∧
        (⋃ a, Set.range (e a)) = Set.univ ∧
        ∀ a, ∃ (E : Type u) (_ : Finite E),
          Nonempty ((Scheme.etalePullback (e a)).obj F ≅
            (constantSheaf (W a).smallEtaleTopology (Type u)).obj E) :=
  Scheme.isLocallyConstantFiniteSheaf_iff_exists_cover F

/-- XIII 2.3 a) (first step, SGA 4 IX 2.2): a locally constant constructible sheaf of sets is
represented by an étale covering (`exists_etaleYoneda_iso`). -/
theorem IsLocallyConstantConstructible.exists_etaleYoneda_iso {Z : Scheme.{u}}
    {F : Sheaf Z.smallEtaleTopology (Type u)} (hF : IsLocallyConstantConstructible F) :
    ∃ (V : Z.Etale) (_ : IsFinite V.hom), Nonempty ((Scheme.etaleYoneda Z).obj V ≅ F) :=
  ExposeXIII.exists_etaleYoneda_iso hF

variable {p Y U} in
/-- For a sheaf `F` represented by an étale covering `V` of `U`, `F` is tamely ramified along `Y`
if and only if `V` is. -/
theorem isTamelyRamifiedSheaf_iff_isTamelyRamifiedCovering
    {F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)} {V : (U : Scheme.{u}).Etale}
    (e : (Scheme.etaleYoneda U).obj V ≅ F) :
    IsTamelyRamifiedSheaf p Y U F ↔ IsTamelyRamifiedCovering p Y U V :=
  ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

variable {p Y U} in
/-- The sheaves of condition b) of XIII 2.4 (locally constant constructible and tamely ramified
along `Y`) are those represented by tamely ramified étale coverings of `U` (SGA 4 IX 2.2,
`fetEquivLocallyConstantFiniteSheaf`). -/
theorem isLocallyConstantConstructible_and_isTamelyRamifiedSheaf_iff
    (F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)) :
    IsLocallyConstantConstructible F ∧ IsTamelyRamifiedSheaf p Y U F ↔
      ∃ (V : (U : Scheme.{u}).Etale) (_ : IsFinite V.hom), IsTamelyRamifiedCovering p Y U V ∧
        Nonempty ((Scheme.etaleYoneda U).obj V ≅ F) := by
  constructor
  · rintro ⟨hF, ht⟩
    obtain ⟨V, hV, ⟨e⟩⟩ := hF.exists_etaleYoneda_iso
    exact ⟨V, hV, (isTamelyRamifiedSheaf_iff_isTamelyRamifiedCovering e).mp ht, ⟨e⟩⟩
  · rintro ⟨V, hV, ht, ⟨e⟩⟩
    exact ⟨(Scheme.isLocallyConstantFiniteSheaf_etaleYoneda V).of_iso e,
      (isTamelyRamifiedSheaf_iff_isTamelyRamifiedCovering e).mpr ht⟩

/-- XIII 2.3 a) (statement only): for a locally constant constructible sheaf `F` on `U`, it
suffices to check the condition of XIII 2.1.1 at the geometric points of `S` over the maximal
points of `S`. SGA reduces to strictly normal crossings, represents `F` by an étale covering `V`
(`IsLocallyConstantConstructible.exists_etaleYoneda_iso`) and applies the relative Abhyankar
lemma XIII.5.5 (not formalized) to `V` over the strict localizations of `X`. -/
def TameRamificationAtMaximalPointsStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (p : X ⟶ S) (Y : Set X) (U : X.Opens), IsNormalCrossingsSupport p Y →
    (U : Set X) = Yᶜ → ∀ F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u),
      IsLocallyConstantConstructible F →
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        IsMaximalPointOf Set.univ (s (IsLocalRing.closedPoint Ω)) →
          IsTamelyRamifiedSheafAt p Y U F Ω s) →
      IsTamelyRamifiedSheaf p Y U F

/-- Condition a) of XIII 2.4 for a sheaf of sets `F` on `U`: locally for the étale topology on
`X` and on `S`, `F` is the inverse image of a sheaf of sets on `S`. That is, there are étale
surjective morphisms `t : S₁ ⟶ S` and `q : X₂ ⟶ X ×_S S₁` and a sheaf `G` on `S₁` such that
the inverse images of `F` and `G` on `U₂ = U ×_X X₂` are isomorphic. -/
def IsLocallyInverseImageFromBase (F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u)) :
    Prop :=
  ∃ (S₁ : Scheme.{u}) (t : S₁ ⟶ S) (_ : Etale t) (_ : Surjective t) (X₂ : Scheme.{u})
    (q : X₂ ⟶ pullback p t) (_ : Etale q) (_ : Surjective q)
    (G : Sheaf S₁.smallEtaleTopology (Type u)),
    Nonempty ((Scheme.etalePullback (pullback.fst U.ι (q ≫ pullback.fst p t))).obj F ≅
      (Scheme.etalePullback
        (pullback.snd U.ι (q ≫ pullback.fst p t) ≫ q ≫ pullback.snd p t)).obj G)

end TameSheaves

section MainTheorem

/-- XIII 2.4 1), case of sheaves of sets (statement only): let `Y` be the support of a divisor
with normal crossings relative to `S` in `X`, `U = X - Y`, and `F` a sheaf of sets on `U`
satisfying a) (étale locally on `X` and `S` the inverse image of a sheaf on `S`) or b) (locally
constant constructible and tamely ramified along `Y` relative to `S`). Then `(F, i)` is
cohomologically proper relative to `S` in dimension `≤ 0`, for `i : U ⟶ X` the inclusion. -/
def TameBaseChangeStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (p : X ⟶ S) (Y : Set X) (U : X.Opens), IsNormalCrossingsSupport p Y →
    (U : Set X) = Yᶜ → ∀ F : Sheaf (U : Scheme.{u}).smallEtaleTopology (Type u),
      (IsLocallyInverseImageFromBase p U F ∨
        (IsLocallyConstantConstructible F ∧ IsTamelyRamifiedSheaf p Y U F)) →
      IsCohomologicallyProperLEZero p U.ι F

end MainTheorem

end SGA.SGA1.ExposeXIII
