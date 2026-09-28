/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.AnalyticSpace
import SGA.Foundations.Analytic.Stalk
import SGA.Foundations.Analytic.Noetherian
import SGA.Foundations.Analytic.Henselian
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Analysis.Complex.Basic
import SGA.SGA1.ExposeXII.Points
import SGA.SGA1.ExposeXII.HenselianQuotient

/-!
# SGA 1, Exposé XII, 1.1 and 2.1: the analytic space of an affine scheme

For `A = 𝕜[x₁, …, xₙ]/(g₁, …, g_k)` (`𝕜 = ℂ`, or any complete nontrivially normed field), the
analytic space `X^an` of `X = Spec A` is the local model `Z(g) ⊆ 𝕜ⁿ` with structure sheaf
`(𝒪_{𝕜ⁿ}/(g))|_{Z(g)}` (`AnalyticGeometry.analytification`, with its canonical morphism
`φ : X^an → X`, `AnalyticGeometry.toSpec`). Here:

* XII.1.1: the underlying space `Z(g)` is the space `X(𝕜)` of `𝕜`-points of `X`
  (`AffineAnalytification.pointsHomeomorph`), and `φ` sends a point to its maximal ideal
  (`toSpec_base_pointsHomeomorph`); for any finitely presented `A` (e.g. of finite type over
  `ℂ`), `affineAnalytification 𝕜 A` is the analytic space of a chosen presentation, with
  `affineToSpec` and `affinePointsHomeomorph`; it does not depend on the presentation
  (`affineAnalytificationIso`), and it has the universal property of XII.1.1 with respect to local
  models (`existsUnique_comp_affineToSpec`). The structure sheaf is not reduced in general; the
  reduced analytic space (the sheaf of analytic functions on `X(ℂ)`) is `Analytic.lean`, compared
  with `X^an` in `ReducedComparison.lean`.
* XII.1.2, affine case: a homomorphism `A → B` induces `Spec(B)^an → Spec(A)^an`
  (`affineAnalytificationMap`), functorially and compatibly with `φ`
  (`affineAnalytificationMap_comp_affineToSpec`).
* XII.2.1, local rings: `𝒪_{X^an, x}` is a noetherian henselian local ring
  (`isNoetherianRing_stalk`, `henselianLocalRing_stalk`, as a quotient of the ring of convergent
  power series) with residue field `𝕜` (`residueFieldEquiv`), and `A → 𝒪_{X^an, x}` induces
  isomorphisms `A/𝔪ₓᵐ ≅ 𝒪_{X^an, x}/𝔪ᵐ` (`jetComparison`, from `SGA.Foundations.Analytic`); the
  consequences for the local rings (XII.2.1 (ii)–(vii)) are in `LocalRings.lean`.
-/


noncomputable section

open CategoryTheory Topology Set AnalyticGeometry AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace AffineAnalytification

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜)

/-- The quotient map `𝕜[x] → A = 𝕜[x]/(g)`. -/
abbrev presentation : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] PresentedAlgebra g :=
  Ideal.Quotient.mkₐ 𝕜 _

lemma range_coords : range (Points.coords (presentation g)) = (polynomialModel g).zeroSet := by
  rw [Points.range_coords (Ideal.Quotient.mkₐ_surjective 𝕜 _), polynomialModel_zeroSet]
  ext x
  have hker : RingHom.ker (presentation g) = Ideal.span (range g) := Ideal.Quotient.mkₐ_ker 𝕜 _
  simp only [mem_ofPred_eq]
  rw [hker]
  constructor
  · exact fun h i ↦ h _ (Ideal.subset_span (mem_range_self i))
  · intro h p hp
    have : Ideal.span (range g) ≤ RingHom.ker (MvPolynomial.eval x) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact h i
    exact this hp

/-- XII.1.1: the underlying space `Z(g) ⊆ 𝕜ⁿ` of `Spec(A)^an`, `A = 𝕜[x]/(g)`, is the space
`X(𝕜)` of `𝕜`-points of `X = Spec A`. -/
def pointsHomeomorph : Points 𝕜 (PresentedAlgebra g) ≃ₜ (polynomialModel g).zeroSet :=
  (Points.isClosedEmbedding_coords
    (Ideal.Quotient.mkₐ_surjective 𝕜 _)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_coords g))

@[simp] lemma coe_pointsHomeomorph (φ : Points 𝕜 (PresentedAlgebra g)) (i : Fin n) :
    (pointsHomeomorph g φ : Fin n → 𝕜) i = φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) := rfl

/-- The evaluation at the point of `Z(g)` attached to `φ ∈ X(𝕜)` is `φ`. -/
lemma evalPoint_pointsHomeomorph (φ : Points 𝕜 (PresentedAlgebra g)) :
    evalPoint (pointsHomeomorph g φ) = φ.toRingHom := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  simp only [RingHom.comp_apply, evalPoint_mk, Points.toRingHom_apply]
  exact (Points.apply_eq_eval (presentation g) φ p).symm

variable [CompleteSpace 𝕜]

/-- XII.1.1: the canonical morphism `φ : Spec(A)^an → Spec A` sends the point `x ∈ X(𝕜)` to the
maximal ideal `ker x` of `A`. -/
theorem toSpec_base_pointsHomeomorph (φ : Points 𝕜 (PresentedAlgebra g)) :
    ((toSpec g).base (pointsHomeomorph g φ)).asIdeal = RingHom.ker φ.toRingHom := by
  rw [toSpec_base_asIdeal, evalPoint_pointsHomeomorph]

variable (x : (polynomialModel g).zeroSet)

/-- The surjection `𝕜{x - a} → 𝒪_{Spec(A)^an, a}` from convergent power series centred at `a`. -/
def convergentToStalk' :
    MvPowerSeries.convergent (Fin n) 𝕜 →+* (analytification g).presheaf.stalk x :=
  ((polynomialModel g).stalkIso x).symm.toRingHom.comp
    ((Ideal.Quotient.mk _).comp (convergentStalkEquiv (x : Fin n → 𝕜)).toRingHom)

lemma surjective_convergentToStalk' : Function.Surjective (convergentToStalk' g x) :=
  ((polynomialModel g).stalkIso x).symm.surjective.comp
    (Ideal.Quotient.mk_surjective.comp (convergentStalkEquiv (x : Fin n → 𝕜)).surjective)

/-- XII.2.1: the local ring `𝒪_{X^an, x}` is noetherian (a quotient of the ring of convergent power
series). -/
instance isNoetherianRing_stalk : IsNoetherianRing ((analytification g).presheaf.stalk x) :=
  isNoetherianRing_of_surjective _ _ _ (surjective_convergentToStalk' g x)

/-- XII.2.1: the local ring `𝒪_{X^an, x}` is henselian (a quotient of the henselian ring of
convergent power series). -/
instance henselianLocalRing_stalk : HenselianLocalRing ((analytification g).presheaf.stalk x) :=
  have := (analytification g).isLocalRing x
  henselianLocalRing_of_surjective _ (surjective_convergentToStalk' g x)

/-- Evaluation at `x`: `𝒪_{X^an, x} → 𝕜`. -/
def evalStalk' : (analytification g).presheaf.stalk x →+* 𝕜 :=
  ((polynomialModel g).evalFiber x).comp ((polynomialModel g).stalkIso x).toRingHom

lemma surjective_evalStalk' : Function.Surjective (evalStalk' g x) := fun c ↦
  ⟨((polynomialModel g).stalkIso x).symm
    ((polynomialModel g).classOf x (fun _ ↦ c) analyticAt_const), by
    change (polynomialModel g).evalFiber x ((polynomialModel g).stalkIso x
      (((polynomialModel g).stalkIso x).symm _)) = c
    rw [RingEquiv.apply_symm_apply, LocalModelData.evalFiber_classOf]⟩

lemma ker_evalStalk' :
    RingHom.ker (evalStalk' g x) =
      IsLocalRing.maximalIdeal ((analytification g).presheaf.stalk x) := by
  have := (analytification g).isLocalRing x
  ext t
  have hu : IsUnit t ↔ IsUnit ((polynomialModel g).stalkIso x t) :=
    (MulEquiv.isUnit_map ((polynomialModel g).stalkIso x).toMulEquiv).symm
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu,
    LocalModelData.isUnit_fiber_iff, not_not]
  rfl

/-- XII.2.1: the residue field of `𝒪_{X^an, x}` is `𝕜`. -/
def residueFieldEquiv :
    IsLocalRing.ResidueField ((analytification g).presheaf.stalk x) ≃+* 𝕜 :=
  have := (analytification g).isLocalRing x
  (Ideal.quotEquivOfEq (ker_evalStalk' g x).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_evalStalk' g x))

/-- XII.2.1, comparison of jets: for `A = 𝕜[x]/(g)` and a point `x ∈ X(𝕜)` with maximal ideal
`𝔪ₓ ⊆ A`, the canonical homomorphism `A → 𝒪_{X^an, x}` (`stalkGermHom`) induces isomorphisms
`A/𝔪ₓᵐ ≅ 𝒪_{X^an, x}/𝔪ᵐ` for all `m`; equivalently `𝒪_{X, x} → 𝒪_{X^an, x}` induces an
isomorphism of completions. -/
theorem jetComparison (m : ℕ) :
    Function.Bijective (Ideal.quotientMap
      (IsLocalRing.maximalIdeal ((analytification g).presheaf.stalk x) ^ m) (stalkGermHom g x)
      (ker_evalPoint_pow_le_comap g x m)) :=
  bijective_quotientMap_stalkGermHom g x m _

section FinitePresentation

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] (A : Type) [CommRing A] [Algebra 𝕜 A]
  [Algebra.FinitePresentation 𝕜 A]

/-- A finitely presented `𝕜`-algebra is isomorphic to some `𝕜[x₁, …, xₙ]/(g₁, …, g_k)`. -/
lemma exists_presentedAlgebra_algEquiv : ∃ (n k : ℕ) (g : Fin k → MvPolynomial (Fin n) 𝕜),
    Nonempty (PresentedAlgebra g ≃ₐ[𝕜] A) := by
  obtain ⟨n, I, e, hI⟩ := Algebra.FinitePresentation.iff.mp ‹_›
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  exact ⟨n, k, g, ⟨(Ideal.quotientEquivAlgOfEq 𝕜 hg).trans e⟩⟩

/-- The number of variables of the chosen presentation of `A`. -/
def presentationVars : ℕ := (exists_presentedAlgebra_algEquiv 𝕜 A).choose

/-- The number of equations of the chosen presentation of `A`. -/
def presentationEqns : ℕ := (exists_presentedAlgebra_algEquiv 𝕜 A).choose_spec.choose

/-- The equations of the chosen presentation `A ≅ 𝕜[x]/(g)`. -/
def presentationPolys : Fin (presentationEqns 𝕜 A) → MvPolynomial (Fin (presentationVars 𝕜 A)) 𝕜 :=
  (exists_presentedAlgebra_algEquiv 𝕜 A).choose_spec.choose_spec.choose

/-- The chosen presentation `𝕜[x]/(g) ≅ A`. -/
def presentationEquiv : PresentedAlgebra (presentationPolys 𝕜 A) ≃ₐ[𝕜] A :=
  (exists_presentedAlgebra_algEquiv 𝕜 A).choose_spec.choose_spec.choose_spec.some

variable [CompleteSpace 𝕜]

/-- XII.1.1: the analytic space `X^an` of `X = Spec A`, `A` finitely presented over `𝕜` (for
instance `𝕜 = ℂ`, `A` of finite type), as a locally ringed space: the local model defined by a
chosen presentation. Its structure sheaf is not assumed reduced. -/
abbrev affineAnalytification : LocallyRingedSpace :=
  analytification (presentationPolys 𝕜 A)

/-- XII.1.1: the canonical morphism `φ : X^an → X = Spec A`. -/
def affineToSpec :
    affineAnalytification 𝕜 A ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of A) :=
  toSpec (presentationPolys 𝕜 A) ≫
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (presentationEquiv 𝕜 A).symm.toRingHom)

/-- XII.1.1: the underlying space of `X^an` is `X(𝕜)`. -/
def affinePointsHomeomorph : Points 𝕜 A ≃ₜ (polynomialModel (presentationPolys 𝕜 A)).zeroSet :=
  (Points.homeomorph (presentationEquiv 𝕜 A)).trans (pointsHomeomorph _)

/-- XII.1.1, independence of the presentation: for any presentation `A ≅ 𝕜[x]/(g)`, the analytic
space `Spec(A)^an` is isomorphic to the local model `Z(g)`, compatibly with the canonical
morphisms to `Spec A` (`affineAnalytificationIso_hom_comp_toSpec`). -/
def affineAnalytificationIso {n k : ℕ} (g : Fin k → MvPolynomial (Fin n) 𝕜)
    (e : PresentedAlgebra g ≃ₐ[𝕜] A) : affineAnalytification 𝕜 A ≅ analytification g :=
  analytificationIso ((presentationEquiv 𝕜 A).trans e.symm)

lemma affineAnalytificationIso_hom_comp_toSpec {n k : ℕ} (g : Fin k → MvPolynomial (Fin n) 𝕜)
    (e : PresentedAlgebra g ≃ₐ[𝕜] A) :
    (affineAnalytificationIso 𝕜 A g e).hom ≫ toSpec g ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom e.symm.toRingHom) = affineToSpec 𝕜 A := by
  rw [affineAnalytificationIso, analytificationIso, ← Category.assoc,
    analytificationMap_comp_toSpec, Category.assoc, ← Spec.locallyRingedSpaceMap_comp,
    affineToSpec]
  congr 2
  ext a
  simp

variable {𝕜 A} {B C : Type} [CommRing B] [Algebra 𝕜 B] [Algebra.FinitePresentation 𝕜 B]
  [CommRing C] [Algebra 𝕜 C] [Algebra.FinitePresentation 𝕜 C]

/-- The homomorphism between the chosen presentations induced by `e : A → B`. -/
def presentedHom (e : A →ₐ[𝕜] B) :
    PresentedAlgebra (presentationPolys 𝕜 A) →ₐ[𝕜] PresentedAlgebra (presentationPolys 𝕜 B) :=
  ((presentationEquiv 𝕜 B).symm.toAlgHom.comp e).comp (presentationEquiv 𝕜 A).toAlgHom

/-- XII.1.2 (affine case): a `𝕜`-algebra homomorphism `e : A → B` of finitely presented algebras,
i.e. a morphism `Spec B → Spec A`, induces a morphism `Spec(B)^an → Spec(A)^an`. -/
def affineAnalytificationMap (e : A →ₐ[𝕜] B) :
    affineAnalytification 𝕜 B ⟶ affineAnalytification 𝕜 A :=
  analytificationMap _ _ (presentedHom e)

lemma affineAnalytificationMap_id :
    affineAnalytificationMap (AlgHom.id 𝕜 A) = 𝟙 (affineAnalytification 𝕜 A) := by
  rw [affineAnalytificationMap]
  convert analytificationMap_id _
  ext a
  simp [presentedHom]

lemma affineAnalytificationMap_comp (e₁ : A →ₐ[𝕜] B) (e₂ : B →ₐ[𝕜] C) :
    affineAnalytificationMap (e₂.comp e₁) =
      affineAnalytificationMap e₂ ≫ affineAnalytificationMap e₁ := by
  rw [affineAnalytificationMap, affineAnalytificationMap, affineAnalytificationMap,
    ← analytificationMap_comp]
  congr 1
  ext a
  simp [presentedHom]

/-- XII.1.2 (affine case): the square formed by `f^an`, `f` and the canonical morphisms `φ`
commutes. -/
theorem affineAnalytificationMap_comp_affineToSpec (e : A →ₐ[𝕜] B) :
    affineAnalytificationMap e ≫ affineToSpec 𝕜 A =
      affineToSpec 𝕜 B ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom e.toRingHom) := by
  rw [affineAnalytificationMap, affineToSpec, ← Category.assoc, analytificationMap_comp_toSpec,
    Category.assoc, ← Spec.locallyRingedSpaceMap_comp, affineToSpec, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp]
  congr 2
  ext a
  simp [presentedHom]

variable (𝕜 A)

/-- XII.1.1, universal property of `X^an` (affine `X`, tested on local models): for a local model
`Y ⊆ 𝕜^{n'}` and a `𝕜`-algebra homomorphism `φ : A → Γ(Y, 𝒪_Y)` (i.e. a `𝕜`-morphism
`Y → Spec A`), there is a unique `𝕜`-linear morphism `f : Y → Spec(A)^an` with `φ_X ∘ f` the
morphism defined by `φ`. -/
theorem existsUnique_comp_affineToSpec {n' : ℕ} (D' : LocalModelData 𝕜 (Fin n' → 𝕜))
    (φ : A →+* D'.presheaf.obj (Opposite.op ⊤))
    (hφ : φ.comp (algebraMap 𝕜 A) = D'.constSectionHom ⊤) :
    ∃! f : D'.toLocallyRingedSpace ⟶ affineAnalytification 𝕜 A, LocalModelData.IsKLinear f ∧
      f ≫ affineToSpec 𝕜 A = D'.toLocallyRingedSpace.toΓSpec ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) := by
  let p := presentationEquiv 𝕜 A
  let ψ : PresentedAlgebra (presentationPolys 𝕜 A) →+* D'.presheaf.obj (Opposite.op ⊤) :=
    φ.comp p.toRingHom
  have hψ' : ψ.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤ := by
    rw [← hφ]
    ext c
    simp [ψ]
  have hψ : Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ) =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom) :=
    Spec.locallyRingedSpaceMap_comp (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom φ)
  have hinv : Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom) ≫
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom) = 𝟙 _ := by
    rw [← Spec.locallyRingedSpaceMap_comp, ← Spec.locallyRingedSpaceMap_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ p.symm_apply_apply a)
  have hinv' : Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom) ≫
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.locallyRingedSpaceMap_comp, ← Spec.locallyRingedSpaceMap_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ p.apply_symm_apply a)
  have key (f : D'.toLocallyRingedSpace ⟶ affineAnalytification 𝕜 A) :
      f ≫ affineToSpec 𝕜 A = D'.toLocallyRingedSpace.toΓSpec ≫
          Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) ↔
        f ≫ toSpec (presentationPolys 𝕜 A) = D'.toLocallyRingedSpace.toΓSpec ≫
          Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ) := by
    erw [hψ]
    change f ≫ toSpec _ ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom) = _ ↔ _
    constructor
    · intro h
      have := congrArg (· ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom)) h
      simp only [Category.assoc, hinv, Category.comp_id] at this
      exact this
    · intro h
      calc f ≫ toSpec _ ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom)
          = (f ≫ toSpec _) ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom) :=
            (Category.assoc _ _ _).symm
        _ = (D'.toLocallyRingedSpace.toΓSpec ≫ (Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) ≫
              Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom))) ≫
              Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom) :=
            congrArg (· ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom)) h
        _ = D'.toLocallyRingedSpace.toΓSpec ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) ≫
              (Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.toRingHom) ≫
                Spec.locallyRingedSpaceMap (CommRingCat.ofHom p.symm.toRingHom)) := by
            simp only [Category.assoc]
        _ = _ := by rw [hinv', Category.comp_id]
  obtain ⟨f, ⟨hf, hfψ⟩, huniq⟩ := LocalModelData.existsUnique_comp_toSpec (g :=
    presentationPolys 𝕜 A) (D' := D') ψ hψ'
  exact ⟨f, ⟨hf, (key f).mpr hfψ⟩, fun f' ⟨hf', hf'φ⟩ ↦ huniq f' ⟨hf', (key f').mp hf'φ⟩⟩

end FinitePresentation

end AffineAnalytification

end SGA.SGA1.ExposeXII
