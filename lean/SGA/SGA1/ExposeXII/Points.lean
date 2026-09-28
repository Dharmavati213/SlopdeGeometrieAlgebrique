/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Field
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# SGA 1, Exposé XII, §1: the points of the analytic space of an affine scheme

For a scheme `X` locally of finite type over `ℂ`, XII.1.1 constructs an analytic space `X^an`
whose underlying set is `X(ℂ)`. Mathlib has no complex analytic spaces; this file builds the
underlying topological space in the affine case, over any topological ring `K`.

For a `K`-algebra `A`, `Points K A` is the set `X(K)` of `K`-points of `X = Spec A`, with the
coarsest topology making the functions `x ↦ a(x)` continuous. For a presentation
`K[x₁, …, xₙ]/I ≅ A` it is the zero set of `I` in `Kⁿ` with the subspace topology
(`isClosedEmbedding_coords`); in particular it does not depend on the presentation. Morphisms
give continuous maps (XII.1.2), closed immersions give closed embeddings and basic open
immersions give open embeddings (the steps of XII.1.1 a)).
-/

universe u v w

noncomputable section

namespace SGA.SGA1.ExposeXII

open Topology Set

variable (K : Type u) [CommRing K]
variable (A : Type v) [CommRing A] [Algebra K A]

/-- XII.1.1: the set `X(K)` of `K`-points of `X = Spec A`, i.e. the `K`-algebra maps `A → K`. -/
def Points : Type (max u v) := A →ₐ[K] K

namespace Points

instance : FunLike (Points K A) A K := inferInstanceAs (FunLike (A →ₐ[K] K) A K)

instance : AlgHomClass (Points K A) K A K := inferInstanceAs (AlgHomClass (A →ₐ[K] K) K A K)

variable {K A}

/-- A `K`-point as a `K`-algebra map. -/
def toAlgHom (φ : Points K A) : A →ₐ[K] K := φ

/-- A `K`-algebra map as a `K`-point. -/
def ofAlgHom (φ : A →ₐ[K] K) : Points K A := φ

@[simp] lemma toAlgHom_apply (φ : Points K A) (a : A) : φ.toAlgHom a = φ a := rfl
@[simp] lemma ofAlgHom_apply (φ : A →ₐ[K] K) (a : A) : ofAlgHom φ a = φ a := rfl
@[simp] lemma ofAlgHom_toAlgHom (φ : Points K A) : ofAlgHom φ.toAlgHom = φ := rfl
@[simp] lemma toAlgHom_ofAlgHom (φ : A →ₐ[K] K) : (ofAlgHom φ).toAlgHom = φ := rfl

/-- A point as a ring map. -/
def toRingHom (φ : Points K A) : A →+* K := φ.toAlgHom.toRingHom

@[simp] lemma toRingHom_apply (φ : Points K A) (a : A) : φ.toRingHom a = φ a := rfl

@[ext] lemma ext {φ ψ : Points K A} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext _ _ h

@[simp] lemma apply_algebraMap (φ : Points K A) (c : K) : φ (algebraMap K A c) = c :=
  φ.toAlgHom.commutes c

variable {B : Type w} [CommRing B] [Algebra K B]

/-- The map `Y(K) → X(K)` induced by a morphism `Y = Spec B → X = Spec A`. -/
def map (f : A →ₐ[K] B) (ψ : Points K B) : Points K A := ψ.toAlgHom.comp f

@[simp] lemma map_apply (f : A →ₐ[K] B) (ψ : Points K B) (a : A) : map f ψ a = ψ (f a) := rfl

@[simp] lemma map_id : map (AlgHom.id K A) = id := rfl

lemma map_comp {C : Type*} [CommRing C] [Algebra K C] (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    map (g.comp f) = map f ∘ map g := rfl

variable (A B) in
/-- The map `Y(K) → X(K)` induced by the structure morphism `Y = Spec B → X = Spec A` of an
`A`-algebra `B`. -/
abbrev proj [Algebra A B] [IsScalarTower K A B] : Points K B → Points K A :=
  map (IsScalarTower.toAlgHom K A B)

lemma proj_apply [Algebra A B] [IsScalarTower K A B] (ψ : Points K B) (a : A) :
    proj A B ψ a = ψ (algebraMap A B a) := rfl

/-- The fibre of `Y(K) → X(K)` over `φ` consists of the ring maps `B → K` extending `φ`. -/
def ofRingHomOver [Algebra A B] [IsScalarTower K A B] (φ : Points K A) (χ : B →+* K)
    (hχ : χ.comp (algebraMap A B) = φ.toAlgHom.toRingHom) : Points K B :=
  ofAlgHom
    { χ with
      commutes' := fun c ↦ by
        change χ (algebraMap K B c) = c
        rw [IsScalarTower.algebraMap_apply K A B, ← RingHom.comp_apply, hχ]
        exact φ.toAlgHom.commutes c }

@[simp] lemma ofRingHomOver_apply [Algebra A B] [IsScalarTower K A B] (φ : Points K A)
    (χ : B →+* K) (hχ) (b : B) : ofRingHomOver φ χ hχ b = χ b := rfl

@[simp] lemma proj_ofRingHomOver [Algebra A B] [IsScalarTower K A B] (φ : Points K A)
    (χ : B →+* K) (hχ) : proj A B (ofRingHomOver φ χ hχ) = φ :=
  ext fun a ↦ congr($hχ a)

/-- The fibre of `Y(K) → X(K)` over `φ` is the set of `A`-algebra maps `B → K`, where `K` is an
`A`-algebra through `φ`. -/
def fiberEquivAlgHom [Algebra A B] [IsScalarTower K A B] (φ : Points K A) :
    (proj A B ⁻¹' {φ} : Set (Points K B)) ≃ @AlgHom A B K _ _ _ _ φ.toRingHom.toAlgebra :=
  letI : Algebra A K := φ.toRingHom.toAlgebra
  { toFun ψ := { ψ.1.toRingHom with commutes' a := congr($(ψ.2) a) }
    invFun χ := ⟨ofRingHomOver φ χ.toRingHom (RingHom.ext χ.commutes), proj_ofRingHomOver ..⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-! ### Presentations: `X(K)` as the zero set of an ideal of `K[σ]` -/

section Presentation

variable {σ : Type*} (q : MvPolynomial σ K →ₐ[K] A)

/-- The coordinates of a point with respect to a presentation `K[σ] → A`. -/
def coords (φ : Points K A) (i : σ) : K := φ (q (MvPolynomial.X i))

lemma apply_eq_eval (φ : Points K A) (p : MvPolynomial σ K) :
    φ (q p) = MvPolynomial.eval (coords q φ) p := by
  have : φ.toAlgHom.comp q = MvPolynomial.aeval (coords q φ) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [coords]
  simpa using congr($this p)

variable {q}

/-- XII.1.1: the points of `X = Spec (K[σ]/I)` are the common zeros of `I` in `K^σ`. -/
lemma range_coords (hq : Function.Surjective q) :
    range (coords q) = {x | ∀ p ∈ RingHom.ker q, MvPolynomial.eval x p = 0} := by
  ext x
  constructor
  · rintro ⟨φ, rfl⟩ p hp
    rw [← apply_eq_eval, (RingHom.mem_ker).mp hp, map_zero]
  · intro hx
    let φ : A →ₐ[K] K := AlgHom.liftOfSurjective q hq (MvPolynomial.aeval x) fun p hp ↦ by
      simpa [RingHom.mem_ker] using hx p hp
    refine ⟨ofAlgHom φ, funext fun i ↦ ?_⟩
    simp [coords, φ]

lemma adjoin_range_coords (hq : Function.Surjective q) :
    Algebra.adjoin K (range fun i ↦ q (MvPolynomial.X i)) = ⊤ := by
  rw [range_comp' q, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact hq

lemma coords_injective (hq : Function.Surjective q) : Function.Injective (coords q) :=
  fun φ ψ h ↦ ext fun a ↦ congr($(AlgHom.ext_of_adjoin_eq_top (adjoin_range_coords hq)
    (φ₁ := φ.toAlgHom) (φ₂ := ψ.toAlgHom) (by rintro _ ⟨i, rfl⟩; exact congr_fun h i)) a)

end Presentation

/-! ### Closed immersions and open immersions, on points -/

section Surjective

variable {q : A →ₐ[K] B}

lemma map_injective_of_surjective (hq : Function.Surjective q) :
    Function.Injective (map (K := K) q) := fun φ ψ h ↦
  ext fun b ↦ by obtain ⟨a, rfl⟩ := hq b; exact congr($h a)

lemma range_map_of_surjective (hq : Function.Surjective q) :
    range (map (K := K) q) = {φ | ∀ a ∈ RingHom.ker q, φ a = 0} := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩ a ha
    simp [(RingHom.mem_ker).mp ha]
  · intro h
    have H : RingHom.ker q.toRingHom ≤ RingHom.ker φ.toAlgHom.toRingHom := fun a ha ↦ by
      rw [RingHom.mem_ker] at ha ⊢; exact h a (RingHom.mem_ker.mpr ha)
    exact ⟨ofAlgHom (AlgHom.liftOfSurjective q hq φ.toAlgHom H),
      ext fun a ↦ AlgHom.liftOfSurjective_apply q hq φ.toAlgHom H a⟩

end Surjective

section Localization

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  (f : A) [IsLocalization.Away f B]
include f

lemma range_map_of_isLocalizationAway :
    range (map (K := K) (IsScalarTower.toAlgHom K A B)) = {φ | φ f ≠ 0} := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    simpa using ((IsLocalization.Away.algebraMap_isUnit f).map ψ).ne_zero
  · intro h
    refine ⟨ofAlgHom (IsLocalization.Away.liftAlgHom f (f := φ.toAlgHom) (Ne.isUnit h)),
      ext fun a ↦ ?_⟩
    simp

lemma map_injective_of_isLocalizationAway :
    Function.Injective (map (K := K) (IsScalarTower.toAlgHom K A B)) := by
  intro φ ψ h
  have : (φ.toAlgHom : B →+* K).comp (algebraMap A B) = (ψ.toAlgHom : B →+* K).comp
      (algebraMap A B) := RingHom.ext fun a ↦ congr($h a)
  exact ext fun b ↦ congr($(IsLocalization.ringHom_ext (Submonoid.powers f) this) b)

end Localization

/-! ### The topology on `X(K)` -/

variable [TopologicalSpace K]

variable (K A) in
/-- XII.1.1: the topology on `X(K)` induced by that of `K`: the coarsest topology making every
function `x ↦ a(x)`, `a ∈ A`, continuous. For `K = ℂ` and `A` of finite type this is the
topology of the analytic space `X^an` (see `isClosedEmbedding_coords`). -/
instance : TopologicalSpace (Points K A) :=
  .induced (fun φ a ↦ φ a) inferInstance

lemma continuous_apply (a : A) : Continuous fun φ : Points K A ↦ φ a :=
  (_root_.continuous_apply a).comp continuous_induced_dom

lemma continuous_iff {X : Type*} [TopologicalSpace X] {f : X → Points K A} :
    Continuous f ↔ ∀ a, Continuous fun x ↦ f x a := by
  rw [continuous_induced_rng, continuous_pi_iff]; rfl

lemma isEmbedding_coe : IsEmbedding fun φ : Points K A ↦ (φ : A → K) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

instance [T2Space K] : T2Space (Points K A) := isEmbedding_coe.t2Space

/-- XII.1.2: a morphism `Spec B → Spec A` induces a continuous map `Y(K) → X(K)`. -/
lemma continuous_map (f : A →ₐ[K] B) : Continuous (map (K := K) f) :=
  continuous_iff.mpr fun a ↦ continuous_apply (f a)

/-- XII.1.1: an isomorphism `Spec B ≅ Spec A` induces a homeomorphism `Y(K) ≃ₜ X(K)`. -/
def homeomorph (e : A ≃ₐ[K] B) : Points K B ≃ₜ Points K A where
  toFun := map e.toAlgHom
  invFun := map e.symm.toAlgHom
  left_inv ψ := ext fun b ↦ by simp
  right_inv φ := ext fun a ↦ by simp
  continuous_toFun := continuous_map _
  continuous_invFun := continuous_map _

section TopologicalRing

variable [IsTopologicalRing K]

variable (K A) in
/-- The elements of `A` whose evaluation along a family of points is continuous form a
subalgebra. -/
def continuousSubalgebra {X : Type*} [TopologicalSpace X] (f : X → Points K A) :
    Subalgebra K A where
  carrier := {a | Continuous fun x ↦ f x a}
  mul_mem' {a b} ha hb := by
    change Continuous fun x ↦ f x (a * b)
    simp_rw [map_mul]
    exact ha.mul hb
  add_mem' {a b} ha hb := by
    change Continuous fun x ↦ f x (a + b)
    simp_rw [map_add]
    exact ha.add hb
  algebraMap_mem' c := by
    change Continuous fun x ↦ f x (algebraMap K A c)
    simp_rw [apply_algebraMap]
    exact continuous_const

/-- A map into `X(K)` is continuous as soon as its composites with the evaluations at a set of
generators of `A` are continuous. -/
lemma continuous_of_adjoin_eq_top {s : Set A} (hs : Algebra.adjoin K s = ⊤)
    {X : Type*} {t : TopologicalSpace X} {f : X → Points K A}
    (h : ∀ a ∈ s, Continuous fun x ↦ f x a) : Continuous f := by
  have : Algebra.adjoin K s ≤ continuousSubalgebra K A f := Algebra.adjoin_le h
  rw [hs] at this
  exact continuous_iff.mpr fun a ↦ this Algebra.mem_top

/-- Criterion for a map out of `X(K)` to be inducing: the evaluation at each generator of `A`
factors through it by a function continuous on its range. -/
lemma isInducing_of_adjoin_eq_top {Y : Type*} [TopologicalSpace Y] {e : Points K A → Y}
    (he : Continuous e) {s : Set A} (hs : Algebra.adjoin K s = ⊤)
    (h : ∀ a ∈ s, ∃ g : Y → K, ContinuousOn g (range e) ∧ ∀ φ, φ a = g (e φ)) :
    IsInducing e := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp he) ?_⟩
  have key : ∀ a ∈ s, Continuous[.induced e ‹_›, _] fun φ : Points K A ↦ φ a := by
    let : TopologicalSpace (Points K A) := .induced e ‹_›
    intro a ha
    obtain ⟨g, hg, hga⟩ := h a ha
    simp only [hga]
    exact hg.comp_continuous continuous_induced_dom mem_range_self
  exact continuous_id_iff_le.mp (continuous_of_adjoin_eq_top (t := .induced e ‹_›) hs key)

lemma isInducing_of_forall {Y : Type*} [TopologicalSpace Y] {e : Points K A → Y}
    (he : Continuous e) (h : ∀ a, ∃ g : Y → K, ContinuousOn g (range e) ∧ ∀ φ, φ a = g (e φ)) :
    IsInducing e :=
  isInducing_of_adjoin_eq_top he (Algebra.adjoin_univ K A) fun a _ ↦ h a

variable [T2Space K]

/-- `X(K)` is a closed subset of `K^A`. -/
lemma isClosed_range_coe : IsClosed (range fun φ : Points K A ↦ (φ : A → K)) := by
  have : range (fun φ : Points K A ↦ (φ : A → K)) =
      {F | F 1 = 1} ∩ (⋂ a, ⋂ b, {F | F (a + b) = F a + F b}) ∩
        (⋂ a, ⋂ b, {F | F (a * b) = F a * F b}) ∩ ⋂ c : K, {F | F (algebraMap K A c) = c} := by
    ext F
    constructor
    · rintro ⟨φ, rfl⟩
      simp [map_add, map_mul]
    · rintro ⟨⟨⟨h1, hadd⟩, hmul⟩, halg⟩
      simp only [mem_iInter, mem_ofPred_eq] at hadd hmul halg h1
      refine ⟨ofAlgHom
        { toFun := F
          map_one' := h1
          map_mul' := hmul
          map_zero' := by simpa using halg 0
          map_add' := hadd
          commutes' := halg }, rfl⟩
  rw [this]
  have hc (a : A) : Continuous fun F : A → K ↦ F a := _root_.continuous_apply a
  refine (((isClosed_eq (hc 1) continuous_const).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (hc _) ((hc a).add (hc b))
  · exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (hc _) ((hc a).mul (hc b))
  · exact isClosed_iInter fun c ↦ isClosed_eq (hc _) continuous_const

lemma isClosedEmbedding_coe : IsClosedEmbedding fun φ : Points K A ↦ (φ : A → K) :=
  ⟨isEmbedding_coe, isClosed_range_coe⟩

/-- XII.1.1: for a presentation `K[σ] → A`, the topology of `X(K)` is the subspace topology of
the zero set of the kernel in `K^σ`; in particular it does not depend on the presentation. -/
lemma isClosedEmbedding_coords {σ : Type*} {q : MvPolynomial σ K →ₐ[K] A}
    (hq : Function.Surjective q) : IsClosedEmbedding (coords q) := by
  have hcont : Continuous (coords q) := continuous_pi fun i ↦ continuous_apply _
  refine ⟨⟨isInducing_of_adjoin_eq_top hcont (adjoin_range_coords hq) ?_,
    coords_injective hq⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun x ↦ x i, (_root_.continuous_apply i).continuousOn, fun φ ↦ rfl⟩
  · have : {x : σ → K | ∀ p ∈ RingHom.ker q, MvPolynomial.eval x p = 0} =
        ⋂ p ∈ RingHom.ker q, {x | MvPolynomial.eval x p = 0} := by
      ext; simp
    rw [range_coords hq, this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

/-- XII.1.1: if `A` is of finite type over `K`, then `X(K)` is homeomorphic to a closed subset
of some `K^n`. -/
lemma exists_isClosedEmbedding [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (e : Points K A → (Fin n → K)), IsClosedEmbedding e := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  exact ⟨n, _, isClosedEmbedding_coords hq⟩

instance [LocallyCompactSpace K] [Algebra.FiniteType K A] : LocallyCompactSpace (Points K A) :=
  have ⟨_, _, he⟩ := exists_isClosedEmbedding (K := K) (A := A)
  he.locallyCompactSpace

/-- XII.1.1 a): a closed immersion `Spec B → Spec A` induces a closed embedding
`Y(K) → X(K)`, whose image is the zero set of the ideal. -/
lemma isClosedEmbedding_map_of_surjective {q : A →ₐ[K] B} (hq : Function.Surjective q) :
    IsClosedEmbedding (map (K := K) q) := by
  refine ⟨⟨isInducing_of_forall (continuous_map q) fun b ↦ ?_,
    map_injective_of_surjective hq⟩, ?_⟩
  · obtain ⟨a, rfl⟩ := hq b
    exact ⟨fun φ ↦ φ a, (continuous_apply a).continuousOn, fun _ ↦ rfl⟩
  · have : {φ : Points K A | ∀ a ∈ RingHom.ker q, φ a = 0} =
        ⋂ a ∈ RingHom.ker q, {φ | φ a = 0} := by
      ext; simp
    rw [range_map_of_surjective hq, this]
    exact isClosed_biInter fun a _ ↦ isClosed_eq (continuous_apply a) continuous_const

end TopologicalRing

section Localization

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  [Algebra A B] [IsScalarTower K A B] (f : A) [IsLocalization.Away f B]
include f

/-- XII.1.1 a): the open immersion `D(f) → Spec A` induces an open embedding
`D(f)(K) → X(K)`, whose image is the set of points where `f` does not vanish. -/
lemma isOpenEmbedding_map_of_isLocalizationAway :
    IsOpenEmbedding (map (K := K) (IsScalarTower.toAlgHom K A B)) := by
  refine ⟨⟨isInducing_of_forall (continuous_map _) fun b ↦ ?_,
    map_injective_of_isLocalizationAway f⟩, ?_⟩
  · obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
    refine ⟨fun φ ↦ φ a * (φ f ^ n)⁻¹, ?_, fun ψ ↦ ?_⟩
    · rw [range_map_of_isLocalizationAway f]
      exact ((continuous_apply a).continuousOn).mul
        (((continuous_apply f).pow n).continuousOn.inv₀ fun φ hφ ↦ pow_ne_zero n hφ)
    · have hu : ψ (algebraMap A B f) ≠ 0 :=
        ((IsLocalization.Away.algebraMap_isUnit f).map ψ).ne_zero
      have := congr(ψ $(IsLocalization.mk'_spec B a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)))
      simp only [map_mul, map_pow] at this
      simp only [map_apply, IsScalarTower.coe_toAlgHom']
      rw [← this, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hu), mul_one]
  · rw [range_map_of_isLocalizationAway f]
    exact isOpen_compl_singleton.preimage (continuous_apply f)

omit [Algebra A B] [IsScalarTower K A B] [IsLocalization.Away f B] in
/-- `isOpenEmbedding_map_of_isLocalizationAway` for a `K`-algebra map `r : A → B` making `B` a
localization of `A` away from `f`. -/
lemma isOpenEmbedding_map_of_isLocalization (r : A →ₐ[K] B)
    (h : @IsLocalization.Away A _ f B _ r.toRingHom.toAlgebra) :
    IsOpenEmbedding (map (K := K) r) := by
  let := r.toRingHom.toAlgebra
  have : IsScalarTower K A B := .of_algebraMap_eq fun c ↦ (r.commutes c).symm
  have hr : IsScalarTower.toAlgHom K A B = r := AlgHom.ext fun _ ↦ rfl
  rw [← hr]
  exact isOpenEmbedding_map_of_isLocalizationAway f

end Localization

end Points

end SGA.SGA1.ExposeXII
