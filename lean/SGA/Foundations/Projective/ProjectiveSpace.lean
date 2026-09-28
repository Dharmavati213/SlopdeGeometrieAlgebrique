/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import SGA.Foundations.Projective.TwistingSheaf

/-!
# Projective space over a scheme

For an index type `σ` and a scheme `S`, the projective space `ℙ(σ; S)` is the base change to `S`
of `Proj ℤ[xᵢ : i ∈ σ]`, as mathlib's affine space `𝔸(σ; S)` is the base change of
`Spec ℤ[xᵢ : i ∈ σ]` (EGA II 4.1.1, where `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`).

## Main definitions and results

- `AlgebraicGeometry.ProjectiveSpace.grading σ R`: the grading of `R[xᵢ : i ∈ σ]` by total
  degree, with the `GradedAlgebra` instance.
- `AlgebraicGeometry.ProjectiveSpace σ S`, with notation `ℙ(σ; S)`, and its structure morphism
  `ℙ(σ; S) ↘ S`, which is separated, and proper for finite `σ` (EGA II 5.5.4 (i)).
- `AlgebraicGeometry.ProjectiveSpace.basicOpen S i`: the standard open subset `D₊(xᵢ)`, affine
  over `S` (EGA II 2.3.1); these cover `ℙ(σ; S)`.
- `AlgebraicGeometry.ProjectiveSpace.twistingSheaf σ S`: the line bundle `𝒪(1)` on `ℙ(σ; S)`,
  with the sections `xᵢ` (`ProjectiveSpace.coord`) whose non-vanishing loci are the `D₊(xᵢ)`,
  and more generally the sections of `𝒪(d)` defined by homogeneous polynomials of degree `d`.
- `AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_twistingSheaf`: `𝒪(1)` is ample relative
  to `ℙ(σ; S) ↘ S` when the latter is quasi-compact (EGA II 4.6.18); hence
  `ℙ(σ; S) ↘ S` is quasi-projective for finite `σ` (EGA II 5.3.1).
- `AlgebraicGeometry.ProjectiveSpace.map` and `ProjectiveSpace.isPullback_map`: projective space
  commutes with base change.
-/

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

section grading

variable (σ : Type*) (R : Type*) [CommRing R]

/-- The grading of `R[xᵢ : i ∈ σ]` by total degree. -/
def grading : ℕ → Submodule R (MvPolynomial σ R) :=
  homogeneousSubmodule σ R

instance : GradedAlgebra (grading σ R) :=
  MvPolynomial.gradedAlgebra

variable {σ R}

lemma mem_grading {n : ℕ} {p : MvPolynomial σ R} : p ∈ grading σ R n ↔ p.IsHomogeneous n :=
  mem_homogeneousSubmodule _ _

lemma X_mem_grading (i : σ) : (X i : MvPolynomial σ R) ∈ grading σ R 1 :=
  isHomogeneous_X R i

variable (σ R)

/-- The variables generate `R[xᵢ : i ∈ σ]` over its degree `0` part. -/
lemma adjoin_range_X :
    Algebra.adjoin (grading σ R 0) (Set.range (X : σ → MvPolynomial σ R)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (⟨C r, isHomogeneous_C σ r⟩ : grading σ R 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

instance [Finite σ] : Algebra.FiniteType (grading σ R 0) (MvPolynomial σ R) :=
  ⟨⟨(Set.finite_range X).toFinset, by simpa using adjoin_range_X σ R⟩⟩

/-- The degree `0` part of `R[xᵢ : i ∈ σ]` is `R`. -/
lemma bijective_algebraMap_grading_zero : Function.Bijective (algebraMap R (grading σ R 0)) := by
  refine ⟨fun r s h ↦ C_injective σ R (congrArg Subtype.val h), fun ⟨p, hp⟩ ↦ ⟨coeff 0 p, ?_⟩⟩
  refine Subtype.ext ?_
  change C (coeff 0 p) = p
  rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hp,
    ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]

/-- The basic open subsets `D₊(xᵢ)` cover `Proj R[xᵢ : i ∈ σ]`. -/
lemma iSup_basicOpen_X :
    ⨆ i, Proj.basicOpen (grading σ R) (X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _ (fun i ↦ ⟨1, X_mem_grading i⟩) (adjoin_range_X σ R)

end grading

end ProjectiveSpace

variable (σ : Type u) (S : Scheme.{u})

set_option hygiene false in
local notation3 "ℤ'" => ULift.{u} ℤ

/-- The projective space `ℙ(σ; S)` over a scheme `S`: the base change to `S` of
`Proj ℤ[xᵢ : i ∈ σ]` (EGA II 4.1.1; `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`). -/
def ProjectiveSpace : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj (ProjectiveSpace.grading σ ℤ')))

namespace ProjectiveSpace

/-- `ℙ(σ; S)` is the projective space with homogeneous coordinates indexed by `σ` over `S`. -/
scoped[AlgebraicGeometry] notation "ℙ(" σ "; " S ")" => ProjectiveSpace σ S

@[simps -isSimp]
instance over : ℙ(σ; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The projection of `ℙ(σ; S)` to `Proj ℤ[xᵢ : i ∈ σ]`. -/
def toProj : ℙ(σ; S) ⟶ Proj (grading σ ℤ') :=
  pullback.snd _ _

lemma isPullback_toProj :
    IsPullback (toProj σ S) (ℙ(σ; S) ↘ S) (terminal.from _) (terminal.from S) :=
  (IsPullback.of_hasPullback _ _).flip

section instances

set_option backward.isDefEq.respectTransparency.types false in
instance : IsIso (terminal.from (Spec (.of (grading σ ℤ' 0)))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  have : IsIso (CommRingCat.ofHom (algebraMap ℤ' (grading σ ℤ' 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_algebraMap_grading_zero σ ℤ')
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom (algebraMap ℤ' (grading σ ℤ' 0))))]
  infer_instance

lemma terminal_from_proj :
    terminal.from (Proj (grading σ ℤ')) =
      Proj.toSpecZero (grading σ ℤ') ≫ terminal.from (Spec (.of (grading σ ℤ' 0))) :=
  (terminal.comp_from _).symm

set_option backward.isDefEq.respectTransparency.types false in
instance : IsSeparated (terminal.from (Proj (grading σ ℤ'))) := by
  rw [terminal_from_proj]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance [Finite σ] : IsProper (terminal.from (Proj (grading σ ℤ'))) := by
  rw [terminal_from_proj]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance : IsSeparated (ℙ(σ; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- EGA II 5.5.4 (i): the projective space over `S` is proper over `S`. -/
instance [Finite σ] : IsProper (ℙ(σ; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ inferInstance

end instances

section basicOpen

variable {σ}

/-- The standard open subset `D₊(xᵢ)` of `ℙ(σ; S)`. -/
def basicOpen (i : σ) : ℙ(σ; S).Opens :=
  toProj σ S ⁻¹ᵁ Proj.basicOpen (grading σ ℤ') (X i)

lemma iSup_basicOpen : ⨆ i, basicOpen S i = (⊤ : ℙ(σ; S).Opens) := by
  simp only [basicOpen, ← Scheme.Hom.preimage_iSup, iSup_basicOpen_X, Scheme.Hom.preimage_top]

lemma isAffineOpen_proj_basicOpen (i : σ) :
    IsAffineOpen (Proj.basicOpen (grading σ ℤ') (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem_grading i) one_pos

/-- The standard open subset `D₊(xᵢ)` of `ℙ(σ; S)` is the base change of `D₊(xᵢ) ⊆ Proj ℤ[σ]`
to `S`. -/
lemma isPullback_basicOpen (i : σ) :
    IsPullback (toProj σ S ∣_ Proj.basicOpen (grading σ ℤ') (X i))
      ((basicOpen S i).ι ≫ ℙ(σ; S) ↘ S)
      ((Proj.basicOpen (grading σ ℤ') (X i)).ι ≫ terminal.from _) (terminal.from S) :=
  (isPullback_morphismRestrict (toProj σ S)
    (Proj.basicOpen (grading σ ℤ') (X i))).paste_vert (isPullback_toProj σ S)

set_option backward.isDefEq.respectTransparency.types false in
/-- EGA II 2.3.1: the standard open subset `D₊(xᵢ)` of `ℙ(σ; S)` is affine over `S`. -/
instance isAffineHom_basicOpen_ι_over (i : σ) : IsAffineHom ((basicOpen S i).ι ≫ ℙ(σ; S) ↘ S) := by
  have : IsAffine (Proj.basicOpen (grading σ ℤ') (X i)) := isAffineOpen_proj_basicOpen i
  exact MorphismProperty.of_isPullback (isPullback_basicOpen S i) inferInstance

end basicOpen

section twistingSheaf

/-- Serre's twisting sheaf `𝒪(1)` on `ℙ(σ; S)` (EGA II 4.1.1): the inverse image of `𝒪(1)` on
`Proj ℤ[xᵢ : i ∈ σ]`, trivialized on the `D₊(xᵢ)` with transition functions `xⱼ / xᵢ`. -/
def twistingSheaf : ℙ(σ; S).LineBundle :=
  (Proj.twistingSheaf (grading σ ℤ') X X_mem_grading (iSup_basicOpen_X σ ℤ')).pullback
    (toProj σ S)

variable {σ}

/-- The section of `𝒪(d)` on `ℙ(σ; S)` defined by a homogeneous polynomial of degree `d`. -/
def homogeneousSection {d : ℕ} {p : MvPolynomial σ ℤ'} (hp : p.IsHomogeneous d) :
    (twistingSheaf σ S).sections d :=
  (Proj.twistingSheaf.homogeneousSection X X_mem_grading (iSup_basicOpen_X σ ℤ')
    (mem_grading.mpr hp)).pullback _ (toProj σ S)

/-- The non-vanishing locus of the section of `𝒪(d)` defined by `p` is `D₊(p)`. -/
lemma nonvanishingLocus_homogeneousSection {d : ℕ} {p : MvPolynomial σ ℤ'}
    (hp : p.IsHomogeneous d) :
    (twistingSheaf σ S).nonvanishingLocus (homogeneousSection S hp) =
      toProj σ S ⁻¹ᵁ Proj.basicOpen (grading σ ℤ') p := by
  exact (Scheme.LineBundle.nonvanishingLocus_pullback _ _ _).trans
    (congrArg _ (Proj.twistingSheaf.nonvanishingLocus_homogeneousSection _ _ _ _))

/-- The homogeneous coordinate `xᵢ`, a section of `𝒪(1)`. -/
def coord (i : σ) : (twistingSheaf σ S).sections 1 :=
  homogeneousSection S (isHomogeneous_X ℤ' i)

lemma nonvanishingLocus_coord (i : σ) :
    (twistingSheaf σ S).nonvanishingLocus (coord S i) = basicOpen S i :=
  nonvanishingLocus_homogeneousSection S _

/-- EGA II 4.6.18: `𝒪(1)` is ample relative to `ℙ(σ; S) ↘ S` when the latter is quasi-compact
(e.g. `σ` is finite). -/
theorem isRelativelyAmple_twistingSheaf [QuasiCompact (ℙ(σ; S) ↘ S)] :
    (twistingSheaf σ S).IsRelativelyAmple (ℙ(σ; S) ↘ S) := by
  refine Scheme.LineBundle.isRelativelyAmple_of_isAffineHom _ (fun _ : σ ↦ 1)
    (fun _ ↦ one_pos) (coord S) (fun x ↦ ?_) (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_basicOpen S).ge (Set.mem_univ x))
    exact ⟨i, by rwa [nonvanishingLocus_coord]⟩
  · rw [nonvanishingLocus_coord]
    infer_instance

variable (σ)

/-- For finite `σ`, the projective space `ℙ(σ; S) ↘ S` is quasi-projective (EGA II 5.3.1). -/
instance [Finite σ] : IsQuasiProjective (ℙ(σ; S) ↘ S) :=
  ⟨inferInstance, inferInstance, ⟨_, isRelativelyAmple_twistingSheaf S⟩⟩

end twistingSheaf

section map

variable {σ} {S' : Scheme.{u}}

/-- The base change morphism `ℙ(σ; S') ⟶ ℙ(σ; S)` along `f : S' ⟶ S`. -/
def map (f : S' ⟶ S) : ℙ(σ; S') ⟶ ℙ(σ; S) :=
  pullback.lift (ℙ(σ; S') ↘ S' ≫ f) (toProj σ S') (by simp)

variable {S}

@[reassoc (attr := simp)]
lemma map_over (f : S' ⟶ S) : map S f ≫ ℙ(σ; S) ↘ S = ℙ(σ; S') ↘ S' ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_toProj (f : S' ⟶ S) : map S f ≫ toProj σ S = toProj σ S' :=
  pullback.lift_snd _ _ _

/-- Projective space commutes with base change: `ℙ(σ; S') = S' ×_S ℙ(σ; S)`. -/
lemma isPullback_map (f : S' ⟶ S) :
    IsPullback (map S f) (ℙ(σ; S') ↘ S') (ℙ(σ; S) ↘ S) f := by
  refine IsPullback.of_right ?_ (map_over f) (isPullback_toProj σ S)
  rw [map_toProj, terminal.comp_from]
  exact isPullback_toProj σ S'

lemma map_preimage_basicOpen (f : S' ⟶ S) (i : σ) :
    map S f ⁻¹ᵁ basicOpen S i = basicOpen S' i := by
  rw [basicOpen, ← Scheme.Hom.comp_preimage, map_toProj, basicOpen]

end map

end ProjectiveSpace

end AlgebraicGeometry
