/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Topology.KrullDimension

/-!
# SGA 1, Exposé II, §2: criteria of smoothness

The main criterion is II.2.1: a morphism locally of finite type (here: of finite presentation)
is smooth at `x` iff it is flat at `x` and its fibre is smooth at `x`. Mathlib proves the global
form (`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`); we deduce the equivalence
for schemes, and prove the pointwise statement for algebras, where the fibre at `q` is
`κ(p) ⊗_R S_q`. For schemes we also prove that smoothness at a point is stable under base change
(II.1.3 (ii), pointwise), in particular that the fibre of `f` at `x` is smooth at `x` if `f` is.

II.2.2 is in `SGA.SGA1.ExposeII.FibrewiseCriterion`. II.2.3 uses SGA's notion of equidimensional
morphism (`IsEquidimensionalAt`, defined here); it is proved in `SGA.SGA1.ExposeII.Equidimensional`
(affine form) and `SGA.SGA1.ExposeII.EquidimensionalScheme` (for schemes). Not formalized: the
remarks II.2.4 and Hironaka's result II.2.5 with its corollary II.2.6.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeII

section Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- II.2.1, necessity: a smooth morphism is flat (mathlib). -/
theorem flat_of_smooth [Smooth f] : Flat f := inferInstance

/-- II.2.1, necessity: the fibres of a smooth morphism are smooth. -/
instance smooth_fiberToSpecResidueField [Smooth f] (y : Y) :
    Smooth (f.fiberToSpecResidueField y) :=
  inferInstanceAs (Smooth (pullback.snd _ _))

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibres of a morphism locally of finite presentation are locally of finite
presentation over the residue fields. -/
instance locallyOfFinitePresentation_fiberToSpecResidueField [LocallyOfFinitePresentation f]
    (y : Y) : LocallyOfFinitePresentation (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- II.1.3 (ii), pointwise, for schemes: smoothness at a point is stable under base change: for a
cartesian square with `Y' = Y ×_S S'`, if `Y` is smooth over `S` at the image of `y'`, then `Y'` is
smooth over `S'` at `y'`. -/
theorem mem_smoothLocus_of_isPullback {Y' S' Y S : Scheme.{u}} {f' : Y' ⟶ S'} {g' : Y' ⟶ Y}
    {g : S' ⟶ S} {f : Y ⟶ S} (h : IsPullback f' g' g f) [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation f'] {y' : Y'} (hy : g' y' ∈ f.smoothLocus) :
    y' ∈ f'.smoothLocus := by
  set V := f.smoothLocus
  have hV : Smooth (V.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self V
  have hsq := (isPullback_morphismRestrict g' V).flip.paste_horiz h
  have : Smooth ((g' ⁻¹ᵁ V).ι ≫ f') := MorphismProperty.of_isPullback hsq.flip hV
  have htop := ((g' ⁻¹ᵁ V).ι ≫ f').smoothLocus_eq_top
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  have hy' : (⟨y', hy⟩ : g' ⁻¹ᵁ V) ∈ (g' ⁻¹ᵁ V).ι ⁻¹ᵁ f'.smoothLocus := htop ▸ trivial
  exact hy'

/-- II.2.1, necessity, pointwise: if `f` is smooth at `x`, its fibre `f⁻¹(f(x))` is smooth over
`κ(f(x))` at `x`. -/
theorem asFiber_mem_smoothLocus [LocallyOfFinitePresentation f] {x : X}
    (hx : x ∈ f.smoothLocus) :
    f.asFiber x ∈ (f.fiberToSpecResidueField (f x)).smoothLocus := by
  refine mem_smoothLocus_of_isPullback (IsPullback.of_hasPullback f _).flip ?_
  change f.fiberι _ (f.asFiber x) ∈ _
  rwa [Scheme.Hom.fiberι_asFiber]

/-- II.2.1, global form: a morphism locally of finite presentation is smooth iff it is flat
with smooth fibres. -/
theorem smooth_iff_flat_and_smooth_fiber [LocallyOfFinitePresentation f] :
    Smooth f ↔ Flat f ∧ ∀ y, Smooth (f.fiberToSpecResidueField y) :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ ↦ inferInstance⟩,
    fun ⟨_, h⟩ ↦ Smooth.of_smooth_fiberToSpecResidueField f h⟩

/-- II.2 (the "recalled" definition before II.2.3): `f` is *equidimensional* at `x` if there is
an open neighbourhood `U` of `x` every irreducible component of which dominates an irreducible
component of `Y`, such that the irreducible components of all the fibres `f⁻¹(y') ∩ U` have one
and the same dimension. -/
def IsEquidimensionalAt (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧
    (∀ Z ∈ irreducibleComponents U,
      closure (f '' (Subtype.val '' Z)) ∈ irreducibleComponents Y) ∧
    ∃ d : ℕ, ∀ y' : Y, ∀ C ∈ irreducibleComponents ↥(f ⁻¹' {y'} ∩ (U : Set X)),
      topologicalKrullDim C = d

end Scheme

section Algebra

open Algebra TensorProduct IsLocalRing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local notation "𝓀[" R "]" => ResidueField R

/-- II.2.1, pointwise affine form, necessity: if `S` is smooth over `R` at `q`, then `S_q` is flat
over `R`. -/
theorem IsSmoothAt.flat_localization [FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [IsSmoothAt R q] : Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨f, hfq, _⟩ := IsSmoothAt.exists_notMem_smooth R q
  let g : Localization.Away f →ₐ[S] Localization.AtPrime q :=
    IsLocalization.liftAlgHom (M := .powers f) (f := Algebra.ofId _ _) (by
      rintro ⟨_, n, rfl⟩
      exact IsLocalization.map_units (M := q.primeCompl) _
        ⟨f ^ n, q.primeCompl.pow_mem hfq n⟩)
  algebraize [g.toRingHom]
  have : IsScalarTower R (Localization.Away f) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f) q.primeCompl)
      (Localization.AtPrime q) :=
    .isLocalization_of_submonoid_le _ _ (.powers f) _ (by
      rintro _ ⟨n, rfl⟩
      exact q.primeCompl.pow_mem hfq n)
  have : Module.Flat (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.flat _ (Algebra.algebraMapSubmonoid (Localization.Away f) q.primeCompl)
  exact .trans R (Localization.Away f) _

set_option backward.isDefEq.respectTransparency false in
/-- II.2.1, pointwise affine form: for `S` finitely presented over `R` and a prime `q` of `S`
over `p`, `S` is smooth over `R` at `q` iff `S_q` is flat over `R` and the fibre
`κ(p) ⊗_R S_q` is formally smooth over `κ(p)`. -/
theorem isSmoothAt_iff_flat_and_formallySmooth_fiber [FinitePresentation R S] (p : Ideal R)
    (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    IsSmoothAt R q ↔ Module.Flat R (Localization.AtPrime q) ∧
      FormallySmooth p.ResidueField (p.ResidueField ⊗[R] Localization.AtPrime q) := by
  refine ⟨fun _ ↦ ⟨IsSmoothAt.flat_localization q, inferInstance⟩, fun ⟨hflat, hfib⟩ ↦ ?_⟩
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr hflat
  have : FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) := by
    exact .of_equiv (Algebra.TensorProduct.equivOfCompatibleSMul Rp R _ _ _)
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

end Algebra

end SGA.SGA1.ExposeII
