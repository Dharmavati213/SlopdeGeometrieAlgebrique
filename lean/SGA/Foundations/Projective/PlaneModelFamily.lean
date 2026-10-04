/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.PlaneModelHypersurface
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import SGA.Foundations.Projective.PlaneModelCurve
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Projective hypersurfaces as families

Let `R` be a commutative ring and `G ∈ R[xᵢ : i ∈ σ]` homogeneous. The hypersurface
`V₊(G) = Proj (R[xᵢ] ⧸ (G))` (`AlgebraicGeometry.projHypersurface`) with its structure morphism
`ProjHypersurface.toSpec : V₊(G) ⟶ Spec R`:

* is a closed subscheme of `ℙ(σ; Spec R)` (`ProjHypersurface.embedding`,
  `ProjHypersurface.isClosedImmersion_embedding`, `ProjHypersurface.embedding_over`), hence
  proper for `σ` finite (`ProjHypersurface.isProper_toSpec`); more generally `Proj` of a
  surjective graded homomorphism is a closed immersion (`Proj.isClosedImmersion_map`);
* is integral when `R[xᵢ] ⧸ (G)` is a domain with a nonzero element of positive degree
  (`Proj.isIntegral_of_isDomain`);
* is flat over a Dedekind domain `R` when `R → R[xᵢ] ⧸ (G)` is injective and the quotient is a
  domain (`ProjHypersurface.flat_toSpec`).

## References

* [EGA II, 2.9 and 3.1] (closed subschemes of `Proj`)
* [R. Hartshorne, *Algebraic Geometry*, II.9.7] (flatness over a Dedekind base)
-/

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization AlgebraicGeometry
  ProjectiveSpace

noncomputable section

namespace HomogeneousIdeal

variable {R R' A B : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R' B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B} [GradedAlgebra 𝒜]
  [GradedAlgebra ℬ]

/-- The irrelevant ideal of the target of a surjective graded homomorphism is the image of the
irrelevant ideal of the source. -/
lemma irrelevant_le_map_of_surjective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
  intro b hb
  obtain ⟨a, rfl⟩ := hψ b
  have h : ψ (a - GradedRing.proj 𝒜 0 a) = ψ a := by
    rw [map_sub, GradedRing.proj_apply, GradedRingHom.map_directSumDecompose]
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hb
    rw [hb, sub_zero]
  rw [← h]
  refine Ideal.mem_map_of_mem _ ?_
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, map_sub,
    GradedRing.proj_apply, GradedRing.proj_apply, DirectSum.decompose_coe,
    DirectSum.of_eq_same, sub_self]

end HomogeneousIdeal

namespace AlgebraicGeometry.Proj

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R' B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B} [GradedAlgebra 𝒜]
  [GradedAlgebra ℬ]

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj` of a surjective graded homomorphism is a closed immersion** (EGA II 2.9.2 (i)):
over `D₊(s)` it is `Spec` of the surjection `A_(s) → B_(ψ s)`. -/
theorem isClosedImmersion_map (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    IsClosedImmersion (Proj.map ψ hirr) := by
  refine IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover fun i ↦ ?_
  let s : A := i.2
  have hs : s ∈ 𝒜 i.1 := i.2.2
  have hk : 0 < (i.1 : ℕ) := i.1.2
  have P1 : IsPullback (Spec.map (CommRingCat.ofHom (Away.map ψ s)))
      (awayι ℬ (ψ s) (ψ.2 hs) hk) (awayι 𝒜 s hs hk) (Proj.map ψ hirr) :=
    IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map _ _ _ _ _)
      (by rw [opensRange_awayι, opensRange_awayι]; rfl)
  have hsurj : Function.Surjective (Away.map ψ s) := by
    intro z
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective _ (ψ.2 hs) z
    obtain ⟨a, rfl⟩ := hψ b
    classical
    refine ⟨Away.mk 𝒜 hs n _ (SetLike.coe_mem (DirectSum.decompose 𝒜 a (n • (i.1 : ℕ)))), ?_⟩
    rw [Away.map_mk]
    congr 1
    rw [GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem_same _ hb]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map ψ s))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have e : pullback.snd (Proj.map ψ hirr) (awayι 𝒜 s hs hk) =
      P1.flip.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Away.map ψ s)) := by
    rw [Iso.eq_inv_comp, P1.flip.isoPullback_hom_snd]
  change IsClosedImmersion (pullback.snd (Proj.map ψ hirr) (awayι 𝒜 s hs hk))
  rw [e]
  infer_instance

/-- `Proj` of a graded domain with a nonzero homogeneous element of positive degree is
integral, with generic point the zero ideal. -/
theorem isIntegral_of_isDomain [IsDomain A] {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n)
    (hf0 : f ≠ 0) : IsIntegral (Proj 𝒜) := by
  let ξ : Proj 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        rw [HomogeneousIdeal.toIdeal_bot]
        exact Ideal.isPrime_bot
      not_irrelevant_le := fun h ↦ by
        have hX : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
          rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
            DirectSum.decompose_of_mem_ne _ hf hn.ne']
        have := h hX
        rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at this
        exact hf0 this }
  have hξ : IsGenericPoint ξ ⊤ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 ξ p).mp (bot_le (a := p.asHomogeneousIdeal))
  have : IrreducibleSpace (Proj 𝒜) := (irreducibleSpace_def _).mpr hξ.isIrreducible
  have : IsReduced (Proj 𝒜) := Proj.isReduced_of_isDomain 𝒜
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- `Proj` of a reduced graded ring is reduced: its local rings are homogeneous localizations,
which are subrings of localizations of the ring. -/
theorem isReduced_of_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  suffices ∀ x : Proj 𝒜, _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) from
    isReduced_of_isReduced_stalk _
  intro x
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let φ : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →+* Localization.AtPrime
      x.asHomogeneousIdeal.toIdeal :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  have : _root_.IsReduced (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    isReduced_of_injective φ (HomogeneousLocalization.val_injective _)
  have e := (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv
  exact isReduced_of_injective e.toRingHom e.injective

/-- The homogeneous localization `A_(s)` of a graded domain at `s ≠ 0` is a domain. -/
theorem isDomain_away [IsDomain A] {s : A} (hs : s ≠ 0) : IsDomain (Away 𝒜 s) := by
  have : IsDomain (Localization.Away s) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  let φ : Away 𝒜 s →+* Localization.Away s :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  exact Function.Injective.isDomain φ (HomogeneousLocalization.val_injective _)

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjHypersurface

variable {σ R : Type u} [CommRing R] (G : MvPolynomial σ R) {d : ℕ} (hG : G.IsHomogeneous d)

/-- The structure morphism `V₊(G) ⟶ Spec R`. -/
abbrev toSpec : projHypersurface G hG ⟶ Spec (.of R) :=
  Proj.toSpecBase _

/-- The irrelevant ideal of `R[xᵢ] ⧸ (G)` is the image of that of `R[xᵢ]`. -/
lemma irrelevant_le_map :
    HomogeneousIdeal.irrelevant (ideal G hG).quotientGrading ≤
      (HomogeneousIdeal.irrelevant (grading σ R)).map (ideal G hG).quotientGradedRingHom :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The embedding `V₊(G) ⟶ ℙ(σ; Spec R)`**: `Proj` of `R[xᵢ] → R[xᵢ] ⧸ (G)`. -/
def embedding : projHypersurface G hG ⟶ ℙ(σ; Spec (.of R)) :=
  Proj.map (ideal G hG).quotientGradedRingHom (irrelevant_le_map G hG) ≫ (isoProj σ R).hom

instance isClosedImmersion_embedding : IsClosedImmersion (embedding G hG) := by
  have := Proj.isClosedImmersion_map _ Ideal.Quotient.mk_surjective (irrelevant_le_map G hG)
  rw [embedding]
  infer_instance

@[reassoc (attr := simp)]
lemma embedding_over : embedding G hG ≫ ℙ(σ; Spec (.of R)) ↘ Spec (.of R) = toSpec G hG := by
  rw [embedding, Category.assoc, isoProj_hom_over]
  change _ ≫ Proj.toSpecBase (grading σ R) = _
  rw [Proj.map_toSpecBase (RingHom.id R) _ (fun r ↦ rfl), CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id]

instance isProper_toSpec [Finite σ] : IsProper (toSpec G hG) := by
  rw [← embedding_over]
  infer_instance

/-- **Flatness over a Dedekind domain**: if `R[xᵢ] ⧸ (G)` is a domain into which `R` injects,
`V₊(G) ⟶ Spec R` is flat. -/
theorem flat_toSpec [IsDedekindDomain R] [IsDomain (MvPolynomial σ R ⧸ (ideal G hG).toIdeal)]
    (hinj : Function.Injective (algebraMap R (MvPolynomial σ R ⧸ (ideal G hG).toIdeal))) :
    Flat (toSpec G hG) := by
  set A := MvPolynomial σ R ⧸ (ideal G hG).toIdeal
  -- (instance search does not find this instance of `HasRingHomProperty`)
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (Proj.affineOpenCover (ideal G hG).quotientGrading).openCover fun i ↦ ?_
  let s : A := i.2
  have hs : s ∈ (ideal G hG).quotientGrading i.1 := i.2.2
  have hk : 0 < (i.1 : ℕ) := i.1.2
  change Flat (Proj.awayι _ s hs hk ≫ Proj.toSpecBase _)
  rw [Proj.awayι_toSpecBase, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  -- `A_(s)` is torsion free over `R`
  have : Module.IsTorsionFree R (Localization.Away s) := by
    by_cases hs0 : s = 0
    · have : Subsingleton (Localization.Away s) := by
        rw [hs0]
        exact IsLocalization.subsingleton (M := Submonoid.powers (0 : A))
          (Submonoid.mem_powers 0)
      infer_instance
    · have : IsDomain (Localization.Away s) :=
        IsLocalization.isDomain_of_le_nonZeroDivisors _
          (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
      rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R A]
      exact (IsLocalization.injective (Localization.Away s)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)).comp hinj
  have : Module.IsTorsionFree R (Away (ideal G hG).quotientGrading s) :=
    Function.Injective.moduleIsTorsionFree _ (HomogeneousLocalization.val_injective _)
      (fun r y ↦ HomogeneousLocalization.val_smul _ r y)
  infer_instance

end AlgebraicGeometry.ProjHypersurface
