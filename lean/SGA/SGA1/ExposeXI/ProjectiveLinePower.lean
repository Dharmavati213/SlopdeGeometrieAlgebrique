/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Serre
import SGA.SGA1.ExposeXI.ProjectiveLine
import SGA.SGA1.ExposeXI.SimplyConnectedProduct

/-!
# Powers of the projective line are simply connected (XI.1)

The projective line `ℙ¹_k = Proj k[x₀, x₁]` is proper and reduced over `k`
(`ProjectiveLine.toSpec`), and simply connected when `k` is algebraically closed
(`isSimplyConnected_projectiveLine`). By the Künneth formula (`isSimplyConnected_pullback`), so is
every power `(ℙ¹)ʳ` (`ProjectiveLine.isSimplyConnected_pow`): this is the input of SGA's second
proof of XI.1.1, which deduces `π₁(ℙʳ) = 1` from the birational invariance X.3.4 (`ℙʳ` and
`(ℙ¹)ʳ` are birational).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MvPolynomial

namespace SGA.SGA1.ExposeXI.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (homogeneousSubmodule (Fin 2) k)

/-- The structure morphism `ℙ¹_k ⟶ Spec k`. -/
noncomputable def toSpec : ℙ¹ ⟶ Spec (.of k) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin 2) k 0)))

instance : IsProper (toSpec k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin 2) k 0)))) :=
    isIso_SpecMap_iff.2 ⟨fun r s h ↦ C_injective (Fin 2) k (congrArg Subtype.val h),
      projectiveSpace.surjective_algebraMap_gradeZero⟩
  rw [toSpec]
  infer_instance

instance : AlgebraicGeometry.IsReduced ℙ¹ := by
  have (i : (Proj.affineOpenCover (homogeneousSubmodule (Fin 2) k)).openCover.I₀) :
      AlgebraicGeometry.IsReduced ((Proj.affineOpenCover _).openCover.X i) := by
    have : _root_.IsReduced
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) i.2.1) :=
      isReduced_of_injective (algebraMap _ (Localization.Away (i.2.1 : MvPolynomial (Fin 2) k)))
        (HomogeneousLocalization.val_injective _)
    exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of _)))
  exact AlgebraicGeometry.IsReduced.of_openCover _ (Proj.affineOpenCover _).openCover

instance : IsLocallyNoetherian ℙ¹ := LocallyOfFiniteType.isLocallyNoetherian (toSpec k)

instance : CompactSpace ℙ¹ := QuasiCompact.compactSpace_of_compactSpace (toSpec k)

/-- `(ℙ¹)ʳ` over `Spec k`, as the iterated fibre product `ℙ¹ ×ₖ (ℙ¹)ʳ⁻¹`. -/
noncomputable def pow : ℕ → Over (Spec (.of k))
  | 0 => Over.mk (𝟙 _)
  | r + 1 => Over.mk (pullback.snd (toSpec k) (pow r).hom ≫ (pow r).hom)

lemma pow_properties [IsAlgClosed k] (r : ℕ) :
    IsSimplyConnected (pow k r).left ∧ LocallyOfFiniteType (pow k r).hom ∧
      CompactSpace (pow k r).left := by
  induction r with
  | zero =>
    exact ⟨isSimplyConnected_spec_of_isSepClosed k, inferInstanceAs (LocallyOfFiniteType (𝟙 _)),
      inferInstanceAs (CompactSpace (Spec (.of k)))⟩
  | succ r ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    have : IsLocallyNoetherian (pow k r).left :=
      LocallyOfFiniteType.isLocallyNoetherian (pow k r).hom
    have : QuasiCompact (toSpec k) := inferInstance
    refine ⟨isSimplyConnected_pullback (toSpec k) (pow k r).hom ?_ h₁,
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _ ≫ _)),
      inferInstanceAs (CompactSpace ↑(pullback (toSpec k) (pow k r).hom))⟩
    exact ⟨connectedSpace_projectiveLine k, fun _ f _ _ _ ↦ isIso_of_isFinite_of_etale f⟩

/-- XI.1: over an algebraically closed field, `(ℙ¹)ʳ` is simply connected (from `π₁(ℙ¹) = 1` and
the Künneth formula X.1.7). -/
theorem isSimplyConnected_pow [IsAlgClosed k] (r : ℕ) : IsSimplyConnected (pow k r).left :=
  (pow_properties k r).1

end SGA.SGA1.ExposeXI.ProjectiveLine
