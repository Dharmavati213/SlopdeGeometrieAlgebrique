/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenExtensionByZero
import SGA.SGA2.ExposeI.ClosedSupportHom
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The open-closed sequence of constant support sheaves

For a closed subset `Z`, the genuine extensions of the constant integer sheaf
fit in the short exact sequence `0 → ℤ_{X\Z,X} → ℤ_X → ℤ_{Z,X} → 0`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Sheafifying before or after open left Kan extension gives canonically
isomorphic functors, by the uniqueness of their common left adjoint. -/
noncomputable def sheafifyOpenExtensionIso (U : Opens X) :
    presheafToSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u} ⋙ iBang_open U ≅
      U.isOpenEmbedding.functor.op.lan ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := by
  letI := U.isOpenEmbedding.functor_isContinuous
  exact Adjunction.leftAdjointUniq
    ((sheafificationAdjunction
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}).comp
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          U.isOpenEmbedding.functor AddCommGrpCat.{u} _ _))
    ((U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).comp
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- The raw open constant presheaf before sheafification. -/
noncomputable def openIntegerPresheaf (U : Opens X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  U.isOpenEmbedding.functor.op.lan.obj
    (integerPresheaf ((Opens.toTopCat X).obj U))

/-- Its sheafification is the already constructed genuine open support object. -/
noncomputable def zZX_openIsoSheafify (U : Opens X) :
    zZX_open U ≅ (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (openIntegerPresheaf U) :=
  (sheafifyOpenExtensionIso U).app (integerPresheaf ((Opens.toTopCat X).obj U))

/-- The raw open constant presheaf maps into the ambient integer presheaf. -/
noncomputable def openIntegerPresheafι (U : Opens X) :
    openIntegerPresheaf U ⟶ integerPresheaf X :=
  (U.isOpenEmbedding.functor.op.lanAdjunction AddCommGrpCat.{u}).counit.app
    (integerPresheaf X)

private theorem openIntegerPresheafι_isIso_app_image (U : Opens X)
    (W : Opens ((Opens.toTopCat X).obj U)) :
    IsIso ((openIntegerPresheafι U).app (op (U.isOpenEmbedding.functor.obj W))) := by
  have : Mono (Opens.inclusion' U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let L := U.isOpenEmbedding.functor.op
  have h := L.lanUnit_app_app_lanAdjunction_counit_app_app (integerPresheaf X) (op W)
  have he : ((L.lanAdjunction AddCommGrpCat.{u}).counit.app
      (integerPresheaf X)).app (L.obj (op W)) =
      inv ((L.lanUnit.app (L ⋙ integerPresheaf X)).app (op W)) := by
    apply (cancel_epi ((L.lanUnit.app (L ⋙ integerPresheaf X)).app (op W))).1
    simpa only [IsIso.hom_inv_id] using h
  change IsIso (((L.lanAdjunction AddCommGrpCat.{u}).counit.app
    (integerPresheaf X)).app (L.obj (op W)))
  rw [he]
  infer_instance

private theorem openIntegerPresheaf_isZero_of_not_le (U V : Opens X) (hV : ¬ V ≤ U) :
    IsZero ((openIntegerPresheaf U).obj (op V)) := by
  let L := U.isOpenEmbedding.functor.op
  have : IsEmpty (CostructuredArrow L (op V)) := ⟨fun A => by
    apply hV
    exact (leOfHom A.hom.unop).trans (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property)⟩
  have hF : IsZero (CostructuredArrow.proj L (op V) ⋙
      integerPresheaf ((Opens.toTopCat X).obj U)) :=
    Functor.isZero _ (fun A => isEmptyElim A)
  exact ((colimit.isColimit _).isZero_pt hF).of_iso
    (L.leftKanExtensionObjIsoColimit _ (op V))

private theorem openIntegerPresheafι_isIso_app_of_le (U V : Opens X) (hV : V ≤ U) :
    IsIso ((openIntegerPresheafι U).app (op V)) := by
  have h : U.isOpenEmbedding.functor.obj
      ((Opens.map (Opens.inclusion' U)).obj V) = V := by
    rw [Opens.functor_obj_map_obj, Opens.isOpenEmbedding_obj_top, inf_eq_right.mpr hV]
  rw [← h]
  exact openIntegerPresheafι_isIso_app_image U _

/-- The raw open constant inclusion is a monomorphism. -/
instance openIntegerPresheafι_mono (U : Opens X) : Mono (openIntegerPresheafι U) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro V
  by_cases hV : V.unop ≤ U
  · have := openIntegerPresheafι_isIso_app_of_le U V.unop hV
    infer_instance
  · exact mono_of_source_iso_zero _ (openIntegerPresheaf_isZero_of_not_le U V.unop hV).isoZero

private theorem openIntegerPresheafι_comp_toClosed (Z : Closeds X) :
    openIntegerPresheafι Z.compl ≫ integerPresheafToClosed Z = 0 := by
  ext V a
  by_cases hV : V.unop ≤ Z.compl
  · exact integerPresheafToClosed_app_eq_zero_of_le_compl Z hV _
  · have hz := openIntegerPresheaf_isZero_of_not_le Z.compl V.unop hV
    exact ConcreteCategory.congr_hom (hz.eq_of_src
      ((openIntegerPresheafι Z.compl).app V ≫
        (integerPresheafToClosed Z).app V) 0) a

/-- The raw open-closed integer complex, before sheafification. -/
noncomputable def integerSupportComplex (Z : Closeds X) :
    ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (openIntegerPresheafι Z.compl) (integerPresheafToClosed Z)
    (openIntegerPresheafι_comp_toClosed Z)

private theorem integerSupportComplex_exact_app (Z : Closeds X) (V : Opens X) :
    ((integerSupportComplex Z).map
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))).Exact := by
  let S := (integerSupportComplex Z).map
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  by_cases hV : V ≤ Z.compl
  · have := openIntegerPresheafι_isIso_app_of_le Z.compl V hV
    apply (S.exact_iff_epi ?_).2
    · change Epi ((openIntegerPresheafι Z.compl).app (op V))
      infer_instance
    · ext n
      exact integerPresheafToClosed_app_eq_zero_of_le_compl Z hV n
  · apply (S.exact_iff_mono ?_).2
    · apply (AddCommGrpCat.mono_iff_injective _).2
      intro a b hab
      have hne : (((Opens.map (closedInclusion Z)).obj V) :
          Set (TopCat.of (Z : Set X))).Nonempty := by
        by_contra he
        apply hV
        intro x hx hxZ
        exact he ⟨⟨x, hxZ⟩, hx⟩
      exact integerPresheaf_toSheafify_injective (TopCat.of (Z : Set X))
        ((Opens.map (closedInclusion Z)).obj V) hne hab
    · exact (openIntegerPresheaf_isZero_of_not_le Z.compl V hV).eq_of_src _ _

/-- The raw open-closed sequence is exact at the ambient integer presheaf. -/
theorem integerSupportComplex_exact (Z : Closeds X) : (integerSupportComplex Z).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro V
  have h := (ShortComplex.exact_iff_isZero_homology _).mp
    (integerSupportComplex_exact_app Z V.unop)
  exact h.of_iso ((integerSupportComplex Z).mapHomologyIso
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V)).symm

/-- The canonical inclusion of the genuine open constant support object. -/
noncomputable def zZX_openToConstant (U : Opens X) : zZX_open U ⟶ constantZ X :=
  (zZX_openIsoSheafify U).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (openIntegerPresheafι U)

/-- The canonical restriction of the ambient constant sheaf to the closed
constant pushforward. -/
noncomputable def constantToClosedSupport (Z : Closeds X) : constantZ X ⟶ zZX_closed Z :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (integerPresheafToClosed Z) ≫
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).counit.app (zZX_closed Z)

theorem zZX_openToConstant_comp_constantToClosedSupport (Z : Closeds X) :
    zZX_openToConstant Z.compl ≫ constantToClosedSupport Z = 0 := by
  simp only [zZX_openToConstant, constantToClosedSupport, Category.assoc]
  rw [← Category.assoc ((presheafToSheaf _ _).map _), ← Functor.map_comp,
    openIntegerPresheafι_comp_toClosed, Functor.map_zero, zero_comp, comp_zero]

/-- The actual open-closed complex of constant support sheaves. -/
noncomputable def constantSupportSequence (Z : Closeds X) :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (zZX_openToConstant Z.compl) (constantToClosedSupport Z)
    (zZX_openToConstant_comp_constantToClosedSupport Z)

private noncomputable def constantSupportSequenceIso (Z : Closeds X) :
    (integerSupportComplex Z).map
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≅
        constantSupportSequence Z :=
  ShortComplex.isoMk (zZX_openIsoSheafify Z.compl).symm (Iso.refl _)
    (asIso ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).counit.app (zZX_closed Z)))
    (by simp [constantSupportSequence, zZX_openToConstant, integerSupportComplex])
    (by simp [constantSupportSequence, constantToClosedSupport, integerSupportComplex])

/-- The genuine constant support objects fit in the short exact sequence
`0 → ℤ_{X\Z,X} → ℤ_X → ℤ_{Z,X} → 0`. -/
theorem constantSupportSequence_shortExact (Z : Closeds X) :
    (constantSupportSequence Z).ShortExact := by
  let L := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : CategoryTheory.Sheaf.IsLocallySurjective (L.map (integerPresheafToClosed Z)) :=
    (CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).mpr
      (integerPresheafToClosed_locallySurjective Z)
  have : Epi (L.map (integerPresheafToClosed Z)) := inferInstance
  have h : ((integerSupportComplex Z).map L).ShortExact :=
    { exact := (integerSupportComplex_exact Z).map L
      mono_f := by
        change Mono (L.map (openIntegerPresheafι Z.compl))
        infer_instance
      epi_g := by
        change Epi (L.map (integerPresheafToClosed Z))
        infer_instance }
  exact ShortComplex.shortExact_of_iso (constantSupportSequenceIso Z) h

instance zZX_openToConstant_mono (U : Opens X) : Mono (zZX_openToConstant U) := by
  have h := (constantSupportSequence_shortExact U.compl).mono_f
  change Mono (zZX_openToConstant U.compl.compl) at h
  exact (congrArg (fun V => Mono (zZX_openToConstant V)) (Opens.compl_compl U)).mp h

instance constantToClosedSupport_epi (Z : Closeds X) : Epi (constantToClosedSupport Z) :=
  (constantSupportSequence_shortExact Z).epi_g

end SGA.SGA2.ExposeI
