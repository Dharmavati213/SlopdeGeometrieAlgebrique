/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenSupportCohomology
import SGA.SGA2.ExposeI.SupportedCohomologyComparison
import SGA.SGA2.ExposeI.ConstantSupportSequenceCompatibility

/-!
# The supported-cohomology criterion for flasqueness (SGA 2, I.2.12)

An abelian sheaf on any topological space is flasque if and only if its first
Ext-defined supported cohomology vanishes for every closed support, equivalently
if all its positive supported cohomology groups vanish.

For the converse, the genuine constant support short exact sequence and its
Ext sequence supply lifts of morphisms out of the open constant support
object. Compatibility of that inclusion with the universal integer section
shows that these lifts are actual extensions of sections. Thus the proof
does not assume that the relative cohomology restriction is the section map.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Vanishing of the first Ext group of the quotient makes restriction of Hom
along a short exact sequence surjective. -/
theorem hom_precomp_surjective_of_ext_one_subsingleton
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    {S : ShortComplex C} (hS : S.ShortExact) (F : C)
    [Subsingleton (Ext S.X₃ F 1)] :
    Function.Surjective (fun g : S.X₂ ⟶ F => S.f ≫ g) := by
  intro g
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS F (Ext.mk₀ g) rfl
    (Subsingleton.elim _ _)
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective S.X₂ F).surjective x
  refine ⟨f, (Ext.mk₀_bijective S.X₁ F).injective ?_⟩
  rw [← Ext.mk₀_comp_mk₀]
  exact hx

/-- First supported cohomology vanishing supplies lifts along the actual
open constant inclusion. -/
theorem zZX_openToConstant_precomp_surjective_of_H_Z_one_subsingleton
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    [Subsingleton (H_Z U.compl F 1)] :
    Function.Surjective (fun g : constantZ X ⟶ F => zZX_openToConstant U ≫ g) := by
  have : Subsingleton (Ext (constantSupportSequence U.compl).X₃ F 1) :=
    inferInstanceAs (Subsingleton (H_Z U.compl F 1))
  have h := hom_precomp_surjective_of_ext_one_subsingleton
    (constantSupportSequence_shortExact U.compl) F
  change Function.Surjective (fun g : constantZ X ⟶ F => zZX_openToConstant U.compl.compl ≫ g) at h
  rwa [Opens.compl_compl] at h

/-- The constant integer sheaf represents global sections, additively. -/
def constantZHomEquiv (F : Sheaf AddCommGrpCat.{u} X) :
    (constantZ X ⟶ F) ≃+ F.presheaf.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv
      (AddCommGrpCat.of (ULift ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The representing correspondence is evaluation on the universal integer `1`. -/
theorem constantZHomEquiv_apply (F : Sheaf AddCommGrpCat.{u} X) (g : constantZ X ⟶ F) :
    constantZHomEquiv F g = g.hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).app (op ⊤) ⟨1⟩) := by
  rfl

/-- The open-support Hom comparison evaluates the adjoint morphism at `1`. -/
theorem openSupportHomEquiv_apply (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X)
    (g : zZX_open U ⟶ F) :
    openSupportHomEquiv U F g = (restrictToOpenSectionsIso U F).hom
      (((openExtensionByZeroAdjunction U).homEquiv _ F g).hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          (integerPresheaf ((Opens.toTopCat X).obj U))).app (op ⊤) ⟨1⟩)) := by
  rfl

/-- Precomposition with the actual open constant inclusion represents ordinary
restriction of global sections. -/
theorem openSupportHomEquiv_zZX_openToConstant (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (g : constantZ X ⟶ F) :
    openSupportHomEquiv U F (zZX_openToConstant U ≫ g) =
      F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (constantZHomEquiv F g) := by
  let a := (openExtensionByZeroAdjunction U).homEquiv _ _ (zZX_openToConstant U)
  let e := U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}
  let t := (toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (integerPresheaf ((Opens.toTopCat X).obj U))).app (op ⊤) (⟨1⟩ : ULift ℤ)
  let k : op (U.isOpenEmbedding.functor.obj ⊤) ⟶ op U := eqToHom (by simp)
  have h := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun q => q.app (op ⊤)) (zZX_openToConstant_adjunction U))
      (⟨1⟩ : ULift.{u} ℤ)
  change (e.hom.app (constantZ X)).hom.app (op ⊤) (a.hom.app (op ⊤) t) =
    (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).app
      (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩ at h
  have he := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun q => q.hom.app (op ⊤)) (e.hom.naturality g))
      (a.hom.app (op ⊤) t)
  change (e.hom.app F).hom.app (op ⊤)
      (((iShriek_open U).map g).hom.app (op ⊤) (a.hom.app (op ⊤) t)) =
    g.hom.app (op (U.isOpenEmbedding.functor.obj ⊤))
      ((e.hom.app (constantZ X)).hom.app (op ⊤) (a.hom.app (op ⊤) t)) at he
  rw [h] at he
  rw [openSupportHomEquiv_apply, Adjunction.homEquiv_naturality_right]
  change F.presheaf.map k
    ((e.hom.app F).hom.app (op ⊤)
      (((iShriek_open U).map g).hom.app (op ⊤) (a.hom.app (op ⊤) t))) = _
  rw [he, ← g.hom.naturality_apply]
  have hu := (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).naturality_apply
    k (⟨1⟩ : ULift ℤ)
  change (toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).app (op U) ⟨1⟩ =
    (constantZ X).obj.map k
      ((toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).app
        (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩) at hu
  rw [← hu, constantZHomEquiv_apply, ← g.hom.naturality_apply]
  exact congrArg (g.hom.app (op U))
    ((toSheafify (Opens.grothendieckTopology X) (integerPresheaf X)).naturality_apply
      (homOfLE le_top : U ⟶ ⊤).op (⟨1⟩ : ULift ℤ))

/-- Surjectivity of global restriction to every open implies flasqueness. -/
theorem isFlasque_of_surjective_global_restriction (F : Sheaf AddCommGrpCat.{u} X)
    (h : ∀ U : Opens X, Function.Surjective
      (F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op)) : IsFlasque F where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t, ht⟩ := h V.unop s
    refine ⟨F.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    convert! ht using 1

/-- First supported cohomology vanishing for the complement makes ordinary
global restriction to an open surjective. -/
theorem surjective_global_restriction_of_H_Z_one_subsingleton
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    [Subsingleton (H_Z U.compl F 1)] :
    Function.Surjective (F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op) := by
  intro s
  obtain ⟨g, hg⟩ := zZX_openToConstant_precomp_surjective_of_H_Z_one_subsingleton F U
    ((openSupportHomEquiv U F).symm s)
  refine ⟨constantZHomEquiv F g, ?_⟩
  rw [← openSupportHomEquiv_zZX_openToConstant]
  exact (congrArg (openSupportHomEquiv U F) hg).trans
    ((openSupportHomEquiv U F).apply_symm_apply s)

/-- **SGA 2, I.2.12, converse:** first supported cohomology vanishing for every
closed support forces the sheaf to be flasque. -/
theorem isFlasque_of_H_Z_one_subsingleton (F : Sheaf AddCommGrpCat.{u} X)
    (h : ∀ Z : Closeds X, Subsingleton (H_Z Z F 1)) : IsFlasque F := by
  apply isFlasque_of_surjective_global_restriction F
  intro U
  have := h U.compl
  exact surjective_global_restriction_of_H_Z_one_subsingleton F U

/-- **SGA 2, I.2.12:** flasqueness is equivalent to vanishing of first supported
cohomology for every closed support. -/
theorem isFlasque_iff_H_Z_one_subsingleton (F : Sheaf AddCommGrpCat.{u} X) :
    IsFlasque F ↔ ∀ Z : Closeds X, Subsingleton (H_Z Z F 1) := by
  constructor
  · intro h Z
    have := h
    exact H_Z_pos_subsingleton_of_isFlasque Z F 0
  · exact isFlasque_of_H_Z_one_subsingleton F

/-- **SGA 2, I.2.12:** flasqueness is equivalent to vanishing of all positive
supported cohomology groups, for every closed support. -/
theorem isFlasque_iff_H_Z_pos_subsingleton (F : Sheaf AddCommGrpCat.{u} X) :
    IsFlasque F ↔ ∀ (Z : Closeds X) (n : ℕ), Subsingleton (H_Z Z F (n + 1)) := by
  constructor
  · intro h Z n
    have := h
    exact H_Z_pos_subsingleton_of_isFlasque Z F n
  · intro h
    exact isFlasque_of_H_Z_one_subsingleton F (fun Z => h Z 0)

end SGA.SGA2.ExposeI
