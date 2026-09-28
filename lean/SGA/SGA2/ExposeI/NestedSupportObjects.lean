/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.NestedSupportSections

/-!
# The genuine short exact sequence of nested integer support sheaves

The actual support objects already represent supported sections. The proved
natural section arrows therefore determine actual morphisms between these
objects. Left exactness on all coefficients proves the cokernel property;
surjectivity on injectives proves the first arrow is mono. Thus I.1.10 is
established without an assumed support-object sequence or extension comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {A B : Closeds X}

/-- The existing integer support object represents sections on `V` with
support in the actual intersection `V ∩ Z`. -/
def openClosedSupportHomFunctorIso (Z : Closeds X) (V : Opens X) :
    preadditiveCoyoneda.obj (op (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z))) ≅
      gammaZSectionsFunctor Z V :=
  locallyClosedSupportHomFunctorIso (LocallyClosedIn.ofOpenClosed V Z) ≪≫
    gammaZSectionsLocallyClosedIso Z V

/-- The same genuine representation, as an additive equivalence. -/
def openClosedSupportHomEquiv (Z : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V Z) ⟶ F) ≃+
      gammaZSections F Z V :=
  ((openClosedSupportHomFunctorIso Z V).app F).addCommGroupIsoToAddEquiv

/-- Restriction of the actual integer support object to the smaller closed
support, defined by the already proved natural section inclusion. -/
def nestedSupportObjectRestriction (h : A ≤ B) (V : Opens X) :
    zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V B) ⟶
      zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V A) :=
  (preadditiveCoyoneda.preimage ((openClosedSupportHomFunctorIso A V).hom ≫
    nestedSupportInclusion h V ≫ (openClosedSupportHomFunctorIso B V).inv)).unop

/-- Inclusion of the difference support, defined by the actual section
restriction, not by postulating an extension-by-zero sequence. -/
def nestedSupportObjectInclusion (A B : Closeds X) (V : Opens X) :
    zZX_locallyClosed (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B) ⟶
      zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V B) :=
  (preadditiveCoyoneda.preimage ((openClosedSupportHomFunctorIso B V).hom ≫
    nestedSupportRestriction A B V ≫
      (openClosedSupportHomFunctorIso B (V ⊓ A.compl)).inv)).unop

/-- The first representing-object arrow induces precisely the original
restriction of supported sections on Hom. -/
theorem nestedSupportObjectInclusion_sections (A B : Closeds X) (V : Opens X)
    {F : Sheaf AddCommGrpCat.{u} X}
    (f : zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V B) ⟶ F) :
    openClosedSupportHomEquiv B (V ⊓ A.compl) F
        (nestedSupportObjectInclusion A B V ≫ f) =
      nestedSupportSectionsRestriction A B V F (openClosedSupportHomEquiv B V F f) := by
  have hs : preadditiveCoyoneda.map (nestedSupportObjectInclusion A B V).op ≫
      (openClosedSupportHomFunctorIso B (V ⊓ A.compl)).hom =
      (openClosedSupportHomFunctorIso B V).hom ≫ nestedSupportRestriction A B V := by
    dsimp only [nestedSupportObjectInclusion]
    simp only [Quiver.Hom.op_unop]
    erw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun t => t.app F) hs) f

/-- The second representing-object arrow induces precisely the original
inclusion of supported sections on Hom. -/
theorem nestedSupportObjectRestriction_sections (h : A ≤ B) (V : Opens X)
    {F : Sheaf AddCommGrpCat.{u} X}
    (f : zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V A) ⟶ F) :
    openClosedSupportHomEquiv B V F (nestedSupportObjectRestriction h V ≫ f) =
      nestedSupportSectionsInclusion h V F (openClosedSupportHomEquiv A V F f) := by
  have hs : preadditiveCoyoneda.map (nestedSupportObjectRestriction h V).op ≫
      (openClosedSupportHomFunctorIso B V).hom =
      (openClosedSupportHomFunctorIso A V).hom ≫ nestedSupportInclusion h V := by
    dsimp only [nestedSupportObjectRestriction]
    simp only [Quiver.Hom.op_unop]
    erw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun t => t.app F) hs) f

/-- The genuine nested support arrows have zero composite. -/
theorem nestedSupportObject_comp (h : A ≤ B) (V : Opens X) :
    nestedSupportObjectInclusion A B V ≫ nestedSupportObjectRestriction h V = 0 := by
  apply (openClosedSupportHomEquiv B (V ⊓ A.compl) _).injective
  rw [nestedSupportObjectInclusion_sections, map_zero]
  have hp := nestedSupportObjectRestriction_sections h V
    (𝟙 (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V A)))
  rw [Category.comp_id] at hp
  rw [hp]
  exact Subtype.ext (openClosedSupportHomEquiv A V _ (𝟙 _)).property

/-- The actual restriction to the smaller closed support is epi. -/
instance nestedSupportObjectRestriction_epi (h : A ≤ B) (V : Opens X) :
    Epi (nestedSupportObjectRestriction h V) where
  left_cancellation f g hfg := by
    apply (openClosedSupportHomEquiv A V _).injective
    apply nestedSupportSectionsInclusion_injective h V
    rw [← nestedSupportObjectRestriction_sections,
      ← nestedSupportObjectRestriction_sections, hfg]

/-- The kernel condition on actual support Hom is the proved section
exactness, so every compatible morphism factors through the second arrow. -/
theorem nestedSupportObject_exists_desc (h : A ≤ B) (V : Opens X)
    {F : Sheaf AddCommGrpCat.{u} X}
    (f : zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V B) ⟶ F)
    (hf : nestedSupportObjectInclusion A B V ≫ f = 0) :
    ∃ g : zZX_locallyClosed (LocallyClosedIn.ofOpenClosed V A) ⟶ F,
      nestedSupportObjectRestriction h V ≫ g = f := by
  have hs : nestedSupportSectionsRestriction A B V F
      (openClosedSupportHomEquiv B V F f) = 0 := by
    rw [← nestedSupportObjectInclusion_sections, hf, map_zero]
  obtain ⟨s, hs⟩ := (nestedSupportSections_exact h V F
    (openClosedSupportHomEquiv B V F f)).mp hs
  refine ⟨(openClosedSupportHomEquiv A V F).symm s, ?_⟩
  apply (openClosedSupportHomEquiv B V F).injective
  rw [nestedSupportObjectRestriction_sections, AddEquiv.apply_symm_apply, hs]

/-- The second arrow is the actual cokernel of the first. -/
def nestedSupportObjectIsCokernel (h : A ≤ B) (V : Opens X) :
    IsColimit (CokernelCofork.ofπ (nestedSupportObjectRestriction h V)
      (nestedSupportObject_comp h V)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun f hf =>
    ⟨(nestedSupportObject_exists_desc h V f hf).choose,
      (nestedSupportObject_exists_desc h V f hf).choose_spec⟩)

/-- Flasque section surjectivity, applied to an actual injective embedding,
proves the first support-object arrow is mono. -/
theorem nestedSupportObjectInclusion_mono (h : A ≤ B) (V : Opens X) :
    Mono (nestedSupportObjectInclusion A B V) := by
  let D := zZX_locallyClosed (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B)
  let I := Injective.under D
  have : IsFlasque I := isFlasque_of_injective I
  obtain ⟨s, hs⟩ := nestedSupportSectionsRestriction_surjective h V I
    (openClosedSupportHomEquiv B (V ⊓ A.compl) I (Injective.ι D))
  let g := (openClosedSupportHomEquiv B V I).symm s
  have hg : nestedSupportObjectInclusion A B V ≫ g = Injective.ι D := by
    apply (openClosedSupportHomEquiv B (V ⊓ A.compl) I).injective
    rw [nestedSupportObjectInclusion_sections]
    exact (congrArg (nestedSupportSectionsRestriction A B V I)
      ((openClosedSupportHomEquiv B V I).apply_symm_apply s)).trans hs
  have : Mono (nestedSupportObjectInclusion A B V ≫ g) := by rw [hg]; infer_instance
  exact mono_of_mono (nestedSupportObjectInclusion A B V) g

/-- The actual nested constant support objects, with their represented maps. -/
def nestedSupportObjectSequence (h : A ≤ B) (V : Opens X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (nestedSupportObjectInclusion A B V)
    (nestedSupportObjectRestriction h V) (nestedSupportObject_comp h V)

/-- **I.1.10, general locally closed support:** the sequence of the original
integer support objects is genuinely short exact. -/
theorem nestedSupportObjectSequence_shortExact (h : A ≤ B) (V : Opens X) :
    (nestedSupportObjectSequence h V).ShortExact where
  exact := (nestedSupportObjectSequence h V).exact_of_g_is_cokernel
    (nestedSupportObjectIsCokernel h V)
  mono_f := nestedSupportObjectInclusion_mono h V
  epi_g := nestedSupportObjectRestriction_epi h V

end SGA.SGA2.ExposeI
