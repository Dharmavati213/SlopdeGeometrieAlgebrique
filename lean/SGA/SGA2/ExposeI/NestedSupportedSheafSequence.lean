/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.NestedSupportedPresheafSequence
import SGA.SGA2.ExposeI.NestedSupportSubspace

/-!
# I.1.9: the original nested supported-sheaf sequence

The original ambient supported sheaves are retained. Their actual maps
are obtained from inclusion and restriction of their sections using the
proved presheaf comparisons and full faithfulness of sheaf inclusion.
Exactness and flasque surjectivity follow from the actual section sequence.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Inclusion of the original supported sheaves for an open/closed presentation. -/
def openClosedSupportedSheafInclusion {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed V A) ⟶
      underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed V B) :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).whiskeringRight (Sheaf AddCommGrpCat.{u} X)).preimage
      ((openClosedSupportedPresheafIso A V).hom ≫
        nestedSupportedPresheafInclusion h V ≫ (openClosedSupportedPresheafIso B V).inv)

/-- Restriction of the original supported sheaf to the actual difference. -/
def openClosedSupportedSheafRestriction (A B : Closeds X) (V : Opens X) :
    underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed V B) ⟶
      underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B) :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).whiskeringRight (Sheaf AddCommGrpCat.{u} X)).preimage
      ((openClosedSupportedPresheafIso B V).hom ≫
        nestedSupportedPresheafRestriction A B V ≫
          (openClosedSupportedPresheafIso B (V ⊓ A.compl)).inv)

/-- The first original sheaf map is precisely actual inclusion on sections. -/
theorem openClosedSupportedSheafInclusion_sections {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) :
    whiskerRight (openClosedSupportedSheafInclusion h V)
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≫
          (openClosedSupportedPresheafIso B V).hom =
      (openClosedSupportedPresheafIso A V).hom ≫ nestedSupportedPresheafInclusion h V := by
  change (((whiskeringRight _ _ _).obj
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).map
      (openClosedSupportedSheafInclusion h V)) ≫ _ = _
  rw [openClosedSupportedSheafInclusion, Functor.FullyFaithful.map_preimage]
  simp

/-- The second original sheaf map is precisely actual restriction on sections. -/
theorem openClosedSupportedSheafRestriction_sections (A B : Closeds X) (V : Opens X) :
    whiskerRight (openClosedSupportedSheafRestriction A B V)
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≫
          (openClosedSupportedPresheafIso B (V ⊓ A.compl)).hom =
      (openClosedSupportedPresheafIso B V).hom ≫ nestedSupportedPresheafRestriction A B V := by
  change (((whiskeringRight _ _ _).obj
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).map
      (openClosedSupportedSheafRestriction A B V)) ≫ _ = _
  rw [openClosedSupportedSheafRestriction, Functor.FullyFaithful.map_preimage]
  simp

/-- The actual sheaf inclusion followed by actual restriction is zero. -/
theorem openClosedSupportedSheaf_comp {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    openClosedSupportedSheafInclusion h V ≫ openClosedSupportedSheafRestriction A B V = 0 := by
  apply ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).whiskeringRight (Sheaf AddCommGrpCat.{u} X)).map_injective
  apply (cancel_mono (openClosedSupportedPresheafIso B (V ⊓ A.compl)).hom).mp
  change (whiskerRight (openClosedSupportedSheafInclusion h V) _ ≫
    whiskerRight (openClosedSupportedSheafRestriction A B V) _) ≫ _ = 0 ≫ _
  rw [Category.assoc, openClosedSupportedSheafRestriction_sections,
    ← Category.assoc, openClosedSupportedSheafInclusion_sections, Category.assoc,
    nestedSupportedPresheaf_comp, comp_zero, zero_comp]

/-- The original nested supported-sheaf functors as a genuine short complex. -/
def openClosedSupportedSheafFunctorSequence {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (openClosedSupportedSheafInclusion h V)
    (openClosedSupportedSheafRestriction A B V) (openClosedSupportedSheaf_comp h V)

/-- Evaluation is the original nested supported-sheaf sequence. -/
def openClosedSupportedSheafSequence {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  (openClosedSupportedSheafFunctorSequence h V).map
    ((evaluation (Sheaf AddCommGrpCat.{u} X) (Sheaf AddCommGrpCat.{u} X)).obj F)

/-- The actual section comparison identifies the short complexes, including maps. -/
def openClosedSupportedSheafSectionsSequence {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := by
  letI := abelianSheafToPresheaf_additive (X := X)
  exact (openClosedSupportedSheafSequence h V F).map
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Original sheaf maps and the actual section maps give isomorphic short complexes. -/
def openClosedSupportedSheafSequencePresheafIso {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    openClosedSupportedSheafSectionsSequence h V F ≅
        nestedSupportedPresheafSequence h V F :=
  ShortComplex.isoMk ((openClosedSupportedPresheafIso A V).app F)
    ((openClosedSupportedPresheafIso B V).app F)
    ((openClosedSupportedPresheafIso B (V ⊓ A.compl)).app F)
    (congrArg (fun α => α.app F) (openClosedSupportedSheafInclusion_sections h V)).symm
    (congrArg (fun α => α.app F) (openClosedSupportedSheafRestriction_sections A B V)).symm

/-- **I.1.9:** the original nested supported-sheaf sequence is exact. -/
theorem openClosedSupportedSheafSequence_exact {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (openClosedSupportedSheafSequence h V F).Exact := by
  let := abelianSheafToPresheaf_additive (X := X)
  exact (sheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).reflects_exact_of_faithful _
    ((ShortComplex.exact_iff_of_iso (openClosedSupportedSheafSequencePresheafIso h V F)).mpr
      (nestedSupportedPresheafSequence_exact h V F))

/-- The first original supported-sheaf map is monic, without flasqueness. -/
theorem openClosedSupportedSheafInclusion_mono {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((openClosedSupportedSheafInclusion h V).app F) := by
  let := abelianSheafToPresheaf_additive (X := X)
  have hm := ((ShortComplex.exact_and_mono_f_iff_of_iso
    (openClosedSupportedSheafSequencePresheafIso h V F)).mpr
      ⟨nestedSupportedPresheafSequence_exact h V F,
        inferInstanceAs (Mono ((nestedSupportedPresheafInclusion h V).app F))⟩).2
  exact (sheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).mono_of_mono_map hm

/-- **I.1.9, flasque case:** the original sequence is short exact. -/
theorem openClosedSupportedSheafSequence_shortExact {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (openClosedSupportedSheafSequence h V F).ShortExact := by
  let := abelianSheafToPresheaf_additive (X := X)
  exact ShortExact.reflects_shortExact_of_faithful
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (ShortComplex.shortExact_of_iso (openClosedSupportedSheafSequencePresheafIso h V F).symm
      (nestedSupportedPresheafSequence_shortExact h V F))

end SGA.SGA2.ExposeI
