/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.CohomologyRestrictionCriterion
import SGA.SGA2.ExposeI.ExactSequences
import SGA.SGA2.ExposeI.SupportedSheafModel

/-!
# The degree-one redundancy in the restriction criterion

The actual ordinary degree-zero restriction maps on every open determine
the original complement unit sectionwise. Their bijectivity makes that
unit an isomorphism and annihilates the original supported sheaves in
degrees zero and one. This proves I.2.13's redundancy clause at `N = 1`,
equivalently III.3.2 at threshold two, for arbitrary abelian sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Actual sections after inverse image on an arbitrary open of the subspace. -/
def openRestrictionSectionIso (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)
    (A : Opens ((Opens.toTopCat X).obj V)) :
    (restrictToOpen F V).presheaf.obj (op A) ≅
      F.presheaf.obj (op (V.isOpenEmbedding.functor.obj A)) :=
  (((sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
    AddCommGrpCat.{u}).mapIso ((V.isOpenEmbedding.sheafPullbackIso
      AddCommGrpCat.{u}).app F)).app (op A))

/-- The section comparisons commute with the literal presheaf restriction. -/
@[reassoc]
theorem openRestrictionSectionIso_naturality (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    {A B : Opens ((Opens.toTopCat X).obj V)} (h : A ≤ B) :
    (restrictToOpen F V).presheaf.map (homOfLE h).op ≫
      (openRestrictionSectionIso V F A).hom =
    (openRestrictionSectionIso V F B).hom ≫
      F.presheaf.map (V.isOpenEmbedding.functor.map (homOfLE h)).op :=
  ((V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app F).hom.naturality _

/-- Degree-zero ordinary restriction on the open subspace is bijective
exactly when restriction to the ambient complement intersection is. -/
theorem restrictToComplement_bijective_iff_ordinary_zero
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    Function.Bijective (restrictToComplement F Z V).hom ↔
      Function.Bijective (ordinaryCohomologyRestriction
        (closedSupportOnOpen Z V).compl (restrictToOpen F V) 0) := by
  let G := restrictToOpen F V
  let A := (closedSupportOnOpen Z V).compl
  have hA : V.isOpenEmbedding.functor.obj A = V ⊓ Z.compl := by
    simpa only [top_inf_eq] using openImage_closedSupportOnOpen_compl Z V
  let a : G.presheaf.obj (op ⊤) ≅ F.presheaf.obj (op V) :=
    openRestrictionSectionIso V F ⊤ ≪≫ F.presheaf.mapIso (eqToIso (by simp))
  let b : G.presheaf.obj (op A) ≅ F.presheaf.obj (op (V ⊓ Z.compl)) :=
    openRestrictionSectionIso V F A ≪≫ F.presheaf.mapIso (eqToIso (congrArg op hA))
  have hab : G.presheaf.map (homOfLE le_top : A ⟶ ⊤).op ≫ b.hom =
      a.hom ≫ restrictToComplement F Z V := by
    dsimp only [a, b, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, openRestrictionSectionIso_naturality, Category.assoc]
    dsimp only [restrictToComplement]
    simp only [Category.assoc]
    erw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
    congr 1
  let e₁ := (CategoryTheory.Sheaf.H.equiv₀ G isTerminalTop).trans
    a.addCommGroupIsoToAddEquiv
  let e₂ := ((CategoryTheory.Sheaf.H.equiv₀ (restrictToOpen G A) isTerminalTop).trans
    (restrictToOpenSectionsIso A G).addCommGroupIsoToAddEquiv).trans
      b.addCommGroupIsoToAddEquiv
  have he : ∀ x, e₂ (ordinaryCohomologyRestriction A G 0 x) =
      (restrictToComplement F Z V).hom (e₁ x) := by
    intro x
    change b.hom ((restrictToOpenSectionsIso A G).hom
      (CategoryTheory.Sheaf.H.equiv₀ (restrictToOpen G A) isTerminalTop
        (ordinaryCohomologyRestriction A G 0 x))) = _
    rw [ordinaryCohomologyRestriction_zero_sections]
    exact ConcreteCategory.congr_hom hab _
  have heq : e₂ ∘ ordinaryCohomologyRestriction A G 0 =
      (restrictToComplement F Z V).hom ∘ e₁ := funext he
  have h := Function.Bijective.of_comp_iff' e₂.bijective
    (ordinaryCohomologyRestriction A G 0)
  rw [heq] at h
  exact ((Function.Bijective.of_comp_iff
    (restrictToComplement F Z V).hom e₁.bijective).symm).trans h

/-- All-open bijectivity in ordinary degree zero makes the original
pullback-pushforward unit an isomorphism of sheaves. -/
theorem toComplementPushforward_isIso_of_intersectionRestriction_zero
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X)
    (h : ∀ V : Opens X, Function.Bijective
      (ordinaryCohomologyRestrictionToIntersection V Z.compl F 0)) :
    IsIso (toComplementPushforward F Z) := by
  have hres (V : Opens X) : Function.Bijective (restrictToComplement F Z V).hom := by
    apply (restrictToComplement_bijective_iff_ordinary_zero Z F V).mpr
    rw [closedSupportOnOpen_compl_eq]
    exact (ordinaryCohomologyRestrictionToIntersection_bijective_iff V Z.compl F 0).mp (h V)
  have hi (V : (Opens X)ᵒᵖ) : IsIso ((toComplementPushforward F Z).hom.app V) := by
    have : Mono (restrictToComplement F Z V.unop) :=
      (AddCommGrpCat.mono_iff_injective _).mpr (hres V.unop).injective
    have : Epi (restrictToComplement F Z V.unop) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr (hres V.unop).surjective
    have : IsIso (restrictToComplement F Z V.unop) := isIso_of_mono_of_epi _
    have : IsIso ((toComplementPushforward F Z).hom.app V ≫
        (complementPushforwardSectionsIso F Z V.unop).hom) := by
      rw [toComplementPushforward_comp_sectionsIso]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (complementPushforwardSectionsIso F Z V.unop).hom
  have hIso : IsIso (toComplementPushforward F Z).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map (toComplementPushforward F Z)) := hIso
  have : (sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).ReflectsIsomorphisms :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).reflectsIsomorphisms
  exact isIso_of_reflects_iso (toComplementPushforward F Z)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- **I.2.13, `N = 1`; III.3.2, threshold two:** injectivity in degree
one is unnecessary: bijectivity of degree-zero restriction on every open
already annihilates both original supported sheaves. -/
theorem derivedSupported_vanishes_two_iff_intersectionRestriction_zero
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    (∀ i < 2, IsZero ((derivedUnderlineGammaZ Z i).obj F)) ↔
      ∀ V : Opens X, Function.Bijective
        (ordinaryCohomologyRestrictionToIntersection V Z.compl F 0) := by
  constructor
  · intro h V
    exact ((derivedSupported_vanishes_iff_intersectionRestriction Z F 1).mp h V).1 0
      (by omega)
  · intro h
    have hu := toComplementPushforward_isIso_of_intersectionRestriction_zero Z F h
    have hz := (I_2_13_degree_zero_one_iso_criterion Z F).mpr hu
    intro i hi
    have hmodel : IsZero (sheafH_Z_n Z F i) := by
      interval_cases i
      · exact hz.1
      · exact hz.2
    exact hmodel.of_iso (derivedUnderlineGammaZObjIsoModel Z F i)

/-- The discarded highest-degree injectivity follows from the actual
degree-zero restriction hypothesis, on every ambient open. -/
theorem intersectionRestriction_one_injective_of_zero_bijective
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X)
    (h : ∀ V : Opens X, Function.Bijective
      (ordinaryCohomologyRestrictionToIntersection V Z.compl F 0))
    (V : Opens X) :
    Function.Injective (ordinaryCohomologyRestrictionToIntersection V Z.compl F 1) :=
  ((derivedSupported_vanishes_iff_intersectionRestriction Z F 1).mp
    ((derivedSupported_vanishes_two_iff_intersectionRestriction_zero Z F).mpr h) V).2

end SGA.SGA2.ExposeIII
