/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.LocallyClosedIndependence

/-!
# Actual nested supported-section sequences

For closed `A ≤ B` and an arbitrary ambient open `V`, the supports are
`V ∩ A`, `V ∩ B`, and `(V ∩ Aᶜ) ∩ B`. Their genuine section inclusion and
restriction form a left exact sequence, short exact for flasque coefficients.
Allowing `V` makes this the general locally closed situation, not merely
the closed-support special case.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {A B : Closeds X}

/-- The actual inclusion of sections when the closed support increases. -/
def nestedSupportSectionsInclusion (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : gammaZSections F A V →+ gammaZSections F B V :=
  AddSubgroup.inclusion (gammaZSections_mono F h V)

/-- The actual restriction from the middle support to its open difference. -/
def nestedSupportSectionsRestriction (A B : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZSections F B V →+ gammaZSections F B (V ⊓ A.compl) :=
  gammaZSectionsRestriction F B (homOfLE inf_le_left)

/-- Nested support inclusion, naturally in the original coefficient sheaf. -/
def nestedSupportInclusion (h : A ≤ B) (V : Opens X) :
    gammaZSectionsFunctor A V ⟶ gammaZSectionsFunctor B V where
  app F := AddCommGrpCat.ofHom (nestedSupportSectionsInclusion h V F)
  naturality _ _ _ := by ext s; rfl

/-- Restriction to the difference, naturally in the original coefficient. -/
def nestedSupportRestriction (A B : Closeds X) (V : Opens X) :
    gammaZSectionsFunctor B V ⟶ gammaZSectionsFunctor B (V ⊓ A.compl) where
  app F := AddCommGrpCat.ofHom (nestedSupportSectionsRestriction A B V F)
  naturality _ _ f := by
    ext s
    apply Subtype.ext
    exact (f.hom.naturality_apply
      (homOfLE (inf_le_left : V ⊓ A.compl ≤ V)).op s.val).symm

/-- The supported inclusion followed by restriction to the difference is zero. -/
theorem nestedSupportSections_comp (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (nestedSupportSectionsRestriction A B V F).comp
      (nestedSupportSectionsInclusion h V F) = 0 := by
  ext s
  exact s.property

/-- **I.1.8:** the actual nested section sequence is left exact. -/
theorem nestedSupportSections_exact (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Exact (nestedSupportSectionsInclusion h V F)
      (nestedSupportSectionsRestriction A B V F) := by
  intro s
  constructor
  · intro hs
    refine ⟨⟨s.val, ?_⟩, rfl⟩
    exact congrArg Subtype.val hs
  · rintro ⟨s, rfl⟩
    exact Subtype.ext s.property

/-- Increasing the support does not identify distinct sections. -/
theorem nestedSupportSectionsInclusion_injective (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (nestedSupportSectionsInclusion h V F) := by
  intro s t hst
  exact Subtype.ext (congrArg (fun x : gammaZSections F B V => x.val) hst)

/-- **I.1.8, flasque surjectivity:** an extension of a section supported in
`B \ A` automatically still vanishes outside `B`. -/
theorem nestedSupportSectionsRestriction_surjective (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    Function.Surjective (nestedSupportSectionsRestriction A B V F) := by
  intro t
  let D := V ⊓ A.compl
  let r := F.presheaf.map (homOfLE (inf_le_left : D ≤ V)).op
  have hr : Epi r := by dsimp [r]; infer_instance
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective r).mp hr t.val
  have hDB : D ⊓ B.compl = V ⊓ B.compl := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun ha => hx.2 (h ha)⟩, hx.2⟩
  have hfac : restrictToComplement F B V = r ≫ restrictToComplement F B D ≫
      F.presheaf.map (eqToHom (congrArg op hDB)) := by
    dsimp only [restrictToComplement, r]
    rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
    congr 1
  refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
  rw [mem_gammaZSections_iff, hfac]
  change F.presheaf.map (eqToHom (congrArg op hDB))
    ((restrictToComplement F B D) (r s)) = 0
  rw [hs, t.property, map_zero]

/-- The original section arrows packaged as an actual short complex. -/
def nestedSupportSectionsSequence (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk ((nestedSupportInclusion h V).app F)
    ((nestedSupportRestriction A B V).app F)
    (by ext s; apply Subtype.ext; exact s.property)

/-- No exactness datum is supplied: flasqueness proves that the actual
nested supported-section complex is short exact. -/
theorem nestedSupportSectionsSequence_shortExact (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (nestedSupportSectionsSequence h V F).ShortExact where
  exact := (ShortComplex.ab_exact_iff_function_exact _).mpr
    (nestedSupportSections_exact h V F)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr
    (nestedSupportSectionsInclusion_injective h V F)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr
    (nestedSupportSectionsRestriction_surjective h V F)

end SGA.SGA2.ExposeI
