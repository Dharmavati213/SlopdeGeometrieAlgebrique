/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeI.LocalToGlobalResolution

/-!
# Flasqueness of supported local linear Hom into injective module sheaves

Closed supported sections of a flasque sheaf form a flasque sheaf: glue a
supported section with zero on the complement and extend the glued section.
Restriction and direct image preserve flasqueness, so the same holds for
arbitrary locally closed support. Applied to VI.1.5, this supplies the
acyclicity needed by VI.1.6.2 on actual module-injective resolutions.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Supported sections of a flasque sheaf extend without changing their support. -/
theorem gammaZSectionsRestriction_surjective_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [ExposeI.IsFlasque F] (Z : Closeds X)
    {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (ExposeI.gammaZSectionsRestriction F Z i) := by
  intro s
  let D := V ⊔ (U ⊓ Z.compl)
  have hVD : V ≤ D := le_sup_left
  have hDU : D ≤ U := sup_le (leOfHom i) inf_le_left
  have hcover : D ≤ V ⊔ (D ⊓ Z.compl) := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨Or.inr hx, hx.2⟩
  let e := ExposeI.gammaZSections_restrict_addEquiv_of_cover F hVD hcover
  let t := e.symm s
  let r := F.presheaf.map (homOfLE hDU).op
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective r).mp inferInstance t.val
  have hcomp : D ⊓ Z.compl = U ⊓ Z.compl := by
    apply le_antisymm
    · exact inf_le_inf_right Z.compl hDU
    · exact le_inf le_sup_right inf_le_right
  have hfac : ExposeI.restrictToComplement F Z U =
      r ≫ ExposeI.restrictToComplement F Z D ≫
        F.presheaf.map (eqToHom (congrArg op hcomp)) := by
    dsimp only [ExposeI.restrictToComplement, r]
    rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
    congr 1
  have hxZ : x ∈ ExposeI.gammaZSections F Z U := by
    rw [ExposeI.mem_gammaZSections_iff, hfac]
    change F.presheaf.map (eqToHom (congrArg op hcomp))
      ((ExposeI.restrictToComplement F Z D) (r x)) = 0
    rw [hx, t.property, map_zero]
  refine ⟨⟨x, hxZ⟩, ?_⟩
  apply Subtype.ext
  have hes := congrArg Subtype.val (e.apply_symm_apply s)
  change F.presheaf.map (homOfLE hVD).op t.val = s.val at hes
  change F.presheaf.map i.op x = s.val
  rw [← hes, ← hx, ← ConcreteCategory.comp_apply]
  congr 1
  dsimp only [r]
  rw [← F.presheaf.map_comp]
  congr 1

/-- The original closed-support kernel sheaf of a flasque sheaf is flasque. -/
theorem underlineGammaZ_isFlasque_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [ExposeI.IsFlasque F] (Z : Closeds X) :
    ExposeI.IsFlasque (ExposeI.underlineGammaZ F Z) := by
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨t, ht⟩ := gammaZSectionsRestriction_surjective_of_isFlasque F Z i.unop
    (ExposeI.underlineGammaZSectionsEquiv F Z V.unop s)
  refine ⟨(ExposeI.underlineGammaZSectionsEquiv F Z U.unop).symm t, ?_⟩
  apply (ExposeI.underlineGammaZSectionsEquiv F Z V.unop).injective
  erw [ExposeI.underlineGammaZSectionsEquiv_restrict, AddEquiv.apply_symm_apply]
  exact ht

/-- Locally closed support preserves flasqueness on the original ambient sheaf. -/
theorem underlineGammaLocallyClosed_isFlasque_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [ExposeI.IsFlasque F] (W : ExposeI.LocallyClosedIn X) :
    ExposeI.IsFlasque ((ExposeI.underlineGammaLocallyClosedFunctor W).obj F) := by
  have : ExposeI.IsFlasque (ExposeI.restrictToOpen F W.V) :=
    ExposeI.isFlasque_pullback_of_isOpenEmbedding W.V.isOpenEmbedding F
  have : ExposeI.IsFlasque ((ExposeI.underlineGammaZFunctor W.ZV).obj
      ((ExposeI.iShriek_open W.V).obj F)) :=
    underlineGammaZ_isFlasque_of_isFlasque (ExposeI.restrictToOpen F W.V) W.ZV
  exact ExposeI.isFlasque_pushforward W.V.inclusion' _

/-- **VI.1.5 for supported internal Hom:** the actual supported Hom into an injective
module sheaf is flasque, for arbitrary locally closed support. -/
theorem moduleLocallyClosedSheafHom_isFlasque_of_injective
    (R : Sheaf RingCat.{u} X) (F G : SheafOfModules.{u} R) [Injective G]
    (W : ExposeI.LocallyClosedIn X) :
    ExposeI.IsFlasque ((moduleLocallyClosedSheafHomFunctor R F W).obj G) := by
  have : ExposeI.IsFlasque ((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).obj G) :=
    moduleSheafHomAb_isFlasque_of_injective R F G
  exact underlineGammaLocallyClosed_isFlasque_of_isFlasque _ W

end SGA.SGA2.ExposeVI
