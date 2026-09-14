/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AnnihilatorFiltrationColimit
import SGA.SGA2.ExposeIV.SupportedScalarChange
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Every supported module is the colimit of its actual power annihilators

This is the original module and the literal inclusion cocone, with no finite
generation assumption on the module or its annihilator stages. It supplies
the source filtration used by the infinite-module duality in IV.5.1.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (J : Ideal R) (H : ModuleCat.{u} R)

/-- Every element lies in an actual ideal-power annihilator. -/
theorem exists_mem_annihilator_of_powerTorsion (hH : powerTorsion J H = ⊤) (x : H) :
    ∃ n : ℕ, x ∈ Submodule.torsionBySet R H (J ^ n : Ideal R) := by
  have hx : x ∈ powerTorsion J H := by rw [hH]; trivial
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J H x).mp hx
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  exact fun r => hn r.val r.property

/-- A stage containing the original element, used only to define cocone descent. -/
def annihilatorStageIndex (hH : powerTorsion J H = ⊤) (x : H) : ℕ :=
  (exists_mem_annihilator_of_powerTorsion J H hH x).choose

theorem mem_annihilatorStageIndex (hH : powerTorsion J H = ⊤) (x : H) :
    x ∈ Submodule.torsionBySet R H (J ^ annihilatorStageIndex J H hH x : Ideal R) :=
  (exists_mem_annihilator_of_powerTorsion J H hH x).choose_spec

/-- Evaluate a cocone on any element through a containing actual annihilator. -/
def annihilatorCoconeValue (hH : powerTorsion J H = ⊤)
    (s : Cocone (annihilatorFiltration J H)) (x : H) : s.pt :=
  s.ι.app (annihilatorStageIndex J H hH x) ⟨x, mem_annihilatorStageIndex J H hH x⟩

/-- The cocone value is independent of the containing stage. -/
theorem annihilatorCoconeValue_eq (hH : powerTorsion J H = ⊤)
    (s : Cocone (annihilatorFiltration J H)) (n : ℕ) (x : H)
    (hx : x ∈ Submodule.torsionBySet R H (J ^ n : Ideal R)) :
    annihilatorCoconeValue J H hH s x = s.ι.app n ⟨x, hx⟩ := by
  let k := annihilatorStageIndex J H hH x
  let m := max k n
  have hk := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_left k n)))
    (⟨x, mem_annihilatorStageIndex J H hH x⟩ : Submodule.torsionBySet R H (J ^ k : Ideal R))
  have hn := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_right k n)))
    (⟨x, hx⟩ : Submodule.torsionBySet R H (J ^ n : Ideal R))
  exact hk.symm.trans hn

/-- Descent along the actual inclusions is genuinely linear. -/
def annihilatorCoconeDesc (hH : powerTorsion J H = ⊤)
    (s : Cocone (annihilatorFiltration J H)) : H ⟶ s.pt :=
  ModuleCat.ofHom
    { toFun := annihilatorCoconeValue J H hH s
      map_add' x y := by
        let n := max (annihilatorStageIndex J H hH x) (annihilatorStageIndex J H hH y)
        have hx : x ∈ Submodule.torsionBySet R H (J ^ n : Ideal R) :=
          torsionBySet_pow_monotone J H (le_max_left _ _) (mem_annihilatorStageIndex J H hH x)
        have hy : y ∈ Submodule.torsionBySet R H (J ^ n : Ideal R) :=
          torsionBySet_pow_monotone J H (le_max_right _ _) (mem_annihilatorStageIndex J H hH y)
        rw [annihilatorCoconeValue_eq J H hH s n (x + y) (Submodule.add_mem _ hx hy),
          annihilatorCoconeValue_eq J H hH s n x hx,
          annihilatorCoconeValue_eq J H hH s n y hy]
        exact (s.ι.app n).hom.map_add ⟨x, hx⟩ ⟨y, hy⟩
      map_smul' r x := by
        let n := annihilatorStageIndex J H hH x
        have hx := mem_annihilatorStageIndex J H hH x
        rw [annihilatorCoconeValue_eq J H hH s n (r • x) (Submodule.smul_mem _ r hx),
          annihilatorCoconeValue_eq J H hH s n x hx]
        exact (s.ι.app n).hom.map_smul r ⟨x, hx⟩ }

/-- Any power-torsion module is the categorical colimit of its actual annihilators. -/
def annihilatorFiltrationIsColimit (hH : powerTorsion J H = ⊤) :
    IsColimit (annihilatorFiltrationCocone J H) where
  desc s := annihilatorCoconeDesc J H hH s
  fac s n := by
    ext x
    exact annihilatorCoconeValue_eq J H hH s n x.val x.property
  uniq s f hf := by
    ext x
    exact ConcreteCategory.congr_hom (hf (annihilatorStageIndex J H hH x))
      (⟨x, mem_annihilatorStageIndex J H hH x⟩ :
        Submodule.torsionBySet R H (J ^ annihilatorStageIndex J H hH x : Ideal R))

/-- In particular the original supported module is this categorical colimit. -/
def supportedAnnihilatorFiltrationIsColimit (hJ : J.FG)
    (hH : supportedModuleProperty J H) : IsColimit (annihilatorFiltrationCocone J H) :=
  annihilatorFiltrationIsColimit J H ((powerTorsion_eq_top_iff_support_of_fg J hJ H).mpr hH)

/-- Actual linear Hom converts the original annihilator colimit into its
original inverse-limit cone. No injectivity of the coefficient is required. -/
def annihilatorHomIsLimit (I : ModuleCat.{u} R) (hH : powerTorsion J H = ⊤) :
    IsLimit ((moduleHomDual I).mapCone (annihilatorFiltrationCocone J H).op) := by
  have : PreservesLimitsOfShape ℕᵒᵖ (moduleHomDual I ⋙ forget (ModuleCat R)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (yoneda.obj I))
  have : PreservesLimitsOfShape ℕᵒᵖ (moduleHomDual I) :=
    preservesLimitsOfShape_of_reflects_of_preserves (moduleHomDual I) (forget (ModuleCat R))
  exact isLimitOfPreserves (moduleHomDual I) (annihilatorFiltrationIsColimit J H hH).op

end SGA.SGA2.ExposeIV
