/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisBidualCompletion

/-!
# SGA 2, VI.2.3: the affine degree-zero quotient-Hom comparison

The actual direct system `Hom_R(M / IⁿM, N)`, with precomposition by the
original quotient maps, has colimit the ideal-power torsion in `Hom_R(M,N)`.
This algebraic step in the proof of VI.2.3 needs neither finite generation
nor noetherianity. The identification with supported sheaf Ext and its
higher-degree comparison are not asserted here.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A power annihilator is unchanged when regarded inside the power-torsion submodule. -/
theorem mem_torsionBySet_powerTorsion_iff (H : ModuleCat.{u} R) (n : ℕ)
    (x : powerTorsion I H) :
    x ∈ Submodule.torsionBySet R (powerTorsion I H) (I ^ n : Ideal R) ↔
      x.val ∈ Submodule.torsionBySet R H (I ^ n : Ideal R) := by
  rw [Submodule.mem_torsionBySet_iff, Submodule.mem_torsionBySet_iff]
  exact ⟨fun h r ↦ congrArg Subtype.val (h r), fun h r ↦ Subtype.ext (h r)⟩

/-- The actual annihilator at each stage, now inside the torsion submodule. -/
def powerAnnihilatorTorsionEquiv (H : ModuleCat.{u} R) (n : ℕ) :
    Submodule.torsionBySet R H (I ^ n : Ideal R) ≃ₗ[R]
      Submodule.torsionBySet R (powerTorsion I H) (I ^ n : Ideal R) where
  toFun x :=
    ⟨⟨x.val, (le_iSup (fun k : ℕ ↦ Submodule.torsionBySet R H (I ^ k : Ideal R)) n)
        x.property⟩,
      (mem_torsionBySet_powerTorsion_iff I H n _).mpr x.property⟩
  invFun x := ⟨x.val.val, (mem_torsionBySet_powerTorsion_iff I H n x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The stage identifications retain all original inclusion maps. -/
def annihilatorFiltrationTorsionIso (H : ModuleCat.{u} R) :
    annihilatorFiltration I H ≅
      annihilatorFiltration I (ModuleCat.of R (powerTorsion I H)) :=
  NatIso.ofComponents (fun n ↦ (powerAnnihilatorTorsionEquiv I H n).toModuleIso)
    (fun _ ↦ by ext x; rfl)

/-- The original power annihilators form a cocone in the actual torsion submodule. -/
def powerTorsionAnnihilatorCocone (H : ModuleCat.{u} R) :
    Cocone (annihilatorFiltration I H) :=
  (Cocone.precompose (annihilatorFiltrationTorsionIso I H).hom).obj
    (annihilatorFiltrationCocone I (ModuleCat.of R (powerTorsion I H)))

/-- The ideal-power torsion is the categorical colimit of the actual annihilators. -/
def powerTorsionAnnihilatorIsColimit (H : ModuleCat.{u} R) :
    IsColimit (powerTorsionAnnihilatorCocone I H) :=
  (IsColimit.precomposeHomEquiv (annihilatorFiltrationTorsionIso I H) _).symm
    (annihilatorFiltrationIsColimit I (ModuleCat.of R (powerTorsion I H))
      (powerTorsion_powerTorsion_eq_top I H))

/-- VI.2.3's original affine quotient-Hom diagram, with the actual quotient transitions. -/
def adicQuotientHomDiagram (M N : ModuleCat.{u} R) : ℕ ⥤ ModuleCat.{u} R :=
  (adicQuotientDiagram I M).rightOp ⋙ moduleHomDual N

/-- Precomposition with each original quotient projection gives the torsion cocone. -/
def adicQuotientHomTorsionCocone (M N : ModuleCat.{u} R) :
    Cocone (adicQuotientHomDiagram I M N) :=
  (Cocone.precompose (dualQuotientAnnihilatorDiagramIso I N M).hom).obj
    (powerTorsionAnnihilatorCocone I ((moduleHomDual N).obj (op M)))

/-- The cocone uses the original quotient-precomposition map on every element. -/
@[simp]
theorem adicQuotientHomTorsionCocone_apply (M N : ModuleCat.{u} R) (n : ℕ)
    (f : ModuleCat.of R (M ⧸ (I ^ n • (⊤ : Submodule R M))) ⟶ N) (x : M) :
    (((adicQuotientHomTorsionCocone I M N).ι.app n f).val).hom x =
      f ((I ^ n • (⊤ : Submodule R M)).mkQ x) := rfl

/-- VI.2.3, affine degree zero: the actual quotient-Hom cocone is a colimit. -/
def adicQuotientHomTorsionIsColimit (M N : ModuleCat.{u} R) :
    IsColimit (adicQuotientHomTorsionCocone I M N) :=
  (IsColimit.precomposeHomEquiv (dualQuotientAnnihilatorDiagramIso I N M) _).symm
    (powerTorsionAnnihilatorIsColimit I ((moduleHomDual N).obj (op M)))

/-- The canonical comparison identifies the quotient-Hom colimit with
the submodule of maps killed by some power of `I`. -/
def adicQuotientHomColimitIsoPowerTorsion (M N : ModuleCat.{u} R) :
    colimit (adicQuotientHomDiagram I M N) ≅
      ModuleCat.of R (powerTorsion I ((moduleHomDual N).obj (op M))) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (adicQuotientHomTorsionIsColimit I M N)

/-- The colimit isomorphism retains the original comparison at every quotient stage. -/
@[reassoc]
theorem adicQuotientHomColimitIsoPowerTorsion_ι (M N : ModuleCat.{u} R) (n : ℕ) :
    colimit.ι (adicQuotientHomDiagram I M N) n ≫
        (adicQuotientHomColimitIsoPowerTorsion I M N).hom =
      (adicQuotientHomTorsionCocone I M N).ι.app n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

end SGA.SGA2.ExposeVI
