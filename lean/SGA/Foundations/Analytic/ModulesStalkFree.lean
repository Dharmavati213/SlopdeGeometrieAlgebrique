/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesExactness
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Stalks of free module sheaves

The stalk of the structure sheaf as a module is the local ring as a module over itself.
Taking stalks commutes with coproducts, so the stalk of a free module sheaf is the free
module on the same basis. We also record stalkwise criteria for monomorphisms and
epimorphisms. These supply the finite-presentation calculations used in coherent Hom
comparison and Oka coherence (Stacks Project, Tag 01CC; EGA 0_I 5.2).

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleStalkFree.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open ZeroObject

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} (x : X)

instance (X : LocallyRingedSpace.{u}) : HasCoproducts.{u} X.Modules :=
  inferInstanceAs (HasCoproducts.{u} (SheafOfModules.{u} X.ringCatSheaf))

instance (X : LocallyRingedSpace.{u}) : HasProducts.{u} X.Modules :=
  inferInstanceAs (HasProducts.{u} (SheafOfModules.{u} X.ringCatSheaf))

private abbrev unitPresheaf (X : LocallyRingedSpace.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X.toSheafedSpace :=
  presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)

/-- Forgetting the ring structure commutes with the filtered colimit defining its stalk. -/
def stalkUnitAddIso :
    (unitPresheaf X).stalk x ≅
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (X.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

@[simp]
lemma stalkUnitAddIso_germ (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    (stalkUnitAddIso x).hom ((unitPresheaf X).germ U x hx r) =
      X.presheaf.germ U x hx r := by
  change ((colimit.ι _ (op ⟨U, hx⟩)) ≫
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).inv) r = _
  rw [ι_preservesColimitIso_inv]
  rfl

/-- The stalk of the unit module sheaf is the local ring, compatibly with its module action. -/
def stalkUnitLinearEquiv :
    (stalkFunctor x).obj (SheafOfModules.unit X.ringCatSheaf) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  __ := (stalkUnitAddIso x).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ :=
      (unitPresheaf X).exists_le_germ_eq m hxU
    change (stalkUnitAddIso x).hom
      (X.presheaf.germ U x hxU r •
        (unitPresheaf X).germ V x hxV m) = _
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r,
      ← germ_smul, stalkUnitAddIso_germ]
    change X.presheaf.germ V x hxV
        (X.presheaf.map (homOfLE hVU).op r * (show X.presheaf.obj (op V) from m)) =
      X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op r) *
        (show X.presheaf.stalk x from (stalkUnitAddIso x).hom
          ((unitPresheaf X).germ V x hxV m))
    rw [stalkUnitAddIso_germ, map_mul]

/-- The categorical form of the unit stalk comparison. -/
def stalkUnitIso : (stalkFunctor x).obj (SheafOfModules.unit X.ringCatSheaf) ≅
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  (stalkUnitLinearEquiv x).toModuleIso

@[simp]
lemma stalkUnitLinearEquiv_germ (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    stalkUnitLinearEquiv x ((unitPresheaf X).germ U x hx r) =
      X.presheaf.germ U x hx r :=
  stalkUnitAddIso_germ x U hx r

/-- The stalk of a free module sheaf is the free local-ring module on the same basis. -/
def stalkFreeIso (I : Type u) :
    (stalkFunctor x).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ModuleCat.of (X.presheaf.stalk x) (I →₀ X.presheaf.stalk x) :=
  PreservesCoproduct.iso (stalkFunctor x) (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) ≪≫
    Sigma.mapIso (fun _ : I ↦ stalkUnitIso x) ≪≫
      (coproductIsCoproduct (fun _ : I ↦
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).coconePointUniqueUpToIso
        (ModuleCat.finsuppCoconeIsColimit (X.presheaf.stalk x) (X.presheaf.stalk x) I)

/-- The linear-equivalence form of the free stalk comparison. -/
def stalkFreeLinearEquiv (I : Type u) :
    (stalkFunctor x).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≃ₗ[X.presheaf.stalk x]
      (I →₀ X.presheaf.stalk x) :=
  (stalkFreeIso x I).toLinearEquiv

/-- The free stalk comparison sends each canonical summand to its corresponding basis
coordinate. -/
@[reassoc]
lemma stalk_ιFree_stalkFreeIso_hom (I : Type u) (i : I) :
    (stalkFunctor x).map (SheafOfModules.ιFree (R := X.ringCatSheaf) i) ≫
      (stalkFreeIso x I).hom =
    (stalkUnitIso x).hom ≫ ModuleCat.ofHom
      (Finsupp.lsingle i (R := X.presheaf.stalk x) (M := X.presheaf.stalk x)) := by
  have h : (stalkFunctor x).map (SheafOfModules.ιFree (R := X.ringCatSheaf) i) ≫
      (PreservesCoproduct.iso (stalkFunctor x)
        (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)).hom =
      Sigma.ι (fun _ : I ↦ (stalkFunctor x).obj (SheafOfModules.unit X.ringCatSheaf)) i :=
    (isColimitOfHasCoproductOfPreservesColimit (stalkFunctor x)
      (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)).comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit _) ⟨i⟩
  simp only [stalkFreeIso, Iso.trans_hom, ← Category.assoc, h]
  rw [Sigma.ι_mapIso_hom]
  rw [Category.assoc]
  congr 1
  exact (coproductIsCoproduct (fun _ : I ↦
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit (X.presheaf.stalk x) (X.presheaf.stalk x) I) ⟨i⟩

@[simp]
lemma stalkFreeLinearEquiv_map_ιFree (I : Type u) (i : I)
    (s : (stalkFunctor x).obj (SheafOfModules.unit X.ringCatSheaf)) :
    stalkFreeLinearEquiv x I
      ((stalkFunctor x).map (SheafOfModules.ιFree (R := X.ringCatSheaf) i) s) =
        Finsupp.single i (stalkUnitLinearEquiv x s) :=
  congrArg (fun f ↦ f s) (stalk_ιFree_stalkFreeIso_hom x I i)

variable {M N : X.Modules}

/-- A morphism of module sheaves is epi exactly when it is epi on all stalks. -/
theorem epi_iff_stalkFunctor_map_epi (f : M ⟶ N) :
    Epi f ↔ ∀ x : X, Epi ((stalkFunctor x).map f) := by
  let C : ShortComplex X.Modules := ShortComplex.mk f (0 : N ⟶ 0) (by simp)
  rw [← C.exact_iff_epi rfl, exact_iff_stalkFunctor_map_exact]
  exact forall_congr' fun x ↦ (C.map (stalkFunctor x)).exact_iff_epi (by simp [C])

/-- A morphism of module sheaves is mono exactly when it is mono on all stalks. -/
theorem mono_iff_stalkFunctor_map_mono (f : M ⟶ N) :
    Mono f ↔ ∀ x : X, Mono ((stalkFunctor x).map f) := by
  let C : ShortComplex X.Modules := ShortComplex.mk (0 : 0 ⟶ M) f (by simp)
  rw [← C.exact_iff_mono rfl, exact_iff_stalkFunctor_map_exact]
  exact forall_congr' fun x ↦ (C.map (stalkFunctor x)).exact_iff_mono (by simp [C])

end AlgebraicGeometry.LocallyRingedSpace.Modules
