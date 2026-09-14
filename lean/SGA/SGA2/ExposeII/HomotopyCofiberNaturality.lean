/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulComplex

/-!
# Naturality of the additive-functor cofiber comparison

For the actual natural-indexed chain complexes, the standard comparison
between an additive functor applied to a cofiber and the cofiber of the
mapped arrow commutes with the original maps of arrows. This retains the
actual power transitions when changing rings in a Koszul complex.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {K L K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
variable (φ : K ⟶ L) (ψ : K' ⟶ L') (α : Arrow.mk φ ⟶ Arrow.mk ψ)

/-- On the shifted summand the actual cofiber map is the left side
of the original square. -/
@[reassoc (attr := simp)]
theorem homotopyCofiber_inlX_mapArrowHom (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel j i) :
    homotopyCofiber.inlX φ i j hij ≫
        (homotopyCofiber.mapArrowHom φ ψ chainShape_hasPredecessor α).f j =
      α.left.f i ≫ homotopyCofiber.inlX ψ i j hij := by
  simp [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f φ _ _ j i hij,
    homotopyCofiber.inrCompHomotopy_hom ψ _ i j hij]

/-- On the unshifted summand the cofiber map is the right side of the square. -/
@[reassoc (attr := simp)]
theorem homotopyCofiber_inrX_mapArrowHom (i : ℕ) :
    homotopyCofiber.inrX φ i ≫
        (homotopyCofiber.mapArrowHom φ ψ chainShape_hasPredecessor α).f i =
      α.right.f i ≫ homotopyCofiber.inrX ψ i := by
  simp [homotopyCofiber.mapArrowHom]

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{v} S) [F.Additive]

/-- The actual mapped square, including its original commutativity proof. -/
def mapChainArrow :
    Arrow.mk ((F.mapHomologicalComplex _).map φ) ⟶
      Arrow.mk ((F.mapHomologicalComplex _).map ψ) :=
  Arrow.homMk ((F.mapHomologicalComplex _).map α.left)
    ((F.mapHomologicalComplex _).map α.right) (by
      change (F.mapHomologicalComplex _).map α.left ≫ (F.mapHomologicalComplex _).map ψ =
        (F.mapHomologicalComplex _).map φ ≫ (F.mapHomologicalComplex _).map α.right
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (F.mapHomologicalComplex _).map α.w)

/-- The inverse cofiber comparison commutes with actual arrow maps. -/
@[reassoc]
theorem homotopyCofiber_mapIso_inv_naturality :
    (homotopyCofiber.mapHomologicalComplexObjIso φ F).inv ≫
        (F.mapHomologicalComplex _).map
          (homotopyCofiber.mapArrowHom φ ψ chainShape_hasPredecessor α) =
      homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor (mapChainArrow φ ψ α F) ≫
        (homotopyCofiber.mapHomologicalComplexObjIso ψ F).inv := by
  ext j : 1
  change (homotopyCofiber.mapHomologicalComplexObjXIso φ F j).inv ≫
      F.map ((homotopyCofiber.mapArrowHom φ ψ chainShape_hasPredecessor α).f j) =
    (homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor
      (mapChainArrow φ ψ α F)).f j ≫
        (homotopyCofiber.mapHomologicalComplexObjXIso ψ F j).inv
  cases j with
  | zero =>
    apply homotopyCofiber.ext_from_X' ((F.mapHomologicalComplex _).map φ) 0 (by simp)
    simp only [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc,
      homotopyCofiber_inrX_mapArrowHom_assoc,
      homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv]
    change F.map (homotopyCofiber.inrX φ 0) ≫ F.map _ =
      F.map (α.right.f 0) ≫ F.map (homotopyCofiber.inrX ψ 0)
    rw [← F.map_comp, homotopyCofiber_inrX_mapArrowHom, F.map_comp]
  | succ i =>
    apply homotopyCofiber.ext_from_X ((F.mapHomologicalComplex _).map φ) i (i + 1) rfl
    · simp only [homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv_assoc,
        homotopyCofiber_inlX_mapArrowHom_assoc,
        homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv]
      change F.map (homotopyCofiber.inlX φ i (i + 1) rfl) ≫ F.map _ =
        F.map (α.left.f i) ≫ F.map (homotopyCofiber.inlX ψ i (i + 1) rfl)
      rw [← F.map_comp, homotopyCofiber_inlX_mapArrowHom, F.map_comp]
    · simp only [homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv_assoc,
        homotopyCofiber_inrX_mapArrowHom_assoc,
        homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv]
      change F.map (homotopyCofiber.inrX φ (i + 1)) ≫ F.map _ =
        F.map (α.right.f (i + 1)) ≫ F.map (homotopyCofiber.inrX ψ (i + 1))
      rw [← F.map_comp, homotopyCofiber_inrX_mapArrowHom, F.map_comp]

/-- The forward cofiber comparison commutes with actual arrow maps. -/
@[reassoc]
theorem homotopyCofiber_mapIso_hom_naturality :
    (F.mapHomologicalComplex _).map
        (homotopyCofiber.mapArrowHom φ ψ chainShape_hasPredecessor α) ≫
          (homotopyCofiber.mapHomologicalComplexObjIso ψ F).hom =
      (homotopyCofiber.mapHomologicalComplexObjIso φ F).hom ≫
        homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor (mapChainArrow φ ψ α F) := by
  rw [← cancel_epi (homotopyCofiber.mapHomologicalComplexObjIso φ F).inv]
  simp only [← Category.assoc]
  rw [homotopyCofiber_mapIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp

end SGA.SGA2.ExposeII
