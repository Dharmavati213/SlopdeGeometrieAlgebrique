/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.HomotopyCofiberNaturality

/-!
# Koszul complexes under scalar-compatible additive functors

The actual recursively defined Koszul complex commutes with a
scalar-compatible additive functor. No exactness or flatness is needed:
the construction only uses finite sums and the original scalar maps.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (σ : R →+* S) (F : ModuleCat.{u} R ⥤ ModuleCat.{v} S) [F.Additive]
variable (hF : ∀ {M N : ModuleCat.{u} R} (f : M ⟶ N) (r : R),
  F.map (r • f) = σ r • F.map f)

include hF in
/-- The mapped complex functor retains the specified original scalar action. -/
theorem mapChain_smul {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (r : R) :
    (F.mapHomologicalComplex _).map (r • f) =
      σ r • (F.mapHomologicalComplex _).map f := by
  ext i : 1
  exact hF (f.f i) r

/-- The arrow isomorphism used in a scalar cofiber, with the scalar map
transported through the actual additive functor. -/
def mapScalarArrowIso {K : ChainComplex (ModuleCat.{u} R) ℕ}
    {L : ChainComplex (ModuleCat.{v} S) ℕ}
    (e : (F.mapHomologicalComplex _).obj K ≅ L) (r : R) :
    Arrow.mk ((F.mapHomologicalComplex _).map (r • 𝟙 K)) ≅ Arrow.mk (σ r • 𝟙 L) :=
  Arrow.isoMk e e (by
    change e.hom ≫ (σ r • 𝟙 L) = (F.mapHomologicalComplex _).map (r • 𝟙 K) ≫ e.hom
    rw [mapChain_smul σ F hF, CategoryTheory.Functor.map_id]
    simp [Linear.smul_comp, Linear.comp_smul])

/-- The genuine Koszul complex comparison for an additive scalar change.
The coefficient isomorphism is retained at the empty-list stage. -/
def koszulScalarChangeIso (M : ModuleCat.{u} R) (N : ModuleCat.{v} S) (e : F.obj M ≅ N) :
    (fs : List R) → (F.mapHomologicalComplex _).obj (koszulComplex M fs) ≅
      koszulComplex N (fs.map σ)
  | [] => (singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app M ≪≫
      (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).mapIso e
  | r :: fs => homotopyCofiber.mapHomologicalComplexObjIso _ F ≪≫
      homotopyCofiber.mapArrowIso _ _ chainShape_hasPredecessor
        (mapScalarArrowIso σ F hF (koszulScalarChangeIso M N e fs) r)

/-- The scalar-power arrow isomorphism has the actual image power on the
target side, as used in the original target-ring Koszul system. -/
def mapScalarPowerArrowIso {K : ChainComplex (ModuleCat.{u} R) ℕ}
    {L : ChainComplex (ModuleCat.{v} S) ℕ}
    (e : (F.mapHomologicalComplex _).obj K ≅ L) (r : R) (n : ℕ) :
    Arrow.mk ((F.mapHomologicalComplex _).map (r ^ n • 𝟙 K)) ≅
      Arrow.mk ((σ r) ^ n • 𝟙 L) :=
  Arrow.isoMk e e (by
    change e.hom ≫ ((σ r) ^ n • 𝟙 L) =
      (F.mapHomologicalComplex _).map (r ^ n • 𝟙 K) ≫ e.hom
    rw [mapChain_smul σ F hF, CategoryTheory.Functor.map_id, map_pow]
    simp [Linear.smul_comp, Linear.comp_smul])

/-- Scalar change at a power stage, with the original target-system indices. -/
def koszulPowerScalarChangeIso (M : ModuleCat.{u} R) (N : ModuleCat.{v} S)
    (e : F.obj M ≅ N) : (fs : List R) → (n : ℕ) →
    (F.mapHomologicalComplex _).obj (koszulPowerComplex M fs n) ≅
      koszulPowerComplex N (fs.map σ) n
  | [], _ => (singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app M ≪≫
      (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).mapIso e
  | r :: fs, n => homotopyCofiber.mapHomologicalComplexObjIso _ F ≪≫
      homotopyCofiber.mapArrowIso _ _ chainShape_hasPredecessor
        (mapScalarPowerArrowIso σ F hF (koszulPowerScalarChangeIso M N e fs n) r n)

/-- The comparison of power stages commutes with every original transition. -/
@[reassoc]
theorem koszulPowerScalarChangeIso_transition (M : ModuleCat.{u} R) (N : ModuleCat.{v} S)
    (e : F.obj M ≅ N) (fs : List R) {n m : ℕ} (hnm : n ≤ m) :
    (F.mapHomologicalComplex _).map (koszulTransition M fs hnm) ≫
        (koszulPowerScalarChangeIso σ F hF M N e fs n).hom =
      (koszulPowerScalarChangeIso σ F hF M N e fs m).hom ≫
        koszulTransition N (fs.map σ) hnm := by
  induction fs with
  | nil =>
    change (F.mapHomologicalComplex _).map (𝟙 _) ≫
        (koszulPowerScalarChangeIso σ F hF M N e [] 0).hom =
      (koszulPowerScalarChangeIso σ F hF M N e [] 0).hom ≫ 𝟙 _
    simp
  | cons r fs ih =>
    change (F.mapHomologicalComplex _).map (koszulTransition M (r :: fs) hnm) ≫
        (koszulPowerScalarChangeIso σ F hF M N e (r :: fs) n).hom =
      (koszulPowerScalarChangeIso σ F hF M N e (r :: fs) m).hom ≫
        koszulTransition N (σ r :: fs.map σ) hnm
    simp only [koszulTransition_cons, koszulPowerScalarChangeIso,
      Iso.trans_hom, homotopyCofiber.mapArrowIso_hom]
    rw [← Category.assoc, homotopyCofiber_mapIso_hom_naturality, Category.assoc]
    simp only [Category.assoc]
    congr 1
    rw [← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
    congr 1
    ext : 1
    · change (F.mapHomologicalComplex _).map (r ^ (m - n) • koszulTransition M fs hnm) ≫
          (koszulPowerScalarChangeIso σ F hF M N e fs n).hom =
        (koszulPowerScalarChangeIso σ F hF M N e fs m).hom ≫
          ((σ r) ^ (m - n) • koszulTransition N (fs.map σ) hnm)
      rw [mapChain_smul σ F hF, map_pow, Linear.smul_comp, Linear.comp_smul, ih]
    · exact ih

/-- The original inverse systems of Koszul complexes commute with scalar change. -/
def koszulSystemScalarChangeIso (M : ModuleCat.{u} R) (N : ModuleCat.{v} S)
    (e : F.obj M ≅ N) (fs : List R) :
    koszulSystem M fs ⋙ F.mapHomologicalComplex _ ≅ koszulSystem N (fs.map σ) :=
  NatIso.ofComponents (fun n ↦ koszulPowerScalarChangeIso σ F hF M N e fs n.unop)
    (fun f ↦ koszulPowerScalarChangeIso_transition σ F hF M N e fs (leOfHom f.unop))

end SGA.SGA2.ExposeII
