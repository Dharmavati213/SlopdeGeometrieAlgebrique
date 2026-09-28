/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulTopTransition
import SGA.SGA2.ExposeII.KoszulLocalCohomology

/-!
# Local cohomology as the explicit top Koszul quotient colimit

The terms are the actual quotients `E / (f₁^r, …, f_d^r) E` and their
maps are induced directly by multiplication by `∏ f_i^(s-r)`. The proved
top-transition calculation identifies this diagram with the original top
Koszul cohomology diagram. Over a noetherian ring its colimit is therefore
the original algebraic local cohomology in degree `fs.length`.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Multiplication by the product of the power differences descends to
the actual coefficient quotients. This follows from the already proved
formula for the genuine Koszul cohomology transition. -/
theorem koszulTopQuotientMap_wellDefined (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) :
    koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E) ≤
      (koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)).comap
        ((fs.map (fun f => f ^ (m - n))).prod • LinearMap.id) := by
  intro y hy
  change (fs.map (fun f => f ^ (m - n))).prod • y ∈
    koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hn : (koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mkQ y = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hy
  have h := koszulTopCohomology_transition_apply fs E hnm y
  rw [hn, map_zero, map_zero, map_zero] at h
  exact h.symm

/-- The direct quotient map induced by multiplication by the product
of the power differences; it is not defined by conjugating cohomology. -/
def koszulTopQuotientMap (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) :
    ModuleCat.of R (E ⧸ koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)) ⟶
      ModuleCat.of R (E ⧸ koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)) :=
  ModuleCat.ofHom ((koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mapQ
    (koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E))
    ((fs.map (fun f => f ^ (m - n))).prod • LinearMap.id)
    (koszulTopQuotientMap_wellDefined fs E hnm))

@[simp]
theorem koszulTopQuotientMap_apply_mk (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) (y : E) :
    koszulTopQuotientMap fs E hnm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((fs.map (fun f => f ^ (m - n))).prod • y) := rfl

@[simp]
theorem koszulTopQuotientMap_self (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    koszulTopQuotientMap fs E (le_refl n) = 𝟙 _ := by
  ext y
  change Submodule.Quotient.mk ((fs.map (fun f => f ^ (n - n))).prod • y) =
    (Submodule.Quotient.mk y : E ⧸ koszulIdeal (fs.map (fun f => f ^ n)) • ⊤)
  simp

/-- The explicit product maps satisfy the actual diagram composition law. -/
@[reassoc]
theorem koszulTopQuotientMap_comp (fs : List R) (E : ModuleCat.{u} R)
    {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    koszulTopQuotientMap fs E hnm ≫ koszulTopQuotientMap fs E hmk =
      koszulTopQuotientMap fs E (hnm.trans hmk) := by
  have hdiff : k - m + (m - n) = k - n := by omega
  have hprod : (fs.map (fun f => f ^ (k - m))).prod *
      (fs.map (fun f => f ^ (m - n))).prod =
      (fs.map (fun f => f ^ (k - n))).prod := by
    rw [← List.prod_map_mul]
    simp only [← pow_add, hdiff]
  ext y
  change Submodule.Quotient.mk ((fs.map (fun f => f ^ (k - m))).prod •
      (fs.map (fun f => f ^ (m - n))).prod • y) =
    (Submodule.Quotient.mk ((fs.map (fun f => f ^ (k - n))).prod • y) :
      E ⧸ koszulIdeal (fs.map (fun f => f ^ k)) • ⊤)
  rw [smul_smul, hprod]

/-- The genuine direct diagram of power-ideal quotients with the explicit
product-multiplication maps of Exposé IV.5.5. -/
def koszulTopQuotientDiagram (fs : List R) (E : ModuleCat.{u} R) :
    ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (E ⧸ koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E))
  map h := koszulTopQuotientMap fs E (leOfHom h)
  map_id n := koszulTopQuotientMap_self fs E n
  map_comp h g := (koszulTopQuotientMap_comp fs E (leOfHom h) (leOfHom g)).symm

@[simp]
theorem koszulTopQuotientDiagram_map_apply (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) (y : E) :
    (koszulTopQuotientDiagram fs E).map (homOfLE hnm) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((fs.map (fun f => f ^ (m - n))).prod • y) := rfl

/-- The literal transition in the quotient diagram has exactly the
`r → r+s` product formula of Exposé IV.5.5. -/
theorem koszulTopQuotientDiagram_map_add_apply (fs : List R) (E : ModuleCat.{u} R)
    (r s : ℕ) (y : E) :
    (koszulTopQuotientDiagram fs E).map (homOfLE (Nat.le_add_right r s))
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((fs.map (fun f => f ^ s)).prod • y) := by
  simpa only [Nat.add_sub_cancel_left] using
    koszulTopQuotientDiagram_map_apply fs E (Nat.le_add_right r s) y

/-- The original injections into this explicit colimit obey the
parameter-product relation, as actual equalities of classes. -/
theorem koszulTopQuotientColimit_ι_add_apply (fs : List R) (E : ModuleCat.{u} R)
    (r s : ℕ) (y : E) :
    colimit.ι (koszulTopQuotientDiagram fs E) (r + s)
        (Submodule.Quotient.mk ((fs.map (fun f => f ^ s)).prod • y)) =
      colimit.ι (koszulTopQuotientDiagram fs E) r (Submodule.Quotient.mk y) := by
  have h := congrArg (fun t => t (Submodule.Quotient.mk y))
    (colimit.w (koszulTopQuotientDiagram fs E) (homOfLE (Nat.le_add_right r s)))
  change colimit.ι (koszulTopQuotientDiagram fs E) (r + s)
    (Submodule.Quotient.mk ((fs.map (fun f => f ^ (r + s - r))).prod • y)) =
      colimit.ι (koszulTopQuotientDiagram fs E) r (Submodule.Quotient.mk y) at h
  simpa only [Nat.add_sub_cancel_left] using h

/-- The original top cohomology identifications intertwine the genuine
Koszul diagram maps with the direct product-multiplication quotient maps. -/
@[reassoc]
theorem koszulPowerTopCohomologyIsoQuotient_naturality (fs : List R)
    (E : ModuleCat.{u} R) {n m : ℕ} (hnm : n ≤ m) :
    (koszulCohomologyDiagram fs E fs.length).map (homOfLE hnm).op.op ≫
        (koszulPowerTopCohomologyIsoQuotient fs E m).hom =
      (koszulPowerTopCohomologyIsoQuotient fs E n).hom ≫ koszulTopQuotientMap fs E hnm := by
  apply (cancel_epi (koszulPowerTopCohomologyIsoQuotient fs E n).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext y
  change (koszulPowerTopCohomologyIsoQuotient fs E m).hom
    (homologyMap (koszulHomTransition fs E hnm) fs.length
      ((koszulPowerTopCohomologyIsoQuotient fs E n).inv
        ((koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mkQ y))) =
    (koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)).mkQ
      ((fs.map (fun f => f ^ (m - n))).prod • y)
  exact koszulTopCohomology_transition_apply fs E hnm y

/-- The explicit quotient diagram is naturally isomorphic to the original
top Koszul cohomology diagram, reindexed from `ℕᵒᵖᵒᵖ` to `ℕ`. -/
def koszulTopQuotientDiagramIso (fs : List R) (E : ModuleCat.{u} R) :
    (opOpEquivalence ℕ).inverse ⋙ koszulCohomologyDiagram fs E fs.length ≅
      koszulTopQuotientDiagram fs E :=
  NatIso.ofComponents (fun n => koszulPowerTopCohomologyIsoQuotient fs E n) (by
    intro n m h
    exact koszulPowerTopCohomologyIsoQuotient_naturality fs E (leOfHom h))

/-- The explicit power-quotient colimit is the original stable top Koszul
cohomology, for every commutative ring and every coefficient module. -/
def koszulTopQuotientColimitIsoStable (fs : List R) (E : ModuleCat.{u} R) :
    colimit (koszulTopQuotientDiagram fs E) ≅ stableKoszulCohomology fs E fs.length :=
  HasColimit.isoOfNatIso (koszulTopQuotientDiagramIso fs E).symm ≪≫
    Functor.Final.colimitIso (opOpEquivalence ℕ).inverse _

/-- The colimit comparison retains the original map from every Koszul
cohomology stage; no new choice of a stage map is made. -/
@[reassoc]
theorem koszulTopQuotientColimitIsoStable_ι (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    colimit.ι (koszulTopQuotientDiagram fs E) n ≫
        (koszulTopQuotientColimitIsoStable fs E).hom =
      (koszulPowerTopCohomologyIsoQuotient fs E n).inv ≫
        colimit.ι (koszulCohomologyDiagram fs E fs.length) (op (op n)) := by
  dsimp only [koszulTopQuotientColimitIsoStable, Iso.trans_hom]
  erw [HasColimit.isoOfNatIso_ι_hom_assoc, Functor.Final.ι_colimitIso_hom]
  rfl

/-- Over a noetherian ring, the colimit of the actual power-ideal
quotients with product-multiplication maps is the original algebraic
local cohomology in top Koszul degree. No regularity is required. -/
def koszulTopQuotientColimitIsoLocalCohomology [IsNoetherianRing R]
    (fs : List R) (E : ModuleCat.{u} R) :
    colimit (koszulTopQuotientDiagram fs E) ≅
      (_root_.localCohomology (koszulIdeal fs) fs.length).obj E :=
  koszulTopQuotientColimitIsoStable fs E ≪≫
    (stableKoszulCohomologyFunctorObjIso fs fs.length E).symm ≪≫
      (localCohomologyIsoStableKoszul fs fs.length).symm.app E

/-- Stage compatibility with the already constructed comparison from
the original stable Koszul cohomology to original local cohomology. -/
@[reassoc]
theorem koszulTopQuotientColimitIsoLocalCohomology_ι [IsNoetherianRing R]
    (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    colimit.ι (koszulTopQuotientDiagram fs E) n ≫
        (koszulTopQuotientColimitIsoLocalCohomology fs E).hom =
      (koszulPowerTopCohomologyIsoQuotient fs E n).inv ≫
        colimit.ι (koszulCohomologyDiagram fs E fs.length) (op (op n)) ≫
          (stableKoszulCohomologyFunctorObjIso fs fs.length E).inv ≫
            (localCohomologyIsoStableKoszul fs fs.length).inv.app E := by
  simp only [koszulTopQuotientColimitIsoLocalCohomology, Iso.trans_hom, Iso.symm_hom,
    koszulTopQuotientColimitIsoStable_ι_assoc]
  rfl

end SGA.SGA2.ExposeII
