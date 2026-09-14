/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleExtPairing
import SGA.SGA2.ExposeIV.SupportedExtDiagram

/-!
# The canonical local-duality map

The original Yoneda pairings on quotient Ext descend along the actual
ideal-power diagram to a map from local cohomology into the dual of Ext.
This construction works over every commutative ring. It does not assert
the local-duality isomorphism theorem, which requires further hypotheses.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original quotient-Ext structural map into local cohomology. -/
def localCohomologyPowerStageι (J : Ideal R) (P : ModuleCat.{u} R) (n k : ℕ) :
    (moduleExtPowerDiagram J P n).obj k ⟶ (_root_.localCohomology J n).obj P :=
  (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram J) n)
    (op (op k))).app P

@[reassoc]
theorem localCohomologyPowerStageι_eq (J : Ideal R) (P : ModuleCat.{u} R) (n k : ℕ) :
    localCohomologyPowerStageι J P n k =
      colimit.ι (moduleExtPowerDiagram J P n) k ≫
        (moduleExtPowerColimitIsoLocalCohomology J P n).hom :=
  (moduleExtPowerColimitIsoLocalCohomology_ι J P n k).symm

@[reassoc (attr := simp)]
theorem localCohomologyPowerStageι_transition (J : Ideal R) (P : ModuleCat.{u} R)
    (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    (moduleExtPowerDiagram J P n).map (homOfLE h) ≫
      localCohomologyPowerStageι J P n l = localCohomologyPowerStageι J P n k := by
  simp only [localCohomologyPowerStageι_eq, colimit.w_assoc]

/-- The target is literally `Hom_R(Ext^j(M,P), H^n_J(P))`. -/
abbrev localDualityTargetValue (J : Ideal R) (M P : ModuleCat.{u} R) (j n : ℕ) :
    ModuleCat.{u} R :=
  ModuleCat.of R (moduleExtValue M P j →ₗ[R] (_root_.localCohomology J n).obj P)

/-- The canonical pairing at the original quotient stage. -/
def localDualityPowerStage (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) (k : ℕ) :
    (moduleExtPowerDiagram J M i).obj k ⟶ localDualityTargetValue J M P j n :=
  ModuleCat.ofHom
    { toFun := fun x => (localCohomologyPowerStageι J P n k).hom.comp
        (moduleExtPairing (ModuleCat.of R (R ⧸ J ^ k)) M P i j n h x)
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro r x; ext z; simp }

@[simp]
theorem localDualityPowerStage_apply (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) (k : ℕ)
    (x : (moduleExtPowerDiagram J M i).obj k) (y : moduleExtValue M P j) :
    localDualityPowerStage J M P i j n h k x y =
      localCohomologyPowerStageι J P n k
        (moduleExtPairing (ModuleCat.of R (R ⧸ J ^ k)) M P i j n h x y) := rfl

/-- Naturality of the original Ext pairing makes these maps compatible
with the original ideal-power transition maps. -/
@[reassoc]
theorem localDualityPowerStage_transition (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) {k l : ℕ} (hkl : k ≤ l) :
    (moduleExtPowerDiagram J M i).map (homOfLE hkl) ≫
      localDualityPowerStage J M P i j n h l = localDualityPowerStage J M P i j n h k := by
  apply ModuleCat.hom_ext
  ext x y
  change localCohomologyPowerStageι J P n l
      (moduleExtPairing (ModuleCat.of R (R ⧸ J ^ l)) M P i j n h
        (((_root_.Ext R (ModuleCat.{u} R) i).map
          (ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hkl))).op).app M x) y) = _
  rw [moduleExtPairing_naturality_first]
  change ((moduleExtPowerDiagram J P n).map (homOfLE hkl) ≫
    localCohomologyPowerStageι J P n l) _ = _
  rw [localCohomologyPowerStageι_transition]
  rfl

/-- The actual quotient-Ext pairings form a cocone. -/
def localDualityPowerCocone (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) : Cocone (moduleExtPowerDiagram J M i) where
  pt := localDualityTargetValue J M P j n
  ι :=
    { app := localDualityPowerStage J M P i j n h
      naturality := fun k l f => by
        have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
        rw [hf]
        change _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact localDualityPowerStage_transition J M P i j n h (leOfHom f) }

/-- The canonical local-duality map, defined by the original Yoneda pairing
and the actual local-cohomology colimit. -/
def localDualityMap (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) :
    (_root_.localCohomology J i).obj M ⟶ localDualityTargetValue J M P j n :=
  (moduleExtPowerColimitIsoLocalCohomology J M i).inv ≫
    colimit.desc _ (localDualityPowerCocone J M P i j n h)

/-- The canonical map agrees with the literal pairing at every original
Ext stage, not just after an unspecified colimit comparison. -/
@[reassoc (attr := simp)]
theorem localDualityMap_stage (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) (k : ℕ) :
    localCohomologyPowerStageι J M i k ≫ localDualityMap J M P i j n h =
      localDualityPowerStage J M P i j n h k := by
  simp [localCohomologyPowerStageι_eq, localDualityMap, localDualityPowerCocone]

/-- The original quotient-Ext inclusions are natural in the coefficient module. -/
@[reassoc]
theorem localCohomologyPowerStageι_naturality (J : Ideal R)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (i k : ℕ) :
    ((_root_.Ext R (ModuleCat.{u} R) i).obj (op (ModuleCat.of R (R ⧸ J ^ k)))).map f ≫
      localCohomologyPowerStageι J M' i k =
    localCohomologyPowerStageι J M i k ≫ (_root_.localCohomology J i).map f :=
  (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram J) i)
    (op (op k))).naturality f

/-- Contravariance of Ext followed by contravariance of Hom gives the
actual covariant target functor of the local-duality map. -/
def localDualityTargetFunctor (J : Ideal R) (P : ModuleCat.{u} R) (j n : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := localDualityTargetValue J M P j n
  map f := ModuleCat.ofHom
    { toFun := fun φ => φ.comp (((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P).hom
      map_add' := by intro φ ψ; rfl
      map_smul' := by intro r φ; rfl }
  map_id M := by
    apply ModuleCat.hom_ext
    ext φ x
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext φ x
    simp

@[simp]
theorem localDualityTargetFunctor_map_apply (J : Ideal R) (P : ModuleCat.{u} R)
    (j n : ℕ) {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (φ : localDualityTargetValue J M P j n) (y : moduleExtValue M' P j) :
    (show localDualityTargetValue J M' P j n from
      (localDualityTargetFunctor J P j n).map f φ) y =
      φ (((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P y) := rfl

/-- The actual stage pairing is natural in the middle module. -/
@[reassoc]
theorem localDualityPowerStage_naturality (J : Ideal R) (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) {M M' : ModuleCat.{u} R} (f : M ⟶ M') (k : ℕ) :
    ((_root_.Ext R (ModuleCat.{u} R) i).obj (op (ModuleCat.of R (R ⧸ J ^ k)))).map f ≫
      localDualityPowerStage J M' P i j n h k =
    localDualityPowerStage J M P i j n h k ≫ (localDualityTargetFunctor J P j n).map f := by
  apply ModuleCat.hom_ext
  ext x y
  exact congrArg (localCohomologyPowerStageι J P n k)
    (moduleExtPairing_naturality_middle (ModuleCat.of R (R ⧸ J ^ k)) f P i j n h x y)

/-- Naturality of the canonical map on the original local-cohomology objects. -/
@[reassoc]
theorem localDualityMap_naturality (J : Ideal R) (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (_root_.localCohomology J i).map f ≫ localDualityMap J M' P i j n h =
      localDualityMap J M P i j n h ≫ (localDualityTargetFunctor J P j n).map f := by
  apply (cancel_epi (moduleExtPowerColimitIsoLocalCohomology J M i).hom).mp
  apply colimit.hom_ext
  intro k
  simp only [← Category.assoc, moduleExtPowerColimitIsoLocalCohomology_ι]
  change (localCohomologyPowerStageι J M i k ≫ _) ≫ _ =
    (localCohomologyPowerStageι J M i k ≫ _) ≫ _
  rw [← localCohomologyPowerStageι_naturality, Category.assoc, localDualityMap_stage,
    localDualityMap_stage, localDualityPowerStage_naturality]

/-- The canonical local-duality transformation, with no regularity or
finiteness assumptions needed for its construction. -/
def localDualityNatTrans (J : Ideal R) (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) :
    _root_.localCohomology J i ⟶ localDualityTargetFunctor J P j n where
  app M := localDualityMap J M P i j n h
  naturality _ _ f := localDualityMap_naturality J P i j n h f

end SGA.SGA2.ExposeV
