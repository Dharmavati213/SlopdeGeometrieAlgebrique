/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDuality
import SGA.SGA2.ExposeIV.MatlisBidualCompletion

/-!
# The canonical transpose of local duality

The transpose `Extʲ(M,P) → Hom(Hⁱ_J(M), Hⁿ_J(P))` evaluates the original
canonical pairing with the Ext class in the second slot. It factors as
actual bidual evaluation followed by dualizing the original local-duality
map, including the literal categorical Hom comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The canonical local-duality map with its target written as actual
categorical Hom, retaining exactly the same linear maps. -/
def localDualityHomMap (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) :
    (_root_.localCohomology J i).obj M ⟶
      (moduleHomDual ((_root_.localCohomology J n).obj P)).obj (op (moduleExtValue M P j)) :=
  localDualityMap J M P i j n h ≫ (localDualityTargetIsoHom J P j n).hom.app M

/-- The canonical transpose is original bidual evaluation followed by
actual precomposition with the canonical local-duality map. -/
def localDualityTransposeMap (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) :
    moduleExtValue M P j ⟶
      (moduleHomDual ((_root_.localCohomology J n).obj P)).obj
        (op ((_root_.localCohomology J i).obj M)) :=
  moduleBidualEvaluation ((_root_.localCohomology J n).obj P) (moduleExtValue M P j) ≫
    (moduleHomDual ((_root_.localCohomology J n).obj P)).map
      (localDualityHomMap J M P i j n h).op

/-- The transpose evaluates the unchanged original pairing. -/
@[simp]
theorem localDualityTransposeMap_apply (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) (y : moduleExtValue M P j)
    (x : (_root_.localCohomology J i).obj M) :
    (localDualityTransposeMap J M P i j n h y).hom x =
      localDualityMap J M P i j n h x y := rfl

instance localDualityHomMap_isIso (J : Ideal R) (M P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) [IsIso (localDualityMap J M P i j n h)] :
    IsIso (localDualityHomMap J M P i j n h) := by
  unfold localDualityHomMap
  infer_instance

/-- The transpose commutes with original contravariant Ext maps and
the original local-cohomology coefficient maps. -/
@[reassoc]
theorem localDualityTransposeMap_naturality (J : Ideal R) (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    ((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P ≫
        localDualityTransposeMap J M P i j n h =
      localDualityTransposeMap J M' P i j n h ≫
        (moduleHomDual ((_root_.localCohomology J n).obj P)).map
          ((_root_.localCohomology J i).map f).op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hn := ConcreteCategory.congr_hom (localDualityMap_naturality J P i j n h f) x
  exact (congrArg (fun z : localDualityTargetValue J M' P j n => z y) hn).symm

/-- The original transpose, naturally contravariant in the coefficient module. -/
def localDualityTransposeNatTrans (J : Ideal R) (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n) :
    (_root_.Ext R (ModuleCat.{u} R) j).flip.obj P ⟶
      (_root_.localCohomology J i).op ⋙ moduleHomDual ((_root_.localCohomology J n).obj P) where
  app M := localDualityTransposeMap J M.unop P i j n h
  naturality _ _ f := localDualityTransposeMap_naturality J P i j n h f.unop

end SGA.SGA2.ExposeV
