/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityRing
import SGA.SGA2.ExposeV.FiniteFreeComparison

/-!
# The canonical top-degree comparison on finite free modules

Both original functors in V.2.1 are additive. Their canonical comparison is
therefore invertible on all finite coordinate modules by the proved
rank-one case. This step holds over every commutative ring and ideal.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIII
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

instance localCohomology_additive (J : Ideal R) (i : ℕ) :
    (_root_.localCohomology J i).Additive :=
  Functor.additive_of_iso (idealPowerExtIsoLocalCohomology J i)

instance localDualityTargetFunctor_additive (J : Ideal R) (P : ModuleCat.{u} R)
    (j n : ℕ) : (localDualityTargetFunctor J P j n).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change localDualityTargetValue J M P j n at φ
    apply LinearMap.ext
    intro y
    change φ (((_root_.Ext R (ModuleCat.{u} R) j).map (f + g).op).app P y) =
      φ (((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P y) +
        φ (((_root_.Ext R (ModuleCat.{u} R) j).map g.op).app P y)
    have h : (((_root_.Ext R (ModuleCat.{u} R) j).map (f + g).op).app P y) =
        (((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P y) +
          (((_root_.Ext R (ModuleCat.{u} R) j).map g.op).app P y) := by
      apply (moduleExtLinearEquivAbelianExt M P j).injective
      simp only [moduleExtLinearEquivAbelianExt_naturality_first, map_add,
        Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]
    rw [h, map_add]

/-- **V.2.1, finite free case.** The actual canonical map is invertible on
the original finite coordinate module, not just on an isomorphic value. -/
instance localDualityMap_finiteFree_top_isIso (J : Ideal R) (n r : ℕ) :
    IsIso (localDualityMap J (ModuleCat.of R (Fin r → R)) (ModuleCat.of R R)
      n 0 n (add_zero n)) := by
  let α := localDualityNatTrans J (ModuleCat.of R R) n 0 n (add_zero n)
  have : IsIso (α.app (ModuleCat.of R R)) := localDualityMap_ring_top_isIso R J n
  exact isIso_app_finiteFree α r

end SGA.SGA2.ExposeV
