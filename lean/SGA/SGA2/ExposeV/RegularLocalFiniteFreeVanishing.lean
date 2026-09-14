/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalDualityFiniteFree
import SGA.SGA2.ExposeV.RegularLocalVanishing

/-!
# Finite-free vanishing for descending local duality

Actual local cohomology on a finite coordinate module vanishes below the
dimension by additivity and the proved depth of the ring. Actual positive
Ext from the same free module vanishes by projectivity.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open scoped BigOperators
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Additivity transports vanishing on the ring to all finite coordinate modules. -/
theorem isZero_obj_finiteFree (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
    (hz : IsZero (F.obj (ModuleCat.of R R))) (r : ℕ) :
    IsZero (F.obj (ModuleCat.of R (Fin r → R))) := by
  classical
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  have h : ∑ i : Fin r, U.map (finiteFreeProjection r i) ≫
      U.map (finiteModulePoint (FGModuleCat.of R (Fin r → R)) (Pi.single i 1)) = 𝟙 _ := by
    simpa only [Functor.map_sum, Functor.map_comp, U.map_id] using
      congrArg U.map (finiteFree_identity (R := R) r)
  rw [IsZero.iff_id_eq_zero]
  rw [← F.map_id]
  change F.map (𝟙 (U.obj (FGModuleCat.of R (Fin r → R)))) = 0
  rw [← h, F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [F.map_comp, hz.eq_zero_of_tgt (F.map (U.map (finiteFreeProjection r i))), zero_comp]

/-- Lower local cohomology of the original finite free module vanishes. -/
theorem regularLocal_localCohomology_finiteFree_isZero_of_lt [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) (r i : ℕ) (hi : i < n) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj
      (ModuleCat.of R (Fin r → R))) :=
  isZero_obj_finiteFree _ (regularLocal_localCohomology_ring_isZero_of_lt n hdim i hi) r

/-- Original module-valued Ext vanishes in positive degrees on a
projective first argument. -/
theorem moduleExt_isZero_of_projective (N P : ModuleCat.{u} R) [Projective N] (j : ℕ) :
    IsZero (moduleExtValue N P (j + 1)) :=
  (isZero_moduleExt_iff_subsingleton_ext N P (j + 1)).mpr
    (Abelian.Ext.subsingleton_of_projective N P j)

/-- In particular the actual finite coordinate module has no positive Ext. -/
theorem moduleExt_finiteFree_isZero (P : ModuleCat.{u} R) (r j : ℕ) :
    IsZero (moduleExtValue (ModuleCat.of R (Fin r → R)) P (j + 1)) :=
  moduleExt_isZero_of_projective _ P j

end SGA.SGA2.ExposeV
