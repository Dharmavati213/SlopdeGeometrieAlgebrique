/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.HomArtinianCriterion
import SGA.SGA2.ExposeIV.CompletionArtinian
import SGA.SGA2.ExposeIV.MatlisCompletedRingDuality
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Full Artinianity of the original Matlis category

Over a complete base, finiteness of the actual dual and the orthogonal
submodule embedding imply the full descending-chain condition. Over a
noncomplete base, the original completion equivalence and equality of
supported submodule lattices give the same conclusion. Completed-ring
noetherianity and duality are proved inputs, not extra assumptions.
Conversely every Artinian module is locally Artinian with finite socle,
so the original category is exactly the full category of Artinian modules.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {H : ModuleCat.{u} R} (hH : SupportedDualizingModule H)

include hH

/-- Over a complete base, every original locally Artinian finite-socle
module is actually Artinian. -/
theorem SupportedDualizingModule.matlisArtinian_isArtinian_complete
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (X : MatlisArtinianModuleCat R) :
    IsArtinian R X.obj := by
  have := X.property.2
  have := hH.supported_finiteSocle_dual_finite X.obj X.supported
  exact hH.isArtinian_of_noetherian_dual X.obj

/-- Every object of the literal original Matlis category has the full
descending-chain condition, without completeness of the original ring. -/
theorem SupportedDualizingModule.matlisArtinian_isArtinian
    (X : MatlisArtinianModuleCat R) : IsArtinian R X.obj := by
  let J := IsLocalRing.maximalIdeal R
  let e := matlisArtinianCompletionEquivalence (R := R)
  let Y := e.functor.obj X
  have : IsArtinian (AdicCompletion J R) Y.obj :=
    hH.completion.matlisArtinian_isArtinian_complete Y
  have hs : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) Y.obj := by
    simpa only [AdicCompletion.maximalIdeal_eq_map] using Y.supported
  have : IsArtinian R ((matlisArtinianModuleProperty R).ι.obj ((e.functor ⋙ e.inverse).obj X)) := by
    change IsArtinian R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj Y.obj)
    exact completion_restrictScalars_isArtinian J Y.obj hs
  exact isArtinian_of_linearEquiv
    (((matlisArtinianModuleProperty R).ι.mapIso (e.unitIso.app X)).symm.toLinearEquiv)

/-- In particular the actual Hom dual of every finite module is Artinian. -/
theorem SupportedDualizingModule.finiteSource_dual_isArtinian
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsArtinian R ((moduleHomDual H).obj (op M)) :=
  hH.matlisArtinian_isArtinian ⟨_, hH.finiteSource_dual_locallyArtinian_finiteSocle M⟩

omit hH

/-- The full Artinian conclusion does not require a chosen dualizing module:
its existence over every noetherian local ring was proved in IV.4.7. -/
theorem matlisArtinianModuleProperty_isArtinian (X : ModuleCat.{u} R)
    (hX : matlisArtinianModuleProperty R X) : IsArtinian R X := by
  obtain ⟨H, hH⟩ := exists_supportedDualizingModule (R := R)
  exact hH.matlisArtinian_isArtinian ⟨X, hX⟩

omit [IsNoetherianRing R] in
/-- An Artinian module has a finite-dimensional actual residue-field socle,
and hence satisfies the literal defining conditions of `CA`. -/
theorem matlisArtinianModuleProperty_of_isArtinian (X : ModuleCat.{u} R)
    [IsArtinian R X] : matlisArtinianModuleProperty R X := by
  refine ⟨fun N _ => inferInstance, ?_⟩
  apply (localSocle_finite_iff_finite_residue R X).mpr
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have : IsArtinian (R ⧸ IsLocalRing.maximalIdeal R) (localSocle (R := R) X) :=
    isArtinian_of_tower R inferInstance
  have : IsNoetherian (R ⧸ IsLocalRing.maximalIdeal R) (localSocle (R := R) X) :=
    IsSemiprimaryRing.isNoetherian_iff_isArtinian.mpr inferInstance
  infer_instance

/-- Over a noetherian local ring, the original Matlis category `CA` consists
exactly of all Artinian modules, including when the ring is not complete. -/
theorem matlisArtinianModuleProperty_iff_isArtinian (X : ModuleCat.{u} R) :
    matlisArtinianModuleProperty R X ↔ IsArtinian R X :=
  ⟨matlisArtinianModuleProperty_isArtinian X,
    fun _ => matlisArtinianModuleProperty_of_isArtinian X⟩

end SGA.SGA2.ExposeIV
