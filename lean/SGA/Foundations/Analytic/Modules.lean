/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import SGA.Foundations.Cohomology.CechPullback

/-!
# Sheaves of modules on locally ringed spaces

Mathlib has sheaves of modules on schemes (`AlgebraicGeometry.Scheme.Modules`), with pullback and
pushforward. Analytic spaces are locally ringed spaces, not schemes; this file copies the minimal
part of that API for an arbitrary locally ringed space `X`, so that `𝒪_{X^an}`-modules and the
analytification `F ↦ F^an = φ^* F` along `φ : X^an → X` can be stated (SGA 1 XII §4):

* `LocallyRingedSpace.ringCatSheaf X`, `LocallyRingedSpace.Modules X` (the abelian category of
  sheaves of `𝒪_X`-modules), definitionally `Scheme.Modules X` when `X` is a scheme
  (`LocallyRingedSpace.modules_scheme`);
* `Modules.pullback f`, `Modules.pushforward f`, and their adjunction, for a morphism `f` of
  locally ringed spaces (mathlib's `SheafOfModules.pullback` along `f^♯`);
* `Modules.toAbSheaf`, `Modules.H M n = Hⁿ(X, M)` (cohomology of the underlying abelian sheaf, as
  in `SGA.Foundations.Cohomology.Basic` for schemes);
* `Modules.pullbackCohomologyMap f M n : Hⁿ(Y, M) →+ Hⁿ(X, f^* M)`, the canonical map induced by
  the exact functor `f⁻¹` on abelian sheaves and the morphism `f⁻¹ M → f^* M`
  (`TopCat.Sheaf.globalCohomologyPullbackMap` of `SGA.Foundations.Cohomology.CechPullback`; the
  inverse image `f⁻¹`, its exactness and `ℤ_X → f⁻¹ ℤ_Y` are taken from there).

References: EGA 0_I 4.3, 5.3; EGA 0_III 12.1; Stacks Project, Tags 01AE, 01BQ (Section 17.10).
-/

universe u

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The structure sheaf of a locally ringed space, as a sheaf of (noncommutative) rings. -/
abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `𝒪_X`-modules on a locally ringed space. -/
def Modules := SheafOfModules.{u} X.ringCatSheaf

instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules.{u} X.ringCatSheaf))

instance : Abelian X.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} X.ringCatSheaf))

/-- For a scheme `X`, `𝒪_X`-modules on the locally ringed space of `X` are `Scheme.Modules X`. -/
lemma modules_scheme (X : Scheme.{u}) : X.toLocallyRingedSpace.Modules = X.Modules := rfl

variable {X} {Y : LocallyRingedSpace.{u}}

/-- The morphism of sheaves of rings `𝒪_Y → f_* 𝒪_X` of a morphism of locally ringed spaces. -/
def Hom.toRingCatSheafHom (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf where
  hom := Functor.whiskerRight f.c _

namespace Modules

/-- The pushforward `f_* : 𝒪_X-Mod → 𝒪_Y-Mod`. -/
def pushforward (f : X ⟶ Y) : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency.types false in
-- as in mathlib's `Scheme.Modules.pullback`: needed to find the right adjoint instance
/-- The pullback `f^* : 𝒪_Y-Mod → 𝒪_X-Mod`. -/
def pullback (f : X ⟶ Y) : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency.types false in
/-- `f^*` is left adjoint to `f_*`. -/
def pullbackPushforwardAdjunction (f : X ⟶ Y) : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

/-- The underlying abelian sheaf of an `𝒪_X`-module. -/
abbrev toAbSheaf (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- `Hⁿ(X, M)`, the cohomology of the underlying abelian sheaf of an `𝒪_X`-module. -/
abbrev H (M : X.Modules) (n : ℕ) : Type u := M.toAbSheaf.H n

/-! ### Pulling back cohomology classes -/

section Cohomology

variable (f : X ⟶ Y)

/-- The inverse image `f⁻¹` of abelian sheaves: `TopCat.Sheaf.abPullback` for the underlying
continuous map (its exactness instances apply). -/
abbrev abPullback :
    Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  TopCat.Sheaf.abPullback f.base

/-- The adjunction `f⁻¹ ⊣ f_*` for abelian sheaves (`TopCat.Sheaf.abAdjunction`). -/
abbrev abAdjunction : abPullback f ⊣ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  TopCat.Sheaf.abAdjunction f.base

/-- The constant sheaf `ℤ` (as `ULift ℤ`) on a locally ringed space (`TopCat.Sheaf.constZ`). -/
abbrev constZ (X : LocallyRingedSpace.{u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  TopCat.Sheaf.constZ X.carrier

/-- The adjunction between the constant sheaf functor and global sections
(`TopCat.Sheaf.constAdj`). -/
abbrev constAdj (X : LocallyRingedSpace.{u}) :=
  TopCat.Sheaf.constAdj X.carrier

/-- The canonical morphism `ℤ_X → f⁻¹ ℤ_Y`: the image of the section `1` of `ℤ_Y`
(`TopCat.Sheaf.constZToPullback`). -/
abbrev constZToPullback : constZ X ⟶ (abPullback f).obj (constZ Y) :=
  TopCat.Sheaf.constZToPullback f.base

/-- The canonical morphism of abelian sheaves `f⁻¹ M → f^* M`, adjoint to the underlying morphism
of abelian sheaves of the unit `M → f_* f^* M`. -/
def abPullbackToPullback (M : Y.Modules) :
    (abPullback f).obj M.toAbSheaf ⟶ ((pullback f).obj M).toAbSheaf :=
  ((abAdjunction f).homEquiv _ _).symm
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map
      ((pullbackPushforwardAdjunction f).unit.app M))

/-- The canonical map `Hⁿ(Y, M) → Hⁿ(X, f^* M)` (EGA 0_III 12.1.3.1): apply the exact functor `f⁻¹`
to `Ext`, then compose with `ℤ_X → f⁻¹ ℤ_Y` and `f⁻¹ M → f^* M`; that is,
`TopCat.Sheaf.globalCohomologyPullbackMap` for `f⁻¹ M → f^* M`. -/
def pullbackCohomologyMap (M : Y.Modules) (n : ℕ) : M.H n →+ ((pullback f).obj M).H n :=
  TopCat.Sheaf.globalCohomologyPullbackMap (f := f.base) (abPullbackToPullback f M) n

end Cohomology

end Modules

end AlgebraicGeometry.LocallyRingedSpace
