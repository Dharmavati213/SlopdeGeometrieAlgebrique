/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.RestrictOpen
import SGA.Foundations.Analytic.ModulesStalkFree
import Mathlib.Topology.Sheaves.Module

/-!
# Restriction of `𝒪_X`-modules to open subspaces

For a locally ringed space `X` and an open `U ⊆ X`,
`LocallyRingedSpace.Modules.restrictOpenFunctor U` restricts `𝒪_X`-modules to `𝒪_U`-modules on
the open subspace `X.restrict U.isOpenEmbedding`
(mathlib's `SheafOfModules.pushforward` along the inclusion of opens). Its sections over an open
`V ⊆ U` are definitionally the sections over the image of `V` in `X`
(`restrictOpenFunctor_presheaf`), and its underlying abelian sheaf is definitionally the
restriction `TopCat.Sheaf.restrictFunctor U` of the underlying abelian sheaf
(`toAbSheaf_restrictOpenFunctor`). Hence (`SGA.Foundations.Cohomology.RestrictOpen`):

* `restrictOpenH'AddEquiv`: `Hⁿ(V', M) ≃+ Hⁿ(V, M|_U)` for an open `V` of `U` with image `V'`,
  cohomology over `V'` computed on `X` and over `V` computed on `U`;
* `restrictOpenStalkEquiv`: the stalks of `M|_U` are the stalks of `M`, semilinearly for the
  canonical isomorphism of local rings.

The functor and the stalk comparison follow the unmerged branch `codex/foundations-missing-inputs`
(commit `c65c9a0`, file `ModuleHomRestriction.lean`). References: EGA 0_I 4.1.9 (restriction of
sheaves to open subspaces), Stacks Project, Tag 01AK.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

/-- Restriction of `𝒪_X`-modules to the open locally ringed subspace `U`. -/
def restrictOpenFunctor (U : Opens X) : X.Modules ⥤ (X.restrict U.isOpenEmbedding).Modules :=
  haveI : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toSheafedSpace)
      (Opens.grothendieckTopology X.toSheafedSpace) :=
    U.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (F := U.isOpenEmbedding.functor)
    (R := X.ringCatSheaf) (S := (X.restrict U.isOpenEmbedding).ringCatSheaf) ⟨𝟙 _⟩

/-- The sections of the restriction over `V ⊆ U` are the sections over the image of `V`. -/
lemma restrictOpenFunctor_presheaf (U : Opens X) (M : X.Modules) :
    ((restrictOpenFunctor U).obj M).presheaf = U.isOpenEmbedding.functor.op ⋙ M.presheaf :=
  rfl

/-- The underlying abelian sheaf of the restriction is the restriction of the underlying abelian
sheaf. -/
lemma toAbSheaf_restrictOpenFunctor (U : Opens X) (M : X.Modules) :
    ((restrictOpenFunctor U).obj M).toAbSheaf = (TopCat.Sheaf.restrictFunctor U).obj M.toAbSheaf :=
  rfl

/-- **Cohomology over an open subspace**: for an open `V` of `U` with image `V'` in `X`,
`Hⁿ(V', M) ≃+ Hⁿ(V, M|_U)`. -/
def restrictOpenH'AddEquiv (U : Opens X) (M : X.Modules) (n : ℕ) (V : Opens U) :
    M.toAbSheaf.H' n (TopCat.Sheaf.openImage V) ≃+
      ((restrictOpenFunctor U).obj M).toAbSheaf.H' n V :=
  TopCat.Sheaf.restrictH'AddEquiv M.toAbSheaf n V

/-- For opens `V ≤ U` of `X`: `Hⁿ(V, M) ≃+ Hⁿ(V ∩ U, M|_U)`. -/
def restrictOpenH'AddEquivOfLE (U : Opens X) (M : X.Modules) (n : ℕ) {V : Opens X}
    (h : V ≤ U) :
    M.toAbSheaf.H' n V ≃+
      ((restrictOpenFunctor U).obj M).toAbSheaf.H' n (TopCat.Sheaf.openPreimage U V) :=
  TopCat.Sheaf.restrictH'AddEquivOfLE M.toAbSheaf n h

/-- Restricting a module sheaf to an open neighbourhood does not change its stalk,
as an abelian group. -/
def restrictOpenStalkAddIso (U : Opens X) (M : X.Modules) (x : U) :
    ((restrictOpenFunctor U).obj M).presheaf.stalk x ≅ M.presheaf.stalk x.1 := by
  rw [restrictOpenFunctor_presheaf]
  exact (show PresheafedSpace AddCommGrpCat.{u} from ⟨X.toTopCat, M.presheaf⟩).restrictStalkIso
    U.isOpenEmbedding x

@[simp] lemma restrictOpenStalkAddIso_germ (U : Opens X) (M : X.Modules) (x : U)
    (V : Opens U) (hx : x ∈ V)
    (s : ((restrictOpenFunctor U).obj M).presheaf.obj (op V)) :
    (restrictOpenStalkAddIso U M x).hom
      (((restrictOpenFunctor U).obj M).presheaf.germ V x hx s) =
      M.presheaf.germ (U.isOpenEmbedding.functor.obj V) x.1 ⟨x, hx, rfl⟩ s :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (show PresheafedSpace AddCommGrpCat.{u} from ⟨X.toTopCat, M.presheaf⟩)
      U.isOpenEmbedding V x hx s

/-- The comparison of local rings for an open subspace. -/
abbrev restrictOpenRingIso (U : Opens X) (x : U) :
    (X.restrict U.isOpenEmbedding).presheaf.stalk x ≅ X.presheaf.stalk x.1 :=
  X.restrictStalkIso U.isOpenEmbedding x

instance restrictOpenStalkRingHomInvPair (U : Opens X) (x : U) :
    RingHomInvPair (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.toRingHom
      (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (restrictOpenRingIso U x).commRingCatIsoToRingEquiv

instance restrictOpenStalkRingHomInvPairSymm (U : Opens X) (x : U) :
    RingHomInvPair (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.symm.toRingHom
      (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (restrictOpenRingIso U x).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
-- the module structures on stalks are only defeq after unfolding `restrictOpenFunctor`
/-- The stalk comparison for an open subspace is semilinear for the canonical isomorphism of
local rings. -/
def restrictOpenStalkEquiv (U : Opens X) (M : X.Modules) (x : U) :
    ((restrictOpenFunctor U).obj M).presheaf.stalk x ≃ₛₗ[
      (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.toRingHom]
        M.presheaf.stalk x.1 where
  __ := (restrictOpenStalkAddIso U M x).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    obtain ⟨V, hxV, r, rfl⟩ := (X.restrict U.isOpenEmbedding).presheaf.exists_germ_eq r
    obtain ⟨W, hWV, hxW, m, rfl⟩ :=
      ((restrictOpenFunctor U).obj M).presheaf.exists_le_germ_eq m hxV
    rw [← (X.restrict U.isOpenEmbedding).presheaf.germ_res_apply (homOfLE hWV) x hxW r,
      ← germ_smul]
    change (restrictOpenStalkAddIso U M x).hom
      (((restrictOpenFunctor U).obj M).presheaf.germ W x hxW
        ((X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hWV).op r • m)) = _
    rw [restrictOpenStalkAddIso_germ]
    rw [germ_smul]
    exact congrArg₂ (fun (r : X.presheaf.stalk x.1) (m : M.presheaf.stalk x.1) ↦ r • m)
      (X.restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding W x hxW _).symm
      (restrictOpenStalkAddIso_germ U M x W hxW m).symm

@[simp] lemma restrictOpenStalkEquiv_germ (U : Opens X) (M : X.Modules) (x : U)
    (V : Opens U) (hx : x ∈ V)
    (s : ((restrictOpenFunctor U).obj M).presheaf.obj (op V)) :
    restrictOpenStalkEquiv U M x (((restrictOpenFunctor U).obj M).presheaf.germ V x hx s) =
      M.presheaf.germ (U.isOpenEmbedding.functor.obj V) x.1 ⟨x, hx, rfl⟩ s :=
  restrictOpenStalkAddIso_germ U M x V hx s

end AlgebraicGeometry.LocallyRingedSpace.Modules
