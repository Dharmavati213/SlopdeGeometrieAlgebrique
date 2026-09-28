/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ProjectiveHomologyExtRepresentatives
import SGA.SGA2.ExposeV.ProjectiveExtConnectingCocycle

/-! # Degree-zero representatives for the original Ext comparison -/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

/-- The canonical opposite-homology comparison respects the original
cycle projection and opcycle inclusion. -/
theorem homologyOpIso_π {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) :
    S.op.homologyπ ≫ S.homologyOpIso.hom =
      S.cyclesOpIso.hom ≫ S.homologyι.op := by
  dsimp only [ShortComplex.homologyOpIso, Iso.trans_hom, Iso.symm_hom,
    Iso.op_hom, ShortComplex.homologyπ, ShortComplex.homologyι]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, op_comp]
  dsimp only [ShortComplex.leftHomologyOpIso]
  rw [← Category.assoc,
    S.rightHomologyData.op.leftHomologyπ_comp_leftHomologyIso_hom]
  rw [Category.assoc]
  rfl

/-- The same opposite-homology comparison respects the other two canonical
maps, with no additional choice of homology data. -/
theorem homologyOpIso_ι {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) :
    S.homologyOpIso.hom ≫ S.homologyπ.op =
      S.op.homologyι ≫ S.opcyclesOpIso.hom := by
  apply (cancel_epi S.op.homologyπ).mp
  rw [← Category.assoc, homologyOpIso_π, Category.assoc, ← op_comp,
    ShortComplex.homology_π_ι, op_comp, ← Category.assoc,
    ← S.cyclesOpIso_inv_op_iCycles, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ShortComplex.homology_π_ι, Category.assoc,
    S.op_pOpcycles_opcyclesOpIso_hom]

/-- In degree zero, the original opposite-homology comparison and cycle
inclusion recover the original opcycle projection. -/
theorem homologyUnop_zero_inclusion {C : Type*} [Category* C] [Abelian C]
    (K : ChainComplex Cᵒᵖ ℕ) :
    (K.homologyι 0).unop ≫ (K.homologyUnop 0).inv ≫
        (CochainComplex.isoHomologyπ₀ K.unop).inv ≫ K.unop.iCycles 0 =
      (K.pOpcycles 0).unop := by
  let S := K.unop.sc 0
  have : IsIso S.homologyπ :=
    inferInstanceAs (IsIso (CochainComplex.isoHomologyπ₀ K.unop).hom)
  have hι : S.homologyOpIso.inv ≫ S.op.homologyι =
      S.homologyπ.op ≫ S.opcyclesOpIso.inv := by
    apply (cancel_mono S.opcyclesOpIso.hom).mp
    rw [Category.assoc, ← homologyOpIso_ι S, Iso.inv_hom_id_assoc]
    simp
  apply Quiver.Hom.op_inj
  change ((S.iCycles.op ≫ (inv S.homologyπ).op) ≫ S.homologyOpIso.inv) ≫
    S.op.homologyι = S.op.pOpcycles
  have hc : (inv S.homologyπ).op ≫ S.homologyπ.op = 𝟙 _ := by
    rw [← op_comp, IsIso.hom_inv_id, op_id]
  rw [Category.assoc, hι]
  simp only [Category.assoc, reassoc_of% hc]
  exact (Iso.comp_inv_eq S.opcyclesOpIso).mpr S.op_pOpcycles_opcyclesOpIso_hom.symm

variable {R : Type u} [CommRing R] {N : ModuleCat.{u} R}

/-- The original degree-zero Ext-to-Hom comparison, computed on any actual
projective resolution, recovers precomposition with its augmentation. -/
theorem extZeroIsoHom_inv_isoExt_cycles (P : ProjectiveResolution N)
    (M : ModuleCat.{u} R) :
    ((extZeroIsoHom M).app (op N)).inv ≫ (P.isoExt 0 M).hom ≫
        (P.complex.linearYonedaObj R M).isoHomologyπ₀.inv ≫
        (P.complex.linearYonedaObj R M).iCycles 0 =
      ((linearYoneda R (ModuleCat R)).obj M).map (P.π.f 0).op := by
  let F := ((linearYoneda R (ModuleCat R)).obj M).rightOp
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  change (F.fromLeftDerivedZero.app N).unop ≫ _ = (F.map (P.π.f 0)).unop
  rw [P.fromLeftDerivedZero_eq F]
  dsimp only [ProjectiveResolution.isoExt, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv]
  simp only [unop_comp, Category.assoc]
  change (P.fromLeftDerivedZero' F).unop ≫ (K.homologyι 0).unop ≫
    (P.isoLeftDerivedObj F 0).unop.hom ≫ (P.isoLeftDerivedObj F 0).unop.inv ≫
      (K.homologyUnop 0).inv ≫ (CochainComplex.isoHomologyπ₀ K.unop).inv ≫
        K.unop.iCycles 0 = _
  rw [Iso.hom_inv_id_assoc, homologyUnop_zero_inclusion, ← unop_comp,
    P.pOpcycles_comp_fromLeftDerivedZero']

/-- The unchanged degree-zero comparison sends a cocycle to the unique
map whose precomposition with the original augmentation is that cocycle. -/
theorem extZeroIsoHom_isoExt_inv_mk (P : ProjectiveResolution N)
    (M : ModuleCat.{u} R) (f : P.complex.X 0 ⟶ M)
    (hf : P.complex.d 1 0 ≫ f = 0) :
    P.π.f 0 ≫ ((extZeroIsoHom M).app (op N)).hom
        ((P.isoExt 0 M).inv
          (moduleCohomologyMk (P.complex.linearYonedaObj R M) 0 f hf)) = f := by
  let K := P.complex.linearYonedaObj R M
  have h : (P.isoExt 0 M).inv ≫ ((extZeroIsoHom M).app (op N)).hom ≫
      ((linearYoneda R (ModuleCat R)).obj M).map (P.π.f 0).op =
        K.isoHomologyπ₀.inv ≫ K.iCycles 0 := by
    rw [← extZeroIsoHom_inv_isoExt_cycles P M]
    simp [K]
  have ht := ConcreteCategory.congr_hom h (moduleCohomologyMk K 0 f hf)
  change _ = K.iCycles 0
    (K.isoHomologyπ₀.inv (K.isoHomologyπ₀.hom (moduleCocycleLift K 0 f hf))) at ht
  have hc := ConcreteCategory.congr_hom K.isoHomologyπ₀.hom_inv_id
    (moduleCocycleLift K 0 f hf)
  change K.isoHomologyπ₀.inv (K.isoHomologyπ₀.hom (moduleCocycleLift K 0 f hf)) =
    moduleCocycleLift K 0 f hf at hc
  rw [hc, moduleCocycleLift_iCycles] at ht
  exact ht

open CochainComplex.HomComplex

/-- An original degree-zero chain map gives its ordinary shifted morphism. -/
theorem homCocycle_ofHom_eq_shiftedHom_mk₀
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ 0 rfl f := by
  ext p : 1
  simp [Cocycle.equivHomShift_symm_apply, ShiftedHom.mk₀, Cochain.rightShift_v,
    shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f, XIsoOfEq]

/-- A degree-zero cocycle induced by an actual map has that map's original
derived Ext class. -/
theorem projectiveExtCocycle_ofHom_augmentation (P : ProjectiveResolution N)
    {M : ModuleCat.{u} R} (g : N ⟶ M) :
    P.extEquivCohomologyClass.symm
        (CohomologyClass.mk (Cocycle.ofHom
          (P.π' ≫ (CochainComplex.singleFunctor (ModuleCat R) 0).map g))) =
      Abelian.Ext.mk₀ g := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  apply Abelian.Ext.ext
  rw [projectiveExtCocycle_hom]
  erw [homCocycle_ofHom_eq_shiftedHom_mk₀,
    ShiftedHom.map_mk₀, Abelian.Ext.mk₀_hom]
  simp only [ShiftedHom.mk₀, CategoryTheory.Functor.map_comp, Category.assoc,
    IsIso.inv_hom_id_assoc]
  rfl

/-- In degree zero, the original `extMk` representative of an augmented
map is exactly its degree-zero derived Ext class. -/
theorem projectiveExtMk_zero_augmentation (P : ProjectiveResolution N)
    {M : ModuleCat.{u} R} (g : N ⟶ M) :
    P.extMk (P.π.f 0 ≫ g) 1 rfl (by simp) = Abelian.Ext.mk₀ g := by
  rw [← projectiveExtCocycle_ofHom_augmentation P g]
  unfold ProjectiveResolution.extMk
  congr 2
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (K := P.cochainComplex) (X := M)
    (show (0 : ℤ) + 0 = 0 from rfl)).injective
  simp [Cochain.toSingleEquiv, ProjectiveResolution.π'_f_zero,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors, Category.assoc,
    single_map_f_self]

/-- The existing degree-zero linear comparison uses exactly the original
projective-resolution `extMk` class. -/
theorem moduleExtLinearEquivAbelianExt_zero_isoExt_inv_mk (P : ProjectiveResolution N)
    (M : ModuleCat.{u} R) (f : P.complex.X 0 ⟶ M)
    (hf : P.complex.d 1 0 ≫ f = 0) :
    moduleExtLinearEquivAbelianExt N M 0
        ((P.isoExt 0 M).inv
          (moduleCohomologyMk (P.complex.linearYonedaObj R M) 0 f hf)) =
      P.extMk f 1 rfl hf := by
  let g := ((extZeroIsoHom M).app (op N)).hom
    ((P.isoExt 0 M).inv (moduleCohomologyMk (P.complex.linearYonedaObj R M) 0 f hf))
  have hg : P.π.f 0 ≫ g = f := extZeroIsoHom_isoExt_inv_mk P M f hf
  change Abelian.Ext.mk₀ g = _
  have ht := projectiveExtMk_zero_augmentation P g
  simpa only [hg] using ht.symm

/-- In every degree, including zero, the original linear Ext comparison
sends an actual Hom-cohomology representative to its original `extMk`. -/
theorem moduleExtLinearEquivAbelianExt_isoExt_inv_mk (N M : ModuleCat.{u} R)
    (n : ℕ) (f : (projectiveResolution N).complex.X n ⟶ M)
    (hf : (projectiveResolution N).complex.d (n + 1) n ≫ f = 0) :
    moduleExtLinearEquivAbelianExt N M n
        (((projectiveResolution N).isoExt n M).inv
          (moduleCohomologyMk ((projectiveResolution N).complex.linearYonedaObj R M) n f hf)) =
      (projectiveResolution N).extMk f (n + 1) rfl hf := by
  cases n with
  | zero => exact moduleExtLinearEquivAbelianExt_zero_isoExt_inv_mk _ M f hf
  | succ n =>
      let P := projectiveResolution N
      let x := moduleCohomologyMk (P.complex.linearYonedaObj R M) (n + 1) f hf
      change (projectiveModuleHomologyLinearIsoExtSucc P M n).hom
        ((P.isoExt (n + 1) M).hom ((P.isoExt (n + 1) M).inv x)) = _
      have hx := ConcreteCategory.congr_hom (P.isoExt (n + 1) M).inv_hom_id x
      change (P.isoExt (n + 1) M).hom ((P.isoExt (n + 1) M).inv x) = x at hx
      rw [hx]
      exact projectiveModuleHomologyLinearIsoExtSucc_mk P M n f hf

end SGA.SGA2.ExposeV
