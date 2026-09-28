/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteIdeals
import SGA.SGA2.ExposeIV.SupportedQuotientStages

/-!
# Genuine quotient stages for finite-length modules

For a cofinite ideal `I`, restriction of scalars embeds the actual finite
`R/I`-modules fully faithfully and exactly into finite-length `R`-modules.
Every original finite-length module occurs in its annihilator stage; its
comparison is the identity on elements, with the quotient action obtained
from its original annihilation property.

No noetherian hypothesis on `R` is needed. The cofinite quotient rings are
themselves noetherian and Artinian, as consequences of their finite length.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Finite modules over a finite-length algebra have finite length over the
original ring: restrict an actual finite free surjection. -/
theorem isFiniteLength_of_finite_over_finiteLength_algebra
    (S : Type v) [CommRing S] [Algebra R S] (hS : IsFiniteLength R S)
    (M : Type w) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] : IsFiniteLength R M := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hS
  let : IsNoetherian R S := hN
  let : IsArtinian R S := hA
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  have hp : IsFiniteLength R (Fin n → S) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hp.of_surjective (f := f.restrictScalars R) hf

instance cofiniteQuotientIsNoetherianRing (I : CofiniteIdealIndex R) :
    IsNoetherianRing (R ⧸ I.val) :=
  isNoetherian_of_tower R
    (isFiniteLength_iff_isNoetherian_isArtinian.mp I.property).1

instance cofiniteQuotientIsArtinianRing (I : CofiniteIdealIndex R) :
    IsArtinianRing (R ⧸ I.val) :=
  isArtinian_of_tower R
    (isFiniteLength_iff_isNoetherian_isArtinian.mp I.property).2

/-- A finite module over the cofinite quotient has actual finite `R`-length. -/
theorem cofiniteQuotientRestriction_finiteLength (I : CofiniteIdealIndex R)
    (M : FGModuleCat.{u} (R ⧸ I.val)) :
    IsFiniteLength R
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj M.obj) := by
  have : IsScalarTower R (R ⧸ I.val)
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj M.obj) :=
    IsScalarTower.of_compHom R (R ⧸ I.val) M
  have : Module.Finite (R ⧸ I.val)
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).obj M.obj) :=
    inferInstanceAs (Module.Finite (R ⧸ I.val) M)
  exact isFiniteLength_of_finite_over_finiteLength_algebra
    (R ⧸ I.val) I.property _

/-- The genuine stage embedding is restriction of the original scalar action. -/
def cofiniteQuotientRestriction (I : CofiniteIdealIndex R) :
    FGModuleCat.{u} (R ⧸ I.val) ⥤ FiniteLengthModuleCat R :=
  (finiteLengthModuleProperty R).lift
    (forget₂ (FGModuleCat.{u} (R ⧸ I.val)) (ModuleCat.{u} (R ⧸ I.val)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk I.val))
    (cofiniteQuotientRestriction_finiteLength I)

instance (I : CofiniteIdealIndex R) : (cofiniteQuotientRestriction I).Full := by
  exact Functor.Full.of_comp_faithful_iso
    ((finiteLengthModuleProperty R).liftCompιIso _
      (cofiniteQuotientRestriction_finiteLength I))

instance (I : CofiniteIdealIndex R) : (cofiniteQuotientRestriction I).Faithful := by
  exact Functor.Faithful.of_comp_iso
    ((finiteLengthModuleProperty R).liftCompιIso _
      (cofiniteQuotientRestriction_finiteLength I))

instance (I : CofiniteIdealIndex R) : (cofiniteQuotientRestriction I).Additive := by
  constructor
  intro M N f g
  apply ObjectProperty.hom_ext
  exact (forget₂ (FGModuleCat (R ⧸ I.val)) (ModuleCat (R ⧸ I.val)) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk I.val)).map_add

/-- Forgetting the finite-length witness gives literally scalar restriction. -/
theorem cofiniteQuotientRestriction_comp_inclusion (I : CofiniteIdealIndex R) :
    cofiniteQuotientRestriction I ⋙ finiteLengthInclusion R =
      forget₂ (FGModuleCat.{u} (R ⧸ I.val)) (ModuleCat.{u} (R ⧸ I.val)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk I.val) := rfl

@[simp]
theorem cofiniteQuotientRestriction_map_apply (I : CofiniteIdealIndex R)
    {M N : FGModuleCat.{u} (R ⧸ I.val)} (f : M ⟶ N) (x : M) :
    ((cofiniteQuotientRestriction I).map f).hom x = f.hom x := rfl

/-- The ring object at a quotient stage is the original cofinite quotient. -/
def cofiniteQuotientRestriction_ringIso (I : CofiniteIdealIndex R) :
    (cofiniteQuotientRestriction I).obj (FGModuleCat.of (R ⧸ I.val) (R ⧸ I.val)) ≅
      cofiniteRingQuotient I :=
  (finiteLengthModuleProperty R).isoMk
    (LinearEquiv.toModuleIso (X₁ :=
      ((cofiniteQuotientRestriction I).obj
        (FGModuleCat.of (R ⧸ I.val) (R ⧸ I.val))).obj)
      (X₂ := (cofiniteRingQuotient I).obj)
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })

@[simp]
theorem cofiniteQuotientRestriction_ringIso_hom_apply (I : CofiniteIdealIndex R)
    (x : R ⧸ I.val) :
    (cofiniteQuotientRestriction_ringIso I).hom.hom x = x := rfl

@[simp]
theorem cofiniteQuotientRestriction_ringIso_inv_apply (I : CofiniteIdealIndex R)
    (x : R ⧸ I.val) :
    (cofiniteQuotientRestriction_ringIso I).inv.hom x = x := rfl

instance (I : CofiniteIdealIndex R) :
    PreservesFiniteLimits (cofiniteQuotientRestriction I) := by
  have : PreservesFiniteLimits
      (cofiniteQuotientRestriction I ⋙ finiteLengthInclusion R) :=
    comp_preservesFiniteLimits
      (forget₂ (FGModuleCat.{u} (R ⧸ I.val)) (ModuleCat.{u} (R ⧸ I.val)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.val))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteLengthInclusion R)

instance (I : CofiniteIdealIndex R) :
    PreservesFiniteColimits (cofiniteQuotientRestriction I) := by
  have : PreservesFiniteColimits
      (cofiniteQuotientRestriction I ⋙ finiteLengthInclusion R) :=
    comp_preservesFiniteColimits
      (forget₂ (FGModuleCat.{u} (R ⧸ I.val)) (ModuleCat.{u} (R ⧸ I.val)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I.val))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (finiteLengthInclusion R)

instance (I : CofiniteIdealIndex R) : (cofiniteQuotientRestriction I).PreservesHomology :=
  inferInstance

/-- Exactness in each stage is the original finite-length module exactness. -/
theorem cofiniteQuotientRestriction_shortExact_iff (I : CofiniteIdealIndex R)
    (S : ShortComplex (FGModuleCat.{u} (R ⧸ I.val))) :
    (S.map (cofiniteQuotientRestriction I)).ShortExact ↔ S.ShortExact :=
  ⟨fun h => CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (cofiniteQuotientRestriction I) h,
    fun h => h.map_of_exact (cofiniteQuotientRestriction I)⟩

/-- The stage ideal annihilates the original restricted module. -/
theorem cofiniteQuotientRestriction_annihilator (I : CofiniteIdealIndex R)
    (M : FGModuleCat.{u} (R ⧸ I.val)) :
    I.val ≤ Module.annihilator R ((cofiniteQuotientRestriction I).obj M).obj := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  change Ideal.Quotient.mk I.val r • (show M from x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- The original quotient action on a module annihilated by the stage ideal. -/
theorem finiteLengthModuleQuotientTorsion (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) :
    Module.IsTorsionBySet R M.obj (I.val : Set R) :=
  (Module.isTorsionBySet_iff_subset_annihilator R M.obj).mpr hI

/-- An actual quotient-ring module at any cofinite annihilating stage. -/
def finiteLengthModuleQuotientStage (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) :
    FGModuleCat.{u} (R ⧸ I.val) := by
  let hM := finiteLengthModuleQuotientTorsion M I hI
  let := hM.module
  let := Module.Finite.of_surjective hM.semilinearMap Function.surjective_id
  exact FGModuleCat.of (R ⧸ I.val) M.obj

@[simp]
theorem finiteLengthModuleQuotientStage_smul (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj)
    (r : R) (x : M.obj) :
    Ideal.Quotient.mk I.val r • (show finiteLengthModuleQuotientStage M I hI from x) =
      r • x := rfl

/-- An original map between annihilated modules is linear for their genuine
quotient actions. -/
def finiteLengthModuleQuotientStageMap {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N) :
    finiteLengthModuleQuotientStage M I hM ⟶ finiteLengthModuleQuotientStage N I hN :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (X := (finiteLengthModuleQuotientStage M I hM).obj)
    (Y := (finiteLengthModuleQuotientStage N I hN).obj)
    { toFun := fun x => f.hom x
      map_add' := f.hom.hom.map_add
      map_smul' := fun q x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact f.hom.hom.map_smul r x })

@[simp]
theorem finiteLengthModuleQuotientStageMap_apply {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N) (x : M.obj) :
    (finiteLengthModuleQuotientStageMap I hM hN f).hom x = f.hom x := rfl

/-- Stage coverage preserves the underlying group and the original `R`-action. -/
def finiteLengthModuleQuotientStageIso (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) :
    (cofiniteQuotientRestriction I).obj (finiteLengthModuleQuotientStage M I hI) ≅ M := by
  apply (finiteLengthModuleProperty R).isoMk
  exact LinearEquiv.toModuleIso
    (X₁ := ((cofiniteQuotientRestriction I).obj
      (finiteLengthModuleQuotientStage M I hI)).obj) (X₂ := M.obj)
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
theorem finiteLengthModuleQuotientStageIso_hom_apply (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) (x : M.obj) :
    (finiteLengthModuleQuotientStageIso M I hI).hom.hom x = x := rfl

@[simp]
theorem finiteLengthModuleQuotientStageIso_inv_apply (M : FiniteLengthModuleCat R)
    (I : CofiniteIdealIndex R) (hI : I.val ≤ Module.annihilator R M.obj) (x : M.obj) :
    (finiteLengthModuleQuotientStageIso M I hI).inv.hom x = x := rfl

/-- The identity-on-elements stage comparisons commute with original maps. -/
theorem finiteLengthModuleQuotientStageIso_naturality {M N : FiniteLengthModuleCat R}
    (I : CofiniteIdealIndex R) (hM : I.val ≤ Module.annihilator R M.obj)
    (hN : I.val ≤ Module.annihilator R N.obj) (f : M ⟶ N) :
    (cofiniteQuotientRestriction I).map (finiteLengthModuleQuotientStageMap I hM hN f) ≫
        (finiteLengthModuleQuotientStageIso N I hN).hom =
      (finiteLengthModuleQuotientStageIso M I hM).hom ≫ f := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  rfl

/-- Every finite-length module is covered by its actual annihilator quotient. -/
theorem cofiniteQuotientRestriction_covers (M : FiniteLengthModuleCat R) :
    ∃ N : FGModuleCat.{u} (R ⧸ Module.annihilator R M.obj),
      Nonempty ((cofiniteQuotientRestriction (cofiniteAnnihilator M.obj M.property)).obj N ≅ M) :=
  ⟨finiteLengthModuleQuotientStage M (cofiniteAnnihilator M.obj M.property) le_rfl,
    ⟨finiteLengthModuleQuotientStageIso M (cofiniteAnnihilator M.obj M.property) le_rfl⟩⟩

end SGA.SGA2.ExposeIV
