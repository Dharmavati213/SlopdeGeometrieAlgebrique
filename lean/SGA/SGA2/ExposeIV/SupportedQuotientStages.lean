/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFiniteModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Quotient-ring stages of finite supported modules

The stages in SGA 2, IV.1.3 are the actual categories of finite `R/Jⁿ`-modules,
embedded by restriction of scalars. Every finite supported module belongs to
some stage, up to an isomorphism which is the identity on its underlying group.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Restriction along a quotient map is full as well as faithful. -/
def fullyFaithfulQuotientRestriction (I : Ideal R) :
    (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I)).FullyFaithful where
  preimage {M N} f := ModuleCat.ofHom
    { f.hom.toAddMonoidHom with
      map_smul' s x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact f.hom.map_smul r x }
  map_preimage f := by ext x; rfl
  preimage_map f := by ext x; rfl

instance (I : Ideal R) : (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I)).Full :=
  (fullyFaithfulQuotientRestriction I).full

private theorem finite_quotient_restriction (I : Ideal R) (M : FGModuleCat.{u} (R ⧸ I)) :
    Module.Finite R ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj) := by
  have : IsScalarTower R (R ⧸ I)
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj) :=
    IsScalarTower.of_compHom R (R ⧸ I) M
  have : Module.Finite (R ⧸ I)
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj) :=
    inferInstanceAs (Module.Finite (R ⧸ I) M)
  exact Module.Finite.trans (R ⧸ I) _

/-- The genuine restriction-of-scalars embedding of finite quotient modules. -/
def quotientFiniteRestriction (I : Ideal R) : FGModuleCat.{u} (R ⧸ I) ⥤ FGModuleCat.{u} R :=
  (ModuleCat.isFG.{u} R).lift
    (forget₂ (FGModuleCat.{u} (R ⧸ I)) (ModuleCat.{u} (R ⧸ I)) ⋙
      ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I))
    (finite_quotient_restriction I)

instance (I : Ideal R) : (quotientFiniteRestriction I).Full := by
  exact Functor.Full.of_comp_faithful_iso
    ((ModuleCat.isFG R).liftCompιIso _ (finite_quotient_restriction I))

instance (I : Ideal R) : (quotientFiniteRestriction I).Faithful := by
  exact Functor.Faithful.of_comp_iso
    ((ModuleCat.isFG R).liftCompιIso _ (finite_quotient_restriction I))

instance (I : Ideal R) : (quotientFiniteRestriction I).Additive := by
  constructor
  intro M N f g
  apply ObjectProperty.hom_ext
  exact (forget₂ (FGModuleCat (R ⧸ I)) (ModuleCat (R ⧸ I)) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map_add

/-- The quotient ideal actually annihilates every restricted module. -/
theorem quotientFiniteRestriction_annihilator (I : Ideal R) (M : FGModuleCat.{u} (R ⧸ I)) :
    I ≤ Module.annihilator R ((quotientFiniteRestriction I).obj M) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  change Ideal.Quotient.mk I r • (show M from x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

section Noetherian

variable [IsNoetherianRing R]

instance (I : Ideal R) : PreservesFiniteLimits (quotientFiniteRestriction I) := by
  have : PreservesFiniteLimits
      (quotientFiniteRestriction I ⋙ forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) :=
    comp_preservesFiniteLimits
      (forget₂ (FGModuleCat.{u} (R ⧸ I)) (ModuleCat.{u} (R ⧸ I)))
      (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))

instance (I : Ideal R) : PreservesFiniteColimits (quotientFiniteRestriction I) := by
  have : PreservesFiniteColimits
      (quotientFiniteRestriction I ⋙ forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) :=
    comp_preservesFiniteColimits
      (forget₂ (FGModuleCat.{u} (R ⧸ I)) (ModuleCat.{u} (R ⧸ I)))
      (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk I))
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))

/-- The `n`-th quotient-ring stage inside actual finite supported modules. -/
def supportedQuotientStage (J : Ideal R) (n : ℕ) :
    FGModuleCat.{u} (R ⧸ J ^ n) ⥤ SupportedFGModuleCat J :=
  (supportedFiniteModuleProperty J).lift (quotientFiniteRestriction (J ^ n)) fun M ↦ by
    change Module.support R ((quotientFiniteRestriction (J ^ n)).obj M) ⊆ _
    exact (support_subset_zeroLocus_iff_exists_pow_le_annihilator J _).mpr
      ⟨n, quotientFiniteRestriction_annihilator (J ^ n) M⟩

instance (J : Ideal R) (n : ℕ) : (supportedQuotientStage J n).Full := by
  unfold supportedQuotientStage
  infer_instance

instance (J : Ideal R) (n : ℕ) : (supportedQuotientStage J n).Faithful := by
  unfold supportedQuotientStage
  infer_instance

instance (J : Ideal R) (n : ℕ) : (supportedQuotientStage J n).Additive := by
  unfold supportedQuotientStage
  infer_instance

instance (J : Ideal R) (n : ℕ) : PreservesFiniteLimits (supportedQuotientStage J n) := by
  have : PreservesFiniteLimits (supportedQuotientStage J n ⋙ supportedFiniteInclusion J) :=
    inferInstanceAs (PreservesFiniteLimits (quotientFiniteRestriction (J ^ n)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (supportedFiniteInclusion J)

instance (J : Ideal R) (n : ℕ) : PreservesFiniteColimits (supportedQuotientStage J n) := by
  have : PreservesFiniteColimits (supportedQuotientStage J n ⋙ supportedFiniteInclusion J) :=
    inferInstanceAs (PreservesFiniteColimits (quotientFiniteRestriction (J ^ n)))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (supportedFiniteInclusion J)

/-- The stage embedding preserves actual short exact sequences. -/
theorem supportedQuotientStage_shortExact (J : Ideal R) (n : ℕ)
    {S : ShortComplex (FGModuleCat.{u} (R ⧸ J ^ n))} (hS : S.ShortExact) :
    (S.map (supportedQuotientStage J n)).ShortExact :=
  hS.map_of_exact (supportedQuotientStage J n)

set_option backward.isDefEq.respectTransparency false in
/-- All finite supported objects are covered by genuine quotient-ring stages. -/
theorem supportedQuotientStage_covers (J : Ideal R) (M : SupportedFGModuleCat J) :
    ∃ n : ℕ, ∃ N : FGModuleCat.{u} (R ⧸ J ^ n),
      Nonempty ((supportedQuotientStage J n).obj N ≅ M) := by
  obtain ⟨n, hn⟩ := supportedFinite_exists_pow_annihilator J M
  have hM : Module.IsTorsionBySet R M.obj ((J ^ n : Ideal R) : Set R) :=
    (Module.isTorsionBySet_iff_subset_annihilator R M.obj).mpr hn
  let := hM.module
  let := Module.Finite.of_surjective hM.semilinearMap Function.surjective_id
  refine ⟨n, FGModuleCat.of (R ⧸ J ^ n) M.obj, ⟨?_⟩⟩
  apply (supportedFiniteModuleProperty J).isoMk
  apply (ModuleCat.isFG R).isoMk
  exact LinearEquiv.toModuleIso (X₁ :=
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ n))).obj
        (ModuleCat.of (R ⧸ J ^ n) M.obj))) (X₂ := M.obj.obj)
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

end Noetherian

end SGA.SGA2.ExposeIV
