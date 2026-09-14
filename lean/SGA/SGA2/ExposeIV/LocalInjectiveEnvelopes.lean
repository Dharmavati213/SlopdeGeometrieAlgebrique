/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.EssentialModuleExtensions
import SGA.SGA2.ExposeIV.LocalSocleDuality
import SGA.SGA2.ExposeIV.HomDualLengthExactness
import SGA.SGA2.ExposeIV.SupportedFunctorAnnihilatorStages
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian

/-!
# SGA 2, IV.4.7: supported dualizing modules and injective envelopes

The support condition is explicit. For an arbitrary module `H`, raw Hom
duality on finite modules supported at the maximal ideal does not imply
that `H` itself has this support: an invisible nonsupported summand may be
added. The source's envelope argument uses the supported representing-module
convention, and the definition below retains precisely that convention.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R]

local instance : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _

/-- Dualizing modules with the supported representing-module convention:
actual support at the maximal ideal and genuine finite canonical Hom duality. -/
def SupportedDualizingModule (H : ModuleCat.{u} R) : Prop :=
  supportedModuleProperty (IsLocalRing.maximalIdeal R) H ∧
    FiniteSupportedHomValues (IsLocalRing.maximalIdeal R) H ∧
    SupportedModuleBiduality (IsLocalRing.maximalIdeal R) H

/-- The image of a residue-field map is contained in the actual local socle. -/
theorem residueMap_range_le_localSocle (H : ModuleCat.{u} R)
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H) :
    LinearMap.range i.hom ≤ localSocle (R := R) H := by
  rintro x ⟨y, rfl⟩
  rw [mem_localSocle]
  intro r hr
  rw [← map_smul]
  have hAnn : r ∈ Module.annihilator R (R ⧸ IsLocalRing.maximalIdeal R) := by
    rwa [Ideal.annihilator_quotient]
  rw [Module.mem_annihilator.mp hAnn y, map_zero]

/-- In an essential residue-field extension, the residue image is precisely
the socle, not merely an abstract isomorphic submodule. -/
theorem localSocle_eq_range_of_essential_residue (H : ModuleCat.{u} R)
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H)
    (hi : EssentialModuleMap i) : localSocle (R := R) H = LinearMap.range i.hom := by
  apply le_antisymm _ (residueMap_range_le_localSocle H i)
  rw [localSocle_eq_sSup_simple]
  apply sSup_le
  intro P hP
  have : IsSimpleModule R P := hP
  by_contra hn
  have hd : Disjoint P (LinearMap.range i.hom) :=
    (IsSimpleModule.isAtom (R := R) (m := P)).not_le_iff_disjoint.mp hn
  have hzero := (essentialIn_iff_disjoint _ _).mp hi.2 |>.2 P le_top hd.symm
  exact (IsSimpleModule.isAtom (R := R) (m := P)).ne_bot hzero

/-- The actual residue Hom module in an essential extension is the residue field. -/
def residueHomIsoOfEssential (H : ModuleCat.{u} R)
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H)
    (hi : EssentialModuleMap i) :
    (moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))) ≅
      ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) :=
  quotientHomAnnihilatorIso _ H ≪≫
    (LinearEquiv.ofEq _ _ (localSocle_eq_range_of_essential_residue H i hi)).toModuleIso ≪≫
    (LinearEquiv.ofInjective i.hom hi.1).symm.toModuleIso

variable [IsNoetherianRing R]

/-- In an arbitrary supported module the actual socle is essential.
Only the individual cyclic submodules are finite length. -/
theorem localSocle_essential_of_support (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty (IsLocalRing.maximalIdeal R) H) :
    EssentialIn (localSocle (R := R) H) ⊤ := by
  refine ⟨le_top, ?_⟩
  intro x _ hx0
  let C : Submodule R H := Submodule.span R {x}
  have hC := supportedSubmodule_isFiniteLength (IsLocalRing.maximalIdeal R) H hH C
  have : IsArtinian R C := (isFiniteLength_iff_isNoetherian_isArtinian.mp hC).2
  have : Nontrivial C := ⟨⟨⟨x, Submodule.mem_span_singleton_self x⟩, 0,
    fun heq => hx0 (congrArg Subtype.val heq)⟩⟩
  obtain ⟨P, hP⟩ := IsAtomic.exists_atom (Submodule R C)
  have : IsSimpleModule R P := isSimpleModule_iff_isAtom.mpr hP
  have : Nontrivial P := IsSimpleModule.nontrivial R P
  obtain ⟨y, hy0⟩ := exists_ne (0 : P)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp y.val.property
  refine ⟨r, ?_, ?_⟩
  · rw [hr, mem_localSocle]
    intro s hs
    have hySocle := simpleSubmodule_le_localSocle C P y.property
    exact congrArg Subtype.val ((mem_localSocle C y.val).mp hySocle s hs)
  · intro heq
    apply hy0
    apply Subtype.ext
    apply Subtype.ext
    exact hr.symm.trans heq

/-- Essential injective residue-field extensions automatically have the
required support. This uses the proved injectivity of ideal-power torsion. -/
theorem supported_of_injective_essential_residue (H : ModuleCat.{u} R) [Injective H]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H)
    (hi : EssentialModuleMap i) :
    supportedModuleProperty (IsLocalRing.maximalIdeal R) H := by
  let m := IsLocalRing.maximalIdeal R
  have hle : LinearMap.range i.hom ≤ powerTorsion m H := by
    intro x hx
    have hxS := residueMap_range_le_localSocle H i hx
    apply (mem_powerTorsion_iff m H x).mpr
    refine ⟨1, ?_⟩
    simpa only [pow_one] using (mem_localSocle H x).mp hxS
  have := powerTorsion_injective_of_injective m H
  have htop : powerTorsion m H = ⊤ :=
    (hi.2.mono_left hle le_top).eq_top_of_injective _
  exact (powerTorsion_eq_top_iff_support_subset_zeroLocus m H).mp htop

/-- Supported canonical Hom duality is equivalent to the original injective
residue-field test. -/
theorem supportedDualizingModule_iff_support_injective_residue (H : ModuleCat.{u} R) :
    SupportedDualizingModule H ↔
      supportedModuleProperty (IsLocalRing.maximalIdeal R) H ∧ Injective H ∧
        moduleHomDualResidueTests (IsLocalRing.maximalIdeal R) H := by
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨hs, (supportedHomBiduality_iff_injective_and_residueTests _ H hs).mp hd⟩
  · rintro ⟨hs, hd⟩
    exact ⟨hs, (supportedHomBiduality_iff_injective_and_residueTests _ H hs).mpr hd⟩

/-- The definition is exactly duality of the original abelian-group-valued
Hom functor, together with the supported representing-module convention. -/
theorem supportedDualizingModule_iff_support_functorDuality (H : ModuleCat.{u} R) :
    SupportedDualizingModule H ↔
      supportedModuleProperty (IsLocalRing.maximalIdeal R) H ∧
        SupportedFunctorDuality (IsLocalRing.maximalIdeal R)
          (supportedModuleHomFunctor (IsLocalRing.maximalIdeal R) H ⋙
            forget₂ (ModuleCat R) AddCommGrpCat) := by
  let m := IsLocalRing.maximalIdeal R
  let T := supportedModuleHomFunctor m H ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  rw [supportedDualizingModule_iff_support_injective_residue]
  constructor
  · rintro ⟨hs, hI, hres⟩
    refine ⟨hs, ?_⟩
    have hexres := (supportedFunctor_exact_residue_iff_injectiveRepresentation m T).mpr
      ⟨H, hI, hres, ⟨Iso.refl _⟩⟩
    exact supportedFunctor_duality_of_exact_residue m T hexres.1 hexres.2
  · rintro ⟨hs, hT⟩
    have hexres := supportedFunctor_exact_residue_of_duality m T hT
    refine ⟨hs, ?_, ?_⟩
    · exact (finiteSupportedHomExact_iff_injective_of_support m H hs).mp
        ((supportedHomFunctorExact_iff m H).mp hexres.1)
    · exact (supportedFunctorResidueTests_iff_of_representation m T H (Iso.refl _)).mp
        hexres.2

/-- **IV.4.7, supported convention:** a module is dualizing if and only if
it is an injective essential extension of the actual residue field.
The implication from an envelope derives support, rather than assuming it. -/
theorem supportedDualizingModule_iff_injective_essential_residue (H : ModuleCat.{u} R) :
    SupportedDualizingModule H ↔ Injective H ∧
      ∃ i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H, EssentialModuleMap i := by
  rw [supportedDualizingModule_iff_support_injective_residue]
  constructor
  · rintro ⟨hs, hI, hres⟩
    obtain ⟨e⟩ := hres (IsLocalRing.maximalIdeal R) inferInstance le_rfl
    let a : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ≅
        ModuleCat.of R (localSocle (R := R) H) :=
      e.symm ≪≫ quotientHomAnnihilatorIso _ H
    let i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H :=
      a.hom ≫ ModuleCat.ofHom (localSocle (R := R) H).subtype
    have hrange : LinearMap.range i.hom = localSocle (R := R) H := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact (a.hom y).property
      · intro x hx
        refine ⟨a.inv ⟨x, hx⟩, ?_⟩
        exact congrArg Subtype.val (a.toLinearEquiv.apply_symm_apply ⟨x, hx⟩)
    refine ⟨hI, i, ?_, ?_⟩
    · intro x y hxy
      apply a.toLinearEquiv.injective
      exact Subtype.ext hxy
    · rw [hrange]
      exact localSocle_essential_of_support H hs
  · rintro ⟨hI, i, hi⟩
    have := hI
    refine ⟨supported_of_injective_essential_residue H i hi, hI, ?_⟩
    intro m hm _
    have heq : m = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
    subst m
    exact ⟨residueHomIsoOfEssential H i hi⟩

/-- The genuine injective envelope of the residue field is dualizing. -/
theorem ModuleInjectiveEnvelope.supportedDualizing
    (E : ModuleInjectiveEnvelope (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))) :
    SupportedDualizingModule E.obj :=
  (supportedDualizingModule_iff_injective_essential_residue E.obj).mpr
    ⟨E.injective, E.ι, E.essential⟩

/-- **IV.4.7, existence:** every noetherian local ring has a supported
dualizing module, obtained from the actually constructed injective envelope. -/
theorem exists_supportedDualizingModule :
    ∃ H : ModuleCat.{u} R, SupportedDualizingModule H :=
  ⟨(moduleInjectiveEnvelope (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))).obj,
    ModuleInjectiveEnvelope.supportedDualizing _⟩

/-- **IV.4.7, uniqueness:** supported dualizing modules are noncanonically
isomorphic. No uniqueness assertion is made for arbitrary raw Hom targets. -/
theorem SupportedDualizingModule.nonempty_iso {H K : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) (hK : SupportedDualizingModule K) : Nonempty (H ≅ K) := by
  obtain ⟨hI, i, hi⟩ := (supportedDualizingModule_iff_injective_essential_residue H).mp hH
  obtain ⟨hJ, j, hj⟩ := (supportedDualizingModule_iff_injective_essential_residue K).mp hK
  obtain ⟨e, _⟩ := ModuleInjectiveEnvelope.exists_iso
    (⟨H, i, hI, hi⟩ : ModuleInjectiveEnvelope (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)))
    ⟨K, j, hJ, hj⟩
  exact ⟨e⟩

/-- The actual socle of a supported dualizing module is the residue field. -/
theorem SupportedDualizingModule.socle_iso {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) :
    Nonempty (ModuleCat.of R (localSocle (R := R) H) ≅
      ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) := by
  obtain ⟨_, _, hres⟩ := (supportedDualizingModule_iff_support_injective_residue H).mp hH
  obtain ⟨e⟩ := hres (IsLocalRing.maximalIdeal R) inferInstance le_rfl
  exact ⟨(quotientHomAnnihilatorIso _ H).symm ≪≫ e⟩

/-- **IV.4.9:** every finitely generated submodule of a supported dualizing
module is Artinian, with no finiteness assumption on the whole module. -/
theorem SupportedDualizingModule.locallyArtinian {H : ModuleCat.{u} R}
    (hH : SupportedDualizingModule H) : ModuleLocallyArtinian (R := R) H :=
  moduleLocallyArtinian_of_support (IsLocalRing.maximalIdeal R) H hH.1

end SGA.SGA2.ExposeIV
