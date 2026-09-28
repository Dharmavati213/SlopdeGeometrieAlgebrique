/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportObject
import SGA.SGA2.ExposeII.AffineComparisonZero

/-!
# Quasi-coherence of the actual closed-supported module sheaf on an affine scheme

For a finitely generated ideal, a supported section on a principal open has
a numerator that becomes ideal-power torsion after multiplication by one
power of the denominator. This proves that the original supported-module
restriction maps are localization maps. The genuine support module sheaf
is consequently the tilde of the original ideal-power torsion module.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Denominators

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M : Type u} [AddCommGroup M] [Module R M]

include hI in
/-- A common denominator moves a numerator into the original ideal-power torsion module. -/
theorem exists_pow_smul_mem_powerTorsion (f : R) (x : M)
    (hx : ∀ g ∈ I, ∃ n : ℕ, (f * g) ^ n • x = 0) :
    ∃ k : ℕ, f ^ k • x ∈ ExposeII.powerTorsion I M := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hspan : Ideal.span (Set.range (fun g : s ↦ (g : R))) = I := by
    rw [show Set.range (fun g : s ↦ (g : R)) = (s : Set R) by ext; simp]
    exact hs
  have hg (g : s) : (g : R) ∈ I := hs ▸ Ideal.subset_span g.property
  choose n hn using fun g : s ↦ hx g (hg g)
  let k : ℕ := ⨆ g : s, n g
  refine ⟨k, ?_⟩
  rw [← hspan, ExposeII.mem_powerTorsion_span_iff_forall]
  intro g
  refine ⟨n g, ?_⟩
  have hle : n g ≤ k := le_ciSup (Finite.bddAbove_range n) g
  have hk : k = (k - n g) + n g := by omega
  rw [hk, pow_add, mul_smul, smul_comm ((g : R) ^ n g) (f ^ (k - n g)),
    smul_comm ((g : R) ^ n g) (f ^ n g)]
  simpa only [mul_pow, mul_smul, smul_zero] using
    congrArg (fun y : M ↦ f ^ (k - n g) • y) (hn g)

end Denominators

variable {R : CommRingCat.{u}} (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R)

local instance (U : (Spec R).Opens) :
    Module R (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)).obj.obj (op U)) :=
  inferInstanceAs (Module R Γ(tilde M, U))

/-- The actual supported module sheaf on the affine spectrum. -/
abbrev affineSupportedModuleSheaf : (Spec R).Modules :=
  moduleGammaZSheaf (Spec R).ringCatSheaf (ExposeII.affineSupportClosed I) (tilde M)

/-- A generator principal open lies in the actual support complement. -/
theorem basicOpen_le_affineSupportComplement {g : R} (hg : g ∈ I) :
    PrimeSpectrum.basicOpen g ≤ (ExposeII.affineSupportClosed I).compl := by
  intro p hp hpZ
  exact hp (hpZ hg)

/-- A numerator of a supported principal-open section vanishes on each product basic open. -/
theorem affineSupportedSection_numerator_vanishes (f : R)
    (s : Γ(affineSupportedModuleSheaf I M, PrimeSpectrum.basicOpen f))
    (x : M) (n : ℕ) (hx : f ^ n • s.val = tilde.toOpen M (PrimeSpectrum.basicOpen f) x)
    {g : R} (hg : g ∈ I) :
    tilde.toOpen M (PrimeSpectrum.basicOpen (f * g)) x = 0 := by
  let i : PrimeSpectrum.basicOpen (f * g) ⟶ PrimeSpectrum.basicOpen f :=
    homOfLE (PrimeSpectrum.basicOpen_mul_le_left f g)
  have hz : (tilde M).val.map i.op s.val = 0 :=
    moduleSupportedLocalSection_restrict_eq_zero (Spec R).ringCatSheaf
      (PrimeSpectrum.basicOpen f) (ExposeII.affineSupportClosed I) (tilde M) s
        (le_inf (PrimeSpectrum.basicOpen_mul_le_left f g)
          ((PrimeSpectrum.basicOpen_mul_le_right f g).trans
            (basicOpen_le_affineSupportComplement I hg)))
  have ht := ConcreteCategory.congr_hom
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen (f * g)) i) x
  change (tilde M).val.map i.op (tilde.toOpen M (PrimeSpectrum.basicOpen f) x) = _ at ht
  rw [← ht, ← hx]
  have hz' : ((modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op).hom s.val = 0 := hz
  exact (((modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op).hom.map_smul (f ^ n) s.val).trans
    ((congrArg (fun y : Γ(tilde M, PrimeSpectrum.basicOpen (f * g)) ↦ f ^ n • y) hz').trans
      (smul_zero _))

/-- The original global supported module sections are the original ideal-power torsion. -/
def affineSupportedModuleGlobalEquiv :
    ExposeII.powerTorsion I M ≃ₗ[R] Γ(affineSupportedModuleSheaf I M, ⊤) where
  toFun x := ⟨(tilde.isoTop M).hom x.val,
    (ExposeII.tilde_isoTop_mem_gammaZ_iff M I hI x.val).mpr x.property⟩
  invFun s := ⟨(tilde.isoTop M).inv s.val,
    (ExposeII.tilde_isoTop_mem_gammaZ_iff M I hI _).mp
      (by
        have hs : s.val ∈ ExposeI.gammaZ (ExposeII.affineTildeAbSheaf M)
            (ExposeII.affineSupportClosed I) := s.property
        simpa only [Iso.inv_hom_id_apply] using hs)⟩
  left_inv x := Subtype.ext ((tilde.isoTop M).hom_inv_id_apply x.val)
  right_inv s := Subtype.ext ((tilde.isoTop M).inv_hom_id_apply s.val)
  map_add' x y := Subtype.ext ((tilde.isoTop M).hom.hom.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((tilde.isoTop M).hom.hom.map_smul r x.val)

include hI in
/-- The actual restriction of supported-module sections to a principal open is localization. -/
theorem affineSupportedModuleSheaf_isLocalizing :
    IsLocalizing (modulesSpecToSheaf.obj (affineSupportedModuleSheaf I M)) := by
  intro f
  let H := affineSupportedModuleSheaf I M
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen f
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · exact H.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro s
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (tilde.toOpen M V).hom f s.val
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_powerTorsion I hI f x (fun g hg ↦
      (ExposeII.tilde_toOpen_basicOpen_eq_zero_iff M (f * g) x).mp
        (affineSupportedSection_numerator_vanishes I M f s x n hx hg))
    refine ⟨k + n, affineSupportedModuleGlobalEquiv I hI M ⟨f ^ k • x, hk⟩, ?_⟩
    apply Subtype.ext
    change f ^ (k + n) • s.val =
      (tilde M).val.map V.leTop.op ((tilde.isoTop M).hom (f ^ k • x))
    have ht := ConcreteCategory.congr_hom (tilde.toOpen_res M ⊤ V V.leTop) (f ^ k • x)
    change (tilde M).val.map V.leTop.op ((tilde.isoTop M).hom (f ^ k • x)) = _ at ht
    rw [ht, (tilde.toOpen M V).hom.map_smul, ← hx, pow_add, mul_smul]
  · intro s hs
    have h : (tilde M).val.map V.leTop.op s.val = 0 := congrArg Subtype.val hs
    have : IsLocalizedModule.Away f
        (((modulesSpecToSheaf.obj (tilde M)).presheaf.map V.leTop.op).hom) :=
      isLocalizing_tilde M f
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq f
      (show ((modulesSpecToSheaf.obj (tilde M)).presheaf.map V.leTop.op).hom s.val =
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map V.leTop.op).hom 0 by
          exact h.trans (map_zero _).symm)
    refine ⟨n, Subtype.ext ?_⟩
    change f ^ n • (s.val : Γ(tilde M, ⊤)) = 0
    exact hn.trans (smul_zero _)

include hI in
/-- The original closed-supported module sheaf is quasi-coherent on an affine spectrum
when its support ideal is finitely generated. -/
theorem affineSupportedModuleSheaf_isQuasicoherent :
    (affineSupportedModuleSheaf I M).IsQuasicoherent := by
  have : IsIso (affineSupportedModuleSheaf I M).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr (affineSupportedModuleSheaf_isLocalizing I hI M)
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance

/-- The actual closed-supported module sheaf is the tilde of the ideal-power torsion module. -/
def affineSupportedModuleSheafIsoTorsion :
    tilde (ModuleCat.of R (ExposeII.powerTorsion I M)) ≅ affineSupportedModuleSheaf I M := by
  have : IsIso (affineSupportedModuleSheaf I M).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr (affineSupportedModuleSheaf_isLocalizing I hI M)
  exact (tilde.functor R).mapIso (affineSupportedModuleGlobalEquiv I hI M).toModuleIso ≪≫
    asIso (affineSupportedModuleSheaf I M).fromTildeΓ

end SGA.SGA2.ExposeVI
