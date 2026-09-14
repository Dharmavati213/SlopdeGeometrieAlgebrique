/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# SGA 2, Exposé II, (4.2) and (5.1): a principal localization cokernel

The direct system `M/fⁿM`, with transition multiplication by the missing
power of `f`, maps to the cokernel of `M → M_f` by `x ↦ x/fⁿ`.
This is the algebraic degree-one comparison for a principal open.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (f : R)

/-- The submodule `fⁿM`. -/
def principalPowerRange (n : ℕ) : Submodule R M :=
  LinearMap.range (f ^ n • (LinearMap.id : M →ₗ[R] M))

/-- The direct transition `M/fⁿM → M/fᵐM` multiplies by `f^(m-n)`. -/
def principalLocalizationQuotientMap {n m : ℕ} (h : n ≤ m) :
    M ⧸ principalPowerRange M f n →ₗ[R] M ⧸ principalPowerRange M f m :=
  (principalPowerRange M f n).mapQ (principalPowerRange M f m)
    (f ^ (m - n) • (LinearMap.id : M →ₗ[R] M)) (by
      rintro x ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel h])

/-- The principal quotient diagram whose colimit computes localization modulo `M`. -/
def principalLocalizationQuotientDiagram : ℕ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (M ⧸ principalPowerRange M f n)
  map h := ModuleCat.ofHom (principalLocalizationQuotientMap M f (leOfHom h))
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    simp [principalLocalizationQuotientMap]
  map_comp {n m k} h j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    have he : k - m + (m - n) = k - n := by
      have := leOfHom h
      have := leOfHom j
      omega
    change Submodule.Quotient.mk (f ^ (k - n) • y) =
      Submodule.Quotient.mk (f ^ (k - m) • (f ^ (m - n) • y))
    rw [smul_smul, ← pow_add, he]

/-- The fraction `x/fⁿ`, as an `R`-linear map. -/
def principalFractionMap (n : ℕ) : M →ₗ[R] LocalizedModule (Submonoid.powers f) M :=
  (LocalizedModule.divBy (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)).comp
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)

@[simp]
theorem principalFractionMap_apply (n : ℕ) (x : M) :
    principalFractionMap M f n x =
      LocalizedModule.mk x (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := by
  simp [principalFractionMap, LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]

/-- Clearing a fraction whose numerator contains its denominator. -/
@[simp]
theorem principalFractionMap_smul (n : ℕ) (x : M) :
    principalFractionMap M f n (f ^ n • x) =
      LocalizedModule.mkLinearMap (Submonoid.powers f) M x :=
  (principalFractionMap_apply M f n _).trans
    (LocalizedModule.mk_cancel (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) x)

/-- The concrete quotient model of the cokernel of the principal localization map. -/
abbrev principalLocalizationCokernel : ModuleCat.{u} R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) M ⧸
    LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))

/-- Each quotient `M/fⁿM` maps to `M_f/M` by the fraction of denominator `fⁿ`. -/
def principalFractionQuotientMap (n : ℕ) :
    M ⧸ principalPowerRange M f n →ₗ[R] principalLocalizationCokernel M f :=
  (principalPowerRange M f n).liftQ
    ((LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mkQ.comp
      (principalFractionMap M f n)) (by
    rintro x ⟨y, rfl⟩
    change Submodule.Quotient.mk (principalFractionMap M f n (f ^ n • y)) = 0
    rw [principalFractionMap_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ y))

/-- Fractions commute with the direct transitions. -/
theorem principalFractionMap_transition {n m : ℕ} (h : n ≤ m) (x : M) :
    principalFractionMap M f m (f ^ (m - n) • x) = principalFractionMap M f n x := by
  simp only [principalFractionMap_apply, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add, Nat.add_sub_of_le h]

/-- The fraction maps define a cocone into the actual localization cokernel. -/
def principalLocalizationCokernelCocone : Cocone (principalLocalizationQuotientDiagram M f) where
  pt := principalLocalizationCokernel M f
  ι :=
    { app := fun n ↦ ModuleCat.ofHom (principalFractionQuotientMap M f n)
      naturality := by
        intro n m h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        refine Submodule.Quotient.induction_on _ x ?_
        intro y
        change Submodule.Quotient.mk (principalFractionMap M f m (f ^ (m - n) • y)) =
          Submodule.Quotient.mk (principalFractionMap M f n y)
        rw [principalFractionMap_transition M f (leOfHom h)] }

/-- The canonical map from the quotient colimit to the principal localization cokernel. -/
def principalLocalizationCokernelComparison :
    colimit (principalLocalizationQuotientDiagram M f) ⟶ principalLocalizationCokernel M f :=
  colimit.desc _ (principalLocalizationCokernelCocone M f)

@[reassoc (attr := simp)]
theorem principalLocalizationCokernelComparison_ι (n : ℕ) :
    colimit.ι (principalLocalizationQuotientDiagram M f) n ≫
      principalLocalizationCokernelComparison M f =
        ModuleCat.ofHom (principalFractionQuotientMap M f n) :=
  colimit.ι_desc _ n

@[simp]
theorem principalLocalizationCokernelComparison_apply (n : ℕ) (x : M) :
    principalLocalizationCokernelComparison M f
      (colimit.ι (principalLocalizationQuotientDiagram M f) n
        ((principalPowerRange M f n).mkQ x)) =
      (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mkQ
        (principalFractionMap M f n x) :=
  ConcreteCategory.congr_hom (principalLocalizationCokernelComparison_ι M f n) _

/-- Every class in `M_f/M` is represented by a fraction from one quotient stage. -/
theorem principalLocalizationCokernelComparison_surjective :
    Function.Surjective (principalLocalizationCokernelComparison M f) := by
  intro z
  obtain ⟨z, rfl⟩ := (LinearMap.range
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mkQ_surjective z
  refine LocalizedModule.induction_on (fun x s ↦ ?_) z
  obtain ⟨n, hn⟩ := s.property
  have hs : s = (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hn.symm
  subst s
  refine ⟨colimit.ι (principalLocalizationQuotientDiagram M f) n
    ((principalPowerRange M f n).mkQ x), ?_⟩
  exact (principalLocalizationCokernelComparison_apply M f n x).trans
    (congrArg (LinearMap.range
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mkQ
        (principalFractionMap_apply M f n x))

/-- A fraction which comes from `M` is already zero in a later quotient stage. -/
theorem principalLocalizationCokernelComparison_injective :
    Function.Injective (principalLocalizationCokernelComparison M f) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  obtain ⟨n, q, rfl⟩ := Concrete.isColimit_exists_rep
    (principalLocalizationQuotientDiagram M f) (colimit.isColimit _) z
  obtain ⟨x, rfl⟩ := (principalPowerRange M f n).mkQ_surjective q
  have hx : (LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mkQ
      (principalFractionMap M f n x) = 0 := by
    change principalLocalizationCokernelComparison M f
      (colimit.ι (principalLocalizationQuotientDiagram M f) n
        ((principalPowerRange M f n).mkQ x)) = 0 at hz
    exact (principalLocalizationCokernelComparison_apply M f n x).symm.trans hz
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
  have he : LocalizedModule.mk x (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) =
      LocalizedModule.mk y (1 : Submonoid.powers f) := by
    simpa only [principalFractionMap_apply, LocalizedModule.mkLinearMap_apply] using hy.symm
  obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp he
  obtain ⟨k, hk⟩ := s.property
  have hxy : f ^ k • x = f ^ (n + k) • y := by
    simpa only [one_smul, Submonoid.smul_def, ← hk, smul_smul, ← pow_add,
      Nat.add_comm k n] using hs
  have hzero : (principalLocalizationQuotientDiagram M f).map (homOfLE (Nat.le_add_right n k))
      ((principalPowerRange M f n).mkQ x) = 0 := by
    change (principalPowerRange M f (n + k)).mkQ (f ^ (n + k - n) • x) = 0
    rw [Nat.add_sub_cancel_left, hxy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  have hι := ConcreteCategory.congr_hom
    (colimit.w (principalLocalizationQuotientDiagram M f) (homOfLE (Nat.le_add_right n k)))
      ((principalPowerRange M f n).mkQ x)
  change colimit.ι (principalLocalizationQuotientDiagram M f) (n + k)
      ((principalLocalizationQuotientDiagram M f).map (homOfLE (Nat.le_add_right n k))
        ((principalPowerRange M f n).mkQ x)) = _ at hι
  rw [hzero, map_zero] at hι
  exact hι.symm

/-- The canonical principal fraction comparison is an isomorphism. -/
instance principalLocalizationCokernelComparison_isIso :
    IsIso (principalLocalizationCokernelComparison M f) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨principalLocalizationCokernelComparison_injective M f,
      principalLocalizationCokernelComparison_surjective M f⟩

/-- The quotient direct limit computes the actual categorical cokernel of localization. -/
def principalLocalizationCokernelColimitIso :
    colimit (principalLocalizationQuotientDiagram M f) ≅
      cokernel (ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :=
  asIso (principalLocalizationCokernelComparison M f) ≪≫
    (ModuleCat.cokernelIsoRangeQuotient
      (ModuleCat.ofHom (R := R) (LocalizedModule.mkLinearMap (Submonoid.powers f) M))).symm

end SGA.SGA2.ExposeII
