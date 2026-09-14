/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.InjectiveTorsion
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# SGA 2, Exposé IV, 2.1: injectivity tested on finite supported modules

For an ideal-power-torsion module over a commutative noetherian ring,
injectivity is equivalent to exactness of the actual contravariant Hom
functor on finite modules supported on the ideal's zero locus. The nontrivial
implication uses Artin–Rees to reduce Baer's criterion to a submodule of a
quotient by an ideal power. No injectivity or comparison is assumed.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- The surjectivity part of contravariant Hom exactness on finite modules
supported on `V(J)`: maps from every submodule extend to the finite ambient
module. Over a noetherian ring the submodule is also finite and supported. -/
def FiniteSupportedHomExtension (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ (M : ModuleCat.{u} R), Module.Finite R M →
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R) →
    ∀ (N : Submodule R M) (f : N →ₗ[R] H),
      ∃ g : M →ₗ[R] H, g.comp N.subtype = f

/-- Exactness of the genuine contravariant Hom functor on finite supported
short exact sequences. It suffices to specify finiteness and support of the
middle term: its submodule and quotient then have the same properties. -/
def FiniteSupportedHomExact (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ (S : ShortComplex (ModuleCat.{u} R)), Module.Finite R S.X₂ →
    Module.support R S.X₂ ⊆ PrimeSpectrum.zeroLocus (J : Set R) →
    S.ShortExact → (S.op.map (preadditiveYoneda.obj H)).ShortExact

/-- Finite support in `V(J)` is precisely uniform annihilation by one power
of `J`, over a noetherian ring. -/
theorem support_subset_zeroLocus_iff_exists_pow_le_annihilator [IsNoetherianRing R]
    (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R) ↔
      ∃ n : ℕ, J ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  constructor
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h J.fg_of_isNoetherianRing
  · rintro ⟨n, hn⟩ a ha
    exact ⟨n, hn (Ideal.pow_mem_pow ha n)⟩

/-- Finitely generated modules supported on `V(J)` are actual ideal-power
torsion modules. -/
theorem powerTorsion_eq_top_of_finite_support [IsNoetherianRing R]
    (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    powerTorsion J M = ⊤ := by
  obtain ⟨n, hn⟩ := (support_subset_zeroLocus_iff_exists_pow_le_annihilator J M).mp hM
  apply top_unique
  intro x _
  exact (mem_powerTorsion_iff J M x).mpr
    ⟨n, fun a ha ↦ Module.mem_annihilator.mp (hn ha) x⟩

/-- Injective modules satisfy the finite supported extension property. -/
theorem finiteSupportedHomExtension_of_injective (J : Ideal R)
    (H : ModuleCat.{u} R) [Injective H] : FiniteSupportedHomExtension J H := by
  intro M _ _ N f
  let i : ModuleCat.of R N ⟶ M := ModuleCat.ofHom N.subtype
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr N.injective_subtype
  refine ⟨(Injective.factorThru (ModuleCat.ofHom f) i).hom, ?_⟩
  exact ModuleCat.hom_ext_iff.mp (Injective.comp_factorThru (ModuleCat.ofHom f) i)

/-- Artin–Rees reduces Baer's criterion for a torsion target to extensions
inside finite quotients `R/J^n`, which are supported on `V(J)`. -/
theorem baer_of_finiteSupportedHomExtension [IsNoetherianRing R]
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : powerTorsion J H = ⊤)
    (hExt : FiniteSupportedHomExtension J H) : Module.Baer R H := by
  intro L f
  obtain ⟨n, hn⟩ := exists_pow_inf_le_map_ker_of_range_le_powerTorsion J L f
    (by rw [hH]; exact le_top)
  let p : L →ₗ[R] R ⧸ J ^ n := (J ^ n).mkQ.comp L.subtype
  have hp : p.ker ≤ f.ker := by
    intro x hx
    have hxJ : (x : R) ∈ J ^ n := (Submodule.Quotient.mk_eq_zero (J ^ n)).mp hx
    obtain ⟨y, hy, he⟩ := hn ⟨hxJ, x.property⟩
    exact (show y = x from Subtype.ext he) ▸ hy
  let f' : p.range →ₗ[R] H :=
    (p.ker.liftQ f hp).comp p.quotKerEquivRange.symm.toLinearMap
  have hsupp : Module.support R (R ⧸ J ^ n) ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
    (support_subset_zeroLocus_iff_exists_pow_le_annihilator J (R ⧸ J ^ n)).mpr
      ⟨n, by rw [Ideal.annihilator_quotient]⟩
  obtain ⟨g, hg⟩ := hExt (ModuleCat.of R (R ⧸ J ^ n)) inferInstance hsupp p.range f'
  refine ⟨g.comp (J ^ n).mkQ, ?_⟩
  intro x hx
  have heval := congrArg (fun k : p.range →ₗ[R] H ↦ k (p.rangeRestrict ⟨x, hx⟩)) hg
  change g ((J ^ n).mkQ x) = f' (p.rangeRestrict ⟨x, hx⟩) at heval
  change g ((J ^ n).mkQ x) = f ⟨x, hx⟩
  rw [heval]
  change p.ker.liftQ f hp (p.quotKerEquivRange.symm ⟨p ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩) = _
  exact congrArg (p.ker.liftQ f hp)
    (p.quotKerEquivRange_symm_apply_image ⟨x, hx⟩ ⟨⟨x, hx⟩, rfl⟩)

/-- **IV.2.1, extension formulation:** a torsion module is injective if Hom
extends along inclusions of finite modules supported on `V(J)`. -/
theorem injective_of_finiteSupportedHomExtension [IsNoetherianRing R]
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : powerTorsion J H = ⊤)
    (hExt : FiniteSupportedHomExtension J H) : Injective H := by
  let : Module.Injective R H := (baer_of_finiteSupportedHomExtension J H hH hExt).injective
  exact Module.injective_object_of_injective_module R H

/-- The full finite-supported extension criterion, with the original
injectivity conclusion in the category of all modules. -/
theorem injective_iff_finiteSupportedHomExtension [IsNoetherianRing R]
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : powerTorsion J H = ⊤) :
    Injective H ↔ FiniteSupportedHomExtension J H :=
  ⟨fun _ ↦ finiteSupportedHomExtension_of_injective J H,
    injective_of_finiteSupportedHomExtension J H hH⟩

/-- Injectivity gives short exact sequences under the actual Hom functor. -/
theorem finiteSupportedHomExact_of_injective (J : Ideal R)
    (H : ModuleCat.{u} R) [Injective H] : FiniteSupportedHomExact J H := by
  intro S _ _ hS
  exact (hS.op.map_of_exact (preadditiveYonedaObj H)).map_of_exact
    (forget₂ (ModuleCat (End H)) AddCommGrpCat)

/-- Exactness of Hom on finite supported short exact sequences supplies
actual extensions from submodules. -/
theorem finiteSupportedHomExtension_of_exact (J : Ideal R) (H : ModuleCat.{u} R)
    (hExact : FiniteSupportedHomExact J H) : FiniteSupportedHomExtension J H := by
  intro M hM hsupp N f
  let S : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext x; simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr (by
        exact N.range_subtype.trans N.ker_mkQ.symm)
      mono_f := (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective }
  have h := hExact S hM hsupp hS
  have hsurj := (AddCommGrpCat.epi_iff_surjective
    (S.op.map (preadditiveYoneda.obj H)).g).mp h.epi_g
  obtain ⟨g, hg⟩ := hsurj (ModuleCat.ofHom f)
  exact ⟨g.hom, ModuleCat.hom_ext_iff.mp hg⟩

/-- **IV.2.1:** for an ideal-power-torsion module over a commutative
noetherian ring, exactness of the genuine Hom functor on finite supported
modules is equivalent to injectivity in the category of all modules. -/
theorem finiteSupportedHomExact_iff_injective [IsNoetherianRing R]
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : powerTorsion J H = ⊤) :
    FiniteSupportedHomExact J H ↔ Injective H :=
  ⟨fun h ↦ injective_of_finiteSupportedHomExtension J H hH
      (finiteSupportedHomExtension_of_exact J H h),
    fun _ ↦ finiteSupportedHomExact_of_injective J H⟩

/-- **IV.2.2:** ideal-power torsion in an injective module is injective.
This is the previously proved Artin–Rees theorem, on the unchanged torsion
submodule. -/
theorem powerTorsion_injective [IsNoetherianRing R]
    (J : Ideal R) (K : ModuleCat.{u} R) [Injective K] :
    Injective (ModuleCat.of R (powerTorsion J K)) :=
  powerTorsion_injective_of_injective J K

end SGA.SGA2.ExposeIV
