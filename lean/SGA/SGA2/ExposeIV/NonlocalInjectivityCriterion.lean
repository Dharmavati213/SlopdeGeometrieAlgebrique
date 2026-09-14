/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CofiniteIdeals
import SGA.SGA2.ExposeIV.FiniteLengthRestrictedHom
import SGA.SGA2.ExposeIV.InjectivityCriterion
import SGA.SGA2.ExposeIV.SupportedArtinianDuality

/-!
# Nonlocal injectivity tested on the original finite-length modules

For a locally Artinian module over a commutative noetherian ring, exactness
of its actual contravariant Hom on finite-length modules is equivalent to
injectivity in the category of all modules.  The proof uses Baer's criterion:
the finite image of an ideal map has a cofinite annihilator, and Artin–Rees
reduces extension to a submodule of an actual finite-length quotient ring.

No local decomposition, representation theorem, or injectivity of the target
is assumed in the converse.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- The unchanged restricted Hom functor is additive. -/
instance finiteLengthModuleRepresentations_obj_additive (H : ModuleCat.{u} R) :
    (finiteLengthModuleRepresentations.obj H).Additive :=
  inferInstanceAs (((finiteLengthInclusion R).op ⋙ preadditiveYoneda.obj H).Additive)

/-- Actual linear maps from submodules of finite-length modules extend to
the original ambient module. -/
def FiniteLengthHomExtension (H : ModuleCat.{u} R) : Prop :=
  ∀ (M : ModuleCat.{u} R), IsFiniteLength R M →
    ∀ (N : Submodule R M) (f : N →ₗ[R] H),
      ∃ g : M →ₗ[R] H, g.comp N.subtype = f

/-- Exactness of the unchanged additive Hom functor on the genuine category
of all finite-length modules. -/
def FiniteLengthHomExact (H : ModuleCat.{u} R) : Prop :=
  ∀ (S : ShortComplex (FiniteLengthModuleCat R)), S.ShortExact →
    (S.op.map (finiteLengthModuleRepresentations.obj H)).ShortExact

/-- Injectivity in all modules gives actual extensions on finite-length modules. -/
theorem finiteLengthHomExtension_of_injective (H : ModuleCat.{u} R) [Injective H] :
    FiniteLengthHomExtension H := by
  intro M _ N f
  let i : ModuleCat.of R N ⟶ M := ModuleCat.ofHom N.subtype
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr N.injective_subtype
  refine ⟨(Injective.factorThru (ModuleCat.ofHom f) i).hom, ?_⟩
  exact ModuleCat.hom_ext_iff.mp (Injective.comp_factorThru (ModuleCat.ofHom f) i)

/-- An injective coefficient makes the original restricted Hom exact. -/
theorem finiteLengthHomExact_of_injective (H : ModuleCat.{u} R) [Injective H] :
    FiniteLengthHomExact H := by
  intro S hS
  have h := (hS.map_of_exact (finiteLengthInclusion R)).op
  exact (h.map_of_exact (preadditiveYonedaObj H)).map_of_exact
    (forget₂ (ModuleCat (End H)) AddCommGrpCat)

/-- Exactness on the original finite-length category supplies extensions
from its actual submodules, which also have finite length. -/
theorem finiteLengthHomExtension_of_exact (H : ModuleCat.{u} R)
    (hExact : FiniteLengthHomExact H) : FiniteLengthHomExtension H := by
  intro M hM N f
  let A : FiniteLengthModuleCat R :=
    ⟨ModuleCat.of R N, hM.of_injective N.injective_subtype⟩
  let B : FiniteLengthModuleCat R := ⟨M, hM⟩
  let C : FiniteLengthModuleCat R :=
    ⟨ModuleCat.of R (M ⧸ N), hM.of_surjective N.mkQ_surjective⟩
  let S : ShortComplex (FiniteLengthModuleCat R) :=
    ShortComplex.mk (X₁ := A) (X₂ := B) (X₃ := C)
      (ObjectProperty.homMk (ModuleCat.ofHom N.subtype))
      (ObjectProperty.homMk (ModuleCat.ofHom N.mkQ))
      (by
        apply ObjectProperty.hom_ext
        ext x
        exact (Submodule.Quotient.mk_eq_zero N).mpr x.property)
  have hS : S.ShortExact := (finiteLengthInclusion_shortExact_iff R S).mp
    { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
        (N.range_subtype.trans N.ker_mkQ.symm)
      mono_f := (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective }
  have hsurj := (AddCommGrpCat.epi_iff_surjective
    (S.op.map (finiteLengthModuleRepresentations.obj H)).g).mp (hExact S hS).epi_g
  obtain ⟨g, hg⟩ := hsurj (ModuleCat.ofHom f)
  exact ⟨g.hom, ModuleCat.hom_ext_iff.mp hg⟩

/-- Exactness on the original finite-length short sequences is precisely
categorical exactness of the same actual restricted Hom functor. -/
theorem finiteLengthHomExact_iff_preservesHomology (H : ModuleCat.{u} R) :
    FiniteLengthHomExact H ↔ (finiteLengthModuleRepresentations.obj H).PreservesHomology := by
  constructor
  · intro h
    apply ((Functor.exact_tfae (finiteLengthModuleRepresentations.obj H)).out 1 3).mp
    intro S hS
    exact ShortComplex.shortExact_of_iso
      ((finiteLengthModuleRepresentations.obj H).mapShortComplex.mapIso S.unopOp)
      (h S.unop hS.unop)
  · intro h S hS
    have h' : ∀ Q : ShortComplex (FiniteLengthModuleCat R)ᵒᵖ, Q.ShortExact →
        (Q.map (finiteLengthModuleRepresentations.obj H)).ShortExact :=
      ((Functor.exact_tfae (finiteLengthModuleRepresentations.obj H)).out 1 3).mpr h
    exact h' S.op hS.op

variable [IsNoetherianRing R]

/-- Powers of an actual cofinite ideal still have finite-length quotients. -/
theorem cofiniteQuotientPower_isFiniteLength (I : CofiniteIdealIndex R) (n : ℕ) :
    IsFiniteLength R (R ⧸ I.val ^ n) := by
  have : IsArtinian R (R ⧸ I.val) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp I.property).2
  have : IsArtinianRing (R ⧸ I.val) := isArtinian_of_tower R inferInstance
  apply isFiniteLength_of_finite_of_support I.val (ModuleCat.of R (R ⧸ I.val ^ n))
  exact (support_subset_zeroLocus_iff_exists_pow_le_annihilator I.val _).mpr
    ⟨n, by rw [Ideal.annihilator_quotient]⟩

/-- Genuine cofinite Baer reduction: every ideal map into a locally Artinian
module kills the intersection with some actual cofinite ideal. -/
theorem exists_cofinite_inf_le_map_ker_of_locallyArtinian (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) (L : Ideal R) (f : L →ₗ[R] H) :
    ∃ I : CofiniteIdealIndex R, I.val ⊓ L ≤ f.ker.map L.subtype := by
  have hRange : IsFiniteLength R f.range :=
    (moduleLocallyArtinian_iff_finiteLength H).mp hH f.range (Submodule.fg_range f)
  let J : CofiniteIdealIndex R := cofiniteAnnihilator f.range hRange
  have hf : f.range ≤ powerTorsion J.val H := by
    rintro y ⟨x, rfl⟩
    apply (mem_powerTorsion_iff J.val H (f x)).mpr
    refine ⟨1, fun r hr => ?_⟩
    have hrJ : r ∈ Module.annihilator R f.range := by
      change r ∈ J.val
      simpa only [pow_one] using hr
    exact congrArg Subtype.val
      (Module.mem_annihilator.mp hrJ (f.rangeRestrict x))
  obtain ⟨n, hn⟩ := exists_pow_inf_le_map_ker_of_range_le_powerTorsion J.val L f hf
  exact ⟨⟨J.val ^ n, cofiniteQuotientPower_isFiniteLength J n⟩, hn⟩

/-- Baer's actual extension property follows from finite-length Hom extension
for a locally Artinian target. -/
theorem baer_of_locallyArtinian_finiteLengthHomExtension (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) (hExt : FiniteLengthHomExtension H) :
    Module.Baer R H := by
  intro L f
  obtain ⟨I, hI⟩ := exists_cofinite_inf_le_map_ker_of_locallyArtinian H hH L f
  let p : L →ₗ[R] R ⧸ I.val := I.val.mkQ.comp L.subtype
  have hp : p.ker ≤ f.ker := by
    intro x hx
    have hxI : (x : R) ∈ I.val := (Submodule.Quotient.mk_eq_zero I.val).mp hx
    obtain ⟨y, hy, he⟩ := hI ⟨hxI, x.property⟩
    exact (show y = x from Subtype.ext he) ▸ hy
  let f' : p.range →ₗ[R] H :=
    (p.ker.liftQ f hp).comp p.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := hExt (ModuleCat.of R (R ⧸ I.val)) I.property p.range f'
  refine ⟨g.comp I.val.mkQ, ?_⟩
  intro x hx
  have heval := congrArg (fun k : p.range →ₗ[R] H => k (p.rangeRestrict ⟨x, hx⟩)) hg
  change g (I.val.mkQ x) = f' (p.rangeRestrict ⟨x, hx⟩) at heval
  change g (I.val.mkQ x) = f ⟨x, hx⟩
  rw [heval]
  change p.ker.liftQ f hp (p.quotKerEquivRange.symm ⟨p ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩) = _
  exact congrArg (p.ker.liftQ f hp)
    (p.quotKerEquivRange_symm_apply_image ⟨x, hx⟩ ⟨⟨x, hx⟩, rfl⟩)

/-- The finite-length extension test gives injectivity among all actual modules. -/
theorem injective_of_locallyArtinian_finiteLengthHomExtension (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) (hExt : FiniteLengthHomExtension H) :
    Injective H := by
  let : Module.Injective R H :=
    (baer_of_locallyArtinian_finiteLengthHomExtension H hH hExt).injective
  exact Module.injective_object_of_injective_module R H

/-- Nonlocal extension-form injectivity criterion, with no finiteness
assumption on the locally Artinian target itself. -/
theorem finiteLengthHomExtension_iff_injective (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) :
    FiniteLengthHomExtension H ↔ Injective H :=
  ⟨injective_of_locallyArtinian_finiteLengthHomExtension H hH,
    fun _ => finiteLengthHomExtension_of_injective H⟩

/-- For an arbitrary locally Artinian module over a commutative noetherian
ring, injectivity is equivalent to exactness of the original Hom functor
on the entire genuine finite-length module category. -/
theorem finiteLengthHomExact_iff_injective (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) :
    FiniteLengthHomExact H ↔ Injective H :=
  ⟨fun h => injective_of_locallyArtinian_finiteLengthHomExtension H hH
      (finiteLengthHomExtension_of_exact H h),
    fun _ => finiteLengthHomExact_of_injective H⟩

/-- The same full nonlocal injectivity test in mathlib's categorical exactness
formulation, on the unchanged original Hom functor. -/
theorem finiteLengthHom_preservesHomology_iff_injective (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) :
    (finiteLengthModuleRepresentations.obj H).PreservesHomology ↔ Injective H :=
  (finiteLengthHomExact_iff_preservesHomology H).symm.trans
    (finiteLengthHomExact_iff_injective H hH)

end SGA.SGA2.ExposeIV
