/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CofiniteFunctorDiagram
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The original nonlocal cofinite-ideal colimit

The colimit uses the original `T(R/I)` groups, their canonical actions and
their quotient-induced transitions. Every finite-source map has image in
one original stage; for a left-exact functor it actually factors through
that stage. The resulting module is locally Artinian over a noetherian
ring. No representing property or finite stage-value hypothesis is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The actual colimit over all cofinite ideals, with the canonical actions. -/
def cofiniteFunctorColimit : ModuleCat.{u} R := colimit (cofiniteFunctorModuleDiagram T)

/-- The original structural map of each quotient-functor stage. -/
def cofiniteFunctorColimitι (I : CofiniteIdealIndex R) :
    cofiniteFunctorStage T I ⟶ cofiniteFunctorColimit T :=
  colimit.ι (cofiniteFunctorModuleDiagram T) I

@[reassoc]
theorem cofiniteFunctorColimitι_transition {I J : CofiniteIdealIndex R} (h : I ≤ J) :
    cofiniteFunctorTransition T h ≫ cofiniteFunctorColimitι T J = cofiniteFunctorColimitι T I :=
  colimit.w (cofiniteFunctorModuleDiagram T) (homOfLE h)

/-- Every actual colimit element is represented in an original stage. -/
theorem cofiniteFunctorColimit_exists_rep (x : cofiniteFunctorColimit T) :
    ∃ (I : CofiniteIdealIndex R) (y : cofiniteFunctorStage T I),
      cofiniteFunctorColimitι T I y = x :=
  Concrete.colimit_exists_rep (cofiniteFunctorModuleDiagram T) x

/-- Stage images increase in the actual reverse-inclusion order. -/
theorem cofiniteFunctorColimit_range_monotone :
    Monotone (fun I : CofiniteIdealIndex R ↦
      LinearMap.range (cofiniteFunctorColimitι T I).hom) := by
  intro I J h x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨cofiniteFunctorTransition T h y, ?_⟩
  exact ConcreteCategory.congr_hom (cofiniteFunctorColimitι_transition T h) y

/-- The original stage images exhaust the actual module. -/
theorem cofiniteFunctorColimit_iSup_range :
    (⨆ I : CofiniteIdealIndex R, LinearMap.range (cofiniteFunctorColimitι T I).hom) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨I, y, rfl⟩ := cofiniteFunctorColimit_exists_rep T x
  exact Submodule.mem_iSup_of_mem I (LinearMap.mem_range_self _ y)

/-- A finite-source image is contained in one original stage image. -/
theorem cofiniteFunctorColimit_range_le_stage (M : ModuleCat.{u} R) [Module.Finite R M]
    (f : M ⟶ cofiniteFunctorColimit T) :
    ∃ I : CofiniteIdealIndex R,
      LinearMap.range f.hom ≤ LinearMap.range (cofiniteFunctorColimitι T I).hom := by
  classical
  obtain ⟨S, hS⟩ := Submodule.fg_range f.hom
  have hrep (x : S) :
      ∃ I : CofiniteIdealIndex R, x.val ∈ LinearMap.range (cofiniteFunctorColimitι T I).hom := by
    obtain ⟨I, y, hy⟩ := cofiniteFunctorColimit_exists_rep T x.val
    exact ⟨I, y, hy⟩
  choose k hk using hrep
  refine ⟨S.attach.sup k, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact cofiniteFunctorColimit_range_monotone T
    (Finset.le_sup (S.mem_attach ⟨x, hx⟩)) (hk ⟨x, hx⟩)

/-- Left exactness makes every original stage-to-colimit map injective. -/
theorem cofiniteFunctorColimitι_injective [PreservesFiniteLimits T] (I : CofiniteIdealIndex R) :
    Function.Injective (cofiniteFunctorColimitι T I) := by
  intro x y h
  obtain ⟨K, f, g, hfg⟩ :=
    Concrete.colimit_exists_of_rep_eq (cofiniteFunctorModuleDiagram T) x y h
  have hg : g = f := Subsingleton.elim _ _
  subst g
  exact cofiniteFunctorTransition_injective T (leOfHom f) hfg

instance [PreservesFiniteLimits T] (I : CofiniteIdealIndex R) :
    Mono (cofiniteFunctorColimitι T I) :=
  (ModuleCat.mono_iff_injective _).mpr (cofiniteFunctorColimitι_injective T I)

/-- Every finite-source map factors through an actual stage for left-exact
`T`; only the source, not the stage value, is assumed finite. -/
theorem cofiniteFunctorColimit_exists_factor [PreservesFiniteLimits T]
    (M : ModuleCat.{u} R) [Module.Finite R M] (f : M ⟶ cofiniteFunctorColimit T) :
    ∃ (I : CofiniteIdealIndex R) (g : M ⟶ cofiniteFunctorStage T I),
      g ≫ cofiniteFunctorColimitι T I = f := by
  obtain ⟨I, hI⟩ := cofiniteFunctorColimit_range_le_stage T M f
  let e := LinearEquiv.ofInjective (cofiniteFunctorColimitι T I).hom
    (cofiniteFunctorColimitι_injective T I)
  let g : M →ₗ[R] cofiniteFunctorStage T I := e.symm.toLinearMap.comp
    (f.hom.codRestrict _ (fun x ↦ hI (LinearMap.mem_range_self f.hom x)))
  refine ⟨I, ModuleCat.ofHom (X := M) (Y := cofiniteFunctorStage T I) g, ?_⟩
  ext x
  exact LinearEquiv.ofInjective_symm_apply _ (h := cofiniteFunctorColimitι_injective T I) _

/-- Every actual finite submodule of the colimit is annihilated by a
cofinite ideal, even without left exactness of the original functor. -/
theorem cofiniteFunctorColimit_finiteSubmodule_annihilator
    (P : Submodule R (cofiniteFunctorColimit T)) [Module.Finite R P] :
    ∃ I : CofiniteIdealIndex R, I.val ≤ Module.annihilator R P := by
  obtain ⟨I, hI⟩ := cofiniteFunctorColimit_range_le_stage T (ModuleCat.of R P)
    (ModuleCat.ofHom P.subtype)
  refine ⟨I, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := hI (LinearMap.mem_range_self P.subtype x)
  change (cofiniteFunctorColimitι T I).hom y = x.val at hy
  change r • x.val = 0
  rw [← hy, ← (cofiniteFunctorColimitι T I).hom.map_smul,
    cofiniteFunctorStage_smul_eq_zero T I hr, map_zero]

/-- The actual original colimit is locally Artinian; neither left exactness
nor finite functor values are needed for this property. -/
theorem cofiniteFunctorColimit_locallyArtinian [IsNoetherianRing R] :
    ModuleLocallyArtinian (R := R) (cofiniteFunctorColimit T) := by
  apply (moduleLocallyArtinian_iff_finiteLength _).mpr
  intro P hP
  have : Module.Finite R P := Module.Finite.of_fg hP
  obtain ⟨I, hI⟩ := cofiniteFunctorColimit_finiteSubmodule_annihilator T P
  have : IsArtinian R (R ⧸ I.val) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp I.property).2
  have : IsArtinianRing (R ⧸ I.val) := isArtinian_of_tower R inferInstance
  apply isFiniteLength_of_finite_of_support I.val (ModuleCat.of R P)
  apply (support_subset_zeroLocus_iff_exists_pow_le_annihilator I.val P).mpr
  exact ⟨1, by simpa only [pow_one] using hI⟩

end SGA.SGA2.ExposeIV
