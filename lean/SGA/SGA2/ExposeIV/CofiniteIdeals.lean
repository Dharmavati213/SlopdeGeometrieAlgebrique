/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteLengthModuleCategory
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Cofinite ideals and their genuine quotient diagram

An ideal is cofinite when its actual quotient has finite module length.
The annihilator of every finite-length module is cofinite: a finite generating
family embeds its quotient ring into a finite power of the original module.
Intersections make reverse inclusion a filtered index, with the original
quotient maps giving a contravariant diagram of finite-length modules.

These facts hold over an arbitrary commutative ring. In particular, no
noetherian hypothesis, representation, or classification is assumed here.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The actual action of a scalar on a finite family of generators. -/
def generatorActionMap {n : ℕ} (s : Fin n → M) : R →ₗ[R] (Fin n → M) where
  toFun r i := r • s i
  map_add' r t := by funext i; exact add_smul r t (s i)
  map_smul' r t := by funext i; exact mul_smul r t (s i)

@[simp]
theorem generatorActionMap_apply {n : ℕ} (s : Fin n → M) (r : R) (i : Fin n) :
    generatorActionMap s r i = r • s i := rfl

/-- For generators, the kernel is exactly the original module annihilator. -/
theorem generatorActionMap_ker {n : ℕ} (s : Fin n → M)
    (hs : Submodule.span R (Set.range s) = ⊤) :
    (generatorActionMap s).ker = Module.annihilator R M := by
  ext r
  have hann : r ∈ Module.annihilator R M ↔ ∀ i, r • s i = 0 := by
    rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    simp only [Subtype.forall, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  rw [LinearMap.mem_ker, hann]
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

/-- The annihilator quotient acts faithfully on an actual generating family. -/
def quotientAnnihilatorGeneratorMap {n : ℕ} (s : Fin n → M)
    (hs : Submodule.span R (Set.range s) = ⊤) :
    (R ⧸ Module.annihilator R M) →ₗ[R] (Fin n → M) :=
  (Module.annihilator R M).liftQ (generatorActionMap s)
    (by rw [generatorActionMap_ker s hs])

@[simp]
theorem quotientAnnihilatorGeneratorMap_mk {n : ℕ} (s : Fin n → M)
    (hs : Submodule.span R (Set.range s) = ⊤) (r : R) (i : Fin n) :
    quotientAnnihilatorGeneratorMap s hs (Ideal.Quotient.mk _ r) i = r • s i := rfl

theorem quotientAnnihilatorGeneratorMap_injective {n : ℕ} (s : Fin n → M)
    (hs : Submodule.span R (Set.range s) = ⊤) :
    Function.Injective (quotientAnnihilatorGeneratorMap s hs) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [generatorActionMap_ker s hs])

/-- The annihilator quotient of a finite-length module has finite length,
without any noetherian hypothesis on the commutative base ring. -/
theorem quotient_annihilator_isFiniteLength (hM : IsFiniteLength R M) :
    IsFiniteLength R (R ⧸ Module.annihilator R M) := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  let : IsNoetherian R M := hN
  let : IsArtinian R M := hA
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hp : IsFiniteLength R (Fin n → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hp.of_injective (quotientAnnihilatorGeneratorMap_injective s hs)

/-- The actual map from the intersection quotient into the product of quotients. -/
def quotientIntersectionMap (I J : Ideal R) :
    (R ⧸ I ⊓ J) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
  (Submodule.factor inf_le_left).prod (Submodule.factor inf_le_right)

@[simp]
theorem quotientIntersectionMap_mk (I J : Ideal R) (r : R) :
    quotientIntersectionMap I J (Ideal.Quotient.mk _ r) =
      (Ideal.Quotient.mk I r, Ideal.Quotient.mk J r) := rfl

theorem quotientIntersectionMap_injective (I J : Ideal R) :
    Function.Injective (quotientIntersectionMap I J) := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  change quotientIntersectionMap I J x = 0 at hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (I ⊓ J) r = 0
  apply (Submodule.Quotient.mk_eq_zero (I ⊓ J)).mpr
  exact ⟨(Submodule.Quotient.mk_eq_zero I).mp (congrArg Prod.fst hx),
    (Submodule.Quotient.mk_eq_zero J).mp (congrArg Prod.snd hx)⟩

/-- Cofiniteness is closed under the original ideal intersection. -/
theorem quotient_inf_isFiniteLength (I J : Ideal R)
    (hI : IsFiniteLength R (R ⧸ I)) (hJ : IsFiniteLength R (R ⧸ J)) :
    IsFiniteLength R (R ⧸ I ⊓ J) := by
  obtain ⟨hIN, hIA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hI
  obtain ⟨hJN, hJA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hJ
  let : IsNoetherian R (R ⧸ I) := hIN
  let : IsArtinian R (R ⧸ I) := hIA
  let : IsNoetherian R (R ⧸ J) := hJN
  let : IsArtinian R (R ⧸ J) := hJA
  have hp : IsFiniteLength R ((R ⧸ I) × (R ⧸ J)) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hp.of_injective (quotientIntersectionMap_injective I J)

/-- Any further quotient of a cofinite quotient has finite length. -/
theorem quotient_isFiniteLength_of_le {I J : Ideal R} (h : I ≤ J)
    (hI : IsFiniteLength R (R ⧸ I)) : IsFiniteLength R (R ⧸ J) :=
  hI.of_surjective (Submodule.factor_surjective h)

/-- Cofiniteness refers to the length of the actual quotient module. -/
def cofiniteIdealProperty (R : Type u) [CommRing R] (I : Ideal R) : Prop :=
  IsFiniteLength R (R ⧸ I)

/-- Actual cofinite ideals, ordered by their ordinary inclusion. -/
abbrev CofiniteIdeal (R : Type u) [CommRing R] :=
  {I : Ideal R // cofiniteIdealProperty R I}

instance cofiniteIdealSemilatticeInf : SemilatticeInf (CofiniteIdeal R) where
  __ := (inferInstance : PartialOrder (CofiniteIdeal R))
  inf I J := ⟨I.val ⊓ J.val, quotient_inf_isFiniteLength _ _ I.property J.property⟩
  inf_le_left _ _ := by exact (inf_le_left : (_ : Ideal R) ⊓ _ ≤ _)
  inf_le_right _ _ := by exact (inf_le_right : (_ : Ideal R) ⊓ _ ≤ _)
  le_inf _ _ _ hI hJ := by exact (le_inf hI hJ : _ ≤ (_ : Ideal R) ⊓ _)

instance cofiniteIdealOrderTop : OrderTop (CofiniteIdeal R) where
  top := ⟨⊤, IsFiniteLength.of_subsingleton⟩
  le_top _ := by exact (le_top : (_ : Ideal R) ≤ ⊤)

instance cofiniteIdealNonempty : Nonempty (CofiniteIdeal R) := ⟨⊤⟩

/-- The index increases when the underlying cofinite ideal gets smaller. -/
abbrev CofiniteIdealIndex (R : Type u) [CommRing R] := (CofiniteIdeal R)ᵒᵈ

instance cofiniteIdealIndexIsFiltered : IsFiltered (CofiniteIdealIndex R) :=
  isFiltered_of_semilatticeSup_nonempty _

/-- Every actual finite-length module has a canonical cofinite annihilator. -/
def cofiniteAnnihilator (M : Type v) [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) : CofiniteIdealIndex R :=
  ⟨Module.annihilator R M, quotient_annihilator_isFiniteLength hM⟩

@[simp]
theorem cofiniteAnnihilator_val (hM : IsFiniteLength R M) :
    (cofiniteAnnihilator M hM).val = Module.annihilator R M := rfl

/-- The original quotient ring, regarded as a finite-length module. -/
def cofiniteRingQuotient (I : CofiniteIdealIndex R) : FiniteLengthModuleCat R :=
  ⟨ModuleCat.of R (R ⧸ I.val), I.property⟩

/-- The original quotient map corresponding to a reverse inclusion. -/
def cofiniteRingQuotientMap {I J : CofiniteIdealIndex R} (h : I ≤ J) :
    cofiniteRingQuotient J ⟶ cofiniteRingQuotient I :=
  ObjectProperty.homMk (ModuleCat.ofHom (Submodule.factor h))

@[simp]
theorem cofiniteRingQuotientMap_apply {I J : CofiniteIdealIndex R} (h : I ≤ J) (r : R) :
    (cofiniteRingQuotientMap h).hom (Ideal.Quotient.mk J.val r) =
      Ideal.Quotient.mk I.val r := rfl

theorem cofiniteRingQuotientMap_refl (I : CofiniteIdealIndex R) :
    cofiniteRingQuotientMap (le_refl I) = 𝟙 (cofiniteRingQuotient I) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem cofiniteRingQuotientMap_comp {I J K : CofiniteIdealIndex R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    cofiniteRingQuotientMap hJK ≫ cofiniteRingQuotientMap hIJ =
      cofiniteRingQuotientMap (hIJ.trans hJK) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  exact Submodule.factor_comp hJK hIJ

instance cofiniteRingQuotientMap_epi {I J : CofiniteIdealIndex R} (h : I ≤ J) :
    Epi (cofiniteRingQuotientMap h) := by
  apply (finiteLengthInclusion R).epi_of_epi_map
  exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.factor_surjective h)

/-- Quotient rings and their original quotient maps form the required diagram. -/
def cofiniteRingQuotientDiagram (R : Type u) [CommRing R] :
    (CofiniteIdealIndex R)ᵒᵖ ⥤ FiniteLengthModuleCat R where
  obj I := cofiniteRingQuotient I.unop
  map f := cofiniteRingQuotientMap (leOfHom f.unop)
  map_id I := cofiniteRingQuotientMap_refl I.unop
  map_comp f g :=
    (cofiniteRingQuotientMap_comp (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Applying an original contravariant functor gives the filtered diagram
whose terms are exactly `T(R/I)`. -/
def cofiniteFunctorDiagram {C : Type*} [Category C]
    (T : (FiniteLengthModuleCat R)ᵒᵖ ⥤ C) : CofiniteIdealIndex R ⥤ C :=
  (cofiniteRingQuotientDiagram R).rightOp ⋙ T

end SGA.SGA2.ExposeIV
