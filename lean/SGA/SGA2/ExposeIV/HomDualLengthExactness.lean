/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.HomDualResidueConverse

/-!
# Length preservation implies exactness of the original Hom dual

This proves the Hom-model form of SGA 2, IV.3.2. The dual sequence is
genuinely left exact without any injectivity hypothesis. Additivity of the
original finite lengths forces its last map to be surjective. The supported
Hom criterion then yields injectivity of the original arbitrary target.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- In a genuinely left exact module sequence, the expected finite length
identity forces the last map to be surjective. -/
theorem linearMap_surjective_of_exact_of_length_eq
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hex : Function.Exact f g) (hA : IsFiniteLength R A) (hC : IsFiniteLength R C)
    (hlen : Module.length R B = Module.length R A + Module.length R C) :
    Function.Surjective g := by
  have hRangeExact : Function.Exact f g.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp hex
  have hRange := Module.length_eq_add_of_exact f g.rangeRestrict hf
    g.surjective_rangeRestrict hRangeExact
  have hRangeLength : Module.length R (LinearMap.range g) = Module.length R C :=
    ENat.add_right_injective_of_ne_top (Module.length_ne_top_iff.mpr hA)
      (hRange.symm.trans hlen)
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hC).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hC).2
  apply LinearMap.range_eq_top.mp
  by_contra h
  exact (Submodule.length_lt h).ne hRangeLength

/-- Genuine left exactness of `Hom_R(-,H)` for arbitrary `H`, expressed on
the original module-valued Hom sequence. -/
theorem moduleHomDual_leftExact (H : ModuleCat.{u} R)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.op.map (moduleHomDual H)).Exact ∧ Mono ((S.op.map (moduleHomDual H)).f) := by
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (preadditiveYoneda.obj H)).mp inferInstance S.op hS.op
  refine ⟨(forget₂ (ModuleCat R) AddCommGrpCat).reflects_exact_of_faithful _ h.1, ?_⟩
  have := hS.epi_g
  exact moduleHomDual_map_mono H S.g

variable [IsNoetherianRing R]
variable (J : Ideal R) [IsArtinianRing (R ⧸ J)]
variable (H : ModuleCat.{u} R) (hlen : SupportedHomLengthPreserving J H)

include hlen

/-- Length preservation gives actual finite Hom values, rather than
presupposing that the dual functor takes values in finite modules. -/
theorem finiteSupportedHomValues_of_length_preserving : FiniteSupportedHomValues J H := by
  intro M hM hSupp
  have := hM
  have hL : IsFiniteLength R ((moduleHomDual H).obj (op M)) := by
    apply Module.length_ne_top_iff.mp
    rw [hlen M hM hSupp]
    exact Module.length_ne_top_iff.mpr (isFiniteLength_of_finite_of_support J M hSupp)
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hL).1
  infer_instance

/-- **IV.3.2, actual Hom form:** equality of all supported finite lengths
forces the genuine Hom sequence to be short exact. Exactness is a conclusion. -/
theorem moduleHomDual_shortExact_of_length_preserving
    (S : ShortComplex (ModuleCat.{u} R)) (hM : Module.Finite R S.X₂)
    (hSupp : supportedModuleProperty J S.X₂) (hS : S.ShortExact) :
    (S.op.map (moduleHomDual H)).ShortExact := by
  have := hM
  have := hS.mono_f
  have := hS.epi_g
  have hM₁ : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom
    ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
  have hM₃ : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom
    ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
  have hs₁ : supportedModuleProperty J S.X₁ :=
    (supportedModuleProperty J).prop_of_mono S.f hSupp
  have hs₃ : supportedModuleProperty J S.X₃ :=
    (supportedModuleProperty J).prop_of_epi S.g hSupp
  let D := S.op.map (moduleHomDual H)
  have hleft := moduleHomDual_leftExact H hS
  have hL₁ : IsFiniteLength R D.X₁ := by
    apply Module.length_ne_top_iff.mp
    change Module.length R ((moduleHomDual H).obj (op S.X₃)) ≠ ⊤
    rw [hlen S.X₃ hM₃ hs₃]
    exact Module.length_ne_top_iff.mpr (isFiniteLength_of_finite_of_support J S.X₃ hs₃)
  have hL₃ : IsFiniteLength R D.X₃ := by
    apply Module.length_ne_top_iff.mp
    change Module.length R ((moduleHomDual H).obj (op S.X₁)) ≠ ⊤
    rw [hlen S.X₁ hM₁ hs₁]
    exact Module.length_ne_top_iff.mpr (isFiniteLength_of_finite_of_support J S.X₁ hs₁)
  have hsum : Module.length R D.X₂ = Module.length R D.X₁ + Module.length R D.X₃ := by
    change Module.length R ((moduleHomDual H).obj (op S.X₂)) =
      Module.length R ((moduleHomDual H).obj (op S.X₃)) +
        Module.length R ((moduleHomDual H).obj (op S.X₁))
    rw [hlen S.X₂ hM hSupp, hlen S.X₃ hM₃ hs₃, hlen S.X₁ hM₁ hs₁, add_comm]
    exact Module.length_eq_add_of_exact S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
  refine ShortComplex.ShortExact.mk' hleft.1 hleft.2
    ((ModuleCat.epi_iff_surjective _).mpr ?_)
  exact linearMap_surjective_of_exact_of_length_eq D.f.hom D.g.hom
    ((ModuleCat.mono_iff_injective _).mp hleft.2)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hleft.1) hL₁ hL₃ hsum

/-- Equality of the original finite supported lengths forces the exactness
condition in the supported injectivity criterion. -/
theorem finiteSupportedHomExact_of_length_preserving : FiniteSupportedHomExact J H := by
  intro S hM hSupp hS
  exact (moduleHomDual_shortExact_of_length_preserving J H hlen S hM hSupp hS).map_of_exact
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- **IV.3.2:** length preservation forces injectivity of the actual
supported target. There is no exactness assumption. -/
theorem injective_of_supported_length_preserving (hH : supportedModuleProperty J H) :
    Injective H :=
  (finiteSupportedHomExact_iff_injective_of_support J H hH).mp
    (finiteSupportedHomExact_of_length_preserving J H hlen)

omit hlen in
/-- The canonical biduality criterion and the injective residue-field
criterion of IV.3.1 are equivalent for the original supported Hom model. -/
theorem supportedHomBiduality_iff_injective_and_residueTests
    (hH : supportedModuleProperty J H) :
    (FiniteSupportedHomValues J H ∧ SupportedModuleBiduality J H) ↔
      (Injective H ∧ moduleHomDualResidueTests J H) := by
  constructor
  · rintro ⟨hfin, hbid⟩
    exact ⟨injective_of_supported_bidually_reflexive J H hH hfin hbid,
      moduleHomDualResidueTests_of_supported_bidually_reflexive J H hH hfin hbid⟩
  · rintro ⟨hI, hres⟩
    have := hI
    constructor
    · intro M hM hs
      have := hM
      exact moduleHomDual_finite_of_artinian_support J H hres M hs
    · intro M hM hs
      have := hM
      exact moduleBidualEvaluation_isIso_of_artinian_support J H hres M hs

omit hlen in
/-- **IV.3.2, supported Hom model:** length preservation alone is equivalent
to injectivity and the residue-field tests. No exactness hypothesis is hidden
on the left-hand side. -/
theorem supportedHomLengthPreserving_iff_injective_and_residueTests
    (hH : supportedModuleProperty J H) :
    SupportedHomLengthPreserving J H ↔ (Injective H ∧ moduleHomDualResidueTests J H) := by
  constructor
  · intro hlen
    exact ⟨injective_of_supported_length_preserving J H hlen hH,
      moduleHomDualResidueTests_of_length_preserving J H hlen⟩
  · rintro ⟨hI, hres⟩ M hM hs
    have := hI
    have := hM
    exact moduleHomDual_length_of_artinian_support J H hres M hs

omit hlen in
/-- The explicit exactness clause in IV.3.1(iv) is redundant for the
original Hom functor, as asserted in IV.3.2. -/
theorem finiteSupportedHomExact_and_length_iff_length :
    (FiniteSupportedHomExact J H ∧ SupportedHomLengthPreserving J H) ↔
      SupportedHomLengthPreserving J H :=
  ⟨And.right, fun h ↦ ⟨finiteSupportedHomExact_of_length_preserving J H h, h⟩⟩

end SGA.SGA2.ExposeIV
