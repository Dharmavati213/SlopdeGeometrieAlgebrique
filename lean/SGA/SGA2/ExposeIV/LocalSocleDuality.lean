/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalMonogenicCriterion

/-!
# SGA 2, IV §5: monogenic modules and the actual socle of their dual

The local socle is the literal maximal-ideal annihilator, also proved to
equal the sum of all simple submodules. It is exactly the orthogonal of
`𝔪 M`. Thus the original duality and genuine Nakayama single-generation
criterion give the source's cyclic/socle statement, including the zero case.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The actual local socle, consisting of elements killed by the maximal ideal. -/
def localSocle (M : Type u) [AddCommGroup M] [Module R M] : Submodule R M :=
  Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R)

@[simp]
theorem mem_localSocle (M : Type u) [AddCommGroup M] [Module R M] (x : M) :
    x ∈ localSocle (R := R) M ↔ ∀ r ∈ IsLocalRing.maximalIdeal R, r • x = 0 := by
  simp only [localSocle, Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

/-- Every simple submodule is annihilated by the original maximal ideal. -/
theorem simpleSubmodule_le_localSocle (M : Type u) [AddCommGroup M] [Module R M]
    (S : Submodule R M) [IsSimpleModule R S] : S ≤ localSocle (R := R) M := by
  intro x hx
  rw [mem_localSocle]
  intro r hr
  have hAnn : Module.annihilator R S = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := S))
  have hr' : r ∈ Module.annihilator R S := by rwa [hAnn]
  exact congrArg Subtype.val (Module.mem_annihilator.mp hr' (⟨x, hx⟩ : S))

/-- The annihilator definition is the genuine socle: the sum of all simple
submodules of the original module. No finite-length assumption is needed. -/
theorem localSocle_eq_sSup_simple (M : Type u) [AddCommGroup M] [Module R M] :
    localSocle (R := R) M = sSup {S : Submodule R M | IsSimpleModule R S} := by
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    let S : Submodule R M := Submodule.span R {x}
    have hxS : x ∈ S := Submodule.mem_span_singleton_self x
    have hS : S ≤ localSocle (R := R) M := Submodule.span_le.mpr (by
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hx)
    have hAnn : IsLocalRing.maximalIdeal R ≤ Module.annihilator R S := by
      intro r hr
      apply Module.mem_annihilator.mpr
      intro y
      apply Subtype.ext
      exact (mem_localSocle M y).mp (hS y.property) r hr
    have hgen : ModuleMonogenic (R := R) S := by
      apply (moduleMonogenic_iff_surjective S).mpr
      refine ⟨⟨x, hxS⟩, ?_⟩
      intro y
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp y.property
      exact ⟨r, Subtype.ext hr⟩
    have hlen := length_le_one_of_moduleMonogenic_of_maximal_annihilator
      S (IsLocalRing.maximalIdeal R) inferInstance hAnn hgen
    have : Nontrivial S := ⟨⟨⟨x, hxS⟩, 0, by
      intro heq
      exact hx0 (congrArg Subtype.val heq)⟩⟩
    have hsimp : IsSimpleModule R S := Module.length_eq_one_iff.mp
      (le_antisymm hlen (Order.one_le_iff_ne_zero.mpr Module.length_pos.ne'))
    have hle : S ≤ sSup {S : Submodule R M | IsSimpleModule R S} := le_sSup hsimp
    exact hle hxS
  · apply sSup_le
    intro S hS
    have : IsSimpleModule R S := hS
    exact simpleSubmodule_le_localSocle M S

/-- The socle commutes with an actual linear identification. -/
theorem localSocle_comap_linearEquiv
    {M D : Type u} [AddCommGroup M] [AddCommGroup D] [Module R M] [Module R D]
    (e : M ≃ₗ[R] D) :
    (localSocle (R := R) D).comap e.toLinearMap = localSocle (R := R) M := by
  ext x
  change e x ∈ localSocle (R := R) D ↔ x ∈ localSocle (R := R) M
  simp only [mem_localSocle, ← e.map_smul, e.map_eq_zero_iff]

/-- **IV §5:** the actual orthogonal of `𝔪 M` is exactly the actual socle
of `Hom_R(M,H)`, for arbitrary original coefficient `H`. -/
theorem homOrthogonal_maximalIdeal_smul (H M : ModuleCat.{u} R) :
    homOrthogonal H M (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) =
      localSocle (R := R) ((moduleHomDual H).obj (op M)) := by
  ext f
  rw [mem_homOrthogonal, mem_localSocle]
  constructor
  · intro hf r hr
    apply ModuleCat.hom_ext
    ext x
    change r • ModuleCat.Hom.hom f x = 0
    rw [← (ModuleCat.Hom.hom f).map_smul]
    exact hf (r • x) (Submodule.smul_mem_smul hr (Submodule.mem_top))
  · intro hf x hx
    have hle : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≤
        LinearMap.ker (ModuleCat.Hom.hom f) := by
      apply Submodule.smul_le.mpr
      intro r hr y _
      change ModuleCat.Hom.hom f (r • y) = 0
      rw [(ModuleCat.Hom.hom f).map_smul]
      exact congrArg (fun g : M ⟶ H ↦ g.hom y) (hf r hr)
    exact hle hx

/-- The actual Hom-dual socle length detects genuine single generation. -/
theorem moduleMonogenic_iff_homSocle_length_le_one
    (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    ModuleMonogenic (R := R) M ↔
      Module.length R (localSocle (R := R) ((moduleHomDual H).obj (op M))) ≤ 1 := by
  rw [moduleMonogenic_iff_residue_length_le_one]
  have hlen := homOrthogonal_colength_eq_length J H hfin hbid M hSupp
    (IsLocalRing.maximalIdeal R • ⊤)
  rw [homOrthogonal_maximalIdeal_smul] at hlen
  rw [hlen]

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The original functor's canonical orthogonal of `𝔪 M` is its actual socle. -/
theorem supportedFunctorOrthogonal_maximalIdeal_smul
    (h : SupportedFunctorDuality J T) (M : SupportedFGModuleCat J) :
    OrderDual.ofDual (supportedFunctorOrthogonalOrderIso J T h M
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M.obj))) =
        localSocle (R := R) (supportedFunctorValue J T M) := by
  let := supportedFunctorDuality_leftExact J T h
  change (homOrthogonal (supportedFunctorColimit J T) M.obj.obj
    (IsLocalRing.maximalIdeal R • ⊤)).comap
      ((supportedFunctorRepresentationIso J T).app (op M)).toLinearEquiv.toLinearMap = _
  rw [homOrthogonal_maximalIdeal_smul]
  exact localSocle_comap_linearEquiv
    ((supportedFunctorRepresentationIso J T).app (op M)).toLinearEquiv

/-- **SGA 2, IV §5, monogenic/socle statement for the original functor.**
The left side asserts one actual generator; the zero module is included. -/
theorem supportedFunctor_monogenic_iff_socle_length_le_one
    (h : SupportedFunctorDuality J T) (M : SupportedFGModuleCat J) :
    (∃ x : M.obj, Submodule.span R {x} = ⊤) ↔
      Module.length R (localSocle (R := R) (supportedFunctorValue J T M)) ≤ 1 := by
  change ModuleMonogenic (R := R) M.obj ↔ _
  rw [moduleMonogenic_iff_residue_length_le_one]
  have hlen := supportedFunctorOrthogonal_colength_eq_length J T h M
    (IsLocalRing.maximalIdeal R • ⊤)
  rw [supportedFunctorOrthogonal_maximalIdeal_smul] at hlen
  rw [hlen]

end SGA.SGA2.ExposeIV
