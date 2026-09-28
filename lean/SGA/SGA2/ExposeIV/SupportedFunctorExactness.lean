/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorRepresentation
import SGA.SGA2.ExposeIV.SupportedModuleTorsion
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# SGA 2, IV.2.1 for the original supported functor

For the original additive left-exact functor `T`, exactness is equivalent to
injectivity of its actual representing colimit. Exactness means preservation
of all genuine short exact sequences, equivalently `PreservesHomology`.
The comparison with the ambient-module Hom criterion is proved by lifting
the actual finite supported sequences, not assumed as an extra hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

instance supportedFiniteToModule_additive (J : Ideal R) : (supportedFiniteToModule J).Additive := by
  unfold supportedFiniteToModule
  infer_instance

instance supportedFiniteToModule_faithful (J : Ideal R) : (supportedFiniteToModule J).Faithful := by
  unfold supportedFiniteToModule
  infer_instance

instance supportedFiniteToModule_preservesFiniteLimits (J : Ideal R) :
    PreservesFiniteLimits (supportedFiniteToModule J) := by
  unfold supportedFiniteToModule
  exact comp_preservesFiniteLimits _ _

instance supportedFiniteToModule_preservesFiniteColimits (J : Ideal R) :
    PreservesFiniteColimits (supportedFiniteToModule J) := by
  unfold supportedFiniteToModule
  exact comp_preservesFiniteColimits _ _

/-- Exactness of the original contravariant functor, formulated on all
short exact sequences in its actual supported source category. -/
def SupportedFunctorExact (J : Ideal R)
    (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive] : Prop :=
  ∀ S : ShortComplex (SupportedFGModuleCat J), S.ShortExact → (S.op.map T).ShortExact

/-- This is the usual categorical exactness condition, not a restricted
selection of test sequences. -/
theorem supportedFunctorExact_iff_preservesHomology (J : Ideal R)
    (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive] :
    SupportedFunctorExact J T ↔ T.PreservesHomology := by
  have h : SupportedFunctorExact J T ↔
      ∀ S : ShortComplex (SupportedFGModuleCat J)ᵒᵖ,
        S.ShortExact → (S.map T).ShortExact := by
    constructor
    · intro h S hS
      exact h S.unop hS.unop
    · intro h S hS
      exact h S.op hS.op
  exact h.trans ((Functor.exact_tfae T).out 1 3)

omit [IsNoetherianRing R] in
/-- Exactness transfers along actual natural isomorphisms. -/
theorem supportedFunctorExact_iff_of_iso (J : Ideal R)
    {T U : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}} [T.Additive] [U.Additive]
    (e : T ≅ U) : SupportedFunctorExact J T ↔ SupportedFunctorExact J U := by
  constructor
  · intro h S hS
    exact (ShortComplex.shortExact_iff_of_iso (S.op.mapNatIso e)).mp (h S hS)
  · intro h S hS
    exact (ShortComplex.shortExact_iff_of_iso (S.op.mapNatIso e)).mpr (h S hS)

/-- Every ambient module short exact sequence with finite supported middle
term is an actual short exact sequence of finite supported modules. Its
image under the unchanged inclusion is the original sequence itself. -/
theorem exists_supportedFiniteShortComplex (J : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    (hM : Module.Finite R S.X₂) (hSupp : supportedModuleProperty J S.X₂) (hS : S.ShortExact) :
    ∃ S' : ShortComplex (SupportedFGModuleCat J),
      S'.ShortExact ∧ S'.map (supportedFiniteToModule J) = S := by
  have := hM
  have h₁ : Module.Finite R S.X₁ := Module.Finite.of_injective S.f.hom
    ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  have h₃ : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom
    ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  have hs₁ : supportedModuleProperty J S.X₁ :=
    (Module.support_subset_of_injective S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)).trans hSupp
  have hs₃ : supportedModuleProperty J S.X₃ :=
    (Module.support_subset_of_surjective S.g.hom
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)).trans hSupp
  let M₁ : SupportedFGModuleCat J := ⟨⟨S.X₁, h₁⟩, hs₁⟩
  let M₂ : SupportedFGModuleCat J := ⟨⟨S.X₂, hM⟩, hSupp⟩
  let M₃ : SupportedFGModuleCat J := ⟨⟨S.X₃, h₃⟩, hs₃⟩
  let f : M₁ ⟶ M₂ := ObjectProperty.homMk (ObjectProperty.homMk S.f)
  let g : M₂ ⟶ M₃ := ObjectProperty.homMk (ObjectProperty.homMk S.g)
  let S' : ShortComplex (SupportedFGModuleCat J) := ShortComplex.mk f g (by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact S.zero)
  have hmap : S'.map (supportedFiniteToModule J) = S := rfl
  refine ⟨S', ?_, hmap⟩
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (supportedFiniteToModule J)
  rw [hmap]
  exact hS

/-- The genuine supported-source Hom exactness condition is equivalent to
the ambient finite-supported Hom criterion of IV.2.1. -/
theorem supportedHomFunctorExact_iff (J : Ideal R) (H : ModuleCat.{u} R) :
    SupportedFunctorExact J
      (supportedModuleHomFunctor J H ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ↔
      FiniteSupportedHomExact J H := by
  constructor
  · intro h S hM hSupp hS
    obtain ⟨S', hS', hmap⟩ := exists_supportedFiniteShortComplex J S hM hSupp hS
    have h' := h S' hS'
    change ((S'.map (supportedFiniteToModule J)).op.map (preadditiveYoneda.obj H)).ShortExact at h'
    rw [hmap] at h'
    exact h'
  · intro h S hS
    exact h (S.map (supportedFiniteToModule J))
      (inferInstanceAs (Module.Finite R S.X₂.obj)) S.X₂.property
      (hS.map_of_exact (supportedFiniteToModule J))

variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T]

/-- **SGA 2, IV.2.1:** the original additive left-exact functor is exact if
and only if its actual colimit `colim T(R/Jⁿ)` is injective among all modules. -/
theorem supportedFunctorExact_iff_injective_colimit :
    SupportedFunctorExact J T ↔ Injective (supportedFunctorColimit J T) :=
  (supportedFunctorExact_iff_of_iso J (additiveSupportedFunctorRepresentationIso J T)).trans
    ((supportedHomFunctorExact_iff J (supportedFunctorColimit J T)).trans
      (finiteSupportedHomExact_iff_injective_of_support J (supportedFunctorColimit J T)
        (supportedFunctorColimit_support J T)))

/-- The literal IV.2.1 conclusion with the standard categorical exactness
predicate and the unchanged original functor. -/
theorem supportedFunctor_preservesHomology_iff_injective_colimit :
    T.PreservesHomology ↔ Injective (supportedFunctorColimit J T) :=
  (supportedFunctorExact_iff_preservesHomology J T).symm.trans
    (supportedFunctorExact_iff_injective_colimit J T)

end SGA.SGA2.ExposeIV
