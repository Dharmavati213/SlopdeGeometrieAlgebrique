/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.FiniteFreeEvaluation
import SGA.SGA2.ExposeII.InjectiveHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Representation of left-exact contravariant functors on finite modules

SGA 2, IV.1.1: the canonical evaluation map is an isomorphism precisely
when the original additive contravariant functor is left exact.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

instance (H : ModuleCat.{u} R) : (finiteModuleHomFunctor H).Additive := by
  unfold finiteModuleHomFunctor
  infer_instance

instance (H : ModuleCat.{u} R) : PreservesFiniteLimits (finiteModuleHomFunctor H) := by
  have := preservesFiniteLimits_op (forget₂ (FGModuleCat R) (ModuleCat R))
  unfold finiteModuleHomFunctor
  exact comp_preservesFiniteLimits _ _

variable (T : (FGModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R) [T.Additive] [T.Linear R]

/-- Evaluation is already injective when the functor is left exact, using a
finite free cover of the coefficient module. -/
theorem finiteModuleEvaluation_injective [PreservesFiniteLimits T] (M : FGModuleCat.{u} R) :
    Function.Injective (finiteModuleEvaluation T M) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
  let q' : FGModuleCat.of R (Fin n → R) ⟶ M := FGModuleCat.ofHom q
  have hq' : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map q') :=
    (ModuleCat.epi_iff_surjective _).mpr hq
  have : Epi q' := (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map hq'
  intro t s h
  apply (ModuleCat.mono_iff_injective (T.map q'.op)).mp inferInstance
  apply finiteModuleEvaluation_free_injective T n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  calc
    _ = finiteModuleEvaluation T M t (q x) := finiteModuleEvaluation_naturality T q' t x
    _ = finiteModuleEvaluation T M s (q x) := by rw [h]
    _ = _ := (finiteModuleEvaluation_naturality T q' s x).symm

/-- Left exactness makes evaluation surjective: lift on a finite free cover,
then descend across its actual kernel, which is finite over a noetherian ring. -/
theorem finiteModuleEvaluation_surjective [IsNoetherianRing R] [PreservesFiniteLimits T]
    (M : FGModuleCat.{u} R) : Function.Surjective (finiteModuleEvaluation T M) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
  let P := FGModuleCat.of R (Fin n → R)
  let K := FGModuleCat.of R q.ker
  let q' : P ⟶ M := FGModuleCat.ofHom q
  let k : K ⟶ P := FGModuleCat.ofHom q.ker.subtype
  let S : ShortComplex (FGModuleCat R) := ShortComplex.mk k q' (by
    apply FGModuleCat.hom_ext
    ext x
    exact x.property)
  have hS : S.Exact := by
    apply (forget₂ (FGModuleCat R) (ModuleCat R)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have hq' : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map q') :=
    (ModuleCat.epi_iff_surjective _).mpr hq
  have : Epi q' := (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map hq'
  have hST : (S.op.map T).Exact :=
    hS.op.map_of_mono_of_preservesKernel T
      (show Mono q'.op from inferInstance) inferInstance
  intro h
  obtain ⟨t, ht⟩ := finiteModuleEvaluation_free_surjective T n (q'.hom ≫ h)
  have hkt : T.map k.op t = 0 := by
    apply finiteModuleEvaluation_injective T K
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    calc
      _ = finiteModuleEvaluation T P t (k.hom x) :=
        finiteModuleEvaluation_naturality T k t x
      _ = (q'.hom ≫ h) (k.hom x) := by rw [ht]
      _ = 0 := by change h.hom (q x.val) = 0; rw [x.property]; exact h.hom.map_zero
      _ = _ := by simp
  have hlift : ∀ t : T.obj (op P), T.map k.op t = 0 →
      ∃ s : T.obj (op M), T.map q'.op s = t :=
    (ShortComplex.moduleCat_exact_iff _).mp hST
  obtain ⟨s, hs⟩ := hlift t hkt
  refine ⟨s, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hq x
  calc
    _ = finiteModuleEvaluation T P (T.map q'.op s) y :=
      (finiteModuleEvaluation_naturality T q' s y).symm
    _ = finiteModuleEvaluation T P t y := by rw [hs]
    _ = _ := congrArg (fun f : P.obj ⟶ T.obj (op (FGModuleCat.of R R)) ↦ f y) ht

/- The isomorphism below is built from the canonical map, not merely from
an abstract existence statement for a representing module. -/

instance [IsNoetherianRing R] [PreservesFiniteLimits T] :
    IsIso (finiteModuleEvaluationNatTrans T) := by
  have (M : (FGModuleCat.{u} R)ᵒᵖ) : IsIso ((finiteModuleEvaluationNatTrans T).app M) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨finiteModuleEvaluation_injective T M.unop,
      finiteModuleEvaluation_surjective T M.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- IV.1.1 for linear module-valued functors: the specified canonical map is
invertible if and only if the functor is left exact. -/
theorem finiteModuleEvaluation_isIso_iff [IsNoetherianRing R] :
    IsIso (finiteModuleEvaluationNatTrans T) ↔ PreservesFiniteLimits T := by
  constructor
  · intro h
    exact preservesFiniteLimits_of_natIso (asIso (finiteModuleEvaluationNatTrans T)).symm
  · intro h
    infer_instance

/-- The natural representation by the functor's actual value on the ring. -/
def finiteModuleRepresentationIso [IsNoetherianRing R] [PreservesFiniteLimits T] :
    T ≅ finiteModuleHomFunctor (T.obj (op (FGModuleCat.of R R))) :=
  asIso (finiteModuleEvaluationNatTrans T)

section AbelianGroupValued

variable (A : (FGModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u}) [A.Additive]

/-- The canonical module lift preserves left exactness of the original
abelian-group-valued functor. -/
instance [PreservesFiniteLimits A] :
    PreservesFiniteLimits (additiveFunctorModuleLift (R := R) A) := by
  have : PreservesFiniteLimits
      (additiveFunctorModuleLift (R := R) A ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    preservesFiniteLimits_of_natIso (additiveFunctorModuleLiftForgetIso (R := R) A).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- The source's canonical `φ_A` for an arbitrary additive functor to abelian
groups, without assuming a pre-existing scalar action or linearity. -/
def additiveFiniteModuleEvaluationNatTrans :
    A ⟶ finiteModuleHomFunctor
      ((additiveFunctorModuleLift (R := R) A).obj (op (FGModuleCat.of R R))) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat :=
  (additiveFunctorModuleLiftForgetIso (R := R) A).inv ≫
    whiskerRight (finiteModuleEvaluationNatTrans (additiveFunctorModuleLift (R := R) A))
      (forget₂ (ModuleCat R) AddCommGrpCat)

/-- SGA 2, IV.1.1, with exactly the original additive abelian-group-valued
functor: canonical evaluation is an isomorphism precisely for left-exact functors. -/
theorem additiveFiniteModuleEvaluation_isIso_iff [IsNoetherianRing R] :
    IsIso (additiveFiniteModuleEvaluationNatTrans A) ↔ PreservesFiniteLimits A := by
  constructor
  · intro h
    have := comp_preservesFiniteLimits
      (finiteModuleHomFunctor
        ((additiveFunctorModuleLift (R := R) A).obj (op (FGModuleCat.of R R))))
      (forget₂ (ModuleCat R) AddCommGrpCat)
    exact preservesFiniteLimits_of_natIso (asIso (additiveFiniteModuleEvaluationNatTrans A)).symm
  · intro h
    unfold additiveFiniteModuleEvaluationNatTrans
    infer_instance

/-- The actual natural representation of an additive left-exact functor. -/
def additiveFiniteModuleRepresentationIso [IsNoetherianRing R] [PreservesFiniteLimits A] :
    A ≅ finiteModuleHomFunctor
      ((additiveFunctorModuleLift (R := R) A).obj (op (FGModuleCat.of R R))) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat := by
  letI := (additiveFiniteModuleEvaluation_isIso_iff A).mpr inferInstance
  exact asIso (additiveFiniteModuleEvaluationNatTrans A)

end AbelianGroupValued

end SGA.SGA2.ExposeIV
