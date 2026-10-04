/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.Foundations.Patching.LaurentSeriesMap
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeXIII.AbhyankarAffineLinePatching

/-!
# XIII.2.13, case A: realizations over `𝔸¹` survive algebraically closed base change

This file proves `AffineLineBaseChangeStatement` (`affineLineBaseChange`), one of the four inputs
of case A of Raynaud's proof of XIII.2.13 (`affineLinePatching_of_statements`): if `k ⊆ K` are
algebraically closed fields and `H ⊆ G` is realized over `𝔸¹_k` with inertia at `∞` in `P`
(`IsRealizedWithInertiaAtInfty`), then it is realized over `𝔸¹_K` with inertia at `∞` in `P`.

* Surjectivity: `π₁(𝔸¹_K) → π₁(𝔸¹_k)` is surjective
  (`AffineLinePGroups.fundamentalGroupMap_polynomial_surjective`) because base change
  `A ↦ K[X] ⊗_{k[X]} A ≅ K ⊗_k A` keeps finite étale `k[X]`-algebras connected
  (`AffineLinePGroups.isConnected_baseChange_polynomial`): `K ⊗_k A` has no nontrivial
  idempotents for `k` algebraically closed
  (`AlgebraicGeometry.CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`). This is
  V.6.9 (`ExposeV.autMap_surjective`).
* Inertia: the square `k[X] → K[X] → K((y))`, `k[X] → k((y)) → K((y))` commutes
  (`PatchingProjectiveLine.mapRingHom_comp_invX`), so base change of finite étale algebras along
  its two sides gives isomorphic functors (`ExposeI.finiteEtaleBaseChangeCompIso`), and every local
  homomorphism `π₁(K((y))) → π₁(𝔸¹_K) → π₁(𝔸¹_k)` factors through a local homomorphism
  `π₁(k((y))) → π₁(𝔸¹_k)` (`exists_autMap_comp_eq_of_iso`).

The local condition in `IsRealizedWithInertiaAtInfty` quantifies over all geometric points of
`k((y))` and all classes of paths; `isRealizedWithInertiaAtInfty_iff` rewrites it as a condition on
`autMap (atInfty k).op E` for all isomorphisms of fibre functors `E`, which is the form used here.
-/

universe u w

open CategoryTheory PreGaloisCategory Polynomial AlgebraicGeometry CommAlgCat

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

open ExposeV

section AutMap

variable {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
  {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}}

/-- Two isomorphisms `e₁ : H ⋙ F ≅ F₁` and `e₂ : H ⋙ F ≅ F₂` give homomorphisms out of `Aut F`
which differ by a change of base point (`autMap` of the identity functor). -/
lemma autMap_eq_autMap_id_autMap (H : C ⥤ D) {F₁ F₂ : C ⥤ FintypeCat.{w}} (e₁ : H ⋙ F ≅ F₁)
    (e₂ : H ⋙ F ≅ F₂) (σ : Aut F) :
    autMap H e₂ σ =
      autMap (𝟭 C) (Functor.leftUnitor F₁ ≪≫ e₁.symm ≪≫ e₂) (autMap H e₁ σ) := by
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [autMap_hom_app]

/-- V.6: a square of functors commuting up to isomorphism, `H₁ ⋙ H₂ ≅ K₁ ⋙ K₂`, gives a square of
fundamental groups which commutes after a suitable choice of the isomorphism of fibre functors on
one side. -/
lemma exists_autMap_comp_eq_of_iso {F'' : E ⥤ FintypeCat.{w}} {G' : D' ⥤ FintypeCat.{w}}
    (H₁ : C ⥤ D) (H₂ : D ⥤ E) (K₁ : C ⥤ D') (K₂ : D' ⥤ E) (ρ : H₁ ⋙ H₂ ≅ K₁ ⋙ K₂)
    (e₁ : H₁ ⋙ F ≅ F') (e₂ : H₂ ⋙ F'' ≅ F) (e₂' : K₂ ⋙ F'' ≅ G') :
    ∃ e₁' : K₁ ⋙ G' ≅ F', ∀ σ, autMap H₁ e₁ (autMap H₂ e₂ σ) = autMap K₁ e₁' (autMap K₂ e₂' σ) := by
  refine ⟨(Functor.isoWhiskerLeft K₁ e₂').symm ≪≫ (Functor.associator K₁ K₂ F'').symm ≪≫
    Functor.isoWhiskerRight ρ.symm F'' ≪≫ Functor.associator H₁ H₂ F'' ≪≫
    Functor.isoWhiskerLeft H₁ e₂ ≪≫ e₁, fun σ ↦ ?_⟩
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp only [autMap_hom_app, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← σ.hom.naturality_assoc, ← F''.map_comp_assoc, Iso.hom_inv_id_app, F''.map_id,
    Category.id_comp]
  rfl

end AutMap

section Connected

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra

/-- Over an algebraically closed field `k`, base change `A ↦ K[X] ⊗_{k[X]} A ≅ K ⊗_k A` along
`k[X] → K[X]` sends connected finite étale `k[X]`-algebras to connected ones (Stacks, Algebra,
Section 10.48: connected `k`-algebras stay connected after any field extension). -/
theorem isConnected_baseChange_polynomial (A : FiniteEtale.{u} k[X])
    (h : IsConnected (Opposite.op A)) :
    IsConnected ((FiniteEtale.baseChange.{u} k[X] K[X]).op.obj (Opposite.op A)) := by
  obtain ⟨hA, hid⟩ := (ExposeV.isConnected_op_iff k[X] A).mp h
  change IsConnected (Opposite.op (FiniteEtale.of K[X] (TensorProduct k[X] K[X] A)))
  rw [ExposeV.isConnected_op_iff]
  let : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq' rfl
  let e := Algebra.IsPushout.cancelBaseChangeAlg k K k[X] K[X] A
  have hK : AlgebraicGeometry.CohomologyAux.TrivialIdempotents K := fun x hx ↦
    IsIdempotentElem.iff_eq_zero_or_one.mp hx
  have hKA := AlgebraicGeometry.CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed
    (k := k) (R := K) (S := A) hK hid
  have : Nontrivial (TensorProduct k K A) :=
    (Algebra.TensorProduct.includeRight_injective (R := k) (A := K) (B := A)
      (algebraMap k K).injective).nontrivial
  refine ⟨e.toEquiv.nontrivial, fun x hx ↦ ?_⟩
  rcases hKA (e x) (hx.map e) with h₀ | h₁
  · exact Or.inl (e.injective (by rw [h₀, map_zero]))
  · exact Or.inr (e.injective (by rw [h₁, map_one]))

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K[X] Ω] [Algebra k[X] Ω]
  [IsScalarTower k[X] K[X] Ω]

/-- V.6.9: for `k` algebraically closed and any extension field `K`, the homomorphism
`π₁(𝔸¹_K, a) → π₁(𝔸¹_k, a)` is surjective. -/
theorem fundamentalGroupMap_polynomial_surjective :
    Function.Surjective (fundamentalGroupMap k[X] K[X] Ω) :=
  ExposeV.autMap_surjective _ _ fun X hX ↦ isConnected_baseChange_polynomial k K X.unop hX

end Connected

end SGA.SGA1.ExposeXIII.AffineLinePGroups

namespace SGA.SGA1.ExposeXIII

section Reformulation

open AffineLinePGroups

variable (k : Type u) [Field k]

/-- Base change of finite étale algebras to the punctured disc at `∞`, `A ↦ k((y)) ⊗_{k[X]} A`,
along `x ↦ y⁻¹` (`PatchingProjectiveLine.invX`). -/
noncomputable abbrev atInfty : FiniteEtale.{u} k[X] ⥤ FiniteEtale.{u} (LaurentSeries k) :=
  letI := (PatchingProjectiveLine.invX k).toAlgebra
  FiniteEtale.baseChange.{u} k[X] (LaurentSeries k)

variable {k} {G : Type u} [Group G] [TopologicalSpace G]

/-- The local condition at `∞` of `IsRealizedWithInertiaAtInfty`, for all isomorphisms of fibre
functors `E` from the base change to `k((y))` (any geometric point of `k((y))`, any class of
paths): the image of `autMap (atInfty k).op E` under `φ` is conjugate by an element of `H` into
`P`. -/
def InertiaAtInftyLE {Ω : Type u} [Field Ω] [Algebra k[X] Ω]
    (φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) G) (H P : Subgroup G) : Prop :=
  ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω'] [Algebra (LaurentSeries k) Ω']
    (E : (atInfty k).op ⋙ ExposeV.fiberFunctor (LaurentSeries k) Ω' ≅
      ExposeV.fiberFunctor k[X] Ω),
    ∃ g ∈ H, ∀ σ, g * φ (ExposeV.autMap (atInfty k).op E σ) * g⁻¹ ∈ P

/-- `IsRealizedWithInertiaAtInfty` in terms of `InertiaAtInftyLE`: the local homomorphisms
`π₁(k((y)), Ω') → π₁(𝔸¹_k, Ω)` composed with classes of paths are exactly the homomorphisms
`autMap (atInfty k).op E` for the isomorphisms of fibre functors `E`. -/
theorem isRealizedWithInertiaAtInfty_iff (H P : Subgroup G) :
    IsRealizedWithInertiaAtInfty k H P ↔
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (_ : Algebra k[X] Ω)
        (φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) G),
        φ.toMonoidHom.range = H ∧ InertiaAtInftyLE φ H P := by
  constructor
  · rintro ⟨Ω, _, _, _, φ, hφ, hloc⟩
    refine ⟨Ω, inferInstance, inferInstance, inferInstance, φ, hφ, fun Ω' _ _ _ E ↦ ?_⟩
    let : Algebra k[X] Ω' :=
      ((algebraMap (LaurentSeries k) Ω').comp (PatchingProjectiveLine.invX k)).toAlgebra
    let := (PatchingProjectiveLine.invX k).toAlgebra
    have : IsScalarTower k[X] (LaurentSeries k) Ω' := IsScalarTower.of_algebraMap_eq' rfl
    let e₀ := FiniteEtale.fiberIsoBaseChangeFiber.{u} k[X] Ω' (LaurentSeries k)
    obtain ⟨g, hg, hg'⟩ := hloc Ω' rfl (Functor.leftUnitor _ ≪≫ e₀.symm.symm ≪≫ E)
    have key : ∀ σ, ExposeV.autMap (atInfty k).op E σ =
        ExposeV.autMap (𝟭 _) (Functor.leftUnitor _ ≪≫ e₀.symm.symm ≪≫ E)
          (fundamentalGroupMapOfRingHom (PatchingProjectiveLine.invX k) Ω' rfl σ) :=
      fun σ ↦ autMap_eq_autMap_id_autMap _ e₀.symm E σ
    exact ⟨g, hg, fun σ ↦ (key σ) ▸ hg' σ⟩
  · rintro ⟨Ω, _, _, _, φ, hφ, hloc⟩
    refine ⟨Ω, inferInstance, inferInstance, inferInstance, φ, hφ, fun Ω' _ _ _ _ h γ ↦ ?_⟩
    let := (PatchingProjectiveLine.invX k).toAlgebra
    have : IsScalarTower k[X] (LaurentSeries k) Ω' := IsScalarTower.of_algebraMap_eq' h
    let e₀ := FiniteEtale.fiberIsoBaseChangeFiber.{u} k[X] Ω' (LaurentSeries k)
    let E := e₀.symm ≪≫ (Functor.leftUnitor _).symm ≪≫ γ
    obtain ⟨g, hg, hg'⟩ := hloc Ω' E
    have hγ : Functor.leftUnitor _ ≪≫ e₀.symm.symm ≪≫ E = γ := by
      apply Iso.ext
      refine NatTrans.ext (funext fun X ↦ ?_)
      simp [E]
    have key : ∀ σ, ExposeV.autMap (atInfty k).op E σ =
        ExposeV.autMap (𝟭 _) γ
          (fundamentalGroupMapOfRingHom (PatchingProjectiveLine.invX k) Ω' h σ) :=
      fun σ ↦ (autMap_eq_autMap_id_autMap _ e₀.symm E σ).trans (by rw [hγ]; rfl)
    exact ⟨g, hg, fun σ ↦ (key σ) ▸ hg' σ⟩

end Reformulation

section BaseChange

open AffineLinePGroups

attribute [local instance] Polynomial.algebra

/-- **Base change of realizations over `𝔸¹`** (`AffineLineBaseChangeStatement`): for algebraically
closed fields `k ⊆ K`, a subgroup realized over `𝔸¹_k` with inertia at `∞` in `P` is realized over
`𝔸¹_K` with inertia at `∞` in `P`. -/
theorem affineLineBaseChange : AffineLineBaseChangeStatement.{u} := by
  intro k K _ _ _ _ _ G _ _ _ _ H P hk
  rw [isRealizedWithInertiaAtInfty_iff] at hk ⊢
  obtain ⟨Ω, _, _, _, φ, hφ, hloc⟩ := hk
  -- the geometric point of `𝔸¹_K`
  let ΩK := AlgebraicClosure K
  let : Algebra K[X] ΩK := (Polynomial.aeval (0 : ΩK)).toRingHom.toAlgebra
  let : Algebra k[X] ΩK := ((algebraMap K[X] ΩK).comp (algebraMap k[X] K[X])).toAlgebra
  have : IsScalarTower k[X] K[X] ΩK := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨γ₀⟩ := ExposeV.nonempty_iso_of_fiberFunctor (ExposeV.fiberFunctor k[X] ΩK)
    (ExposeV.fiberFunctor k[X] Ω)
  let E₁ : (FiniteEtale.baseChange.{u} k[X] K[X]).op ⋙ ExposeV.fiberFunctor K[X] ΩK ≅
      ExposeV.fiberFunctor k[X] Ω :=
    (FiniteEtale.fiberIsoBaseChangeFiber.{u} k[X] ΩK K[X]).symm ≪≫ γ₀
  let φK : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor K[X] ΩK)) G :=
    φ.comp ⟨ExposeV.autMap _ E₁, ExposeV.continuous_autMap _ _⟩
  have hsurj : Function.Surjective (ExposeV.autMap _ E₁) :=
    ExposeV.autMap_surjective _ _ fun X hX ↦ isConnected_baseChange_polynomial k K X.unop hX
  refine ⟨ΩK, inferInstance, inferInstance, inferInstance, φK, ?_, fun Ω' _ _ _ EK ↦ ?_⟩
  · rw [← hφ]
    ext g
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, rfl⟩ := hsurj τ
      exact ⟨σ, rfl⟩
  -- the square `k[X] → K[X] → K((y))`, `k[X] → k((y)) → K((y))`
  let : Algebra (LaurentSeries k) (LaurentSeries K) :=
    (HahnSeries.mapRingHom ℤ (algebraMap k K)).toAlgebra
  let : Algebra (LaurentSeries k) Ω' :=
    ((algebraMap (LaurentSeries K) Ω').comp
      (algebraMap (LaurentSeries k) (LaurentSeries K))).toAlgebra
  have : IsScalarTower (LaurentSeries k) (LaurentSeries K) Ω' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ρ : (atInfty k ⋙ FiniteEtale.baseChange.{u} (LaurentSeries k) (LaurentSeries K)) ≅
      (FiniteEtale.baseChange.{u} k[X] K[X] ⋙ atInfty K) := by
    letI : Algebra k[X] (LaurentSeries K) :=
      ((PatchingProjectiveLine.invX K).comp (algebraMap k[X] K[X])).toAlgebra
    letI := (PatchingProjectiveLine.invX K).toAlgebra
    letI := (PatchingProjectiveLine.invX k).toAlgebra
    haveI : IsScalarTower k[X] K[X] (LaurentSeries K) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower k[X] (LaurentSeries k) (LaurentSeries K) :=
      IsScalarTower.of_algebraMap_eq' (PatchingProjectiveLine.mapRingHom_comp_invX
        (algebraMap k K)).symm
    exact ExposeI.finiteEtaleBaseChangeCompIso (A := k[X]) (LaurentSeries k) (LaurentSeries K) ≪≫
      (ExposeI.finiteEtaleBaseChangeCompIso (A := k[X]) K[X] (LaurentSeries K)).symm
  obtain ⟨E₄, hE₄⟩ := exists_autMap_comp_eq_of_iso
    (FiniteEtale.baseChange.{u} k[X] K[X]).op (atInfty K).op (atInfty k).op
    (FiniteEtale.baseChange.{u} (LaurentSeries k) (LaurentSeries K)).op
    (NatIso.op ρ) E₁ EK (FiniteEtale.fiberIsoBaseChangeFiber.{u} (LaurentSeries k) Ω'
      (LaurentSeries K)).symm
  obtain ⟨g, hg, hg'⟩ := hloc Ω' E₄
  refine ⟨g, hg, fun σ ↦ ?_⟩
  change g * φ (ExposeV.autMap _ E₁ (ExposeV.autMap _ EK σ)) * g⁻¹ ∈ P
  rw [hE₄]
  exact hg' _

end BaseChange

end SGA.SGA1.ExposeXIII
