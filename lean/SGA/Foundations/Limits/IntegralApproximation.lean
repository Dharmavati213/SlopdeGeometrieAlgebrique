/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Étale algebras over an integral algebra come from a finite subalgebra

Let `A ⟶ B` be integral. Finitely many étale `B`-algebras `D i` are base changes of étale
algebras over a finite `A`-subalgebra `B'` of `B`
(`CommRingCat.exists_finite_etale_isPushout_of_isIntegral`; EGA IV 8.8.2, 17.7.8, Stacks 07RP
for the colimit `B = colim B'` of the finite subalgebras). Geometrically: for `f : X ⟶ Y` integral
with `Y` affine, finitely many affine étale `X`-schemes `U i` are base changes of étale schemes
over some `X'` finite over `Y`, through which `f` factors by a surjection `X ⟶ X'`
(`AlgebraicGeometry.Scheme.exists_isFinite_etale_isPullback_of_isIntegralHom`).
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

set_option backward.isDefEq.respectTransparency false in
/-- An étale `B`-algebra `D` is defined over a finitely generated subring of `B`: there is a
finite set `s ⊆ B` such that `D` is the base change of an étale algebra over every subring `B'`
of `B` containing `s`. -/
theorem exists_etale_isPushout_of_subring {B D : CommRingCat.{u}} (φ : B ⟶ D) (hφ : φ.hom.Etale) :
    ∃ s : Finset B, ∀ (B' : Subring B), (s : Set B) ⊆ B' →
      ∃ (D' : CommRingCat.{u}) (φ' : of B' ⟶ D') (ψ : D' ⟶ D),
        φ'.hom.Etale ∧ IsPushout (ofHom B'.subtype) φ' φ ψ := by
  algebraize [φ.hom]
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ B D
  obtain ⟨s, hs⟩ := hA₀
  refine ⟨s, fun B' hsB' ↦ ?_⟩
  have hle (r : B) (hr : r ∈ A₀) : r ∈ B' := by
    rw [← hs] at hr
    exact mem_subalgebraOfSubring.mp (Algebra.adjoin_le (S := subalgebraOfSubring B')
      (fun x hx ↦ mem_subalgebraOfSubring.mpr (hsB' hx)) hr)
  let g : A₀ →+* B' :=
    { toFun r := ⟨r, hle r r.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  let _ : Algebra A₀ B' := g.toAlgebra
  have hι (r : A₀) : (algebraMap A₀ B' r : B) = algebraMap A₀ B r := rfl
  let ιB' : B' →ₐ[A₀] B := { B'.subtype with commutes' := hι }
  let m : B' ⊗[A₀] B₀ →ₐ[A₀] B ⊗[A₀] B₀ := Algebra.TensorProduct.map ιB' (AlgHom.id A₀ B₀)
  refine ⟨.of (B' ⊗[A₀] B₀), ofHom (algebraMap B' (B' ⊗[A₀] B₀)),
    ofHom (e.symm.toRingHom.comp m.toRingHom), RingHom.etale_algebraMap.mpr inferInstance, ?_⟩
  have t := CommRingCat.isPushout_tensorProduct A₀ B' B₀
  have s := CommRingCat.isPushout_tensorProduct A₀ B B₀
  have s' : IsPushout (ofHom (algebraMap A₀ B') ≫ ofHom B'.subtype) (ofHom (algebraMap A₀ B₀))
      (ofHom (S := B ⊗[A₀] B₀) Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := B' ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom) := by
    have e₁ : ofHom (algebraMap A₀ B') ≫ ofHom B'.subtype = ofHom (algebraMap A₀ B) := by
      ext r
      exact hι r
    have e₂ : ofHom (S := B' ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom =
          ofHom (S := B ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom := by
      ext b
      simp [m]
    rw [e₁, e₂]
    exact s
  have r := IsPushout.of_left s' (by ext x; simp [m, ιB']) t
  refine r.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso
    (by simp) (by simp; rfl) ?_ (by simp)
  ext x
  have hx : (x ⊗ₜ[A₀] (1 : B₀) : B ⊗[A₀] B₀) = algebraMap B (B ⊗[A₀] B₀) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  simp only [Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
    hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  change e.symm (x ⊗ₜ[A₀] (1 : B₀)) = φ.hom x
  rw [hx, AlgEquiv.commutes]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2, 17.7.8 for integral algebras: let `α : A ⟶ B` be integral and `φ i : B ⟶ D i`
finitely many étale maps. There is a finite `A`-subalgebra `B'` of `B` (`α = α' ≫ β` with `α'`
finite and `β` injective) such that every `D i` is the base change `B ⊗_{B'} D' i` of an étale
`B'`-algebra `D' i`. -/
theorem exists_finite_etale_isPushout_of_isIntegral {A B : CommRingCat.{u}} (α : A ⟶ B)
    (hα : α.hom.IsIntegral) {ι : Type*} [Finite ι] {D : ι → CommRingCat.{u}} (φ : ∀ i, B ⟶ D i)
    (hφ : ∀ i, (φ i).hom.Etale) :
    ∃ (B' : CommRingCat.{u}) (α' : A ⟶ B') (β : B' ⟶ B) (D' : ι → CommRingCat.{u})
      (φ' : ∀ i, B' ⟶ D' i) (ψ : ∀ i, D' i ⟶ D i),
      α' ≫ β = α ∧ α'.hom.Finite ∧ Function.Injective β.hom ∧
        ∀ i, (φ' i).hom.Etale ∧ IsPushout β (φ' i) (φ i) (ψ i) := by
  classical
  have := Fintype.ofFinite ι
  algebraize [α.hom]
  choose s hs using fun i ↦ exists_etale_isPushout_of_subring (φ i) (hφ i)
  let S : Finset B := Finset.univ.biUnion s
  let B'' : Subalgebra A B := Algebra.adjoin A (S : Set B)
  have hfin : Module.Finite A B'' := by
    change Module.Finite A (Subalgebra.toSubmodule B'')
    exact Module.Finite.iff_fg.mpr
      (fg_adjoin_of_finite S.finite_toSet fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hsub (i : ι) : (s i : Set B) ⊆ B''.toSubring := fun x hx ↦
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))
  choose D' φ' ψ hφ' hpush using fun i ↦ hs i B''.toSubring (hsub i)
  refine ⟨.of B''.toSubring, ofHom (algebraMap A B''), ofHom B''.toSubring.subtype, D', φ', ψ,
    ?_, ?_, Subtype.val_injective, fun i ↦ ⟨hφ' i, hpush i⟩⟩
  · ext a
    rfl
  · exact RingHom.finite_algebraMap.mpr hfin

end CommRingCat

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 for integral morphisms: let `f : X ⟶ Y` be integral with `Y` affine and
`u i : U i ⟶ X` finitely many étale morphisms from affine schemes. Then `f` factors as a surjection
`π : X ⟶ X'` followed by a finite `f' : X' ⟶ Y`, and every `U i` is the base change along `π` of
an étale `X'`-scheme `W i`. -/
theorem Scheme.exists_isFinite_etale_isPullback_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [IsAffine Y] {ι : Type*} [Finite ι] {U : ι → Scheme.{u}}
    [∀ i, IsAffine (U i)] (u : ∀ i, U i ⟶ X) [∀ i, Etale (u i)] :
    ∃ (X' : Scheme.{u}) (π : X ⟶ X') (f' : X' ⟶ Y) (W : ι → Scheme.{u}) (w : ∀ i, W i ⟶ X')
      (e : ∀ i, U i ⟶ W i), π ≫ f' = f ∧ IsFinite f' ∧ Function.Surjective π ∧
        (∀ i, Etale (w i)) ∧ ∀ i, IsPullback (e i) (u i) (w i) π := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hα : f.appTop.hom.IsIntegral :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp inferInstance).2
  have hφ (i : ι) : (u i).appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  obtain ⟨B', α', β, D', φ', ψ, hαβ, hα', hβ, hD'⟩ :=
    CommRingCat.exists_finite_etale_isPushout_of_isIntegral f.appTop hα (fun i ↦ (u i).appTop) hφ
  have hβint : β.hom.IsIntegral := by
    have : (β.hom.comp α'.hom).IsIntegral := by
      rw [← CommRingCat.hom_comp, hαβ]
      exact hα
    exact RingHom.IsIntegral.tower_top _ _ this
  refine ⟨Spec B', X.isoSpec.hom ≫ Spec.map β, Spec.map α' ≫ Y.isoSpec.inv, fun i ↦ Spec (D' i),
    fun i ↦ Spec.map (φ' i), fun i ↦ (U i).isoSpec.hom ≫ Spec.map (ψ i), ?_, ?_, ?_,
    fun i ↦ HasRingHomProperty.Spec_iff.mpr (hD' i).1, fun i ↦ ?_⟩
  · rw [Category.assoc, ← Category.assoc (Spec.map β), ← Spec.map_comp, hαβ,
      Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  · have : IsFinite (Spec.map α') := (IsFinite.SpecMap_iff _).mpr hα'
    infer_instance
  · intro x'
    obtain ⟨y, hy⟩ := RingHom.IsIntegral.comap_surjective hβint hβ x'
    refine ⟨X.isoSpec.inv y, ?_⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply X.isoSpec.inv, Iso.inv_hom_id]
    exact hy
  · have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ (hD' i).2
    refine hSpec.flip.of_iso (U i).isoSpec.symm (Iso.refl _) X.isoSpec.symm (Iso.refl _)
      ?_ ?_ (by simp) (by simp)
    · simp
    · simp only [Iso.symm_hom]
      exact Scheme.isoSpec_inv_naturality (u i)

end AlgebraicGeometry
