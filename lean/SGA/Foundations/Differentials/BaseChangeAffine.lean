/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.Tilde
import SGA.Foundations.Differentials.Restrict
import SGA.Foundations.Differentials.AffineOpens
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Derivations and base change: the affine case

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of schemes, `V ⊆ Y`, `U ⊆ f⁻¹ V`, `V' ⊆ g⁻¹ V`
affine opens, `A = Γ(Y, V)`, `B = Γ(X, U)`, `A' = Γ(Y', V')` and `C = B ⊗_A A'`. For the
morphisms `q : Spec C ⟶ X` and `p : Spec C ⟶ Y'` induced by `B → C` and `A' → C`, and an
`𝒪_{Spec C}`-module `N`, composing with `q^♯` is a bijection from the derivations of
`𝒪_{Spec C}` into `N` relative to `p` onto the derivations of `𝒪_X` into `q_* N` relative to `f`
(`AlgebraicGeometry.BaseChangeChart.bijective_pushforward`). This is the local step of the base
change theorem for `Ω` (EGA IV 16.4.5; Stacks Project, Tag 01V0).

We also prove that on an affine open a derivation is determined by its values on the sections
over it (`Scheme.Modules.Derivation.app_eq_of_isAffineOpen`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace TensorProduct

noncomputable section

section Algebra

variable {A B A' N : Type*} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  [AddCommGroup N] [Module (B ⊗[A] A') N]

/-- An additive map `δ : B → N` into a `B ⊗[A] A'`-module satisfying the Leibniz rule and
vanishing on `A` extends to the additive map `b ⊗ a' ↦ (1 ⊗ a') • δ b` of `B ⊗[A] A'`. -/
def TensorProduct.derivationExtend (δ : B →+ N)
    (hδ : ∀ x y, δ (x * y) = (x ⊗ₜ[A] (1 : A')) • δ y + (y ⊗ₜ[A] (1 : A')) • δ x)
    (hδA : ∀ a, δ (algebraMap A B a) = 0) : B ⊗[A] A' →+ N :=
  liftAddHom
    { toFun b :=
        { toFun a' := ((1 : B) ⊗ₜ[A] a') • δ b
          map_zero' := by simp
          map_add' a₁ a₂ := by rw [tmul_add, add_smul] }
      map_zero' := by ext; simp
      map_add' b₁ b₂ := by ext; simp }
    fun a b a' ↦ by
      change ((1 : B) ⊗ₜ[A] a') • δ (a • b) = ((1 : B) ⊗ₜ[A] (a • a')) • δ b
      have e : (1 : B) ⊗ₜ[A] a' * (algebraMap A B a ⊗ₜ[A] (1 : A')) =
          (1 : B) ⊗ₜ[A] (a • a') := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one,
          smul_tmul]
      rw [show a • b = algebraMap A B a * b from _root_.Algebra.smul_def a b, hδ, hδA, smul_zero,
        add_zero, smul_smul, e]

variable (δ : B →+ N)
  (hδ : ∀ x y, δ (x * y) = (x ⊗ₜ[A] (1 : A')) • δ y + (y ⊗ₜ[A] (1 : A')) • δ x)
  (hδA : ∀ a, δ (algebraMap A B a) = 0)

@[simp]
lemma TensorProduct.derivationExtend_tmul (b : B) (a' : A') :
    derivationExtend δ hδ hδA (b ⊗ₜ a') = ((1 : B) ⊗ₜ[A] a') • δ b :=
  rfl

lemma TensorProduct.derivationExtend_mul (x y : B ⊗[A] A') :
    derivationExtend δ hδ hδA (x * y) =
      x • derivationExtend δ hδ hδA y + y • derivationExtend δ hδ hδA x := by
  induction x with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add, smul_add, add_smul]
    abel
  | tmul b a' =>
  induction y with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    rw [mul_add, map_add, h₁, h₂, map_add, smul_add, add_smul]
    abel
  | tmul b' a'' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, derivationExtend_tmul, derivationExtend_tmul,
      derivationExtend_tmul, hδ, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_mul, mul_one, mul_comm a' a'']

end Algebra

namespace AlgebraicGeometry

namespace Scheme.Modules.Derivation

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {M : X.Modules}

/-- On an affine open `U`, a derivation is determined by its values on `Γ(X, U)`. -/
theorem app_eq_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {D D' : M.Derivation f}
    (h : ∀ a : Γ(X, U), D.app U a = D'.app U a) {W : X.Opens} (hW : W ≤ U) (a : Γ(X, W)) :
    D.app W a = D'.app W a := by
  apply M.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨r, hrW, hxr⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hW hx)
  refine ⟨X.basicOpen r, hrW, hxr, ?_⟩
  rw [← app_map, ← app_map]
  have := hU.isLocalization_basicOpen r
  have : D.app (X.basicOpen r) = D'.app (X.basicOpen r) :=
    AddMonoidHom.eq_of_leibniz_of_isLocalization (Submonoid.powers r) (RingHom.id _)
      (D.app_mul _) (D'.app_mul _) fun b ↦ by
        change D.app _ (X.presheaf.map (homOfLE _).op b) =
          D'.app _ (X.presheaf.map (homOfLE _).op b)
        rw [app_map, app_map, h]
  rw [this]

/-- A derivation with values in the direct image of a module along a morphism `q` which factors
through an affine open `U` is determined by its values on `Γ(X, U)`. -/
theorem ext_of_pushforward {S : Scheme.{u}} (q : S ⟶ X) {N : S.Modules} {U : X.Opens}
    (hU : IsAffineOpen U) (hq : q ⁻¹ᵁ U = ⊤)
    {D D' : ((Scheme.Modules.pushforward q).obj N).Derivation f}
    (h : ∀ a : Γ(X, U), D.app U a = D'.app U a) : D = D' := by
  ext T a
  have e : q ⁻¹ᵁ (T ⊓ U) = q ⁻¹ᵁ T := by rw [Scheme.Hom.preimage_inf, hq, inf_top_eq]
  apply presheaf_map_injective_of_eq N (homOfLE (q.preimage_mono inf_le_left)) e
  change ((Scheme.Modules.pushforward q).obj N).presheaf.map (homOfLE inf_le_left).op
      (D.app T a) = ((Scheme.Modules.pushforward q).obj N).presheaf.map
        (homOfLE inf_le_left).op (D'.app T a)
  rw [← app_map, ← app_map]
  exact app_eq_of_isAffineOpen hU h inf_le_right _

end Scheme.Modules.Derivation

namespace BaseChangeChart

section

variable {Z : Scheme.{u}} {W : Z.Opens} (hW : IsAffineOpen W) {C : CommRingCat.{u}}
  (χ : Γ(Z, W) ⟶ C)

lemma preimage_eq_top : (Spec.map χ ≫ hW.fromSpec) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage, hW.fromSpec_preimage_self, Scheme.Hom.preimage_top]

set_option backward.isDefEq.respectTransparency false in
lemma appLE_eq : (Spec.map χ ≫ hW.fromSpec).appLE W ⊤ (preimage_eq_top hW χ).ge =
    χ ≫ (Scheme.ΓSpecIso C).inv := by
  rw [Scheme.Hom.comp_appLE, hW.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE,
    Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The sections of `𝒪_Z` over `W` pulled back to `Spec C` along `Spec C ⟶ Spec Γ(Z, W) ⟶ Z`,
restricted to `⊤`, are the images of `χ`. -/
lemma map_app_eq (b : Γ(Z, W)) :
    (Spec C).presheaf.map (homOfLE (preimage_eq_top hW χ).ge).op
      ((Spec.map χ ≫ hW.fromSpec).app W b) = (Scheme.ΓSpecIso C).inv (χ b) :=
  congr($(appLE_eq hW χ) b)

end

section

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) {U : X.Opens} {V : Y.Opens}
  {V' : Y'.Opens} (hU : IsAffineOpen U) (hV' : IsAffineOpen V') (eU : U ≤ f ⁻¹ᵁ V)
  {C : CommRingCat.{u}} (inl : Γ(X, U) ⟶ C) (inr : Γ(Y', V') ⟶ C)

open Scheme.Modules

/-- The equalizer of two derivations of `𝒪_{Spec C}`, on global sections, as a subring of `C`. -/
def eqSubring {N : (Spec C).Modules} {p : Spec C ⟶ Y'} (D₁ D₂ : N.Derivation p) : Subring C where
  carrier := {c | D₁.app ⊤ ((Scheme.ΓSpecIso C).inv c) = D₂.app ⊤ ((Scheme.ΓSpecIso C).inv c)}
  mul_mem' {a b} (ha : D₁.app ⊤ _ = D₂.app ⊤ _) (hb : D₁.app ⊤ _ = D₂.app ⊤ _) := by
    change D₁.app ⊤ _ = D₂.app ⊤ _
    rw [map_mul, Derivation.app_mul, Derivation.app_mul, ha, hb]
  one_mem' := by
    change D₁.app ⊤ _ = D₂.app ⊤ _
    rw [map_one, Derivation.app_one, Derivation.app_one]
  add_mem' {a b} (ha : D₁.app ⊤ _ = D₂.app ⊤ _) (hb : D₁.app ⊤ _ = D₂.app ⊤ _) := by
    change D₁.app ⊤ _ = D₂.app ⊤ _
    rw [map_add, map_add, map_add, ha, hb]
  zero_mem' := by
    change D₁.app ⊤ _ = D₂.app ⊤ _
    rw [map_zero, map_zero, map_zero]
  neg_mem' {a} (ha : D₁.app ⊤ _ = D₂.app ⊤ _) := by
    change D₁.app ⊤ _ = D₂.app ⊤ _
    rw [map_neg, map_neg, map_neg, ha]

/-- The local step of the base change theorem: for `q : Spec C ⟶ X`, `p : Spec C ⟶ Y'` induced by
`B = Γ(X, U) → C` and `A' = Γ(Y', V') → C`, where `C` is generated by `B` and `A'` and derivations
of `B` over `Γ(Y, V)` extend to derivations of `C` over `A'` (e.g. `C = B ⊗_A A'`), composition
with `q^♯` is a bijection `Der_p(𝒪_{Spec C}, N) ≃ Der_f(𝒪_X, q_* N)`. -/
theorem bijective_pushforward
    (hgen : ∀ c : C, c ∈ Subring.closure (Set.range inl ∪ Set.range inr))
    (hext : ∀ (N : Type u) [AddCommGroup N] [Module C N] (δ : Γ(X, U) →+ N),
      (∀ x y, δ (x * y) = inl x • δ y + inl y • δ x) → (∀ a, δ (f.appLE V U eU a) = 0) →
      ∃ δ' : C →+ N, (∀ x y, δ' (x * y) = x • δ' y + y • δ' x) ∧ (∀ b, δ' (inl b) = δ b) ∧
        ∀ a', δ' (inr a') = 0)
    (q : Spec C ⟶ X) (p : Spec C ⟶ Y') (hq : q = Spec.map inl ≫ hU.fromSpec)
    (hp : p = Spec.map inr ≫ hV'.fromSpec) (w : p ≫ g = q ≫ f) (N : (Spec C).Modules) :
    Function.Bijective fun D : N.Derivation p ↦
      ((D.restrictScalars p g).congrHom w).pushforward := by
  subst hq hp
  have hq : (Spec.map inl ≫ hU.fromSpec) ⁻¹ᵁ U = ⊤ := preimage_eq_top hU inl
  have hp : (Spec.map inr ≫ hV'.fromSpec) ⁻¹ᵁ V' = ⊤ := preimage_eq_top hV' inr
  constructor
  · intro D₁ D₂ h
    refine Derivation.ext_of_isAffine fun x ↦ ?_
    have hS : Subring.closure (Set.range inl ∪ Set.range inr) ≤ eqSubring D₁ D₂ := by
      refine Subring.closure_le.mpr ?_
      rintro _ (⟨b, rfl⟩ | ⟨a', rfl⟩)
      · have hb := congr(Derivation.app $h U b)
        change D₁.app _ ((Spec.map inl ≫ hU.fromSpec).app U b) =
          D₂.app _ ((Spec.map inl ≫ hU.fromSpec).app U b) at hb
        change D₁.app ⊤ _ = D₂.app ⊤ _
        rw [← map_app_eq hU inl, Derivation.app_map, Derivation.app_map, hb]
      · change D₁.app ⊤ _ = D₂.app ⊤ _
        rw [← map_app_eq hV' inr, Derivation.app_map, Derivation.app_map, Derivation.app_app,
          Derivation.app_app]
    have := hS (hgen ((Scheme.ΓSpecIso C).hom x))
    change D₁.app ⊤ _ = D₂.app ⊤ _ at this
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
  · intro D₀
    -- the derivation `B → Γ(N, ⊤)` induced by `D₀`
    let res := N.presheaf.map (homOfLE hq.ge).op
    let δ : Γ(X, U) →+ Γ(N, ⊤) := res.hom.comp (D₀.app U)
    have hδ (x y : Γ(X, U)) : δ (x * y) = inl x • δ y + inl y • δ x := by
      change res (D₀.app U (x * y)) = inl x • res (D₀.app U y) + inl y • res (D₀.app U x)
      rw [Derivation.app_mul]
      refine (res.hom.map_add _ _).trans ?_
      change res ((Spec.map inl ≫ hU.fromSpec).app U x •
          (show Γ(N, (Spec.map inl ≫ hU.fromSpec) ⁻¹ᵁ U) from D₀.app U y)) +
        res ((Spec.map inl ≫ hU.fromSpec).app U y •
          (show Γ(N, (Spec.map inl ≫ hU.fromSpec) ⁻¹ᵁ U) from D₀.app U x)) = _
      rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_app_eq hU inl,
        map_app_eq hU inl, ← smul_top_eq, ← smul_top_eq]
    have hδA (a : Γ(Y, V)) : δ (f.appLE V U eU a) = 0 := by
      change res (D₀.app U (f.appLE V U eU a)) = 0
      rw [Derivation.app_appLE]
      exact res.hom.map_zero
    obtain ⟨δ', hδ'mul, hδ'l, hδ'r⟩ := hext Γ(N, ⊤) δ hδ hδA
    let δg : Γ(Spec C, ⊤) →+ Γ(N, ⊤) := δ'.comp (Scheme.ΓSpecIso C).hom.hom.toAddMonoidHom
    have hδg (x y : Γ(Spec C, ⊤)) : δg (x * y) = x • δg y + y • δg x := by
      change δ' ((Scheme.ΓSpecIso C).hom (x * y)) = x • δ' ((Scheme.ΓSpecIso C).hom y) +
        y • δ' ((Scheme.ΓSpecIso C).hom x)
      rw [map_mul, hδ'mul, smul_top_eq, smul_top_eq, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    have hδgf (s : Γ(Spec Γ(Y', V'), ⊤)) : δg ((Spec.map inr).appTop s) = 0 := by
      change δ' ((Scheme.ΓSpecIso C).hom ((Spec.map inr).appTop s)) = 0
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hδ'r]
    let D : N.Derivation (Spec.map inr ≫ hV'.fromSpec) :=
      (Derivation.ofGlobal δg hδg hδgf).restrictScalars _ _
    refine ⟨D, Derivation.ext_of_pushforward _ hU hq fun a ↦ ?_⟩
    apply presheaf_map_injective_of_eq N (homOfLE hq.ge) hq.symm
    change res (D.app _ ((Spec.map inl ≫ hU.fromSpec).app U a)) = res (D₀.app U a)
    rw [← Derivation.app_map, map_app_eq hU inl, Derivation.restrictScalars_app,
      Derivation.ofGlobal_app_top]
    change δ' ((Scheme.ΓSpecIso C).hom ((Scheme.ΓSpecIso C).inv (inl a))) = _
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, hδ'l]
    rfl

end

end BaseChangeChart

end AlgebraicGeometry
