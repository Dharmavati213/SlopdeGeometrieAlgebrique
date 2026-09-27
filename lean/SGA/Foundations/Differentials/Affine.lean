/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.Basic
import SGA.Foundations.Differentials.Localization
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Derivations on affine schemes

Let `f : X ⟶ Y` be a morphism of affine schemes and `M` an `𝒪_X`-module. A derivation of `𝒪_X`
into `M` relative to `f` is determined by its value on global sections
(`Scheme.Modules.Derivation.ext_of_isAffine`), and every derivation
`Γ(X, ⊤) → Γ(M, ⊤)` vanishing on `Γ(Y, ⊤)` extends to a derivation of `𝒪_X`
(`Scheme.Modules.Derivation.ofGlobal`): on a basic open `D(r)` it is given by the quotient rule,
and the sheaf property of `M` glues these. In other words
`Der_Y(𝒪_X, M) ≃ Der_{Γ(Y, 𝒪_Y)}(Γ(X, 𝒪_X), Γ(X, M))` (`globalDerivationEquiv`).
This is the key step in the computation of `Ω_{X/Y}` on affine opens (Stacks Project, Tag 01UQ).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {M : X.Modules}

/-- On an affine scheme, two sections of an `𝒪_X`-module over `W` are equal if they agree on
every basic open `D(r) ⊆ W`. -/
lemma section_ext_basicOpen [IsAffine X] {W : X.Opens} {s t : Γ(M, W)}
    (h : ∀ (r : Γ(X, ⊤)) (hr : X.basicOpen r ≤ W),
      M.presheaf.map (homOfLE hr).op s = M.presheaf.map (homOfLE hr).op t) : s = t := by
  apply M.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrW⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X) hx
  exact ⟨X.basicOpen r, hrW, hxr, h r hrW⟩

namespace Derivation

/-- On an affine scheme, a derivation is determined by its values on global sections. -/
theorem ext_of_isAffine [IsAffine X] {D D' : M.Derivation f}
    (h : ∀ a : Γ(X, ⊤), D.app ⊤ a = D'.app ⊤ a) : D = D' := by
  ext U a
  refine section_ext_basicOpen fun r hr ↦ ?_
  rw [← app_map, ← app_map]
  have : D.app (X.basicOpen r) = D'.app (X.basicOpen r) :=
    AddMonoidHom.eq_of_leibniz_of_isLocalization (Submonoid.powers r) (RingHom.id _)
      (D.app_mul _) (D'.app_mul _) fun b ↦ by
        change D.app _ (X.presheaf.map (homOfLE _).op b) =
          D'.app _ (X.presheaf.map (homOfLE _).op b)
        rw [app_map, app_map, h]
  rw [this]

section ofGlobal

variable [IsAffine X] (δ : Γ(X, ⊤) →+ Γ(M, ⊤)) (hδ : ∀ a b, δ (a * b) = a • δ b + b • δ a)

/-- The extension of a derivation `δ : Γ(X, ⊤) → Γ(M, ⊤)` to the basic open `D(r)`, given by the
quotient rule. -/
noncomputable def extendBasicOpen (r : Γ(X, ⊤)) :
    _root_.Derivation ℤ Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
  letI : Module Γ(X, ⊤) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r))
  haveI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    IsScalarTower.of_compHom _ _ _
  let δ₀ : _root_.Derivation ℤ Γ(X, ⊤) Γ(M, X.basicOpen r) :=
    _root_.Derivation.mk' ((M.presheaf.map (homOfLE le_top).op).hom.comp δ).toIntLinearMap
      fun a b ↦ by
        change M.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op (δ (a * b)) =
          X.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op a •
            M.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op (δ b) +
          X.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op b •
            M.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op (δ a)
        rw [hδ, map_add, map_smul, map_smul]
  δ₀.extendOfIsLocalization (Submonoid.powers r) (B := Γ(X, X.basicOpen r))

lemma extendBasicOpen_algebraMap (r : Γ(X, ⊤)) (a : Γ(X, ⊤)) :
    extendBasicOpen δ hδ r (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r) a) =
      M.presheaf.map (homOfLE le_top).op (δ a) := by
  let : Module Γ(X, ⊤) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r))
  have : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    IsScalarTower.of_compHom _ _ _
  exact _root_.Derivation.extendOfIsLocalization_algebraMap (Submonoid.powers r) _ a

lemma extendBasicOpen_map (r : Γ(X, ⊤)) (a : Γ(X, ⊤)) :
    extendBasicOpen δ hδ r (X.presheaf.map (homOfLE le_top).op a) =
      M.presheaf.map (homOfLE le_top).op (δ a) :=
  extendBasicOpen_algebraMap δ hδ r a

lemma map_extendBasicOpen {r r' : Γ(X, ⊤)} (i : X.basicOpen r' ⟶ X.basicOpen r)
    (x : Γ(X, X.basicOpen r)) :
    M.presheaf.map i.op (extendBasicOpen δ hδ r x) =
      extendBasicOpen δ hδ r' (X.presheaf.map i.op x) := by
  let d₁ : Γ(X, X.basicOpen r) →+ Γ(M, X.basicOpen r') :=
    (M.presheaf.map i.op).hom.comp (extendBasicOpen δ hδ r).toAddMonoidHom
  let d₂ : Γ(X, X.basicOpen r) →+ Γ(M, X.basicOpen r') :=
    (extendBasicOpen δ hδ r').toAddMonoidHom.comp (X.presheaf.map i.op).hom.toAddMonoidHom
  suffices d₁ = d₂ from congr($this x)
  refine AddMonoidHom.eq_of_leibniz_of_isLocalization (Submonoid.powers r)
    (X.presheaf.map i.op).hom (fun x y ↦ ?_) (fun x y ↦ ?_) fun a ↦ ?_
  · change M.presheaf.map i.op (extendBasicOpen δ hδ r (x * y)) = _
    rw [_root_.Derivation.leibniz, map_add, map_smul, map_smul]
    rfl
  · change extendBasicOpen δ hδ r' (X.presheaf.map i.op (x * y)) = _
    rw [map_mul, _root_.Derivation.leibniz]
    rfl
  · change M.presheaf.map i.op (extendBasicOpen δ hδ r (X.presheaf.map (homOfLE le_top).op a)) =
      extendBasicOpen δ hδ r' (X.presheaf.map i.op (X.presheaf.map (homOfLE le_top).op a))
    have e : i ≫ homOfLE (le_top : X.basicOpen r ≤ ⊤) = homOfLE le_top := Subsingleton.elim _ _
    rw [extendBasicOpen_map, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, e,
      extendBasicOpen_map, ← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp, e]

/-- The derivations `extendBasicOpen δ hδ r` on the basic opens, as a morphism of presheaves of
abelian groups on the basis of basic opens. -/
noncomputable def extendBasicOpenFamily :
    (inducedFunctor (X.basicOpen : Γ(X, ⊤) → X.Opens)).op ⋙
        (X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      (inducedFunctor (X.basicOpen : Γ(X, ⊤) → X.Opens)).op ⋙ M.presheaf where
  app r := AddCommGrpCat.ofHom (extendBasicOpen δ hδ r.unop).toLinearMap.toAddMonoidHom
  naturality {r r'} i := by
    ext x
    exact (map_extendBasicOpen δ hδ i.unop.hom x).symm

/-- The extension of `δ` to a morphism of presheaves of abelian groups `𝒪_X ⟶ M`, glued from
the derivations `extendBasicOpen δ hδ r` on the basic opens. -/
noncomputable def extendHom :
    X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⟶ M.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom
    (X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ⟨M.presheaf, M.isSheaf⟩ (isBasis_basicOpen X) (extendBasicOpenFamily δ hδ)

lemma extendHom_app_basicOpen (r : Γ(X, ⊤)) (x : Γ(X, X.basicOpen r)) :
    (extendHom δ hδ).app (op (X.basicOpen r)) x = extendBasicOpen δ hδ r x :=
  congr($(TopCat.Sheaf.extend_hom_app
    (X.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ⟨M.presheaf, M.isSheaf⟩ (isBasis_basicOpen X) (extendBasicOpenFamily δ hδ) r) x)

lemma extendHom_map {U V : X.Opens} (i : U ⟶ V) (x : Γ(X, V)) :
    (extendHom δ hδ).app (op U) (X.presheaf.map i.op x) =
      M.presheaf.map i.op ((extendHom δ hδ).app (op V) x) :=
  congr($((extendHom δ hδ).naturality i.op) x)

lemma extendHom_mul (U : X.Opens) (x y : Γ(X, U)) :
    (extendHom δ hδ).app (op U) (x * y) =
      x • (extendHom δ hδ).app (op U) y + y • (extendHom δ hδ).app (op U) x := by
  refine section_ext_basicOpen fun r hr ↦ ?_
  rw [← extendHom_map, map_mul, extendHom_app_basicOpen, _root_.Derivation.leibniz, map_add,
    map_smul, map_smul, ← extendHom_map, ← extendHom_map, extendHom_app_basicOpen,
    extendHom_app_basicOpen]

lemma extendHom_app_top (a : Γ(X, ⊤)) : (extendHom δ hδ).app (op ⊤) a = δ a := by
  refine section_ext_basicOpen fun r hr ↦ ?_
  rw [← extendHom_map, extendHom_app_basicOpen]
  exact extendBasicOpen_map δ hδ r a

variable [IsAffine Y] (hδf : ∀ s : Γ(Y, ⊤), δ (f.appTop s) = 0)
include hδf

lemma extendHom_app_basicOpen_eq_zero (t : Γ(Y, ⊤)) (s : Γ(Y, Y.basicOpen t)) :
    (extendHom δ hδ).app (op (f ⁻¹ᵁ Y.basicOpen t)) (f.app (Y.basicOpen t) s) = 0 := by
  let W := f ⁻¹ᵁ Y.basicOpen t
  let d₁ : Γ(Y, Y.basicOpen t) →+ Γ(M, W) :=
    ((extendHom δ hδ).app (op W)).hom.comp (f.app (Y.basicOpen t)).hom.toAddMonoidHom
  suffices d₁ = 0 from congr($this s)
  refine AddMonoidHom.eq_of_leibniz_of_isLocalization (Submonoid.powers t)
    (f.app (Y.basicOpen t)).hom (fun x y ↦ ?_) (fun x y ↦ by simp) fun a ↦ ?_
  · change (extendHom δ hδ).app (op W) (f.app _ (x * y)) = _
    rw [map_mul, extendHom_mul]
    rfl
  · change (extendHom δ hδ).app (op W) (f.app _ (Y.presheaf.map (homOfLE le_top).op a)) = 0
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, extendHom_map]
    change M.presheaf.map _ ((extendHom δ hδ).app (op ⊤) (f.appTop a)) = 0
    rw [extendHom_app_top, hδf, map_zero]

lemma extendHom_app_eq_zero (V : Y.Opens) (s : Γ(Y, V)) :
    (extendHom δ hδ).app (op (f ⁻¹ᵁ V)) (f.app V s) = 0 := by
  apply M.isSheaf.section_ext (U := op (f ⁻¹ᵁ V))
  intro x hx
  obtain ⟨_, ⟨t, rfl⟩, hxt, htV⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y) hx
  refine ⟨f ⁻¹ᵁ Y.basicOpen t, f.preimage_mono htV, hxt, ?_⟩
  rw [← extendHom_map, map_zero]
  have := extendHom_app_basicOpen_eq_zero δ hδ hδf t (Y.presheaf.map (homOfLE htV).op s)
  rwa [← CommRingCat.comp_apply, f.naturality] at this

/-- A derivation `δ : Γ(X, ⊤) → Γ(M, ⊤)` of global sections vanishing on `Γ(Y, ⊤)`, for a
morphism of affine schemes `f : X ⟶ Y`, extends to a derivation of `𝒪_X` into `M`. -/
noncomputable def ofGlobal : M.Derivation f where
  d {U} := ((extendHom δ hδ).app U).hom
  d_mul {U} a b := extendHom_mul δ hδ U.unop a b
  d_map i a := extendHom_map δ hδ i.unop a
  d_app {V} s := extendHom_app_eq_zero δ hδ hδf V.unop s

@[simp]
lemma ofGlobal_app_top (a : Γ(X, ⊤)) : (ofGlobal δ hδ hδf).app ⊤ a = δ a :=
  extendHom_app_top δ hδ a

end ofGlobal

end Derivation

end AlgebraicGeometry.Scheme.Modules
