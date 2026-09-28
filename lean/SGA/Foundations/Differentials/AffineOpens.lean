/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.Restrict
import SGA.Foundations.Differentials.Tilde

/-!
# `Ω_{X/Y}` on affine opens

Let `f : X ⟶ Y` be a morphism of schemes, `V ⊆ Y` and `U ⊆ f⁻¹ V` affine opens, `A = Γ(X, U)`,
`R = Γ(Y, V)`. Then `Ω_{X/Y}|_U ≅ Ω_{A/R}^~` (`Scheme.Hom.relativeDifferentialsFromSpecIso`) and
`Γ(U, Ω_{X/Y}) ≅ Ω_{A/R}` as `A`-modules, compatibly with `d`
(`Scheme.Hom.relativeDifferentialsAppEquiv`; Stacks Project, Tag 01UQ; EGA IV 16.5.4).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules.Derivation

variable {X Y : Scheme.{u}} {M : X.Modules}

/-- Transport of a derivation along an equality of morphisms. -/
def congrHom {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (D : M.Derivation f₁) : M.Derivation f₂ where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {V} s := by subst h; exact D.d_app s

@[simp]
lemma congrHom_app {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (D : M.Derivation f₁) (U : X.Opens)
    (a : Γ(X, U)) : (D.congrHom h).app U a = D.app U a :=
  rfl

/-- A universal derivation stays universal after transport along an equality of morphisms. -/
def Universal.congrHom {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) {d : M.Derivation f₁} (hd : d.Universal) :
    (d.congrHom h).Universal where
  desc D' := hd.desc (D'.congrHom h.symm)
  fac D' := congr(Derivation.congrHom h $(hd.fac (D'.congrHom h.symm)))
  postcomp_injective α β e := hd.postcomp_injective α β congr(Derivation.congrHom h.symm $e)

end Scheme.Modules.Derivation

open Scheme.Modules

namespace IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

set_option backward.isDefEq.respectTransparency false in
lemma appIso_fromSpec_top_hom_map (h : hU.fromSpec ''ᵁ ⊤ ≤ U) (a : Γ(X, U)) :
    (hU.fromSpec.appIso ⊤).hom (X.presheaf.map (homOfLE h).op a) =
      (Scheme.ΓSpecIso Γ(X, U)).inv a := by
  have h' : U ≤ hU.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have h1 : X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op a) = a := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE h' ≫ homOfLE h) (𝟙 _), op_id, X.presheaf.map_id,
      CommRingCat.id_apply]
  rw [Scheme.Hom.appIso_hom, hU.fromSpec_app_of_le _ h', CommRingCat.comp_apply,
    CommRingCat.comp_apply, CommRingCat.comp_apply, h1, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  have h2 (i : op (⊤ : (Spec Γ(X, U)).Opens) ⟶ op ⊤) (y : Γ(Spec Γ(X, U), ⊤)) :
      (Spec Γ(X, U)).presheaf.map i y = y := by
    rw [show i = 𝟙 _ from Quiver.Hom.unop_inj (Subsingleton.elim _ _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact h2 _ _

lemma appIso_fromSpec_top_inv (h : hU.fromSpec ''ᵁ ⊤ ≤ U) (a : Γ(X, U)) :
    (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a) =
      X.presheaf.map (homOfLE h).op a := by
  rw [← hU.appIso_fromSpec_top_hom_map h, ← CommRingCat.comp_apply, Iso.hom_inv_id,
    CommRingCat.id_apply]

lemma fromSpec_image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

end IsAffineOpen

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

/-- The universal derivation of `Ω_{X/Y}|_U`, for `U ⊆ f⁻¹ V` affine opens, as a derivation
relative to `Spec Γ(X, U) ⟶ Spec Γ(Y, V)`. -/
def fromSpecDerivation :
    (f.relativeDifferentials.restrict hU.fromSpec).Derivation (Spec.map (f.appLE V U e)) :=
  ((f.universalDerivation.restrict hU.fromSpec).congrHom
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e).symm).ofRestrictScalars _ _

/-- `fromSpecDerivation` is universal. -/
def isUniversalFromSpecDerivation : (f.fromSpecDerivation hU hV e).Universal :=
  (((f.isUniversal.restrict hU.fromSpec).congrHom
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e).symm)).ofRestrictScalars

@[simp]
lemma fromSpecDerivation_app (W : (Spec Γ(X, U)).Opens) (a : Γ(Spec Γ(X, U), W)) :
    (f.fromSpecDerivation hU hV e).app W a =
      f.universalDerivation.app (hU.fromSpec ''ᵁ W) ((hU.fromSpec.appIso W).inv a) :=
  rfl

/-- `Ω_{X/Y}|_U ≅ Ω_{A/R}^~` for affine opens `U ⊆ f⁻¹ V`, `A = Γ(X, U)`, `R = Γ(Y, V)`
(Stacks Project, Tag 01UQ). -/
def relativeDifferentialsFromSpecIso :
    f.relativeDifferentials.restrict hU.fromSpec ≅
      tilde (CommRingCat.KaehlerDifferential (f.appLE V U e)) :=
  (f.isUniversalFromSpecDerivation hU hV e).iso
    (isUniversalTildeKaehlerDerivation (f.appLE V U e))

lemma relativeDifferentialsFromSpecIso_hom_app_top (a : Γ(Spec Γ(X, U), ⊤)) :
    (f.relativeDifferentialsFromSpecIso hU hV e).hom.app ⊤
        ((f.fromSpecDerivation hU hV e).app ⊤ a) =
      tilde.toOpen _ ⊤ (CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso Γ(X, U)).hom a)) := by
  rw [relativeDifferentialsFromSpecIso, Derivation.Universal.iso_hom,
    Derivation.Universal.desc_app_app, tildeKaehlerDerivation_app_top]

/-- The additive isomorphism `Γ(U, Ω_{X/Y}) ≅ Ω_{A/R}` underlying
`relativeDifferentialsAppEquiv`. -/
def relativeDifferentialsAppAddEquiv :
    Γ(f.relativeDifferentials, U) ≃+ CommRingCat.KaehlerDifferential (f.appLE V U e) :=
  let e₁ : Γ(f.relativeDifferentials, U) ≃+ Γ(f.relativeDifferentials, hU.fromSpec ''ᵁ ⊤) :=
    (f.relativeDifferentials.presheaf.mapIso
      (eqToIso (hU.fromSpec_image_top)).op).addCommGroupIsoToAddEquiv
  let e₂ : Γ(f.relativeDifferentials.restrict hU.fromSpec, ⊤) ≃+
      Γ(tilde (CommRingCat.KaehlerDifferential (f.appLE V U e)), ⊤) :=
    ((Scheme.Modules.toPresheaf _).mapIso
      (f.relativeDifferentialsFromSpecIso hU hV e)).app (op ⊤) |>.addCommGroupIsoToAddEquiv
  let e₃ : Γ(tilde (CommRingCat.KaehlerDifferential (f.appLE V U e)), ⊤) ≃+
      CommRingCat.KaehlerDifferential (f.appLE V U e) :=
    (tilde.isoTop _).symm.toLinearEquiv.toAddEquiv
  e₁.trans (e₂.trans e₃)

set_option backward.isDefEq.respectTransparency false in
lemma relativeDifferentialsAppAddEquiv_universalDerivation (a : Γ(X, U)) :
    f.relativeDifferentialsAppAddEquiv hU hV e (f.universalDerivation.app U a) =
      CommRingCat.KaehlerDifferential.d a := by
  have h₁ : f.relativeDifferentials.presheaf.map (eqToHom (hU.fromSpec_image_top)).op
      (f.universalDerivation.app U a) =
        (f.fromSpecDerivation hU hV e).app ⊤ ((Scheme.ΓSpecIso Γ(X, U)).inv a) := by
    rw [fromSpecDerivation_app, IsAffineOpen.appIso_fromSpec_top_inv hU
      (hU.fromSpec_image_top).le, ← Derivation.app_map]
    rfl
  change (tilde.isoTop _).inv ((f.relativeDifferentialsFromSpecIso hU hV e).hom.app ⊤
    (f.relativeDifferentials.presheaf.map (eqToHom (hU.fromSpec_image_top)).op
      (f.universalDerivation.app U a))) = _
  rw [h₁, relativeDifferentialsFromSpecIso_hom_app_top, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]
  exact congr($((tilde.isoTop _).hom_inv_id) _)

set_option backward.isDefEq.respectTransparency false in
/-- `Γ(U, Ω_{X/Y}) ≅ Ω_{A/R}` as `A`-modules, for affine opens `U ⊆ f⁻¹ V`, `A = Γ(X, U)`,
`R = Γ(Y, V)` (Stacks Project, Tag 01UQ; EGA IV 16.5.4). It sends `d a` to `d a`
(`relativeDifferentialsAppEquiv_universalDerivation`). -/
def relativeDifferentialsAppEquiv :
    Γ(f.relativeDifferentials, U) ≃ₗ[Γ(X, U)] CommRingCat.KaehlerDifferential (f.appLE V U e) :=
  { f.relativeDifferentialsAppAddEquiv hU hV e with
    map_smul' a y := by
      change (tilde.isoTop _).inv ((f.relativeDifferentialsFromSpecIso hU hV e).hom.app ⊤
        (f.relativeDifferentials.presheaf.map (eqToHom hU.fromSpec_image_top).op (a • y))) =
          a • (tilde.isoTop _).inv ((f.relativeDifferentialsFromSpecIso hU hV e).hom.app ⊤
            (f.relativeDifferentials.presheaf.map (eqToHom hU.fromSpec_image_top).op y))
      have ha : X.presheaf.map (eqToHom hU.fromSpec_image_top).op a =
          (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a) :=
        (IsAffineOpen.appIso_fromSpec_top_inv hU hU.fromSpec_image_top.le a).symm
      rw [Scheme.Modules.map_smul, ha]
      change (tilde.isoTop _).inv ((f.relativeDifferentialsFromSpecIso hU hV e).hom.app ⊤
        ((Scheme.ΓSpecIso Γ(X, U)).inv a • _)) = _
      rw [Scheme.Modules.Hom.app_smul, ← smul_top_eq]
      exact (tilde.isoTop _).inv.hom.map_smul a _ }

@[simp]
lemma relativeDifferentialsAppEquiv_universalDerivation (a : Γ(X, U)) :
    f.relativeDifferentialsAppEquiv hU hV e (f.universalDerivation.app U a) =
      CommRingCat.KaehlerDifferential.d a :=
  f.relativeDifferentialsAppAddEquiv_universalDerivation hU hV e a

end Scheme.Hom

end AlgebraicGeometry
