/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.Basic

/-!
# Derivations and open immersions

* `Scheme.Modules.Derivation.restrict`: a derivation `𝒪_X → M` relative to `f : X ⟶ Y` restricts
  along an open immersion `j : U ⟶ X` to a derivation `𝒪_U → M|_U` relative to `j ≫ f`, and a
  universal derivation restricts to a universal derivation
  (`Scheme.Modules.Derivation.Universal.restrict`). Hence `Ω_{X/Y}|_U ≅ Ω_{U/Y}`.
* `Scheme.Modules.Derivation.restrictScalars`: a derivation relative to `g : X ⟶ V` is a
  derivation relative to `g ≫ j` for any `j : V ⟶ Y`; when `j` is an open immersion this is a
  bijection (`restrictScalarsEquiv`), so `Ω_{X/V} ≅ Ω_{X/Y}` in that case.

This is EGA IV 16.4.14 / Stacks Project, Tag 01UR for open immersions.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.Derivation

variable {U X Y V : Scheme.{u}}

section restrict

variable (j : U ⟶ X) [IsOpenImmersion j] {f : X ⟶ Y} {M : X.Modules}

/-- The restriction of a derivation along an open immersion `j : U ⟶ X`:
`Γ(U, W) ≅ Γ(X, j(W)) → Γ(M, j(W)) = Γ(M|_U, W)`. -/
def restrict (D : M.Derivation f) : (M.restrict j).Derivation (j ≫ f) where
  d {W} := (D.app (j ''ᵁ W.unop)).comp (j.appIso W.unop).inv.hom.toAddMonoidHom
  d_mul {W} a b := by
    change D.app _ ((j.appIso W.unop).inv (a * b)) =
      (j.appIso W.unop).inv a • D.app _ ((j.appIso W.unop).inv b) +
        (j.appIso W.unop).inv b • D.app _ ((j.appIso W.unop).inv a)
    rw [map_mul, app_mul]
  d_map {W W'} i a := by
    change D.app _ ((j.appIso W'.unop).inv (U.presheaf.map i a)) =
      M.presheaf.map (j.opensFunctor.map i.unop).op (D.app _ ((j.appIso W.unop).inv a))
    rw [← app_map, ← CommRingCat.comp_apply, j.appIso_inv_naturality]
    rfl
  d_app {W} s := by
    change D.app (j ''ᵁ (j ⁻¹ᵁ (f ⁻¹ᵁ W.unop)))
      ((j.appIso (j ⁻¹ᵁ (f ⁻¹ᵁ W.unop))).inv (j.app (f ⁻¹ᵁ W.unop) (f.app W.unop s))) = 0
    rw [← CommRingCat.comp_apply (j.app _), j.app_appIso_inv]
    exact (D.app_map (homOfLE (j.image_preimage_le _)) _).trans (by rw [app_app, map_zero])

@[simp]
lemma restrict_app (D : M.Derivation f) (W : U.Opens) (a : Γ(U, W)) :
    (D.restrict j).app W a = D.app (j ''ᵁ W) ((j.appIso W).inv a) :=
  rfl

lemma restrict_postcomp (D : M.Derivation f) {N : X.Modules} (α : M ⟶ N) :
    (D.postcomp α).restrict j = (D.restrict j).postcomp ((restrictFunctor j).map α) :=
  rfl

lemma restrictAdjunction_homEquiv_symm_app {N : U.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward j).obj N)
    (W : U.Opens) (x : Γ(M, j ''ᵁ W)) :
    (((restrictAdjunction j).homEquiv M N).symm φ).app W x =
      N.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op (φ.app (j ''ᵁ W) x) := by
  rw [Adjunction.homEquiv_counit]
  rfl

lemma restrictAdjunction_homEquiv_app {N : U.Modules} (α : M.restrict j ⟶ N)
    (V : X.Opens) (x : Γ(M, V)) :
    (((restrictAdjunction j).homEquiv M N) α).app V x =
      α.app (j ⁻¹ᵁ V) (M.presheaf.map (homOfLE (j.image_preimage_le V)).op x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The restriction of a universal derivation along an open immersion is universal: this
identifies `Ω_{X/Y}|_U` with `Ω_{U/Y}`. -/
def Universal.restrict {d : M.Derivation f} (hd : d.Universal) : (d.restrict j).Universal where
  desc {N} D := ((restrictAdjunction j).homEquiv M N).symm (hd.desc D.pushforward)
  fac {N} D := by
    ext W a
    rw [postcomp_app, restrict_app, restrictAdjunction_homEquiv_symm_app, hd.desc_app_app,
      pushforward_app, ← app_map, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      j.appIso_inv_app_presheafMap]
    rfl
  postcomp_injective {N} α β h := by
    apply ((restrictAdjunction j).homEquiv M N).injective
    refine hd.hom_ext fun V a ↦ ?_
    rw [restrictAdjunction_homEquiv_app, restrictAdjunction_homEquiv_app, ← app_map]
    have e : X.presheaf.map (homOfLE (j.image_preimage_le V)).op a =
        (j.appIso (j ⁻¹ᵁ V)).inv (j.app V a) := by
      rw [← CommRingCat.comp_apply, j.app_appIso_inv]
      rfl
    rw [e]
    exact congr($(h).app (j ⁻¹ᵁ V) (j.app V a))

end restrict

section restrictScalars

variable {M : X.Modules} (g : X ⟶ V) (j : V ⟶ Y)

/-- A derivation relative to `g : X ⟶ V` is a derivation relative to `g ≫ j`. -/
def restrictScalars (D : M.Derivation g) : M.Derivation (g ≫ j) where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {W} s := D.app_app (j ⁻¹ᵁ W.unop) (j.app W.unop s)

@[simp]
lemma restrictScalars_app (D : M.Derivation g) (W : X.Opens) (a : Γ(X, W)) :
    (D.restrictScalars g j).app W a = D.app W a :=
  rfl

lemma restrictScalars_postcomp (D : M.Derivation g) {N : X.Modules} (α : M ⟶ N) :
    (D.postcomp α).restrictScalars g j = (D.restrictScalars g j).postcomp α :=
  rfl

variable [IsOpenImmersion j]

/-- A derivation relative to `g ≫ j`, where `j` is an open immersion, is a derivation relative
to `g`. -/
def ofRestrictScalars (D : M.Derivation (g ≫ j)) : M.Derivation g where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {W} s := by
    change D.app (g ⁻¹ᵁ W.unop) (g.app W.unop s) = 0
    have e : j ⁻¹ᵁ j ''ᵁ W.unop = W.unop := j.preimage_image_eq W.unop
    have h₁ : D.app (g ⁻¹ᵁ (j ⁻¹ᵁ (j ''ᵁ W.unop)))
        (g.app (j ⁻¹ᵁ (j ''ᵁ W.unop)) (j.app (j ''ᵁ W.unop) ((j.appIso W.unop).inv s))) = 0 :=
      D.app_app (j ''ᵁ W.unop) ((j.appIso W.unop).inv s)
    rw [Scheme.Hom.appIso_inv_app_apply, ← CommRingCat.comp_apply, g.naturality,
      CommRingCat.comp_apply, app_map] at h₁
    exact Scheme.Modules.presheaf_map_injective_of_eq M _ (congrArg (g ⁻¹ᵁ ·) e)
      (h₁.trans (map_zero _).symm)

@[simp]
lemma ofRestrictScalars_app (D : M.Derivation (g ≫ j)) (W : X.Opens) (a : Γ(X, W)) :
    (D.ofRestrictScalars g j).app W a = D.app W a :=
  rfl

/-- For an open immersion `j : V ⟶ Y`, derivations relative to `g` and to `g ≫ j` coincide. -/
@[simps]
def restrictScalarsEquiv : M.Derivation g ≃ M.Derivation (g ≫ j) where
  toFun D := D.restrictScalars g j
  invFun D := D.ofRestrictScalars g j
  left_inv _ := rfl
  right_inv _ := rfl

variable {g j} in
/-- A universal derivation relative to `g ≫ j` is universal relative to `g`, when `j` is an open
immersion. -/
def Universal.ofRestrictScalars {d : M.Derivation (g ≫ j)} (hd : d.Universal) :
    (d.ofRestrictScalars g j).Universal where
  desc D' := hd.desc (D'.restrictScalars g j)
  fac D' := congr(Derivation.ofRestrictScalars g j $(hd.fac (D'.restrictScalars g j)))
  postcomp_injective α β h := hd.postcomp_injective α β congr(Derivation.restrictScalars g j $h)

variable {g j} in
/-- A universal derivation relative to `g` is universal relative to `g ≫ j`, when `j` is an open
immersion. -/
def Universal.restrictScalars {d : M.Derivation g} (hd : d.Universal) :
    (d.restrictScalars g j).Universal where
  desc D' := hd.desc (D'.ofRestrictScalars g j)
  fac D' := congr(Derivation.restrictScalars g j $(hd.fac (D'.ofRestrictScalars g j)))
  postcomp_injective α β h :=
    hd.postcomp_injective α β congr(Derivation.ofRestrictScalars g j $h)

end restrictScalars

end AlgebraicGeometry.Scheme.Modules.Derivation

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {U X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `Ω_{X/Y}|_U` is the sheaf of differentials of `j ≫ f : U ⟶ Y` for an open immersion
`j : U ⟶ X` (Stacks Project, Tag 01UR). -/
def relativeDifferentialsRestrictIso (j : U ⟶ X) [IsOpenImmersion j] :
    f.relativeDifferentials.restrict j ≅ (j ≫ f).relativeDifferentials :=
  (f.isUniversal.restrict j).iso (j ≫ f).isUniversal

/-- `Ω_{X/V} ≅ Ω_{X/Y}` for `g : X ⟶ V` and an open immersion `j : V ⟶ Y`. -/
def relativeDifferentialsCompIso {V : Scheme.{u}} (g : X ⟶ V) (j : V ⟶ Y) [IsOpenImmersion j] :
    (g ≫ j).relativeDifferentials ≅ g.relativeDifferentials :=
  (g ≫ j).isUniversal.ofRestrictScalars.iso g.isUniversal

end AlgebraicGeometry.Scheme.Hom
