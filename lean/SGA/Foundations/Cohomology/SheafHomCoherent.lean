/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.AffineOpenVanishing
import SGA.Foundations.Cohomology.Helpers
import SGA.Foundations.Cohomology.QuasiCoherentLocal
import SGA.Foundations.Cohomology.QuasiCoherentKernel
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.Differentials.SheafHom
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Coherence of `ℋom(M, N)`

For `𝒪_X`-modules `M`, `N`, the sheaf `ℋom(M, N)` of `SGA.Foundations.Differentials.SheafHom` has
as sections over `U` the `𝒪_U`-linear maps `M|_U → N|_U` (`Scheme.Modules.HomOn`). We describe
it over affine opens and prove that it is coherent when `M` and `N` are, on a locally noetherian
scheme (EGA I 1.3.12, 9.1.1; Stacks Tag 01CM):

* `CohomologyAux.homOnOfRestrict'`: the `HomOn` defined by a morphism `M|_Y ⟶ N|_Y` for an open
  immersion `Y ⟶ X`;
* `CohomologyAux.bijective_moduleSpecΓFunctor_map`: on `Spec R`, `Γ` is bijective on morphisms
  out of a quasi-coherent module (`M ≅ Γ(M)^~`);
* `CohomologyAux.exists_homOn_app_eq`, `CohomologyAux.homOn_ext_of_app_eq`: for `V` affine and `M`
  quasi-coherent, `HomOn M N V ≅ Hom_{Γ(X, V)}(Γ(M, V), Γ(N, V))`
  (`CohomologyAux.sheafHomAffineEquiv`);
* `CohomologyAux.isLocalizedModule_sheafHom`: the sections over `D(c)` are the localization at
  `c`, for `Γ(M, V)` finitely presented;
* `CohomologyAux.isQuasicoherent_sheafHom`, `CohomologyAux.isCoherent_sheafHom`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section OpenImmersion

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {M N : X.Modules}

lemma le_image_preimage_of_le_opensRange {V : X.Opens} (hV : V ≤ g.opensRange) :
    V ≤ g ''ᵁ g ⁻¹ᵁ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact le_inf hV le_rfl

/-- The map `Γ(M, V) → Γ(N, V)`, for `V` in the image of the open immersion `g`, induced by
`α : M|_Y ⟶ N|_Y`. -/
def homOnOfRestrictApp' (α : M.restrict g ⟶ N.restrict g) {V : X.Opens} (hV : V ≤ g.opensRange)
    (m : Γ(M, V)) : Γ(N, V) :=
  N.presheaf.map (homOfLE (le_image_preimage_of_le_opensRange g hV)).op
    (α.app (g ⁻¹ᵁ V) (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m))

lemma homOnOfRestrictApp'_add (α : M.restrict g ⟶ N.restrict g) {V : X.Opens}
    (hV : V ≤ g.opensRange) (m m' : Γ(M, V)) :
    homOnOfRestrictApp' g α hV (m + m') =
      homOnOfRestrictApp' g α hV m + homOnOfRestrictApp' g α hV m' := by
  unfold homOnOfRestrictApp'
  rw [map_add]
  exact (congrArg _ (map_add (α.app (g ⁻¹ᵁ V)).hom _ _)).trans (map_add _ _ _)

lemma homOnOfRestrictApp'_smul (α : M.restrict g ⟶ N.restrict g) {V : X.Opens}
    (hV : V ≤ g.opensRange) (r : Γ(X, V)) (m : Γ(M, V)) :
    homOnOfRestrictApp' g α hV (r • m) = r • homOnOfRestrictApp' g α hV m := by
  have e : X.presheaf.map (homOfLE (g.image_preimage_le V)).op r =
      (g.appIso (g ⁻¹ᵁ V)).inv (g.app V r) := by
    rw [← CommRingCat.comp_apply, g.app_appIso_inv]
    rfl
  have h₁ : M.presheaf.map (homOfLE (g.image_preimage_le V)).op (r • m) =
      (show Γ(M.restrict g, g ⁻¹ᵁ V) from g.app V r • (show Γ(M.restrict g, g ⁻¹ᵁ V) from
        M.presheaf.map (homOfLE (g.image_preimage_le V)).op m)) := by
    rw [map_smul, e]
    rfl
  have h₂ := Hom.app_smul α (U := g ⁻¹ᵁ V) (g.app V r)
    (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m)
  unfold homOnOfRestrictApp'
  rw [h₁, h₂]
  change N.presheaf.map (homOfLE (le_image_preimage_of_le_opensRange g hV)).op
    ((g.appIso (g ⁻¹ᵁ V)).inv (g.app V r) • (show Γ(N, g ''ᵁ g ⁻¹ᵁ V) from
      α.app (g ⁻¹ᵁ V) (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m))) = _
  rw [map_smul, ← e, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE (le_image_preimage_of_le_opensRange g hV) ≫ homOfLE _) (𝟙 V),
    op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]

lemma homOnOfRestrictApp'_naturality (α : M.restrict g ⟶ N.restrict g) {V W : X.Opens}
    (hWV : W ≤ V) (hV : V ≤ g.opensRange) (m : Γ(M, V)) :
    homOnOfRestrictApp' g α (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op m) =
      N.presheaf.map (homOfLE hWV).op (homOnOfRestrictApp' g α hV m) := by
  unfold homOnOfRestrictApp'
  rw [Scheme.Modules.presheaf_map_map M (homOfLE (g.image_preimage_le W)) (homOfLE hWV)
    (homOfLE (g.image_mono (g.preimage_mono hWV))) (homOfLE (g.image_preimage_le V))]
  have h := congr($(α.mapPresheaf.naturality (homOfLE (g.preimage_mono hWV)).op)
    (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m))
  change α.app (g ⁻¹ᵁ W) (M.presheaf.map (homOfLE (g.image_mono (g.preimage_mono hWV))).op
      (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m)) =
    N.presheaf.map (homOfLE (g.image_mono (g.preimage_mono hWV))).op
      (α.app (g ⁻¹ᵁ V) (M.presheaf.map (homOfLE (g.image_preimage_le V)).op m)) at h
  rw [h]
  exact Scheme.Modules.presheaf_map_map N _ _ (homOfLE hWV)
    (homOfLE (le_image_preimage_of_le_opensRange g hV)) _

/-- The `HomOn M N U` defined by a morphism `M|_Y ⟶ N|_Y` for an open immersion `g : Y ⟶ X` with
image `U`. -/
def homOnOfRestrict' (α : M.restrict g ⟶ N.restrict g) {U : X.Opens} (hU : g.opensRange = U) :
    HomOn M N U where
  app _ hV :=
    { toFun := homOnOfRestrictApp' g α (hV.trans hU.ge)
      map_add' := homOnOfRestrictApp'_add g α (hV.trans hU.ge)
      map_smul' := homOnOfRestrictApp'_smul g α (hV.trans hU.ge) }
  naturality hWV hV m := homOnOfRestrictApp'_naturality g α hWV (hV.trans hU.ge) m

lemma homOnOfRestrict'_app (α : M.restrict g ⟶ N.restrict g) {U : X.Opens}
    (hU : g.opensRange = U) {V : X.Opens} (hV : V ≤ U) (m : Γ(M, V)) :
    (homOnOfRestrict' g α hU).app V hV m = homOnOfRestrictApp' g α (hV.trans hU.ge) m :=
  rfl

end OpenImmersion

section Tilde

/-- On `Spec R`, the global sections functor is bijective on morphisms out of a quasi-coherent
module (`M ≅ Γ(M)^~` and `^~ ⊣ Γ`). -/
lemma bijective_moduleSpecΓFunctor_map {R : CommRingCat.{u}} (P Q : (Spec R).Modules)
    [P.IsQuasicoherent] :
    Function.Bijective (fun α : P ⟶ Q ↦ moduleSpecΓFunctor.map α) := by
  have key : ∀ α : P ⟶ Q, moduleSpecΓFunctor.map α =
      (tilde.adjunction.homEquiv _ _) (tilde.adjunction.counit.app P ≫ α) := by
    intro α
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.right_triangle_components, Category.id_comp]
  have : IsIso (tilde.adjunction.counit.app P) :=
    inferInstanceAs (IsIso (Scheme.Modules.fromTildeΓ P))
  have hb : Function.Bijective (fun α : P ⟶ Q ↦ tilde.adjunction.counit.app P ≫ α) :=
    ⟨fun a b h ↦ (cancel_epi _).mp h, fun β ↦ ⟨inv (tilde.adjunction.counit.app P) ≫ β, by simp⟩⟩
  have e : (fun α : P ⟶ Q ↦ moduleSpecΓFunctor.map α) =
      (tilde.adjunction.homEquiv _ _) ∘ (fun α : P ⟶ Q ↦ tilde.adjunction.counit.app P ≫ α) :=
    funext key
  rw [e]
  exact (tilde.adjunction.homEquiv _ _).bijective.comp hb

end Tilde

section Affine

/-- Composition of restriction maps of an `𝒪_X`-module. -/
lemma modules_map_map_apply {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens} (f : A ⟶ B)
    (g : B ⟶ C) (h : A ⟶ C) (x : Γ(M, C)) :
    M.presheaf.map f.op (M.presheaf.map g.op x) = M.presheaf.map h.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (f ≫ g) h]


variable {X : Scheme.{u}} {V : X.Opens}

lemma image_fromSpec_top (hV : IsAffineOpen V) : hV.fromSpec ''ᵁ ⊤ = V := by
  rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]

/-- `Γ(M|_{Spec Γ(X, V)}, ⊤) ≅ Γ(M, V)`, `Γ(X, V)`-linearly. -/
def restrictFromSpecTopEquiv (hV : IsAffineOpen V) (M : X.Modules) :
    Γ(M.restrict hV.fromSpec, ⊤) ≃ₗ[Γ(X, V)] Γ(M, V) where
  toFun x := M.presheaf.map (homOfLE (image_fromSpec_top hV).ge).op x
  invFun y := M.presheaf.map (homOfLE (image_fromSpec_top hV).le).op y
  map_add' := map_add _
  map_smul' r x := by
    have h := CohomologyAux.restrictAppIso_smul hV M ⊤ (image_fromSpec_top hV).le r x
    change M.presheaf.map _ ((M.restrictAppIso hV.fromSpec ⊤).hom (r • x)) = _
    rw [h, Scheme.Modules.map_smul, presheaf_map_map, presheaf_map_self]
    rfl
  left_inv x := by
    have := Scheme.Modules.presheaf_map_map M (homOfLE (image_fromSpec_top hV).le)
      (homOfLE (image_fromSpec_top hV).ge) (𝟙 _) (𝟙 _) (x : Γ(M, hV.fromSpec ''ᵁ ⊤))
    rw [op_id, CategoryTheory.Functor.map_id] at this
    exact this
  right_inv y := by
    have := Scheme.Modules.presheaf_map_map M (homOfLE (image_fromSpec_top hV).ge)
      (homOfLE (image_fromSpec_top hV).le) (𝟙 _) (𝟙 _) y
    rw [op_id, CategoryTheory.Functor.map_id] at this
    exact this

/-- **Morphisms of quasi-coherent modules on an affine open** (EGA I 1.3.8): every
`Γ(X, V)`-linear map `Γ(M, V) → Γ(N, V)`, `M` quasi-coherent, is the component over `V` of an
`𝒪_V`-linear map `M|_V → N|_V`. -/
theorem exists_homOn_app_eq (hV : IsAffineOpen V) {M N : X.Modules} [M.IsQuasicoherent]
    (h : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V)) : ∃ φ : HomOn M N V, φ.app V le_rfl = h := by
  let g := hV.fromSpec
  let eM := restrictFromSpecTopEquiv hV M
  let eN := restrictFromSpecTopEquiv hV N
  let h' : Γ(M.restrict g, ⊤) →ₗ[Γ(X, V)] Γ(N.restrict g, ⊤) :=
    eN.symm.toLinearMap ∘ₗ h ∘ₗ eM.toLinearMap
  let φ₀ : ModuleCat.of Γ(X, V) Γ(M.restrict g, ⊤) ⟶ ModuleCat.of Γ(X, V) Γ(N.restrict g, ⊤) :=
    ModuleCat.ofHom h'
  obtain ⟨α, hα⟩ := (bijective_moduleSpecΓFunctor_map (M.restrict g) (N.restrict g)).2 φ₀
  have hα' : ∀ x, α.app ⊤ x = h' x := fun x ↦ congr($(hα).hom x)
  refine ⟨homOnOfRestrict' g α hV.opensRange_fromSpec, LinearMap.ext fun m ↦ ?_⟩
  rw [homOnOfRestrict'_app]
  unfold homOnOfRestrictApp'
  let T := g ⁻¹ᵁ V
  have hnat := congr($(α.mapPresheaf.naturality (homOfLE (le_top : T ≤ ⊤)).op) (eM.symm m))
  change α.app T ((M.restrict g).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op (eM.symm m)) =
    (N.restrict g).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op (α.app ⊤ (eM.symm m)) at hnat
  have e1 : (M.restrict g).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op (eM.symm m) =
      M.presheaf.map (homOfLE (g.image_preimage_le V)).op m :=
    modules_map_map_apply M (g.opensFunctor.map (homOfLE (le_top : T ≤ ⊤)))
      (homOfLE (image_fromSpec_top hV).le) (homOfLE (g.image_preimage_le V)) m
  have e2 : h' (eM.symm m) = N.presheaf.map (homOfLE (image_fromSpec_top hV).le).op (h m) := by
    change eN.symm (h (eM (eM.symm m))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [← e1, hnat, hα', e2]
  have e3 : (N.restrict g).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op
      (N.presheaf.map (homOfLE (image_fromSpec_top hV).le).op (h m)) =
      N.presheaf.map (homOfLE (g.image_preimage_le V)).op (h m) :=
    modules_map_map_apply N (g.opensFunctor.map (homOfLE (le_top : T ≤ ⊤)))
      (homOfLE (image_fromSpec_top hV).le) (homOfLE (g.image_preimage_le V)) (h m)
  rw [e3, modules_map_map_apply N _ _ (𝟙 V), op_id, CategoryTheory.Functor.map_id]
  rfl

end Affine

section Ext

variable {X : Scheme.{u}}

/-- A section of `𝒪_X` over `V` becomes a unit on every open contained in its basic open. -/
lemma isUnit_res_of_le_basicOpen {V U : X.Opens} (s : Γ(X, V)) (hU : U ≤ X.basicOpen s) :
    IsUnit (X.presheaf.map (homOfLE (hU.trans (X.basicOpen_le s))).op s) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have h := (Scheme.mem_basicOpen X s x (X.basicOpen_le s (hU hx))).mp (hU hx)
  exact (TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (hU.trans (X.basicOpen_le s))) x hx s).symm ▸ h

/-- In a module over `Γ(X, U)`, multiplication by the restriction of a section `s` with
`U ⊆ D(s)` is injective. -/
lemma eq_of_res_smul_eq {V U : X.Opens} (s : Γ(X, V)) (hU : U ≤ X.basicOpen s) {P : Type*}
    [AddCommGroup P] [Module Γ(X, U) P] {a b : P}
    (h : X.presheaf.map (homOfLE (hU.trans (X.basicOpen_le s))).op s • a =
      X.presheaf.map (homOfLE (hU.trans (X.basicOpen_le s))).op s • b) : a = b := by
  obtain ⟨u, hu⟩ := isUnit_res_of_le_basicOpen s hU
  rw [← hu] at h
  have := congrArg (fun y ↦ (↑u⁻¹ : Γ(X, U)) • y) h
  simpa only [smul_smul, Units.inv_mul, one_smul] using this

/-- **`𝒪_V`-linear maps are determined by their component over an affine `V`** (EGA I 1.3.8):
for `M` quasi-coherent, two `φ, ψ : HomOn M N V` agreeing on `Γ(M, V)` are equal. -/
theorem homOn_ext_of_app_eq {V : X.Opens} (hV : IsAffineOpen V) {M N : X.Modules}
    [M.IsQuasicoherent] {φ ψ : HomOn M N V} (h : φ.app V le_rfl = ψ.app V le_rfl) : φ = ψ := by
  have hbasic : ∀ (t : Γ(X, V)) (m' : Γ(M, X.basicOpen t)),
      φ.app (X.basicOpen t) (X.basicOpen_le t) m' =
        ψ.app (X.basicOpen t) (X.basicOpen_le t) m' := by
    intro t m'
    obtain ⟨m₀, k, hk⟩ := exists_pow_smul_eq_map M hV t m'
    have e : ∀ χ : HomOn M N V, χ.app (X.basicOpen t) (X.basicOpen_le t)
        (X.presheaf.map (homOfLE (X.basicOpen_le t)).op (t ^ k) • m') =
        N.presheaf.map (homOfLE (X.basicOpen_le t)).op (χ.app V le_rfl m₀) := by
      intro χ
      rw [hk]
      exact χ.naturality (X.basicOpen_le t) le_rfl m₀
    have hφ := e φ
    have hψ := e ψ
    rw [LinearMap.map_smul] at hφ hψ
    rw [h] at hφ
    have hU : X.basicOpen t ≤ X.basicOpen (t ^ k) := by
      cases k with
      | zero => rw [pow_zero, Scheme.basicOpen_one]; exact X.basicOpen_le t
      | succ k => rw [Scheme.basicOpen_pow _ _ k.succ_pos]
    exact eq_of_res_smul_eq (t ^ k) hU (hφ.trans hψ.symm)
  refine HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun m ↦ ?_)
  apply N.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨t, htW, hxt⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hW hx)
  refine ⟨X.basicOpen t, htW, hxt, ?_⟩
  rw [← φ.naturality, ← ψ.naturality]
  exact hbasic t _

end Ext

section QuasiCoherent

variable {X : Scheme.{u}} (M N : X.Modules)

/-- The `Γ(X, V)`-linear map `Γ(M, W ⊓ V) → Γ(N, W ⊓ V)` defined by `φ : HomOn M N (W ⊓ V)`. -/
def homOnInfₗ {V : X.Opens} (W : X.Opens) (φ : HomOn M N (W ⊓ V)) :
    (M.presheafInf V).obj (op W) →ₗ[Γ(X, V)] (N.presheafInf V).obj (op W) where
  toFun m := φ.app (W ⊓ V) le_rfl m
  map_add' := map_add _
  map_smul' _ m := (φ.app (W ⊓ V) le_rfl).map_smul _ m

lemma finite_presheafInf_top {F : X.Modules} {V : X.Opens}
    (hF : Module.Finite Γ(X, V) Γ(F, V)) :
    Module.Finite Γ(X, V) ((F.presheafInf V).obj (op ⊤)) := by
  let res : Γ(F, V) →ₗ[Γ(X, V)] (F.presheafInf V).obj (op ⊤) :=
    { toFun := fun t ↦ F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op t
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r t ↦ by
        change F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (r • t) =
          X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op r •
            F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op t
        rw [Scheme.Modules.map_smul] }
  exact Module.Finite.of_surjective res fun s ↦
    ⟨F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s, by
      change F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op
          (F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op
            (@id Γ(F, ⊤ ⊓ V) s)) = @id Γ(F, ⊤ ⊓ V) s
      rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]⟩

/-- **`ℋom(M, N)` localizes** (EGA 0_I 5.? / I 1.3.12): for `M`, `N` quasi-coherent with
`Γ(M, V)` finite over the noetherian ring `Γ(X, V)`, `V` affine, the sections of `ℋom(M, N)`
over `D(c)` are the localization at `c` of those over `V`. -/
theorem isLocalizedModule_sheafHom [M.IsQuasicoherent] [N.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (hMV : Module.Finite Γ(X, V) Γ(M, V))
    (c : Γ(X, V)) :
    IsLocalizedModule.Away c (TopCat.Presheaf.resₗ ((sheafHom M N).presheafInf V)
      ((sheafHom M N).presheafInf_map_smul V) (le_top : X.basicOpen c ≤ ⊤)) := by
  have hW : X.basicOpen c ⊓ V = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  have hU₁ : IsAffineOpen (⊤ ⊓ V) := by rw [top_inf_eq]; exact hV
  have hU₂ : IsAffineOpen (X.basicOpen c ⊓ V) := by rw [hW]; exact hV.basicOpen c
  have hM := M.isLocalizedModule_presheafInf_top hV c hW
  have hN := N.isLocalizedModule_presheafInf_top hV c hW
  have hfin := finite_presheafInf_top hMV
  have hfp : Module.FinitePresentation Γ(X, V) ((M.presheafInf V).obj (op ⊤)) :=
    Module.finitePresentation_of_finite _ _
  let resM := TopCat.Presheaf.resₗ (M.presheafInf V) (M.presheafInf_map_smul V)
    (le_top : X.basicOpen c ≤ ⊤)
  let resN := TopCat.Presheaf.resₗ (N.presheafInf V) (N.presheafInf_map_smul V)
    (le_top : X.basicOpen c ≤ ⊤)
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c) := by
    rw [← CohomologyAux.presheaf_map_map (X.basicOpen_le c)
      (inf_le_left : X.basicOpen c ⊓ V ≤ X.basicOpen c)]
    exact (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map _).hom
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun y ↦ ?_) (fun x hx ↦ ?_)
  · rw [Module.End.isUnit_iff]
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
          (@id (HomOn M N (X.basicOpen c ⊓ V)) x) =
        X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
          (@id (HomOn M N (X.basicOpen c ⊓ V)) y) at hxy
      have := congrArg (hunit.unit⁻¹.1 • ·) hxy
      simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
      exact this
    · refine ⟨hunit.unit⁻¹.1 • (@id (HomOn M N (X.basicOpen c ⊓ V)) y), ?_⟩
      change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
        (hunit.unit⁻¹.1 • (@id (HomOn M N (X.basicOpen c ⊓ V)) y)) = y
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
      rfl
  · -- surjectivity: lift `y ∘ res` to `Γ(M, V) → Γ(N, V)` after multiplying by a power of `c`
    obtain ⟨h', ⟨_, n, rfl⟩, hh'⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (Submonoid.powers c) resN (homOnInfₗ M N (X.basicOpen c) y ∘ₗ resM)
    let h'' : Γ(M, ⊤ ⊓ V) →ₗ[Γ(X, ⊤ ⊓ V)] Γ(N, ⊤ ⊓ V) :=
      { toFun := h'
        map_add' := h'.map_add
        map_smul' := fun s m ↦ by
          have hs : s = X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op
              (X.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op s) := by
            rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_self]
          rw [hs]
          exact h'.map_smul _ m }
    obtain ⟨φ, hφ⟩ := exists_homOn_app_eq hU₁ h''
    refine ⟨n, φ, ?_⟩
    change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op (c ^ n) •
        (@id (HomOn M N (X.basicOpen c ⊓ V)) y) = φ.restrict (inf_le_inf_right V le_top)
    apply homOn_ext_of_app_eq hU₂
    refine LinearMap.ext fun z ↦ ?_
    rw [HomOn.smul_app, HomOn.restrict_app, LinearMap.smul_apply, CohomologyAux.presheaf_map_self]
    obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj resM c z
    change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op (c ^ k) •
        (@id Γ(M, X.basicOpen c ⊓ V) z) =
      M.presheaf.map (homOfLE (inf_le_inf_right V le_top :
        X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (@id Γ(M, ⊤ ⊓ V) m) at hm
    have hk := (hunit.pow k)
    rw [← map_pow] at hk
    refine (hk.smul_left_cancel).mp ?_
    have e1 := congrArg (fun f ↦ f m) hh'
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at e1
    change N.presheaf.map (homOfLE (inf_le_inf_right V le_top :
        X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (h' m) =
      X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op (c ^ n) •
        y.app (X.basicOpen c ⊓ V) le_rfl (M.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op m) at e1
    let r₂ := X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op
    let mr : Γ(M, X.basicOpen c ⊓ V) := M.presheaf.map (homOfLE (inf_le_inf_right V le_top :
      X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op m
    have hm' : r₂ (c ^ k) • z = mr := hm
    have hφm : φ.app (⊤ ⊓ V) le_rfl m = h' m := congrArg (fun f ↦ f m) hφ
    have e2 : φ.app (X.basicOpen c ⊓ V) (inf_le_inf_right V le_top) mr =
        N.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (φ.app (⊤ ⊓ V) le_rfl m) :=
      φ.naturality (inf_le_inf_right V le_top) le_rfl m
    calc r₂ (c ^ k) • r₂ (c ^ n) • y.app (X.basicOpen c ⊓ V) le_rfl z
        = r₂ (c ^ n) • y.app (X.basicOpen c ⊓ V) le_rfl (r₂ (c ^ k) • z) := by
          rw [LinearMap.map_smul, smul_comm]
      _ = r₂ (c ^ n) • y.app (X.basicOpen c ⊓ V) le_rfl mr := by rw [hm']
      _ = N.presheaf.map (homOfLE (inf_le_inf_right V le_top :
            X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (h' m) := e1.symm
      _ = φ.app (X.basicOpen c ⊓ V) (inf_le_inf_right V le_top) mr := by rw [e2, hφm]
      _ = φ.app (X.basicOpen c ⊓ V) (inf_le_inf_right V le_top) (r₂ (c ^ k) • z) := by rw [hm']
      _ = r₂ (c ^ k) • φ.app (X.basicOpen c ⊓ V) (inf_le_inf_right V le_top) z :=
          LinearMap.map_smul _ _ _
  · -- injectivity: a homomorphism vanishing on `D(c)` is killed by a power of `c`
    have hcomp : resN ∘ₗ homOnInfₗ M N ⊤ x = resN ∘ₗ 0 := by
      refine LinearMap.ext fun m ↦ ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
      change N.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (x.app (⊤ ⊓ V) le_rfl m) = 0
      rw [← x.naturality (inf_le_inf_right V le_top) le_rfl m]
      have hx' : x.restrict (inf_le_inf_right V le_top) = 0 := hx
      exact congrArg (fun ψ : HomOn M N (X.basicOpen c ⊓ V) ↦
        ψ.app (X.basicOpen c ⊓ V) le_rfl (M.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op m)) hx'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
      (Submonoid.powers c) resN _ _ hcomp
    refine ⟨n, ?_⟩
    change X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ n) •
      (@id (HomOn M N (⊤ ⊓ V)) x) = 0
    apply homOn_ext_of_app_eq hU₁
    refine LinearMap.ext fun m ↦ ?_
    rw [HomOn.smul_app, LinearMap.smul_apply, CohomologyAux.presheaf_map_self]
    have := congrArg (fun f ↦ f m) hn
    simp only [smul_zero] at this
    exact this

end QuasiCoherent

section Coherent

/-- Over a noetherian ring, linear maps between finite modules form a finite module. -/
lemma finite_linearMap_of_isNoetherianRing {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] : Module.Finite R (M →ₗ[R] N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let pre : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) := LinearMap.lcomp R N π
  have hinj : Function.Injective pre := fun f g h ↦ LinearMap.ext fun m ↦ by
    obtain ⟨x, rfl⟩ := hπ m
    exact LinearMap.congr_fun h x
  exact Module.Finite.of_injective pre hinj

variable {X : Scheme.{u}}

/-- On an affine open, sections of `ℋom(M, N)` are the `Γ(X, V)`-linear maps `Γ(M, V) → Γ(N, V)`
(EGA I 1.3.8), for `M` quasi-coherent. -/
def sheafHomAffineEquiv {V : X.Opens} (hV : IsAffineOpen V) (M N : X.Modules)
    [M.IsQuasicoherent] :
    Γ(sheafHom M N, V) ≃ₗ[Γ(X, V)] (Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V)) :=
  LinearEquiv.ofBijective
    { toFun := fun φ : HomOn M N V ↦ φ.app V le_rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ by
        ext m
        change X.presheaf.map (homOfLE le_rfl).op r • φ.app V le_rfl m = r • φ.app V le_rfl m
        rw [CohomologyAux.presheaf_map_self] }
    ⟨fun _ _ h ↦ homOn_ext_of_app_eq hV h, fun h ↦ exists_homOn_app_eq hV h⟩

lemma sheafHomAffineEquiv_apply {V : X.Opens} (hV : IsAffineOpen V) (M N : X.Modules)
    [M.IsQuasicoherent] (φ : Γ(sheafHom M N, V)) (m : Γ(M, V)) :
    sheafHomAffineEquiv hV M N φ m = (φ : HomOn M N V).app V le_rfl m :=
  rfl

/-- **`ℋom(M, N)` is quasi-coherent** for `M` coherent and `N` quasi-coherent on a locally
noetherian scheme (EGA I 1.3.12, 9.1.1). -/
theorem isQuasicoherent_sheafHom [IsLocallyNoetherian X] (M N : X.Modules) [M.IsCoherent]
    [N.IsQuasicoherent] : (sheafHom M N).IsQuasicoherent := by
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  exact isQuasicoherent_of_isLocalizedModule _ (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U c ↦ by
      have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      exact isLocalizedModule_sheafHom M N U.2 (finite_sections_of_isFiniteType M U.2) c

/-- **`ℋom(M, N)` is coherent** for `M`, `N` coherent on a locally noetherian scheme (EGA I 9.1.1;
Stacks Tag 01CM). -/
theorem isCoherent_sheafHom [IsLocallyNoetherian X] (M N : X.Modules) [M.IsCoherent]
    [N.IsCoherent] : (sheafHom M N).IsCoherent := by
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : N.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have := isQuasicoherent_sheafHom M N
  refine ⟨this, isFiniteType_of_finite_sections _ (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦ ?_⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := finite_sections_of_isFiniteType M U.2
  have := finite_sections_of_isFiniteType N U.2
  have : Module.Finite Γ(X, U.1) (Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1)) :=
    finite_linearMap_of_isNoetherianRing
  exact Module.Finite.equiv (sheafHomAffineEquiv U.2 M N).symm

end Coherent

end AlgebraicGeometry.CohomologyAux
