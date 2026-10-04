/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHom
import SGA.Foundations.Analytic.ModulesExactness

/-!
# Local morphisms and their maps on stalks

Sections of the Hom sheaf are the morphisms on an open subspace, and therefore induce
linear maps on the stalks at every point of that open subspace.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomStalk.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} {M N : X.Modules}

/-- Local morphisms over `U` agree with morphisms on the open site over `U`. -/
def homOnOverEquiv (U : Opens X) : HomOn M N U ≃ (M.over U ⟶ N.over U) where
  toFun φ := ⟨{
    app V := ModuleCat.ofHom (φ.app V.unop.left V.unop.hom.le)
    naturality i := by
      ext m
      exact φ.naturality i.unop.left.le _ m }⟩
  invFun f := {
    app V hV := (f.val.app (op (Over.mk (homOfLE hV)))).hom
    naturality {V W} hWV hV m := by
      let a : Over.mk (homOfLE (hWV.trans hV)) ⟶ Over.mk (homOfLE hV) :=
        Over.homMk (homOfLE hWV) (Subsingleton.elim _ _)
      exact PresheafOfModules.naturality_apply f.val a.op m }
  left_inv φ := rfl
  right_inv f := by ext V m; rfl

namespace HomOn

variable {M' : X.Modules}

/-- Precomposition of a local morphism by a morphism of module sheaves. -/
def precomp (f : M' ⟶ M) {U : Opens X} (φ : HomOn M N U) : HomOn M' N U where
  app V hV := (φ.app V hV).comp (f.val.app (op V)).hom
  naturality hWV hV m := by
    simp only [LinearMap.comp_apply]
    erw [PresheafOfModules.naturality_apply]
    exact φ.naturality hWV hV (f.val.app _ m)

@[simp] lemma precomp_app (f : M' ⟶ M) {U : Opens X} (φ : HomOn M N U)
    (V : Opens X) (hV : V ≤ U) (m : M'.presheaf.obj (op V)) :
    (φ.precomp f).app V hV m = φ.app V hV (f.val.app (op V) m) := rfl

@[simp] lemma precomp_add (f : M' ⟶ M) {U : Opens X} (φ ψ : HomOn M N U) :
    (φ + ψ).precomp f = φ.precomp f + ψ.precomp f := rfl

lemma precomp_smul (f : M' ⟶ M) {U : Opens X} (r : X.presheaf.obj (op U))
    (φ : HomOn M N U) : (r • φ).precomp f = r • φ.precomp f := by
  ext V hV m
  rfl

variable {U : Opens X} (φ : HomOn M N U) (x : X) (hxU : x ∈ U)

/-- A local morphism maps germs at a point of its domain into the skyscraper of the
target stalk. Intersecting an arbitrary open with its domain makes this a global map. -/
def toStalkSkyscraper : M ⟶ skyscraper x ((stalkFunctor x).obj N) := ⟨{
  app V := ModuleCat.ofHom
    (R := X.presheaf.obj V)
    (X := M.val.obj V)
    (Y := skyscraperSections x ((stalkFunctor x).obj N) V.unop)
    { toFun := fun m hxV ↦ N.presheaf.germ (V.unop ⊓ U) x ⟨hxV.down, hxU⟩
        (φ.app (V.unop ⊓ U) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m))
      map_add' := fun _ _ ↦ by funext hxV; erw [map_add, map_add, map_add]; rfl
      map_smul' := fun r m ↦ by
        funext hxV
        change N.presheaf.germ (V.unop ⊓ U) x ⟨hxV.down, hxU⟩
          (φ.app (V.unop ⊓ U) inf_le_right
            (M.presheaf.map (homOfLE inf_le_left).op (r • m))) =
          X.presheaf.germ V.unop x hxV.down r •
            N.presheaf.germ (V.unop ⊓ U) x ⟨hxV.down, hxU⟩
              (φ.app (V.unop ⊓ U) inf_le_right
                (M.presheaf.map (homOfLE inf_le_left).op m))
        rw [Modules.map_smul, LinearMap.map_smul, germ_smul, X.presheaf.germ_res_apply] }
  naturality {V W} i := by
    ext m
    funext hxW
    change N.presheaf.germ (W.unop ⊓ U) x ⟨hxW.down, hxU⟩
      (φ.app (W.unop ⊓ U) inf_le_right
        (M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map i m))) =
      N.presheaf.germ (V.unop ⊓ U) x ⟨i.unop.le hxW.down, hxU⟩
        (φ.app (V.unop ⊓ U) inf_le_right
          (M.presheaf.map (homOfLE inf_le_left).op m))
    erw [presheaf_map_map M (homOfLE inf_le_left) i.unop
      (homOfLE (inf_le_inf_right U i.unop.le)) (homOfLE inf_le_left),
      φ.naturality, N.presheaf.germ_res_apply] }⟩

/-- The linear map on stalks induced by a local morphism. -/
def stalkMap : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  (fromSkyscraper x (φ.toStalkSkyscraper x hxU)).hom

lemma stalkMap_germ {V : Opens X} (hVU : V ≤ U) (hxV : x ∈ V)
    (m : M.presheaf.obj (op V)) :
    φ.stalkMap x hxU (M.presheaf.germ V x hxV m) =
      N.presheaf.germ V x hxV (φ.app V hVU m) := by
  change fromSkyscraperAddHom x (φ.toStalkSkyscraper x hxU)
    (M.presheaf.germ V x hxV m) = _
  rw [fromSkyscraperAddHom_germ]
  change N.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩
    (φ.app (V ⊓ U) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m)) = _
  rw [φ.naturality (inf_le_left : V ⊓ U ≤ V) hVU, N.presheaf.germ_res_apply]

lemma stalkMap_restrict {V : Opens X} (hVU : V ≤ U) (hxV : x ∈ V) :
    (φ.restrict hVU).stalkMap x hxV = φ.stalkMap x hxU := by
  apply LinearMap.ext
  intro m
  obtain ⟨W, hWV, hxW, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxV
  rw [stalkMap_germ _ _ _ hWV, stalkMap_germ _ _ _ (hWV.trans hVU)]
  rfl

@[simp] lemma stalkMap_zero : (0 : HomOn M N U).stalkMap x hxU = 0 := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [stalkMap_germ _ _ _ hVU]
  simp only [zero_app, LinearMap.zero_apply, map_zero]

@[simp] lemma stalkMap_add (ψ : HomOn M N U) :
    (φ + ψ).stalkMap x hxU = φ.stalkMap x hxU + ψ.stalkMap x hxU := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [LinearMap.add_apply, stalkMap_germ _ _ _ hVU,
    stalkMap_germ _ _ _ hVU, stalkMap_germ _ _ _ hVU]
  simp only [add_app, LinearMap.add_apply, map_add]

lemma stalkMap_smul (r : X.presheaf.obj (op U)) :
    (r • φ).stalkMap x hxU =
      @HSMul.hSMul (X.presheaf.stalk x)
        (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x)
        (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) inferInstance
        (X.presheaf.germ U x hxU r) (φ.stalkMap x hxU) := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [LinearMap.smul_apply, stalkMap_germ _ _ _ hVU, stalkMap_germ _ _ _ hVU,
    smul_app, LinearMap.smul_apply, germ_smul, X.presheaf.germ_res_apply]

lemma stalkMap_precomp (f : M' ⟶ M) :
    (φ.precomp f).stalkMap x hxU = (φ.stalkMap x hxU).comp (Modules.stalkMap f x) := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M'.presheaf.exists_le_germ_eq m hxU
  rw [LinearMap.comp_apply, Modules.stalkMap_germ, stalkMap_germ _ _ _ hVU,
    stalkMap_germ _ _ _ hVU]
  rfl

end HomOn

/-- Contravariance of the Hom sheaf in its source. -/
def sheafHomPrecomp {M' : X.Modules} (f : M' ⟶ M) (N : X.Modules) :
    sheafHom M N ⟶ sheafHom M' N := ⟨{
  app U := ModuleCat.ofHom {
    toFun := fun φ ↦ φ.precomp f
    map_add' := HomOn.precomp_add f
    map_smul' := HomOn.precomp_smul f }
  naturality i := by ext φ; rfl }⟩

@[simp] lemma sheafHomPrecomp_app {M' : X.Modules} (f : M' ⟶ M) (N : X.Modules)
    (U : Opens X) (φ : HomOn M N U) :
    (sheafHomPrecomp f N).val.app (op U) φ = φ.precomp f := rfl

lemma homOnOverEquiv_precomp {M' : X.Modules} (f : M' ⟶ M) (U : Opens X)
    (φ : HomOn M N U) :
    homOnOverEquiv U (φ.precomp f) = f.over U ≫ homOnOverEquiv U φ := by
  ext V m
  rfl

variable (M N) (x : X)

/-- Maps on stalks form a cocone on the neighbourhood diagram of the Hom sheaf. -/
def homStalkCocone : Cocone ((OpenNhds.inclusion x).op ⋙ (sheafHom M N).presheaf) where
  pt := AddCommGrpCat.of (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x)
  ι := {
    app U := AddCommGrpCat.ofHom {
      toFun := fun φ ↦ φ.stalkMap x U.unop.2
      map_zero' := HomOn.stalkMap_zero x U.unop.2
      map_add' := fun φ ψ ↦ HomOn.stalkMap_add φ x U.unop.2 ψ }
    naturality {U V} i := by
      ext φ
      exact HomOn.stalkMap_restrict φ x U.unop.2 i.unop.le V.unop.2 }

/-- The map from germs of local morphisms to homomorphisms of stalks, as an additive map. -/
def homStalkAddHom : (sheafHom M N).presheaf.stalk x →+
    (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :=
  (colimit.desc _ (homStalkCocone M N x)).hom

@[simp] lemma homStalkAddHom_germ (U : Opens X) (hx : x ∈ U) (φ : HomOn M N U) :
    homStalkAddHom M N x ((sheafHom M N).presheaf.germ U x hx φ) = φ.stalkMap x hx :=
  ConcreteCategory.congr_hom (colimit.ι_desc (homStalkCocone M N x) (op ⟨U, hx⟩)) φ

/-- Evaluation on germs gives the canonical linear map
`Hom(M,N)_x → Hom(M_x,N_x)`. -/
def homStalkMap : (sheafHom M N).presheaf.stalk x →ₗ[X.presheaf.stalk x]
    (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) where
  toFun := homStalkAddHom M N x
  map_add' := map_add _
  map_smul' r φ := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, φ, rfl⟩ := (sheafHom M N).presheaf.exists_le_germ_eq φ hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r, ← germ_smul]
    erw [homStalkAddHom_germ, homStalkAddHom_germ]
    exact HomOn.stalkMap_smul φ x hxV (X.presheaf.map (homOfLE hVU).op r)

@[simp] lemma homStalkMap_germ (U : Opens X) (hx : x ∈ U) (φ : HomOn M N U) :
    homStalkMap M N x ((sheafHom M N).presheaf.germ U x hx φ) = φ.stalkMap x hx :=
  homStalkAddHom_germ M N x U hx φ

lemma homStalkMap_precomp {M' : X.Modules} (f : M' ⟶ M)
    (s : (sheafHom M N).presheaf.stalk x) :
    homStalkMap M' N x (stalkMap (sheafHomPrecomp f N) x s) =
      (homStalkMap M N x s).comp (stalkMap f x) := by
  obtain ⟨U, hxU, φ, rfl⟩ := (sheafHom M N).presheaf.exists_germ_eq s
  rw [stalkMap_germ, sheafHomPrecomp_app, homStalkMap_germ,
    homStalkMap_germ, HomOn.stalkMap_precomp]

end AlgebraicGeometry.LocallyRingedSpace.Modules
