/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Modules
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Stalks and inverse images of module sheaves

Stalks of module sheaves carry their natural module structure over the stalk of the
structure sheaf. The stalk functor is left adjoint to skyscraper modules. Direct image
of skyscrapers restricts scalars along the stalk map; uniqueness of left adjoints then
gives a natural isomorphism
`(f* M)_x ≅ 𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)}` for every module sheaf.

This is the inverse-image stalk formula of the theory of ringed spaces used in Serre,
*Géométrie algébrique et géométrie analytique*, §2 (Stacks Project, Tag 0096 for skyscrapers;
EGA 0_I 5.3.1 for the stalks of an inverse image). Adopted from the unmerged branch
`codex/foundations-missing-inputs` (commit `c65c9a0`, file `ModuleStalk.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

/-- Extensionality for morphisms of `𝒪_X`-modules (`X.Modules` is not reducible to
`SheafOfModules`, so mathlib's extensionality lemma is restated). -/
@[ext]
lemma hom_ext {M N : X.Modules} {f g : M ⟶ N} (h : f.val = g.val) : f = g :=
  SheafOfModules.hom_ext h

/-- The underlying presheaf of abelian groups of a module sheaf. -/
abbrev presheaf (M : X.Modules) : TopCat.Presheaf AddCommGrpCat.{u} X.toSheafedSpace  :=
  M.val.presheaf

instance moduleSections (M : X.Modules) (U : Opens X) :
    Module (X.presheaf.obj (op U)) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

instance modulePresheafSections (M : X.Modules) (U : Opens X) :
    Module (X.presheaf.obj (op U)) (M.presheaf.obj (op U)) := moduleSections M U

/-- The underlying morphism of presheaves of abelian groups. -/
abbrev mapPresheaf {M N : X.Modules} (f : M ⟶ N) : M.presheaf ⟶ N.presheaf :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val

/-- The stalk of a module sheaf is a module over the stalk of the structure sheaf. -/
instance moduleStalk (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x

lemma germ_smul (M : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (r : X.presheaf.obj (op U)) (m : M.val.obj (op U)) :
    M.presheaf.germ U x hx (r • m) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val x U hx r m

/-- The map on stalks induced by a morphism of module sheaves is linear. -/
def stalkMap {M N : X.Modules} (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (mapPresheaf f)
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r, ← germ_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (mapPresheaf f)]
    change N.presheaf.germ V x hxV
      (f.val.app (op V) (X.presheaf.map (homOfLE hVU).op r • m)) = _
    rw [map_smul, germ_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV (mapPresheaf f)]
    rfl

@[simp] lemma stalkMap_germ {M N : X.Modules} (f : M ⟶ N) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    stalkMap f x (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (f.val.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (mapPresheaf f) m

/-- Taking the stalk of a module sheaf as a module over the local ring. -/
def stalkFunctor (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map f := ModuleCat.ofHom (stalkMap f x)
  map_id M := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := M.presheaf.exists_germ_eq m
    change stalkMap (𝟙 M) x (M.presheaf.germ U x hx m) = M.presheaf.germ U x hx m
    erw [stalkMap_germ]
    rfl
  map_comp {M N P} f g := by
    ext m
    obtain ⟨U, hx, m, rfl⟩ := M.presheaf.exists_germ_eq m
    change stalkMap (f ≫ g) x (M.presheaf.germ U x hx m) =
      stalkMap g x (stalkMap f x (M.presheaf.germ U x hx m))
    erw [stalkMap_germ, stalkMap_germ, stalkMap_germ]
    rfl

instance skyscraperSectionsModule (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : Opens X) :
    Module (X.presheaf.obj (op U)) (PLift (x ∈ U) → N) where
  smul r s hx := X.presheaf.germ U x hx.down r • s hx
  one_smul s := by funext hx; change X.presheaf.germ U x hx.down 1 • s hx = _; simp
  mul_smul r t s := by
    funext hx
    change X.presheaf.germ U x hx.down (r * t) • s hx =
      X.presheaf.germ U x hx.down r • (X.presheaf.germ U x hx.down t • s hx)
    simp [mul_smul]
  smul_add r s t := by funext hx; exact smul_add _ _ _
  smul_zero r := by funext hx; exact smul_zero _
  add_smul r t s := by
    funext hx
    change X.presheaf.germ U x hx.down (r + t) • s hx =
      X.presheaf.germ U x hx.down r • s hx + X.presheaf.germ U x hx.down t • s hx
    simp [add_smul]
  zero_smul s := by funext hx; change X.presheaf.germ U x hx.down 0 • s hx = _; simp

/-- Sections of a skyscraper module on an open set. -/
abbrev skyscraperSections (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : Opens X) :
    ModuleCat.{u} (X.presheaf.obj (op U)) := ModuleCat.of _ (PLift (x ∈ U) → N)

instance skyscraperSectionsModuleOp (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (Opens X)ᵒᵖ) : Module (X.presheaf.obj U) (PLift (x ∈ U.unop) → N) :=
  skyscraperSectionsModule x N U.unop

/-- A skyscraper module, before verifying the sheaf condition. -/
def skyscraperPresheaf (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    PresheafOfModules X.ringCatSheaf.obj where
  obj U := skyscraperSections x N U.unop
  map {U V} i := ModuleCat.ofHom
    (X := skyscraperSections x N U.unop)
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (skyscraperSections x N V.unop))
    { toFun := fun s hx ↦ s ⟨i.unop.le hx.down⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ by
        funext hx
        change X.presheaf.germ U.unop x (i.unop.le hx.down) r • s ⟨i.unop.le hx.down⟩ =
          X.presheaf.germ V.unop x hx.down (X.presheaf.map i r) • s ⟨i.unop.le hx.down⟩
        erw [X.presheaf.germ_res_apply i.unop x hx.down r] }
  map_id U := by ext s; rfl
  map_comp i j := by ext s; rfl

/-- Skyscraper modules satisfy the sheaf condition. -/
lemma skyscraperPresheaf_isSheaf (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf.IsSheaf (X := X.toSheafedSpace) (skyscraperPresheaf x N).presheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U s hs
  let chooseIndex (h : x ∈ iSup U) : ι := (Opens.mem_iSup.mp h).choose
  have hchoose (h : x ∈ iSup U) : x ∈ U (chooseIndex h) := (Opens.mem_iSup.mp h).choose_spec
  let t : PLift (x ∈ iSup U) → N := fun h ↦ s (chooseIndex h.down) ⟨hchoose h.down⟩
  have ht : ∀ i (hi : x ∈ U i), t ⟨Opens.mem_iSup.mpr ⟨i, hi⟩⟩ = s i ⟨hi⟩ := by
    intro i hi
    exact congrFun (hs (chooseIndex (Opens.mem_iSup.mpr ⟨i, hi⟩)) i)
      ⟨⟨hchoose (Opens.mem_iSup.mpr ⟨i, hi⟩), hi⟩⟩
  refine ⟨t, ?_, ?_⟩
  · intro i
    funext hi
    exact ht i hi.down
  · intro t' ht'
    funext h
    exact congrFun (ht' (chooseIndex h.down)) ⟨hchoose h.down⟩

/-- A skyscraper sheaf of modules with prescribed value at a point. -/
def skyscraper (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules :=
  ⟨skyscraperPresheaf x N, skyscraperPresheaf_isSheaf x N⟩

/-- Skyscraper modules are functorial in the module over the local ring. -/
def skyscraperFunctor (x : X) : ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj := skyscraper x
  map {M N} f := ⟨{
    app U := ModuleCat.ofHom
      (X := skyscraperSections x M U.unop) (Y := skyscraperSections x N U.unop)
      { toFun := fun s hx ↦ f (s hx)
        map_add' := fun _ _ ↦ by ext; simp
        map_smul' := fun r s ↦ by
          funext hx
          exact f.hom.map_smul (X.presheaf.germ U.unop x hx.down r) (s hx) }
    naturality i := by ext s; rfl }⟩
  map_id N := by ext U s; rfl
  map_comp f g := by ext U s; rfl

variable (x : X)

/-- A linear map out of a stalk induces a morphism to the skyscraper module. -/
def toSkyscraper {M : X.Modules} {N : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : (stalkFunctor x).obj M ⟶ N) : M ⟶ skyscraper x N := ⟨{
  app U := ModuleCat.ofHom
    (R := X.presheaf.obj U)
    (X := M.val.obj U) (Y := skyscraperSections x N U.unop)
    { toFun := fun m hx ↦ f (M.presheaf.germ U.unop x hx.down m)
      map_add' := fun _ _ ↦ by funext hx; simp
      map_smul' := fun r m ↦ by
        funext hx
        change f (M.presheaf.germ U.unop x hx.down (r • m)) =
          X.presheaf.germ U.unop x hx.down r • f (M.presheaf.germ U.unop x hx.down m)
        rw [germ_smul, map_smul] }
  naturality {U V} i := by
    ext m
    funext hx
    change f (M.presheaf.germ V.unop x hx.down (M.val.map i m)) =
      f (M.presheaf.germ U.unop x (i.unop.le hx.down) m)
    congr 1
    exact M.presheaf.germ_res_apply i.unop x hx.down m }⟩

/-- The cocone obtained by evaluating a morphism to a skyscraper on neighbourhoods. -/
def fromSkyscraperCocone {M : X.Modules} {N : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : M ⟶ skyscraper x N) : Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι := {
    app U := AddCommGrpCat.ofHom
      { toFun := fun m ↦ (f.val.app (op U.unop.1) m) ⟨U.unop.2⟩
        map_zero' := by change (f.val.app _ 0) _ = 0; simp only [map_zero]; rfl
        map_add' := fun _ _ ↦ by change (f.val.app _ (_ + _)) _ = _; simp only [map_add]; rfl }
    naturality {U V} i := by
      ext m
      exact congrFun (PresheafOfModules.naturality_apply f.val ((OpenNhds.inclusion x).op.map i) m)
        ⟨V.unop.2⟩ }

/-- The additive map from a stalk induced by a morphism to a skyscraper. -/
def fromSkyscraperAddHom {M : X.Modules} {N : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : M ⟶ skyscraper x N) : M.presheaf.stalk x →+ N :=
  (colimit.desc _ (fromSkyscraperCocone x f)).hom

@[simp] lemma fromSkyscraperAddHom_germ {M : X.Modules}
    {N : ModuleCat.{u} (X.presheaf.stalk x)} (f : M ⟶ skyscraper x N)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    fromSkyscraperAddHom x f (M.presheaf.germ U x hx m) = f.val.app (op U) m ⟨hx⟩ :=
  ConcreteCategory.congr_hom (colimit.ι_desc (fromSkyscraperCocone x f) (op ⟨U, hx⟩)) m

/-- A morphism to a skyscraper induces a linear map out of the stalk. -/
def fromSkyscraper {M : X.Modules} {N : ModuleCat.{u} (X.presheaf.stalk x)}
    (f : M ⟶ skyscraper x N) : (stalkFunctor x).obj M ⟶ N := ModuleCat.ofHom {
  toFun := fromSkyscraperAddHom x f
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r, ← germ_smul]
    erw [fromSkyscraperAddHom_germ, fromSkyscraperAddHom_germ]
    exact congrFun ((f.val.app (op V)).hom.map_smul
      (X.presheaf.map (homOfLE hVU).op r) m) ⟨hxV⟩ }

/-- The stalk-skyscraper adjunction on morphisms of module sheaves. -/
def stalkSkyscraperHomEquiv (M : X.Modules) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((stalkFunctor x).obj M ⟶ N) ≃ (M ⟶ (skyscraperFunctor x).obj N) where
  toFun := toSkyscraper x
  invFun := fromSkyscraper x
  left_inv f := by
    ext m
    obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
    exact fromSkyscraperAddHom_germ x (toSkyscraper x f) U hxU m
  right_inv f := by
    ext U m
    funext hx
    exact fromSkyscraperAddHom_germ x f U.unop hx.down m

/-- The stalk functor is left adjoint to the skyscraper functor for module sheaves. -/
def stalkSkyscraperAdjunction : stalkFunctor x ⊣ skyscraperFunctor x :=
  Adjunction.mkOfHomEquiv {
    homEquiv := stalkSkyscraperHomEquiv x
    homEquiv_naturality_left_symm := by
      intro M M' N f h
      ext m
      obtain ⟨U, hxU, m, rfl⟩ := M.presheaf.exists_germ_eq m
      change fromSkyscraperAddHom x (f ≫ h) (M.presheaf.germ U x hxU m) =
        fromSkyscraperAddHom x h (stalkMap f x (M.presheaf.germ U x hxU m))
      erw [fromSkyscraperAddHom_germ, stalkMap_germ, fromSkyscraperAddHom_germ]
      rfl
    homEquiv_naturality_right := by
      intro M N N' f h
      ext U m
      funext hx
      rfl }

instance : (stalkFunctor x).IsLeftAdjoint := (stalkSkyscraperAdjunction x).isLeftAdjoint

instance : (skyscraperFunctor x).IsRightAdjoint := (stalkSkyscraperAdjunction x).isRightAdjoint

variable {Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- Direct image of a skyscraper restricts its local-ring scalars along the stalk map. -/
def pushforwardSkyscraperIso (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (pushforward f).obj (skyscraper x N) ≅
      skyscraper (f.base x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) where
  hom := ⟨{
    app U := ModuleCat.ofHom
      (X := ((pushforward f).obj (skyscraper x N)).val.obj U)
      (Y := (skyscraper (f.base x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).val.obj U)
      { toFun := fun s ↦ s
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r s ↦ by
          funext hx
          change X.presheaf.germ ((Opens.map f.base).obj U.unop) x hx.down
            (f.c.app U r) • s hx =
            f.stalkMap x (Y.presheaf.germ U.unop (f.base x) hx.down r) • s hx
          rw [LocallyRingedSpace.stalkMap_germ_apply] }
    naturality i := by ext s; rfl }⟩
  inv := ⟨{
    app U := ModuleCat.ofHom
      (X := (skyscraper (f.base x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).val.obj U)
      (Y := ((pushforward f).obj (skyscraper x N)).val.obj U)
      { toFun := fun s ↦ s
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r s ↦ by
          funext hx
          change f.stalkMap x (Y.presheaf.germ U.unop (f.base x) hx.down r) • s hx =
            X.presheaf.germ ((Opens.map f.base).obj U.unop) x hx.down (f.c.app U r) • s hx
          rw [LocallyRingedSpace.stalkMap_germ_apply] }
    naturality i := by ext s; rfl }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

/-- The skyscraper comparison is natural in the local module. -/
def pushforwardSkyscraperNatIso :
    skyscraperFunctor x ⋙ pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ skyscraperFunctor (f.base x) :=
  NatIso.ofComponents (pushforwardSkyscraperIso x f) (fun h ↦ by ext U s; rfl)

/-- Taking a stalk of an inverse image is extension of scalars along the local-ring map.
This is a natural isomorphism for all sheaves of modules, with no coherence or flatness
assumption. -/
def pullbackStalkIso :
    pullback f ⋙ stalkFunctor x ≅
      stalkFunctor (f.base x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  Adjunction.leftAdjointUniq
    (((pullbackPushforwardAdjunction f).comp (stalkSkyscraperAdjunction x)).ofNatIsoRight
      (pushforwardSkyscraperNatIso x f))
    ((stalkSkyscraperAdjunction (f.base x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))

/-- The stalk of the inverse image of a module sheaf is its scalar extension from the
target local ring to the source local ring. -/
def pullbackStalkModuleIso (M : Y.Modules) :
    (stalkFunctor x).obj ((pullback f).obj M) ≅
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj ((stalkFunctor (f.base x)).obj M) :=
  (pullbackStalkIso x f).app M

open TensorProduct in
/-- The inverse-image stalk formula as an explicit linear equivalence with a tensor
product. The algebra structure on the source local ring is induced by the stalk map. -/
def pullbackStalkLinearEquiv (M : Y.Modules) :
    letI := (f.stalkMap x).hom.toAlgebra
    ((pullback f).obj M).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x ⊗[Y.presheaf.stalk (f.base x)] M.presheaf.stalk (f.base x) := by
  letI := (f.stalkMap x).hom.toAlgebra
  exact (pullbackStalkModuleIso x f M).toLinearEquiv

end AlgebraicGeometry.LocallyRingedSpace.Modules
