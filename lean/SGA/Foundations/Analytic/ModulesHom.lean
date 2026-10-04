/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesStalk
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Hom sheaves on locally ringed spaces

For module sheaves `M` and `N`, the sheaf `sheafHom M N` has on each open set `U`
the compatible families of linear maps on sections over all opens contained in `U`.
These are the morphisms of their restrictions to `U`. The sheaf condition is proved
by gluing sections of `N`; global sections identify with morphisms `M ⟶ N`.

This is the internal Hom construction for ringed spaces (EGA 0_I, 4.1.1;
Stacks Project, Tag 01CM) used in coherent analytification.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHom.lean`).
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

/-- Sections of a module sheaf on an open set, as an abelian group. -/
abbrev moduleSectionsObj {X : LocallyRingedSpace.{u}} (M : X.Modules) (U : Opens X) :=
  M.presheaf.obj (op U)

local notation3 "Γₘ(" M ", " U ")" => moduleSectionsObj M U

instance {X : LocallyRingedSpace.{u}} (M : X.Modules) (U : Opens X) :
    Module (X.presheaf.obj (op U)) Γₘ(M, U) := modulePresheafSections M U

@[simp] lemma map_smul {X : LocallyRingedSpace.{u}} (M : X.Modules) {U V : Opens X}
    (i : U ⟶ V) (r : X.presheaf.obj (op V)) (m : Γₘ(M, V)) :
    M.presheaf.map i.op (r • m) =
      @HSMul.hSMul (X.presheaf.obj (op U)) Γₘ(M, U) Γₘ(M, U) inferInstance
      (X.presheaf.map i.op r) (M.presheaf.map i.op m) :=
  M.val.map_smul _ _ _

lemma presheaf_map_injective_of_eq {X : LocallyRingedSpace.{u}} (M : X.Modules)
    {W W' : Opens X} (i : W ⟶ W') (h : W = W') : Function.Injective (M.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 W), op_id, M.presheaf.map_id]
  exact Function.injective_id

lemma presheaf_map_map {X : LocallyRingedSpace.{u}} (M : X.Modules) {A B C D : Opens X}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ D) (g' : D ⟶ C) (m : Γₘ(M, C)) :
    M.presheaf.map f.op (M.presheaf.map g.op m) =
      M.presheaf.map f'.op (M.presheaf.map g'.op m) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (f ≫ g) (f' ≫ g')]

variable {X : LocallyRingedSpace.{u}} (M N : X.Modules)

/-- The `𝒪_U`-linear maps `M|_U → N|_U`, as compatible families of section-linear maps
`Γₘ(M, V) → Γₘ(N, V)` for the opens `V ⊆ U`. -/
@[ext]
structure HomOn (U : (Opens X)) where
  /-- The linear map on sections over `V ⊆ U`. -/
  app (V : (Opens X)) (hV : V ≤ U) : Γₘ(M, V) →ₗ[(X.presheaf.obj (op V))] Γₘ(N, V)
  naturality {V W : (Opens X)} (hWV : W ≤ V) (hV : V ≤ U) (m : Γₘ(M, V)) :
    app W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op m) =
      N.presheaf.map (homOfLE hWV).op (app V hV m)

namespace HomOn

variable {M N} {U : (Opens X)}

instance : Zero (HomOn M N U) where
  zero := ⟨fun _ _ ↦ 0, fun _ _ _ ↦ by simp only [LinearMap.zero_apply, map_zero]⟩

instance : Add (HomOn M N U) where
  add φ ψ := ⟨fun V hV ↦ φ.app V hV + ψ.app V hV, fun hWV hV m ↦ by
    rw [LinearMap.add_apply, LinearMap.add_apply, φ.naturality, ψ.naturality, map_add]⟩

instance : Neg (HomOn M N U) where
  neg φ := ⟨fun V hV ↦ -φ.app V hV, fun hWV hV m ↦ by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, φ.naturality, map_neg]⟩

instance : Sub (HomOn M N U) where
  sub φ ψ := ⟨fun V hV ↦ φ.app V hV - ψ.app V hV, fun hWV hV m ↦ by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, φ.naturality, ψ.naturality, map_sub]⟩

instance : SMul ℕ (HomOn M N U) where
  smul n φ := ⟨fun V hV ↦ n • φ.app V hV, fun hWV hV m ↦ by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.naturality, map_nsmul]⟩

instance : SMul ℤ (HomOn M N U) where
  smul n φ := ⟨fun V hV ↦ n • φ.app V hV, fun hWV hV m ↦ by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.naturality, map_zsmul]⟩

@[simp] lemma zero_app (V : (Opens X)) (hV : V ≤ U) : (0 : HomOn M N U).app V hV = 0 := rfl
@[simp] lemma add_app (φ ψ : HomOn M N U) (V : (Opens X)) (hV : V ≤ U) :
    (φ + ψ).app V hV = φ.app V hV + ψ.app V hV := rfl
@[simp] lemma neg_app (φ : HomOn M N U) (V : (Opens X)) (hV : V ≤ U) :
    (-φ).app V hV = -φ.app V hV := rfl
@[simp] lemma sub_app (φ ψ : HomOn M N U) (V : (Opens X)) (hV : V ≤ U) :
    (φ - ψ).app V hV = φ.app V hV - ψ.app V hV := rfl

/-- The underlying family of linear maps, indexed by the opens contained in `U`. -/
def toFamily (φ : HomOn M N U) :
    ∀ V : {V : Opens X // V ≤ U}, Γₘ(M, V.1) →ₗ[X.presheaf.obj (op V.1)] Γₘ(N, V.1) :=
  fun V ↦ φ.app V.1 V.2

lemma toFamily_injective : Function.Injective (toFamily (M := M) (N := N) (U := U)) :=
  fun _ _ h ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦ congr_fun h ⟨V, hV⟩)

instance : AddCommGroup (HomOn M N U) :=
  toFamily_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : SMul (X.presheaf.obj (op U)) (HomOn M N U) where
  smul r φ := ⟨fun V hV ↦ @HSMul.hSMul (X.presheaf.obj (op V))
    (Γₘ(M, V) →ₗ[X.presheaf.obj (op V)] Γₘ(N, V))
    (Γₘ(M, V) →ₗ[X.presheaf.obj (op V)] Γₘ(N, V)) inferInstance
    (X.presheaf.map (homOfLE hV).op r) (φ.app V hV), fun hWV hV m ↦ by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, φ.naturality,
      ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl⟩

@[simp] lemma smul_app (r : X.presheaf.obj (op U)) (φ : HomOn M N U)
    (V : Opens X) (hV : V ≤ U) :
    (r • φ).app V hV = @HSMul.hSMul (X.presheaf.obj (op V))
    (Γₘ(M, V) →ₗ[X.presheaf.obj (op V)] Γₘ(N, V))
    (Γₘ(M, V) →ₗ[X.presheaf.obj (op V)] Γₘ(N, V)) inferInstance
    (X.presheaf.map (homOfLE hV).op r) (φ.app V hV) := rfl

instance : Module (X.presheaf.obj (op U)) (HomOn M N U) where
  one_smul φ := by ext V hV m; simp
  mul_smul r s φ := by ext V hV m; simp [mul_smul]
  smul_zero r := by ext V hV m; simp; rfl
  smul_add r φ ψ := by ext V hV m; simp
  add_smul r s φ := by ext V hV m; simp [add_smul]
  zero_smul φ := by ext V hV m; simp; rfl

/-- The restriction of `φ : HomOn M N U` to an open `U' ⊆ U`. -/
@[simps]
def restrict (φ : HomOn M N U) {U' : (Opens X)} (h : U' ≤ U) : HomOn M N U' where
  app V hV := φ.app V (hV.trans h)
  naturality hWV hV m := φ.naturality hWV (hV.trans h) m

@[simp] lemma restrict_add (φ ψ : HomOn M N U) {U' : (Opens X)} (h : U' ≤ U) :
    (φ + ψ).restrict h = φ.restrict h + ψ.restrict h := rfl

lemma restrict_smul (r : (X.presheaf.obj (op U))) (φ : HomOn M N U) {U' : (Opens X)} (h : U' ≤ U) :
    (r • φ).restrict h =
      @HSMul.hSMul (X.presheaf.obj (op U')) (HomOn M N U') (HomOn M N U') inferInstance
      (X.presheaf.map (homOfLE h).op r) (φ.restrict h) := by
  ext V hV m
  simp only [restrict_app, smul_app, LinearMap.smul_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end HomOn

instance (U : (Opens X)ᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) (HomOn M N U.unop) :=
  inferInstanceAs (Module (X.presheaf.obj (op U.unop)) _)

/-- The presheaf of modules `U ↦ Hom_{𝒪_U}(M|_U, N|_U)`. -/
def homPresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj U := ModuleCat.of (X.ringCatSheaf.obj.obj U) (HomOn M N U.unop)
  map {_ U'} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj U') (HomOn M N U'.unop)))
    { toFun φ := φ.restrict i.unop.le
      map_add' _ _ := rfl
      map_smul' r φ := HomOn.restrict_smul r φ i.unop.le }
  map_id _ := rfl
  map_comp _ _ := rfl

variable {M N}

/-- Gluing of sections of `N` over the members `V ⊓ U i` of an open cover of `V`. -/
lemma existsUnique_gluing_inf {ι : Type u} (U : ι → (Opens X)) {V : (Opens X)} (hV : V ≤ iSup U)
    (t : ∀ i, Γₘ(N, V ⊓ U i))
    (ht : ∀ i j, N.presheaf.map (homOfLE (inf_le_left : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ _)).op (t i) =
      N.presheaf.map (homOfLE (inf_le_right : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ _)).op (t j)) :
    ∃! s : Γₘ(N, V), ∀ i, N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s = t i := by
  refine TopCat.Sheaf.existsUnique_gluing' (F := ⟨N.presheaf, N.isSheaf⟩) (U := fun i ↦ V ⊓ U i)
    V (fun i ↦ homOfLE inf_le_left) ?_ t ht
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hV

namespace HomOn

variable {ι : Type u} {U : ι → (Opens X)} (φ : ∀ i, HomOn M N (U i))
  (hφ : ∀ i j, (φ i).restrict (inf_le_left : U i ⊓ U j ≤ U i) =
    (φ j).restrict (inf_le_right : U i ⊓ U j ≤ U j))

include hφ in
lemma existsUnique_glue_app (V : (Opens X)) (hV : V ≤ iSup U) (m : Γₘ(M, V)) :
    ∃! s : Γₘ(N, V), ∀ i, N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s =
      (φ i).app (V ⊓ U i) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m) := by
  refine existsUnique_gluing_inf U hV _ fun i j ↦ ?_
  rw [← (φ i).naturality, ← (φ j).naturality, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  have h := congr(HomOn.app $(hφ i j) ((V ⊓ U i) ⊓ (V ⊓ U j))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
  exact congr($h (M.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op m))

/-- The glued section. -/
def glueApp (V : (Opens X)) (hV : V ≤ iSup U) (m : Γₘ(M, V)) : Γₘ(N, V) :=
  (existsUnique_glue_app φ hφ V hV m).exists.choose

lemma glueApp_spec (V : (Opens X)) (hV : V ≤ iSup U) (m : Γₘ(M, V)) (i : ι) :
    N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (glueApp φ hφ V hV m) =
      (φ i).app (V ⊓ U i) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m) :=
  (existsUnique_glue_app φ hφ V hV m).exists.choose_spec i

lemma glueApp_eq (V : (Opens X)) (hV : V ≤ iSup U) (m : Γₘ(M, V)) (s : Γₘ(N, V))
    (hs : ∀ i, N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s =
      (φ i).app (V ⊓ U i) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m)) :
    glueApp φ hφ V hV m = s :=
  (existsUnique_glue_app φ hφ V hV m).unique (fun i ↦ glueApp_spec φ hφ V hV m i) hs

/-- The gluing of a compatible family of `HomOn M N (U i)`. -/
def glue : HomOn M N (iSup U) where
  app V hV :=
    { toFun := glueApp φ hφ V hV
      map_add' m m' := glueApp_eq φ hφ V hV _ _ fun i ↦ by
        rw [map_add, glueApp_spec, glueApp_spec, map_add, map_add]
      map_smul' r m := glueApp_eq φ hφ V hV _ _ fun i ↦ by
        rw [RingHom.id_apply, map_smul, glueApp_spec, map_smul,
          LinearMap.map_smul] }
  naturality {V W} hWV hV m := by
    refine glueApp_eq φ hφ W (hWV.trans hV) _ _ fun i ↦ ?_
    change N.presheaf.map (homOfLE inf_le_left).op
      (N.presheaf.map (homOfLE hWV).op (glueApp φ hφ V hV m)) = _
    rw [presheaf_map_map N _ _ (homOfLE (inf_le_inf_right (U i) hWV)) (homOfLE inf_le_left),
      glueApp_spec, ← (φ i).naturality (inf_le_inf_right (U i) hWV),
      presheaf_map_map M (homOfLE (inf_le_left : W ⊓ U i ≤ W)) (homOfLE hWV)
        (homOfLE (inf_le_inf_right (U i) hWV)) (homOfLE inf_le_left)]

lemma glue_restrict (i : ι) : (glue φ hφ).restrict (le_iSup U i) = φ i := by
  ext V hV m
  change glueApp φ hφ V (hV.trans (le_iSup U i)) m = _
  have e : V ⊓ U i = V := inf_eq_left.mpr hV
  apply presheaf_map_injective_of_eq N (homOfLE (inf_le_left : V ⊓ U i ≤ V)) e
  rw [glueApp_spec, ← (φ i).naturality]

end HomOn

variable (M N) in
/-- The presheaf `U ↦ Hom_{𝒪_U}(M|_U, N|_U)` is a sheaf. -/
lemma isSheaf_homPresheaf : TopCat.Presheaf.IsSheaf (homPresheaf M N).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hφ (i j : ι) : (sf i).restrict (inf_le_left : U i ⊓ U j ≤ U i) =
      (sf j).restrict (inf_le_right : U i ⊓ U j ≤ U j) := hsf i j
  refine ⟨HomOn.glue sf hφ, fun i ↦ HomOn.glue_restrict sf hφ i, fun t ht ↦ ?_⟩
  have ht' (i : ι) : t.restrict (le_iSup U i) = sf i := ht i
  refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦ ?_)
  refine (HomOn.glueApp_eq sf hφ V hV m _ fun i ↦ ?_).symm
  rw [← t.naturality, ← ht' i]
  rfl

variable (M N) in
/-- The sheaf `ℋom(M, N)` of `𝒪_X`-linear maps between two `𝒪_X`-modules
(EGA 0_I 4.1.1; Stacks Project, Tag 01CM). -/
def sheafHom : X.Modules where
  val := homPresheaf M N
  isSheaf := isSheaf_homPresheaf M N

/-- The sections of `ℋom(M, N)` over `U` are the `𝒪_U`-linear maps `M|_U → N|_U`. -/
def sheafHomSectionsEquiv (U : Opens X) :
    Γₘ(sheafHom M N, U) ≃ₗ[X.presheaf.obj (op U)] HomOn M N U :=
  LinearEquiv.refl _ _

/-- `𝒪_X`-linear maps `M|_⊤ → N|_⊤` are the morphisms `M ⟶ N`. -/
def homOnTopEquiv : HomOn M N ⊤ ≃ (M ⟶ N) where
  toFun φ :=
    { val := PresheafOfModules.homMk
        { app U := AddCommGrpCat.ofHom (φ.app U.unop le_top).toAddMonoidHom
          naturality U V i := by
            ext m
            exact φ.naturality i.unop.le le_top m }
        fun U r m ↦ (φ.app U.unop le_top).map_smul r m }
  invFun α :=
    { app V _ :=
        { toFun := α.val.app (op V)
          map_add' := map_add _
          map_smul' := (α.val.app (op V)).hom.map_smul }
      naturality {V W} hWV _ m := congr($((mapPresheaf α).naturality (homOfLE hWV).op) m) }
  left_inv φ := rfl
  right_inv α := rfl

@[simp]
lemma homOnTopEquiv_app (φ : HomOn M N ⊤) (U : (Opens X)) (m : Γₘ(M, U)) :
    (homOnTopEquiv φ).val.app (op U) m = φ.app U le_top m :=
  rfl

@[simp]
lemma homOnTopEquiv_symm_app (α : M ⟶ N) (U : (Opens X)) (m : Γₘ(M, U)) :
    (homOnTopEquiv.symm α).app U le_top m = α.val.app (op U) m :=
  rfl

/-- The global sections of `ℋom(M, N)` are the morphisms `M ⟶ N`. -/
def sheafHomTopEquiv : Γₘ(sheafHom M N, ⊤) ≃ (M ⟶ N) :=
  homOnTopEquiv

end AlgebraicGeometry.LocallyRingedSpace.Modules
