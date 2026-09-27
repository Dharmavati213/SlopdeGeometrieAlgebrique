/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.RelativeSpec


/-!
# The direct image algebra and the universal property of the relative spectrum

For a morphism of schemes `g : Z ⟶ X`, `g_* 𝒪_Z` is an `𝒪_X`-algebra (`pushforwardAlgebra`) whose
sections over `U` are the ring `Γ(Z, g⁻¹ U)` (`pushforwardAlgebraSectionsEquiv`). An algebra
morphism `φ : B ⟶ g_* 𝒪_Z` (multiplicative and unital on sections) defines a morphism
`toRelativeSpec : Z ⟶ Spec_X B` over `X` (`toRelativeSpec_relativeSpecHom`), glued from the
`g⁻¹ U ⟶ Spec Γ(Z, g⁻¹ U) ⟶ Spec Γ(B, U)`, `U` affine (EGA II 1.2.7; Stacks 01LQ). It is an
isomorphism when `g` is affine and the ring maps `Γ(B, U) → Γ(Z, g⁻¹ U)` are bijective
(`isIso_toRelativeSpec`); in particular every affine morphism is the relative spectrum of its
direct image algebra (`isIso_toRelativeSpec_pushforwardAlgebra`; EGA II 1.3.7).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

variable {X Z : Scheme.{u}} (g : Z ⟶ X)

/-- The direct image `g_* 𝒪_Z`. -/
abbrev pushforwardUnit : X.Modules := (Scheme.Modules.pushforward g).obj (unitModule Z)

/-- Sections of `g_* 𝒪_Z` as sections of `𝒪_Z`. -/
abbrev pushforwardUnitEquiv {V : X.Opens} : Γ(pushforwardUnit g, V) ≃ Γ(Z, g ⁻¹ᵁ V) := Equiv.refl _

lemma pushforwardUnit_smul {V : X.Opens} (r : Γ(X, V)) (y : Γ(pushforwardUnit g, V)) :
    pushforwardUnitEquiv g (r • y) = g.app V r * pushforwardUnitEquiv g y := rfl

lemma pushforwardUnit_map {V W : X.Opens} (h : W ≤ V) (y : Γ(pushforwardUnit g, V)) :
    pushforwardUnitEquiv g ((pushforwardUnit g).presheaf.map (homOfLE h).op y) =
      Z.presheaf.map (homOfLE (g.preimage_mono h)).op (pushforwardUnitEquiv g y) := rfl

/-- The ring structure: `x * y` for sections of `g_* 𝒪_Z` over `V`. -/
def pfMul {V : X.Opens} (x y : Γ(pushforwardUnit g, V)) : Γ(pushforwardUnit g, V) :=
  (pushforwardUnitEquiv g).symm (pushforwardUnitEquiv g x * pushforwardUnitEquiv g y)

lemma pfMul_res {V W : X.Opens} (h : W ≤ V) (x y : Γ(pushforwardUnit g, V)) :
    (pushforwardUnit g).presheaf.map (homOfLE h).op (pfMul g x y) =
      pfMul g ((pushforwardUnit g).presheaf.map (homOfLE h).op x)
        ((pushforwardUnit g).presheaf.map (homOfLE h).op y) :=
  (Z.presheaf.map (homOfLE (g.preimage_mono h)).op).hom.map_mul _ _

/-- Multiplication by `x`, a section of `ℋom(g_* 𝒪_Z, g_* 𝒪_Z)` over `U`. -/
def pfMulHomOn {U : X.Opens} (x : Γ(pushforwardUnit g, U)) :
    HomOn (pushforwardUnit g) (pushforwardUnit g) U where
  app V hV :=
    { toFun := fun y ↦ pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op x) y
      map_add' := fun y y' ↦ mul_add (pushforwardUnitEquiv g
        ((pushforwardUnit g).presheaf.map (homOfLE hV).op x)) (pushforwardUnitEquiv g y)
          (pushforwardUnitEquiv g y')
      map_smul' := fun r y ↦ mul_left_comm (pushforwardUnitEquiv g
        ((pushforwardUnit g).presheaf.map (homOfLE hV).op x)) (g.app V r)
          (pushforwardUnitEquiv g y) }
  naturality {V W} hWV hV y := by
    change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE (hWV.trans hV)).op x)
        ((pushforwardUnit g).presheaf.map (homOfLE hWV).op y) =
      (pushforwardUnit g).presheaf.map (homOfLE hWV).op
        (pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op x) y)
    rw [pfMul_res, modules_map_map_apply (pushforwardUnit g) (homOfLE hWV) (homOfLE hV)
      (homOfLE (hWV.trans hV))]

/-- The multiplication `g_* 𝒪_Z ⟶ ℋom(g_* 𝒪_Z, g_* 𝒪_Z)`. -/
def pfMulHom : pushforwardUnit g ⟶ sheafHom (pushforwardUnit g) (pushforwardUnit g) :=
  ⟨_root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun x : Γ(pushforwardUnit g, U.unop) ↦ pfMulHomOn g x
          map_zero' := HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun y ↦ by
            change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op 0) y = 0
            rw [map_zero]
            exact zero_mul (pushforwardUnitEquiv g y))
          map_add' := fun (x x' : Γ(pushforwardUnit g, U.unop)) ↦ HomOn.ext (funext fun V ↦
            funext fun hV ↦ LinearMap.ext fun y ↦ by
              change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op (x + x')) y =
                pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op x) y +
                  pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op x') y
              rw [map_add]
              exact add_mul _ _ (pushforwardUnitEquiv g y)) }
      naturality U U' i := by
        ext (x : Γ(pushforwardUnit g, U.unop))
        refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun y ↦ ?_)
        change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op
            ((pushforwardUnit g).presheaf.map (homOfLE i.unop.le).op x)) y =
          pfMul g ((pushforwardUnit g).presheaf.map (homOfLE (hV.trans i.unop.le)).op x) y
        rw [modules_map_map_apply (pushforwardUnit g) (homOfLE hV) (homOfLE i.unop.le)
          (homOfLE (hV.trans i.unop.le))] }
    fun U (r : Γ(X, U.unop)) (x : Γ(pushforwardUnit g, U.unop)) ↦ HomOn.ext (funext fun V ↦
      funext fun hV ↦ LinearMap.ext fun y ↦ by
        change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op (r • x)) y =
          X.presheaf.map (homOfLE hV).op r •
            pfMul g ((pushforwardUnit g).presheaf.map (homOfLE hV).op x) y
        rw [Scheme.Modules.map_smul]
        exact mul_assoc _ _ (pushforwardUnitEquiv g y))⟩

lemma mulApp_pfMulHom (U : X.Opens) (x y : Γ(pushforwardUnit g, U)) :
    mulApp (pfMulHom g) U x y = pfMul g x y := by
  change pfMul g ((pushforwardUnit g).presheaf.map (homOfLE le_rfl).op x) y = _
  rw [modules_map_self]

/-- **The algebra `g_* 𝒪_Z`** of a morphism of schemes `g : Z ⟶ X`. -/
def pushforwardAlgebra : ModuleAlgebra (pushforwardUnit g) where
  mul := pfMulHom g
  one := (pushforwardUnitEquiv g).symm 1
  mul_comm U x y := by
    rw [mulApp_pfMulHom, mulApp_pfMulHom]
    exact mul_comm (pushforwardUnitEquiv g x) (pushforwardUnitEquiv g y)
  mul_assoc U x y z := by
    rw [mulApp_pfMulHom, mulApp_pfMulHom, mulApp_pfMulHom, mulApp_pfMulHom]
    exact mul_assoc (pushforwardUnitEquiv g x) (pushforwardUnitEquiv g y)
      (pushforwardUnitEquiv g z)
  one_mul U x := by
    rw [mulApp_pfMulHom]
    change (Z.presheaf.map (homOfLE (g.preimage_mono le_top)).op 1 : Γ(Z, g ⁻¹ᵁ U)) *
      pushforwardUnitEquiv g x = pushforwardUnitEquiv g x
    rw [map_one, one_mul]

/-- The sections of `g_* 𝒪_Z` over `U`, with the ring structure of `pushforwardAlgebra g`, are
the ring `Γ(Z, g⁻¹ U)`. -/
def pushforwardAlgebraSectionsEquiv (U : X.Opens) :
    (pushforwardAlgebra g).Sections U ≃+* Γ(Z, g ⁻¹ᵁ U) where
  toFun x := pushforwardUnitEquiv g x
  invFun y := (pushforwardUnitEquiv g).symm y
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := congrArg (pushforwardUnitEquiv g) (mulApp_pfMulHom g U x y)
  map_add' _ _ := rfl

section ToRelativeSpec

variable {B : X.Modules} [B.IsQuasicoherent] (algB : ModuleAlgebra B) {g}
  (φ : B ⟶ pushforwardUnit g)
  (hmul : ∀ (U : X.Opens) (x y : Γ(B, U)),
    φ.app U (mulApp algB.mul U x y) = pfMul g (φ.app U x) (φ.app U y))
  (hone : φ.app ⊤ algB.one = (pushforwardUnitEquiv g).symm 1)

include hmul hone in
/-- The ring homomorphisms `Γ(B, U) → Γ(Z, g⁻¹ U)` of an algebra morphism `B ⟶ g_* 𝒪_Z`. -/
def algHomApp (U : X.Opens) : algB.Sections U →+* Γ(Z, g ⁻¹ᵁ U) where
  toFun (x : Γ(B, U)) := pushforwardUnitEquiv g (φ.app U x)
  map_mul' (x y : Γ(B, U)) := congrArg (pushforwardUnitEquiv g) (hmul U x y)
  map_one' := by
    change pushforwardUnitEquiv g (φ.app U (B.presheaf.map (homOfLE le_top).op algB.one)) = 1
    rw [hom_app_presheaf_map, hone]
    exact (Z.presheaf.map _).hom.map_one
  map_zero' := congrArg (pushforwardUnitEquiv g) (φ.app U).hom.map_zero
  map_add' (x y : Γ(B, U)) := congrArg (pushforwardUnitEquiv g) ((φ.app U).hom.map_add x y)

omit [B.IsQuasicoherent] in
lemma algHomApp_apply (U : X.Opens) (x : Γ(B, U)) :
    algHomApp algB φ hmul hone U x = pushforwardUnitEquiv g (φ.app U x) := rfl

omit [B.IsQuasicoherent] in
lemma algHomApp_res {U V : X.Opens} (h : V ≤ U) (x : Γ(B, U)) :
    algHomApp algB φ hmul hone V (algB.resRingHom h x) =
      Z.presheaf.map (homOfLE (g.preimage_mono h)).op (algHomApp algB φ hmul hone U x) := by
  change pushforwardUnitEquiv g (φ.app V (B.presheaf.map (homOfLE h).op x)) = _
  rw [hom_app_presheaf_map]
  rfl

omit [B.IsQuasicoherent] in
lemma algHomApp_algebraMap (U : X.Opens) (r : Γ(X, U)) :
    algHomApp algB φ hmul hone U (algebraMap Γ(X, U) (algB.Sections U) r) = g.app U r := by
  change pushforwardUnitEquiv g (φ.app U (r • (algB.oneApp U : Γ(B, U)))) = _
  rw [Scheme.Modules.Hom.app_smul, pushforwardUnit_smul]
  change g.app U r * algHomApp algB φ hmul hone U 1 = _
  rw [map_one, mul_one]

open Scheme.AffineZariskiSite in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The universal property of `Spec_X B`**: an algebra morphism `B ⟶ g_* 𝒪_Z` defines a
morphism `Z ⟶ Spec_X B`. -/
def toRelativeSpec : Z ⟶ algB.relativeSpec :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover X).pullback₁ g)
    (fun U ↦ (pullbackRestrictIsoRestrict g _).hom ≫ (g ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (algHomApp algB φ hmul hone U.1)) ≫
        algB.relativeSpecCover.f U) fun {U V : X.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict g U.1).inv ≫
      Scheme.Cover.trans ((directedCover X).pullback₁ g) i ≫
      (pullbackRestrictIsoRestrict g V.1).hom = Z.homOfLE
        (g.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc, ← algB.relativeSpecCover_map i, ← Spec.map_comp_assoc]
  congr 3
  ext x
  exact (algHomApp_res algB φ hmul hone (toOpens_mono i.1.1) x).symm

open Scheme.AffineZariskiSite in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_toRelativeSpec (U : X.AffineZariskiSite) :
    (g ⁻¹ᵁ U.1).ι ≫ toRelativeSpec algB φ hmul hone = (g ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (algHomApp algB φ hmul hone U.1)) ≫
        algB.relativeSpecCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict g U.1).hom, ← Category.assoc]
  trans ((directedCover X).pullback₁ g).f U ≫ toRelativeSpec algB φ hmul hone
  · congr 1; simp
  delta toRelativeSpec
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toRelativeSpec_relativeSpecHom :
    toRelativeSpec algB φ hmul hone ≫ algB.relativeSpecHom = g := by
  refine Scheme.Cover.hom_ext (Z.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top X) g.base.1)) _ _ fun U ↦ ?_
  refine (ι_toRelativeSpec_assoc algB φ hmul hone U _).trans ?_
  rw [ModuleAlgebra.ι_relativeSpecHom, ← Spec.map_comp_assoc]
  have e : algB.ringFunctorι.app (op U) ≫ CommRingCat.ofHom (algHomApp algB φ hmul hone U.1) =
      g.app U.1 := by
    ext r
    exact algHomApp_algebraMap algB φ hmul hone U.1 r
  rw [e]
  change (g ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (g.app _) ≫ U.2.fromSpec = (g ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **An algebra isomorphism gives an isomorphism with the relative spectrum**: if the ring maps
`Γ(B, U) → Γ(Z, g⁻¹ U)` are bijective for all affine `U` (and `g` is affine), then
`Z ⟶ Spec_X B` is an isomorphism. -/
theorem isIso_toRelativeSpec [IsAffineHom g]
    (hbij : ∀ U : X.AffineZariskiSite, Function.Bijective (algHomApp algB φ hmul hone U.1)) :
    IsIso (toRelativeSpec algB φ hmul hone) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    algB.relativeSpecCover).mpr fun U ↦ ?_
  have hpre : (toRelativeSpec algB φ hmul hone) ⁻¹ᵁ (algB.relativeSpecCover.f U).opensRange =
      g ⁻¹ᵁ U.1 := by
    rw [← algB.relativeSpecHom_preimage U, ← Scheme.Hom.comp_preimage,
      toRelativeSpec_relativeSpecHom]
  have hrange : Set.range (pullback.fst (toRelativeSpec algB φ hmul hone)
      (algB.relativeSpecCover.f U)) = Set.range (g ⁻¹ᵁ U.1).ι := by
    have h := congrArg (fun W : Z.Opens ↦ (W : Set Z))
      (show (pullback.fst (toRelativeSpec algB φ hmul hone)
        (algB.relativeSpecCover.f U)).opensRange = (g ⁻¹ᵁ U.1).ι.opensRange by
          rw [Scheme.Hom.opensRange_pullbackFst, hpre, Scheme.Opens.opensRange_ι])
    simpa only [Scheme.Hom.coe_opensRange] using h
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (toRelativeSpec algB φ hmul hone)
    (algB.relativeSpecCover.f U)) (g ⁻¹ᵁ U.1).ι hrange
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _)
    (e ≪≫ (U.2.preimage g).isoSpec).inv]
  convert_to! IsIso (Spec.map (CommRingCat.ofHom (algHomApp algB φ hmul hone U.1)))
  · rw [← cancel_mono (algB.relativeSpecCover.f U), ← cancel_epi (U.2.preimage g).isoSpec.hom]
    change (U.2.preimage g).isoSpec.hom ≫ (e ≪≫ (U.2.preimage g).isoSpec).inv ≫
        pullback.snd _ _ ≫ algB.relativeSpecCover.f U =
      (U.2.preimage g).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algHomApp algB φ hmul hone U.1)) ≫ algB.relativeSpecCover.f U
    rw [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc, ← pullback.condition,
      IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, ι_toRelativeSpec, IsAffineOpen.isoSpec_hom]
  exact (Scheme.Spec.mapIso (RingEquiv.ofBijective _ (hbij U)).toCommRingCatIso.op).isIso_hom

end ToRelativeSpec

section AffineIsRelativeSpec

variable [IsAffineHom g]

instance : (pushforwardUnit g).IsQuasicoherent := isQuasicoherent_pushforward g (unitModule Z)

omit [IsAffineHom g] in
lemma pushforwardAlgebra_hmul (U : X.Opens) (x y : Γ(pushforwardUnit g, U)) :
    (𝟙 (pushforwardUnit g) : pushforwardUnit g ⟶ _).app U
        (mulApp (pushforwardAlgebra g).mul U x y) =
      pfMul g ((𝟙 (pushforwardUnit g) : pushforwardUnit g ⟶ _).app U x)
        ((𝟙 (pushforwardUnit g) : pushforwardUnit g ⟶ _).app U y) :=
  mulApp_pfMulHom g U x y

/-- **An affine morphism is the relative spectrum of its direct image algebra**: for `g : Z ⟶ X`
affine, `Z ≅ Spec_X (g_* 𝒪_Z)` over `X` (EGA II 1.3.7; Stacks 01S8). -/
theorem isIso_toRelativeSpec_pushforwardAlgebra :
    IsIso (toRelativeSpec (pushforwardAlgebra g) (𝟙 _) (pushforwardAlgebra_hmul g) rfl) :=
  isIso_toRelativeSpec _ _ _ _ fun U ↦ (pushforwardAlgebraSectionsEquiv g U.1).bijective

end AffineIsRelativeSpec

end AlgebraicGeometry.CohomologyAux
