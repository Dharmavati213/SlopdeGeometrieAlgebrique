/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.AlgebraAlgebraization
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale


/-!
# The relative spectrum of a quasi-coherent algebra

For a quasi-coherent `𝒪_X`-module `B` with a commutative algebra structure (`ModuleAlgebra`), the
sections over each open form a commutative `Γ(X, U)`-algebra (`ModuleAlgebra.Sections`), and over
the affine opens they form a presheaf of rings satisfying `Γ(B, D(f)) = Γ(B, U)[1/f]`
(`ModuleAlgebra.coequifibered`). Mathlib's relative gluing then produces the relative spectrum
`Spec_X B` (`ModuleAlgebra.relativeSpec`, EGA II 1.3.1; Stacks 01LL) with its affine structure
morphism `Spec_X B ⟶ X`.

* `ModuleAlgebra.relativeSpecHom_of`: properties local at the target hold for `Spec_X B ⟶ X` as
  soon as they hold for the `Spec Γ(B, U) ⟶ Spec Γ(X, U)`;
* `IsFinite` for `B` of finite type, `ModuleAlgebra.etale_relativeSpecHom`;
* `ModuleAlgebra.sectionsIso`, `ModuleAlgebra.relativeSpecHom_app`: the sections of `Spec_X B`
  over the inverse image of an affine open `U` are `Γ(B, U)`, as a `Γ(X, U)`-algebra.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

variable {X : Scheme.{u}}

section MulApp

variable {M : X.Modules} (m : M ⟶ sheafHom M M) (U : X.Opens)

lemma mulApp_add_left (x x' y : Γ(M, U)) :
    mulApp m U (x + x') y = mulApp m U x y + mulApp m U x' y := by
  unfold mulApp
  rw [map_add]
  rfl

lemma mulApp_add_right (x y y' : Γ(M, U)) :
    mulApp m U x (y + y') = mulApp m U x y + mulApp m U x y' :=
  map_add _ _ _

lemma mulApp_smul_left (r : Γ(X, U)) (x y : Γ(M, U)) :
    mulApp m U (r • x) y = r • mulApp m U x y := by
  unfold mulApp
  rw [Scheme.Modules.Hom.app_smul]
  change X.presheaf.map (homOfLE (le_refl U)).op r •
      ((m.app U x : Γ(sheafHom M M, U)) : HomOn M M U).app U le_rfl y =
    r • ((m.app U x : Γ(sheafHom M M, U)) : HomOn M M U).app U le_rfl y
  rw [presheaf_map_self]

lemma mulApp_smul_right (r : Γ(X, U)) (x y : Γ(M, U)) :
    mulApp m U x (r • y) = r • mulApp m U x y :=
  LinearMap.map_smul _ _ _

lemma mulApp_zero_left (y : Γ(M, U)) : mulApp m U 0 y = 0 := by
  have := mulApp_add_left m U 0 0 y
  rw [add_zero] at this
  exact left_eq_add.mp this

lemma mulApp_zero_right (x : Γ(M, U)) : mulApp m U x 0 = 0 :=
  map_zero _

end MulApp

variable {B : X.Modules} (algB : ModuleAlgebra B)

namespace ModuleAlgebra

/-- The unit section over `U`. -/
def oneApp (U : X.Opens) : Γ(B, U) := B.presheaf.map (homOfLE le_top).op algB.one

/-- The sections of `B` over `U`, with the ring structure given by `algB`. -/
@[nolint unusedArguments]
def Sections (_algB : ModuleAlgebra B) (U : X.Opens) : Type u := Γ(B, U)

instance (U : X.Opens) : AddCommGroup (algB.Sections U) :=
  inferInstanceAs (AddCommGroup Γ(B, U))

instance (U : X.Opens) : CommRing (algB.Sections U) where
  __ := (inferInstance : AddCommGroup (algB.Sections U))
  mul x y := mulApp algB.mul U x y
  one := algB.oneApp U
  mul_assoc x y z := algB.mul_assoc U x y z
  mul_comm x y := algB.mul_comm U x y
  one_mul x := algB.one_mul U x
  mul_one x := (algB.mul_comm U _ _).trans (algB.one_mul U x)
  zero_mul x := mulApp_zero_left algB.mul U x
  mul_zero x := mulApp_zero_right algB.mul U x
  left_distrib x y z := mulApp_add_right algB.mul U x y z
  right_distrib x y z := mulApp_add_left algB.mul U x y z

end ModuleAlgebra

namespace ModuleAlgebra

instance (U : X.Opens) : Module Γ(X, U) (algB.Sections U) :=
  inferInstanceAs (Module Γ(X, U) Γ(B, U))

instance (U : X.Opens) : Algebra Γ(X, U) (algB.Sections U) :=
  Algebra.ofModule (fun r x y ↦ mulApp_smul_left algB.mul U r x y)
    (fun r x y ↦ mulApp_smul_right algB.mul U r x y)

lemma mul_def (U : X.Opens) (x y : algB.Sections U) : x * y = mulApp algB.mul U x y := rfl

lemma one_def (U : X.Opens) : (1 : algB.Sections U) = algB.oneApp U := rfl

lemma algebraMap_def (U : X.Opens) (r : Γ(X, U)) :
    algebraMap Γ(X, U) (algB.Sections U) r = r • (1 : algB.Sections U) := rfl

/-- Restriction of sections, as a ring homomorphism. -/
def resRingHom {U V : X.Opens} (h : V ≤ U) : algB.Sections U →+* algB.Sections V where
  toFun x := B.presheaf.map (homOfLE h).op x
  map_one' := by
    change B.presheaf.map (homOfLE h).op (B.presheaf.map (homOfLE le_top).op algB.one) =
      B.presheaf.map (homOfLE le_top).op algB.one
    rw [modules_map_map_apply B (homOfLE h) (homOfLE le_top) (homOfLE le_top)]
  map_mul' x y := mulApp_res algB.mul h x y
  map_zero' := map_zero _
  map_add' := map_add _

lemma resRingHom_apply {U V : X.Opens} (h : V ≤ U) (x : algB.Sections U) :
    algB.resRingHom h x = B.presheaf.map (homOfLE h).op x := rfl

lemma resRingHom_algebraMap {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    algB.resRingHom h (algebraMap Γ(X, U) (algB.Sections U) r) =
      algebraMap Γ(X, V) (algB.Sections V) (X.presheaf.map (homOfLE h).op r) := by
  rw [algebraMap_def, algebraMap_def, resRingHom_apply]
  change B.presheaf.map (homOfLE h).op (r • (algB.oneApp U : Γ(B, U))) =
    X.presheaf.map (homOfLE h).op r • (algB.oneApp V : Γ(B, V))
  rw [Scheme.Modules.map_smul]
  congr 1
  exact (algB.resRingHom h).map_one

/-- The presheaf of rings `U ↦ Γ(B, U)` on the affine opens of `X`. -/
def ringFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (algB.Sections U.unop.toOpens)
  map f := CommRingCat.ofHom (algB.resRingHom
    (Scheme.AffineZariskiSite.toOpens_mono f.unop.le))
  map_id U := by
    ext x
    exact modules_map_self B _ x
  map_comp f g := by
    ext x
    exact (modules_map_map_apply B _ _ _ x).symm

/-- The structure morphism `𝒪_X ⟶ B` on affine opens. -/
def ringFunctorι : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶
    algB.ringFunctor where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.toOpens) (algB.Sections U.unop.toOpens))
  naturality U V f := by
    ext r
    exact (algB.resRingHom_algebraMap _ r).symm

lemma mul_algebraMap (U : X.Opens) (c : Γ(X, U)) (s : algB.Sections U) :
    s * algebraMap Γ(X, U) (algB.Sections U) c = c • s := by
  rw [Algebra.smul_def, _root_.mul_comm]

variable [B.IsQuasicoherent]

/-- `B` is a quasi-coherent algebra: `Γ(B, D(f)) = Γ(B, U)[1/f]`. -/
lemma coequifibered : algB.ringFunctorι.Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  let ρ := algB.resRingHom (X.basicOpen_le f)
  let _ : Algebra (algB.Sections U.toOpens) (algB.Sections (X.basicOpen f)) := ρ.toAlgebra
  change IsLocalization.Away (algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) f)
    (algB.Sections (X.basicOpen f))
  have hα : ρ (algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) f) =
      algebraMap Γ(X, X.basicOpen f) (algB.Sections (X.basicOpen f))
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    algB.resRingHom_algebraMap (X.basicOpen_le f) f
  have hpow : ∀ k : ℕ, ρ (algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) f) ^ k =
      algebraMap Γ(X, X.basicOpen f) (algB.Sections (X.basicOpen f))
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k)) := by
    intro k
    rw [hα, ← map_pow]
    congr 1
    exact (map_pow _ f k).symm
  refine IsLocalization.Away.mk _ ?_ (fun s ↦ ?_) (fun a b hab ↦ ?_)
  · change IsUnit (ρ _)
    rw [hα]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).map _
  · obtain ⟨m, k, hmk⟩ := exists_pow_smul_eq_map B U.2 f s
    refine ⟨k, m, ?_⟩
    change s * ρ _ ^ k = ρ m
    rw [hpow, mul_algebraMap]
    exact hmk
  · change ρ a = ρ b at hab
    have h0 : ρ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero B U.2 f (a - b) h0
    refine ⟨k, ?_⟩
    have e1 : ∀ x : algB.Sections U.toOpens,
        algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) f ^ k * x = f ^ k • x := fun x ↦ by
      rw [← map_pow, _root_.mul_comm, mul_algebraMap]
    rw [e1, e1, ← sub_eq_zero, ← smul_sub]
    exact hk

/-- **The relative spectrum** `Spec_X B` of a quasi-coherent commutative `𝒪_X`-algebra
(EGA II 1.3.1; Stacks 01LL), glued from the `Spec Γ(B, U)` over the affine opens `U`. -/
abbrev relativeSpec : Scheme.{u} :=
  (Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered).glued

/-- The structure morphism `Spec_X B ⟶ X`. -/
abbrev relativeSpecHom : algB.relativeSpec ⟶ X :=
  (Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered).toBase

/-- A property of morphisms local at the target holds for `Spec_X B ⟶ X` as soon as it holds for
the `Spec Γ(B, U) ⟶ Spec Γ(X, U)`, `U` affine. -/
theorem relativeSpecHom_of {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    (H : ∀ U : X.AffineZariskiSite, P (Spec.map (algB.ringFunctorι.app (op U)))) :
    P algB.relativeSpecHom := by
  let d := Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : X.AffineZariskiSite ↦ U.toOpens)
    (by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩) fun U ↦ ?_
  have h₁ := d.isPullback_natTrans_ι_toBase U
  have h₂ := isPullback_morphismRestrict d.toBase U.toOpens
  have : IsIso ((Scheme.AffineZariskiSite.restrictIsoSpec X).inv.app U) :=
    (inferInstance : IsIso ((Scheme.AffineZariskiSite.restrictIsoSpec X).app U).inv)
  have hP : P (d.natTrans.app U) := by
    change P (Spec.map (algB.ringFunctorι.app (op U)) ≫
      (Scheme.AffineZariskiSite.restrictIsoSpec X).inv.app U)
    rw [P.cancel_right_of_respectsIso]
    exact H U
  refine (P.arrow_mk_iso_iff (Arrow.isoMk (h₁.isoIsPullback _ _ h₂) (Iso.refl _) ?_)).mp hP
  simp only [Iso.refl_hom, Category.comp_id]
  exact IsPullback.isoIsPullback_hom_fst _ _ h₁ h₂

set_option backward.isDefEq.respectTransparency.types false in
instance : IsAffineHom algB.relativeSpecHom :=
  algB.relativeSpecHom_of (P := @IsAffineHom) fun _ ↦ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- `Spec_X B ⟶ X` is finite for `B` of finite type. -/
instance [B.IsFiniteType] : IsFinite algB.relativeSpecHom :=
  algB.relativeSpecHom_of (P := @IsFinite) fun U ↦ by
    rw [IsFinite.SpecMap_iff]
    have : Module.Finite Γ(X, U.toOpens) (algB.Sections U.toOpens) :=
      finite_sections_of_isFiniteType B U.2
    exact RingHom.finite_algebraMap.mpr this

set_option backward.isDefEq.respectTransparency.types false in
/-- `Spec_X B ⟶ X` is étale if the algebras of sections over affine opens are étale. -/
theorem etale_relativeSpecHom
    (h : ∀ U : X.AffineZariskiSite, Algebra.Etale Γ(X, U.toOpens) (algB.Sections U.toOpens)) :
    Etale algB.relativeSpecHom :=
  algB.relativeSpecHom_of (P := @Etale) fun U ↦ by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr (h U)

instance : ((Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered).functor ⋙
    Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The open cover of `Spec_X B` by the `Spec Γ(B, U)`, `U` affine. -/
abbrev relativeSpecCover : algB.relativeSpec.OpenCover :=
  (Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered).cover

@[reassoc]
lemma relativeSpecCover_map {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (algB.resRingHom
      (Scheme.AffineZariskiSite.toOpens_mono i.le))) ≫ algB.relativeSpecCover.f V =
        algB.relativeSpecCover.f U :=
  colimit.w (Scheme.AffineZariskiSite.relativeGluingData algB.coequifibered).functor i

@[reassoc]
lemma ι_relativeSpecHom (U : X.AffineZariskiSite) :
    algB.relativeSpecCover.f U ≫ algB.relativeSpecHom =
      Spec.map (algB.ringFunctorι.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma relativeSpecHom_preimage (U : X.AffineZariskiSite) :
    algB.relativeSpecHom ⁻¹ᵁ U.toOpens = (algB.relativeSpecCover.f U).opensRange := by
  simpa using! (Scheme.AffineZariskiSite.relativeGluingData
    algB.coequifibered).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of `Spec_X B` over the inverse image of an affine open `U` are `Γ(B, U)`. -/
def sectionsIso (U : X.AffineZariskiSite) :
    Γ(algB.relativeSpec, algB.relativeSpecHom ⁻¹ᵁ U.toOpens) ≅
      CommRingCat.of (algB.Sections U.toOpens) :=
  algB.relativeSpec.presheaf.mapIso (eqToIso
    (by simpa using! (algB.relativeSpecHom_preimage U).symm)).op ≪≫
  (algB.relativeSpecCover.f U).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma relativeSpecHom_app (U : X.AffineZariskiSite) :
    algB.relativeSpecHom.app U.toOpens = CommRingCat.ofHom (algebraMap _ _) ≫
      (algB.sectionsIso U).inv := by
  have : IsIso ((algB.relativeSpecCover.f U).app (algB.relativeSpecHom ⁻¹ᵁ U.toOpens)) :=
    Scheme.Hom.isIso_app _ _ (by rw [algB.relativeSpecHom_preimage U])
  have H : ⊤ = (algB.relativeSpecCover.f U ≫ algB.relativeSpecHom) ⁻¹ᵁ U.toOpens := by
    rw [algB.ι_relativeSpecHom]; simp
  rw [← cancel_mono ((algB.relativeSpecCover.f U).app (algB.relativeSpecHom ⁻¹ᵁ U.toOpens)),
    ← Scheme.Hom.comp_app, Scheme.Hom.congr_app (algB.ι_relativeSpecHom U) U.toOpens,
    ← cancel_mono ((algB.relativeSpecCover.X U).presheaf.map (eqToHom H).op)]
  dsimp [sectionsIso]
  rw [IsAffineOpen.fromSpec_app_self]
  simp only [Scheme.Hom.app_eq_appLE, Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  simp [Scheme.Hom.appLE, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end ModuleAlgebra

end AlgebraicGeometry.CohomologyAux

