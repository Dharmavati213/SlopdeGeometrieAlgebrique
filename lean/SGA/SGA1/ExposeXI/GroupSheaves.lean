/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import SGA.SGA1.ExposeVIII.QuasiCoherentDescent
import SGA.SGA1.ExposeXI.AbelianH1

/-!
# SGA 1, Exposé XI, §4–§6: the additive and multiplicative groups as fpqc sheaves

For a scheme `S`, the category `Over S` of `S`-schemes with the fpqc topology is the site on
which the principal homogeneous bundles of XI.4.1 are the torsors (`SGA.Foundations.Etale`), and
`H¹(S, G)` is the set of classes of torsors under `G` (XI.4.4; for affine `G` this is the
notation of SGA 4, see footnote 296 of XI.4.4). This file defines the fpqc sheaves of groups
represented by `𝔾_{a,S}` and `𝔾_{m,S}` (XI.5.1):

* `Ga S`: `T ↦ Γ(T, 𝒪_T)` (written multiplicatively, `Multiplicative Γ(T, 𝒪_T)`), and
  `Gm S`: `T ↦ Γ(T, 𝒪_T)ˣ`, with their sheaf property (`isSheaf_Ga`, `isSheaf_Gm`), from the
  fact that `Γ` is an fpqc sheaf (VIII.1.7, `isSheaf_fpqcTopology_Γ`);
* `mem_fpqcTopology_of_affine`: a sieve on a scheme `X` is an fpqc covering as soon as every
  morphism `Spec A ⟶ X` becomes a member after a faithfully flat extension `A → B`. This is the
  form in which fpqc-local surjectivity of the Kummer and Artin–Schreier maps is proved in
  `KummerCohomology` and `ArtinSchreierCohomology`;
* `exists_fpqc_cover_of_affine`: its form on the site `Over S`.

The global sections of these sheaves over the final object `S` of `Over S` are
`H⁰(S, 𝒪_S) = Γ(S, 𝒪_S)` and `H⁰(S, 𝒪_S^*) = Γ(S, 𝒪_S)ˣ`.
-/

universe u

open CategoryTheory Opposite Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

/-- XI.4.1: a sieve on a scheme `X` is an fpqc covering if every morphism `Spec A ⟶ X` belongs to
it after some faithfully flat extension `A → B`. -/
theorem mem_fpqcTopology_of_affine {X : Scheme.{u}} (R : Sieve X)
    (H : ∀ (A : CommRingCat.{u}) (g : Spec A ⟶ X), ∃ (B : CommRingCat.{u}) (φ : A ⟶ B),
      φ.hom.FaithfullyFlat ∧ R.arrows (Spec.map φ ≫ g)) :
    R ∈ Scheme.fpqcTopology X := by
  let 𝒰 := X.affineCover
  have h𝒰 : Sieve.generate 𝒰.presieve₀ ∈ Scheme.fpqcTopology X :=
    Precoverage.generate_mem_toGrothendieck (Scheme.zariskiPrecoverage_le_fpqcPrecoverage X 𝒰.mem₀)
  refine GrothendieckTopology.transitive _ h𝒰 R fun Y f hf ↦ ?_
  obtain ⟨Z, h, g, hg, rfl⟩ := hf
  obtain ⟨i⟩ := hg
  rw [Sieve.pullback_comp]
  refine GrothendieckTopology.pullback_stable _ h ?_
  obtain ⟨B, φ, hφ, hR⟩ := H _ (𝒰.f i)
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    (Scheme.Hom.singleton_mem_fpqcPrecoverage (Spec.map φ)))
  rintro W a ⟨_, b, _, ⟨⟩, rfl⟩
  exact (R.pullback (𝒰.f i)).downward_closed hR b

/-- For `φ : A ⟶ B` and `g : Spec A ⟶ X`, the image of a global section `c` of `X` in
`Γ(Spec B) = B` is `φ` applied to the image of `c` in `Γ(Spec A) = A`. -/
lemma ΓSpecIso_inv_map_appTop {X : Scheme.{u}} {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (g : Spec A ⟶ X) (c : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso B).inv (φ ((Scheme.ΓSpecIso A).hom (g.appTop c))) =
      (Spec.map φ ≫ g).appTop c := by
  have key := congr_arg (fun h ↦ h ((Scheme.ΓSpecIso A).hom (g.appTop c)))
    (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at key
  rw [key, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 1
  exact (Scheme.ΓSpecIso A).hom_inv_id_apply (g.appTop c)

variable (S : Scheme.{u})

/-- The fpqc topology on the category of `S`-schemes. -/
abbrev fpqc : GrothendieckTopology (Over S) :=
  Scheme.fpqcTopology.over S

variable {S} in
/-- XI.4.1: on the site of `S`-schemes, a property of morphisms to `T` which is stable under
composition holds fpqc-locally if it holds after a faithfully flat extension of every affine
scheme over `T`. -/
theorem exists_fpqc_cover_of_affine {T : Over S} (Q : ∀ ⦃W : Scheme.{u}⦄, (W ⟶ T.left) → Prop)
    (hQ : ∀ ⦃W W' : Scheme.{u}⦄ (h : W' ⟶ W) (g : W ⟶ T.left), Q g → Q (h ≫ g))
    (H : ∀ (A : CommRingCat.{u}) (g : Spec A ⟶ T.left), ∃ (B : CommRingCat.{u}) (φ : A ⟶ B),
      φ.hom.FaithfullyFlat ∧ Q (Spec.map φ ≫ g)) :
    ∃ R ∈ fpqc S T, ∀ ⦃V : Over S⦄ (f : V ⟶ T), R f → Q f.left := by
  let R₀ : Sieve T.left :=
    { arrows W g := Q g
      downward_closed {_ _} _ hg h := hQ h _ hg }
  exact ⟨(Sieve.overEquiv T).symm R₀,
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _ (mem_fpqcTopology_of_affine R₀ H),
    fun _ _ hf ↦ hf⟩

/-- The structure sheaf `T ↦ Γ(T, 𝒪_T)` of rings on the category of `S`-schemes. -/
abbrev ringPresheaf : (Over S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ

/-- VIII.1.7: `T ↦ Γ(T, 𝒪_T)` is an fpqc sheaf on the category of `S`-schemes. -/
theorem isSheaf_ringPresheaf :
    Presieve.IsSheaf (fpqc S) (ringPresheaf S ⋙ CategoryTheory.forget CommRingCat) := by
  let e : coyoneda.obj (op (CommRingCat.free.obj PUnit.{u + 1})) ≅
      CategoryTheory.forget CommRingCat.{u} :=
    (CommRingCat.adj.corepresentableBy PUnit).toIso ≪≫
      Functor.isoWhiskerLeft (CategoryTheory.forget CommRingCat.{u})
        (NatIso.ofComponents (F := coyoneda.obj (op PUnit.{u + 1})) (G := 𝟭 (Type u))
          (fun X ↦ Equiv.toIso (show (PUnit.{u + 1} ⟶ X) ≃ X from
            { toFun f := f PUnit.unit
              invFun x := homOfElement x
              left_inv f := by ext ⟨⟩; rfl
              right_inv x := rfl })) fun _ ↦ rfl) ≪≫
      Functor.rightUnitor _
  have h : Presieve.IsSheaf Scheme.fpqcTopology.{u}
      (Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft Scheme.Γ e)
      (ExposeVIII.isSheaf_fpqcTopology_Γ _)
  exact (Over.forget S).op_comp_isSheaf_of_isSheaf_type (fpqc S) h

/-- XI.5.1: the additive group `𝔾_{a,S}` as a presheaf of groups on the category of `S`-schemes,
`T ↦ Γ(T, 𝒪_T)`, written multiplicatively. -/
@[simps]
def Ga : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Multiplicative Γ(T.unop.left, ⊤))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative (f.unop.left.appTop.hom.toAddMonoidHom))
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ ?_)
    change (𝟙 T.unop.left : T.unop.left ⟶ _).appTop x = x
    simp only [Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ ?_)
    change (g.unop.left ≫ f.unop.left).appTop x = g.unop.left.appTop (f.unop.left.appTop x)
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- XI.5.1: the multiplicative group `𝔾_{m,S}` as a presheaf of groups on the category of
`S`-schemes, `T ↦ Γ(T, 𝒪_T)ˣ`. -/
@[simps]
def Gm : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Γ(T.unop.left, ⊤))ˣ
  map f := GrpCat.ofHom (Units.map f.unop.left.appTop.hom.toMonoidHom)
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ Units.ext ?_)
    change (𝟙 T.unop.left : T.unop.left ⟶ _).appTop x.1 = x.1
    simp only [Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ Units.ext ?_)
    change (g.unop.left ≫ f.unop.left).appTop x.1 = g.unop.left.appTop (f.unop.left.appTop x.1)
    rw [Scheme.Hom.comp_appTop]
    rfl

lemma Ga_isCommutative : PresheafOfGroups.IsCommutative (Ga S) :=
  fun T (a b : Multiplicative Γ(T.unop.left, ⊤)) ↦ mul_comm a b

lemma Gm_isCommutative : PresheafOfGroups.IsCommutative (Gm S) :=
  fun T (a b : (Γ(T.unop.left, ⊤))ˣ) ↦ mul_comm a b

/-- XI.5.1: `𝔾_{a,S}` is an fpqc sheaf. -/
theorem isSheaf_Ga : Presieve.IsSheaf (fpqc S) (Ga S ⋙ CategoryTheory.forget GrpCat) :=
  isSheaf_ringPresheaf S

/-- XI.5.1: `𝔾_{m,S}` is an fpqc sheaf: a section of `𝒪` which is locally a unit is a unit,
the local inverses gluing to an inverse. -/
theorem isSheaf_Gm : Presieve.IsSheaf (fpqc S) (Gm S ⋙ CategoryTheory.forget GrpCat) := by
  have hO := isSheaf_ringPresheaf S
  intro T R hR x hx
  let val : Presieve.FamilyOfElements (ringPresheaf S ⋙ CategoryTheory.forget CommRingCat) R :=
    fun V f hf ↦ ((show (Γ(V.left, ⊤))ˣ from x f hf) : Γ(V.left, ⊤))
  let inv : Presieve.FamilyOfElements (ringPresheaf S ⋙ CategoryTheory.forget CommRingCat) R :=
    fun V f hf ↦ ((show (Γ(V.left, ⊤))ˣ from x f hf)⁻¹).1
  have hval : val.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun y : (Γ(Z.left, ⊤))ˣ ↦ (y : Γ(Z.left, ⊤))) (hx g₁ g₂ h₁ h₂ w)
  have hinv : inv.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun y : (Γ(Z.left, ⊤))ˣ ↦ ((y⁻¹ : (Γ(Z.left, ⊤))ˣ) : Γ(Z.left, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨a, ha, -⟩ := hO R hR val hval
  obtain ⟨b, hb, -⟩ := hO R hR inv hinv
  change Γ(T.left, ⊤) at a b
  have hab : a * b = 1 := by
    refine (hO R hR).isSeparatedFor.ext fun V f hf ↦ ?_
    change f.left.appTop.hom (a * b) = f.left.appTop.hom 1
    rw [map_mul, map_one]
    have h₁ : f.left.appTop.hom a = val f hf := ha f hf
    have h₂ : f.left.appTop.hom b = inv f hf := hb f hf
    rw [h₁, h₂]
    exact Units.mul_inv _
  let u : (Γ(T.left, ⊤))ˣ := ⟨a, b, hab, by rw [mul_comm, hab]⟩
  refine ⟨u, fun V f hf ↦ Units.ext (ha f hf), fun (v : (Γ(T.left, ⊤))ˣ) hv ↦ Units.ext ?_⟩
  refine (hO R hR).isSeparatedFor.ext fun V f hf ↦ ?_
  have h₁ : f.left.appTop.hom a = val f hf := ha f hf
  change f.left.appTop.hom (v : Γ(T.left, ⊤)) = f.left.appTop.hom a
  rw [h₁]
  exact congr_arg (fun y : (Γ(V.left, ⊤))ˣ ↦ (y : Γ(V.left, ⊤))) (hv f hf)

end SGA.SGA1.ExposeXI
