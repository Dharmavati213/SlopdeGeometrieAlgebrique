/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedCohomologyComparison
import SGA.SGA2.ExposeI.OpenSupportCohomology

/-!
# Excision for actual supported cohomology in every degree

For a closed subset `Z` contained in an open `U`, `supportedExcisionEquiv`
identifies `H_Z Z F n` with the existing Ext-defined supported cohomology
of the actual restriction `restrictToOpen F U`, in every degree and naturally
in `F`. No separation or noetherian hypotheses are imposed on the space.

First, supported sections on the actual pullback are compared with the concrete
kernel on `U`. The degree-zero excision theorem then gives a natural Hom
equivalence. Preadditive Yoneda identifies the actual closed support object
with open extension by zero of its counterpart on `U`. Finally the Ext
adjunction for the exact, injective-preserving restriction gives all degrees.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The closed support induced on an open subspace. -/
def closedSupportOnOpen (Z : Closeds X) (U : Opens X) :
    Closeds ((Opens.toTopCat X).obj U) :=
  Z.preimage continuous_subtype_val

theorem openImage_closedSupportOnOpen_compl (Z : Closeds X) (U : Opens X) :
    U.isOpenEmbedding.functor.obj (⊤ ⊓ (closedSupportOnOpen Z U).compl) = U ⊓ Z.compl := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy.2⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, ⟨trivial, hx.2⟩, rfl⟩

/-- A commutative square with vertical additive equivalences identifies kernels. -/
def kerAddEquivOfCommSq {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ B) (g : C →+ D) (a : A ≃+ C) (b : B ≃+ D)
    (h : ∀ x, b (f x) = g (a x)) : f.ker ≃+ g.ker where
  toFun x := ⟨a x, by rw [AddMonoidHom.mem_ker, ← h, x.property, map_zero]⟩
  invFun y := ⟨a.symm y, by
    apply b.injective
    rw [h, AddEquiv.apply_symm_apply, y.property, map_zero]⟩
  left_inv x := Subtype.ext (a.symm_apply_apply x)
  right_inv y := Subtype.ext (a.apply_symm_apply y)
  map_add' x y := Subtype.ext (a.map_add x y)

/-- Naive restriction identifies the two concrete supported-section kernels. -/
def naiveRestrictGammaZEquiv (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj F)
      (closedSupportOnOpen Z U) ≃+ gammaZSections F Z U := by
  let G := (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj F
  let a : G.presheaf.obj (op ⊤) ≅ F.presheaf.obj (op U) :=
    F.presheaf.mapIso (eqToIso (by simp))
  let b : G.presheaf.obj (op (⊤ ⊓ (closedSupportOnOpen Z U).compl)) ≅
      F.presheaf.obj (op (U ⊓ Z.compl)) :=
    F.presheaf.mapIso (eqToIso (congrArg op (openImage_closedSupportOnOpen_compl Z U)))
  exact kerAddEquivOfCommSq (restrictToComplement G (closedSupportOnOpen Z U) ⊤).hom
    (restrictToComplement F Z U).hom
    a.addCommGroupIsoToAddEquiv b.addCommGroupIsoToAddEquiv (fun x => by
      change (G.presheaf.map (homOfLE inf_le_left).op ≫ b.hom) x =
        (a.hom ≫ F.presheaf.map (homOfLE inf_le_left).op) x
      apply ConcreteCategory.congr_hom
      change F.presheaf.map _ ≫ F.presheaf.map _ =
        F.presheaf.map _ ≫ F.presheaf.map _
      rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
      congr 1)

/-- Actual open pullback identifies supported global sections on the subspace
with the concrete supported sections on the original open. -/
def restrictToOpenGammaZEquiv (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ (restrictToOpen F U) (closedSupportOnOpen Z U) ≃+ gammaZSections F Z U :=
  (((gammaZSectionsFunctor (closedSupportOnOpen Z U) ⊤).mapIso
      ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).app F)).addCommGroupIsoToAddEquiv).trans
    (naiveRestrictGammaZEquiv Z U F)

theorem restrictToOpenGammaZEquiv_apply_val (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (s : gammaZ (restrictToOpen F U) (closedSupportOnOpen Z U)) :
    (restrictToOpenGammaZEquiv Z U F s).val = (restrictToOpenSectionsIso U F).hom s.val := rfl

/-- The standard comparison of sections after open pullback is natural. -/
theorem restrictToOpenSectionsIso_naturality (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    ((iShriek_open U).map f).hom.app (op ⊤) ≫ (restrictToOpenSectionsIso U G).hom =
      (restrictToOpenSectionsIso U F).hom ≫ f.hom.app (op U) := by
  have h := congrArg (fun k => k.hom.app (op ⊤))
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.naturality f)
  change ((iShriek_open U).map f).hom.app (op ⊤) ≫
      ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.app G).hom.app (op ⊤) =
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.app F).hom.app (op ⊤) ≫
      f.hom.app (op (U.isOpenEmbedding.functor.obj ⊤)) at h
  let k : op (U.isOpenEmbedding.functor.obj ⊤) ⟶ op U := eqToHom (by simp)
  change ((iShriek_open U).map f).hom.app (op ⊤) ≫
      (((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.app G).hom.app (op ⊤) ≫
        G.presheaf.map k) =
    (((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.app F).hom.app (op ⊤) ≫
      F.presheaf.map k) ≫ f.hom.app (op U)
  rw [← Category.assoc, h, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun t => ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat).hom.app F).hom.app
      (op ⊤) ≫ t) (f.hom.naturality k).symm

/-- Naturality of the concrete supported-section restriction comparison. -/
theorem restrictToOpenGammaZEquiv_naturality (Z : Closeds X) (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (s : gammaZ (restrictToOpen F U) (closedSupportOnOpen Z U)) :
    restrictToOpenGammaZEquiv Z U G
        (gammaZSectionsMap ((iShriek_open U).map f) (closedSupportOnOpen Z U) ⊤ s) =
      gammaZSectionsMap f Z U (restrictToOpenGammaZEquiv Z U F s) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (restrictToOpenSectionsIso_naturality U f) s.val

/-- Excision of actual supported sections under the hypothesis `Z ⊆ U`. -/
def gammaZExcisionEquiv {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z ≃+ gammaZ (restrictToOpen F U) (closedSupportOnOpen Z U) :=
  (gammaZ_restrict_addEquiv F hZ).trans (restrictToOpenGammaZEquiv Z U F).symm

/-- Naturality of supported-section excision. -/
theorem gammaZExcisionEquiv_naturality {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (s : gammaZ F Z) :
    gammaZExcisionEquiv hZ G (gammaZSectionsMap f Z ⊤ s) =
      gammaZSectionsMap ((iShriek_open U).map f) (closedSupportOnOpen Z U) ⊤
        (gammaZExcisionEquiv hZ F s) := by
  apply (restrictToOpenGammaZEquiv Z U G).injective
  rw [restrictToOpenGammaZEquiv_naturality]
  change (restrictToOpenGammaZEquiv Z U G)
      ((restrictToOpenGammaZEquiv Z U G).symm _) =
    gammaZSectionsMap f Z U
      ((restrictToOpenGammaZEquiv Z U F) ((restrictToOpenGammaZEquiv Z U F).symm _))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (f.hom.naturality_apply (homOfLE le_top : U ⟶ ⊤).op s.val).symm

/-- The two supported objects have naturally equivalent Hom groups. -/
def supportedExcisionHomEquiv {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) (F : Sheaf AddCommGrpCat.{u} X) :
    (zZX_closed Z ⟶ F) ≃+
      ((iBang_open U).obj (zZX_closed (closedSupportOnOpen Z U)) ⟶ F) :=
  (closedSupportHomEquiv Z F).trans
    ((gammaZExcisionEquiv hZ F).trans
      ((closedSupportHomEquiv (closedSupportOnOpen Z U) (restrictToOpen F U)).symm.trans
        ((openExtensionByZeroAdjunction U).homAddEquiv
          (zZX_closed (closedSupportOnOpen Z U)) F).symm))

theorem supportedExcisionHomEquiv_naturality {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (φ : zZX_closed Z ⟶ F) :
    supportedExcisionHomEquiv hZ G (φ ≫ f) = supportedExcisionHomEquiv hZ F φ ≫ f := by
  apply ((openExtensionByZeroAdjunction U).homEquiv _ G).injective
  simp only [supportedExcisionHomEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_symm_apply, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  apply (closedSupportHomEquiv (closedSupportOnOpen Z U) (restrictToOpen G U)).injective
  erw [AddEquiv.apply_symm_apply,
    closedSupportHomEquiv_naturality (closedSupportOnOpen Z U) ((iShriek_open U).map f),
    AddEquiv.apply_symm_apply, closedSupportHomEquiv_naturality Z f,
    gammaZExcisionEquiv_naturality]

/-- Excision identifies the actual closed support object with extension by zero
of the actual support object on the open neighbourhood. -/
def closedSupportExcisionIso {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) :
    (iBang_open U).obj (zZX_closed (closedSupportOnOpen Z U)) ≅ zZX_closed Z :=
  (preadditiveCoyoneda.preimageIso
    (NatIso.ofComponents (fun F => (supportedExcisionHomEquiv hZ F).toAddCommGrpIso)
      (fun f => by ext φ; exact supportedExcisionHomEquiv_naturality hZ f φ))).unop

/-- The source-object change in Ext induced by the proved support-object isomorphism. -/
def supportedExcisionExtSourceEquiv {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_Z Z F n ≃+
      Ext ((iBang_open U).obj (zZX_closed (closedSupportOnOpen Z U))) F n :=
  (((extFunctor n).mapIso (closedSupportExcisionIso hZ).op).app F).addCommGroupIsoToAddEquiv

/-- **SGA 2, I.2.2:** excision for actual supported cohomology in every degree. -/
def supportedExcisionEquiv {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_Z Z F n ≃+ H_Z (closedSupportOnOpen Z U) (restrictToOpen F U) n := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  exact (supportedExcisionExtSourceEquiv hZ F n).trans
    (adjunctionExtEquiv (openExtensionByZeroAdjunction U)
      (zZX_closed (closedSupportOnOpen Z U)) F n)

/-- Excision respects the original maps on supported cohomology. -/
theorem supportedExcisionEquiv_naturality {Z : Closeds X} {U : Opens X}
    (hZ : (Z : Set X) ⊆ (U : Set X)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : H_Z Z F n) :
    supportedExcisionEquiv hZ G n (H_Z_map Z f n x) =
      H_Z_map (closedSupportOnOpen Z U) ((iShriek_open U).map f) n
        (supportedExcisionEquiv hZ F n x) := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  have h := ConcreteCategory.congr_hom
    (((extFunctor n).mapIso (closedSupportExcisionIso hZ).op).hom.naturality f) x
  change supportedExcisionExtSourceEquiv hZ G n (H_Z_map Z f n x) =
    (supportedExcisionExtSourceEquiv hZ F n x).comp (Ext.mk₀ f) (add_zero n) at h
  change adjunctionExtMap (openExtensionByZeroAdjunction U) _ G n
      (supportedExcisionExtSourceEquiv hZ G n (H_Z_map Z f n x)) = _
  rw [h, adjunctionExtMap_naturality]
  rfl

end SGA.SGA2.ExposeI
