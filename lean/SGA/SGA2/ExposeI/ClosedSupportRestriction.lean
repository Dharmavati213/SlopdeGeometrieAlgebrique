/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSections

/-! # Actual restriction of the closed integer support sheaf -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Direct-image global sections are the actual global sections on the open. -/
def openPushforwardGlobalSectionsIso (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G).presheaf.obj (op ⊤) ≅
      G.presheaf.obj (op ⊤) :=
  G.presheaf.mapIso (eqToIso (congrArg op (show
    (Opens.map U.inclusion').obj ⊤ = ⊤ by ext; rfl)))

theorem openPushforwardGlobalSectionsIso_hom (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    (openPushforwardGlobalSectionsIso U G).hom = 𝟙 (G.presheaf.obj (op ⊤)) := by
  change G.presheaf.map _ = 𝟙 _
  rw [Subsingleton.elim (eqToIso _).hom (𝟙 _), G.presheaf.map_id]

private theorem openPreimage_supportComplement (Z : Closeds X) (U : Opens X) :
    (Opens.map U.inclusion').obj (⊤ ⊓ Z.compl) =
      ⊤ ⊓ (closedSupportOnOpen Z U).compl := by
  ext x
  rfl

/-- Reindex the complement sections of a direct image. -/
def openPushforwardComplementSectionsIso (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G).presheaf.obj
        (op (⊤ ⊓ Z.compl)) ≅
      G.presheaf.obj (op (⊤ ⊓ (closedSupportOnOpen Z U).compl)) :=
  G.presheaf.mapIso (eqToIso (congrArg op (openPreimage_supportComplement Z U)))

/-- Supported sections of an actual direct image are supported sections on
the open, without requiring the original support to lie inside that open. -/
def gammaZOpenPushforwardEquiv (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    gammaZ ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z ≃+
      gammaZ G (closedSupportOnOpen Z U) :=
  kerAddEquivOfCommSq
    (restrictToComplement ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z ⊤).hom
    (restrictToComplement G (closedSupportOnOpen Z U) ⊤).hom
    (openPushforwardGlobalSectionsIso U G).addCommGroupIsoToAddEquiv
    (openPushforwardComplementSectionsIso Z U G).addCommGroupIsoToAddEquiv
    (fun s ↦ by
      change ((((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G).presheaf.map
          (homOfLE inf_le_left).op) ≫ (openPushforwardComplementSectionsIso Z U G).hom) s =
        ((openPushforwardGlobalSectionsIso U G).hom ≫
          G.presheaf.map (homOfLE inf_le_left).op) s
      apply ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) _ s
      change G.presheaf.map _ ≫ G.presheaf.map _ = G.presheaf.map _ ≫ G.presheaf.map _
      rw [← G.presheaf.map_comp, ← G.presheaf.map_comp]
      congr 1)

/-- The support comparison has the expected underlying section. -/
theorem gammaZOpenPushforwardEquiv_val (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (s : gammaZ ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z) :
    (gammaZOpenPushforwardEquiv Z U G s).val =
      (openPushforwardGlobalSectionsIso U G).hom s.val := rfl

/-- Reindexing supported sections of a direct image is natural in the sheaf
on the open subspace. -/
theorem gammaZOpenPushforwardEquiv_naturality (Z : Closeds X) (U : Opens X)
    {G H : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)} (f : G ⟶ H)
    (s : gammaZ ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z) :
    gammaZOpenPushforwardEquiv Z U H
        (gammaZSectionsMap ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').map f) Z ⊤ s) =
      gammaZSectionsMap f (closedSupportOnOpen Z U) ⊤ (gammaZOpenPushforwardEquiv Z U G s) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (f.hom.naturality _).symm s.val

/-- The actual restriction/direct-image adjunction expressed using the same
actual-to-naive restriction isomorphism as local internal Hom. -/
def closedSupportRestrictionAdjunction (U : Opens X) :
    iShriek_open U ⊣ Sheaf.pushforward AddCommGrpCat.{u} U.inclusion' :=
  (naiveOpenPullbackAdjunction U).ofNatIsoLeft
    (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).symm

/-- Ordinary restriction of the actual integer support object has the Hom
representation of the actual restricted closed support. -/
def closedSupportRestrictionHomEquiv (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    (restrictToOpen (zZX_closed Z) U ⟶ G) ≃+
      (zZX_closed (closedSupportOnOpen Z U) ⟶ G) :=
  ((closedSupportRestrictionAdjunction U).homAddEquiv
    (zZX_closed Z) G).trans
    ((closedSupportHomEquiv Z ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G)).trans
      ((gammaZOpenPushforwardEquiv Z U G).trans
        (closedSupportHomEquiv (closedSupportOnOpen Z U) G).symm))

theorem closedSupportRestrictionHomEquiv_naturality (Z : Closeds X) (U : Opens X)
    {G H : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)} (f : G ⟶ H)
    (φ : restrictToOpen (zZX_closed Z) U ⟶ G) :
    closedSupportRestrictionHomEquiv Z U H (φ ≫ f) =
      closedSupportRestrictionHomEquiv Z U G φ ≫ f := by
  change (closedSupportHomEquiv (closedSupportOnOpen Z U) H).symm
    (gammaZOpenPushforwardEquiv Z U H
      (closedSupportHomEquiv Z _
        ((closedSupportRestrictionAdjunction U).homEquiv _ _
          (φ ≫ f)))) = _
  rw [Adjunction.homEquiv_naturality_right, closedSupportHomEquiv_naturality,
    gammaZOpenPushforwardEquiv_naturality, closedSupportHomEquiv_symm_naturality]
  rfl

/-- The Hom comparison as a natural isomorphism. -/
def closedSupportRestrictionHomFunctorIso (Z : Closeds X) (U : Opens X) :
    preadditiveCoyoneda.obj (op (restrictToOpen (zZX_closed Z) U)) ≅
      preadditiveCoyoneda.obj (op (zZX_closed (closedSupportOnOpen Z U))) :=
  NatIso.ofComponents (fun G => (closedSupportRestrictionHomEquiv Z U G).toAddCommGrpIso)
    (fun f => by ext φ; exact closedSupportRestrictionHomEquiv_naturality Z U f φ)

/-- Actual closed-support base change for an arbitrary open, without any
containment hypothesis on the closed subset. -/
def closedSupportRestrictionIso (Z : Closeds X) (U : Opens X) :
    restrictToOpen (zZX_closed Z) U ≅ zZX_closed (closedSupportOnOpen Z U) :=
  (preadditiveCoyoneda.preimageIso (closedSupportRestrictionHomFunctorIso Z U)).unop.symm

/-- The base-change isomorphism induces exactly the Hom equivalence used in
its construction, rather than an unspecified isomorphism of representing objects. -/
theorem closedSupportRestrictionIso_inv_comp (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (φ : restrictToOpen (zZX_closed Z) U ⟶ G) :
    (closedSupportRestrictionIso Z U).inv ≫ φ = closedSupportRestrictionHomEquiv Z U G φ := by
  have h : preadditiveCoyoneda.map (closedSupportRestrictionIso Z U).inv.op =
      (closedSupportRestrictionHomFunctorIso Z U).hom := by
    change preadditiveCoyoneda.map
      (preadditiveCoyoneda.preimage (closedSupportRestrictionHomFunctorIso Z U).hom) = _
    exact preadditiveCoyoneda.map_preimage _
  exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
    (congrArg (fun k => k.app G) h) φ

theorem closedSupportRestrictionHomEquiv_hom_comp (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (φ : zZX_closed (closedSupportOnOpen Z U) ⟶ G) :
    closedSupportRestrictionHomEquiv Z U G ((closedSupportRestrictionIso Z U).hom ≫ φ) = φ := by
  rw [← closedSupportRestrictionIso_inv_comp, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

private theorem naiveAdjunction_supportedSection_val (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    (ψ : (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (zZX_closed Z) ⟶ G) :
    (gammaZOpenPushforwardEquiv Z U G
      (closedSupportHomEquiv Z _ ((naiveOpenPullbackAdjunction U).homEquiv _ G ψ))).val =
        ψ.hom.app (op ⊤)
          ((integerPresheafToClosed Z).app (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩) := by
  change (openPushforwardGlobalSectionsIso U G).hom
    (((naiveOpenPullbackAdjunction U).homEquiv _ G ψ).hom.app (op ⊤)
      ((integerPresheafToClosed Z).app (op ⊤) ⟨1⟩)) = _
  rw [openPushforwardGlobalSectionsIso_hom]
  change (((naiveOpenPullbackAdjunction U).homEquiv _ G ψ).hom.app (op ⊤)
    ((integerPresheafToClosed Z).app (op ⊤) ⟨1⟩)) = _
  rw [Adjunction.homEquiv_unit]
  change ψ.hom.app (op ⊤)
    (((naiveOpenPullbackAdjunction U).unit.app (zZX_closed Z)).hom.app (op ⊤)
      ((integerPresheafToClosed Z).app (op ⊤) ⟨1⟩)) = _
  rw [naiveOpenPullbackAdjunction_unit_app]
  congr 1
  exact ((integerPresheafToClosed Z).naturality_apply
    (U.isOpenEmbedding.isOpenMap.adjunction.counit.app ⊤).op (⟨1⟩ : ULift ℤ)).symm

/-- Under the same actual-to-naive restriction comparison used by internal
Hom, the base-change map sends the integer generator to the original local generator. -/
theorem closedSupportRestrictionIso_generator (Z : Closeds X) (U : Opens X) :
    (((closedSupportRestrictionIso Z U).inv ≫
      (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z)).hom.app
        (op ⊤)) ((integerPresheafToClosed (closedSupportOnOpen Z U)).app (op ⊤) ⟨1⟩) =
      (integerPresheafToClosed Z).app (op (U.isOpenEmbedding.functor.obj ⊤)) ⟨1⟩ := by
  change (closedSupportHomEquiv (closedSupportOnOpen Z U) _
    ((closedSupportRestrictionIso Z U).inv ≫
      (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z))).val = _
  rw [closedSupportRestrictionIso_inv_comp]
  change (closedSupportHomEquiv (closedSupportOnOpen Z U) _
    ((closedSupportHomEquiv (closedSupportOnOpen Z U) _).symm _)).val = _
  rw [AddEquiv.apply_symm_apply]
  change (gammaZOpenPushforwardEquiv Z U _
    (closedSupportHomEquiv Z _
      ((closedSupportRestrictionAdjunction U).homEquiv _ _
        ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z))))).val = _
  rw [closedSupportRestrictionAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Iso.symm_hom, Iso.inv_hom_id_app]
  exact naiveAdjunction_supportedSection_val Z U _ (𝟙 _)

/-- The base-change isomorphism respects the entire canonical integer
presheaf presentation, hence all restrictions to smaller opens simultaneously. -/
theorem integerPresheafToClosed_comp_closedSupportRestrictionIso (Z : Closeds X) (U : Opens X) :
    integerPresheafToClosed (closedSupportOnOpen Z U) ≫
      ((closedSupportRestrictionIso Z U).inv ≫
        (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z)).hom =
      Functor.whiskerLeft U.isOpenEmbedding.functor.op (integerPresheafToClosed Z) := by
  let G := (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj (zZX_closed Z)
  let d₁ := integerPresheafToClosed (closedSupportOnOpen Z U) ≫
    ((closedSupportRestrictionIso Z U).inv ≫
      (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app (zZX_closed Z)).hom
  let d₂ := Functor.whiskerLeft U.isOpenEmbedding.functor.op (integerPresheafToClosed Z)
  calc
    d₁ = integerPresheafMap G (d₁.app (op ⊤) ⟨1⟩) := (integerPresheafMap_eval_one G d₁).symm
    _ = integerPresheafMap G (d₂.app (op ⊤) ⟨1⟩) := by
      congr 1
      exact closedSupportRestrictionIso_generator Z U
    _ = d₂ := integerPresheafMap_eval_one G d₂

/-- The direct-image support comparison extends to every ambient open.
At this level the underlying supported-section kernels are definitionally the same. -/
def gammaZSectionsOpenPushforwardEquiv (Z : Closeds X) (U V : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)) :
    gammaZSections ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z V ≃+
      gammaZSections G (closedSupportOnOpen Z U) ((Opens.map U.inclusion').obj V) :=
  AddEquiv.refl _

theorem gammaZSectionsOpenPushforwardEquiv_naturality (Z : Closeds X) (U V : Opens X)
    {G H : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U)} (f : G ⟶ H)
    (s : gammaZSections ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z V) :
    gammaZSectionsOpenPushforwardEquiv Z U V H
        (gammaZSectionsMap ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').map f) Z V s) =
      gammaZSectionsMap f (closedSupportOnOpen Z U) ((Opens.map U.inclusion').obj V)
        (gammaZSectionsOpenPushforwardEquiv Z U V G s) := rfl

/-- The supported-section base change commutes with restriction to every
smaller ambient open, without extra hypotheses on either open or support. -/
theorem gammaZSectionsOpenPushforwardEquiv_restrict (Z : Closeds X) (U : Opens X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj U))
    {V V' : Opens X} (i : V' ⟶ V)
    (s : gammaZSections ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z V) :
    gammaZSectionsOpenPushforwardEquiv Z U V' G
        (gammaZSectionsRestriction
          ((Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj G) Z i s) =
      gammaZSectionsRestriction G (closedSupportOnOpen Z U) ((Opens.map U.inclusion').map i)
        (gammaZSectionsOpenPushforwardEquiv Z U V G s) := rfl

end SGA.SGA2.ExposeI
