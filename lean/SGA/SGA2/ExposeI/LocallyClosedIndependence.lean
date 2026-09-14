/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedCohomology
import SGA.SGA2.ExposeI.SupportedExcision

/-!
# Independence of a locally closed support witness

Supported sections are compared on the intersection of two open witnesses.
Their natural Hom representations then identify the actual support sheaves,
and hence their Ext groups and original right-derived functors.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Set Abelian
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Relative excision only requires the support inside `V` to lie in `V'`:
equivalently, `V'` and the complement of the support cover `V`. -/
noncomputable def gammaZSections_restrict_addEquiv_of_cover
    (F : Sheaf AddCommGrpCat.{u} X) {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) :
    gammaZSections F Z V ≃+ gammaZSections F Z V' := by
  refine AddEquiv.ofBijective
    ({ toFun := fun s => ⟨F.presheaf.map (homOfLE hV).op s.val,
         restrict_mem_gammaZSections F hV s.property⟩
       map_zero' := by ext; exact map_zero _
       map_add' := by intro x y; ext; exact map_add _ _ _ } :
      gammaZSections F Z V →+ gammaZSections F Z V') ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Sheaf.eq_of_locally_eq₂ F (homOfLE hV)
      (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V)) (fun x hx => hcover hx)
    · exact congrArg Subtype.val hab
    · exact a.property.trans b.property.symm
  · intro t
    let O : Bool → Opens X
      | true => V'
      | false => V ⊓ Z.compl
    let sf : ∀ i : Bool, ToType (F.presheaf.obj (op (O i)))
      | true => t.val
      | false => 0
    have hcompat : Presheaf.IsCompatible F.presheaf O sf := by
      intro i j
      cases i <;> cases j
      · rfl
      · dsimp [sf, O]
        symm
        let B : Opens X := (V ⊓ Z.compl) ⊓ V'
        have hle : B ≤ V' ⊓ Z.compl := fun _ hx => ⟨hx.2, hx.1.2⟩
        have hfac : F.presheaf.map ((V ⊓ Z.compl).infLERight V').op =
            F.presheaf.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op ≫
              F.presheaf.map (homOfLE hle).op := by
          rw [← Functor.map_comp]
          rfl
        rw [hfac, ConcreteCategory.comp_apply]
        have ht : F.presheaf.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op t.val = 0 :=
          t.property
        rw [ht, map_zero]
        exact (map_zero _).symm
      · dsimp [sf, O]
        let B : Opens X := V' ⊓ (V ⊓ Z.compl)
        have hle : B ≤ V' ⊓ Z.compl := fun _ hx => ⟨hx.1, hx.2.2⟩
        have hfac : F.presheaf.map (V'.infLELeft (V ⊓ Z.compl)).op =
            F.presheaf.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op ≫
              F.presheaf.map (homOfLE hle).op := by
          rw [← Functor.map_comp]
          rfl
        rw [hfac, ConcreteCategory.comp_apply]
        have ht : F.presheaf.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op t.val = 0 :=
          t.property
        rw [ht, map_zero]
        exact (map_zero _).symm
      · rfl
    have hiSup : iSup O = V' ⊔ (V ⊓ Z.compl) := by
      apply le_antisymm
      · exact iSup_le fun i => by cases i <;> simp [O, le_sup_left, le_sup_right]
      · exact sup_le (le_iSup O true) (le_iSup O false)
    let iOV : ∀ i : Bool, O i ⟶ V
      | true => homOfLE hV
      | false => homOfLE (inf_le_left : V ⊓ Z.compl ≤ V)
    obtain ⟨s, hs, _⟩ := Sheaf.existsUnique_gluing' F O V iOV
      (hiSup.symm ▸ hcover) sf hcompat
    refine ⟨⟨s, ?_⟩, ?_⟩
    · exact hs false
    · exact Subtype.ext (hs true)

/-- Relative excision is the existing restriction on underlying sections. -/
theorem gammaZSections_restrict_addEquiv_of_cover_apply_val
    (F : Sheaf AddCommGrpCat.{u} X) {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) (s : gammaZSections F Z V) :
    (gammaZSections_restrict_addEquiv_of_cover F hV hcover s).val =
      F.presheaf.map (homOfLE hV).op s.val := rfl

/-- Relative excision commutes with morphisms of coefficient sheaves. -/
theorem gammaZSections_restrict_addEquiv_of_cover_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) (f : F ⟶ G)
    (s : gammaZSections F Z V) :
    gammaZSections_restrict_addEquiv_of_cover G hV hcover (gammaZSectionsMap f Z V s) =
      gammaZSectionsMap f Z V'
        (gammaZSections_restrict_addEquiv_of_cover F hV hcover s) := by
  apply Subtype.ext
  exact (f.hom.naturality_apply (homOfLE hV).op s.val).symm

/-- A canonical ambient closed hull of the given support. -/
def LocallyClosedIn.closedHull (W : LocallyClosedIn X) : Closeds X :=
  ⟨closure W.asSet, isClosed_closure⟩

/-- Restricting the canonical closed hull to the witness recovers its original
closed subset. -/
theorem LocallyClosedIn.closedSupportOnOpen_closedHull (W : LocallyClosedIn X) :
    closedSupportOnOpen W.closedHull W.V = W.ZV := by
  apply Closeds.ext
  change (Subtype.val : W.V → X) ⁻¹' closure
    (Subtype.val '' (W.ZV : Set W.V)) = (W.ZV : Set W.V)
  rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, W.ZV.isClosed.closure_eq]

/-- The part of the canonical closed hull lying in the witness is exactly
the original locally closed subset. -/
theorem LocallyClosedIn.inter_closedHull (W : LocallyClosedIn X) :
    (W.V : Set X) ∩ (W.closedHull : Set X) = W.asSet := by
  ext x
  constructor
  · rintro ⟨hxV, hxZ⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    have h := congrArg (fun Z : Closeds W.V => (⟨x, hxV⟩ : W.V) ∈ Z)
      W.closedSupportOnOpen_closedHull
    exact h.mp hxZ
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, subset_closure ⟨y, hy, rfl⟩⟩

/-- The common locally closed subset determines the same ambient closed hull. -/
theorem LocallyClosedIn.closedHull_eq_of_asSet_eq {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) : W.closedHull = W'.closedHull := by
  apply Closeds.ext
  exact congrArg closure h

/-- The underlying support is contained in its chosen open neighbourhood. -/
theorem LocallyClosedIn.asSet_subset (W : LocallyClosedIn X) : W.asSet ⊆ (W.V : Set X) := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

/-- Intersecting two witnesses for the same subset is a relative excision
cover for the first witness. -/
theorem LocallyClosedIn.inter_cover {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    W.V ≤ (W.V ⊓ W'.V) ⊔ (W.V ⊓ W.closedHull.compl) := by
  intro x hx
  by_cases hz : x ∈ W.closedHull
  · left
    refine ⟨hx, W'.asSet_subset ?_⟩
    rw [← h, ← W.inter_closedHull]
    exact ⟨hx, hz⟩
  · exact Or.inr ⟨hx, hz⟩

/-- A witness's actual supported sections agree with the concrete supported
sections of any ambient closed subset that restricts to its closed support. -/
noncomputable def locallyClosedGammaAmbientEquiv (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    (F : Sheaf AddCommGrpCat.{u} X) : W.gamma F ≃+ gammaZSections F Z W.V :=
  (AddEquiv.addSubgroupCongr (congrArg (gammaZ (restrictToOpen F W.V)) hZ.symm)).trans
    (restrictToOpenGammaZEquiv Z W.V F)

theorem locallyClosedGammaAmbientEquiv_apply_val (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    (F : Sheaf AddCommGrpCat.{u} X) (s : W.gamma F) :
    (locallyClosedGammaAmbientEquiv W Z hZ F s).val =
      (restrictToOpenSectionsIso W.V F).hom s.val := rfl

/-- The concrete comparison is natural in the original coefficient sheaf. -/
theorem locallyClosedGammaAmbientEquiv_naturality (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (s : W.gamma F) :
    locallyClosedGammaAmbientEquiv W Z hZ G ((gammaLocallyClosedFunctor W).map f s) =
      gammaZSectionsMap f Z W.V (locallyClosedGammaAmbientEquiv W Z hZ F s) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (restrictToOpenSectionsIso_naturality W.V f) s.val

/-- The witness-to-ambient comparison as a natural isomorphism. -/
noncomputable def gammaLocallyClosedAmbientIso (W : LocallyClosedIn X)
    (Z : Closeds X) (hZ : closedSupportOnOpen Z W.V = W.ZV) :
    gammaLocallyClosedFunctor W ≅ gammaZSectionsFunctor Z W.V :=
  NatIso.ofComponents (fun F => (locallyClosedGammaAmbientEquiv W Z hZ F).toAddCommGrpIso)
    (fun f => by ext s; exact locallyClosedGammaAmbientEquiv_naturality W Z hZ f s)

/-- Relative supported-section excision as a natural isomorphism. -/
noncomputable def gammaZSectionsRestrictionIsoOfCover {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) :
    gammaZSectionsFunctor Z V ≅ gammaZSectionsFunctor Z V' :=
  NatIso.ofComponents
    (fun F => (gammaZSections_restrict_addEquiv_of_cover F hV hcover).toAddCommGrpIso)
    (fun f => by ext s; exact gammaZSections_restrict_addEquiv_of_cover_naturality hV hcover f s)

/-- **I.1, independence of the open neighbourhood:** the original
supported-section functors of two arbitrary witnesses for the same locally
closed subset are naturally isomorphic. -/
noncomputable def gammaLocallyClosedIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    gammaLocallyClosedFunctor W ≅ gammaLocallyClosedFunctor W' := by
  have hZ : closedSupportOnOpen W.closedHull W'.V = W'.ZV := by
    rw [LocallyClosedIn.closedHull_eq_of_asSet_eq h]
    exact W'.closedSupportOnOpen_closedHull
  have hc : W'.V ≤ (W.V ⊓ W'.V) ⊔ (W'.V ⊓ W.closedHull.compl) := by
    rw [LocallyClosedIn.closedHull_eq_of_asSet_eq h, inf_comm W.V W'.V]
    exact LocallyClosedIn.inter_cover h.symm
  exact gammaLocallyClosedAmbientIso W W.closedHull W.closedSupportOnOpen_closedHull ≪≫
    gammaZSectionsRestrictionIsoOfCover inf_le_left (LocallyClosedIn.inter_cover h) ≪≫
    (gammaZSectionsRestrictionIsoOfCover inf_le_right hc).symm ≪≫
    (gammaLocallyClosedAmbientIso W' W.closedHull hZ).symm

/-- Independence of the original supported-section groups. -/
noncomputable def locallyClosedGammaEquivOfSameSet {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (F : Sheaf AddCommGrpCat.{u} X) : W.gamma F ≃+ W'.gamma F :=
  ((gammaLocallyClosedIndependenceIso h).app F).addCommGroupIsoToAddEquiv

/-- Independence of the supported-section groups is natural in coefficients. -/
private theorem natIso_addEquiv_naturality
    {C : Type*} [Category* C] {P Q : C ⥤ AddCommGrpCat.{u}} (e : P ≅ Q)
    {A B : C} (f : A ⟶ B) (s : P.obj A) :
    (e.app B).addCommGroupIsoToAddEquiv (P.map f s) =
      Q.map f ((e.app A).addCommGroupIsoToAddEquiv s) := by
  have h := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) (e.hom.naturality f) s
  exact h

/-- Independence of the supported-section groups is natural in coefficients. -/
theorem locallyClosedGammaEquivOfSameSet_naturality {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (s : W.gamma F) :
    locallyClosedGammaEquivOfSameSet h G ((gammaLocallyClosedFunctor W).map f s) =
      (gammaLocallyClosedFunctor W').map f (locallyClosedGammaEquivOfSameSet h F s) :=
  natIso_addEquiv_naturality (gammaLocallyClosedIndependenceIso h) f s

/-- The actual locally closed integer support sheaf is independent of the
arbitrary open/closed witness used to define it. -/
noncomputable def locallyClosedSupportIsoOfSameSet {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) : zZX_locallyClosed W ≅ zZX_locallyClosed W' :=
  (preadditiveCoyoneda.preimageIso
    (locallyClosedSupportHomFunctorIso W ≪≫ gammaLocallyClosedIndependenceIso h ≪≫
      (locallyClosedSupportHomFunctorIso W').symm)).unop.symm

/-- Independence of the original right-derived locally closed support functor. -/
noncomputable def derivedGammaLocallyClosedIndependenceIso {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (n : ℕ) :
    derivedGammaLocallyClosed W n ≅ derivedGammaLocallyClosed W' n :=
  rightDerivedFunctorIso (gammaLocallyClosedIndependenceIso h) n

/-- Source transport in Ext along an actual sheaf isomorphism. -/
private noncomputable def sheafExtSourceIsoEquiv
    {A B : Sheaf AddCommGrpCat.{u} X} (e : A ≅ B)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Ext.{u} A F n ≃+ Ext.{u} B F n :=
  (((extFunctor n).mapIso e.symm.op).app F).addCommGroupIsoToAddEquiv

private theorem sheafExtSourceIsoEquiv_naturality
    {A B : Sheaf AddCommGrpCat.{u} X} (e : A ≅ B)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (n : ℕ) (x : Ext.{u} A F n) :
    sheafExtSourceIsoEquiv e G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (sheafExtSourceIsoEquiv e F n x).comp (Ext.mk₀ f) (add_zero n) :=
  natIso_addEquiv_naturality ((extFunctor n).mapIso e.symm.op) f x

/-- The actual Ext-valued locally closed cohomology is independent of its
chosen witness in every degree. -/
noncomputable def locallyClosedCohomologyEquivOfSameSet {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed W F n ≃+ H_locallyClosed W' F n :=
  sheafExtSourceIsoEquiv (locallyClosedSupportIsoOfSameSet h) F n

/-- The all-degree witness-independence equivalence is natural in coefficients. -/
theorem locallyClosedCohomologyEquivOfSameSet_naturality {W W' : LocallyClosedIn X}
    (h : W.asSet = W'.asSet) {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (n : ℕ) (x : H_locallyClosed W F n) :
    locallyClosedCohomologyEquivOfSameSet h G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (locallyClosedCohomologyEquivOfSameSet h F n x).comp (Ext.mk₀ f) (add_zero n) :=
  sheafExtSourceIsoEquiv_naturality (locallyClosedSupportIsoOfSameSet h) f n x

end SGA.SGA2.ExposeI
