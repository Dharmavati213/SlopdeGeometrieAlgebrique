/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import SGA.SGA2.ExposeI.GammaZ

/-!
# SGA 2, Exposé I, §1: locally closed supports

SGA extends `Γ_Z` from closed to **locally closed** `Z ⊆ X` by choosing an open
`V ⊇ Z` in which `Z` is closed and setting `Γ_Z(F) = Γ_Z(F|_V)` (I.1, (3)).
Independence of `V` is proved by the sheaf property on the cover `(V', V \ Z)`.

Numbering follows Grothendieck. English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Set
open scoped ConcreteCategory

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- A locally closed subset of `X`, given as an open `V` together with a closed
subset of `V`. The underlying set is the image of `ZV` in `X`. -/
structure LocallyClosedIn (X : TopCat.{u}) where
  /-- An open of `X` in which the support is closed. -/
  V : Opens X
  /-- The support, closed in `V`. -/
  ZV : Closeds V

/-- The underlying set of a locally closed witness, as a subset of `X`. -/
def LocallyClosedIn.asSet (W : LocallyClosedIn X) : Set X :=
  Subtype.val '' (W.ZV : Set W.V)

lemma LocallyClosedIn.isLocallyClosed_asSet (W : LocallyClosedIn X) :
    IsLocallyClosed W.asSet := by
  have hZ : IsLocallyClosed (W.ZV : Set W.V) := W.ZV.isClosed.isLocallyClosed
  have hV : IsLocallyClosed (range (Subtype.val : W.V → X)) := by
    rw [Subtype.range_val]
    exact W.V.isOpen.isLocallyClosed
  exact hZ.image IsInducing.subtypeVal hV

/-- Restrict an abelian sheaf on `X` to the open witness `V`. -/
noncomputable def LocallyClosedIn.restrictSheaf (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  (Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' W.V)).obj F

/-- **I.1, (3):** `Γ_Z(F)` for locally closed `Z`, via the closed case on `V`. -/
noncomputable def LocallyClosedIn.gamma (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    AddSubgroup ((W.restrictSheaf F).1.obj (op (⊤ : Opens ((Opens.toTopCat X).obj W.V)))) :=
  gammaZ (W.restrictSheaf F) W.ZV

/-- When the support is open, take `V = U` and `ZV = ⊤` (closed in itself). -/
noncomputable def LocallyClosedIn.ofOpen (U : Opens X) : LocallyClosedIn X where
  V := U
  ZV := ⊤

@[simp] lemma LocallyClosedIn.ofOpen_asSet (U : Opens X) :
    (LocallyClosedIn.ofOpen U).asSet = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, -, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/-- **I.1, (6):** if `Z` is open then `Γ_Z(F) = Γ(Z, F)` (no support condition). -/
lemma LocallyClosedIn.gamma_ofOpen (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (LocallyClosedIn.ofOpen U).gamma F = ⊤ :=
  gammaZSections_top ((LocallyClosedIn.ofOpen U).restrictSheaf F) ⊤

/-- Open ∩ closed as a locally closed witness (I.1). -/
noncomputable def LocallyClosedIn.ofOpenClosed (U : Opens X) (Z : Closeds X) :
    LocallyClosedIn X where
  V := U
  ZV := {
    carrier := (Subtype.val : U → X) ⁻¹' (Z : Set X)
    isClosed' := Z.isClosed.preimage continuous_subtype_val
  }

lemma LocallyClosedIn.ofOpenClosed_asSet (U : Opens X) (Z : Closeds X) :
    (LocallyClosedIn.ofOpenClosed U Z).asSet = (U : Set X) ∩ (Z : Set X) := by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyZ, rfl⟩
    exact ⟨hyU, hyZ⟩
  · rintro ⟨hxU, hxZ⟩
    exact ⟨⟨x, hxU⟩, hxZ, rfl⟩

/-- **I.1:** a closed set is locally closed. -/
lemma isLocallyClosed_closed (Z : Closeds X) : IsLocallyClosed (Z : Set X) :=
  Z.isClosed.isLocallyClosed

/-- **I.1:** an open set is locally closed. -/
lemma isLocallyClosed_open (U : Opens X) : IsLocallyClosed (U : Set X) :=
  U.isOpen.isLocallyClosed

/-- **I.1:** the intersection of an open and a closed is locally closed. -/
lemma isLocallyClosed_inter_open_closed (U : Opens X) (Z : Closeds X) :
    IsLocallyClosed ((U : Set X) ∩ (Z : Set X)) :=
  U.isOpen.isLocallyClosed.inter Z.isClosed.isLocallyClosed

/-! ## Independence of the open (I.1, after (3)–(4)) -/

variable (F : Sheaf AddCommGrpCat.{u} X)

lemma restrictToComplement_commSq {Z : Closeds X} {V' V : Opens X} (hV : V' ≤ V) :
    restrictToComplement F Z V ≫
        F.1.map (homOfLE (fun (_ : X) (hx : _ ∈ V' ⊓ Z.compl) =>
          ⟨hV hx.1, hx.2⟩ : V' ⊓ Z.compl ≤ V ⊓ Z.compl)).op =
      F.1.map (homOfLE hV).op ≫ restrictToComplement F Z V' := by
  dsimp [restrictToComplement]
  simp only [← Functor.map_comp]
  rfl

lemma restrict_mem_gammaZSections {Z : Closeds X} {V' V : Opens X} (hV : V' ≤ V)
    {s : F.1.obj (op V)} (hs : s ∈ gammaZSections F Z V) :
    (F.1.map (homOfLE hV).op).hom s ∈ gammaZSections F Z V' := by
  rw [mem_gammaZSections_iff] at hs ⊢
  have hsq := congrArg (fun (f : F.1.obj (op V) ⟶ F.1.obj (op (V' ⊓ Z.compl))) => f.hom s)
    (restrictToComplement_commSq F hV)
  simpa [hs] using hsq.symm

lemma mem_sup_of_subset_open {Z : Closeds X} {V' V : Opens X}
    (hZ : (Z : Set X) ⊆ (V' : Set X)) {x : X} (hxV : x ∈ V) :
    x ∈ (V' ⊔ (V ⊓ Z.compl) : Opens X) := by
  by_cases hxZ : x ∈ (Z : Set X)
  · exact Or.inl (hZ hxZ)
  · refine Or.inr ⟨hxV, ?_⟩
    simpa [Closeds.compl] using hxZ

/-- Injectivity half of independence of the open. -/
lemma gammaZSections_restrict_injective {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hZ : (Z : Set X) ⊆ (V' : Set X))
    {s : F.1.obj (op V)} (hs : s ∈ gammaZSections F Z V)
    (hρ : (F.1.map (homOfLE hV).op).hom s = 0) : s = 0 := by
  refine Sheaf.eq_of_locally_eq₂ F (homOfLE hV)
    (homOfLE (inf_le_left : V ⊓ Z.compl ≤ V))
    (fun x hx => mem_sup_of_subset_open hZ hx) s 0 ?_ ?_
  · change (F.1.map (homOfLE hV).op).hom s = (F.1.map (homOfLE hV).op).hom 0
    rw [map_zero]; exact hρ
  · change (restrictToComplement F Z V).hom s = (restrictToComplement F Z V).hom 0
    rw [map_zero]; exact hs

/-- Surjectivity half of independence of the open (glue with zero on the complement). -/
lemma gammaZSections_restrict_surjective {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hZ : (Z : Set X) ⊆ (V' : Set X))
    (t : F.1.obj (op V')) (ht : t ∈ gammaZSections F Z V') :
    ∃ s : F.1.obj (op V), s ∈ gammaZSections F Z V ∧
      (F.1.map (homOfLE hV).op).hom s = t := by
  let U : Bool → Opens X
    | true => V'
    | false => V ⊓ Z.compl
  let sf : ∀ i : Bool, ToType (F.1.obj (op (U i)))
    | true => t
    | false => 0
  have hcompat : Presheaf.IsCompatible F.1 U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · dsimp [sf, U]
      simp only [map_zero]
      symm
      let W : Opens X := (V ⊓ Z.compl) ⊓ V'
      have hle : W ≤ V' ⊓ Z.compl := fun _ hx => ⟨hx.2, hx.1.2⟩
      have hfac :
          F.1.map ((V ⊓ Z.compl).infLERight V').op =
            F.1.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op ≫
              F.1.map (homOfLE hle).op := by
        simp only [← Functor.map_comp]; rfl
      rw [hfac, ConcreteCategory.comp_apply]
      have : (F.1.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op).hom t = 0 := ht
      rw [this, map_zero]
    · dsimp [sf, U]
      simp only [map_zero]
      let W : Opens X := V' ⊓ (V ⊓ Z.compl)
      have hle : W ≤ V' ⊓ Z.compl := fun _ hx => ⟨hx.1, hx.2.2⟩
      have hfac :
          F.1.map (V'.infLELeft (V ⊓ Z.compl)).op =
            F.1.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op ≫
              F.1.map (homOfLE hle).op := by
        simp only [← Functor.map_comp]; rfl
      rw [hfac, ConcreteCategory.comp_apply]
      have : (F.1.map (homOfLE (inf_le_left : V' ⊓ Z.compl ≤ V')).op).hom t = 0 := ht
      rw [this, map_zero]
    · rfl
  have hiSup : iSup U = V' ⊔ (V ⊓ Z.compl) := by
    apply le_antisymm
    · exact iSup_le fun i => by cases i <;> simp [U, le_sup_left, le_sup_right]
    · exact sup_le (le_iSup U true) (le_iSup U false)
  have hcover : V ≤ iSup U := by
    rw [hiSup]; intro x hx; exact mem_sup_of_subset_open hZ hx
  let iUV : ∀ i : Bool, U i ⟶ V
    | true => homOfLE hV
    | false => homOfLE (inf_le_left : V ⊓ Z.compl ≤ V)
  obtain ⟨s, hs_glue, _⟩ := Sheaf.existsUnique_gluing' F U V iUV hcover sf hcompat
  refine ⟨s, ?_, ?_⟩
  · have h1 := hs_glue false
    change (restrictToComplement F Z V).hom s = 0 at h1
    exact h1
  · exact hs_glue true

/-- **I.1 (independence of open as an isomorphism of groups).**

If `Z` is closed and `Z ⊆ V' ≤ V` are opens, restriction `F(V) → F(V')` induces a
group isomorphism `Γ_Z(F|_V) ≅ Γ_Z(F|_V')`. -/
noncomputable def gammaZSections_restrict_addEquiv {Z : Closeds X} {V' V : Opens X}
    (hV : V' ≤ V) (hZ : (Z : Set X) ⊆ (V' : Set X)) :
    gammaZSections F Z V ≃+ gammaZSections F Z V' := by
  refine AddEquiv.ofBijective
    ({ toFun := fun s => ⟨(F.1.map (homOfLE hV).op).hom s.1, restrict_mem_gammaZSections F hV s.2⟩
       map_zero' := by ext; exact map_zero _
       map_add' := by intro x y; ext; exact map_add _ _ _ } : gammaZSections F Z V →+ _)
    ⟨?inj, ?surj⟩
  case inj =>
    intro a b h
    ext
    have hab : (F.1.map (homOfLE hV).op).hom (a.1 - b.1) = 0 := by
      have := congrArg Subtype.val h
      dsimp at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp
      (gammaZSections_restrict_injective F hV hZ (AddSubgroup.sub_mem _ a.2 b.2) hab)
  case surj =>
    intro t
    obtain ⟨s, hs, hst⟩ := gammaZSections_restrict_surjective F hV hZ t.1 t.2
    exact ⟨⟨s, hs⟩, Subtype.ext hst⟩

/-- **I.1:** global form of independence (`V = X`). -/
noncomputable def gammaZ_restrict_addEquiv {Z : Closeds X} {V' : Opens X}
    (hZ : (Z : Set X) ⊆ (V' : Set X)) :
    gammaZ F Z ≃+ gammaZSections F Z V' :=
  gammaZSections_restrict_addEquiv F (le_top : V' ≤ ⊤) hZ

end SGA.SGA2.ExposeI
