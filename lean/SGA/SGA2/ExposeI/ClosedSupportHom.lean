/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ExtensionByZero
import SGA.SGA2.ExposeI.SupportedSectionExactness
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero

/-!
# The closed-support Hom representation of SGA 2, I.1.6

For every closed subset `Z` of an arbitrary topological space, the actual
pushforward `zZX_closed Z = i_* ℤ_Z` represents `gammaZ F Z`. The additive
equivalence `closedSupportHomEquiv` is natural in the sheaf `F`.

The proof uses the locally surjective presentation of `i_* ℤ_Z` by the constant
integer presheaf on the ambient space. A section supported on `Z` annihilates
its kernel: a nonzero constant integer can vanish on an open of `Z` only when
that open is empty. Exactness of sheafification then supplies the unique
descended morphism. Thus no closed-support adjunction or alternate definition
of `ℤ_{Z,X}` is assumed.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The constant integer presheaf, before sheafification. -/
abbrev integerPresheaf (Y : TopCat.{u}) : Y.Presheaf AddCommGrpCat.{u} :=
  (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))

/-- The universal locally constant integer section on the closed subspace. -/
noncomputable def integerPresheafToClosed (Z : Closeds X) :
    integerPresheaf X ⟶ (zZX_closed Z).presheaf :=
  Functor.whiskerLeft (Opens.map (closedInclusion Z)).op
    (toSheafify (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
      (integerPresheaf (TopCat.of (Z : Set X))))

/-- Constant presheaf sections remain distinct on every nonempty open. -/
theorem integerPresheaf_toSheafify_injective (Y : TopCat.{u}) (U : Opens Y)
    (hU : (U : Set Y).Nonempty) : Function.Injective
      ((toSheafify (Opens.grothendieckTopology Y) (integerPresheaf Y)).app (op U)) := by
  intro a b hab
  obtain ⟨x, hx⟩ := hU
  obtain ⟨V, i, hi, hxV⟩ :=
    CategoryTheory.Presheaf.equalizerSieve_mem (Opens.grothendieckTopology Y)
      (toSheafify (Opens.grothendieckTopology Y) (integerPresheaf Y)) a b hab x hx
  exact hi

/-- The constant integer presheaf locally generates the actual closed pushforward. -/
theorem integerPresheafToClosed_locallySurjective (Z : Closeds X) :
    TopCat.Presheaf.IsLocallySurjective (integerPresheafToClosed Z) := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  by_cases hxZ : x ∈ Z
  · let c := toSheafify (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
      (integerPresheaf (TopCat.of (Z : Set X)))
    obtain ⟨W, hW, ⟨n, hn⟩, hxW⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff c).mp
        (show CategoryTheory.Presheaf.IsLocallySurjective _ c from inferInstance)
        ((Opens.map (closedInclusion Z)).obj U) t ⟨x, hxZ⟩ hx
    let hi : IsInducing (closedInclusion Z) := IsInducing.subtypeVal
    let V := U ⊓ hi.functorObj W
    have hV : V ≤ U := inf_le_left
    have hVW : (Opens.map (closedInclusion Z)).obj V = W := by
      apply le_antisymm
      · exact hi.le_functorObj_iff.mp inf_le_right
      · intro z hz
        exact ⟨hW hz, (hi.mem_functorObj_iff W).mpr hz⟩
    refine ⟨V, hV, ⟨n, ?_⟩, hx, (hi.mem_functorObj_iff W).mpr hxW⟩
    change c.app (op ((Opens.map (closedInclusion Z)).obj V)) n =
      (constantZ (TopCat.of (Z : Set X))).presheaf.map
        ((Opens.map (closedInclusion Z)).map (homOfLE hV)).op t
    have hn' := congrArg
      ((constantZ (TopCat.of (Z : Set X))).presheaf.map (eqToHom hVW).op) hn
    have hc := c.naturality_apply (eqToHom hVW).op n
    change c.app (op ((Opens.map (closedInclusion Z)).obj V)) n =
      (constantZ (TopCat.of (Z : Set X))).presheaf.map (eqToHom hVW).op
        (c.app (op W) n) at hc
    rw [← hc] at hn'
    change c.app (op ((Opens.map (closedInclusion Z)).obj V)) n =
      (constantZ (TopCat.of (Z : Set X))).presheaf.map (eqToHom hVW).op
        ((constantZ (TopCat.of (Z : Set X))).presheaf.map (homOfLE hW).op t) at hn'
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hn'
    convert! hn' using 1
  · let V := U ⊓ Z.compl
    have hV : V ≤ U := inf_le_left
    have hVZ : (Opens.map (closedInclusion Z)).obj V = ⊥ := by
      ext z
      exact ⟨fun hz => (hz.2 z.property).elim, False.elim⟩
    refine ⟨V, hV, ⟨0, ?_⟩, hx, hxZ⟩
    have ht := (constantZ (TopCat.of (Z : Set X))).isTerminalOfEqEmpty hVZ
    have hz := (IsZero.iff_id_eq_zero _).mpr (ht.hom_ext _ _)
    exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim _ _

/-- Descent of an additive presheaf map along a locally surjective presentation
of a sheaf. The kernel condition is checked before sheafification. -/
theorem exists_desc_of_locallySurjective
    {P : X.Presheaf AddCommGrpCat.{u}}
    {Q F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (c : P ⟶ Q.obj) (e : P ⟶ F.obj)
    (hc : TopCat.Presheaf.IsLocallySurjective c) (he : kernel.ι c ≫ e = 0) :
    ∃ φ : Q ⟶ F, c ≫ φ.hom = e := by
  let L := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : L.Additive := inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive
  have : PreservesFiniteLimits L := inferInstanceAs
    (PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  have : CategoryTheory.Sheaf.IsLocallySurjective (L.map c) :=
    (CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ c).mpr hc
  have : Epi (L.map c) := inferInstance
  have he' : kernel.ι (L.map c) ≫ L.map e = 0 := by
    rw [← cancel_epi (kernelComparison c L), kernelComparison_comp_ι_assoc,
      ← L.map_comp, he, L.map_zero, comp_zero]
  let d := Abelian.epiDesc (L.map c) (L.map e) he'
  let φ : Q ⟶ F := inv (adj.counit.app Q) ≫ d ≫ adj.counit.app F
  refine ⟨φ, ?_⟩
  have h : L.map c ≫ adj.counit.app Q ≫ φ = L.map e ≫ adj.counit.app F := by
    simp [φ, d]
  change c ≫ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ = e
  apply (adj.homEquiv P F).symm.injective
  rw [adj.homEquiv_naturality_right_symm]
  simpa only [Adjunction.homEquiv_counit, Category.assoc] using h

/-- Descent into a sheaf along a locally surjective presentation is unique. -/
theorem desc_unique_of_locallySurjective
    {P : X.Presheaf AddCommGrpCat.{u}}
    {Q F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (c : P ⟶ Q.obj) (hc : TopCat.Presheaf.IsLocallySurjective c)
    {φ ψ : Q ⟶ F} (h : c ≫ φ.hom = c ≫ ψ.hom) : φ = ψ := by
  let L := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : CategoryTheory.Sheaf.IsLocallySurjective (L.map c) :=
    (CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ c).mpr hc
  have : Epi (L.map c) := inferInstance
  change c ≫ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ =
    c ≫ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map ψ at h
  have hh := congrArg ((adj.homEquiv P F).symm) h
  rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_counit] at hh
  exact (cancel_epi (adj.counit.app Q)).mp ((cancel_epi (L.map c)).mp (by
    simpa only [Category.assoc] using hh))

/-- A global section gives the corresponding map out of the integer presheaf. -/
noncomputable def integerPresheafMap (F : Sheaf AddCommGrpCat.{u} X)
    (s : F.presheaf.obj (op ⊤)) : integerPresheaf X ⟶ F.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun n := n.down • F.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op s
      map_zero' := zero_zsmul _
      map_add' a b := add_zsmul _ _ _ }
  naturality {U V} i := by
    ext n
    change n.down • F.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op s =
      F.presheaf.map i (n.down • F.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op s)
    rw [map_zsmul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rfl

/-- A section supported on `Z` restricts to zero on every open disjoint from `Z`. -/
theorem supportedSection_restrict_eq_zero (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (s : gammaZ F Z) {U : Opens X} (hU : U ≤ Z.compl) :
    F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s.val = 0 := by
  have hs := congrArg
    (F.presheaf.map (homOfLE (le_inf le_top hU) : U ⟶ ⊤ ⊓ Z.compl).op) s.property
  change F.presheaf.map (homOfLE (le_inf le_top hU)).op
    (F.presheaf.map (homOfLE inf_le_left).op s.val) = _ at hs
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, map_zero,
    ← op_comp, homOfLE_comp] using hs

/-- The only relations in the closed constant presentation are killed by every
supported section. -/
theorem integerPresheafMap_kills_closed_kernel (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (s : gammaZ F Z) :
    kernel.ι (integerPresheafToClosed Z) ≫ integerPresheafMap F s.val = 0 := by
  ext U a
  let n := (kernel.ι (integerPresheafToClosed Z)).app (op U) a
  have hn : (integerPresheafToClosed Z).app (op U) n = 0 := by
    have h := congrArg (fun k => k.app (op U)) (kernel.condition (integerPresheafToClosed Z))
    exact ConcreteCategory.congr_hom h a
  change n.down • F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s.val = 0
  by_cases hn0 : n = 0
  · rw [hn0]
    exact zero_zsmul _
  · have hU : U ≤ Z.compl := by
      intro x hx hxZ
      apply hn0
      apply integerPresheaf_toSheafify_injective (TopCat.of (Z : Set X))
        ((Opens.map (closedInclusion Z)).obj U) ⟨⟨x, hxZ⟩, hx⟩
      exact hn.trans (map_zero _).symm
    rw [supportedSection_restrict_eq_zero F Z s hU, smul_zero]

/-- A supported section descends through the actual closed pushforward. -/
noncomputable def closedSupportHomOfSection (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (s : gammaZ F Z) : zZX_closed Z ⟶ F :=
  (exists_desc_of_locallySurjective (integerPresheafToClosed Z) (integerPresheafMap F s.val)
    (integerPresheafToClosed_locallySurjective Z)
    (integerPresheafMap_kills_closed_kernel F Z s)).choose

/-- The defining relation for the descended morphism. -/
theorem integerPresheafToClosed_comp_closedSupportHomOfSection (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (s : gammaZ F Z) :
    integerPresheafToClosed Z ≫ (closedSupportHomOfSection Z F s).hom =
      integerPresheafMap F s.val :=
  (exists_desc_of_locallySurjective (integerPresheafToClosed Z) (integerPresheafMap F s.val)
    (integerPresheafToClosed_locallySurjective Z)
    (integerPresheafMap_kills_closed_kernel F Z s)).choose_spec

/-- Sections of the closed constant sheaf vanish away from the closed set. -/
theorem integerPresheafToClosed_app_eq_zero_of_le_compl (Z : Closeds X)
    {U : Opens X} (hU : U ≤ Z.compl) (n : ULift.{u} ℤ) :
    (integerPresheafToClosed Z).app (op U) n = 0 := by
  have h : (Opens.map (closedInclusion Z)).obj U = ⊥ := by
    ext z
    exact ⟨fun hz => (hU hz z.property).elim, False.elim⟩
  exact (AddCommGrpCat.isZero_iff_subsingleton.mp
    ((constantZ (TopCat.of (Z : Set X))).isTerminalOfEqEmpty h).isZero).elim _ _

/-- Evaluation at the integer `1` sends a morphism out of `ℤ_{Z,X}` to a
global section with support in `Z`. -/
noncomputable def closedSupportSectionOfHom (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (φ : zZX_closed Z ⟶ F) : gammaZ F Z :=
  ⟨φ.hom.app (op ⊤) ((integerPresheafToClosed Z).app (op ⊤) ⟨1⟩), by
    change F.presheaf.map (homOfLE inf_le_left : ⊤ ⊓ Z.compl ⟶ ⊤).op
      (φ.hom.app (op ⊤) ((integerPresheafToClosed Z).app (op ⊤) ⟨1⟩)) = 0
    rw [← φ.hom.naturality_apply]
    have hc := (integerPresheafToClosed Z).naturality_apply
      (homOfLE inf_le_left : ⊤ ⊓ Z.compl ⟶ ⊤).op (⟨1⟩ : ULift ℤ)
    change (integerPresheafToClosed Z).app (op (⊤ ⊓ Z.compl)) ⟨1⟩ = _ at hc
    rw [← hc, integerPresheafToClosed_app_eq_zero_of_le_compl Z inf_le_right, map_zero]⟩

/-- A morphism from the integer presheaf is determined by its global value at `1`. -/
theorem integerPresheafMap_eval_one (F : Sheaf AddCommGrpCat.{u} X)
    (d : integerPresheaf X ⟶ F.presheaf) :
    integerPresheafMap F (d.app (op ⊤) ⟨1⟩) = d := by
  ext U n
  change n.down • F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
    (d.app (op ⊤) ⟨1⟩) = d.app (op U) n
  have hd := d.naturality_apply (homOfLE le_top : U ⟶ ⊤).op (⟨1⟩ : ULift ℤ)
  change d.app (op U) ⟨1⟩ = _ at hd
  rw [← hd, ← map_zsmul]
  congr 1
  apply ULift.ext
  simp

/-- The section of a descended supported section is the original section. -/
theorem closedSupportSectionOfHom_homOfSection (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (s : gammaZ F Z) :
    closedSupportSectionOfHom Z F (closedSupportHomOfSection Z F s) = s := by
  apply Subtype.ext
  have h := congrArg (fun k => k.app (op ⊤))
    (integerPresheafToClosed_comp_closedSupportHomOfSection Z F s)
  have h' := ConcreteCategory.congr_hom h (⟨1⟩ : ULift ℤ)
  change (closedSupportSectionOfHom Z F (closedSupportHomOfSection Z F s)).val =
    (1 : ℤ) • F.presheaf.map (homOfLE le_top : (⊤ : Opens X) ⟶ ⊤).op s.val at h'
  simpa only [homOfLE_refl, op_id, F.presheaf.map_id, AddCommGrpCat.id_apply, one_smul] using h'

/-- A morphism is recovered from its supported section. -/
theorem closedSupportHomOfSection_sectionOfHom (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (φ : zZX_closed Z ⟶ F) :
    closedSupportHomOfSection Z F (closedSupportSectionOfHom Z F φ) = φ := by
  apply desc_unique_of_locallySurjective (integerPresheafToClosed Z)
    (integerPresheafToClosed_locallySurjective Z)
  rw [integerPresheafToClosed_comp_closedSupportHomOfSection]
  exact integerPresheafMap_eval_one F (integerPresheafToClosed Z ≫ φ.hom)

/-- **SGA 2, I.1.6, closed support:** the actual closed pushforward of the
constant integer sheaf represents global sections with support in `Z`. -/
noncomputable def closedSupportHomEquiv (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) : (zZX_closed Z ⟶ F) ≃+ gammaZ F Z where
  toFun := closedSupportSectionOfHom Z F
  invFun := closedSupportHomOfSection Z F
  left_inv := closedSupportHomOfSection_sectionOfHom Z F
  right_inv := closedSupportSectionOfHom_homOfSection Z F
  map_add' φ ψ := by
    apply Subtype.ext
    rfl

/-- The closed-support Hom comparison is natural in the target sheaf. -/
theorem closedSupportHomEquiv_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (φ : zZX_closed Z ⟶ F) :
    closedSupportHomEquiv Z G (φ ≫ f) =
      gammaZSectionsMap f Z ⊤ (closedSupportHomEquiv Z F φ) := by
  apply Subtype.ext
  rfl

/-- The inverse closed-support comparison is natural in the target sheaf. -/
theorem closedSupportHomEquiv_symm_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (s : gammaZ F Z) :
    (closedSupportHomEquiv Z G).symm (gammaZSectionsMap f Z ⊤ s) =
      (closedSupportHomEquiv Z F).symm s ≫ f := by
  apply (closedSupportHomEquiv Z G).injective
  rw [AddEquiv.apply_symm_apply, closedSupportHomEquiv_naturality,
    AddEquiv.apply_symm_apply]

end SGA.SGA2.ExposeI
