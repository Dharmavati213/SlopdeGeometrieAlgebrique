/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.CartanInfinite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Cohomology over an open subset and cohomology of the restricted sheaf

Let `X` be a topological space, `U ⊆ X` an open subset, `F` an abelian sheaf on `X` and `V` an
open subset of the space `U`, with image `V'` in `X`. The cohomology `Hⁿ(V', F)` of the
repository (`CategoryTheory.Sheaf.H'`, i.e. `Extⁿ(ℤ_{V'}, F)` computed in abelian sheaves on `X`)
is isomorphic to the cohomology `Hⁿ(V, F|_U)` of the restriction `F|_U`
(`TopologicalSpace.Opens.sheafRestrict`) computed in abelian sheaves on `U`
(`TopCat.Sheaf.restrictH'AddEquiv`). The isomorphism is natural in `F`
(`TopCat.Sheaf.restrictH'_map`), compatible with the connecting maps of short exact sequences
(`TopCat.Sheaf.restrictExt_comp_extClass`) and is the identity of `F(V')` in degree `0`
(`TopCat.Sheaf.restrictH'_equiv₀`). This is the standard fact `Hⁿ(U, F) = Hⁿ(U, F|_U)`
(Hartshorne, *Algebraic Geometry*, III.2.6 and its proof; Stacks Project, Chapter "Cohomology of
Sheaves", the lemma on cohomology of open subspaces), which the docstring of
`SGA.Foundations.Cohomology.Basic` leaves aside.

## Proof

Restriction to `U` is exact (`Opens.sheafRestrict` preserves finite limits, and it is isomorphic
to the pullback along the inclusion, a left adjoint). It therefore maps `Ext` groups
(`CategoryTheory.Abelian.Ext.mapExactFunctor`); composing with the canonical morphism
`ℤ_V ⟶ (ℤ_{V'})|_U` (`TopCat.Sheaf.freeRestrictHom`) gives the comparison map
`TopCat.Sheaf.restrictH'`. It is bijective in degree `0` (both sides are `F(V')`), and the
induction on the degree is dimension shifting along `0 → F → I → Q → 0` with `I` injective. The
needed vanishing `Hⁿ⁺¹(V, I|_U) = 0` (`TopCat.Sheaf.subsingleton_H'_restrict_of_injective`)
comes from Cartan's criterion (`TopCat.Sheaf.H'_subsingleton_of_forall_cech`): `I` is a retract
of the Godement sheaf of its stalks, and the restriction of a Godement sheaf to `U` is a retract
of a Godement sheaf on `U`, whose Čech complexes are exact
(`TopCat.Presheaf.cechComplex_godement_exactAt`).

## Main results

* `TopCat.Sheaf.restrictH'`: the comparison map `Hⁿ(V', F) →+ Hⁿ(V, F|_U)` (on `Ext` groups,
  `TopCat.Sheaf.restrictExt`), natural in `F` (`restrictH'_map`), compatible with connecting
  maps (`restrictExt_comp_extClass`), the identity of `F(V')` in degree `0` (`restrictH'_equiv₀`);
* `TopCat.Sheaf.restrictExt_bijective`, `TopCat.Sheaf.restrictH'AddEquiv`: it is bijective;
* `TopCat.Sheaf.restrictH'AddEquivOfLE`, `TopCat.Sheaf.subsingleton_H'_iff_restrict`: the same
  for an open `V ≤ U` of `X` and its preimage in `U`;
* `TopCat.Sheaf.subsingleton_H'_restrict_of_injective`: restrictions of injective sheaves are
  acyclic on the opens of `U`;
* `TopCat.Presheaf.cechComplex_exactAt_of_retract`: Čech exactness passes to retracts.
-/

universe w w' u

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Presheaf

variable {Y : TopCat.{u}} {ι : Type*} (𝒰 : ι → Opens Y)

/-- A retract of a presheaf whose Čech complex (for a family `𝒰`) is exact in degree `n + 1` has
the same property. -/
theorem cechComplex_exactAt_of_retract {P Q : Y.Presheaf AddCommGrpCat.{u}} (i : P ⟶ Q)
    (r : Q ⟶ P) (hir : i ≫ r = 𝟙 P) {n : ℕ} (hQ : (cechComplex 𝒰 Q).ExactAt (n + 1)) :
    (cechComplex 𝒰 P).ExactAt (n + 1) := by
  rw [cechComplex_exactAt_succ_iff] at hQ ⊢
  intro c hc
  obtain ⟨b, hb⟩ := hQ (cechCochainMap 𝒰 i (n + 1) c)
    (by rw [cechD_cechCochainMap, hc, map_zero])
  refine ⟨cechCochainMap 𝒰 r n b, ?_⟩
  rw [cechD_cechCochainMap, hb, ← cechCochainMap_comp, hir, cechCochainMap_id]

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- Restriction of abelian sheaves from `X` to the open subspace `U`. -/
abbrev restrictFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} :=
  Opens.sheafRestrict U

/-- The inclusion `U ⟶ X` as a morphism of topological spaces. -/
abbrev openInclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨_, continuous_subtype_val⟩

/-- Restriction to `U` is left adjoint to the direct image along the inclusion: it is isomorphic
to the inverse image (`Topology.IsOpenEmbedding.sheafPullbackIso`). -/
def restrictAdjunction :
    restrictFunctor U ⊣ TopCat.Sheaf.pushforward AddCommGrpCat.{u} (openInclusion U) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} _).ofNatIsoLeft
    (U.isOpenEmbedding.sheafPullbackIso (f := openInclusion U) AddCommGrpCat.{u})

instance : PreservesFiniteColimits (restrictFunctor U) := by
  have := (restrictAdjunction U).leftAdjoint_preservesColimits
  infer_instance

instance : (restrictFunctor U).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {U}

/-- The image in `X` of an open subset `V` of `U`. -/
abbrev openImage (V : Opens U) : Opens X :=
  U.isOpenEmbedding.isOpenMap.functor.obj V

variable (U) in
/-- The preimage in `U` of an open subset of `X`. -/
abbrev openPreimage (V : Opens X) : Opens U :=
  (Opens.map (openInclusion U)).obj V

lemma openImage_openPreimage {V : Opens X} (h : V ≤ U) : openImage (openPreimage U V) = V := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩

/-- The free abelian sheaf `ℤ_V` on `X` generated by an open `V`. -/
abbrev freeSheaf (V : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf _ _).obj (yoneda.obj V ⋙ AddCommGrpCat.free)

/-- The canonical section of `ℤ_V` over `V` (the image of `1`). -/
def freeSheafGen (V : Opens X) : (freeSheaf V).obj.obj (op V) :=
  CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv (freeSheaf V) V (𝟙 _)

/-- The canonical morphism `ℤ_V ⟶ (ℤ_{V'})|_U` for an open `V` of `U` with image `V'` in `X`:
it sends the generator to the generator. -/
def freeRestrictHom (V : Opens U) :
    freeSheaf (X := TopCat.of U) V ⟶ (restrictFunctor U).obj (freeSheaf (openImage V)) :=
  (CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv _ V).symm (freeSheafGen (openImage V))

lemma freeYonedaSheafHomAddEquiv_freeRestrictHom (V : Opens U) :
    CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv _ V (freeRestrictHom V) =
      freeSheafGen (openImage V) :=
  AddEquiv.apply_symm_apply _ _

/-- A morphism out of `ℤ_V` is determined by the image of the generator. -/
lemma freeYonedaSheafHomAddEquiv_eq_app_gen {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (V : Opens X) (f : freeSheaf V ⟶ F) :
    CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv F V f = f.hom.app (op V) (freeSheafGen V) := by
  have := CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv_comp V (𝟙 (freeSheaf V)) f
  rwa [Category.id_comp] at this

/-- On morphisms out of the free sheaves, the comparison is the identity of `F(V')`. -/
lemma freeYonedaSheafHomAddEquiv_freeRestrictHom_comp
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} {V : Opens U}
    (f : freeSheaf (openImage V) ⟶ F) :
    CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv ((restrictFunctor U).obj F) V
      (freeRestrictHom V ≫ (restrictFunctor U).map f) =
      CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv F (openImage V) f := by
  rw [CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv_comp,
    freeYonedaSheafHomAddEquiv_freeRestrictHom, freeYonedaSheafHomAddEquiv_eq_app_gen]
  rfl

/-! ### Restrictions of injective sheaves are acyclic -/

lemma mem_of_mem_openImage {W : Opens U} {x : X} (hx : x ∈ openImage W) : x ∈ U := by
  obtain ⟨a, -, rfl⟩ := hx
  exact a.2

lemma mk_mem_of_mem_openImage {W : Opens U} {x : X} (hx : x ∈ openImage W) :
    (⟨x, mem_of_mem_openImage hx⟩ : U) ∈ W := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha

variable (U) in
/-- The restriction to `U` of the Godement sheaf of `A` maps to the Godement presheaf of
`A|_U` on `U` (an isomorphism, of which only the retraction is needed). -/
def restrictGodementToGodement (A : X → AddCommGrpCat.{u}) :
    ((restrictFunctor U).obj (godement A)).obj ⟶
      Presheaf.godement (X := TopCat.of U) (fun y ↦ A y.1) where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
    Pi.evalAddMonoidHom (fun x : openImage W.unop ↦ A x) ⟨y.1.1, ⟨y.1, y.2, rfl⟩⟩)
  naturality _ _ _ := rfl

variable (U) in
/-- The inverse of `TopCat.Sheaf.restrictGodementToGodement`. -/
def godementToRestrictGodement (A : X → AddCommGrpCat.{u}) :
    Presheaf.godement (X := TopCat.of U) (fun y ↦ A y.1) ⟶
      ((restrictFunctor U).obj (godement A)).obj where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x ↦
    Pi.evalAddMonoidHom (fun y : W.unop ↦ A y.1.1)
      ⟨⟨x.1, mem_of_mem_openImage x.2⟩, mk_mem_of_mem_openImage x.2⟩)
  naturality _ _ _ := rfl

lemma restrictGodementToGodement_comp (A : X → AddCommGrpCat.{u}) :
    restrictGodementToGodement U A ≫ godementToRestrictGodement U A = 𝟙 _ :=
  rfl

/-- The Čech complexes of the restriction of an injective sheaf to `U`, for families of opens of
`U`, are exact in positive degrees. -/
theorem cechComplex_restrict_exactAt_of_injective
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    {ι : Type*} (𝒱 : ι → Opens (TopCat.of U)) (n : ℕ) :
    (Presheaf.cechComplex 𝒱 ((restrictFunctor U).obj I).obj).ExactAt (n + 1) := by
  let i := toGodement I
  let r := Injective.factorThru (𝟙 I) i
  have hir : ((restrictFunctor U).map i).hom ≫ ((restrictFunctor U).map r).hom = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom) (show (restrictFunctor U).map i ≫ (restrictFunctor U).map r = 𝟙 _ by
      rw [← Functor.map_comp, Injective.comp_factorThru, CategoryTheory.Functor.map_id])
  refine Presheaf.cechComplex_exactAt_of_retract 𝒱
    (((restrictFunctor U).map i).hom ≫ restrictGodementToGodement U _)
    (godementToRestrictGodement U _ ≫ ((restrictFunctor U).map r).hom) ?_
    (Presheaf.cechComplex_godement_exactAt (X := TopCat.of U) _ 𝒱 n)
  rw [Category.assoc, ← Category.assoc (restrictGodementToGodement U _),
    restrictGodementToGodement_comp, Category.id_comp, hir]

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})]

/-- The comparison map on `Ext` groups underlying `TopCat.Sheaf.restrictH'`: restrict an extension
class to `U` (`Ext.mapExactFunctor`) and pull it back along `ℤ_V ⟶ (ℤ_{V'})|_U`. -/
def restrictExt (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens U) :
    Ext (freeSheaf (openImage V)) F n →+
      Ext (freeSheaf (X := TopCat.of U) V) ((restrictFunctor U).obj F) n :=
  ((Ext.mk₀ (freeRestrictHom V)).precomp _ (zero_add n)).comp
    ((restrictFunctor U).mapExtAddHom _ _ n)

lemma restrictExt_apply (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} {V : Opens U} (x : Ext (freeSheaf (openImage V)) F n) :
    restrictExt F n V x = (Ext.mk₀ (freeRestrictHom V)).comp
      (x.mapExactFunctor (restrictFunctor U)) (zero_add n) :=
  rfl

/-- The comparison map `Hⁿ(V', F) → Hⁿ(V, F|_U)` for an open `V` of `U` with image `V'` in `X`
(`TopCat.Sheaf.restrictExt` on the underlying `Ext` groups). -/
def restrictH' (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens U) :
    F.H' n (openImage V) →+ ((restrictFunctor U).obj F).H' n V :=
  restrictExt F n V

lemma restrictExt_mk₀ {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {V : Opens U} (f : freeSheaf (openImage V) ⟶ F) :
    restrictExt F 0 V (Ext.mk₀ f) = Ext.mk₀ (freeRestrictHom V ≫ (restrictFunctor U).map f) := by
  rw [restrictExt_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma restrictExt_bijective_zero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens U) :
    Function.Bijective (restrictExt F 0 V) := by
  let g : (freeSheaf (openImage V) ⟶ F) →
      (freeSheaf (X := TopCat.of U) V ⟶ (restrictFunctor U).obj F) :=
    fun f ↦ freeRestrictHom V ≫ (restrictFunctor U).map f
  have hg : Function.Bijective g := by
    have hcomp : (CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv ((restrictFunctor U).obj F) V) ∘
        g = CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv F (openImage V) :=
      funext freeYonedaSheafHomAddEquiv_freeRestrictHom_comp
    refine (Function.Bijective.of_comp_iff'
      (CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv ((restrictFunctor U).obj F) V).bijective
      g).mp ?_
    rw [hcomp]
    exact (CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv F (openImage V)).bijective
  have h : ⇑(restrictExt F 0 V) = Ext.mk₀ ∘ g ∘ Ext.homEquiv₀ := by
    funext x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    simp only [Function.comp_apply]
    rw [restrictExt_mk₀]
    have : Ext.homEquiv₀ (Ext.mk₀ f) = f := by
      rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]
    rw [this]
  rw [h]
  exact (Ext.mk₀_bijective _ _).comp (hg.comp Ext.homEquiv₀.bijective)

/-- The comparison map is natural in the sheaf. -/
lemma restrictExt_comp_mk₀
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) {n : ℕ} {V : Opens U} (x : Ext (freeSheaf (openImage V)) F n) :
    restrictExt G n V (x.comp (Ext.mk₀ f) (add_zero n)) =
      (restrictExt F n V x).comp (Ext.mk₀ ((restrictFunctor U).map f)) (add_zero n) := by
  rw [restrictExt_apply, restrictExt_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- The comparison map is compatible with the connecting maps of a short exact sequence. -/
lemma restrictExt_comp_extClass
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n : ℕ} {V : Opens U} (x : Ext (freeSheaf (openImage V)) S.X₃ n) :
    restrictExt S.X₁ (n + 1) V (x.comp hS.extClass rfl) =
      (restrictExt S.X₃ n V x).comp (hS.map_of_exact (restrictFunctor U)).extClass rfl := by
  rw [restrictExt_apply, restrictExt_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ _ _ (by lia)).symm

omit [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The restriction to `U` of an injective sheaf on `X` has no cohomology in positive degrees on
the opens of `U` (Cartan's criterion, `TopCat.Sheaf.H'_subsingleton_of_forall_cech`). -/
theorem subsingleton_H'_restrict_of_injective
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    (n : ℕ) (V : Opens U) : Subsingleton (((restrictFunctor U).obj I).H' (n + 1) V) :=
  H'_subsingleton_of_forall_cech (X := TopCat.of U) ((restrictFunctor U).obj I)
    (fun _ 𝒱 p ↦ cechComplex_restrict_exactAt_of_injective I 𝒱 p) n V

/-- The inductive step: dimension shifting along a short exact sequence with injective middle
term. -/
lemma restrictExt_bijective_succ_of_shortExact
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] (n : ℕ) (V : Opens U)
    (h₂ : Function.Bijective (restrictExt S.X₂ n V))
    (h₃ : Function.Bijective (restrictExt S.X₃ n V)) :
    Function.Bijective (restrictExt S.X₁ (n + 1) V) := by
  let hS' := hS.map_of_exact (restrictFunctor U)
  have hI : Subsingleton (Ext (freeSheaf (X := TopCat.of U) V)
      ((restrictFunctor U).obj S.X₂) (n + 1)) :=
    subsingleton_H'_restrict_of_injective S.X₂ n V
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _)
      (n₀ := n) rfl
    rw [restrictExt_comp_extClass] at hx
    obtain ⟨w', hw'⟩ := Ext.covariant_sequence_exact₃ _ hS' (restrictExt S.X₃ n V z) rfl hx
    obtain ⟨w, rfl⟩ := h₂.2 w'
    have hw'' : restrictExt S.X₃ n V (w.comp (Ext.mk₀ S.g) (add_zero n)) =
        restrictExt S.X₃ n V z :=
      (restrictExt_comp_mk₀ S.g w).trans hw'
    rw [← h₃.1 hw'', Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  · intro y
    obtain ⟨z', rfl⟩ := Ext.covariant_sequence_exact₁ _ hS' y (@Subsingleton.elim _ hI _ _)
      (n₀ := n) rfl
    obtain ⟨z, rfl⟩ := h₃.2 z'
    exact ⟨z.comp hS.extClass rfl, restrictExt_comp_extClass hS z⟩

/-- **Cohomology over an open subset is the cohomology of the restriction**: for an open `V` of
`U` with image `V'` in `X`, the comparison map `Hⁿ(V', F) → Hⁿ(V, F|_U)` is bijective. -/
theorem restrictExt_bijective (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) (V : Opens U) : Function.Bijective (restrictExt F n V) := by
  induction n generalizing F with
  | zero => exact restrictExt_bijective_zero F V
  | succ n ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    exact restrictExt_bijective_succ_of_shortExact hS n V (ih _) (ih _)

/-- `Hⁿ(V', F) ≃+ Hⁿ(V, F|_U)` for an open `V` of `U` with image `V'` in `X`. -/
def restrictH'AddEquiv (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) (V : Opens U) :
    F.H' n (openImage V) ≃+ ((restrictFunctor U).obj F).H' n V :=
  AddEquiv.ofBijective (restrictH' F n V) (restrictExt_bijective F n V)

lemma restrictH'AddEquiv_apply (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) (V : Opens U) (x : F.H' n (openImage V)) :
    restrictH'AddEquiv F n V x = restrictH' F n V x :=
  rfl

/-- The comparison map is natural in the sheaf (the `H'` form of
`TopCat.Sheaf.restrictExt_comp_mk₀`). -/
lemma restrictH'_map {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) {n : ℕ} {V : Opens U} (x : F.H' n (openImage V)) :
    restrictH' G n V (CategoryTheory.Sheaf.H'.map f n (openImage V) x) =
      CategoryTheory.Sheaf.H'.map ((restrictFunctor U).map f) n V (restrictH' F n V x) :=
  restrictExt_comp_mk₀ f (show Ext _ _ n from x)

/-- In degree `0` the comparison map is the identity of `F(V')`. -/
lemma restrictH'_equiv₀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (V : Opens U) (x : F.H' 0 (openImage V)) :
    CategoryTheory.Sheaf.H'.equiv₀ ((restrictFunctor U).obj F) V (restrictH' F 0 V x) =
      CategoryTheory.Sheaf.H'.equiv₀ F (openImage V) x := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 (show Ext _ _ 0 from x)
  have h₀ : Ext.addEquiv₀ (Ext.mk₀ f) = f := by
    rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  have h₁ : Ext.addEquiv₀ (Ext.mk₀ (freeRestrictHom V ≫ (restrictFunctor U).map f)) =
      freeRestrictHom V ≫ (restrictFunctor U).map f := by
    rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  have h₂ : restrictH' F 0 V (Ext.mk₀ f) =
      Ext.mk₀ (freeRestrictHom V ≫ (restrictFunctor U).map f) :=
    restrictExt_mk₀ f
  change CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv ((restrictFunctor U).obj F) V
      (Ext.addEquiv₀ (restrictH' F 0 V (Ext.mk₀ f))) =
    CategoryTheory.Sheaf.freeYonedaSheafHomAddEquiv F (openImage V) (Ext.addEquiv₀ (Ext.mk₀ f))
  rw [h₂, h₁, h₀]
  exact freeYonedaSheafHomAddEquiv_freeRestrictHom_comp f

/-- For opens `V ≤ U` of `X`: `Hⁿ(V, F) ≃+ Hⁿ(V ∩ U, F|_U)`, cohomology over `V` computed on `X`
and on `U`. -/
def restrictH'AddEquivOfLE (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) {V : Opens X} (h : V ≤ U) :
    F.H' n V ≃+ ((restrictFunctor U).obj F).H' n (openPreimage U V) :=
  ((F.cohomologyPresheaf n).mapIso
    (eqToIso (openImage_openPreimage h)).op).addCommGroupIsoToAddEquiv.trans
      (restrictH'AddEquiv F n (openPreimage U V))

/-- The vanishing of cohomology over `V ≤ U` can be checked on `U`. -/
lemma subsingleton_H'_iff_restrict (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) {V : Opens X} (h : V ≤ U) :
    Subsingleton (F.H' n V) ↔
      Subsingleton (((restrictFunctor U).obj F).H' n (openPreimage U V)) :=
  (restrictH'AddEquivOfLE F n h).toEquiv.subsingleton_congr

end TopCat.Sheaf
