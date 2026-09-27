/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Topology.Germ
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# The sheaf of analytic functions on a normed space

Let `𝕜` be a complete nontrivially normed field and `E` a normed space over `𝕜`. The analytic
functions `U → 𝕜` on the open subsets `U ⊆ E` form a sheaf of `𝕜`-algebras `𝒪_E`; its stalk at
`x` is the ring of germs at `x` of functions analytic at `x`, a local ring whose maximal ideal
consists of the germs vanishing at `x`. For `𝕜 = ℂ` and `E = ℂⁿ` this is the sheaf of holomorphic
functions of the theory of complex analytic spaces ([Grauert–Remmert, *Coherent analytic
sheaves*, §1.1]; [SGA 1, XII.1]).

## Main definitions

* `AnalyticGeometry.analyticSections 𝕜 U`: the `𝕜`-algebra of analytic functions on `U`.
* `AnalyticGeometry.analyticSheaf 𝕜 E`: the sheaf of commutative rings `𝒪_E`.
* `AnalyticGeometry.analyticGerms 𝕜 x`: the subring of `Germ (𝓝 x) 𝕜` of analytic germs.
* `AnalyticGeometry.stalkToGerm`: the isomorphism of the stalk `𝒪_{E,x}` with `analyticGerms 𝕜 x`.
* `AnalyticGeometry.evalStalk`: evaluation of germs at `x`.
* `AnalyticGeometry.modelSpace 𝕜 E`: `E` with the sheaf `𝒪_E`, as a locally ringed space.
-/

universe u

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter Set CategoryTheory.Limits

namespace AnalyticGeometry

section Extend

variable {E : Type*} {𝕜 : Type*} [Zero 𝕜]

open Classical in
/-- Extension by zero of a function on a subset of `E`. -/
def extendByZero {U : Set E} (f : U → 𝕜) (y : E) : 𝕜 :=
  if h : y ∈ U then f ⟨y, h⟩ else 0

lemma extendByZero_of_mem {U : Set E} (f : U → 𝕜) {y : E} (hy : y ∈ U) :
    extendByZero f y = f ⟨y, hy⟩ := by
  simp [extendByZero, hy]

@[simp] lemma extendByZero_coe {U : Set E} (f : U → 𝕜) (y : U) : extendByZero f y = f y :=
  extendByZero_of_mem f y.2

lemma extendByZero_of_notMem {U : Set E} (f : U → 𝕜) {y : E} (hy : y ∉ U) :
    extendByZero f y = 0 := by
  simp [extendByZero, hy]

lemma extendByZero_eventuallyEq [TopologicalSpace E] {U V : Set E} (hV : IsOpen V) (h : V ⊆ U)
    (f : U → 𝕜) (g : V → 𝕜) (hfg : ∀ y : V, g y = f ⟨y, h y.2⟩) {x : E} (hx : x ∈ V) :
    extendByZero g =ᶠ[𝓝 x] extendByZero f := by
  filter_upwards [hV.mem_nhds hx] with y hy
  rw [extendByZero_of_mem _ hy, extendByZero_of_mem _ (h hy), hfg]

end Extend

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] {E : Type u} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-! ### Analytic functions on open subsets -/

/-- A function on a subset `U` of `E` is analytic if its extension by zero is analytic at every
point of `U` (for `U` open this does not depend on the extension). -/
def IsAnalyticOn {U : Set E} (f : U → 𝕜) : Prop :=
  ∀ x : U, AnalyticAt 𝕜 (extendByZero f) x

variable {𝕜}

lemma IsAnalyticOn.analyticAt_of_eventuallyEq {U : Set E} {f : U → 𝕜} (hf : IsAnalyticOn 𝕜 f)
    {g : E → 𝕜} {x : E} (hx : x ∈ U) (h : extendByZero f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  (hf ⟨x, hx⟩).congr h

lemma isAnalyticOn_of_forall {U : Set E} (hU : IsOpen U) (f : U → 𝕜)
    (h : ∀ x : U, ∃ g : E → 𝕜, AnalyticAt 𝕜 g x ∧ ∀ᶠ y in 𝓝 (x : E), ∀ hy : y ∈ U,
      f ⟨y, hy⟩ = g y) : IsAnalyticOn 𝕜 f := by
  intro x
  obtain ⟨g, hg, hfg⟩ := h x
  refine hg.congr ?_
  filter_upwards [hfg, hU.mem_nhds x.2] with y hy hyU
  rw [extendByZero_of_mem _ hyU, hy hyU]

/-- The restriction of an analytic function `E → 𝕜` to an open set. -/
lemma isAnalyticOn_restrict {U : Set E} (hU : IsOpen U) {g : E → 𝕜}
    (hg : ∀ x ∈ U, AnalyticAt 𝕜 g x) :
    IsAnalyticOn 𝕜 (fun x : U ↦ g x) :=
  isAnalyticOn_of_forall hU _ fun x ↦ ⟨g, hg x x.2, Eventually.of_forall fun _ _ ↦ rfl⟩

variable (𝕜)

/-- The analytic functions on an open subset of `E` form a `𝕜`-subalgebra of all functions. -/
def analyticSections (U : Opens E) : Subalgebra 𝕜 (U → 𝕜) where
  carrier := {f | IsAnalyticOn 𝕜 f}
  mul_mem' {f g} hf hg x := ((hf x).mul (hg x)).congr (Eventually.of_forall fun y ↦ by
    by_cases hy : y ∈ U <;> simp [extendByZero, hy])
  add_mem' {f g} hf hg x := ((hf x).add (hg x)).congr (Eventually.of_forall fun y ↦ by
    by_cases hy : y ∈ U <;> simp [extendByZero, hy])
  algebraMap_mem' c x := (analyticAt_const (v := c)).congr (by
    filter_upwards [U.2.mem_nhds x.2] with y hy
    rw [extendByZero_of_mem _ hy]
    rfl)

variable {𝕜}

@[simp] lemma mem_analyticSections {U : Opens E} (f : U → 𝕜) :
    f ∈ analyticSections 𝕜 U ↔ IsAnalyticOn 𝕜 f := Iff.rfl

lemma analyticSections_analyticAt {U : Opens E} (f : analyticSections 𝕜 U) (x : U) :
    AnalyticAt 𝕜 (extendByZero f.1) x :=
  f.2 x

/-- Restriction of analytic functions to a smaller open set. -/
def analyticRestrict {U V : Opens E} (h : V ≤ U) :
    analyticSections 𝕜 U →ₐ[𝕜] analyticSections 𝕜 V where
  toFun f := ⟨fun x ↦ f.1 ⟨x, h x.2⟩, fun x ↦ (f.2 ⟨x, h x.2⟩).congr
    (extendByZero_eventuallyEq V.2 h _ _ (fun _ ↦ rfl) x.2).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma analyticRestrict_apply {U V : Opens E} (h : V ≤ U) (f : analyticSections 𝕜 U)
    (x : V) : (analyticRestrict h f).1 x = f.1 ⟨x, h x.2⟩ := rfl

/-- An analytic function on `E` restricts to a section over any open set on which it is
analytic. -/
def ofAnalyticOnNhd {U : Opens E} (g : E → 𝕜) (hg : ∀ x ∈ U, AnalyticAt 𝕜 g x) :
    analyticSections 𝕜 U :=
  ⟨fun x ↦ g x, isAnalyticOn_restrict U.2 hg⟩

@[simp] lemma ofAnalyticOnNhd_apply {U : Opens E} (g : E → 𝕜) (hg : ∀ x ∈ U, AnalyticAt 𝕜 g x)
    (x : U) : (ofAnalyticOnNhd g hg).1 x = g x := rfl

/-! ### The sheaf `𝒪_E` -/

variable (𝕜 E)

/-- The local predicate "analytic" on functions on open subsets of `E`. -/
def analyticPredicate : TopCat.LocalPredicate fun _ : TopCat.of E ↦ 𝕜 where
  pred {U} f := IsAnalyticOn 𝕜 f
  res {U V} i f hf x := (hf ⟨x, leOfHom i x.2⟩).congr
    (extendByZero_eventuallyEq U.2 (leOfHom i) _ _ (fun _ ↦ rfl) x.2).symm
  locality {U} f hf x := by
    obtain ⟨V, hxV, i, hV⟩ := hf x
    exact (hV ⟨x, hxV⟩).congr (extendByZero_eventuallyEq V.2 (leOfHom i) _ _ (fun _ ↦ rfl) hxV)

/-- The presheaf of analytic functions on `E`, as a presheaf of commutative rings. -/
def analyticPresheaf : TopCat.Presheaf CommRingCat.{u} (TopCat.of E) where
  obj U := CommRingCat.of (analyticSections 𝕜 U.unop)
  map {U V} i := CommRingCat.ofHom (analyticRestrict (𝕜 := 𝕜) (leOfHom i.unop)).toRingHom

/-- The sheaf `𝒪_E` of analytic functions on `E` (for `E = ℂⁿ`, the sheaf of holomorphic
functions). -/
def analyticSheaf : TopCat.Sheaf CommRingCat.{u} (TopCat.of E) where
  obj := analyticPresheaf 𝕜 E
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (TopCat.subsheafToTypes (analyticPredicate 𝕜 E)).property

instance (U : (Opens (TopCat.of E))ᵒᵖ) : Algebra 𝕜 ((analyticPresheaf 𝕜 E).obj U) :=
  inferInstanceAs (Algebra 𝕜 (analyticSections 𝕜 U.unop))

variable {𝕜 E}

@[simp] lemma analyticPresheaf_map_apply {U V : (Opens (TopCat.of E))ᵒᵖ} (i : U ⟶ V)
    (f : (analyticPresheaf 𝕜 E).obj U) (x : V.unop) :
    ((analyticPresheaf 𝕜 E).map i f).1 x = f.1 ⟨x, leOfHom i.unop x.2⟩ := rfl

/-! ### Stalks: germs of analytic functions -/

variable (𝕜) in
/-- The ring of germs at `x` of functions analytic at `x`. -/
def analyticGerms (x : E) : Subring (Germ (𝓝 x) 𝕜) where
  carrier := {g | ∃ f : E → 𝕜, AnalyticAt 𝕜 f x ∧ (f : Germ (𝓝 x) 𝕜) = g}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

lemma mem_analyticGerms {x : E} {g : Germ (𝓝 x) 𝕜} :
    g ∈ analyticGerms 𝕜 x ↔ ∃ f : E → 𝕜, AnalyticAt 𝕜 f x ∧ (f : Germ (𝓝 x) 𝕜) = g := Iff.rfl

lemma coe_mem_analyticGerms {x : E} {f : E → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    (f : Germ (𝓝 x) 𝕜) ∈ analyticGerms 𝕜 x := ⟨f, hf, rfl⟩

lemma analyticAt_of_coe_mem_analyticGerms {x : E} {f : E → 𝕜}
    (hf : (f : Germ (𝓝 x) 𝕜) ∈ analyticGerms 𝕜 x) : AnalyticAt 𝕜 f x := by
  obtain ⟨g, hg, e⟩ := hf
  exact hg.congr (Germ.coe_eq.mp e)

/-- The germ at `x` of a section defined near `x`. -/
def sectionGerm (x : E) (U : OpenNhds (X := TopCat.of E) x) :
    (analyticPresheaf 𝕜 E).obj (op U.1) ⟶ CommRingCat.of (analyticGerms 𝕜 x) :=
  CommRingCat.ofHom
    { toFun f := ⟨(extendByZero f.1 : Germ (𝓝 x) 𝕜), coe_mem_analyticGerms (f.2 ⟨x, U.2⟩)⟩
      map_one' := Subtype.ext <| Germ.coe_eq.mpr <| by
        filter_upwards [U.1.2.mem_nhds U.2] with y hy
        rw [extendByZero_of_mem _ hy]
        rfl
      map_mul' f g := Subtype.ext <| Germ.coe_eq.mpr <| Eventually.of_forall fun y ↦ by
        by_cases hy : y ∈ U.1 <;> simp [extendByZero, hy]
      map_zero' := Subtype.ext <| Germ.coe_eq.mpr <| Eventually.of_forall fun y ↦ by
        by_cases hy : y ∈ U.1 <;> simp [extendByZero, hy]
      map_add' f g := Subtype.ext <| Germ.coe_eq.mpr <| Eventually.of_forall fun y ↦ by
        by_cases hy : y ∈ U.1 <;> simp [extendByZero, hy] }

/-- The map from the stalk of `𝒪_E` at `x` to germs of analytic functions at `x`. -/
def stalkToGermHom (x : E) :
    (analyticPresheaf 𝕜 E).stalk x ⟶
      CommRingCat.of (analyticGerms 𝕜 x) :=
  colimit.desc ((OpenNhds.inclusion (X := TopCat.of E) x).op ⋙ analyticPresheaf 𝕜 E)
    { pt := CommRingCat.of (analyticGerms 𝕜 x)
      ι :=
        { app U := sectionGerm x U.unop
          naturality {U V} i := by
            ext f
            apply Subtype.ext
            refine Germ.coe_eq.mpr ?_
            exact extendByZero_eventuallyEq V.unop.1.2 (leOfHom i.unop) _ _ (fun _ ↦ rfl)
              V.unop.2 } }

lemma stalkToGermHom_germ (U : Opens (TopCat.of E)) (x : E) (hx : x ∈ U)
    (f : (analyticPresheaf 𝕜 E).obj (op U)) :
    (stalkToGermHom x ((analyticPresheaf 𝕜 E).germ U x hx f) : Germ (𝓝 x) 𝕜) =
      (extendByZero f.1 : Germ (𝓝 x) 𝕜) := by
  change ((colimit.ι ((OpenNhds.inclusion (X := TopCat.of E) x).op ⋙ analyticPresheaf 𝕜 E)
    (op ⟨U, hx⟩) ≫ stalkToGermHom x) f : Germ (𝓝 x) 𝕜) = _
  rw [stalkToGermHom, colimit.ι_desc]
  rfl

lemma stalkToGermHom_injective (x : E) : Function.Injective (stalkToGermHom (𝕜 := 𝕜) x) := by
  intro s t hst
  obtain ⟨U, hxU, f, rfl⟩ := (analyticPresheaf 𝕜 E).exists_germ_eq s
  obtain ⟨V, hxV, g, rfl⟩ := (analyticPresheaf 𝕜 E).exists_germ_eq t
  have h := congr_arg Subtype.val hst
  rw [stalkToGermHom_germ, stalkToGermHom_germ] at h
  obtain ⟨W₀, hW₀, hW₀o, hxW₀⟩ := mem_nhds_iff.mp
    (((Germ.coe_eq.mp h).and (U.2.mem_nhds hxU)).and (V.2.mem_nhds hxV))
  let W : Opens (TopCat.of E) := ⟨W₀, hW₀o⟩
  have hWU : W ≤ U := fun y hy ↦ (hW₀ hy).1.2
  have hWV : W ≤ V := fun y hy ↦ (hW₀ hy).2
  refine TopCat.Presheaf.germ_ext _ W hxW₀ (homOfLE hWU) (homOfLE hWV) ?_
  apply Subtype.ext
  funext y
  have := (hW₀ y.2).1.1
  rwa [extendByZero_of_mem _ (hWU y.2), extendByZero_of_mem _ (hWV y.2)] at this

variable [CompleteSpace 𝕜]

variable (𝕜) in
/-- The open set on which a function is analytic. -/
def analyticLocus (f : E → 𝕜) : Opens (TopCat.of E) :=
  ⟨{y | AnalyticAt 𝕜 f y}, isOpen_analyticAt 𝕜 f⟩

/-- The germ at `x` of a function analytic at `x`, as an element of the stalk of `𝒪_E`. -/
def germOf {x : E} (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) :
    (analyticPresheaf 𝕜 E).stalk x :=
  (analyticPresheaf 𝕜 E).germ (analyticLocus 𝕜 f) x (show x ∈ analyticLocus 𝕜 f from hf)
    (ofAnalyticOnNhd f fun _ h ↦ h)

@[simp] lemma stalkToGermHom_germOf {x : E} (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) :
    (stalkToGermHom x (germOf f hf) : Germ (𝓝 x) 𝕜) = f := by
  rw [germOf]
  erw [stalkToGermHom_germ]
  exact Germ.coe_eq.mpr (by
    filter_upwards [(analyticLocus 𝕜 f).2.mem_nhds hf] with y hy
    rw [extendByZero_of_mem _ hy]
    rfl)

lemma stalkToGermHom_surjective (x : E) : Function.Surjective (stalkToGermHom (𝕜 := 𝕜) x) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨germOf f hf, Subtype.ext (stalkToGermHom_germOf f hf)⟩

/-- The stalk of `𝒪_E` at `x` is the ring of germs of analytic functions at `x`. -/
def stalkToGerm (x : E) :
    (analyticPresheaf 𝕜 E).stalk x ≃+* analyticGerms 𝕜 x :=
  RingEquiv.ofBijective (stalkToGermHom x).hom
    ⟨stalkToGermHom_injective x, stalkToGermHom_surjective x⟩

@[simp] lemma stalkToGerm_apply (x : E)
    (s : (analyticPresheaf 𝕜 E).stalk x) :
    stalkToGerm x s = stalkToGermHom x s := rfl

@[simp] lemma stalkToGerm_germOf {x : E} (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) :
    (stalkToGerm x (germOf f hf) : Germ (𝓝 x) 𝕜) = f :=
  stalkToGermHom_germOf f hf

lemma germOf_eq_germOf_iff {x : E} {f g : E → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) : germOf f hf = germOf g hg ↔ f =ᶠ[𝓝 x] g := by
  rw [← (stalkToGerm (𝕜 := 𝕜) x).injective.eq_iff, ← Subtype.coe_inj, stalkToGerm_apply,
    stalkToGerm_apply, stalkToGermHom_germOf, stalkToGermHom_germOf]
  exact Germ.coe_eq

lemma exists_germOf_eq {x : E} (s : (analyticPresheaf 𝕜 E).stalk x) :
    ∃ (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x), germOf f hf = s := by
  obtain ⟨f, hf, e⟩ := (stalkToGermHom x s).2
  refine ⟨f, hf, stalkToGermHom_injective x (Subtype.ext ?_)⟩
  rw [stalkToGermHom_germOf, e]

lemma germ_eq_germOf (U : Opens (TopCat.of E)) {x : E} (hx : x ∈ U)
    (f : (analyticPresheaf 𝕜 E).obj (op U)) :
    (analyticPresheaf 𝕜 E).germ U x hx f = germOf (extendByZero f.1) (f.2 ⟨x, hx⟩) := by
  apply stalkToGermHom_injective x
  apply Subtype.ext
  rw [stalkToGermHom_germ, stalkToGermHom_germOf]

lemma germOf_add {x : E} {f g : E → 𝕜} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    germOf (f + g) (hf.add hg) = germOf f hf + germOf g hg :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_add, Subring.coe_add, stalkToGerm_germOf, stalkToGerm_germOf, stalkToGerm_germOf,
      Germ.coe_add]))

lemma germOf_mul {x : E} {f g : E → 𝕜} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    germOf (f * g) (hf.mul hg) = germOf f hf * germOf g hg :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_mul, Subring.coe_mul, stalkToGerm_germOf, stalkToGerm_germOf, stalkToGerm_germOf,
      Germ.coe_mul]))

lemma germOf_neg {x : E} {f : E → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    germOf (-f) hf.neg = -germOf f hf :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_neg, Subring.coe_neg, stalkToGerm_germOf, stalkToGerm_germOf, Germ.coe_neg]))

lemma germOf_sub {x : E} {f g : E → 𝕜} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    germOf (f - g) (hf.sub hg) = germOf f hf - germOf g hg :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_sub, AddSubgroupClass.coe_sub, stalkToGerm_germOf, stalkToGerm_germOf,
      stalkToGerm_germOf, Germ.coe_sub]))

lemma germOf_one {x : E} : germOf (fun _ ↦ (1 : 𝕜)) (analyticAt_const (x := x)) = 1 :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_one, Subring.coe_one, stalkToGerm_germOf]; rfl))

lemma germOf_zero {x : E} : germOf (fun _ ↦ (0 : 𝕜)) (analyticAt_const (x := x)) = 0 :=
  (stalkToGerm (𝕜 := 𝕜) x).injective (Subtype.ext (by
    rw [map_zero, Subring.coe_zero, stalkToGerm_germOf]; rfl))

lemma germOf_congr {x : E} {f g : E → 𝕜} (hf : AnalyticAt 𝕜 f x) (h : f =ᶠ[𝓝 x] g) :
    germOf f hf = germOf g (hf.congr h) :=
  (germOf_eq_germOf_iff _ _).mpr h

lemma germOf_sum {x : E} {ι : Type*} (s : Finset ι) {g : ι → E → 𝕜}
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h : AnalyticAt 𝕜 (fun y ↦ ∑ i ∈ s, g i y) x) :
    germOf (fun y ↦ ∑ i ∈ s, g i y) h = ∑ i ∈ s, germOf (g i) (hg i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact germOf_zero
  | insert j s hj ih =>
    have hs : AnalyticAt 𝕜 (fun y ↦ ∑ i ∈ s, g i y) x :=
      (s.analyticAt_sum fun i _ ↦ hg i).congr (Eventually.of_forall fun z ↦ by simp)
    rw [Finset.sum_insert hj, ← ih hs, ← germOf_add]
    exact germOf_congr _ (Eventually.of_forall fun z ↦ by simp [Finset.sum_insert hj])

/-- Induction principle for elements of the stalk: every element is `germOf f` for an analytic
`f`. -/
@[elab_as_elim]
lemma germOf_induction {x : E}
    {P : (analyticPresheaf 𝕜 E).stalk x → Prop}
    (h : ∀ (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x), P (germOf f hf)) (s) : P s := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf_eq s
  exact h f hf

/-! ### Evaluation and the local ring structure -/

/-- Evaluation at `x` of germs of analytic functions. -/
def evalStalk (x : E) :
    (analyticPresheaf 𝕜 E).stalk x →+* 𝕜 :=
  Germ.valueRingHom.comp ((analyticGerms 𝕜 x).subtype.comp (stalkToGermHom x).hom)

@[simp] lemma evalStalk_germOf {x : E} (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) :
    evalStalk x (germOf f hf) = f x := by
  change Germ.value (stalkToGerm x (germOf f hf) : Germ (𝓝 x) 𝕜) = f x
  rw [stalkToGerm_germOf, Germ.value_ofFun]

lemma evalStalk_germ (U : Opens (TopCat.of E)) {x : E} (hx : x ∈ U)
    (f : (analyticPresheaf 𝕜 E).obj (op U)) :
    evalStalk x ((analyticPresheaf 𝕜 E).germ U x hx f) = f.1 ⟨x, hx⟩ := by
  rw [germ_eq_germOf, evalStalk_germOf, extendByZero_of_mem _ hx]

/-- A germ of an analytic function is invertible if and only if it does not vanish at `x`. -/
theorem isUnit_stalk_iff {x : E} (s : (analyticPresheaf 𝕜 E).stalk x) :
    IsUnit s ↔ evalStalk x s ≠ 0 := by
  refine ⟨fun h ↦ (h.map (evalStalk x)).ne_zero, fun h ↦ ?_⟩
  induction s using germOf_induction with
  | h f hf =>
  rw [evalStalk_germOf] at h
  have hinv : AnalyticAt 𝕜 (fun y ↦ (f y)⁻¹) x := hf.inv h
  refine IsUnit.of_mul_eq_one (germOf _ hinv) ?_
  rw [← germOf_mul, ← germOf_one]
  apply germOf_congr
  filter_upwards [hf.continuousAt.eventually_ne h] with y hy
  simp [hy]

instance (x : E) : Nontrivial ((analyticPresheaf 𝕜 E).stalk x) :=
  ⟨⟨0, 1, fun h ↦ by simpa using congr_arg (evalStalk x) h⟩⟩

instance isLocalRing_stalk (x : E) :
    IsLocalRing ((analyticPresheaf 𝕜 E).stalk x) := by
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_stalk_iff, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

lemma mem_maximalIdeal_stalk_iff {x : E}
    (s : (analyticPresheaf 𝕜 E).stalk x) :
    s ∈ IsLocalRing.maximalIdeal _ ↔ evalStalk x s = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_stalk_iff, not_not]

variable (𝕜 E) in
/-- The normed space `E` with its sheaf of analytic functions, as a locally ringed space. For
`E = ℂⁿ` this is the complex analytic space `ℂⁿ`. -/
def modelSpace : AlgebraicGeometry.LocallyRingedSpace.{u} where
  carrier := TopCat.of E
  presheaf := analyticPresheaf 𝕜 E
  IsSheaf := (analyticSheaf 𝕜 E).property
  isLocalRing x := isLocalRing_stalk (E := E) x

end AnalyticGeometry
