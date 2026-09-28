/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Basic
import SGA.Foundations.Cohomology.Godement
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Cartan's criterion: Čech acyclicity on a basis implies acyclicity

Let `X` be a topological space, `B` a set of opens and `Cov` a set of finite families of opens
such that
* every finite intersection of members of a family in `Cov` lies in `B`;
* every open cover of a member `V ∈ B` is refined by a family in `Cov` whose union is `V`.

If an abelian sheaf `F` has vanishing Čech cohomology in positive degrees for every family in
`Cov`, then `Hⁿ(V, F) = 0` for all `n > 0` and all `V ∈ B`
(Stacks Project, Tag 01EW, a variant of Tag 01EV; Cartan, Séminaire 1950/51; Godement,
*Théorie des faisceaux*,
II.5.9.2). This is how Serre's vanishing theorem for quasi-coherent sheaves on affine schemes is
deduced from the exactness of Čech complexes of standard covers
(`SGA.Foundations.Cohomology.AffineVanishing`).

The proof embeds `F` into an injective sheaf `I` with cokernel `Q`, shows that `I(V) → Q(V)` is
onto for `V ∈ B` (using `Ȟ¹ = 0`), that `Q` again satisfies the hypothesis (using the Čech
acyclicity of injective sheaves, `TopCat.Sheaf.cechComplex_exactAt_of_injective`), and concludes
by dimension shifting.

## Main results

* `CategoryTheory.Sheaf.ShortComplex.app_injective`, `…exists_app_eq`: a short exact sequence of
  abelian sheaves is left exact on sections.
* `TopCat.Sheaf.surjective_app_of_cech`: `I(V) → Q(V)` is onto.
* `TopCat.Sheaf.H'_subsingleton_of_cech`: Cartan's criterion.
-/

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite Abelian TopCat.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- The morphism `ℤ_U ⟶ F` corresponding to a section `s ∈ F(U)`. -/
private noncomputable abbrev fromFree (F : Sheaf J AddCommGrpCat.{v}) {U : C}
    (s : F.obj.obj (op U)) :
    (presheafToSheaf J _).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F :=
  (freeYonedaSheafHomAddEquiv F U).symm s

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}

/-- A monomorphism of abelian sheaves is injective on sections. -/
lemma app_injective_of_mono {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] (U : C) :
    Function.Injective (f.hom.app (op U)) := by
  intro s t h
  apply (freeYonedaSheafHomAddEquiv F U).symm.injective
  rw [← cancel_mono f]
  apply (freeYonedaSheafHomAddEquiv G U).injective
  rw [freeYonedaSheafHomAddEquiv_comp, freeYonedaSheafHomAddEquiv_comp,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, h]

/-- In a short exact sequence of abelian sheaves, a section of the middle term that maps to zero
comes from the first term: sections are left exact. -/
lemma exists_app_eq_of_exact (hS : S.Exact) [Mono S.f] {U : C} (t : S.X₂.obj.obj (op U))
    (ht : S.g.hom.app (op U) t = 0) : ∃ s, S.f.hom.app (op U) s = t := by
  have hk : fromFree S.X₂ t ≫ S.g = 0 := by
    apply (freeYonedaSheafHomAddEquiv S.X₃ U).injective
    rw [freeYonedaSheafHomAddEquiv_comp, AddEquiv.apply_symm_apply, ht, map_zero]
  refine ⟨freeYonedaSheafHomAddEquiv S.X₁ U (hS.lift _ hk), ?_⟩
  rw [← freeYonedaSheafHomAddEquiv_comp, hS.lift_f, AddEquiv.apply_symm_apply]

omit [HasSheafify J AddCommGrpCat.{v}] in
lemma app_comp_app_eq_zero {U : C} (s : S.X₁.obj.obj (op U)) :
    S.g.hom.app (op U) (S.f.hom.app (op U) s) = 0 := by
  have h : S.f.hom ≫ S.g.hom = 0 := congrArg (fun φ ↦ φ.hom) S.zero
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, h]
  rfl

end CategoryTheory.Sheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section CechShortExact

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) {ι : Type w} (U : ι → Opens X)

include hS

lemma cechCochainMap_injective (n : ℕ) :
    Function.Injective (cechCochainMap U S.f.hom n) := by
  have := hS.mono_f
  intro c c' h
  funext x
  exact Sheaf.app_injective_of_mono S.f _ (congrFun h x)

omit hS in
lemma cechCochainMap_g_f (n : ℕ) (c : CechCochain U S.X₁.obj n) :
    cechCochainMap U S.g.hom n (cechCochainMap U S.f.hom n c) = 0 :=
  funext fun _ ↦ Sheaf.app_comp_app_eq_zero _

lemma exists_cechCochainMap_eq (n : ℕ) (c : CechCochain U S.X₂.obj n)
    (hc : cechCochainMap U S.g.hom n c = 0) : ∃ b, cechCochainMap U S.f.hom n b = c := by
  have := hS.mono_f
  choose b hb using fun x ↦ Sheaf.exists_app_eq_of_exact hS.exact (c x) (congrFun hc x)
  exact ⟨b, funext hb⟩

end CechShortExact

section Cartan

variable (B : Set (Opens X)) (Cov : ∀ ⦃n : ℕ⦄, (Fin n → Opens X) → Prop)

/-- The hypothesis of Cartan's criterion on an abelian sheaf `F`: its Čech complex for every
family in `Cov` is exact in positive degrees. -/
def CechAcyclic (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Prop :=
  ∀ ⦃n : ℕ⦄ (U : Fin n → Opens X), Cov U → ∀ p : ℕ, (cechComplex U F.obj).ExactAt (p + 1)

variable {B Cov}

/-- If `0 → F → I → Q → 0` is short exact, `F` has `Ȟ¹ = 0` for the families in `Cov` and every
open cover of `V ∈ B` is refined by a family in `Cov` with union `V`, then `I(V) → Q(V)` is
onto (first step of the proof of Stacks Tag 01EW). -/
theorem surjective_app_of_cech
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (n : ℕ) (U : Fin n → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hF : CechAcyclic Cov S.X₁) {V : Opens X} (hV : V ∈ B) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  have hloc : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hloc
  choose W hWV ht hxW using fun x : V ↦ hloc V s x.1 x.2
  choose t ht using ht
  obtain ⟨n, U, hU, rfl, hUW⟩ := hRefine V hV W hxW
  choose y hy using hUW
  -- local lifts of `s`, as a Čech `0`-cochain of `S.X₂`
  let c : CechCochain U S.X₂.obj 0 := fun z ↦
    S.X₂.obj.map (homOfLE ((cechOpen_le U z 0).trans (hy (z 0)))).op (t (y (z 0)))
  have hgc : cechCochainMap U S.g.hom 0 c = cechAugmentation U S.X₃.obj s := by
    funext z
    simp only [cechCochainMap_apply, c, cechAugmentation_apply]
    rw [NatTrans.naturality_apply, ht]
    exact map_map_apply _ _ _ s
  have hdc : cechCochainMap U S.g.hom 1 (cechD U S.X₂.obj 0 c) = 0 := by
    rw [← cechD_cechCochainMap, hgc, cechD_cechAugmentation]
  obtain ⟨f, hf⟩ := exists_cechCochainMap_eq hS U 1 _ hdc
  have hdf : cechD U S.X₁.obj 1 f = 0 := by
    apply cechCochainMap_injective hS U 2
    rw [← cechD_cechCochainMap, hf, cechD_cechD, map_zero]
  have h1 := hF U hU 0
  rw [cechComplex_exactAt_succ_iff] at h1
  obtain ⟨b, hb⟩ := h1 f hdf
  obtain ⟨t', ht'⟩ := exists_cechAugmentation_eq U S.X₂
    (c - cechCochainMap U S.f.hom 0 b) (by rw [map_sub, cechD_cechCochainMap, hb, hf, sub_self])
  refine ⟨t', cechAugmentation_injective U S.X₃ ?_⟩
  have e : cechAugmentation U S.X₃.obj (S.g.hom.app _ t') =
      cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t') :=
    funext fun z ↦ (NatTrans.naturality_apply S.g.hom _ t').symm
  rw [← hgc, e, ht', map_sub, cechCochainMap_g_f, sub_zero]

/-- If `0 → F → I → Q → 0` is short exact with `I` injective and `F` satisfies Cartan's
hypothesis, so does `Q` (second step of the proof of Stacks Tag 01EW). -/
theorem cechAcyclic_of_shortExact
    (hCov : ∀ ⦃n⦄ (U : Fin n → Opens X), Cov U → ∀ ⦃p⦄ (x : Fin (p + 1) → Fin n),
      cechOpen U x ∈ B)
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (n : ℕ) (U : Fin n → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] (hF : CechAcyclic Cov S.X₁) : CechAcyclic Cov S.X₃ := by
  intro n U hU p
  rw [cechComplex_exactAt_succ_iff]
  intro q hq
  have hsurj : ∀ x : Fin (p + 2) → Fin n, Function.Surjective (S.g.hom.app (op (cechOpen U x))) :=
    fun x ↦ surjective_app_of_cech hRefine hS hF (hCov U hU x)
  choose i hi using fun x ↦ hsurj x (q x)
  have hdi : cechCochainMap U S.g.hom (p + 2) (cechD U S.X₂.obj (p + 1) i) = 0 := by
    rw [← cechD_cechCochainMap, show cechCochainMap U S.g.hom (p + 1) i = q from funext hi, hq]
  obtain ⟨φ, hφ⟩ := exists_cechCochainMap_eq hS U (p + 2) _ hdi
  have hdφ : cechD U S.X₁.obj (p + 2) φ = 0 := by
    apply cechCochainMap_injective hS U (p + 3)
    rw [← cechD_cechCochainMap, hφ, cechD_cechD, map_zero]
  have h2 := hF U hU (p + 1)
  rw [cechComplex_exactAt_succ_iff] at h2
  obtain ⟨ψ, hψ⟩ := h2 φ hdφ
  have hI := cechComplex_exactAt_of_injective S.X₂ U p
  rw [cechComplex_exactAt_succ_iff] at hI
  obtain ⟨j, hj⟩ := hI (i - cechCochainMap U S.f.hom (p + 1) ψ)
    (by rw [map_sub, cechD_cechCochainMap, hψ, hφ, sub_self])
  refine ⟨cechCochainMap U S.g.hom p j, ?_⟩
  rw [cechD_cechCochainMap, hj, map_sub, cechCochainMap_g_f, sub_zero]
  exact funext hi

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Cartan's criterion** (Stacks Tag 01EW). Let `B` be a set of opens and `Cov` a set of finite
families of opens such that all finite intersections of members of a family in `Cov` are in `B`,
and every open cover of a member of `B` is refined by a family in `Cov` covering it. If the Čech
complexes of an abelian sheaf `F` for the families in `Cov` are exact in positive degrees, then
`Hⁿ(V, F) = 0` for every `V ∈ B` and every `n > 0`. -/
theorem H'_subsingleton_of_cech
    (hCov : ∀ ⦃n⦄ (U : Fin n → Opens X), Cov U → ∀ ⦃p⦄ (x : Fin (p + 1) → Fin n),
      cechOpen U x ∈ B)
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (n : ℕ) (U : Fin n → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    (p : ℕ) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : CechAcyclic Cov F) {V : Opens X} (hV : V ∈ B) : Subsingleton (F.H' (p + 1) V) := by
  induction p generalizing F with
  | zero =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _)
      (n₀ := 0) rfl
    obtain ⟨z, rfl⟩ := CategoryTheory.Sheaf.H'.map_zero_surjective S.g
      (surjective_app_of_cech hRefine hS hF hV) y
    rw [← hy, CategoryTheory.Sheaf.H'.map_apply]
    exact (Ext.comp_assoc_of_second_deg_zero (show Ext _ _ 0 from z) (Ext.mk₀ S.g) hS.extClass
      (zero_add 1)).trans (by rw [hS.comp_extClass, Ext.comp_zero]; rfl)
  | succ p ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hsub : Subsingleton (S.X₃.H' (p + 1) V) :=
      ih S.X₃ (cechAcyclic_of_shortExact hCov hRefine hS hF)
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _)
      (n₀ := p + 1) rfl
    rw [← hy, show y = 0 from @Subsingleton.elim _ hsub y 0, Ext.zero_comp]
    rfl

end Cartan

end TopCat.Sheaf
