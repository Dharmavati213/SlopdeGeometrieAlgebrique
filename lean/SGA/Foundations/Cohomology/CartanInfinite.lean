/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Leray

/-!
# Cartan's criterion for families of opens indexed by arbitrary types

`SGA.Foundations.Cohomology.Cartan` proves Cartan's criterion (Stacks Project, Tag 01EW;
Godement, *Théorie des faisceaux*, II.5.9.2) for finite families of opens `Fin n → Opens X`.
On a space that is not compact, such as an open disc in `ℂ`, an open cover need not be refined by
a finite family covering the same set, so that version does not apply. This file proves the
criterion for families `U : ι → Opens X` indexed by arbitrary types `ι`; the argument is the one
of `Cartan.lean` (embed `F` into an injective sheaf and shift dimensions), which never uses
finiteness.

We also record the two steps of dimension shifting along a short exact sequence
`0 → F → G → Q → 0` whose middle term is acyclic on `V` (not necessarily injective), which is how
a resolution by acyclic sheaves computes cohomology (Godement II.4.7; Hörmander, *An introduction
to complex analysis in several variables*, 7.4).

## Main results

* `TopCat.Sheaf.surjective_app_of_cechExactAt_one`, `TopCat.Sheaf.H'_one_subsingleton_of_cech`:
  if every open cover of `V` is refined by a family of opens with union `V` whose Čech complex of
  `F` is exact in degree `1`, then `H¹(V, F) = 0`.
* `TopCat.Sheaf.H'_subsingleton_of_cechAcyclicFor`: Cartan's criterion for a set `B` of opens and
  a class `Cov` of families of opens indexed by arbitrary types.
* `TopCat.Sheaf.H'_subsingleton_of_forall_cech`: if the Čech complexes of `F` for all families of
  opens are exact in positive degrees (e.g. `F` a module over a sheaf of rings with partitions of
  unity), then `Hⁿ(V, F) = 0` for every open `V` and every `n > 0`.
* `TopCat.Sheaf.subsingleton_H'_one_of_shortExact`,
  `TopCat.Sheaf.subsingleton_H'_succ_succ_of_shortExact`: dimension shifting along a short exact
  sequence with acyclic middle term; `TopCat.Sheaf.subsingleton_H'_succ_of_shortExact_right`,
  `TopCat.Sheaf.subsingleton_H'_of_shortExact_of_acyclic`: towards the quotient (a sheaf with a
  finite resolution by acyclic sheaves is acyclic).
* `TopCat.Sheaf.shortExact_of_sections`: a short complex of abelian sheaves which is left exact on
  sections and locally surjective on the right is short exact.
-/

universe w' w u

open CategoryTheory Limits TopologicalSpace Opposite Abelian TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Refinement

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- Let `0 → F → I → Q → 0` be short exact and `V` an open such that every open cover of `V` is
refined by a family of opens (indexed by any type) with union `V` for which the Čech complex of
`F` is exact in degree `1`. Then `I(V) → Q(V)` is onto. (First step of the proof of Stacks
Tag 01EW, for families indexed by arbitrary types.) -/
theorem surjective_app_of_cechExactAt_one (hS : S.ShortExact) {V : Opens X}
    (hRefine : ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (ι : Type w) (U : ι → Opens X), ⨆ i, U i = V ∧ (∀ i, ∃ x, U i ≤ W x) ∧
        (cechComplex U S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  have hloc : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hloc
  choose W hWV ht hxW using fun x : V ↦ hloc V s x.1 x.2
  choose t ht using ht
  obtain ⟨ι, U, rfl, hUW, h1⟩ := hRefine W hxW
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
  obtain ⟨b, hb⟩ := (cechComplex_exactAt_succ_iff U S.X₁.obj 0).mp h1 f hdf
  obtain ⟨t', ht'⟩ := exists_cechAugmentation_eq U S.X₂
    (c - cechCochainMap U S.f.hom 0 b) (by rw [map_sub, cechD_cechCochainMap, hb, hf, sub_self])
  refine ⟨t', cechAugmentation_injective U S.X₃ ?_⟩
  have e : cechAugmentation U S.X₃.obj (S.g.hom.app _ t') =
      cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t') :=
    funext fun z ↦ (NatTrans.naturality_apply S.g.hom _ t').symm
  rw [← hgc, e, ht', map_sub, cechCochainMap_g_f, sub_zero]

variable [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **`H¹` from Čech cohomology of refining families.** If every open cover of `V` is refined by
a family of opens (indexed by any type) with union `V` for which the Čech complex of `F` is exact
in degree `1`, then `H¹(V, F) = 0`. -/
theorem H'_one_subsingleton_of_cech
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {V : Opens X}
    (hRefine : ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (ι : Type w) (U : ι → Opens X), ⨆ i, U i = V ∧ (∀ i, ∃ x, U i ≤ W x) ∧
        (cechComplex U F.obj).ExactAt 1) :
    Subsingleton (F.H' 1 V) := by
  let S := ShortComplex.cokernelSequence (Injective.ι F)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono (Injective.ι F); infer_instance
      epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
  have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
  exact subsingleton_H'_one_of_surjective hS V (surjective_app_of_cechExactAt_one hS hRefine)

end Refinement

section Cartan

variable (Cov : ∀ ⦃ι : Type w⦄, (ι → Opens X) → Prop)

/-- The hypothesis of Cartan's criterion on an abelian sheaf `F`, for a class `Cov` of families
of opens indexed by arbitrary types: the Čech complex of `F` for every family in `Cov` is exact in
positive degrees. (The finite version is `TopCat.Sheaf.CechAcyclic`.) -/
def CechAcyclicFor (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Cov U → ∀ p : ℕ, (cechComplex U F.obj).ExactAt (p + 1)

variable {B : Set (Opens X)} {Cov}

/-- If `0 → F → I → Q → 0` is short exact, `F` satisfies Cartan's hypothesis for `Cov` and every
open cover of `V ∈ B` is refined by a family in `Cov` with union `V`, then `I(V) → Q(V)` is
onto. -/
theorem surjective_app_of_cechAcyclicFor
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (ι : Type w) (U : ι → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (hF : CechAcyclicFor Cov S.X₁) {V : Opens X} (hV : V ∈ B) :
    Function.Surjective (S.g.hom.app (op V)) :=
  surjective_app_of_cechExactAt_one hS fun W hW ↦ by
    obtain ⟨ι, U, hU, hUV, hUW⟩ := hRefine V hV W hW
    exact ⟨ι, U, hUV, hUW, hF U hU 0⟩

/-- If `0 → F → I → Q → 0` is short exact with `I` injective and `F` satisfies Cartan's
hypothesis for `Cov`, so does `Q` (second step of the proof of Stacks Tag 01EW, for families
indexed by arbitrary types). -/
theorem cechAcyclicFor_of_shortExact
    (hCov : ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Cov U → ∀ ⦃p⦄ (x : Fin (p + 1) → ι),
      cechOpen U x ∈ B)
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (ι : Type w) (U : ι → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] (hF : CechAcyclicFor Cov S.X₁) :
    CechAcyclicFor Cov S.X₃ := by
  intro ι U hU p
  rw [cechComplex_exactAt_succ_iff]
  intro q hq
  have hsurj : ∀ x : Fin (p + 2) → ι, Function.Surjective (S.g.hom.app (op (cechOpen U x))) :=
    fun x ↦ surjective_app_of_cechAcyclicFor hRefine hS hF (hCov U hU x)
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

variable [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Cartan's criterion** (Stacks Tag 01EW; Godement II.5.9.2), for families of opens indexed by
arbitrary types. Let `B` be a set of opens and `Cov` a class of families of opens such that all
finite intersections of members of a family in `Cov` are in `B`, and every open cover of a member
`V` of `B` is refined by a family in `Cov` with union `V`. If the Čech complexes of an abelian
sheaf `F` for the families in `Cov` are exact in positive degrees, then `Hⁿ(V, F) = 0` for every
`V ∈ B` and every `n > 0`. -/
theorem H'_subsingleton_of_cechAcyclicFor
    (hCov : ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Cov U → ∀ ⦃p⦄ (x : Fin (p + 1) → ι),
      cechOpen U x ∈ B)
    (hRefine : ∀ V ∈ B, ∀ W : V → Opens X, (∀ x, x.1 ∈ W x) →
      ∃ (ι : Type w) (U : ι → Opens X), Cov U ∧ ⨆ i, U i = V ∧ ∀ i, ∃ x, U i ≤ W x)
    (p : ℕ) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : CechAcyclicFor Cov F) {V : Opens X} (hV : V ∈ B) : Subsingleton (F.H' (p + 1) V) := by
  induction p generalizing F with
  | zero =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    exact subsingleton_H'_one_of_surjective hS V
      (surjective_app_of_cechAcyclicFor hRefine hS hF hV)
  | succ p ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    exact (subsingleton_H'_succ_iff hS V p).mp
      (ih S.X₃ (cechAcyclicFor_of_shortExact hCov hRefine hS hF))

/-- **Acyclicity from Čech acyclicity for all families.** If the Čech complex of an abelian sheaf
`F` for every family of opens (indexed by a type in the universe of `X`) is exact in positive
degrees, then `Hⁿ(V, F) = 0` for every open `V` and every `n > 0`. This applies for instance to
sheaves of modules over the sheaf of smooth functions on a manifold, by partitions of unity
(Godement II.3.7, II.4.4; Hörmander 7.4). -/
theorem H'_subsingleton_of_forall_cech
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ ⦃ι : Type u⦄ (U : ι → Opens X) (p : ℕ), (cechComplex U F.obj).ExactAt (p + 1))
    (p : ℕ) (V : Opens X) : Subsingleton (F.H' (p + 1) V) :=
  H'_subsingleton_of_cechAcyclicFor (B := Set.univ) (Cov := fun _ _ ↦ True)
    (fun _ _ _ _ _ ↦ Set.mem_univ _)
    (fun V _ W hW ↦ ⟨V, fun x ↦ W x ⊓ V, True.intro,
      le_antisymm (iSup_le fun _ ↦ inf_le_right) fun y hy ↦
        Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hW ⟨y, hy⟩, hy⟩,
      fun x ↦ ⟨x, inf_le_left⟩⟩)
    p F (fun _ U _ q ↦ hF U q) (Set.mem_univ V)

end Cartan

section AcyclicResolution

variable [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (V : Opens X)

include hS

/-- Dimension shifting in degree `1`: if `0 → F → G → Q → 0` is short exact, `H¹(V, G) = 0` and
`G(V) → Q(V)` is onto, then `H¹(V, F) = 0`. -/
lemma subsingleton_H'_one_of_shortExact (hG : Subsingleton (S.X₂.H' 1 V))
    (h : Function.Surjective (S.g.hom.app (op V))) : Subsingleton (S.X₁.H' 1 V) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
    (show (x.comp (Ext.mk₀ S.f) (add_zero 1) : S.X₂.H' 1 V) = 0 from
      @Subsingleton.elim _ hG _ _)
    (n₀ := 0) rfl
  obtain ⟨z, rfl⟩ := CategoryTheory.Sheaf.H'.map_zero_surjective S.g h y
  rw [← hy, CategoryTheory.Sheaf.H'.map_apply]
  exact (Ext.comp_assoc_of_second_deg_zero (show Ext _ _ 0 from z) (Ext.mk₀ S.g) hS.extClass
    (zero_add 1)).trans (by rw [hS.comp_extClass, Ext.comp_zero]; rfl)

/-- Dimension shifting in degree `q + 2`: if `0 → F → G → Q → 0` is short exact,
`H^{q+1}(V, Q) = 0` and `H^{q+2}(V, G) = 0`, then `H^{q+2}(V, F) = 0`. -/
lemma subsingleton_H'_succ_succ_of_shortExact (q : ℕ) (hQ : Subsingleton (S.X₃.H' (q + 1) V))
    (hG : Subsingleton (S.X₂.H' (q + 2) V)) : Subsingleton (S.X₁.H' (q + 2) V) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
    (show (x.comp (Ext.mk₀ S.f) (add_zero (q + 2)) : S.X₂.H' (q + 2) V) = 0 from
      @Subsingleton.elim _ hG _ _)
    (n₀ := q + 1) rfl
  rw [← hy, show y = 0 from @Subsingleton.elim _ hQ y 0, Ext.zero_comp]
  rfl

/-- Dimension shifting towards the quotient: if `0 → F → G → Q → 0` is short exact,
`H^{q+1}(V, G) = 0` and `H^{q+2}(V, F) = 0`, then `H^{q+1}(V, Q) = 0`. -/
lemma subsingleton_H'_succ_of_shortExact_right (q : ℕ)
    (hG : Subsingleton (S.X₂.H' (q + 1) V)) (hF : Subsingleton (S.X₁.H' (q + 2) V)) :
    Subsingleton (S.X₃.H' (q + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS x (n₁ := q + 2) rfl
    (@Subsingleton.elim _ hF _ _)
  rw [← hy, show y = 0 from @Subsingleton.elim _ hG y 0, Ext.zero_comp]
  rfl

/-- **Acyclicity passes to quotients**: if `0 → F → G → Q → 0` is short exact and `F`, `G` have
no higher cohomology on `V`, neither has `Q`. Applied `n` times along
`0 → Pₙ → ⋯ → P₀ → M → 0` (split into short exact sequences), it shows that a sheaf with a finite
resolution by sheaves acyclic on `V` is acyclic on `V`. -/
lemma subsingleton_H'_of_shortExact_of_acyclic (hG : ∀ q, Subsingleton (S.X₂.H' (q + 1) V))
    (hF : ∀ q, Subsingleton (S.X₁.H' (q + 1) V)) (q : ℕ) : Subsingleton (S.X₃.H' (q + 1) V) :=
  subsingleton_H'_succ_of_shortExact_right hS V q (hG q) (hF (q + 1))

end AcyclicResolution

section ShortExact

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

variable (hf : ∀ U, Function.Injective (S.f.hom.app U))
  (hfg : ∀ U (b : S.X₂.obj.obj U), S.g.hom.app U b = 0 → ∃ a, S.f.hom.app U a = b)

private lemma app_eq_zero_of_comp {W : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} {k : W ⟶ S.X₂} (hk : k ≫ S.g = 0) (U) (w : W.obj.obj U) :
    S.g.hom.app U (k.hom.app U w) = 0 := by
  have := congrArg (fun φ ↦ φ.hom.app U w) hk
  simpa using this

include hf hfg in
/-- The lift of a morphism `k : W ⟶ X₂` with `k ≫ g = 0` through `f`, section by section. -/
private noncomputable def liftOfSections
    {W : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (k : W ⟶ S.X₂)
    (hk : k ≫ S.g = 0) : W ⟶ S.X₁ :=
  have hl : ∀ U w, S.f.hom.app U ((hfg U _ (app_eq_zero_of_comp hk U w)).choose) =
      k.hom.app U w := fun U w ↦ (hfg U _ (app_eq_zero_of_comp hk U w)).choose_spec
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun w ↦ (hfg U _ (app_eq_zero_of_comp hk U w)).choose
          map_zero' := hf U (by rw [hl, map_zero, map_zero])
          map_add' := fun a b ↦ hf U (by rw [hl, map_add, map_add, hl, hl]) }
      naturality := fun U V i ↦ by
        ext w
        apply hf V
        simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply]
        erw [NatTrans.naturality_apply S.f.hom i, hl, hl]
        exact NatTrans.naturality_apply k.hom i w }

private lemma liftOfSections_app
    {W : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (k : W ⟶ S.X₂)
    (hk : k ≫ S.g = 0) (U) (w : W.obj.obj U) :
    S.f.hom.app U ((liftOfSections hf hfg k hk).hom.app U w) = k.hom.app U w :=
  (hfg U _ (app_eq_zero_of_comp hk U w)).choose_spec

/-- If `f` is injective on sections and every section killed by `g` comes from `f`, then `f` is
a kernel of `g` in the category of abelian sheaves. -/
noncomputable def isLimitKernelForkOfSections : IsLimit (KernelFork.ofι S.f S.zero) :=
  KernelFork.IsLimit.ofι _ _ (fun k hk ↦ liftOfSections hf hfg k hk)
    (fun k hk ↦ by
      ext U w
      exact liftOfSections_app hf hfg k hk U w)
    (fun {W} k hk m hm ↦ by
      ext U w
      apply hf U
      rw [liftOfSections_app hf hfg k hk U w, ← hm]
      rfl)

include hf hfg in
/-- **Short exact sequences of abelian sheaves from sections.** A short complex
`0 → F → G → Q → 0` of abelian sheaves is short exact if `F(U) → G(U)` is injective and
`F(U) → G(U) → Q(U)` is exact for every open `U`, and `G → Q` is locally surjective. -/
theorem shortExact_of_sections (hg : TopCat.Presheaf.IsLocallySurjective S.g.hom) :
    S.ShortExact := by
  obtain ⟨hex, hmono⟩ := S.exact_and_mono_f_iff_f_is_kernel.mpr
    ⟨isLimitKernelForkOfSections hf hfg⟩
  exact ShortComplex.ShortExact.mk' hex hmono
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mp hg)

end ShortExact

end TopCat.Sheaf
