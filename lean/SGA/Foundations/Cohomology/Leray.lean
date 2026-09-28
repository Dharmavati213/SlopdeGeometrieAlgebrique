/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cartan

/-!
# Leray's acyclicity theorem (vanishing form)

Let `U₁, …, Uₙ` be opens of a topological space with union `W`, and `F` an abelian sheaf whose
cohomology vanishes in positive degrees on every finite intersection `U_x` of the `Uᵢ`. Leray's
theorem (Stacks Project, Tag 01ET; Godement II.5.9.1) says that the Čech cohomology of `F` for
the cover `(Uᵢ)` computes `H^*(W, F)`. Here we prove the form of it that does not need a
comparison map: for every `p ≥ 1`, the Čech complex of `F` is exact in degree `p` if and only if
`Hᵖ(W, F) = 0` (`TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H'`).

The proof is by dimension shifting along `0 → F → I → Q → 0` with `I` injective, as in Cartan's
criterion; the Čech complex of `I` is exact (`TopCat.Sheaf.cechComplex_exactAt_of_injective`).

The isomorphism form is `TopCat.Sheaf.nonempty_cechHomologyIso` in
`SGA.Foundations.Cohomology.CechComparison`.
-/

universe w u

open CategoryTheory Limits TopologicalSpace Opposite Abelian TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

section Ext

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (V : Opens X)

include hS

/-- If `H¹(V, F) = 0` for the kernel `F` of `I ⟶ Q`, then `I(V) → Q(V)` is onto. -/
lemma surjective_app_of_subsingleton_H'_one (h : Subsingleton (S.X₁.H' 1 V)) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  let y : S.X₃.H' 0 V := (CategoryTheory.Sheaf.H'.equiv₀ S.X₃ V).symm s
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hS y (zero_add 1)
    (@Subsingleton.elim _ h _ _)
  let z' : S.X₂.H' 0 V := z
  refine ⟨CategoryTheory.Sheaf.H'.equiv₀ S.X₂ V z', ?_⟩
  rw [← CategoryTheory.Sheaf.H'.equiv₀_naturality, CategoryTheory.Sheaf.H'.map_apply]
  change CategoryTheory.Sheaf.H'.equiv₀ S.X₃ V (z.comp (Ext.mk₀ S.g) (add_zero 0)) = s
  rw [hz]
  exact AddEquiv.apply_symm_apply _ s

/-- With `I` injective, if `I(V) → Q(V)` is onto then `H¹(V, F) = 0`. -/
lemma subsingleton_H'_one_of_surjective [Injective S.X₂]
    (h : Function.Surjective (S.g.hom.app (op V))) : Subsingleton (S.X₁.H' 1 V) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _)
    (n₀ := 0) rfl
  obtain ⟨z, rfl⟩ := CategoryTheory.Sheaf.H'.map_zero_surjective S.g h y
  rw [← hy, CategoryTheory.Sheaf.H'.map_apply]
  exact (Ext.comp_assoc_of_second_deg_zero (show Ext _ _ 0 from z) (Ext.mk₀ S.g) hS.extClass
    (zero_add 1)).trans (by rw [hS.comp_extClass, Ext.comp_zero]; rfl)

/-- With `I` injective, `H^{q+1}(V, Q) = 0` if and only if `H^{q+2}(V, F) = 0`. -/
lemma subsingleton_H'_succ_iff [Injective S.X₂] (q : ℕ) :
    Subsingleton (S.X₃.H' (q + 1) V) ↔ Subsingleton (S.X₁.H' (q + 2) V) := by
  constructor
  · intro hsub
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _)
      (n₀ := q + 1) rfl
    rw [← hy, show y = 0 from @Subsingleton.elim _ hsub y 0, Ext.zero_comp]
    rfl
  · intro hsub
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS (show Ext _ _ (q + 1) from x) rfl
      (@Subsingleton.elim _ hsub _ _)
    rw [← hy, show y = 0 from Ext.eq_zero_of_injective y, Ext.zero_comp]
    rfl

end Ext

section Cech

omit [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) {n : ℕ} (U : Fin n → Opens X)
  (hsurj : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
    Function.Surjective (S.g.hom.app (op (cechOpen U x))))

include hS hsurj

/-- In a short exact sequence `0 → F → I → Q → 0` with `I` injective which is exact on the
sections over all `U_x`, the Čech complex of `F` is exact in degree `p + 2` iff the one of `Q` is
exact in degree `p + 1`. -/
lemma cechComplex_exactAt_succ_succ_iff [Injective S.X₂] (p : ℕ) :
    (cechComplex U S.X₁.obj).ExactAt (p + 2) ↔ (cechComplex U S.X₃.obj).ExactAt (p + 1) := by
  have hI := cechComplex_exactAt_of_injective S.X₂ U
  constructor
  · intro hF
    rw [cechComplex_exactAt_succ_iff] at hF ⊢
    intro q hq
    choose i hi using fun x ↦ hsurj x (q x)
    have hdi : cechCochainMap U S.g.hom (p + 2) (cechD U S.X₂.obj (p + 1) i) = 0 := by
      rw [← cechD_cechCochainMap, show cechCochainMap U S.g.hom (p + 1) i = q from funext hi, hq]
    obtain ⟨φ, hφ⟩ := exists_cechCochainMap_eq hS U (p + 2) _ hdi
    have hdφ : cechD U S.X₁.obj (p + 2) φ = 0 := by
      apply cechCochainMap_injective hS U (p + 3)
      rw [← cechD_cechCochainMap, hφ, cechD_cechD, map_zero]
    obtain ⟨ψ, hψ⟩ := hF φ hdφ
    have hIp := hI p
    rw [cechComplex_exactAt_succ_iff] at hIp
    obtain ⟨j, hj⟩ := hIp (i - cechCochainMap U S.f.hom (p + 1) ψ)
      (by rw [map_sub, cechD_cechCochainMap, hψ, hφ, sub_self])
    refine ⟨cechCochainMap U S.g.hom p j, ?_⟩
    rw [cechD_cechCochainMap, hj, map_sub, cechCochainMap_g_f, sub_zero]
    exact funext hi
  · intro hQ
    rw [cechComplex_exactAt_succ_iff] at hQ ⊢
    intro φ hφ
    have hIp := hI (p + 1)
    rw [cechComplex_exactAt_succ_iff] at hIp
    obtain ⟨i, hi⟩ := hIp (cechCochainMap U S.f.hom (p + 2) φ)
      (by rw [cechD_cechCochainMap, hφ, map_zero])
    have hgi : cechD U S.X₃.obj (p + 1) (cechCochainMap U S.g.hom (p + 1) i) = 0 := by
      rw [cechD_cechCochainMap, hi, cechCochainMap_g_f]
    obtain ⟨q', hq'⟩ := hQ _ hgi
    choose i' hi' using fun x ↦ hsurj x (q' x)
    obtain ⟨ψ, hψ⟩ := exists_cechCochainMap_eq hS U (p + 1) (i - cechD U S.X₂.obj p i') (by
      rw [map_sub, ← cechD_cechCochainMap, show cechCochainMap U S.g.hom p i' = q' from funext hi',
        hq', sub_self])
    refine ⟨ψ, cechCochainMap_injective hS U (p + 2) ?_⟩
    rw [← cechD_cechCochainMap, hψ, map_sub, cechD_cechD, sub_zero, hi]

/-- In a short exact sequence `0 → F → I → Q → 0` with `I` injective which is exact on the
sections over all `U_x`, the Čech complex of `F` is exact in degree `1` iff `I(W) → Q(W)` is onto,
`W = ⋃ Uᵢ`. -/
lemma cechComplex_exactAt_one_iff [Injective S.X₂] :
    (cechComplex U S.X₁.obj).ExactAt 1 ↔ Function.Surjective (S.g.hom.app (op (⨆ i, U i))) := by
  have hI := cechComplex_exactAt_of_injective S.X₂ U 0
  rw [cechComplex_exactAt_succ_iff] at hI
  rw [cechComplex_exactAt_succ_iff]
  constructor
  · intro hF s
    choose t ht using fun x : Fin 1 → Fin n ↦ hsurj x (cechAugmentation U S.X₃.obj s x)
    have hgt : cechCochainMap U S.g.hom 0 t = cechAugmentation U S.X₃.obj s := funext ht
    have hdt : cechCochainMap U S.g.hom 1 (cechD U S.X₂.obj 0 t) = 0 := by
      rw [← cechD_cechCochainMap, hgt, cechD_cechAugmentation]
    obtain ⟨f, hf⟩ := exists_cechCochainMap_eq hS U 1 _ hdt
    have hdf : cechD U S.X₁.obj 1 f = 0 := by
      apply cechCochainMap_injective hS U 2
      rw [← cechD_cechCochainMap, hf, cechD_cechD, map_zero]
    obtain ⟨b, hb⟩ := hF f hdf
    obtain ⟨t', ht'⟩ := exists_cechAugmentation_eq U S.X₂
      (t - cechCochainMap U S.f.hom 0 b) (by rw [map_sub, cechD_cechCochainMap, hb, hf, sub_self])
    refine ⟨t', cechAugmentation_injective U S.X₃ ?_⟩
    have e : cechAugmentation U S.X₃.obj (S.g.hom.app _ t') =
        cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t') :=
      funext fun z ↦ (NatTrans.naturality_apply S.g.hom _ t').symm
    rw [← hgt, e, ht', map_sub, cechCochainMap_g_f, sub_zero]
  · intro hW φ hφ
    obtain ⟨i, hi⟩ := hI (cechCochainMap U S.f.hom 1 φ)
      (by rw [cechD_cechCochainMap, hφ, map_zero])
    have hgi : cechD U S.X₃.obj 0 (cechCochainMap U S.g.hom 0 i) = 0 := by
      rw [cechD_cechCochainMap, hi, cechCochainMap_g_f]
    obtain ⟨s, hs⟩ := exists_cechAugmentation_eq U S.X₃ _ hgi
    obtain ⟨t, rfl⟩ := hW s
    have e : cechAugmentation U S.X₃.obj (S.g.hom.app _ t) =
        cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t) :=
      funext fun z ↦ (NatTrans.naturality_apply S.g.hom _ t).symm
    obtain ⟨ψ, hψ⟩ := exists_cechCochainMap_eq hS U 0 (i - cechAugmentation U S.X₂.obj t) (by
      rw [map_sub, ← e, hs, sub_self])
    refine ⟨ψ, cechCochainMap_injective hS U 1 ?_⟩
    rw [← cechD_cechCochainMap, hψ, map_sub, cechD_cechAugmentation, sub_zero, hi]

end Cech

/-- **Leray's acyclicity theorem, vanishing form** (Stacks Tag 01ET). Let `U₁, …, Uₙ` be opens
with union `W` and `F` an abelian sheaf with `H^q(U_x, F) = 0` for all `q > 0` and all finite
intersections `U_x` of the `Uᵢ`. Then, for every `p ≥ 1`, the Čech complex of `F` for `(Uᵢ)` is
exact in degree `p` if and only if `Hᵖ(W, F) = 0`. -/
theorem cechComplex_exactAt_iff_subsingleton_H' {n : ℕ} (U : Fin n → Opens X) (p : ℕ)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ), Subsingleton (F.H' (q + 1) (cechOpen U x))) :
    (cechComplex U F.obj).ExactAt (p + 1) ↔ Subsingleton (F.H' (p + 1) (⨆ i, U i)) := by
  induction p generalizing F with
  | zero =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    exact (cechComplex_exactAt_one_iff hS U
      (fun x ↦ surjective_app_of_subsingleton_H'_one hS _ (hF x 0))).trans
      ⟨fun h ↦ subsingleton_H'_one_of_surjective hS _ h,
        fun h ↦ surjective_app_of_subsingleton_H'_one hS _ h⟩
  | succ p ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι F)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι F); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι F)); infer_instance }
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hQ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ) :
        Subsingleton (S.X₃.H' (q + 1) (cechOpen U x)) :=
      (subsingleton_H'_succ_iff hS _ q).mpr (hF x (q + 1))
    exact (cechComplex_exactAt_succ_succ_iff hS U
      (fun x ↦ surjective_app_of_subsingleton_H'_one hS _ (hF x 0)) p).trans
      ((ih S.X₃ hQ).trans (subsingleton_H'_succ_iff hS _ p))

end TopCat.Sheaf
