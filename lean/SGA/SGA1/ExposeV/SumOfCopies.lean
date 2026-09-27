/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import SGA.SGA1.ExposeV.FiniteQuotient

/-!
# SGA 1, Exposé V, end of §1: the schemes `Y × E`

For a set `E`, `Y × E` is the sum of copies of `Y` indexed by `E`; it is characterized by
`Hom(Y × E, Z) = Hom(E, Hom(Y, Z))` (the universal property of the coproduct). If a group `G`
acts on `E`, it acts on `Y × E` by permuting the summands, and `(Y × E)/G = Y × (E/G)`
(`isQuotient_sumCopies`). The formulas `(Y × E) ×_Z Z' = (Y ×_Z Z') × E`
(`isIso_sigmaDesc_pullbackMap_sumCopies`), `(Y × E) × F = Y × (F × E)` (`sumCopiesSumCopiesIso`)
and `Y × (E × F) = (Y × E) ×_Y (Y × F)` (`isIso_sigmaDesc_pullbackLift_sumCopies`) are proved
by identifying open covers by disjoint open immersions with sums
(`isIso_sigmaDesc_of_disjoint`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeV

section Basic

variable (Y : Scheme.{u}) (E : Type u)

/-- V.1: `Y × E`, the sum of copies of `Y` indexed by the set `E`. -/
noncomputable abbrev sumCopies : Scheme.{u} := ∐ fun _ : E ↦ Y

/-- V.1, formula `(*)`: `Hom(Y × E, Z) = Hom(E, Hom(Y, Z))`. -/
noncomputable def sumCopiesHomEquiv (Z : Scheme.{u}) : (sumCopies Y E ⟶ Z) ≃ (E → (Y ⟶ Z)) where
  toFun f e := Sigma.ι (fun _ : E ↦ Y) e ≫ f
  invFun φ := Sigma.desc φ
  left_inv f := Sigma.hom_ext _ _ fun e ↦ by simp
  right_inv φ := funext fun e ↦ by simp

variable {E} (G : Type*) [Group G] [MulAction G E]

/-- The action of `g` on `Y × E`, sending the summand of index `e` to that of `g • e`. -/
noncomputable def sumCopiesAction (g : G) : sumCopies Y E ⟶ sumCopies Y E :=
  Sigma.desc fun e ↦ Sigma.ι (fun _ : E ↦ Y) (g • e)

/-- The projection `Y × E ⟶ Y × (E/G)`. -/
noncomputable def sumCopiesProj : sumCopies Y E ⟶ sumCopies Y (MulAction.orbitRel.Quotient G E) :=
  Sigma.desc fun e ↦ Sigma.ι (fun _ ↦ Y) (Quotient.mk _ e)

@[reassoc (attr := simp)]
lemma ι_sumCopiesAction (g : G) (e : E) :
    Sigma.ι (fun _ : E ↦ Y) e ≫ sumCopiesAction Y G g = Sigma.ι (fun _ : E ↦ Y) (g • e) :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
lemma ι_sumCopiesProj (e : E) :
    Sigma.ι (fun _ : E ↦ Y) e ≫ sumCopiesProj Y G = Sigma.ι (fun _ ↦ Y) (Quotient.mk _ e) :=
  Sigma.ι_desc _ _

/-- V.1: `(Y × E)/G = Y × (E/G)`. -/
theorem isQuotient_sumCopies : IsQuotient (sumCopiesAction Y G) (sumCopiesProj Y (E := E) G) := by
  refine ⟨fun g ↦ Sigma.hom_ext _ _ fun e ↦ ?_, fun {Z} f hf ↦ ?_⟩
  · simp only [ι_sumCopiesAction_assoc, ι_sumCopiesProj]
    congr 1
    exact Quotient.sound ⟨g, rfl⟩
  have hf' : ∀ (g : G) (e : E), Sigma.ι (fun _ : E ↦ Y) (g • e) ≫ f = Sigma.ι _ e ≫ f :=
    fun g e ↦ by rw [← ι_sumCopiesAction_assoc Y G g e, hf]
  have key : ∀ e : E, Sigma.ι (fun _ : E ↦ Y) (Quotient.out (Quotient.mk
      (MulAction.orbitRel G E) e)) ≫ f = Sigma.ι _ e ≫ f := fun e ↦ by
    obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel G E) e
    rw [← hg, hf']
  refine ⟨Sigma.desc fun q ↦ Sigma.ι (fun _ : E ↦ Y) q.out ≫ f,
    Sigma.hom_ext _ _ fun e ↦ by simp [key], fun h hh ↦ Sigma.hom_ext _ _ fun q ↦ ?_⟩
  obtain ⟨e, rfl⟩ := Quotient.exists_rep q
  rw [Sigma.ι_desc, key, ← hh, ι_sumCopiesProj_assoc]

end Basic

section Formulas

variable (Y : Scheme.{u}) (E : Type u)

lemma exists_sigmaι_eq {Y : Scheme.{u}} {E : Type u} (z : sumCopies Y E) :
    ∃ e y, Sigma.ι (fun _ : E ↦ Y) e y = z := by
  obtain ⟨⟨e, y⟩, rfl⟩ := (sigmaMk fun _ : E ↦ Y).surjective z
  exact ⟨e, y, (sigmaMk_mk (fun _ : E ↦ Y) e y).symm⟩

/-- A family of open immersions into `S` indexed by `E`, with pairwise disjoint images covering
`S`, identifies `S` with a sum. -/
lemma isIso_sigmaDesc_of_disjoint {E : Type u} {X : E → Scheme.{u}} {S : Scheme.{u}}
    (φ : ∀ e, X e ⟶ S) [∀ e, IsOpenImmersion (φ e)] (hcov : ∀ s, ∃ e x, φ e x = s)
    (hdisj : ∀ e e' x x', φ e x = φ e' x' → e = e') : IsIso (Sigma.desc φ) := by
  have hc : ⨆ e, (φ e).opensRange = ⊤ := top_le_iff.mp fun s _ ↦ by
    obtain ⟨e, x, rfl⟩ := hcov s
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e, x, rfl⟩
  have hd : Pairwise (Function.onFun Disjoint fun e ↦ (φ e).opensRange) := fun e e' hee' ↦
    disjoint_iff.mpr (le_bot_iff.mp fun s ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ ↦ (hee' (hdisj e e' x x'
      (hx.trans hx'.symm))).elim)
  obtain ⟨h⟩ := nonempty_isColimit_cofanMk_of φ hc hd
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S φ)).mp ⟨h⟩

variable {Y E} {Z Z' : Scheme.{u}} (q : Y ⟶ Z) (h : Z' ⟶ Z)

/-- End of V.1: `(Y × E) ×_Z Z' = (Y ×_Z Z') × E`. -/
theorem isIso_sigmaDesc_pullbackMap_sumCopies :
    IsIso (Sigma.desc fun e : E ↦ pullback.map q h (Sigma.desc fun _ : E ↦ q) h
      (Sigma.ι (fun _ : E ↦ Y) e) (𝟙 Z') (𝟙 Z) (by simp) (by simp) :
      sumCopies (pullback q h) E ⟶ pullback (Sigma.desc fun _ : E ↦ q) h) := by
  refine isIso_sigmaDesc_of_disjoint _ (fun z ↦ ?_) (fun e e' x x' hxx' ↦ ?_)
  · obtain ⟨e, y, hy⟩ := exists_sigmaι_eq (pullback.fst _ h z)
    have hz : z ∈ Set.range (pullback.map q h (Sigma.desc fun _ : E ↦ q) h
        (Sigma.ι (fun _ : E ↦ Y) e) (𝟙 Z') (𝟙 Z) (by simp) (by simp)) := by
      rw [Scheme.Pullback.range_map]
      exact ⟨⟨y, hy⟩, ⟨_, rfl⟩⟩
    obtain ⟨x, hx⟩ := hz
    exact ⟨e, x, hx⟩
  · have := congr_arg (pullback.fst (Sigma.desc fun _ : E ↦ q) h) hxx'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    by_contra hne
    exact (disjoint_iff.mp (disjoint_opensRange_sigmaι (fun _ : E ↦ Y) e e' hne)).le
      ⟨⟨_, rfl⟩, ⟨_, this.symm⟩⟩

variable (Y) in
/-- The structure morphism `Y × E ⟶ Y`. -/
noncomputable abbrev sumCopiesToBase (E : Type u) : sumCopies Y E ⟶ Y :=
  Sigma.desc fun _ : E ↦ 𝟙 Y

lemma eq_of_sigmaι_apply_eq {Y : Scheme.{u}} {E : Type u} {e e' : E} {y y' : Y}
    (h : Sigma.ι (fun _ : E ↦ Y) e y = Sigma.ι (fun _ : E ↦ Y) e' y') : e = e' := by
  by_contra hne
  exact (disjoint_iff.mp (disjoint_opensRange_sigmaι (fun _ : E ↦ Y) e e' hne)).le
    ⟨⟨_, rfl⟩, ⟨_, h.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
variable (Y) in
/-- End of V.1: `Y × (E × F) = (Y × E) ×_Y (Y × F)`. -/
theorem isIso_sigmaDesc_pullbackLift_sumCopies (F : Type u) :
    IsIso (Sigma.desc fun ef : E × F ↦ pullback.lift (Sigma.ι (fun _ : E ↦ Y) ef.1)
      (Sigma.ι (fun _ : F ↦ Y) ef.2) (by simp) :
      sumCopies Y (E × F) ⟶ pullback (sumCopiesToBase Y E) (sumCopiesToBase Y F)) := by
  let ψ : ∀ ef : E × F, pullback (𝟙 Y) (𝟙 Y) ⟶ pullback (sumCopiesToBase Y E)
      (sumCopiesToBase Y F) := fun ef ↦ pullback.map (𝟙 Y) (𝟙 Y) _ _
    (Sigma.ι (fun _ : E ↦ Y) ef.1) (Sigma.ι (fun _ : F ↦ Y) ef.2) (𝟙 Y) (by simp) (by simp)
  have hφ : ∀ ef : E × F, pullback.lift (Sigma.ι (fun _ : E ↦ Y) ef.1)
      (Sigma.ι (fun _ : F ↦ Y) ef.2) (by simp) = inv (pullback.fst (𝟙 Y) (𝟙 Y)) ≫ ψ ef := by
    intro ef
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext
    · simp [ψ, pullback.map]
    · have hc : pullback.fst (𝟙 Y) (𝟙 Y) = pullback.snd (𝟙 Y) (𝟙 Y) := by
        simpa using pullback.condition (f := 𝟙 Y) (g := 𝟙 Y)
      simp [ψ, pullback.map, hc]
  have : ∀ ef : E × F, IsOpenImmersion (pullback.lift (f := sumCopiesToBase Y E)
      (g := sumCopiesToBase Y F) (Sigma.ι (fun _ : E ↦ Y) ef.1)
      (Sigma.ι (fun _ : F ↦ Y) ef.2) (by simp)) := fun ef ↦ by rw [hφ]; infer_instance
  refine isIso_sigmaDesc_of_disjoint _ (fun z ↦ ?_) (fun ef ef' x x' hxx' ↦ ?_)
  · obtain ⟨e, y, hy⟩ :=
      exists_sigmaι_eq (pullback.fst (sumCopiesToBase Y E) (sumCopiesToBase Y F) z)
    obtain ⟨f, y', hy'⟩ :=
      exists_sigmaι_eq (pullback.snd (sumCopiesToBase Y E) (sumCopiesToBase Y F) z)
    have hz : z ∈ Set.range (ψ (e, f)) := by
      rw [Scheme.Pullback.range_map]
      exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨(e, f), pullback.fst (𝟙 Y) (𝟙 Y) w, ?_⟩
    rw [hφ, ← Scheme.Hom.comp_apply, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, hw]
  · have h₁ := congr_arg (pullback.fst (sumCopiesToBase Y E) (sumCopiesToBase Y F)) hxx'
    have h₂ := congr_arg (pullback.snd (sumCopiesToBase Y E) (sumCopiesToBase Y F)) hxx'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst,
      pullback.lift_fst] at h₁
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd,
      pullback.lift_snd] at h₂
    exact Prod.ext (eq_of_sigmaι_apply_eq h₁) (eq_of_sigmaι_apply_eq h₂)


variable (Y) in
/-- End of V.1: `(Y × E) × F = Y × (F × E)`. -/
noncomputable def sumCopiesSumCopiesIso (E F : Type u) :
    sumCopies (sumCopies Y E) F ≅ sumCopies Y (F × E) :=
  sigmaSigmaIso (fun _ : F ↦ E) (fun _ _ ↦ Y) ≪≫
    Sigma.reindex (Equiv.sigmaEquivProd F E) (fun _ ↦ Y)

end Formulas

end SGA.SGA1.ExposeV
