/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Transport of Čech complexes

`CohomologyAux.CechTransport U₁ U₂ P₁ P₂`: compatible additive equivalences between the sections
of presheaves `P₁`, `P₂` (on possibly different spaces) over the finite intersections of two
families of opens `U₁`, `U₂`. The Čech complexes are then exact in the same degrees
(`CechTransport.exactAt_iff`).

`CohomologyAux.restrictCechTransport`: for an open immersion `g : Y ⟶ X` and an `𝒪_X`-module `M`,
the Čech complex of `M|_Y` for a family `U` of opens of `Y` is the Čech complex of `M` for the
images `g(Uᵢ)`.
-/

universe w v u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

lemma presheaf_map_map_eq' {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{v} T)
    {U₁ U₂ U₃ U₂' : (TopologicalSpace.Opens T)ᵒᵖ} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₂')
    (d : U₂' ⟶ U₃) (s : P.obj U₁) : P.map b (P.map a s) = P.map d (P.map c s) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← ConcreteCategory.comp_apply, ← P.map_comp,
    Subsingleton.elim (a ≫ b) (c ≫ d)]

section Transport

variable {X₁ X₂ : TopCat.{u}} {ι : Type w} (U₁ : ι → Opens X₁) (U₂ : ι → Opens X₂)
  (P₁ : TopCat.Presheaf AddCommGrpCat.{v} X₁) (P₂ : TopCat.Presheaf AddCommGrpCat.{v} X₂)

/-- Families of additive equivalences between the sections over the finite intersections of two
families of opens, compatible with the face restrictions. -/
structure CechTransport where
  e : ∀ {m : ℕ} (x : Fin (m + 1) → ι),
    P₁.obj (op (cechOpen U₁ x)) ≃+ P₂.obj (op (cechOpen U₂ x))
  comm : ∀ {m : ℕ} (x : Fin (m + 2) → ι) (i : Fin (m + 2))
    (s : P₁.obj (op (cechOpen U₁ (x ∘ i.succAbove)))),
    e x (P₁.map (homOfLE (cechOpen_le_comp U₁ x i.succAbove)).op s) =
      P₂.map (homOfLE (cechOpen_le_comp U₂ x i.succAbove)).op (e (x ∘ i.succAbove) s)

variable {U₁ U₂ P₁ P₂}

/-- The inverse transport. -/
def CechTransport.symm (T : CechTransport U₁ U₂ P₁ P₂) : CechTransport U₂ U₁ P₂ P₁ where
  e x := (T.e x).symm
  comm x i s := by
    apply (T.e x).injective
    rw [AddEquiv.apply_symm_apply, T.comm, AddEquiv.apply_symm_apply]

/-- The induced map on Čech cochains. -/
def CechTransport.cochain (T : CechTransport U₁ U₂ P₁ P₂) (m : ℕ) :
    CechCochain U₁ P₁ m →+ CechCochain U₂ P₂ m where
  toFun c x := T.e x (c x)
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _ _ := funext fun _ ↦ map_add _ _ _

lemma CechTransport.cechD_cochain (T : CechTransport U₁ U₂ P₁ P₂) (m : ℕ)
    (c : CechCochain U₁ P₁ m) :
    cechD U₂ P₂ m (T.cochain m c) = T.cochain (m + 1) (cechD U₁ P₁ m c) := by
  funext x
  change cechD U₂ P₂ m (fun y ↦ T.e y (c y)) x = T.e x (cechD U₁ P₁ m c x)
  rw [cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, T.comm]

lemma CechTransport.cochain_symm (T : CechTransport U₁ U₂ P₁ P₂) (m : ℕ)
    (c : CechCochain U₂ P₂ m) : T.cochain m (T.symm.cochain m c) = c :=
  funext fun _ ↦ AddEquiv.apply_symm_apply _ _

lemma CechTransport.exactAt (T : CechTransport U₁ U₂ P₁ P₂) (p : ℕ)
    (h : (cechComplex U₁ P₁).ExactAt (p + 1)) : (cechComplex U₂ P₂).ExactAt (p + 1) := by
  rw [cechComplex_exactAt_succ_iff] at h ⊢
  intro c hc
  obtain ⟨b, hb⟩ := h (T.symm.cochain (p + 1) c) (by
    rw [T.symm.cechD_cochain, hc, map_zero])
  refine ⟨T.cochain p b, ?_⟩
  rw [T.cechD_cochain, hb, T.cochain_symm]

lemma CechTransport.exactAt_iff (T : CechTransport U₁ U₂ P₁ P₂) (p : ℕ) :
    (cechComplex U₁ P₁).ExactAt (p + 1) ↔ (cechComplex U₂ P₂).ExactAt (p + 1) :=
  ⟨T.exactAt p, T.symm.exactAt p⟩

end Transport

section OpenImmersion

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

lemma image_inf_of_isOpenImmersion (A B : Y.Opens) : g ''ᵁ (A ⊓ B) = g ''ᵁ A ⊓ g ''ᵁ B := by
  ext x
  change x ∈ g.base '' (A ∩ B) ↔ x ∈ g.base '' A ∩ g.base '' B
  rw [Set.image_inter g.isOpenEmbedding.injective]

lemma image_cechOpen {ι : Type*} (U : ι → Y.Opens) {m : ℕ} (x : Fin (m + 1) → ι) :
    g ''ᵁ cechOpen U x = cechOpen (fun i ↦ g ''ᵁ U i) x := by
  induction m with
  | zero =>
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    simp only [cechOpen]
    rw [iInf_unique, iInf_unique]
  | succ m ih =>
    rw [← Fin.cons_self_tail x, cechOpen_cons_eq, cechOpen_cons_eq, image_inf_of_isOpenImmersion,
      ih]

variable (M : X.Modules) {ι : Type*} (U : ι → Y.Opens)

/-- Čech transport along an open immersion. -/
noncomputable def restrictCechTransport :
    CechTransport U (fun i ↦ g ''ᵁ U i) (M.restrict g).presheaf M.presheaf where
  e x :=
    { toFun := fun s ↦ M.presheaf.map (homOfLE (image_cechOpen g U x).ge).op
        (@id Γ(M, g ''ᵁ cechOpen U x) s)
      invFun := fun t ↦ M.presheaf.map (homOfLE (image_cechOpen g U x).le).op t
      left_inv := fun s ↦ by
        change M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ cechOpen U x) s)) =
          @id Γ(M, g ''ᵁ cechOpen U x) s
        rw [presheaf_map_map_eq' M.presheaf _ _ (𝟙 _) (𝟙 _)]
        simp
      right_inv := fun t ↦ by
        change M.presheaf.map _ (M.presheaf.map _ t) = t
        rw [presheaf_map_map_eq' M.presheaf _ _ (𝟙 _) (𝟙 _)]
        simp
      map_add' := fun _ _ ↦ map_add _ _ _ }
  comm x i s := by
    change M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ cechOpen U (x ∘ i.succAbove)) s)) =
      M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ cechOpen U (x ∘ i.succAbove)) s))
    exact presheaf_map_map_eq' M.presheaf _ _ _ _ _

end OpenImmersion

end AlgebraicGeometry.CohomologyAux
