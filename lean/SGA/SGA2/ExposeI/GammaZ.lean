/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sets.Closeds
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# SGA 2, Exposé I, §1: the functors `Γ_Z`, `Γ̲_Z`

For a topological space `X`, an abelian sheaf `F` on `X`, and a **closed** subset `Z ⊆ X`,
SGA defines (I.1, (2) and (4))

```
Γ_Z(F) = { s ∈ Γ(X, F) | supp(s) ⊆ Z } = ker( Γ(X, F) → Γ(X \ Z, F) ).
```

More generally, for an open `U ⊆ X` one sets

```
Γ(U, Γ̲_Z(F)) = Γ_{U ∩ Z}(F|_U) = ker( F(U) → F(U \ Z) )
```

(I.1, (8)). When `Z` is closed this realises `Γ̲_Z(F)` as a subsheaf of `F`
(canonical immersion (8')).

The locally closed case (I.1, (3)) reduces to the closed case on an open in which `Z`
is closed; it is not formalised in this file.

Numbering follows Grothendieck (`I.1.1`, …). English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}} (F : Sheaf AddCommGrpCat.{u} X)

/-- Restriction map `F(U) → F(U \ Z)` for closed `Z`. -/
noncomputable def restrictToComplement (Z : Closeds X) (U : Opens X) :
    F.1.obj (op U) ⟶ F.1.obj (op (U ⊓ Z.compl)) :=
  F.1.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op

/-- **I.1, (4)/(8):** sections of `F` over `U` with support in `Z ∩ U`, for closed `Z`.

This is `Γ_{U ∩ Z}(F|_U)`, realised as the kernel of restriction to `U \ Z`. -/
noncomputable def gammaZSections (Z : Closeds X) (U : Opens X) :
    AddSubgroup (F.1.obj (op U)) :=
  (restrictToComplement F Z U).hom.ker

/-- **I.1, (2):** global sections with support in the closed set `Z`. -/
noncomputable abbrev gammaZ (Z : Closeds X) : AddSubgroup (F.1.obj (op (⊤ : Opens X))) :=
  gammaZSections F Z ⊤

lemma mem_gammaZSections_iff {Z : Closeds X} {U : Opens X} {s : F.1.obj (op U)} :
    s ∈ gammaZSections F Z U ↔ (restrictToComplement F Z U).hom s = 0 :=
  Iff.rfl

lemma mem_gammaZ_iff {Z : Closeds X} {s : F.1.obj (op (⊤ : Opens X))} :
    s ∈ gammaZ F Z ↔ (restrictToComplement F Z ⊤).hom s = 0 :=
  Iff.rfl

/-- **I.1:** if `Z = X`, then `Γ_Z(U, F) = F(U)`. -/
lemma gammaZSections_top (U : Opens X) :
    gammaZSections F (⊤ : Closeds X) U = ⊤ := by
  ext s
  simp only [AddSubgroup.mem_top, mem_gammaZSections_iff, iff_true]
  have hOpen : U ⊓ (⊤ : Closeds X).compl = ⊥ := by
    ext x
    simp [Closeds.compl]
  have hz : IsZero (F.1.obj (op (U ⊓ (⊤ : Closeds X).compl))) :=
    (Sheaf.isTerminalOfEqEmpty F hOpen).isZero
  have h0 : restrictToComplement F (⊤ : Closeds X) U = 0 := hz.eq_of_tgt _ _
  rw [h0]
  simp

/-- **I.1:** `Γ_∅(U, F) = 0`.

After the identification `U \ ∅ = U`, the restriction map is an isomorphism
(in fact an identity), so its kernel vanishes. -/
lemma gammaZSections_bot (U : Opens X) :
    gammaZSections F (⊥ : Closeds X) U = ⊥ := by
  have hOpen : U ⊓ (⊥ : Closeds X).compl = U := by
    ext x
    simp [Closeds.compl]
  have : IsIso (homOfLE (inf_le_left : U ⊓ (⊥ : Closeds X).compl ≤ U)) :=
    ⟨homOfLE (hOpen.symm.trans_le le_rfl), by constructor <;> rfl⟩
  have : IsIso (restrictToComplement F (⊥ : Closeds X) U) := by
    dsimp [restrictToComplement]
    infer_instance
  -- Kernel of an isomorphism of abelian groups is trivial.
  ext s
  simp only [AddSubgroup.mem_bot, mem_gammaZSections_iff]
  constructor
  · intro hs
    -- apply inverse to both sides of `restrict s = 0`
    have := congrArg (inv (restrictToComplement F (⊥ : Closeds X) U)).hom hs
    simpa using this
  · rintro rfl
    simp

/-- **I.1:** monotonicity in the closed support. If `Z' ≤ Z` then
`Γ_{Z'}(U, F) ≤ Γ_Z(U, F)`. -/
lemma gammaZSections_mono {Z' Z : Closeds X} (h : Z' ≤ Z) (U : Opens X) :
    gammaZSections F Z' U ≤ gammaZSections F Z U := by
  intro s hs
  rw [mem_gammaZSections_iff] at hs ⊢
  have hle : U ⊓ Z.compl ≤ U ⊓ Z'.compl := by
    intro x hx
    exact ⟨hx.1, fun hxZ => hx.2 (h hxZ)⟩
  have hfac :
      restrictToComplement F Z U =
        restrictToComplement F Z' U ≫ F.1.map (homOfLE hle).op := by
    dsimp [restrictToComplement]
    rw [← Functor.map_comp]
    rfl
  calc
    (restrictToComplement F Z U).hom s
        = (restrictToComplement F Z' U ≫ F.1.map (homOfLE hle).op).hom s := by rw [hfac]
      _ = (F.1.map (homOfLE hle).op).hom ((restrictToComplement F Z' U).hom s) := rfl
      _ = (F.1.map (homOfLE hle).op).hom 0 := by rw [hs]
      _ = 0 := by simp

/-- Global form of monotonicity. -/
lemma gammaZ_mono {Z' Z : Closeds X} (h : Z' ≤ Z) : gammaZ F Z' ≤ gammaZ F Z :=
  gammaZSections_mono F h ⊤

/-- **I.1.8 (closed case, degree 0):** if `Z' ≤ Z` are closed, then

```
Γ_{Z'}(F) = Γ_Z(F) ∩ ker(Γ(X,F) → Γ(X \ Z', F)).
```

Thus `0 → Γ_{Z'}(F) → Γ_Z(F) → Γ(X \ Z', F)` is exact at the first two terms.
(Surjectivity onto `Γ_{Z\Z'}(F)` when `F` is flasque is I.1.8 in full; see `Flasque.lean`.) -/
lemma exact_gammaZ_of_le {Z' Z : Closeds X} (h : Z' ≤ Z) :
    gammaZ F Z' = gammaZ F Z ⊓ (restrictToComplement F Z' ⊤).hom.ker := by
  ext s
  simp only [AddSubgroup.mem_inf, mem_gammaZ_iff, AddMonoidHom.mem_ker]
  constructor
  · intro hs
    exact ⟨gammaZSections_mono F h ⊤ hs, hs⟩
  · intro ⟨_, hsZ'⟩
    exact hsZ'

/-- **I.1:** the zero section always has support in `Z`. -/
lemma zero_mem_gammaZSections (Z : Closeds X) (U : Opens X) :
    (0 : F.1.obj (op U)) ∈ gammaZSections F Z U :=
  AddSubgroup.zero_mem _

/-- Functoriality in `F`: images of sections supported in `Z` remain supported in `Z`. -/
lemma map_mem_gammaZSections {G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    {Z : Closeds X} {U : Opens X} {s : F.1.obj (op U)}
    (hs : s ∈ gammaZSections F Z U) :
    (φ.hom.app (op U)).hom s ∈ gammaZSections G Z U := by
  rw [mem_gammaZSections_iff] at hs ⊢
  have hnat := φ.hom.naturality (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op
  -- `F.map i ≫ φ.app _ = φ.app _ ≫ G.map i`
  have hcomp :
      (φ.hom.app (op (U ⊓ Z.compl))).hom ((restrictToComplement F Z U).hom s) =
        (restrictToComplement G Z U).hom ((φ.hom.app (op U)).hom s) := by
    dsimp [restrictToComplement]
    exact congrArg (fun (f : F.1.obj (op U) ⟶ G.1.obj (op (U ⊓ Z.compl))) => f.hom s) hnat
  have hL :
      (φ.hom.app (op (U ⊓ Z.compl))).hom ((restrictToComplement F Z U).hom s) = 0 := by
    rw [hs, map_zero]
  exact hcomp.symm.trans hL

end SGA.SGA2.ExposeI
