/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Functors
import SGA.SGA2.ExposeI.GammaZ

/-!
# SGA 2, Exposé I, §1: the sheaf `Γ̲_Z` (closed supports)

For closed `Z ⊆ X`, SGA defines the sheaf `Γ̲_Z(F)` on `X` by
`Γ(U, Γ̲_Z(F)) = Γ_{U ∩ Z}(F|_U)` (I.1, (8)), and records a canonical immersion
`Γ̲_Z(F) ↪ F` (I.1, (8')).

We realise `Γ̲_Z(F)` as the **kernel** of the unit of the adjunction
`j^* ⊣ j_*` for the open immersion `j : X \ Z ↪ X`. This matches the
degree-0 identification of I.2.11: `ℋ_Z^0(F) = ker(F → j_* j^*(F))`.

The sectionwise description `gammaZSections` of `GammaZ.lean` is the concrete
avatar of the same kernel on each open; the comparison of the adjunction unit
with `restrictToComplement` is the content of the open-immersion pullback iso
in mathlib (`Topology.IsOpenEmbedding.sheafPullbackIso`).

Numbering follows Grothendieck. English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Open immersion of the complement of a closed set. -/
noncomputable def complementInclusion (Z : Closeds X) :
    (Opens.toTopCat X).obj Z.compl ⟶ X :=
  Opens.inclusion' Z.compl

lemma isOpenEmbedding_complementInclusion (Z : Closeds X) :
    IsOpenEmbedding (complementInclusion Z) :=
  Z.compl.isOpenEmbedding

/-- **I.1 (8') / I.2.11:** the unit `F → j_* j^* F` for `j : X \ Z ↪ X`. -/
noncomputable def toComplementPushforward (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    F ⟶ (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).obj
      ((Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).obj F) :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (complementInclusion Z)).unit.app F

/-- **I.1, (8):** the sheaf `Γ̲_Z(F)` of sections with support in the closed set `Z`. -/
noncomputable abbrev underlineGammaZ (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X :=
  kernel (toComplementPushforward F Z)

/-- **I.1, (8'):** canonical immersion `Γ̲_Z(F) ↪ F`. -/
noncomputable abbrev underlineGammaZ_ι (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    underlineGammaZ F Z ⟶ F :=
  kernel.ι (toComplementPushforward F Z)

instance mono_underlineGammaZ_ι (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    Mono (underlineGammaZ_ι F Z) :=
  equalizer.ι_mono

/-- The immersion composes to zero with the unit to the complement. -/
@[reassoc (attr := simp)]
lemma underlineGammaZ_ι_comp_toComplement (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    underlineGammaZ_ι F Z ≫ toComplementPushforward F Z = 0 :=
  kernel.condition _

/-- Functoriality of `Γ̲_Z` in the sheaf. -/
noncomputable def underlineGammaZMap {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    (Z : Closeds X) : underlineGammaZ F Z ⟶ underlineGammaZ G Z :=
  kernel.map (toComplementPushforward F Z) (toComplementPushforward G Z) φ
    ((Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).map
      ((Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).map φ))
    ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (complementInclusion Z)).unit.naturality φ).symm

/-- The sheaf functor `Γ̲_Z : C_X ⥤ C_X` (I.1). -/
noncomputable def underlineGammaZFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := underlineGammaZ F Z
  map φ := underlineGammaZMap φ Z
  map_id F := by
    apply equalizer.hom_ext
    simp [underlineGammaZMap, kernel.map]
  map_comp φ ψ := by
    apply equalizer.hom_ext
    simp [underlineGammaZMap, kernel.map]

/-- **I.2.11 (degree 0):** `ℋ_Z^0(F)` is realised as `Γ̲_Z(F)`. -/
noncomputable abbrev sheafH_Z_zero (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X :=
  underlineGammaZ F Z

/-- **I.1 (open case, (8'')):** for an open `U`, the unit of `i^* ⊣ i_*` is the canonical
homomorphism `F → i_* i^*(F)` of (6 bis)/(8''). -/
noncomputable def toOpenUnderlineGamma (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    F ⟶ (Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj
      ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj F) :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Opens.inclusion' U)).unit.app F

/-- **I.1, (6 bis):** for open `U`, `Γ̲_U(F) ≃ i_* i^*(F)`. -/
noncomputable abbrev underlineGammaOpen (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X :=
  (Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).obj
    ((Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' U)).obj F)

end SGA.SGA2.ExposeI
