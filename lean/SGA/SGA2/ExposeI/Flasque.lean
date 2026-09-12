/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Topology.Sheaves.Flasque
import SGA.SGA2.ExposeI.GammaZ

/-!
# SGA 2, Exposé I, §1–2: flasque sheaves

SGA uses flasque sheaves as the acyclic class for the functors `Γ_Z` (I.1.8, I.2.12):
if `F` is flasque then `H^i_Z(X, F) = 0` for `i ≠ 0`, and conversely vanishing of
`H^1_Z` for every closed `Z` characterises flasque sheaves.

Mathlib's `TopCat.Sheaf.IsFlasque` is the standard definition (all restriction maps
are epimorphisms). This file records that language under SGA numbering; the derived
vanishing `H^i_Z = 0` waits on the definition of `H_Z^*` (I.2.1).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- **I.2.12 (definition):** an abelian sheaf is flasque in the sense of SGA /
Godement iff mathlib's `IsFlasque`. -/
abbrev IsFlasque (F : Sheaf AddCommGrpCat.{u} X) : Prop := Sheaf.IsFlasque F

/-- **I.2.12:** for a flasque sheaf, restriction of global sections to any open is
surjective (the `i = 0` half of acyclicity for `Γ`). -/
lemma surjective_restrict_of_isFlasque (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (U : Opens X) :
    Function.Surjective (F.1.map (homOfLE (le_top : U ≤ ⊤)).op).hom :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- **I.1.8 / I.2.12:** if `F` is flasque, every section over the open complement of a
closed set extends to a global section. This is the input used in the proof of
I.1.8 (surjectivity of `Γ_Z → Γ_{Z''}` when `F` is flasque). -/
lemma exists_extension_of_isFlasque (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (Z' : Closeds X) (t : F.1.obj (op Z'.compl)) :
    ∃ s : F.1.obj (op (⊤ : Opens X)),
      (F.1.map (homOfLE (le_top : Z'.compl ≤ ⊤)).op).hom s = t :=
  surjective_restrict_of_isFlasque F Z'.compl t

end SGA.SGA2.ExposeI
