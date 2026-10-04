/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.DolbeaultCohomology
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Topology.Sheaves.Abelian

/-!
# The Dolbeault isomorphism (statement)

For a complex manifold `M` modelled on `E`, let `𝒪_M` be its sheaf of holomorphic functions
(mathlib's `smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ`: complex `C^∞` functions, i.e. holomorphic
ones), as an abelian sheaf (`Hodge.holomorphicSheaf E M`). Its sheaf cohomology
`Hᵍ(M, 𝒪_M)` (`CategoryTheory.Sheaf.H`, `Ext` from the constant sheaf `ℤ`) is a complex vector
space through the endomorphisms of `𝒪_M` given by multiplication by constants
(`Hodge.holomorphicSheafSMul`, `Hodge.holomorphicCohomologySMul`).

* `Hodge.DolbeaultIsomorphismStatement`: for `M` Hausdorff, second countable and finite
  dimensional, `Hᵍ(M, 𝒪_M) ≅ H^{0,q}_∂̄(M)` (`Hodge.dolbeaultCohomology`), complex linearly.

Proof plan (registry row C23): the sheaves `𝒜^{0,q}` of smooth `(0,q)`-forms are fine (partitions
of unity), and `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → ⋯` is exact by the Dolbeault–Grothendieck lemma
(local `∂̄`-Poincaré lemma in several variables, owned by `an-cohom`, registry row C10); a fine
resolution computes sheaf cohomology. References: Wells, *Differential analysis on complex
manifolds*, II.3.15 and II.3.17; Huybrechts, *Complex geometry*, Prop. 1.3.8 and §2.6;
Griffiths–Harris, Ch. 0 §6.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace Hodge

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The sheaf `𝒪_M` of holomorphic functions on the complex manifold `M`, as an abelian sheaf. -/
def holomorphicSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ)

/-- Multiplication by a constant `c ∈ ℂ`, as an endomorphism of the abelian sheaf `𝒪_M`. -/
def holomorphicSheafSMul (c : ℂ) : holomorphicSheaf E M ⟶ holomorphicSheaf E M where
  hom :=
  { app U := AddCommGrpCat.ofHom
      ({ toFun := fun f ↦ (c • (f : C^∞⟮𝓘(ℂ, E), (unop U : Opens M); 𝓘(ℂ), ℂ⟯) :)
         map_zero' := smul_zero (A := C^∞⟮𝓘(ℂ, E), (unop U : Opens M); 𝓘(ℂ), ℂ⟯) c
         map_add' := smul_add (A := C^∞⟮𝓘(ℂ, E), (unop U : Opens M); 𝓘(ℂ), ℂ⟯) c } :
        C^∞⟮𝓘(ℂ, E), (unop U : Opens M); 𝓘(ℂ), ℂ⟯ →+ C^∞⟮𝓘(ℂ, E), (unop U : Opens M); 𝓘(ℂ), ℂ⟯)
    naturality U V i := by
      ext f
      rfl }

/-- The sheaf cohomology `Hⁿ(M, 𝒪_M)` of the sheaf of holomorphic functions (`Ext` groups in
universe `0`). -/
def holomorphicCohomology (n : ℕ) : Type :=
  Sheaf.H.{0} (holomorphicSheaf E M) n

/-- The group structure of `Hⁿ(M, 𝒪_M)` (that of `Ext`; given explicitly because instance search
does not find it through `Sheaf.H`). -/
instance (n : ℕ) : AddCommGroup (holomorphicCohomology E M n) :=
  @Abelian.Ext.instAddCommGroup _ _ _ inferInstance _ _ _

/-- The action of `c ∈ ℂ` on the sheaf cohomology `Hⁿ(M, 𝒪_M)`, induced by
`Hodge.holomorphicSheafSMul c`. -/
def holomorphicCohomologySMul (n : ℕ) (c : ℂ) (x : holomorphicCohomology E M n) :
    holomorphicCohomology E M n :=
  Abelian.Ext.comp (show Sheaf.H.{0} (holomorphicSheaf E M) n from x)
    (Abelian.Ext.mk₀ (holomorphicSheafSMul E M c)) (add_zero n)

/-- **The Dolbeault isomorphism** (statement only): for a Hausdorff, second countable complex
manifold `M` modelled on a finite-dimensional complex normed space `E`, and every `q`, the sheaf
cohomology `Hᵍ(M, 𝒪_M)` is isomorphic to the Dolbeault cohomology `H^{0,q}_∂̄(M)` by an additive
isomorphism which is complex linear for the action of `ℂ` on `Hᵍ(M, 𝒪_M)` by multiplication by
constants on `𝒪_M`. Stated in universe `0`, where mathlib's sheaf of holomorphic functions lives
for `ℂ`-valued functions. -/
def DolbeaultIsomorphismStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [T2Space M] [SecondCountableTopology M] (q : ℕ),
    ∃ e : holomorphicCohomology E M q ≃+ dolbeaultCohomology E M 0 q,
      ∀ (c : ℂ) (x : holomorphicCohomology E M q),
        e (holomorphicCohomologySMul E M q c x) = c • e x

end Hodge
