/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Basic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Cohomology of `𝒪_X`-modules

For a scheme `X` and an `𝒪_X`-module `M`, the cohomology `Hⁿ(U, M)` over an open `U` is the
cohomology of the underlying abelian sheaf `M.toAbSheaf` (see the module docstring of
`SGA.Foundations.Cohomology.Basic` for the framework). A global section `r ∈ Γ(X, 𝒪_X)` acts on `M`
by the endomorphism `M.smulHom r` of abelian sheaves, hence on `Hⁿ(U, M)`; this makes `Hⁿ(U, M)` a
`Γ(X, 𝒪_X)`-module (for `X` over `Spec A` this gives the `A`-module structure of EGA III 1.4.1).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.H' M n U`: `Hⁿ(U, M)`, a `Γ(X, 𝒪_X)`-module;
  `AlgebraicGeometry.Scheme.Modules.H M n = H' M n ⊤ = Hⁿ(X, M)`, identified with mathlib's
  `Sheaf.H M.toAbSheaf n` by `Scheme.Modules.H.addEquivSheafH`.
* `AlgebraicGeometry.Scheme.Modules.H'.map`: the `Γ(X, 𝒪_X)`-linear map induced by a morphism of
  `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.Modules.H.equiv₀ : H⁰(X, M) ≃ Γ(X, M)`, `Γ(X, 𝒪_X)`-linearly.

Long exact sequences for short exact sequences of `𝒪_X`-modules are in
`SGA.Foundations.Cohomology.LongExactSequence`.
-/

universe u

open CategoryTheory Limits Opposite Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The `Ext` groups of abelian sheaves on a scheme (a Grothendieck abelian category) are
`u`-small. (Stated once as an instance so that later declarations refer to this constant.) -/
noncomputable instance hasExtSheaf (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.hasExt _

section Cohomology

variable (M : X.Modules) (n : ℕ) (U : X.Opens)

/-- The cohomology `Hⁿ(U, M)` over an open `U` of an `𝒪_X`-module `M`, i.e. of its underlying
abelian sheaf; it is a `Γ(X, 𝒪_X)`-module. -/
abbrev H' : Type u := M.toAbSheaf.H' n U

noncomputable instance : Module Γ(X, ⊤) (M.H' n U) :=
  Module.compHom (M.toAbSheaf.H' n U) ((Sheaf.H'.endRingHom M.toAbSheaf n U).comp M.smulRingHom)

lemma H'.smul_def (r : Γ(X, ⊤)) (x : M.H' n U) :
    r • x = Sheaf.H'.map (M.smulHom r) n U (show M.toAbSheaf.H' n U from x) :=
  rfl

/-- The cohomology `Hⁿ(X, M)` of an `𝒪_X`-module, as a `Γ(X, 𝒪_X)`-module: cohomology over the
open `⊤`. -/
abbrev H : Type u := M.H' n ⊤

/-- `Hⁿ(X, M)` is mathlib's sheaf cohomology `Sheaf.H` of the underlying abelian sheaf. -/
noncomputable def H.addEquivSheafH : M.H n ≃+ Sheaf.H M.toAbSheaf n :=
  Sheaf.H'.addEquivH isTerminalTop M.toAbSheaf n

variable {M} {N : X.Modules}

/-- The `Γ(X, 𝒪_X)`-linear map `Hⁿ(U, M) → Hⁿ(U, N)` induced by a morphism of `𝒪_X`-modules. -/
noncomputable def H'.map (φ : M ⟶ N) (n : ℕ) (U : X.Opens) : M.H' n U →ₗ[Γ(X, ⊤)] N.H' n U where
  toFun x := Sheaf.H'.map (Hom.toAbSheaf φ) n U x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    change Sheaf.H'.map (Hom.toAbSheaf φ) n U (Sheaf.H'.map (M.smulHom r) n U x) =
      Sheaf.H'.map (N.smulHom r) n U (Sheaf.H'.map (Hom.toAbSheaf φ) n U x)
    exact ((Sheaf.H'.map_comp_apply (M.smulHom r) (Hom.toAbSheaf φ) x).symm.trans
      (congrArg (fun f ↦ Sheaf.H'.map f n U x) (Hom.toAbSheaf_smulHom φ r).symm)).trans
      (Sheaf.H'.map_comp_apply _ _ x)

lemma H'.map_apply (φ : M ⟶ N) {n : ℕ} {U : X.Opens} (x : M.H' n U) :
    H'.map φ n U x = Sheaf.H'.map (Hom.toAbSheaf φ) n U x :=
  rfl

lemma H'.map_comp_apply {K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) {n : ℕ} {U : X.Opens}
    (x : M.H' n U) : H'.map (φ ≫ ψ) n U x = H'.map ψ n U (H'.map φ n U x) := by
  have h : Hom.toAbSheaf (φ ≫ ψ) = Hom.toAbSheaf φ ≫ Hom.toAbSheaf ψ := Functor.map_comp _ _ _
  rw [H'.map_apply, H'.map_apply, H'.map_apply, h]
  exact Sheaf.H'.map_comp_apply (Hom.toAbSheaf φ) (Hom.toAbSheaf ψ) (show M.toAbSheaf.H' n U from x)

variable (M)

/-- `H⁰(U, M) = Γ(U, M)`, compatibly with the action of `Γ(X, 𝒪_X)` (acting on `Γ(U, M)` through
restriction). -/
lemma H'.equiv₀_smul (r : Γ(X, ⊤)) (x : M.H' 0 U) :
    Sheaf.H'.equiv₀ M.toAbSheaf U (r • x) =
      (M.smulHom r).hom.app (op U)
        (Sheaf.H'.equiv₀ M.toAbSheaf U (show M.toAbSheaf.H' 0 U from x)) :=
  Sheaf.H'.equiv₀_naturality _ _

/-- `H⁰(X, M) = Γ(X, M)` as `Γ(X, 𝒪_X)`-modules. -/
noncomputable def H.equiv₀ : M.H 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  __ := Sheaf.H'.equiv₀ M.toAbSheaf ⊤
  map_smul' r x := by
    refine (H'.equiv₀_smul M ⊤ r x).trans ((smulHom_app_apply M r _).trans ?_)
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    rfl

end Cohomology

end AlgebraicGeometry.Scheme.Modules
