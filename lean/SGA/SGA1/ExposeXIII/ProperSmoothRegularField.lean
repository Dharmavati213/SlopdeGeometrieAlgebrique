/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# An algebraically closed field receiving a family of field extensions

For the second part of SGA 1 XIII.4.4 over a regular base we need one geometric generic point
`Spec Ω → S` such that the fraction fields `F_s` of the completed strict henselizations of the
local rings at all codimension-one points `s` of `S` embed into `Ω` over the function field `K`;
then all fundamental groups in the argument can be taken at the same geometric point.

* `nonempty_algHom_of_isTranscendenceBasis`: a field `F` over `K` embeds into an algebraically
  closed `Ω` over `K` as soon as a transcendence basis of `F/K` maps to an algebraically
  independent family of `Ω` (extend from `K(x)` to `F`, which is algebraic over it, by
  `IsAlgClosed.lift`).
* `exists_isAlgClosed_forall_nonempty_algHom`: for any family `(F i)` of field extensions of `K`,
  the algebraic closure of `K(T_x : x ∈ ⨆ᵢ F i)` receives all of them.

(Bourbaki, *Algèbre* V §14; Lang, *Algebra* VIII §1.)
-/

universe u

namespace SGA.SGA1.ExposeXIII

open MvPolynomial

/-- A field `F` over `K` embeds into an algebraically closed field `Ω` over `K` if some
transcendence basis of `F/K` is sent to an algebraically independent family of `Ω`. -/
theorem nonempty_algHom_of_isTranscendenceBasis {K F Ω : Type*} [Field K] [Field F] [Field Ω]
    [IsAlgClosed Ω] [Algebra K F] [Algebra K Ω] {ι : Type*} {x : ι → F}
    (hx : IsTranscendenceBasis K x) {y : ι → Ω} (hy : AlgebraicIndependent K y) :
    Nonempty (F →ₐ[K] Ω) := by
  let E := IntermediateField.adjoin K (Set.range x)
  let ψ₀ : FractionRing (MvPolynomial ι K) →ₐ[K] Ω :=
    IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.2 hy)
  let ψ : E →ₐ[K] Ω := ψ₀.comp hx.1.aevalEquivField.symm.toAlgHom
  let : Algebra E Ω := ψ.toRingHom.toAlgebra
  have : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  have : Algebra.IsAlgebraic E F := hx.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift : F →ₐ[E] Ω).restrictScalars K⟩

/-- Every family of field extensions of `K` (in one universe) embeds into a single algebraically
closed field over `K`: the algebraic closure of the rational function field over `K` in as many
variables as the disjoint union of the family. -/
theorem exists_isAlgClosed_forall_nonempty_algHom (K : Type u) [Field K] {I : Type u}
    (F : I → Type u) [∀ i, Field (F i)] [∀ i, Algebra K (F i)] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra K Ω),
      ∀ i, Nonempty (F i →ₐ[K] Ω) := by
  let T := Σ i, F i
  let P := FractionRing (MvPolynomial T K)
  refine ⟨AlgebraicClosure P, inferInstance, inferInstance, inferInstance, fun i ↦ ?_⟩
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K (F i)
  let j : MvPolynomial T K →ₐ[K] AlgebraicClosure P :=
    (IsScalarTower.toAlgHom K P (AlgebraicClosure P)).comp
      (IsScalarTower.toAlgHom K (MvPolynomial T K) P)
  have hj : Function.Injective j :=
    (algebraMap P (AlgebraicClosure P)).injective.comp (IsFractionRing.injective _ P)
  have hinj : Function.Injective (fun x : s ↦ (⟨i, x⟩ : T)) := fun a b h ↦
    Subtype.ext (eq_of_heq (Sigma.mk.inj h).2)
  have hy : AlgebraicIndependent K (j ∘ (X ∘ fun x : s ↦ (⟨i, x⟩ : T))) :=
    ((algebraicIndependent_X T K).comp _ hinj).map' hj
  exact nonempty_algHom_of_isTranscendenceBasis hs hy

end SGA.SGA1.ExposeXIII
