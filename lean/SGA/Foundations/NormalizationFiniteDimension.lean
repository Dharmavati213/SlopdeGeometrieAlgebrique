/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.NormalizationFinite
import SGA.Foundations.Dimension.FiniteType

/-!
# The dimension of an integral scheme of finite type over a field

Let `X` be an integral scheme, locally of finite type over a field `k`. Its dimension is the
transcendence degree of its function field over `k`
(`AlgebraicGeometry.topologicalKrullDim_eq_trdeg_functionField`; Stacks Project, Tag 0A21). The
proof reads both sides on a nonempty affine open `U`: `dim X = dim U`
(`AlgebraicGeometry.topologicalKrullDim_opens_eq_of_isIntegral`), `dim U = dim Γ(X, U)`, and
`dim Γ(X, U) = trdeg_k Γ(X, U) = trdeg_k K(X)` (`Algebra.FiniteType.ringKrullDim_eq_trdeg`,
`Algebra.FiniteType.trdeg_eq_of_isFractionRing`).

The `k`-algebra structure on `K(X)` is given as an instance together with the hypothesis that it is
the composite `k ≅ Γ(Spec k) → Γ(X) → K(X)` induced by the structure morphism.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f]

/-- **The dimension of an integral scheme locally of finite type over a field `k` is the
transcendence degree of its function field over `k`** (Stacks 0A21). The `k`-algebra structure of
`K(X)` must be the one induced by `f` (hypothesis `hf`). -/
theorem topologicalKrullDim_eq_trdeg_functionField [Algebra k X.functionField]
    (hf : algebraMap k X.functionField =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom) :
    topologicalKrullDim X = (Algebra.trdeg k X.functionField).toENat := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top
  have hft : ψ.hom.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv _).mpr
      (f.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let := ψ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hft
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower k Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [hf, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    congr 1
    simp only [ψ, Category.assoc, Scheme.germToFunctionField, Scheme.Hom.appLE,
      TopCat.Presheaf.germ_res]
    rfl
  rw [← topologicalKrullDim_opens_eq_of_isIntegral f U ⟨x, hxU⟩]
  refine (IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph).trans ?_
  change topologicalKrullDim (PrimeSpectrum Γ(X, U)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, Algebra.FiniteType.ringKrullDim_eq_trdeg k]
  have h := Algebra.FiniteType.trdeg_eq_of_isFractionRing k (B := Γ(X, U)) (K := X.functionField)
  rw [Cardinal.lift_id, Cardinal.lift_id] at h
  rw [h]

end AlgebraicGeometry
