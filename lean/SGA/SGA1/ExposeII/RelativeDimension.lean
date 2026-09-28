/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import SGA.Foundations.Dimension.FiniteType
import SGA.Foundations.Dimension.FlatScheme
import SGA.Foundations.Dimension.Scheme
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeII.SmoothnessAux

/-!
# SGA 1, Exposé II, II.1.5: the relative dimension is the dimension of the fibre

The integer `n` of II.1.1 is determined by `x`: it is the rank of `Ω¹_{X/Y}` at `x`
(`SGA.SGA1.ExposeII.Generalities`), and, as SGA says, the dimension of the fibre at `x`. Over a
field we prove: if `A` is étale over `k[t₁,…,tₙ]`, then `dim 𝒪_P + trdeg_k κ(P) = n` at every point
(`height_add_trdeg_residueField_of_etale_mvPolynomial`), using that étale local homomorphisms
preserve the dimension (I.9.1) and are residually finite, and `ht q + trdeg κ(q) = n` on the affine
space (`SGA.Foundations.Dimension`). The relative statement, for schemes, is in
`SGA.Foundations.Dimension.Scheme` and is recorded here: the fibres of a morphism smooth of
relative dimension `n` have dimension `n` at every point (`fiberDimAt_eq_of_smooth`). With the
dimension formula for flat morphisms this gives the dimension part of formula (3.1),
`dim 𝒪_x = dim 𝒪_y + n - d` (`ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_smooth`). The depth
part of (3.1) and (3.2) are not formalized.
-/

universe u

open IsLocalRing Algebra Cardinal

namespace SGA.SGA1.ExposeII

/-- For a `T`-algebra `A` over `k`, essentially of finite type and étale at a prime `P` over `q`
(`T`, `A` noetherian), the local dimension `ht P + trdeg_k κ(P)` equals that of `T` at `q`. -/
theorem height_add_trdeg_eq_of_isEtaleAt {k T A : Type u} [Field k] [CommRing T] [CommRing A]
    [Algebra k T] [Algebra T A] [Algebra k A] [IsScalarTower k T A] [IsNoetherianRing T]
    [IsNoetherianRing A] [EssFiniteType T A] (q : Ideal T) (P : Ideal A) [q.IsPrime] [P.IsPrime]
    [P.LiesOver q] [IsEtaleAt T P] :
    (P.height : WithBot ℕ∞) + (trdeg k P.ResidueField).toENat =
      q.height + (trdeg k q.ResidueField).toENat := by
  let := Localization.AtPrime.algebraOfLiesOver q P
  have hE : FormallyEtale T (Localization.AtPrime P) := ‹IsEtaleAt T P›
  -- the heights agree
  have hP : P.height = q.height := by
    have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) := by
      rw [RingHom.algebraMap_toAlgebra]
      exact Localization.isLocalHom_localRingHom q P (algebraMap T A) Ideal.LiesOver.over
    have : EssFiniteType T (Localization.AtPrime P) := .comp T A _
    have : Module.Flat T (Localization.AtPrime P) := flat_of_formallySmooth_of_essFiniteType
    have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime P) :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl _).mpr ‹_›
    have : FormallyEtale (Localization.AtPrime q) (Localization.AtPrime P) :=
      .localization_base q.primeCompl
    have : EssFiniteType (Localization.AtPrime q) (Localization.AtPrime P) := .of_comp T _ _
    have : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
    have : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have h := ringKrullDim_eq_of_flat_of_map_maximalIdeal (A := Localization.AtPrime q)
      (B := Localization.AtPrime P) FormallyUnramified.map_maximalIdeal
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P,
      IsLocalization.AtPrime.ringKrullDim_eq_height q] at h
    exact_mod_cast h
  -- `κ(P)` is finite over `κ(q)`
  have : IsUnramifiedAt T P := by
    change FormallyUnramified T (Localization.AtPrime P)
    infer_instance
  have : Module.Finite q.ResidueField P.ResidueField := inferInstance
  have : IsScalarTower k q.ResidueField P.ResidueField := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k T q.ResidueField,
      IsScalarTower.algebraMap_apply k A P.ResidueField,
      IsScalarTower.algebraMap_apply k T A]
    exact ((IsScalarTower.algebraMap_apply T q.ResidueField P.ResidueField _).symm.trans
      (IsScalarTower.algebraMap_apply T A P.ResidueField _)).symm
  have h := lift_trdeg_add_eq k q.ResidueField P.ResidueField
  rw [trdeg_eq_zero (R := q.ResidueField) (A := P.ResidueField), lift_zero, add_zero, lift_id,
    lift_id] at h
  rw [hP, ← h]

/-- For an étale `T`-algebra `A` over `k` and a prime `P` of `A` over `q`, the local dimension
`ht P + trdeg_k κ(P)` equals that of `T` at `q`. -/
theorem height_add_trdeg_eq_of_etale {k T A : Type u} [Field k] [CommRing T] [CommRing A]
    [Algebra k T] [Algebra T A] [Algebra k A] [IsScalarTower k T A] [IsNoetherianRing T]
    [Etale T A] (q : Ideal T) (P : Ideal A) [q.IsPrime] [P.IsPrime] [P.LiesOver q] :
    (P.height : WithBot ℕ∞) + (trdeg k P.ResidueField).toENat =
      q.height + (trdeg k q.ResidueField).toENat := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing T A
  have : IsEtaleAt T P := by
    change FormallyEtale T (Localization.AtPrime P)
    exact .comp T A _
  exact height_add_trdeg_eq_of_isEtaleAt q P

/-- II.1.5, over a field: if `A` is étale over `k[t₁,…,tₙ]`, then at every point `P` of `Spec A`,
`dim 𝒪_P + trdeg_k κ(P) = n`, i.e. `Spec A` has dimension `n` at every point. Applied to the fibres
of a smooth morphism (which are étale over `κ(y)[t₁,…,tₙ]` by base change), this identifies the
integer `n` of II.1.1 with the dimension of the fibre at `x`. -/
theorem height_add_trdeg_residueField_of_etale_mvPolynomial {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (n : ℕ) [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Etale (MvPolynomial (Fin n) k) A] (P : Ideal A)
    [P.IsPrime] : (P.height : WithBot ℕ∞) + (trdeg k P.ResidueField).toENat = n := by
  rw [height_add_trdeg_eq_of_etale (k := k) (P.under (MvPolynomial (Fin n) k)) P,
    Algebra.FiniteType.height_add_trdeg_residueField k,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

section Scheme

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- II.1.5: the relative dimension `n` of a morphism smooth of relative dimension `n` is the
dimension of its fibres: `dim_x f⁻¹(f(x)) = n` at every `x` (`SGA.Foundations`). -/
theorem fiberDimAt_eq_of_smooth (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    f.fiberDimAt x = n :=
  f.fiberDimAt_eq_of_smoothOfRelativeDimension n x

/-- II.1.5, "the dimension of the local ring of `x` in its fibre": for `f` smooth of relative
dimension `n`, `dim 𝒪_{f⁻¹(f(x)),x} + trdeg_{κ(f(x))} κ(x) = n` (`SGA.Foundations`); SGA's
phrasing is the case of a point closed in its fibre. -/
theorem ringKrullDim_stalk_fiber_add_trdeg_eq_of_smooth (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
      (f.residueFieldTrdeg x).toENat = n :=
  f.ringKrullDim_stalk_fiber_add_residueFieldTrdeg_of_smoothOfRelativeDimension n x

/-- Formula (3.1), dimension part: if `f` is smooth of relative dimension `n` and `Y` is locally
noetherian, then `dim 𝒪_x + d = dim 𝒪_y + n`, where `d` is the transcendence degree of `κ(x)`
over `κ(y)`. -/
theorem ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_smooth (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + (f.residueFieldTrdeg x).toENat =
      ringKrullDim (Y.presheaf.stalk (f x)) + n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  rw [f.ringKrullDim_stalk_add_residueFieldTrdeg_eq_of_flat x,
    f.fiberDimAt_eq_of_smoothOfRelativeDimension n x]

end Scheme

end SGA.SGA1.ExposeII
