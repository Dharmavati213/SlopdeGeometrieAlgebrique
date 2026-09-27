/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeII.Criteria
import SGA.SGA1.ExposeII.SmoothnessAux

/-!
# SGA 1, Exposé II, II.2.2: the fibrewise criterion of smoothness

Let `S` be locally noetherian, `f : X → Y` an `S`-morphism of finite type with `Y` of finite type
and flat over `S`, `x ∈ X` over `s ∈ S`. Then `f` is smooth at `x` iff `X` is flat over `S` at `x`
and `f_s : X_s → Y_s` is smooth at `x`. We prove the affine local form: the smoothness of `f_s`
at `x` is the formal smoothness of the local homomorphism of the local rings of the fibres,
`A_q / 𝔪_s A_q → B_Q / 𝔪_s B_Q`. As in SGA, sufficiency combines II.2.1 with the fibrewise
flatness criterion (I.5.9, proved as IV.5.9 in `SGA.SGA1.ExposeIV.LocalCriterion`): the flatness
of `B_Q / 𝔪_s B_Q` over `A_q / 𝔪_s A_q` comes from its formal smoothness, and the fibre of `f` at
`y` is the fibre of `f_s` at `y`.
-/

universe u

open Algebra IsLocalRing
open scoped TensorProduct

namespace SGA.SGA1.ExposeII

open SGA.SGA1.ExposeIV

set_option backward.isDefEq.respectTransparency false in
/-- II.2.2, local form. Let `R → A → B` be of finite type with `R` noetherian and `A` flat over `R`
(`f : X → Y` an `S`-morphism of finite type, `Y` of finite type and flat over `S`), and let
`Q ⊆ B` lie over `q ⊆ A` over `p ⊆ R` (points `x ↦ y ↦ s`). The local rings of the fibres
`Y_s`, `X_s` at `y`, `x` are `A_q / p A_q` and `B_Q / p B_Q`. Then `f` is smooth at `x` iff `X` is
flat over `S` at `x` and `f_s : X_s → Y_s` is smooth at `x`, i.e. `B_Q / p B_Q` is formally
smooth over `A_q / p A_q`. -/
theorem isSmoothAt_iff_flat_and_formallySmooth_quotient_of_liesOver {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsNoetherianRing R] [FiniteType R A] [Module.Flat R A]
    [FiniteType A B] (p : Ideal R) (q : Ideal A) (Q : Ideal B) [p.IsPrime] [q.IsPrime]
    [Q.IsPrime] [Q.LiesOver q] [q.LiesOver p] [Q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver q Q
    IsSmoothAt A Q ↔ Module.Flat R (Localization.AtPrime Q) ∧
      FormallySmooth (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
        (Localization.AtPrime Q ⧸ (p.map (algebraMap R (Localization.AtPrime q))).map
          (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q))) := by
  have : IsNoetherianRing A := FiniteType.isNoetherianRing R A
  have : IsNoetherianRing B := FiniteType.isNoetherianRing A B
  have : FinitePresentation A B := FinitePresentation.of_finiteType.mp inferInstance
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Localization.AtPrime.algebraOfLiesOver q Q
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p q (algebraMap R A) Ideal.LiesOver.over
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom q Q (algebraMap A B) Ideal.LiesOver.over
  have hJ : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
        p.map (algebraMap R (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hflatAq : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    have : Module.Flat R (Localization.AtPrime q) := .trans R A _
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr this
  constructor
  · intro hQ
    have : FormallySmooth A (Localization.AtPrime Q) := hQ
    have : FormallySmooth (Localization.AtPrime q) (Localization.AtPrime Q) :=
      .localization_base q.primeCompl
    refine ⟨?_, ?_⟩
    · have : Module.Flat A (Localization.AtPrime Q) := IsSmoothAt.flat_localization Q
      exact .trans R A _
    · exact .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Localization.AtPrime Q)
        (p.map (algebraMap R (Localization.AtPrime q)))).symm
  · rintro ⟨hflat, hfib⟩
    -- flatness over `𝒪_y`, by the fibrewise flatness criterion IV.5.9
    have hflatRp : Module.Flat (Localization.AtPrime p) (Localization.AtPrime Q) :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr hflat
    have : EssFiniteType (Localization.AtPrime q) (Localization.AtPrime Q) := by
      have : EssFiniteType A (Localization.AtPrime Q) := .comp A B _
      exact .of_comp A _ _
    have : IsNoetherianRing
        (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
      Ideal.Quotient.isNoetherianRing _
    have hfibflat : Module.Flat
        (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
        (Localization.AtPrime Q ⧸ (p.map (algebraMap R (Localization.AtPrime q))).map
          (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q))) :=
      flat_of_formallySmooth_of_essFiniteType
    have h59 := flat_iff_flat_and_flat_fibre (A := Localization.AtPrime p)
      (B := Localization.AtPrime q) (C := Localization.AtPrime Q) (M := Localization.AtPrime Q)
    rw [hJ] at h59
    have hflatq : Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q) :=
      h59.2 ⟨hflatRp, .of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Localization.AtPrime Q)
        (p.map (algebraMap R (Localization.AtPrime q)))).symm.toLinearEquiv⟩
    have : Module.Flat A (Localization.AtPrime Q) := .trans A (Localization.AtPrime q) _
    -- the fibre at `y` is the fibre of `f_s` at `y`, which is smooth
    have hJm : p.map (algebraMap R (Localization.AtPrime q)) ≤
        maximalIdeal (Localization.AtPrime q) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq R A,
        ← Ideal.map_map]
      exact Ideal.map_mono (Ideal.map_le_of_le_comap (Ideal.LiesOver.over (P := q) (p := p)).le)
    have hfib' : FormallySmooth q.ResidueField
        (q.ResidueField ⊗[Localization.AtPrime q] Localization.AtPrime Q) :=
      formallySmooth_tensorProduct_of_formallySmooth_quotient _ q.ResidueField fun b hb ↦ by
        rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
        exact hJm hb
    have : FormallySmooth q.ResidueField (q.ResidueField ⊗[A] Localization.AtPrime Q) :=
      .of_equiv (Algebra.TensorProduct.equivOfCompatibleSMul A (Localization.AtPrime q)
        q.ResidueField q.ResidueField (Localization.AtPrime Q))
    exact (isSmoothAt_iff_flat_and_formallySmooth_fiber q Q).mpr ⟨inferInstance, this⟩

/-- II.2.2, local form, at the images of `Q` (see
`isSmoothAt_iff_flat_and_formallySmooth_quotient_of_liesOver`): `f` is smooth at `x` iff `X` is
flat over `S` at `x` and `f_s` is smooth at `x`. -/
theorem isSmoothAt_iff_flat_and_formallySmooth_quotient {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsNoetherianRing R] [FiniteType R A] [Module.Flat R A] [FiniteType A B] (Q : Ideal B)
    [Q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (Q.under A) Q
    IsSmoothAt A Q ↔ Module.Flat R (Localization.AtPrime Q) ∧
      FormallySmooth
        (Localization.AtPrime (Q.under A) ⧸
          (Q.under R).map (algebraMap R (Localization.AtPrime (Q.under A))))
        (Localization.AtPrime Q ⧸
          ((Q.under R).map (algebraMap R (Localization.AtPrime (Q.under A)))).map
            (algebraMap (Localization.AtPrime (Q.under A)) (Localization.AtPrime Q))) :=
  isSmoothAt_iff_flat_and_formallySmooth_quotient_of_liesOver (Q.under R) (Q.under A) Q

end SGA.SGA1.ExposeII
