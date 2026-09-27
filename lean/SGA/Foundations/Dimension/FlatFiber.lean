/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import SGA.Foundations.Dimension.FlatLocal
import SGA.Foundations.Dimension.LocalDimension

/-!
# Dimension of the local rings of a flat algebra and of its fibres

Let `R → S` be a flat homomorphism of noetherian rings, `p` a prime of `R` and `q` a prime of the
fibre `κ(p) ⊗_R S`, corresponding to the prime `r = q ∩ S` of `S` over `p`. Then
`dim S_r = dim R_p + dim (κ(p) ⊗_R S)_q`
(`ringKrullDim_localization_comap_eq_add_of_flat`; EGA IV §6.1, Stacks Project, Tag 00ON).

If moreover `S` is of finite type over `R`, the fibre is of finite type over the field `κ(p)`
and we obtain the dimension formula (EGA IV §6.1, SGA 1 II (3.1))
`dim S_r + trdeg_{κ(p)} κ(q) = dim R_p + dim_q (Spec (κ(p) ⊗_R S))`
(`ringKrullDim_localization_comap_add_trdeg_eq_of_flat`), where the last term is the dimension of
the fibre at the point, which may equally be computed in the fibre `Spec S ×_{Spec R} {p}`
of `Spec S → Spec R` (`topologicalKrullDimAt_preimage_eq_fiber`).
-/

open Order PrimeSpectrum IsLocalRing Algebra.TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]

/-- The prime `q ∩ S` of `S` lies over `p`. -/
instance Ideal.Fiber.liesOver_comap_includeRight : (q.comap includeRight : Ideal S).LiesOver p :=
  ⟨(Ideal.over_def q p).trans <| by ext x; simp [Ideal.under]⟩

/-- **Dimension of a flat extension**: for a flat homomorphism of noetherian rings `R → S`, a
prime `p` of `R` and a prime `q` of the fibre over `p`, `dim S_r = dim R_p + dim (κ(p) ⊗ S)_q`
where `r = q ∩ S`. -/
theorem ringKrullDim_localization_comap_eq_add_of_flat [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim (Localization.AtPrime (q.comap includeRight : Ideal S)) =
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (Localization.AtPrime q) := by
  set r : Ideal S := q.comap includeRight
  let := Localization.AtPrime.algebraOfLiesOver p r
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p _ (algebraMap R S) Ideal.LiesOver.over
  have : Module.Flat R (Localization.AtPrime r) := .trans R S (Localization.AtPrime r)
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime r) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr this
  rw [ringKrullDim_eq_ringKrullDim_add_ringKrullDim_quotient_of_flat (A := Localization.AtPrime p),
    ringKrullDim_eq_of_ringEquiv (Ideal.Fiber.localizationAlgEquivQuotient p q).toRingEquiv,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The two natural `κ(p)`-algebra structures on the residue field `κ(q)` of a prime `q` of the
fibre `κ(p) ⊗_R S` coincide: the one induced by the local homomorphism `R_p → (κ(p) ⊗ S)_q`,
and the one coming from the `κ(p)`-algebra `κ(p) ⊗ S`. -/
theorem Ideal.Fiber.algebra_residueField_eq :
    (inferInstance : Algebra p.ResidueField q.ResidueField) =
      IsLocalRing.ResidueField.algebra (Localization.AtPrime q) := by
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  have key : algebraMap (Localization.AtPrime p) (Localization.AtPrime q) =
      (algebraMap (p.Fiber S) (Localization.AtPrime q)).comp
        ((algebraMap p.ResidueField (p.Fiber S)).comp
          (IsLocalRing.residue (Localization.AtPrime p))) := by
    refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun a ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq, Localization.localRingHom_to_map,
      ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
      ← IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber S)]
  change IsLocalRing.residue _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime q) x) =
    IsLocalRing.residue _ (algebraMap (p.Fiber S) (Localization.AtPrime q)
      (algebraMap p.ResidueField (p.Fiber S) (IsLocalRing.residue _ x)))
  rw [key]
  rfl

/-- **The dimension formula for flat algebras of finite type** (EGA IV §6.1; SGA 1 II (3.1)):
for `R → S` flat and of finite type between noetherian rings, a prime `p` of `R` and a prime `q`
of the fibre `κ(p) ⊗_R S` (a point `x` of the fibre over `y = p`, with `r = q ∩ S`),
`dim 𝒪_x + trdeg_{κ(y)} κ(x) = dim 𝒪_y + dim_x (fibre)`. -/
theorem ringKrullDim_localization_comap_add_trdeg_eq_of_flat [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S] [Algebra.FiniteType R S] :
    ringKrullDim (Localization.AtPrime (q.comap includeRight : Ideal S)) +
        (Algebra.trdeg p.ResidueField q.ResidueField).toENat =
      ringKrullDim (Localization.AtPrime p) +
        topologicalKrullDimAt (PrimeSpectrum (p.Fiber S)) ⟨q, ‹_›⟩ := by
  rw [Algebra.FiniteType.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg p.ResidueField q,
    ringKrullDim_localization_comap_eq_add_of_flat, add_assoc]
  have h := Ideal.Fiber.algebra_residueField_eq p q
  congr 4
  convert (congrArg (fun i : Algebra p.ResidueField q.ResidueField ↦
    @Algebra.trdeg p.ResidueField q.ResidueField _ _ i) h).symm using 2
  · rfl
  · exact h.symm

/-- The dimension at a point of the fibre `Spec (κ(p) ⊗_R S)` equals the dimension at the
corresponding point of the set-theoretic fibre of `Spec S → Spec R` over `p`. -/
theorem topologicalKrullDimAt_preimage_eq_fiber :
    topologicalKrullDimAt (comap (algebraMap R S) ⁻¹' {⟨p, ‹_›⟩})
      ((preimageHomeomorphFiber R S ⟨p, ‹_›⟩).symm ⟨q, ‹_›⟩) =
      topologicalKrullDimAt (PrimeSpectrum (p.Fiber S)) ⟨q, ‹_›⟩ := by
  rw [(preimageHomeomorphFiber R S ⟨p, ‹_›⟩).symm.topologicalKrullDimAt_eq]

/-- **Dimension of a flat extension**, order-theoretic form: for a flat homomorphism of
noetherian rings `R → S` and a prime `r` of `S` over `p`, `ht r = ht p + ht_{fibre}(r)`, the last
height being computed in the fibre of `Spec S → Spec R` over `p`. -/
theorem PrimeSpectrum.height_eq_height_comap_add_height_fiber [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S] (r : PrimeSpectrum S) :
    height r = height (comap (algebraMap R S) r) +
      height (⟨r, rfl⟩ : comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) r}) := by
  set p := comap (algebraMap R S) r
  set e := preimageOrderIsoFiber R S p
  set q := e ⟨r, rfl⟩
  have hr : q.asIdeal.comap (includeRight : S →ₐ[R] p.asIdeal.Fiber S) = r.asIdeal :=
    congrArg (fun y ↦ (Subtype.val y).asIdeal) (e.symm_apply_apply ⟨r, rfl⟩)
  have h := ringKrullDim_localization_comap_eq_add_of_flat p.asIdeal q.asIdeal
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (q.asIdeal.comap (includeRight : S →ₐ[R] p.asIdeal.Fiber S)) (Localization.AtPrime _),
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime _), hr] at h
  have h₃ : ringKrullDim (Localization.AtPrime q.asIdeal) = q.asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)
  rw [h₃, ← WithBot.coe_add, WithBot.coe_inj] at h
  rw [← height_orderIso e, ← height_eq_orderHeight, ← height_eq_orderHeight,
    ← height_eq_orderHeight]
  exact h
