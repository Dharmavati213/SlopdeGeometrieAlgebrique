/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Ramification data under local isomorphisms

The ramification index of a prime `q` of an `R`-algebra `S` and its residue field extension only
depend on the local ring `S_q` as an `R`-algebra. Hence, for an `R`-algebra map `f : S → S'` and a
prime `q'` of `S'` such that `S_q → S'_{q'}` is an isomorphism (`q = f⁻¹ q'`):

* `Ideal.ramificationIdx_comap_of_bijective`: `e(q) = e(q')`;
* `Ideal.isSeparable_residueField_comap_iff_of_bijective`: `κ(q)/κ(p)` is separable if and only if
  `κ(q')/κ(p)` is.

This applies to isomorphisms of `R`-algebras (`Ideal.ramificationIdx_map_algEquiv`,
`Ideal.isSeparable_residueField_map_algEquiv_iff`) and to the projections of a finite product
(`Localization.AtPrime.mapPiEvalRingHom_bijective`). Likewise for étaleness at a prime
(`Algebra.IsEtaleAt.of_bijective_localAlgHom`, `Algebra.IsEtaleAt.of_algEquiv`).
-/

namespace Ideal

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

section Local

variable (f : S →ₐ[R] S') (q' : Ideal S') [q'.IsPrime]

omit [q'.IsPrime] in
lemma under_comap_algHom : (q'.comap f).under R = q'.under R := by
  ext r
  rw [under, under, mem_comap, mem_comap, mem_comap, AlgHom.commutes]

variable (hf : Function.Bijective (Localization.localAlgHom (q'.comap f) q' f rfl))
include hf

/-- The ramification index only depends on the local ring. -/
theorem ramificationIdx_comap_of_bijective :
    (q'.comap f).ramificationIdx R = q'.ramificationIdx R := by
  set q := q'.comap f
  set p := q'.under R
  have : q.LiesOver p := ⟨(under_comap_algHom f q').symm⟩
  let Sq := Localization.AtPrime q
  let Sq' := Localization.AtPrime q'
  let φ : Sq ≃ₐ[R] Sq' := AlgEquiv.ofBijective (Localization.localAlgHom q q' f rfl) hf
  let : Algebra Sq Sq' := φ.toRingHom.toAlgebra
  have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom φ.toAlgHom
  let φS : Sq ≃ₐ[Sq] Sq' := AlgEquiv.ofRingEquiv (f := φ.toRingEquiv) fun _ ↦ rfl
  let e' : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
    Ideal.quotientEquivAlg _ _ φS (by
      rw [Ideal.map_map]
      congr 1
      ext r
      exact (φ.commutes r).symm)
  rw [ramificationIdx_eq p q, ramificationIdx_eq p q',
    e'.toLinearEquiv.length_eq, Module.length_eq_of_surjective φ.surjective]

/-- Separability of the residue field extension only depends on the local ring. -/
theorem isSeparable_residueField_comap_iff_of_bijective (p : Ideal R) [p.IsPrime]
    [q'.LiesOver p] :
    haveI : (q'.comap f).LiesOver p :=
      ⟨(under_comap_algHom f q').trans (over_def q' p).symm |>.symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver p (q'.comap f)
    letI := Localization.AtPrime.algebraOfLiesOver p q'
    Algebra.IsSeparable p.ResidueField (q'.comap f).ResidueField ↔
      Algebra.IsSeparable p.ResidueField q'.ResidueField := by
  set q := q'.comap f
  have : q.LiesOver p := ⟨(under_comap_algHom f q').trans (over_def q' p).symm |>.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Localization.AtPrime.algebraOfLiesOver p q'
  let φ : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q' :=
    AlgEquiv.ofBijective (Localization.localAlgHom q q' f rfl) hf
  let g : q.ResidueField ≃ₐ[R] q'.ResidueField := IsLocalRing.ResidueField.mapAlgEquiv φ
  have he : (algebraMap p.ResidueField q'.ResidueField).comp (RingEquiv.refl _).toRingHom =
      (g.toRingEquiv : q.ResidueField →+* q'.ResidueField).comp
        (algebraMap p.ResidueField q.ResidueField) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (g.commutes r).symm
  exact Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl _) g.toRingEquiv he

end Local

section Equiv

variable (e : S ≃ₐ[R] S') (q : Ideal S)

lemma comap_map_algEquiv : (q.map e).comap e = q :=
  comap_map_of_bijective _ e.bijective

lemma under_map_algEquiv : (q.map e).under R = q.under R := by
  ext r
  rw [under, under, mem_comap, mem_comap, ← e.commutes r, ← mem_comap, comap_map_algEquiv]

lemma bijective_localAlgHom_map_algEquiv [q.IsPrime] :
    haveI : (q.map e).IsPrime := map_isPrime_of_equiv e
    Function.Bijective (Localization.localAlgHom ((q.map e).comap (e : S →ₐ[R] S')) (q.map e)
      (e : S →ₐ[R] S') rfl) := by
  have : (q.map e).IsPrime := map_isPrime_of_equiv e
  exact (Localization.localRingEquiv ((q.map e).comap (e : S →ₐ[R] S')) (q.map e)
    e.toRingEquiv rfl).bijective

/-- The ramification index is invariant under isomorphisms of `R`-algebras. -/
theorem ramificationIdx_map_algEquiv : (q.map e).ramificationIdx R = q.ramificationIdx R := by
  by_cases hq : q.IsPrime; swap
  · have : ¬ (q.map e).IsPrime := fun h ↦ hq (comap_map_algEquiv e q ▸ Ideal.comap_isPrime _ _)
    rw [ramificationIdx_of_not_isPrime _ _ this, ramificationIdx_of_not_isPrime _ _ hq]
  · have : (q.map e).IsPrime := map_isPrime_of_equiv e
    have := ramificationIdx_comap_of_bijective (e : S →ₐ[R] S') (q.map e)
      (bijective_localAlgHom_map_algEquiv e q)
    rwa [show (q.map e).comap (e : S →ₐ[R] S') = q from comap_map_algEquiv e q, eq_comm] at this

/-- Separability of the residue field extension is invariant under isomorphisms of
`R`-algebras. -/
theorem isSeparable_residueField_map_algEquiv_iff (p : Ideal R) [p.IsPrime] [q.IsPrime]
    [q.LiesOver p] :
    haveI : (q.map e).IsPrime := map_isPrime_of_equiv e
    haveI : (q.map e).LiesOver p := ⟨(under_map_algEquiv e q).trans (over_def q p).symm |>.symm⟩
    letI := Localization.AtPrime.algebraOfLiesOver p q
    letI := Localization.AtPrime.algebraOfLiesOver p (q.map e)
    Algebra.IsSeparable p.ResidueField (q.map e).ResidueField ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField := by
  have : (q.map e).IsPrime := map_isPrime_of_equiv e
  have : (q.map e).LiesOver p := ⟨(under_map_algEquiv e q).trans (over_def q p).symm |>.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Localization.AtPrime.algebraOfLiesOver p (q.map e)
  let g : q.ResidueField ≃ₐ[p.ResidueField] (q.map e).ResidueField :=
    Ideal.residueFieldAlgEquiv' p q (q.map e) e (comap_map_algEquiv e q).symm
  exact ⟨fun _ ↦ Algebra.IsSeparable.of_algHom _ _ g.toAlgHom,
    fun _ ↦ Algebra.IsSeparable.of_algHom _ _ g.symm.toAlgHom⟩

end Equiv

end Ideal

namespace Algebra.IsEtaleAt

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

/-- Étaleness at a prime only depends on the local ring. -/
theorem of_bijective_localAlgHom (f : S →ₐ[R] S') (q' : Ideal S') [q'.IsPrime]
    (hf : Function.Bijective (Localization.localAlgHom (q'.comap f) q' f rfl))
    (h : Algebra.IsEtaleAt R (q'.comap f)) : Algebra.IsEtaleAt R q' :=
  Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective _ hf)

/-- Étaleness at a prime is invariant under isomorphisms of `R`-algebras. -/
theorem of_algEquiv (e : S ≃ₐ[R] S') (q' : Ideal S') [q'.IsPrime]
    (h : Algebra.IsEtaleAt R (q'.comap (e : S →ₐ[R] S'))) : Algebra.IsEtaleAt R q' :=
  of_bijective_localAlgHom _ q'
    (Localization.localRingEquiv (q'.comap (e : S →ₐ[R] S')) q' e.toRingEquiv rfl).bijective h

end Algebra.IsEtaleAt
