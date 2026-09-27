/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.Foundations.Formal.FiniteEtaleSpec

/-!
# The fundamental group of the spectrum of an artinian local ring

Let `A` be an artinian local ring with residue field `k`. Base change along the closed point
`Spec k ⟶ Spec A` is an equivalence of the categories of étale coverings (SGA 1 I.8.3, IX.1.7:
"fundamental groups do not change on dividing out by the nilpotent elements";
`FEt.isEquivalence_pullback_residue`), deduced from the equivalence of finite étale algebras over
the complete local ring `A` and over `k`
(`CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective`).
Hence `π₁(Spec A) ≅ π₁(Spec k) ≅ Gal(k̄/k)` (IX.6.1, last assertion;
`nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_isArtinianRing`).

We also record that isomorphic fields have isomorphic absolute Galois groups
(`nonempty_absoluteGaloisGroup_continuousMulEquiv`), via their categories of étale coverings.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

section Artinian

variable (A : CommRingCat.{u}) [IsLocalRing A] [IsArtinianRing A]

instance : Subsingleton (PrimeSpectrum A) := Ring.KrullDimLE.subsingleton_primeSpectrum A

instance : ConnectedSpace (PrimeSpectrum A) :=
  { isPreconnected_univ := Set.subsingleton_of_subsingleton.isPreconnected
    toNonempty := inferInstance }

/-- The closed point `Spec k ⟶ Spec A` of the spectrum of a local ring. -/
noncomputable abbrev residuePoint :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))

/-- SGA 1 I.8.3, IX.1.7 for an artinian local ring `A`: base change along `Spec k ⟶ Spec A` is an
equivalence between the étale coverings of `Spec A` and those of `Spec k`. -/
instance FEt.isEquivalence_pullback_residue : (FEt.pullback (residuePoint A)).IsEquivalence := by
  have hker : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) =
      IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_residue
  have : IsAdicComplete (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) A := by
    rw [hker]
    infer_instance
  have : (CommAlgCat.FiniteEtale.baseChange.{u} A
      (CommRingCat.of (IsLocalRing.ResidueField A))).IsEquivalence :=
    CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective
      (S := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective
  exact Scheme.FiniteEtale.isEquivalence_pullback_spec A
    (CommRingCat.of (IsLocalRing.ResidueField A))

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- IX.1.7 for the fundamental group: `π₁(Spec k, t̄) ≅ π₁(Spec A, t̄)` for a geometric point `t̄`
of `Spec k`. -/
noncomputable def etaleFundamentalGroupResidueEquiv
    (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField A))) :
    etaleFundamentalGroup Ω t ≃ₜ* etaleFundamentalGroup Ω (t ≫ residuePoint A) :=
  autContinuousMulEquiv (FEt.pullback (residuePoint A)) (FEt.pullbackFiberIso Ω _ t)

/-- IX.6.1, last assertion, for `S = Spec A` with `A` artinian local: for every fibre functor `F`
of the étale coverings of `Spec A`, `Aut F` is isomorphic to the absolute Galois group of the
residue field `k` of `A`. -/
theorem nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_isArtinianRing
    (F : FEt (Spec A) ⥤ FintypeCat.{u}) [FiberFunctor F] :
    Nonempty (Aut F ≃ₜ* Field.absoluteGaloisGroup (IsLocalRing.ResidueField A)) := by
  let k := IsLocalRing.ResidueField A
  let t := specPoint (CommRingCat.of k) (AlgebraicClosure k)
  obtain ⟨φ⟩ := nonempty_iso_of_fiberFunctor F (FEt.fiber (AlgebraicClosure k)
    (t ≫ residuePoint A))
  exact ⟨(conjAutContinuousMulEquiv φ).trans
    ((etaleFundamentalGroupResidueEquiv A (AlgebraicClosure k) t).symm.trans
      (etaleFundamentalGroupEquivAbsoluteGaloisGroup k))⟩

/-- For a point `x` of the spectrum of an artinian local ring `A`, base change along
`Spec κ(x) ⟶ Spec A` is an equivalence of the categories of étale coverings. -/
instance FEt.isEquivalence_pullback_fromSpecResidueField_spec (x : Spec A) :
    (FEt.pullback ((Spec A).fromSpecResidueField x)).IsEquivalence := by
  have hx : x.asIdeal = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (α := PrimeSpectrum A) x (IsLocalRing.closedPoint A))
  have : x.asIdeal.IsMaximal := hx ▸ inferInstance
  have hsurj : Function.Surjective (algebraMap A x.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have : IsAdicComplete (RingHom.ker (algebraMap A x.asIdeal.ResidueField)) A := by
    rw [Ideal.ker_algebraMap_residueField, hx]
    infer_instance
  have : (CommAlgCat.FiniteEtale.baseChange.{u} A
      (CommRingCat.of x.asIdeal.ResidueField)).IsEquivalence :=
    CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective hsurj
  have : (FEt.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A x.asIdeal.ResidueField)))).IsEquivalence :=
    Scheme.FiniteEtale.isEquivalence_pullback_spec A (CommRingCat.of x.asIdeal.ResidueField)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  exact FEt.isEquivalence_pullback_comp _ _

end Artinian

section OnePoint

variable {S : Scheme.{u}} (A : CommRingCat.{u}) [IsLocalRing A] [IsArtinianRing A]

/-- SGA 1 IX.1.7 for a scheme `S` isomorphic to the spectrum of an artinian local ring: base
change along `Spec κ(s) ⟶ S` is an equivalence of the categories of étale coverings. -/
lemma FEt.isEquivalence_pullback_fromSpecResidueField (e : S ≅ Spec A) (s : S) :
    (FEt.pullback (S.fromSpecResidueField s)).IsEquivalence := by
  have : (FEt.pullback (Spec.map (e.hom.residueFieldMap s) ≫
      (Spec A).fromSpecResidueField (e.hom s))).IsEquivalence :=
    FEt.isEquivalence_pullback_comp _ _
  rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at this
  exact FEt.isEquivalence_pullback_of_comp _ e.hom

/-- IX.6.1, last assertion: if `S` is the spectrum of an artinian local ring and `s` its point,
the fundamental group of `S` (the automorphism group of any fibre functor on its étale
coverings) is isomorphic to the absolute Galois group of the residue field `κ(s)`. -/
theorem nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_residueField (e : S ≅ Spec A)
    (s : S) [ConnectedSpace S] (F : FEt S ⥤ FintypeCat.{u}) [FiberFunctor F] :
    Nonempty (Aut F ≃ₜ* Field.absoluteGaloisGroup (S.residueField s)) := by
  let k := (S.residueField s : Type u)
  let j : Spec (CommRingCat.of k) ⟶ S := S.fromSpecResidueField s
  have : (FEt.pullback j).IsEquivalence := FEt.isEquivalence_pullback_fromSpecResidueField A e s
  let t := specPoint (CommRingCat.of k) (AlgebraicClosure k)
  obtain ⟨φ⟩ := nonempty_iso_of_fiberFunctor F (FEt.fiber (AlgebraicClosure k) (t ≫ j))
  exact ⟨(conjAutContinuousMulEquiv φ).trans ((autContinuousMulEquiv (FEt.pullback j)
    (FEt.pullbackFiberIso (AlgebraicClosure k) j t)).symm.trans
      (etaleFundamentalGroupEquivAbsoluteGaloisGroup k))⟩

end OnePoint

section FieldIso

/-- Isomorphic fields have isomorphic absolute Galois groups (as topological groups): both are
the fundamental groups of isomorphic schemes. -/
theorem nonempty_absoluteGaloisGroup_continuousMulEquiv {K L : Type u} [Field K] [Field L]
    (e : K ≃+* L) :
    Nonempty (Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup L) := by
  let i : Spec (CommRingCat.of L) ≅ Spec (CommRingCat.of K) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op
  let t := specPoint (CommRingCat.of L) (AlgebraicClosure L)
  have : (FEt.pullback i.hom).IsEquivalence := inferInstance
  let F : FEt (Spec (CommRingCat.of K)) ⥤ FintypeCat.{u} :=
    FEt.fiber (AlgebraicClosure L) (t ≫ i.hom)
  obtain ⟨eK⟩ := nonempty_aut_continuousMulEquiv_absoluteGaloisGroup K F
  exact ⟨eK.symm.trans ((autContinuousMulEquiv (FEt.pullback i.hom)
    (FEt.pullbackFiberIso (AlgebraicClosure L) i.hom t)).symm.trans
      (etaleFundamentalGroupEquivAbsoluteGaloisGroup L))⟩

end FieldIso

end SGA.SGA1.ExposeV
