/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import SGA.SGA1.ExposeV.FiniteEtaleGalois
import SGA.SGA1.ExposeV.GaloisEquivalence
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeI.NormalCoverings

/-!
# SGA 1, Exposé V, §8: the fundamental group of a field and of a normal base

* V.8.1: for a field `k` and a geometric point `k → Ω` (`Ω` separably closed; SGA takes `Ω`
  algebraically closed), `π₁(Spec k, a)` is isomorphic, as a topological group, to the Galois
  group of the separable closure `k̄` of `k` in `Ω` (`fundamentalGroupContinuousMulEquivGal`,
  and `etaleFundamentalGroupContinuousMulEquivGal` for `FEt (Spec k)`). The proof shows that
  `Gal(k̄/k)`, acting on the geometric points `A → k̄`, is a fundamental group of the fiber
  functor in mathlib's sense (`isFundamentalGroup`). Consequently the étale coverings of
  `Spec k` are the finite continuous `Gal(k̄/k)`-sets (`finiteEtaleEquivContAction`), and over a
  separably closed field every étale covering is a finite sum of copies of the base
  (`FEt.exists_iso_sigma_terminal`).
* V.8.2 (affine): for a normal domain `R` with fraction field `K`, the homomorphism
  `π₁(Spec K) → π₁(Spec R)` is surjective (`genericPointMap_surjective`); this uses I.10.1 in the
  form "`K ⊗_R A` is connected for `A` connected finite étale" (`isConnected_baseChange`). The
  description of the kernel is `genericPointMapKernelStatement`, proved in
  `SGA.SGA1.ExposeV.FundamentalGroupNormal` (`genericPointMapKernelStatement_holds`).

Mathlib's `Field.absoluteGaloisGroup k` is `Aut(k̄ᵃˡᵍ/k)`; it is isomorphic to the group
`Gal(k̄/k)` above (with `Ω` the algebraic closure) by `galRestrictSeparableClosure`
(`SGA.SGA1.ExposeV.FundamentalGroupField`).
-/

universe u

open CategoryTheory Limits CommAlgCat PreGaloisCategory AlgebraicGeometry TensorProduct

namespace SGA.SGA1.ExposeV

section FieldCase

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]

/-- The Galois group of `K/k` acts on the geometric points `A → K` of finite étale
`k`-algebras by composition. -/
instance (A : (FiniteEtale.{u} k)ᵒᵖ) : MulAction Gal(K/k) ((fiberFunctor k K).obj A) where
  smul σ x := (σ.toAlgHom.comp (x : A.unop →ₐ[k] K) : A.unop →ₐ[k] K)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A point of the fiber, as an algebra map. -/
abbrev fiberToAlgHom {A : (FiniteEtale.{u} k)ᵒᵖ} (x : (fiberFunctor k K).obj A) :
    A.unop →ₐ[k] K := x

lemma smul_apply (A : (FiniteEtale.{u} k)ᵒᵖ) (σ : Gal(K/k)) (x : (fiberFunctor k K).obj A)
    (a : A.unop) : fiberToAlgHom k K (σ • x) a = σ (fiberToAlgHom k K x a) := rfl

instance : IsNaturalSMul (fiberFunctor k K) Gal(K/k) where
  naturality _ _ _ _ _ := rfl

variable [IsGalois k K]

/-- A connected finite étale algebra over a field has a unique prime. -/
lemma subsingleton_primeSpectrum_of_isConnected (A : FiniteEtale.{u} k)
    [IsConnected (Opposite.op A)] : Subsingleton (PrimeSpectrum A) := by
  have : ConnectedSpace (PrimeSpectrum A) :=
    (isConnected_op_iff_connectedSpace k A).mp inferInstance
  have : IsArtinianRing A := inferInstance
  exact PreconnectedSpace.trivial_of_discrete

lemma isPretransitive_of_isConnected (X : (FiniteEtale.{u} k)ᵒᵖ) [IsConnected X] :
    MulAction.IsPretransitive Gal(K/k) ((fiberFunctor k K).obj X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨A⟩ := X
  have := subsingleton_primeSpectrum_of_isConnected k A
  let x' := fiberToAlgHom k K x
  let y' := fiberToAlgHom k K y
  have hx := RingHom.ker_isPrime x'
  have hy := RingHom.ker_isPrime y'
  have hp : RingHom.ker x' = RingHom.ker y' := congr_arg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨RingHom.ker x', hx⟩ : PrimeSpectrum A) ⟨RingHom.ker y', hy⟩)
  let p := RingHom.ker x'
  have : p.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p
  let _ := Ideal.Quotient.field p
  let xb : A ⧸ p →ₐ[k] K := Ideal.Quotient.liftₐ p x' (fun _ h ↦ h)
  let yb : A ⧸ p →ₐ[k] K := Ideal.Quotient.liftₐ p y' (fun a h ↦ by
    change a ∈ RingHom.ker x' at h
    rw [hp] at h
    exact h)
  have : FiniteDimensional k (A ⧸ p) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k (A ⧸ p)
  have hmin : minpoly k (yb α) = minpoly k (xb α) := by
    rw [minpoly.algHom_eq yb yb.injective, minpoly.algHom_eq xb xb.injective]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp hmin
  refine ⟨σ, ?_⟩
  have hext : σ.toAlgHom.comp xb = yb := by
    apply AlgHom.ext_of_adjoin_eq_top (s := {α})
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic α), hα]
      rfl
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha]
      exact hσ
  apply AlgHom.ext
  intro a
  exact congr($hext (Ideal.Quotient.mk p a))

/-- The stabilizers of geometric points are open in the Krull topology. (Private: the name
`SGA.SGA1.ExposeV.continuousSMul_fiber` is used in `SGA.SGA1.ExposeV.GaloisAxioms`.) -/
private lemma continuousSMul_fiber (X : (FiniteEtale.{u} k)ᵒᵖ) :
    ContinuousSMul Gal(K/k) ((fiberFunctor k K).obj X) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := k) (M := X.unop)
  let H : Subgroup Gal(K/k) := ⨅ i, MulAction.stabilizer Gal(K/k) (fiberToAlgHom k K x (v i))
  have hH : IsOpen (H : Set Gal(K/k)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ stabilizer_isOpen_of_isIntegral _
  refine Subgroup.isOpen_mono (H₁ := H) ?_ hH
  intro σ hσ
  rw [Subgroup.mem_iInf] at hσ
  rw [MulAction.mem_stabilizer_iff]
  have : (σ.toAlgHom.comp (fiberToAlgHom k K x)).toLinearMap =
      (fiberToAlgHom k K x).toLinearMap := by
    apply LinearMap.ext_on_range hv
    intro i
    exact hσ i
  exact AlgHom.toLinearMap_injective this

/-- Only the identity of the Galois group acts trivially on all geometric points. -/
lemma eq_one_of_smul_eq (σ : Gal(K/k))
    (h : ∀ (X : (FiniteEtale.{u} k)ᵒᵖ) (x : (fiberFunctor k K).obj X), σ • x = x) : σ = 1 := by
  ext z
  let L := IntermediateField.adjoin k {z}
  have : FiniteDimensional k L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have : Algebra.Etale k L :=
    ⟨Algebra.FormallyEtale.of_isSeparable k L, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  have := h (Opposite.op (FiniteEtale.of k L)) (L.val : L →ₐ[k] K)
  have := congr_arg (fun y : (fiberFunctor k K).obj (Opposite.op (FiniteEtale.of k L)) ↦
    fiberToAlgHom k K y (⟨z, IntermediateField.mem_adjoin_simple_self k z⟩ : L)) this
  exact this

/-- V.8.1: the Galois group `Gal(K/k)` of a separable closure `K` of `k` is a fundamental group
of the Galois category of finite étale `k`-algebras at the geometric point `k → K`. -/
instance isFundamentalGroup : IsFundamentalGroup (fiberFunctor k K) Gal(K/k) where
  transitive_of_isGalois X _ := isPretransitive_of_isConnected k K X
  continuous_smul X := continuousSMul_fiber k K X
  non_trivial' σ h := eq_one_of_smul_eq k K σ h

variable [IsSepClosed K]

/-- V.8.1: for a separable closure `K` of `k`, `Gal(K/k)` is isomorphic, as a
topological group, to the fundamental group `Aut F` of the fiber functor `A ↦ Hom_k(A, K)`. -/
noncomputable def galContinuousMulEquivAut : Gal(K/k) ≃ₜ* Aut (fiberFunctor k K) :=
  { toAutMulEquiv (fiberFunctor k K) Gal(K/k) with
    continuous_toFun := (toAutMulEquiv_isHomeomorph (fiberFunctor k K) Gal(K/k)).continuous
    continuous_invFun :=
      (toAutMulEquiv_isHomeomorph (fiberFunctor k K) Gal(K/k)).homeomorph.symm.continuous }

open scoped FintypeCatDiscrete in
/-- V.8.1: the finite étale `k`-algebras (étale coverings of `Spec k`) are anti-equivalent to
finite sets with a continuous action of `Gal(K/k)`. -/
noncomputable def finiteEtaleEquivContAction :
    (FiniteEtale.{u} k)ᵒᵖ ≌ ContAction FintypeCat Gal(K/k) :=
  (functorToContAction (fiberFunctor k K)).asEquivalence.trans
    (ContAction.resEquiv FintypeCat (galContinuousMulEquivAut k K))

end FieldCase

section SeparableClosure

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k Ω]

instance : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k

/-- The inclusion of the separable closure `k̄` of `k` in `Ω` identifies the fiber functors at
the geometric points `k → k̄` and `k → Ω`. -/
noncomputable def fiberFunctorSepClosureIso :
    fiberFunctor k (separableClosure k Ω) ≅ fiberFunctor k Ω :=
  NatIso.ofComponents (fun _ ↦ FintypeCat.equivEquivIso
    { toFun := fun y ↦ (separableClosure k Ω).val.comp y
      invFun := fun x ↦ x.codRestrict (separableClosure k Ω).toSubalgebra
        (algHom_apply_mem_separableClosure k Ω x)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

/-- V.8.1: the fundamental group `π₁(Spec k, a)` at a geometric point `a : k → Ω` (`Ω`
separably closed) is canonically isomorphic, as a topological group, to the Galois group of the
separable closure `k̄` of `k` in `Ω`. -/
noncomputable def fundamentalGroupContinuousMulEquivGal :
    fundamentalGroup k Ω ≃ₜ* Gal(separableClosure k Ω/k) :=
  (autContinuousMulEquiv (𝟭 _) ((fiberFunctor k Ω).leftUnitor ≪≫
    (fiberFunctorSepClosureIso k Ω).symm)).trans
    (galContinuousMulEquivAut k (separableClosure k Ω)).symm

/-- V.8.1, scheme version: `π₁(Spec k, s̄)` is the Galois group of the separable closure of `k`
in `Ω`, where `k → Ω` is the ring map of the geometric point `s̄`. -/
noncomputable def etaleFundamentalGroupContinuousMulEquivGal
    (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k)) :
    letI := algebraOfPoint (CommRingCat.of k) Ω s
    etaleFundamentalGroup Ω s ≃ₜ* Gal(separableClosure k Ω/k) :=
  letI := algebraOfPoint (CommRingCat.of k) Ω s
  (autContinuousMulEquiv (specEquivalence (CommRingCat.of k)).inverse
    (FEt.fiberSpecIso (CommRingCat.of k) Ω s).symm).symm.trans
    (fundamentalGroupContinuousMulEquivGal k Ω)

end SeparableClosure


section SepClosedField

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- `Ω` is the initial finite étale `Ω`-algebra. -/
def FiniteEtale.isInitialSelf : IsInitial (FiniteEtale.of Ω Ω) :=
  IsInitial.ofUniqueHom (fun B ↦ ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId Ω B)))
    (fun B f ↦ by ext)

/-- The product of `n` copies of `Ω`, as a fan in the finite étale `Ω`-algebras. -/
noncomputable def FiniteEtale.piSelfFan (n : ℕ) :
    Fan (fun _ : Fin n ↦ FiniteEtale.of Ω Ω) :=
  Fan.mk (FiniteEtale.of Ω (Fin n → Ω))
    fun i ↦ ObjectProperty.homMk (CommAlgCat.ofHom (Pi.evalAlgHom Ω (fun _ ↦ Ω) i))

/-- `Ω^n` is the product of `n` copies of `Ω`. -/
noncomputable def FiniteEtale.piSelfFanIsLimit (n : ℕ) : IsLimit (FiniteEtale.piSelfFan Ω n) :=
  Fan.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk (CommAlgCat.ofHom (AlgHom.pi fun i ↦ (s.proj i).hom.hom)))
    (fun s i ↦ rfl)
    (fun s m hm ↦ by
      ext x
      funext i
      exact congr($(hm i).hom.hom x))

/-- V.7 and V.8: over a separably closed field `Ω` every étale covering is trivial, i.e. a finite
sum of copies of the final object (finite étale `Ω`-algebras are products of copies of `Ω`). -/
theorem FiniteEtale.exists_iso_sigma_terminal (X : (FiniteEtale.{u} Ω)ᵒᵖ) :
    ∃ n : ℕ, Nonempty (X ≅ ∐ fun _ : Fin n ↦ ⊤_ (FiniteEtale.{u} Ω)ᵒᵖ) := by
  let A := X.unop
  have : Finite (PrimeSpectrum A) :=
    Finite.of_equiv _ (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω A)
  let eι := Finite.equivFin (PrimeSpectrum A)
  let eA : A ≃ₐ[Ω] (Fin (Nat.card (PrimeSpectrum A)) → Ω) :=
    (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω A).trans
      (AlgEquiv.piCongrLeft' Ω (fun _ ↦ Ω) eι)
  refine ⟨Nat.card (PrimeSpectrum A), ⟨?_⟩⟩
  let hc := Fan.IsLimit.op (FiniteEtale.piSelfFanIsLimit Ω (Nat.card (PrimeSpectrum A)))
  have hT : IsTerminal (Opposite.op (FiniteEtale.of Ω Ω)) := (FiniteEtale.isInitialSelf Ω).op
  exact (FiniteEtale.isoMk eA).op.symm ≪≫
    ((colimit.isColimit _).coconePointUniqueUpToIso hc).symm ≪≫
    Sigma.mapIso fun _ ↦ (terminalIsoIsTerminal hT).symm

/-- V.7 and V.8: over `Spec Ω`, `Ω` separably closed, every étale covering is a finite sum of
copies of `Spec Ω`. -/
theorem FEt.exists_iso_sigma_terminal (X : FEt (Spec (CommRingCat.of Ω))) :
    ∃ n : ℕ, Nonempty (X ≅ ∐ fun _ : Fin n ↦ ⊤_ (FEt (Spec (CommRingCat.of Ω)))) := by
  let E := specEquivalence (CommRingCat.of Ω)
  obtain ⟨n, ⟨i⟩⟩ := FiniteEtale.exists_iso_sigma_terminal Ω (E.inverse.obj X)
  exact ⟨n, ⟨(E.counitIso.app X).symm ≪≫ E.functor.mapIso i ≪≫
    PreservesCoproduct.iso E.functor _ ≪≫ Sigma.mapIso fun _ ↦ PreservesTerminal.iso E.functor⟩⟩

end SepClosedField

section NormalBase

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]

lemma isIntegral_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral A e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
  · simp [Polynomial.eval₂_sub, sq, he.eq]

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

/-- V.8.2: the homomorphism `π₁(Spec K, a') → π₁(Spec R, a)` induced by the generic point
`Spec K → Spec R`, where `a` is the image of the geometric point `a' : K → Ω`. -/
noncomputable def genericPointMap : fundamentalGroup K Ω →* fundamentalGroup R Ω :=
  autMap (FiniteEtale.baseChange R K).op (FiniteEtale.fiberIsoBaseChangeFiber R Ω K).symm

lemma continuous_genericPointMap : Continuous (genericPointMap R K Ω) :=
  continuous_autMap _ _

variable [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]

/-- I.10.1 in the form used in V.8.2: over a normal domain `R` with fraction field `K`, the
generic fiber `K ⊗_R A` of a connected finite étale `R`-algebra `A` is connected. -/
theorem isConnected_baseChange (A : FiniteEtale.{u} R) (h : IsConnected (Opposite.op A)) :
    IsConnected ((FiniteEtale.baseChange R K).op.obj (Opposite.op A)) := by
  have : ConnectedSpace (PrimeSpectrum R) := by
    rw [connectedSpace_primeSpectrum_iff]
    exact ⟨inferInstance, fun e he ↦ IsIdempotentElem.iff_eq_zero_or_one.mp he⟩
  obtain ⟨hA, hid⟩ := (isConnected_op_iff R A).mp h
  change IsConnected (Opposite.op (FiniteEtale.of K (K ⊗[R] A)))
  rw [isConnected_op_iff]
  have hinj : Function.Injective (algebraMap A (A ⊗[R] K)) :=
    SGA.SGA1.ExposeI.injective_algebraMap_tensor_fractionRing K
  have hic : IsIntegrallyClosedIn A (A ⊗[R] K) :=
    SGA.SGA1.ExposeI.isIntegrallyClosedIn_tensor_fractionRing K
  let c := Algebra.TensorProduct.comm R K A
  refine ⟨?_, fun e he ↦ ?_⟩
  · have : Nontrivial (A ⊗[R] K) := hinj.nontrivial
    exact c.toEquiv.nontrivial
  · have he' : IsIdempotentElem (c e) := he.map c
    obtain ⟨a, ha⟩ := hic.isIntegral_iff.mp (isIntegral_of_isIdempotentElem (A := A) he')
    have haid : IsIdempotentElem a := hinj (by rw [map_mul, ha, he'.eq])
    rcases hid a haid with rfl | rfl
    · left
      apply c.injective
      rw [← ha, map_zero, map_zero]
    · right
      apply c.injective
      rw [← ha, map_one, map_one]

/-- V.8.2 (first assertion): if `R` is a normal domain with fraction field `K`, the
homomorphism `π₁(Spec K, a') → π₁(Spec R, a)` is surjective. (SGA assumes `R` noetherian.) -/
theorem genericPointMap_surjective [IsSepClosed Ω] :
    Function.Surjective (genericPointMap R K Ω) := by
  have : ConnectedSpace (PrimeSpectrum R) := by
    rw [connectedSpace_primeSpectrum_iff]
    exact ⟨inferInstance, fun e he ↦ IsIdempotentElem.iff_eq_zero_or_one.mp he⟩
  exact autMap_surjective _ _ fun X hX ↦ isConnected_baseChange R K X.unop hX

end NormalBase

/-- V.8.2 (second assertion): identifying `π₁(Spec K, a')` with the Galois group of
the separable closure `K̄` of `K` in `Ω` (V.8.1), the kernel of `π₁(Spec K) → π₁(Spec R)` is the
subgroup fixing the compositum of the finite subextensions of `K̄/K` which are unramified over
`Spec R` (I.10.3: the integral closure of `R` in them is étale over `R`). It is proved in
`SGA.SGA1.ExposeV.FundamentalGroupNormal` (`genericPointMapKernelStatement_holds`). -/
def genericPointMapKernelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra (FractionRing R) Ω] [Algebra R Ω]
    [IsScalarTower R (FractionRing R) Ω],
    ((genericPointMap R (FractionRing R) Ω).comp
        (fundamentalGroupContinuousMulEquivGal (FractionRing R) Ω).symm.toMonoidHom).ker =
      (⨆ (L : IntermediateField (FractionRing R) (separableClosure (FractionRing R) Ω))
        (_ : FiniteDimensional (FractionRing R) L ∧ SGA.SGA1.ExposeI.IsUnramifiedOver R L),
        L).fixingSubgroup

end SGA.SGA1.ExposeV
