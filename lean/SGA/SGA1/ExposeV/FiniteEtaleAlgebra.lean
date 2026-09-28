/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SeparableClosure


/-!
# SGA 1, Exposé V: algebra of finite étale coverings of an affine base

This file contains the commutative algebra behind V.7 (the fundamental group of a connected
prescheme) for an affine base `Spec R` with `Spec R` connected. The categorical statements
(Galois category, fundamental group) are in `SGA.SGA1.ExposeV.FiniteEtaleGalois`.

* V.3.4 (affine, connected base): the invariants `A^G` of a finite étale `R`-algebra under a
  finite group are finite étale (`finite_etale_fixedPoints`). The proof splits `A` by a
  faithfully flat finite étale `R`-algebra without nontrivial idempotents (Lenstra 5.10 and a
  connected component of it), computes the invariants of a split algebra, and descends.
* The geometric points of `A^G` are the `G`-orbits of those of `A`
  (`exists_comp_val_eq_of_fixedPoints`, `exists_eq_comp_smul_of_comp_val_eq`).
* V.3.7 (affine, connected base): a map of finite étale algebras inducing a bijection on the
  geometric points over one geometric point is an isomorphism (`bijective_of_bijective_comp`).
* V.7: the number of geometric points of a finite étale algebra is its rank
  (`card_algHom_eq_rankAtStalk`).
* Ingredients for (G 3) and (G 5): surjections of étale algebras have idempotent kernel
  (`exists_isIdempotentElem_ker_eq`), and maps satisfying the categorical monomorphism
  condition are surjective on spectra (`comap_surjective_of_cancel`).
-/

universe u v

open TensorProduct Pointwise

namespace SGA.SGA1.ExposeV

section Rank

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite étale algebra is finitely presented as a module. -/
lemma finitePresentation_of_finite_etale [Module.Finite R A] [Algebra.Etale R A] :
    Module.FinitePresentation R A :=
  .of_finite_of_finitePresentation R A

variable [PreconnectedSpace (PrimeSpectrum R)] [Module.Finite R A] [Algebra.Etale R A]

/-- Over a ring with connected spectrum, a finite étale algebra has constant rank. -/
lemma rankAtStalk_eq_of_preconnected (p q : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) A p = Module.rankAtStalk (R := R) A q := by
  have := finitePresentation_of_finite_etale (R := R) (A := A)
  exact Module.isLocallyConstant_rankAtStalk.apply_eq_of_preconnectedSpace p q

/-- Over a ring with connected spectrum, a nonzero finite étale algebra has positive rank
at every prime. -/
lemma rankAtStalk_pos_of_nontrivial [Nontrivial A] (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) A p := by
  have := finitePresentation_of_finite_etale (R := R) (A := A)
  by_contra! h
  have h0 : Module.rankAtStalk (R := R) A = 0 := by
    ext q
    rw [rankAtStalk_eq_of_preconnected q p]
    simpa using h
  rw [Module.rankAtStalk_eq_zero_iff_subsingleton] at h0
  exact not_subsingleton A h0

/-- Over a ring with connected spectrum, a nonzero finite étale algebra is faithfully flat. -/
lemma faithfullyFlat_of_nontrivial [Nontrivial A] : Module.FaithfullyFlat R A := by
  apply Module.FaithfullyFlat.of_comap_surjective
  rw [← PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]
  exact rankAtStalk_pos_of_nontrivial

end Rank

section ConnectedSpectrum

/-- The spectrum of a ring is connected if and only if the ring is nonzero and has no idempotents
other than `0` and `1`. -/
lemma connectedSpace_primeSpectrum_iff (A : Type*) [CommRing A] :
    ConnectedSpace (PrimeSpectrum A) ↔
      Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [connectedSpace_iff_clopen, PrimeSpectrum.nonempty_iff_nontrivial]
  refine and_congr_right fun _ ↦ ⟨fun h e he ↦ ?_, fun h s hs ↦ ?_⟩
  · rcases h _ (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩) with h₀ | h₁
    · left
      apply he.eq_zero_of_isNilpotent
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      exact TopologicalSpace.Opens.ext h₀
    · right
      have hu : IsUnit e := by
        by_contra hne
        obtain ⟨M, hM, heM⟩ := exists_max_ideal_of_mem_nonunits hne
        have : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen e : Set _) := by
          rw [h₁]
          trivial
        exact this heM
      exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he
  · obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left
      simp
    · right
      simp

end ConnectedSpectrum

section Points

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
  [Algebra.Etale R A] (Ω : Type*) [Field Ω] [Algebra R Ω]

/-- The point of `Spec R` under a geometric point `R → Ω`. -/
def geomPointImage : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R Ω), RingHom.ker_isPrime _⟩

/-- V.7: the number of geometric points of a finite étale `R`-algebra over a geometric point
`R → Ω` (with `Ω` separably closed) is the rank of the algebra at the image point. -/
lemma card_algHom_eq_rankAtStalk [IsSepClosed Ω] :
    Nat.card (A →ₐ[R] Ω) = Module.rankAtStalk (R := R) A (geomPointImage Ω) := by
  classical
  let e₁ := Algebra.TensorProduct.liftEquivRight R Ω A Ω
  let e₂ := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω (Ω ⊗[R] A)
  let e₃ := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] A)
  have : Finite (PrimeSpectrum (Ω ⊗[R] A)) := Finite.of_equiv _ (e₁.trans e₂)
  have : Fintype (PrimeSpectrum (Ω ⊗[R] A)) := Fintype.ofFinite _
  let p : PrimeSpectrum Ω := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : PrimeSpectrum.comap (algebraMap R Ω) p = geomPointImage Ω := by
    ext x
    simp [geomPointImage, p]
  rw [Nat.card_congr (e₁.trans e₂), ← hp, ← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free, e₃.toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card, Pi.natCast_apply, Nat.cast_id]

/-- A nonzero finite étale algebra over a ring with connected spectrum has a geometric point
over every geometric point of the base. -/
lemma nonempty_algHom_of_nontrivial [PreconnectedSpace (PrimeSpectrum R)] [Nontrivial A]
    [IsSepClosed Ω] : Nonempty (A →ₐ[R] Ω) := by
  have hpos := rankAtStalk_pos_of_nontrivial (R := R) (A := A) (geomPointImage Ω)
  have : Finite (A →ₐ[R] Ω) := by
    by_contra h
    rw [not_finite_iff_infinite] at h
    have := card_algHom_eq_rankAtStalk (R := R) (A := A) Ω
    rw [Nat.card_eq_zero_of_infinite] at this
    omega
  rw [← card_algHom_eq_rankAtStalk (R := R) (A := A) Ω] at hpos
  exact (Nat.card_pos_iff.mp hpos).1

end Points

section SeparableClosure

variable (k : Type*) [Field k] (Ω : Type*) [Field Ω] [Algebra k Ω]

/-- Geometric points of a finite étale algebra over a field `k` take values in the separable
closure of `k`. -/
lemma algHom_apply_mem_separableClosure {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.Etale k A] (x : A →ₐ[k] Ω) (a : A) : x a ∈ separableClosure k Ω := by
  have := RingHom.ker_isPrime x
  let p := RingHom.ker x
  let xb : (A ⧸ p) →ₐ[k] Ω := Ideal.Quotient.liftₐ p x (fun _ h ↦ h)
  have hxb : Function.Injective xb := (Ideal.injective_lift_iff _).mpr rfl
  have h : x a = xb (Ideal.Quotient.mk p a) := rfl
  rw [h, mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq xb hxb]
  exact Algebra.IsSeparable.isSeparable k _

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
  [Algebra R Ω] (L : Type*) [Field L] [Algebra Ω L] [Algebra R L]
  [IsScalarTower R Ω L] [IsSepClosed L]

/-- If `Ω` is separably closed, the geometric points of a finite étale `R`-algebra with values in
an extension `L` of `Ω` take values in `Ω`. -/
lemma algHom_apply_mem_range_of_isSepClosed [IsSepClosed Ω] (x : A →ₐ[R] L) (a : A) :
    x a ∈ Set.range (algebraMap Ω L) := by
  let y := Algebra.TensorProduct.liftEquivRight R Ω A L x
  have h := algHom_apply_mem_separableClosure Ω L y (1 ⊗ₜ a)
  rw [(IsSepClosed.separableClosure_eq_bot_iff Ω L).mpr inferInstance,
    IntermediateField.mem_bot] at h
  simpa [y] using h

end SeparableClosure

section Lift

variable {B A Ω : Type*} [CommRing B] [CommRing A] [Algebra B A] [Field Ω] [IsAlgClosed Ω]

/-- Lifting geometric points along an integral extension: if `A` is integral over `B`, `y` is a
geometric point of `B` and some prime of `A` lies over the kernel of `y`, then `y` extends to
`A`. -/
lemma exists_lift_of_isIntegral [Algebra.IsIntegral B A] (y : B →+* Ω) (P : Ideal A) [P.IsPrime]
    (hP : P.comap (algebraMap B A) = RingHom.ker y) :
    ∃ x : A →+* Ω, x.comp (algebraMap B A) = y := by
  let p := RingHom.ker y
  have : p.IsPrime := RingHom.ker_isPrime y
  have : P.LiesOver p := ⟨hP.symm⟩
  let ybar : B ⧸ p →+* Ω := Ideal.Quotient.lift p y (fun _ h ↦ h)
  let _ : Algebra (B ⧸ p) Ω := ybar.toAlgebra
  have : FaithfulSMul (B ⧸ p) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Ideal.injective_lift_iff (I := p) (f := y) (fun _ h ↦ h) |>.mpr rfl
  have : Algebra.IsAlgebraic (B ⧸ p) (A ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let f : (A ⧸ P) →ₐ[B ⧸ p] Ω := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext b
  exact f.commutes (Ideal.Quotient.mk p b)

/-- Lifting geometric points along an integral algebra map which is surjective on spectra. -/
lemma exists_lift_of_isIntegral_of_surjective [Algebra.IsIntegral B A]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap B A))) (y : B →+* Ω) :
    ∃ x : A →+* Ω, x.comp (algebraMap B A) = y := by
  obtain ⟨P, hP⟩ := h ⟨RingHom.ker y, RingHom.ker_isPrime y⟩
  exact exists_lift_of_isIntegral y P.asIdeal congr($(hP).asIdeal)

end Lift

section Invariants

variable {B A Ω : Type*} [CommRing B] [CommRing A] [Algebra B A] [Field Ω]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G]

omit [SMulCommClass G B A] in
open Polynomial in
/-- Two geometric points of `A` which agree on the invariants differ elementwise by `G`. -/
lemma exists_smul_apply_eq_of_comp_eq (x y : A →+* Ω)
    (hxy : x.comp (algebraMap B A) = y.comp (algebraMap B A)) (a : A) :
    ∃ g : G, y a = x (g • a) := by
  cases nonempty_fintype G
  obtain ⟨q, hq⟩ := Polynomial.mem_lifts _ |>.mp (Algebra.IsInvariant.charpoly_mem_lifts B A G a)
  have h0 : (MulSemiringAction.charpoly G a).eval a = 0 := MulSemiringAction.eval_charpoly G a
  have h1 : ((MulSemiringAction.charpoly G a).map y).eval (y a) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, h0, map_zero]
  have h2 : (MulSemiringAction.charpoly G a).map y = (MulSemiringAction.charpoly G a).map x := by
    rw [← hq, Polynomial.map_map, Polynomial.map_map, hxy]
  rw [h2, MulSemiringAction.charpoly, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h1
  obtain ⟨g, -, hg⟩ := h1
  exact ⟨g, by simpa [sub_eq_zero] using hg⟩

omit [Finite G] [Algebra.IsInvariant B A G] in
lemma ker_comp_smul (x : A →+* Ω) (g : G) :
    RingHom.ker (x.comp (MulSemiringAction.toRingHom G A g⁻¹)) = g • RingHom.ker x := by
  ext a
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

/-- Two geometric points of `A` which agree on the invariants are conjugate under `G`. -/
lemma exists_eq_comp_smul_of_comp_eq (x y : A →+* Ω)
    (hxy : x.comp (algebraMap B A) = y.comp (algebraMap B A)) :
    ∃ g : G, ∀ a, y a = x (g • a) := by
  have := RingHom.ker_isPrime x
  have := RingHom.ker_isPrime y
  have hunder : (RingHom.ker x).under B = (RingHom.ker y).under B := by
    simp only [Ideal.under, RingHom.comap_ker, hxy]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G (RingHom.ker x)
    (RingHom.ker y) hunder
  set Q := RingHom.ker y
  set x' := x.comp (MulSemiringAction.toRingHom G A g⁻¹)
  have hx'Q : RingHom.ker x' = Q := by rw [ker_comp_smul, hg]
  have hx'B : x'.comp (algebraMap B A) = y.comp (algebraMap B A) := by
    ext b
    simp [x', ← hxy, smul_algebraMap]
  set p := Q.under B
  let xb : A ⧸ Q →+* Ω := Ideal.Quotient.lift Q x' (fun a ha ↦ by rwa [← RingHom.mem_ker, hx'Q])
  let yb : A ⧸ Q →+* Ω := Ideal.Quotient.lift Q y (fun a ha ↦ ha)
  have hxb : Function.Injective xb := by
    rw [Ideal.injective_lift_iff]
    exact hx'Q
  have hyb : Function.Injective yb := (Ideal.injective_lift_iff _).2 rfl
  have hrange : ∀ z, yb z ∈ Set.range xb := by
    rintro ⟨a⟩
    obtain ⟨h, hh⟩ := exists_smul_apply_eq_of_comp_eq (B := B) G x' y hx'B a
    exact ⟨Ideal.Quotient.mk Q (h • a), hh.symm⟩
  have hrange' : ∀ z, xb z ∈ Set.range yb := by
    rintro ⟨a⟩
    obtain ⟨h, hh⟩ := exists_smul_apply_eq_of_comp_eq (B := B) G y x' hx'B.symm a
    exact ⟨Ideal.Quotient.mk Q (h • a), hh.symm⟩
  choose σ₀ hσ₀ using hrange
  have hσ₀' : ∀ z, xb (σ₀ z) = yb z := hσ₀
  let σ : (A ⧸ Q) ≃ₐ[B ⧸ p] (A ⧸ Q) :=
    { toFun := σ₀
      invFun := fun w ↦ (hrange' w).choose
      left_inv := fun z ↦ hyb (by rw [(hrange' _).choose_spec, hσ₀'])
      right_inv := fun w ↦ hxb (by rw [hσ₀', (hrange' w).choose_spec])
      map_mul' := fun z w ↦ hxb (by simp [hσ₀'])
      map_add' := fun z w ↦ hxb (by simp [hσ₀'])
      commutes' := by
        rintro ⟨b⟩
        apply hxb
        rw [hσ₀']
        exact (congr($hx'B b)).symm }
  obtain ⟨τ, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective G p Q σ
  refine ⟨g⁻¹ * τ, fun a ↦ ?_⟩
  have h1 : y a = xb (σ (Ideal.Quotient.mk Q a)) := (hσ₀' (Ideal.Quotient.mk Q a)).symm
  rw [h1, ← hτ, Ideal.Quotient.stabilizerHom_apply]
  simp [xb, x', mul_smul]
  rfl

end Invariants


section FixedPointsPoints

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (G : Type*) [Group G] [MulSemiringAction G A] [SMulCommClass G R A]
  {Ω : Type*} [Field Ω] [Algebra R Ω]

instance isInvariant_fixedPoints :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G :=
  ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

/-- V.1 / V.2, on geometric points: every geometric point of the invariants `A^G` extends to a
geometric point of `A` (`Ω` algebraically closed). -/
lemma exists_comp_val_eq_of_fixedPoints [Finite G] [IsAlgClosed Ω]
    (z : FixedPoints.subalgebra R A G →ₐ[R] Ω) :
    ∃ x : A →ₐ[R] Ω, x.comp (FixedPoints.subalgebra R A G).val = z := by
  have : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
    Algebra.IsInvariant.isIntegral _ A G
  have : FaithfulSMul (FixedPoints.subalgebra R A G) A :=
    (faithfulSMul_iff_algebraMap_injective (FixedPoints.subalgebra R A G) A).mpr
      Subtype.val_injective
  obtain ⟨x, hx⟩ := exists_lift_of_isIntegral_of_surjective
    (Algebra.IsIntegral.comap_surjective (FixedPoints.subalgebra R A G) A) z.toRingHom
  refine ⟨{ x with commutes' := fun r ↦ ?_ }, AlgHom.ext fun b ↦ congr($hx b)⟩
  have := congr($hx (algebraMap R _ r))
  simpa using this

/-- V.1 / V.2, on geometric points: two geometric points of `A` which agree on the invariants
`A^G` differ by an element of `G`. -/
lemma exists_eq_comp_smul_of_comp_val_eq [Finite G] (x y : A →ₐ[R] Ω)
    (h : x.comp (FixedPoints.subalgebra R A G).val = y.comp (FixedPoints.subalgebra R A G).val) :
    ∃ g : G, ∀ a, y a = x (g • a) :=
  exists_eq_comp_smul_of_comp_eq (B := FixedPoints.subalgebra R A G) G x.toRingHom y.toRingHom
    (RingHom.ext fun b ↦ congr($h b))

end FixedPointsPoints

section FlatBaseChange

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  (G : Type*) [Group G] [MulSemiringAction G A] [SMulCommClass G R A]
  (T : Type*) [CommRing T] [Algebra R T]

/-- The action of `g : G` on `T ⊗[R] A`, through the second factor. -/
noncomputable def baseChangeSMul (g : G) : T ⊗[R] A →ₐ[T] T ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom R A g)

/-- The map `T ⊗[R] A^G → T ⊗[R] A`. -/
noncomputable def fixedBaseChangeMap :
    T ⊗[R] FixedPoints.subalgebra R A G →ₐ[T] T ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra R A G).val

variable [Module.Flat R T]

lemma fixedBaseChangeMap_injective : Function.Injective (fixedBaseChangeMap R A G T) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := T)
    (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective

/-- Formation of invariants commutes with flat base change. -/
lemma mem_range_fixedBaseChangeMap [Finite G] (x : T ⊗[R] A) :
    x ∈ (fixedBaseChangeMap R A G T).range ↔ ∀ g, baseChangeSMul R A G T g x = x := by
  cases nonempty_fintype G
  classical
  let δ : A →ₗ[R] (G → A) := LinearMap.pi
    fun g ↦ (MulSemiringAction.toAlgHom R A g).toLinearMap - LinearMap.id
  have hex : Function.Exact (FixedPoints.subalgebra R A G).val.toLinearMap δ := by
    intro a
    constructor
    · intro h
      refine ⟨⟨a, fun g ↦ ?_⟩, rfl⟩
      simpa [δ, sub_eq_zero] using congr_fun h g
    · rintro ⟨⟨b, hb⟩, rfl⟩
      ext g
      simpa [δ, sub_eq_zero] using hb g
  have hT := Module.Flat.lTensor_exact T hex
  have h1 : ∀ y, fixedBaseChangeMap R A G T y =
      LinearMap.lTensor T (FixedPoints.subalgebra R A G).val.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => rfl
    | add y z hy hz => simp [hy, hz]
  have h2 : ∀ y, TensorProduct.piRightHom R R T (fun _ : G ↦ A) (LinearMap.lTensor T δ y) =
      fun g ↦ baseChangeSMul R A G T g y - y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => ext; simp
    | tmul t a =>
      ext g
      simp [δ, baseChangeSMul, TensorProduct.tmul_sub]
    | add y z hy hz =>
      ext g
      simp only [map_add, Pi.add_apply, hy, hz]
      abel
  have hinj : Function.Injective (TensorProduct.piRightHom R R T (fun _ : G ↦ A)) := by
    intro a b hab
    apply (TensorProduct.piRight R R T (fun _ : G ↦ A)).injective
    simpa using hab
  rw [AlgHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩ g
    rw [h1]
    have := hT (LinearMap.lTensor T (FixedPoints.subalgebra R A G).val.toLinearMap y) |>.mpr
      ⟨y, rfl⟩
    have h3 := congr_fun (congr_arg (TensorProduct.piRightHom R R T (fun _ : G ↦ A)) this) g
    rw [h2, map_zero] at h3
    simpa [sub_eq_zero] using h3
  · intro h
    have : LinearMap.lTensor T δ x = 0 := by
      apply hinj
      rw [h2, map_zero]
      ext g
      simp [h g]
    obtain ⟨y, hy⟩ := (hT x).mp this
    exact ⟨y, (h1 y).trans hy⟩

end FlatBaseChange

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)] {D : Type*} [CommRing D]

/-- A ring map out of a product which sends the `i`-th unit idempotent to `1` factors through
the `i`-th projection. -/
lemma apply_eq_apply_single_of_single_one [DecidableEq ι] (x : (Π i, A i) →+* D) {i : ι}
    (hi : x (Pi.single i 1) = 1) (f : Π i, A i) : x f = x (Pi.single i (f i)) := by
  calc x f = x f * x (Pi.single i 1) := by rw [hi, mul_one]
    _ = x (Pi.single i (f i)) := by
      rw [← map_mul]
      congr 1
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]

/-- A ring map from a finite product into a nonzero ring without nontrivial idempotents sends
exactly one unit idempotent to `1`. -/
lemma exists_single_one [Finite ι] [DecidableEq ι] [Nontrivial D]
    (hD : ∀ e : D, IsIdempotentElem e → e = 0 ∨ e = 1) (x : (Π i, A i) →+* D) :
    ∃ i, x (Pi.single i 1) = 1 := by
  cases nonempty_fintype ι
  by_contra! h
  have hid (i : ι) : IsIdempotentElem (Pi.single (M := A) i 1) := by
    simp [IsIdempotentElem, ← Pi.single_mul]
  have h0 (i : ι) : x (Pi.single i 1) = 0 :=
    (hD _ ((hid i).map x)).resolve_right (h i)
  have : x 1 = ∑ i, x (Pi.single i 1) := by
    rw [← map_sum, Finset.univ_sum_single]
    rfl
  simp [h0] at this

lemma eq_of_single_one [DecidableEq ι] [Nontrivial D] (x : (Π i, A i) →+* D) {i j : ι}
    (hi : x (Pi.single i 1) = 1) (hj : x (Pi.single j 1) = 1) : i = j := by
  by_contra h
  have h0 : (Pi.single i 1 * Pi.single j 1 : Π i, A i) = 0 := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [h]
    · simp [hk]
  have := congr_arg x h0
  rw [map_mul, hi, hj, map_zero, mul_one] at this
  exact one_ne_zero this

end Pi

section Split

variable {T : Type*} [CommRing T] [Nontrivial T]
  (hT : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) {ι : Type v} [Finite ι]

include hT in
/-- If `T` has no nontrivial idempotents, the `T`-algebra maps `(ι → T) → T` are the
evaluations. -/
lemma exists_eq_evalAlgHom (χ : (ι → T) →ₐ[T] T) :
    ∃ i, χ = Pi.evalAlgHom T (fun _ ↦ T) i := by
  classical
  obtain ⟨i, hi⟩ := exists_single_one hT χ.toRingHom
  refine ⟨i, AlgHom.ext fun f ↦ ?_⟩
  have h1 := apply_eq_apply_single_of_single_one χ.toRingHom hi f
  have h2 : (Pi.single i (f i) : ι → T) = f i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 hi
  rw [h1, h2, map_smul, hi, smul_eq_mul, mul_one]
  rfl

include hT in
/-- If `T` has no nontrivial idempotents, the `T`-algebra endomorphisms of `ι → T` are given by
precomposition with maps `ι → ι`. -/
lemma exists_eq_comp (ψ : (ι → T) →ₐ[T] (ι → T)) : ∃ τ : ι → ι, ∀ f, ψ f = f ∘ τ := by
  choose τ hτ using fun k ↦ exists_eq_evalAlgHom hT ((Pi.evalAlgHom T (fun _ ↦ T) k).comp ψ)
  exact ⟨τ, fun f ↦ funext fun k ↦ congr($(hτ k) f)⟩

include hT in
/-- If `T` has no nontrivial idempotents, the joint fixed points of a family of `T`-algebra
endomorphisms of `ι → T` form again a split algebra. -/
lemma nonempty_algEquiv_fixed {J : Type*} (ψ : J → ((ι → T) →ₐ[T] (ι → T))) :
    ∃ (κ : Type v) (_ : Finite κ),
      Nonempty ((⨅ j, AlgHom.equalizer (ψ j) (AlgHom.id T _) : Subalgebra T (ι → T)) ≃ₐ[T]
        (κ → T)) := by
  choose τ hτ using fun j ↦ exists_eq_comp hT (ψ j)
  let r : ι → ι → Prop := fun a b ↦ ∃ j, τ j a = b
  let π : ι → Quot r := Quot.mk r
  let φ : (Quot r → T) →ₐ[T] (ι → T) := AlgHom.pi fun a ↦ Pi.evalAlgHom T (fun _ ↦ T) (π a)
  have hφ : ∀ g a, φ g a = g (π a) := fun _ _ ↦ rfl
  have hinj : Function.Injective φ := by
    intro g g' h
    funext q
    obtain ⟨a, rfl⟩ := Quot.exists_rep q
    exact congr_fun h a
  have hrange : φ.range = ⨅ j, AlgHom.equalizer (ψ j) (AlgHom.id T _) := by
    ext f
    simp only [AlgHom.mem_range, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.coe_id,
      id_eq]
    constructor
    · rintro ⟨g, rfl⟩ j
      rw [hτ]
      funext a
      simp only [Function.comp_apply, hφ]
      exact congr_arg g (Quot.sound ⟨j, rfl⟩).symm
    · intro h
      refine ⟨Quot.lift f fun a b ⟨j, hj⟩ ↦ ?_, rfl⟩
      rw [← hj, ← congr_fun (h j) a, hτ]
      rfl
  exact ⟨Quot r, inferInstance,
    ⟨((AlgEquiv.ofInjective φ hinj).trans (Subalgebra.equivOfEq _ _ hrange)).symm⟩⟩

end Split

section ConnectedSplitting

variable {R : Type u} [CommRing R]

/-- The quotient of a finite étale algebra by an idempotent is finite étale. -/
lemma finite_etale_quotient_one_sub {T : Type*} [CommRing T] [Algebra R T] [Module.Finite R T]
    [Algebra.Etale R T] {e : T} (he : IsIdempotentElem e) :
    Module.Finite R (T ⧸ Ideal.span {1 - e}) ∧ Algebra.Etale R (T ⧸ Ideal.span {1 - e}) := by
  refine ⟨Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap
    Ideal.Quotient.mk_surjective, ?_⟩
  have : IsLocalization.Away e (T ⧸ Ideal.span {1 - e}) :=
    IsLocalization.away_of_isIdempotentElem he (Ideal.mk_ker) Ideal.Quotient.mk_surjective
  have : Algebra.Etale T (T ⧸ Ideal.span {1 - e}) := .of_isLocalizationAway e
  exact .comp R T _

lemma nontrivial_quotient_one_sub {T : Type*} [CommRing T] {e : T} (he : IsIdempotentElem e)
    (he0 : e ≠ 0) : Nontrivial (T ⧸ Ideal.span {1 - e}) := by
  rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
  intro hu
  exact he0 (by simpa using (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he.one_sub)

variable [PreconnectedSpace (PrimeSpectrum R)]

/-- Over a ring with connected spectrum, every nonzero finite étale algebra has a nonzero finite
étale quotient without nontrivial idempotents (a connected component). -/
lemma exists_connected_quotient (p₀ : PrimeSpectrum R) (n : ℕ) : ∀ (T₀ : Type u) [CommRing T₀]
    [Algebra R T₀] [Module.Finite R T₀] [Algebra.Etale R T₀] [Nontrivial T₀],
    Module.rankAtStalk (R := R) T₀ p₀ = n →
    ∃ (T₁ : Type u) (_ : CommRing T₁) (_ : Algebra R T₁) (_ : Module.Finite R T₁)
      (_ : Algebra.Etale R T₁) (_ : Nontrivial T₁),
      (∀ e : T₁, IsIdempotentElem e → e = 0 ∨ e = 1) ∧ Nonempty (T₀ →ₐ[R] T₁) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T₀ _ _ _ _ _ hn
  by_cases h : ∀ e : T₀, IsIdempotentElem e → e = 0 ∨ e = 1
  · exact ⟨T₀, _, _, inferInstance, inferInstance, inferInstance, h, ⟨AlgHom.id R T₀⟩⟩
  push Not at h
  obtain ⟨e, he, he0, he1⟩ := h
  obtain ⟨_, _⟩ := finite_etale_quotient_one_sub (R := R) he
  have := nontrivial_quotient_one_sub he he0
  obtain ⟨_, _⟩ := finite_etale_quotient_one_sub (R := R) he.one_sub
  have : Nontrivial (T₀ ⧸ Ideal.span {1 - (1 - e)}) :=
    nontrivial_quotient_one_sub he.one_sub (sub_ne_zero.mpr (Ne.symm he1))
  let E := AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub.one_sub he.one_sub
    (sub_add_cancel 1 (1 - e)) (by rw [(he.one_sub).one_sub_mul_self])
  have hrank := Module.rankAtStalk_eq_of_equiv E.toLinearEquiv
  rw [Module.rankAtStalk_prod] at hrank
  have hlt : Module.rankAtStalk (R := R) (T₀ ⧸ Ideal.span {1 - e}) p₀ < n := by
    have := congr_fun hrank p₀
    have hpos := rankAtStalk_pos_of_nontrivial (R := R) (A := T₀ ⧸ Ideal.span {1 - (1 - e)}) p₀
    simp only [Pi.add_apply] at this
    omega
  obtain ⟨T₁, _, _, _, _, _, hT₁, ⟨f⟩⟩ := ih _ hlt (T₀ ⧸ Ideal.span {1 - e}) rfl
  exact ⟨T₁, _, _, inferInstance, inferInstance, inferInstance, hT₁,
    ⟨f.comp (Ideal.Quotient.mkₐ R _)⟩⟩

omit [PreconnectedSpace (PrimeSpectrum R)] in
lemma nontrivial_of_faithfullyFlat [Nontrivial R] (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] : Nontrivial T :=
  (TensorProduct.lid R T).toEquiv.symm.nontrivial

/-- Over a ring with connected spectrum, a finite étale algebra is split by a faithfully flat
algebra without nontrivial idempotents. -/
lemma exists_connected_split [Nonempty (PrimeSpectrum R)] (A : Type u) [CommRing A]
    [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T), Module.FaithfullyFlat R T ∧ Nontrivial T ∧
      (∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) ∧ Algebra.IsFiniteSplit T (T ⊗[R] A) := by
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p₀⟩
  have hA : Module.rankAtStalk (R := R) A = (Module.rankAtStalk (R := R) A p₀ : ℕ) := by
    ext p
    simp [rankAtStalk_eq_of_preconnected (A := A) p p₀]
  obtain ⟨T₀, _, _, _, _, _, hsplit⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hA
  have := nontrivial_of_faithfullyFlat (R := R) T₀
  obtain ⟨T₁, _, _, _, _, _, hT₁, ⟨f⟩⟩ := exists_connected_quotient p₀ _ T₀ rfl
  let _ := f.toAlgebra
  have : IsScalarTower R T₀ T₁ := .of_algebraMap_eq' f.comp_algebraMap.symm
  exact ⟨T₁, _, _, faithfullyFlat_of_nontrivial, inferInstance, hT₁,
    .of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₀ T₁ T₁ A)⟩

end ConnectedSplitting

section FixedPointsFiniteEtale

variable {R : Type u} [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
  [Nonempty (PrimeSpectrum R)]

/-- V.3.4 (affine case, over a connected base): if `A` is a finite étale `R`-algebra and `G` a
finite group acting on `A` by `R`-algebra automorphisms, then the invariants `A^G` form a finite
étale `R`-algebra. (SGA proves this for any locally noetherian base; here `Spec R` is assumed
connected, which is the case needed in V.7.) -/
theorem finite_etale_fixedPoints (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A]
    [Algebra.Etale R A] (G : Type*) [Group G] [Finite G] [MulSemiringAction G A]
    [SMulCommClass G R A] :
    Module.Finite R (FixedPoints.subalgebra R A G) ∧
      Algebra.Etale R (FixedPoints.subalgebra R A G) := by
  obtain ⟨T, _, _, _, _, hT, hsplit⟩ := exists_connected_split (R := R) A
  obtain ⟨n, ⟨e⟩⟩ := hsplit.nonempty_algEquiv_fun
  let ψ : G → ((Fin n → T) →ₐ[T] (Fin n → T)) := fun g ↦
    (e.toAlgHom.comp (baseChangeSMul R A G T g)).comp e.symm.toAlgHom
  obtain ⟨κ, _, ⟨E⟩⟩ := nonempty_algEquiv_fixed hT ψ
  let Φ := fixedBaseChangeMap R A G T
  have hrange : Φ.range.map e.toAlgHom = ⨅ g, AlgHom.equalizer (ψ g) (AlgHom.id T _) := by
    ext y
    simp only [Subalgebra.mem_map, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.coe_id, id_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩ g
      rw [mem_range_fixedBaseChangeMap] at hx
      simp [ψ, hx g]
    · intro h
      refine ⟨e.symm y, (mem_range_fixedBaseChangeMap R A G T _).mpr fun g ↦ ?_, by simp⟩
      apply e.injective
      simpa [ψ] using h g
  let EE : T ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[T] (κ → T) :=
    (AlgEquiv.ofInjective Φ (fixedBaseChangeMap_injective R A G T)).trans <|
      (Subalgebra.equivMapOfInjective _ e.toAlgHom e.injective).trans <|
        (Subalgebra.equivOfEq _ _ hrange).trans E
  have : Module.Finite T (T ⊗[R] FixedPoints.subalgebra R A G) :=
    Module.Finite.equiv EE.symm.toLinearEquiv
  have : Algebra.Etale T (T ⊗[R] FixedPoints.subalgebra R A G) := .of_equiv EE.symm
  exact ⟨.of_finite_tensorProduct_of_faithfullyFlat T,
    .of_etale_tensorProduct_of_faithfullyFlat T⟩

end FixedPointsFiniteEtale

section Morphisms

variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B]

/-- A surjection of étale algebras has kernel generated by an idempotent. -/
lemma exists_isIdempotentElem_ker_eq [Algebra.Etale R A] [Algebra.Etale R B] (g : A →ₐ[R] B)
    (hg : Function.Surjective g) :
    ∃ e : A, IsIdempotentElem e ∧ RingHom.ker g = Ideal.span {e} := by
  let _ := g.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.FormallyEtale A B := .of_restrictScalars (R := R)
  obtain ⟨e, he, hfe⟩ := (Ideal.isIdempotentElem_iff_of_fg _
    (Algebra.FinitePresentation.ker_fG_of_surjective g hg)).mp
      ((Algebra.FormallyEtale.iff_of_surjective (R := A) (S := B) hg).mp inferInstance)
  exact ⟨e, he, hfe⟩

/-- The tensor product of two finite étale algebras over a finite étale algebra is finite
étale. -/
lemma finite_etale_tensorProduct {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
    [Algebra R B] [Algebra R A] [Algebra R C] [Algebra B A] [IsScalarTower R B A] [Algebra B C]
    [IsScalarTower R B C] [Algebra.Etale R B] [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R C] [Algebra.Etale R C] :
    Module.Finite R (A ⊗[B] C) ∧ Algebra.Etale R (A ⊗[B] C) := by
  have : Algebra.Etale B C := .of_restrictScalars R B C
  have : Module.Finite B C := .of_restrictScalars_finite R B C
  exact ⟨.trans A _, .comp R A _⟩

/-- If `b ⊗ 1 = 1 ⊗ b` in `B ⊗[A] B` for all `b`, then a finite flat `A`-algebra `B` is a
quotient of `A`. -/
lemma surjective_algebraMap_of_tmul_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Flat A B] (h : ∀ b : B, b ⊗ₜ[A] (1 : B) = 1 ⊗ₜ b) :
    Function.Surjective (algebraMap A B) := by
  have key : ∀ x : B ⊗[A] B, x = LinearMap.mul' A B x ⊗ₜ 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [LinearMap.mul'_apply, ← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul,
        ← h b, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add x y hx hy => rw [map_add, TensorProduct.add_tmul, ← hx, ← hy]
  have hbij : Function.Bijective (LinearMap.mul' A B) := by
    refine ⟨fun x y hxy ↦ ?_, fun b ↦ ⟨b ⊗ₜ 1, by simp⟩⟩
    rw [key x, key y, hxy]
  exact ((Module.Flat.tfae_algebraMap_surjective A B).out 2 1).mp hbij

end Morphisms

section Connected

variable {R : Type*} [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B] [Algebra.Etale R B]
  (Ω : Type*) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

omit [Module.Finite R B] in
/-- Over a connected base, a surjection `g : A → B` of finite étale algebras through which every
geometric point of `A` factors is an isomorphism. -/
lemma injective_of_forall_exists_comp (g : A →ₐ[R] B) (hg : Function.Surjective g)
    (h : ∀ x : A →ₐ[R] Ω, ∃ y : B →ₐ[R] Ω, y.comp g = x) : Function.Injective g := by
  obtain ⟨e, he, hker⟩ := exists_isIdempotentElem_ker_eq g hg
  by_cases he0 : e = 0
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ RingHom.ker g := ha
    rwa [hker, he0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
  have := nontrivial_quotient_one_sub he he0
  obtain ⟨_, _⟩ := finite_etale_quotient_one_sub (R := R) he
  obtain ⟨z⟩ := nonempty_algHom_of_nontrivial (R := R) (A := A ⧸ Ideal.span {1 - e}) Ω
  obtain ⟨y, hy⟩ := h (z.comp (Ideal.Quotient.mkₐ R _))
  have h1 : g e = 0 := by
    change e ∈ RingHom.ker g
    rw [hker]
    exact Ideal.mem_span_singleton_self e
  have h2 : Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩
  have := congr($hy e)
  simp only [AlgHom.comp_apply, h1, map_zero, Ideal.Quotient.mkₐ_eq_mk, h2, map_one] at this
  exact absurd this zero_ne_one

omit [PreconnectedSpace (PrimeSpectrum R)] [Module.Finite R B] in
/-- A map `φ : B → A` of finite étale algebras which is left cancellable against maps out of
`B × B` (in particular, a monomorphism of finite étale algebras) is surjective on spectra. -/
lemma comap_surjective_of_cancel (φ : B →ₐ[R] A)
    (h : ∀ u₁ u₂ : (Fin 2 → B) →ₐ[R] B, φ.comp u₁ = φ.comp u₂ → u₁ = u₂) :
    Function.Surjective (PrimeSpectrum.comap (φ : B →+* A)) := by
  let _ := φ.toAlgebra
  have : IsScalarTower R B A := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.Etale B A := .of_restrictScalars R B A
  have : Module.Finite B A := .of_restrictScalars_finite R B A
  have : Module.FinitePresentation B A := finitePresentation_of_finite_etale
  obtain ⟨e, he, hZ⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ((Module.isLocallyConstant_rankAtStalk (R := B) (M := A)).isClopen_fiber 0)
  have hφe : φ e = 0 := by
    apply (he.map φ).eq_zero_of_isNilpotent
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    have hpos := (PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap (R := B) (S := A)
      (PrimeSpectrum.comap (algebraMap B A) ⟨P, hP⟩)).mpr ⟨_, rfl⟩
    have : PrimeSpectrum.comap (algebraMap B A) ⟨P, hP⟩ ∉
        (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) := by
      rw [← hZ]
      simp only [Set.mem_ofPred_eq]
      omega
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_not] at this
    exact this
  let u₂ : (Fin 2 → B) →ₐ[R] B :=
    { toFun := fun f ↦ (1 - e) * f 0 + e * f 1
      map_one' := by simp
      map_mul' := fun f g ↦ by
        simp only [Pi.mul_apply]
        linear_combination (f 0 * g 1 + f 1 * g 0 - f 0 * g 0 - f 1 * g 1) * he.eq
      map_zero' := by simp
      map_add' := fun f g ↦ by simp only [Pi.add_apply]; ring
      commutes' := fun r ↦ by simp only [Pi.algebraMap_apply]; ring }
  have hu := h (Pi.evalAlgHom R (fun _ ↦ B) 0) u₂ (by
    ext f
    simp [u₂, hφe])
  have he0 : e = 0 := by
    have := congr($hu (Pi.single 1 1))
    simpa [u₂] using this.symm
  change Function.Surjective (PrimeSpectrum.comap (algebraMap B A))
  rw [← PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective (R := B) (S := A)]
  intro p
  by_contra hp
  have : p ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) := by
    rw [← hZ]
    simp only [Set.mem_ofPred_eq]
    omega
  simp [he0] at this

/-- V.3.7 (affine case): over a connected base, a map of finite étale algebras inducing a
bijection on geometric points over one geometric point is an isomorphism. -/
theorem bijective_of_bijective_comp (φ : B →ₐ[R] A)
    (h : Function.Bijective fun x : A →ₐ[R] Ω ↦ x.comp φ) : Function.Bijective φ := by
  let _ := φ.toAlgebra
  have : IsScalarTower R B A := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.Etale B A := .of_restrictScalars R B A
  have : Module.Finite B A := .of_restrictScalars_finite R B A
  obtain ⟨_, _⟩ := finite_etale_tensorProduct (R := R) (B := B) (A := A) (C := A)
  let μ : A ⊗[B] A →ₐ[R] A := (Algebra.TensorProduct.lmul' B).restrictScalars R
  have hμ : Function.Surjective μ := fun a ↦ ⟨a ⊗ₜ 1, by simp [μ]⟩
  have hμinj : Function.Injective μ := by
    refine injective_of_forall_exists_comp Ω μ hμ fun z ↦ ?_
    let x₁ : A →ₐ[R] Ω := z.comp Algebra.TensorProduct.includeLeft
    let x₂ : A →ₐ[R] Ω := z.comp (Algebra.TensorProduct.includeRight.restrictScalars R)
    have h12 : x₁ = x₂ := h.1 (by
      ext b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply, x₁, x₂]
      congr 1
      rw [show φ b = algebraMap B A b from rfl, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul])
    refine ⟨x₁, ?_⟩
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' =>
      have e1 : z (a ⊗ₜ[B] a') = x₁ a * x₂ a' := by
        simp [x₁, x₂, ← map_mul]
      rw [e1, ← h12]
      simp [μ, x₁, ← map_mul]
    | add t t' ht ht' => simp only [map_add, ht, ht']
  have hbij : Function.Bijective (LinearMap.mul' B A) := ⟨hμinj, hμ⟩
  have hsurj : Function.Surjective φ :=
    ((Module.Flat.tfae_algebraMap_surjective B A).out 2 1).mp hbij
  exact ⟨injective_of_forall_exists_comp Ω φ hsurj fun x ↦ h.2 x, hsurj⟩

end Connected

end SGA.SGA1.ExposeV
