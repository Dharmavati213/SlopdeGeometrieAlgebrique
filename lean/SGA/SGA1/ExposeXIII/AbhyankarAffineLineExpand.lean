/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Flat.TorsionFree
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeV.GaloisAxioms
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP

/-!
# XIII.2.13, case A: connected coverings of `𝔸¹` stay connected under `x ↦ xᵐ`

For Abhyankar's lemma at `∞` (`AbhyankarLemmaAtInfinityStatement`) one pulls a covering of the
affine line back along `𝔸¹ → 𝔸¹`, `z ↦ zᵐ = x`. This file proves that the pullback of a connected
étale covering stays connected, for every `m ≥ 1` and over every field `k`
(`AffineLinePGroups.isConnected_bcRingHom_expand`): base change along `Polynomial.expand k m`
sends connected finite étale `k[X]`-algebras to connected ones.

The proof, for a prime `q`: a connected finite étale `k[X]`-algebra `A` is a normal domain (I.10.1,
I.9.5); with `L = Frac A`, `X` is not a `q`-th power in `L`, since a `q`-th root `g` would lie in
`A`, hence in `X A` (the ideal `X A` is radical, `A/XA` being étale over `k`), and then `X` would
be a unit of `A`. So `Tᵠ - X` is irreducible over `L`, and the base change
`k[Z] ⊗_{k[X]} A`, `X ↦ Zᵠ`, embeds into the field `L[T]/(Tᵠ - X)` (it is spanned over `A` by
`1, Z, …, Z^{q-1}`, which go to an `L`-basis). The general case follows by induction on the prime
factors of `m`, base change along a composite being the composite of the base changes
(`AffineLinePGroups.bcRingHomCompIso`).

`AffineLinePGroups.bcRingHom f` is base change of finite étale algebras along a ring
homomorphism `f` (with `f.toAlgebra`), which avoids clashes of algebra structures when, as here,
source and target are the same ring.
-/

universe u

open CategoryTheory PreGaloisCategory Polynomial CommAlgCat

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

section BaseChange

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Base change of finite étale algebras along a ring homomorphism `f : R → S`, i.e.
`FiniteEtale.baseChange` for the algebra structure `f.toAlgebra`. -/
noncomputable abbrev bcRingHom (f : R →+* S) : FiniteEtale.{u} R ⥤ FiniteEtale.{u} S :=
  letI := f.toAlgebra
  FiniteEtale.baseChange.{u} R S

/-- Base change along a composite is the composite of the base changes. -/
noncomputable def bcRingHomCompIso (f : R →+* S) (g : S →+* T) :
    bcRingHom f ⋙ bcRingHom g ≅ bcRingHom (g.comp f) :=
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  ExposeI.finiteEtaleBaseChangeCompIso (A := R) S T

end BaseChange

section Expand

variable (k : Type u) [Field k]

/-- Every polynomial is a combination of `1, X, …, X^{q-1}` with coefficients in `k[Xᵠ]`. -/
lemma exists_eq_sum_X_pow_mul_expand {q : ℕ} (hq : 0 < q) (s : k[X]) :
    ∃ h : Fin q → k[X], s = ∑ i : Fin q, X ^ (i : ℕ) * expand k q (h i) := by
  induction s using Polynomial.induction_on' with
  | add s t hs ht =>
    obtain ⟨h₁, rfl⟩ := hs
    obtain ⟨h₂, rfl⟩ := ht
    exact ⟨h₁ + h₂, by simp [mul_add, Finset.sum_add_distrib]⟩
  | monomial n c =>
    classical
    let i₀ : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
    refine ⟨fun i ↦ if i = i₀ then monomial (n / q) c else 0, ?_⟩
    rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ by simp [hi]) (by simp)]
    simp only [↓reduceIte, expand_monomial, X_pow_mul_monomial]
    rw [show (i₀ : ℕ) = n % q from rfl, Nat.div_add_mod']

variable {k}

/-- A connected finite étale `k[X]`-algebra is a domain whose structure map is injective. -/
lemma isDomain_and_injective_of_isConnected (A : FiniteEtale.{u} k[X])
    (h : IsConnected (Opposite.op A)) :
    IsDomain A ∧ Function.Injective (algebraMap k[X] A) := by
  have : ConnectedSpace (PrimeSpectrum A) :=
    (ExposeV.isConnected_op_iff_connectedSpace k[X] A).mp h
  have : IsDomain A := isDomain_of_etale_of_connectedSpace (R := k[X])
  refine ⟨this, (injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_⟩
  rw [Algebra.algebraMap_eq_smul_one] at hr
  rcases smul_eq_zero.mp hr with h | h
  · exact h
  · exact absurd h one_ne_zero

/-- In a connected finite étale `k[X]`-algebra `A`, `X` is not a `d`-th power of an element of
`Frac A` for `d ≥ 2`: such a root would lie in `X A`, which is a radical ideal since `A/XA` is
étale over `k`, and `X` would be a unit. -/
lemma pow_ne_algebraMap_X (A : FiniteEtale.{u} k[X]) (h : IsConnected (Opposite.op A)) {d : ℕ}
    (hd : 2 ≤ d) (b : FractionRing A) : b ^ d ≠ algebraMap k[X] (FractionRing A) X := by
  obtain ⟨_, hinj⟩ := isDomain_and_injective_of_isConnected A h
  have : IsIntegrallyClosed A := ExposeI.isIntegrallyClosed_of_etale (A := k[X])
  intro hb
  -- `b` is integral over `A`, hence in `A`
  have hint : IsIntegral A b := by
    refine ⟨X ^ d - C (algebraMap k[X] A X), monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [hb, ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ha : a ^ d = algebraMap k[X] A X :=
    IsFractionRing.injective A (FractionRing A) (by
      rw [map_pow, hb, IsScalarTower.algebraMap_apply k[X] A (FractionRing A)])
  -- `X A` is radical
  have hmax : (Ideal.span {(X : k[X])}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
  have hrad := Algebra.FormallyUnramified.isRadical_map_isMaximal k[X] A
    (Ideal.span {(X : k[X])})
  rw [Ideal.map_span, Set.image_singleton] at hrad
  have haX : a ∈ Ideal.span {algebraMap k[X] A X} :=
    hrad ⟨d, by rw [ha]; exact Ideal.mem_span_singleton_self _⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp haX
  -- then `X` is a unit of `A`
  have hX0 : algebraMap k[X] A X ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap k[X] A)]
    exact fun h ↦ X_ne_zero (hinj h)
  have hunit : IsUnit (algebraMap k[X] A X) := by
    set x := algebraMap k[X] A X
    have hcx : c ^ d * x ^ d = x := by rw [← mul_pow, hc, ha]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    have h1 : x * (c ^ (e + 2) * x ^ (e + 1) - 1) = 0 := by linear_combination hcx
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact absurd h1 hX0
    exact IsUnit.of_mul_eq_one (c ^ (e + 2) * x ^ e) (by linear_combination h1)
  -- but `X` lies in a maximal ideal of `A` over `(X)` (lying over)
  obtain ⟨Q, hQ, hQX⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A)
    (Ideal.span {(X : k[X])}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le)
  have : algebraMap k[X] A X ∈ Q := by
    rw [← Ideal.mem_comap, hQX]
    exact Ideal.mem_span_singleton_self _
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q this hunit)

/-- The core of `isConnected_bcRingHom_expand_of_irreducible`, for any `k[X]`-algebra `S` with an
element `z` such that `1, z, …, z^{q-1}` span `S` over `k[X]`, an irreducible polynomial `P` of
degree `q` over `L = Frac A` and a `k[X]`-algebra map `S → L[T]/(P)`, `z ↦ T`: then
`S ⊗_{k[X]} A` is a domain. -/
lemma isDomain_tensorProduct_of_irreducible {S : Type u} [CommRing S] [Algebra k[X] S] {q : ℕ}
    (z : S) (hspanS : ∀ s : S, ∃ h : Fin q → k[X],
      s = ∑ i : Fin q, z ^ (i : ℕ) * algebraMap k[X] S (h i))
    (A : FiniteEtale.{u} k[X]) [IsDomain A] {P : (FractionRing A)[X]} (hirr : Irreducible P)
    (hdeg : P.natDegree = q) (fZ : S →ₐ[k[X]] AdjoinRoot P) (hfZ : fZ z = AdjoinRoot.root P) :
    IsDomain (TensorProduct k[X] S A) := by
  have : Fact (Irreducible P) := ⟨hirr⟩
  let gA : A →ₐ[k[X]] AdjoinRoot P :=
    (IsScalarTower.toAlgHom k[X] (FractionRing A) (AdjoinRoot P)).comp
      (IsScalarTower.toAlgHom k[X] A (FractionRing A))
  let ρ := Algebra.TensorProduct.lift fZ gA fun _ _ ↦ Commute.all _ _
  -- the elements `zⁱ ⊗ 1` span over `A`
  have hspan : ∀ b : TensorProduct k[X] S A, ∃ a : Fin q → A,
      b = ∑ i : Fin q, (z ^ (i : ℕ)) ⊗ₜ[k[X]] a i := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s a =>
      obtain ⟨h', hs⟩ := hspanS s
      refine ⟨fun i ↦ algebraMap k[X] A (h' i) * a, ?_⟩
      rw [hs, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change (z ^ (i : ℕ) * algebraMap k[X] S (h' i)) ⊗ₜ[k[X]] a =
        (z ^ (i : ℕ)) ⊗ₜ[k[X]] (algebraMap k[X] A (h' i) * a)
      rw [mul_comm (z ^ (i : ℕ)), ← Algebra.smul_def (h' i) (z ^ (i : ℕ)),
        ← Algebra.smul_def (h' i) a, TensorProduct.smul_tmul]
    | add b c hb hc =>
      obtain ⟨a₁, rfl⟩ := hb
      obtain ⟨a₂, rfl⟩ := hc
      exact ⟨a₁ + a₂, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  -- `ρ` is injective
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have hdim : pb.dim = q := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨a, rfl⟩ := hspan b
    have hli := pb.basis.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have hsum : ∑ j : Fin pb.dim,
        algebraMap A (FractionRing A) (a (Fin.cast hdim j)) • pb.basis j = 0 := by
      rw [map_sum] at hb
      rw [← hb]
      refine Fintype.sum_equiv (finCongr hdim) _ _ fun j ↦ ?_
      rw [PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, Algebra.smul_def, mul_comm]
      change _ = fZ (z ^ (j : ℕ)) * gA (a (Fin.cast hdim j))
      rw [map_pow, hfZ]
      rfl
    have key : ∀ i : Fin q, a i = 0 := fun i ↦ IsFractionRing.injective A (FractionRing A) (by
      have := hli _ hsum (Fin.cast hdim.symm i)
      simpa using this)
    simp [funext key]
  exact hρinj.isDomain ρ.toRingHom

/-- **Connectedness under `x ↦ xᵠ`, given irreducibility**: if `A` is a connected finite étale
`k[X]`-algebra and `Tᵠ - X` is irreducible over `Frac A`, the base change of `A` along
`expand k q` (`X ↦ Xᵠ`) is connected. -/
lemma isConnected_bcRingHom_expand_of_irreducible {q : ℕ} (hq : 0 < q)
    (A : FiniteEtale.{u} k[X]) (h : IsConnected (Opposite.op A))
    (hirr : Irreducible (X ^ q - C (algebraMap k[X] (FractionRing A) X))) :
    IsConnected ((bcRingHom (expand k q).toRingHom).op.obj (Opposite.op A)) := by
  obtain ⟨_, -⟩ := isDomain_and_injective_of_isConnected A h
  change IsConnected (Opposite.op ((bcRingHom (expand k q).toRingHom).obj A))
  rw [ExposeV.isConnected_op_iff]
  let : Algebra k[X] k[X] := (expand k q).toRingHom.toAlgebra
  let P : (FractionRing A)[X] := X ^ q - C (algebraMap k[X] (FractionRing A) X)
  have hroot : AdjoinRoot.root P ^ q = algebraMap k[X] (AdjoinRoot P) X := by
    have := AdjoinRoot.eval₂_root P
    simp only [P, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [this, IsScalarTower.algebraMap_apply k[X] (FractionRing A) (AdjoinRoot P)]
    rfl
  let fZ : k[X] →ₐ[k[X]] AdjoinRoot P :=
    { eval₂RingHom ((algebraMap k[X] (AdjoinRoot P)).comp C) (AdjoinRoot.root P) with
      commutes' := fun r ↦ by
        change eval₂ ((algebraMap k[X] (AdjoinRoot P)).comp C) (AdjoinRoot.root P)
          (expand k q r) = algebraMap k[X] (AdjoinRoot P) r
        induction r using Polynomial.induction_on with
        | C c => simp
        | add r s hr hs => simp only [map_add, eval₂_add, hr, hs]
        | monomial n c _ =>
          simp only [map_mul, map_pow, expand_C, expand_X, eval₂_mul, eval₂_pow, eval₂_C,
            eval₂_X, hroot, RingHom.comp_apply] }
  have hdom := isDomain_tensorProduct_of_irreducible (S := k[X]) (q := q) X
    (fun s ↦ exists_eq_sum_X_pow_mul_expand k hq s) A hirr natDegree_X_pow_sub_C fZ
    (by simp [fZ, P])
  have hdom' : IsDomain ((bcRingHom (expand k q).toRingHom).obj A).obj := hdom
  exact ⟨hdom'.toNontrivial, fun e he ↦ IsIdempotentElem.iff_eq_zero_or_one.mp he⟩

/-- **Connected coverings of `𝔸¹` stay connected under `x ↦ xᵐ`**: for every `m ≥ 1`, the base
change of a connected finite étale `k[X]`-algebra along `expand k m` (`X ↦ Xᵐ`) is connected.
There is no hypothesis on `k` or on `m` (for `m` a power of the characteristic this is the
pullback along a purely inseparable morphism). -/
theorem isConnected_bcRingHom_expand {m : ℕ} (hm : 0 < m) (A : FiniteEtale.{u} k[X])
    (h : IsConnected (Opposite.op A)) :
    IsConnected ((bcRingHom (expand k m).toRingHom).op.obj (Opposite.op A)) := by
  induction m using Nat.recOnMul generalizing A with
  | zero => omega
  | one =>
    have := (isDomain_and_injective_of_isConnected A h).1
    refine isConnected_bcRingHom_expand_of_irreducible one_pos A h ?_
    rw [pow_one]
    exact irreducible_X_sub_C _
  | prime q hq =>
    have := (isDomain_and_injective_of_isConnected A h).1
    exact isConnected_bcRingHom_expand_of_irreducible hq.pos A h
      (X_pow_sub_C_irreducible_of_prime hq fun b ↦ pow_ne_algebraMap_X A h hq.two_le b)
  | mul a b iha ihb =>
    have ha : 0 < a := Nat.pos_of_mul_pos_right hm
    have hb : 0 < b := Nat.pos_of_mul_pos_left hm
    have h₁ : IsConnected (Opposite.op ((bcRingHom (expand k a).toRingHom).obj A)) := iha ha A h
    have h₂ : IsConnected (Opposite.op ((bcRingHom (expand k b).toRingHom).obj
        ((bcRingHom (expand k a).toRingHom).obj A))) := ihb hb _ h₁
    have hcomp : (expand k b).toRingHom.comp (expand k a).toRingHom =
        (expand k (a * b)).toRingHom := by
      refine RingHom.ext fun s ↦ ?_
      change expand k b (expand k a s) = expand k (a * b) s
      rw [expand_expand, mul_comm]
    have : IsConnected (Opposite.op
        ((bcRingHom (expand k a).toRingHom ⋙ bcRingHom (expand k b).toRingHom).obj A)) := h₂
    let e := (bcRingHomCompIso (expand k a).toRingHom (expand k b).toRingHom).app A
    rw [hcomp] at e
    exact ExposeV.isConnected_of_iso
      (X := Opposite.op ((bcRingHom (expand k (a * b)).toRingHom).obj A)) (Iso.op e.symm)

end Expand

end SGA.SGA1.ExposeXIII.AffineLinePGroups
