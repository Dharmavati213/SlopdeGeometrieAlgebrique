/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeII.Differentials
import SGA.SGA1.ExposeII.Jacobian

/-!
# SGA 1, Exposé II, §4 (4.9–4.11): étale coordinates adapted to a smooth subscheme

Let `X` be smooth over `S` at `x`, `Y ⊆ X` defined by `𝒥` and `x ∈ Y`. In the local situation
`P = 𝒪_{X,x}` (local, essentially of finite type and formally smooth over `R`), `J = 𝒥_x`, a
family `g = (g₁,…,gₚ, h₁,…,h_q)` of elements of `P` defines `R[t₁,…,tₙ] → P`, and "`g` is étale
at `x`" means that `P` is formally étale over `R[t₁,…,tₙ]`; "`Y` is the inverse image of
`t₁ = ⋯ = tₚ = 0`" means that `g₁,…,gₚ` generate `J`. We prove:

* II.4.9, (i) ⇔ (iii): `g` is étale at `x` with `Y = g⁻¹(Y')` iff `g₁,…,gₚ` generate `J` and the
  `dgᵢ(x)` form a basis of `Ω¹_{X/S}(x)`;
* II.4.11, (i) ⇔ (iv): generators `g₁,…,gₚ` of `J` with `dgᵢ(x)` linearly independent can be
  completed to étale coordinates `(g, h)`;
* II.4.10, (i) ⇔ (ii) ⇔ (iii): `Y` is smooth at `x` iff there are étale coordinates in which
  `Y = g⁻¹(Y')` iff `J` has generators with linearly independent differentials at `x`;
* II.4.17, (i) ⇔ (iv): along a section, smoothness is the existence of étale coordinates
  vanishing on the section.

The statements are local (at the local ring of `x`), as the proofs of SGA are.
-/

universe u

open Algebra KaehlerDifferential TensorProduct IsLocalRing

namespace SGA.SGA1.ExposeII

/-- Completing a linearly independent family to a basis with vectors taken from a spanning
family. -/
private lemma exists_sumElim_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι α : Type*} (v : ι → V) (hv : LinearIndependent K v) (w : α → V)
    (hw : Submodule.span K (Set.range w) = ⊤) :
    ∃ (q : ℕ) (a : Fin q → α), LinearIndependent K (Sum.elim v (w ∘ a)) ∧
      Submodule.span K (Set.range (Sum.elim v (w ∘ a))) = ⊤ := by
  set W := Submodule.span K (Set.range v)
  obtain ⟨κ, a', -, hsp, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ w)
  have htop : Submodule.span K (Set.range (W.mkQ ∘ w)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, hw, Submodule.map_top, Submodule.range_mkQ]
  rw [htop] at hsp
  have : Finite κ := Module.Finite.finite_basis (Module.Basis.mk hli hsp.ge)
  let e := Finite.equivFin κ
  refine ⟨Nat.card κ, a' ∘ e.symm, ?_, ?_⟩
  · have hv' : LinearIndependent K (fun i ↦ (⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hv
    exact hv'.sumElim_of_quotient (w ∘ a' ∘ e.symm) (hli.comp e.symm e.symm.injective)
  · set U := Submodule.span K (Set.range (Sum.elim v (w ∘ a' ∘ e.symm)))
    have hWU : W ≤ U := Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨Sum.inl i, hi⟩
    have hmap : Submodule.map W.mkQ U = ⊤ := by
      rw [_root_.eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨w (a' j), Submodule.subset_span ⟨Sum.inr (e j), by simp⟩, rfl⟩
    rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hWU] at hmap
    exact hmap

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P] [IsLocalRing P]
  [FormallySmooth R P] [EssFiniteType R P]

/-- The fibre version of II.4.8 for a family `Sum.elim g h`. -/
private lemma formallyEtale_sumElim_iff {p q : ℕ} (g : Fin p → P) (h : Fin q → P) :
    (MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom.FormallyEtale ↔
      LinearIndependent (ResidueField P) (Sum.elim
        (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i))
        (fun j ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (h j))) ∧
      Submodule.span (ResidueField P) (Set.range (Sum.elim
        (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i))
        (fun j ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (h j)))) = ⊤ := by
  algebraize [(MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom]
  have : IsScalarTower R (MvPolynomial (Fin p ⊕ Fin q) R) P :=
    .of_algHom (MvPolynomial.aeval (Sum.elim g h))
  have hfun : (fun i ↦ (1 : ResidueField P) ⊗ₜ[P]
      D R P (algebraMap (MvPolynomial (Fin p ⊕ Fin q) R) P (.X i))) =
      Sum.elim (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i))
        (fun j ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (h j)) := by
    ext (i | j) <;> simp [RingHom.algebraMap_toAlgebra]
  rw [← hfun]
  exact formallyEtale_mvPolynomial_iff_residueField (R := R) (B := P) (ι := Fin p ⊕ Fin q)

/-- II.4.9, (i) ⇔ (iii), local form: `g = (g₁,…,gₚ,h₁,…,h_q)` is étale at `x` and `Y` is the
inverse image of `t₁ = ⋯ = tₚ = 0` iff the `gᵢ` generate `J` and the differentials of
`g₁,…,gₚ,h₁,…,h_q` at `x` form a basis of `Ω¹_{X/S}(x)`. -/
theorem formallyEtale_and_span_iff {p q : ℕ} (J : Ideal P) (g : Fin p → P) (h : Fin q → P) :
    (Ideal.span (Set.range g) = J ∧
      (MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom.FormallyEtale) ↔
      Ideal.span (Set.range g) = J ∧
        LinearIndependent (ResidueField P) (Sum.elim
          (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i))
          (fun j ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (h j))) ∧
        Submodule.span (ResidueField P) (Set.range (Sum.elim
          (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i))
          (fun j ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (h j)))) = ⊤ := by
  rw [formallyEtale_sumElim_iff]

/-- II.4.11, (i) ⇔ (iv), local form: elements `g₁,…,gₚ` of `P = 𝒪_{X,x}` (with `X` smooth over
`S` at `x`) have linearly independent differentials at `x` iff they can be completed by
`h₁,…,h_q` to a family `(g, h) : X → S[t₁,…,tₙ]` which is étale at `x`. -/
theorem linearIndependent_iff_exists_formallyEtale {p : ℕ} (g : Fin p → P) :
    LinearIndependent (ResidueField P) (fun i ↦ (1 : ResidueField P) ⊗ₜ[P] D R P (g i)) ↔
      ∃ (q : ℕ) (h : Fin q → P),
        (MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom.FormallyEtale := by
  constructor
  · intro hli
    have hw : Submodule.span (ResidueField P)
        (Set.range fun a : P ↦ (1 : ResidueField P) ⊗ₜ[P] D R P a) = ⊤ := by
      have := Submodule.baseChange_span (R := P) (A := ResidueField P) (Set.range (D R P))
      rw [span_range_derivation, Submodule.baseChange_top, ← Set.range_comp] at this
      exact this.symm
    obtain ⟨q, a, hli', hsp⟩ := exists_sumElim_basis _ hli _ hw
    exact ⟨q, a, (formallyEtale_sumElim_iff g a).mpr ⟨hli', hsp⟩⟩
  · rintro ⟨q, h, hgh⟩
    exact ((formallyEtale_sumElim_iff g h).mp hgh).1.comp Sum.inl Sum.inl_injective

variable [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]

/-- II.4.10, (i) ⇔ (ii) ⇔ (iii), local form: for `J ⊆ 𝔪_P` finitely generated, `Y` is smooth
over `S` at `x` iff there are étale coordinates `(g₁,…,gₚ,h₁,…,h_q)` at `x` with `Y` the inverse
image of `t₁ = ⋯ = tₚ = 0`. (The equivalence with (iii) is
`formallySmooth_quotient_iff_exists_linearIndependent`.) -/
theorem formallySmooth_quotient_iff_exists_formallyEtale (J : Ideal P)
    (hJ : J ≤ maximalIdeal P) (hJfg : J.FG) :
    FormallySmooth R (P ⧸ J) ↔ ∃ (p q : ℕ) (g : Fin p → P) (h : Fin q → P),
      Ideal.span (Set.range g) = J ∧
        (MvPolynomial.aeval (R := R) (Sum.elim g h)).toRingHom.FormallyEtale := by
  rw [formallySmooth_quotient_iff_exists_linearIndependent J hJ hJfg]
  constructor
  · rintro ⟨p, g, hgJ, hli⟩
    obtain ⟨q, h, hgh⟩ := (linearIndependent_iff_exists_formallyEtale g).mp hli
    exact ⟨p, q, g, h, hgJ, hgh⟩
  · rintro ⟨p, q, g, h, hgJ, hgh⟩
    exact ⟨p, g, hgJ, (linearIndependent_iff_exists_formallyEtale g).mpr ⟨q, h, hgh⟩⟩

omit [FormallySmooth R P] [Module.Free P Ω[P⁄R]] in
/-- II.4.17, (i) ⇔ (iv), local form: let `P = 𝒪_{X,x}` be local and essentially of finite type
over `R`, and `σ : P → R` an `R`-algebra retraction (a section of `X` over `Y = Spec R` through
`x`) whose ideal `ker σ` is finitely generated. Then `X` is smooth over `R` at `x` iff there are
étale coordinates `g : X → 𝔸ⁿ_R` at `x` vanishing on the section, i.e. transforming the section
into the zero section. (For "if", neither the section nor the vanishing is needed.) -/
theorem formallySmooth_iff_exists_formallyEtale_of_section (σ : P →ₐ[R] R)
    (hfg : (RingHom.ker σ).FG) :
    FormallySmooth R P ↔ ∃ (p q : ℕ) (g : Fin p ⊕ Fin q → P), (∀ i, σ (g i) = 0) ∧
      (MvPolynomial.aeval (R := R) g).toRingHom.FormallyEtale := by
  constructor
  · intro
    have hsurj : Function.Surjective σ := fun r ↦ ⟨algebraMap R P r, σ.commutes r⟩
    have hY : FormallySmooth R (P ⧸ RingHom.ker σ) :=
      .of_equiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm
    have hJ : RingHom.ker σ ≤ maximalIdeal P := by
      refine IsLocalRing.le_maximalIdeal fun h ↦ ?_
      have h1 : (1 : P) ∈ RingHom.ker σ := h ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      have : Nontrivial R := (algebraMap R P).domain_nontrivial
      exact one_ne_zero h1
    have : Module.Free P Ω[P⁄R] := free_kaehler_of_formallySmooth R P
    obtain ⟨p, q, g, h, hgJ, hgh⟩ :=
      (formallySmooth_quotient_iff_exists_formallyEtale _ hJ hfg).mp hY
    -- replace `h` by `h - σ(h)`, which vanishes on the section and has the same differential
    let h' : Fin q → P := fun j ↦ h j - algebraMap R P (σ (h j))
    have hDh (j : Fin q) : D R P (h' j) = D R P (h j) := by
      simp [h', map_sub, Derivation.map_algebraMap]
    have hgh' := ((formallyEtale_and_span_iff _ g h).mp ⟨hgJ, hgh⟩)
    obtain ⟨-, hgh''⟩ := (formallyEtale_and_span_iff (R := R) _ g h').mpr (by
      simp only [hDh]
      exact hgh')
    refine ⟨p, q, Sum.elim g h', fun i ↦ ?_, hgh''⟩
    rcases i with i | j
    · have : g i ∈ RingHom.ker σ := hgJ ▸ Ideal.subset_span ⟨i, rfl⟩
      exact this
    · simp [h']
  · rintro ⟨p, q, g, -, hg⟩
    algebraize [(MvPolynomial.aeval (R := R) g).toRingHom]
    have : IsScalarTower R (MvPolynomial (Fin p ⊕ Fin q) R) P := .of_algHom (MvPolynomial.aeval g)
    exact .comp R (MvPolynomial (Fin p ⊕ Fin q) R) P

end SGA.SGA1.ExposeII
