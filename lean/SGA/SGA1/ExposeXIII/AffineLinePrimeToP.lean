/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeV.FiniteEtaleGalois
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeV.GaloisEquivalence
import SGA.SGA1.ExposeXI.TameGaloisCovering
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeXIII.ProLQuotient

/-!
# XIII.2.12 for the affine line: `π₁^{p'}(𝔸¹_k) = 1`

For `k` algebraically closed of characteristic `p`, the maximal prime-to-`p` quotient of the
fundamental group of `𝔸¹_k` is trivial (`proLKernel_etaleFundamentalGroup_eq_top`, which proves
`AffineLinePrimeToPTrivialStatement` of `SGA.SGA1.ExposeXIII.SchemeFundamentalGroup`). SGA
obtains this case `g = 0`, `n = 1` of XIII.2.12 from Riemann's existence theorem; here it is
proved algebraically. An open normal subgroup `N` of `π₁` of index prime to `p` is the stabilizer
of the points of the fibre of a connected Galois covering `Spec A → 𝔸¹_k`, with
`|Aut A| = [A : k[T]] = [π₁ : N]` (`exists_isGalois_card_fiber_eq_index`); `A` is a domain
(`isDomain_of_etale_of_connectedSpace`), so the covering is trivial by the lattice method
(`SGA.SGA1.ExposeXI.finrank_eq_one_of_le_card`), and `N = π₁`.
-/

universe u

namespace SGA.SGA1.ExposeXIII

open CategoryTheory PreGaloisCategory AlgebraicGeometry Polynomial Module

section Galois

variable {C : Type*} [Category* C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u}) [FiberFunctor F]

/-- An open normal subgroup `N` of `Aut F` is the stabilizer of every point of the fibre of a
connected Galois object `X`; in particular `|F X| = [Aut F : N]`. -/
theorem exists_isGalois_card_fiber_eq_index (N : Subgroup (Aut F)) [hN : N.Normal]
    (ho : IsOpen (N : Set (Aut F))) :
    ∃ X : C, IsConnected X ∧ IsGalois X ∧ Nat.card (F.obj X) = N.index := by
  obtain ⟨X, x, hX, hx⟩ := exists_isConnected_stabilizer_eq F ⟨N, ho⟩
  have hstab : ∀ y : F.obj X, MulAction.stabilizer (Aut F) y = N := by
    intro y
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) x y
    ext g
    have h1 : g • σ • x = σ • x ↔ (σ⁻¹ * g * σ) • x = x := by
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
    rw [MulAction.mem_stabilizer_iff, h1, ← MulAction.mem_stabilizer_iff, hx]
    change σ⁻¹ * g * σ ∈ N ↔ g ∈ N
    constructor
    · intro h
      have := hN.conj_mem _ h σ
      simpa [mul_assoc] using this
    · intro h
      have := hN.conj_mem _ h σ⁻¹
      simpa [mul_assoc] using this
  have hgal : IsGalois X := by
    rw [isGalois_iff_pretransitive F X]
    refine ⟨fun y z ↦ ?_⟩
    obtain ⟨f, hf⟩ := exists_hom_of_stabilizer_le F y z (by rw [hstab, hstab])
    have : Nonempty (F.obj X) := ⟨x⟩
    have hsurj := surjective_of_nonempty_fiber_of_isConnected F f
    have : IsIso (F.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    have : IsIso f := isIso_of_reflects_iso f F
    exact ⟨asIso f, hf⟩
  refine ⟨X, hX, hgal, ?_⟩
  rw [← MulAction.index_stabilizer_of_transitive (Aut F) x, hstab x]

end Galois

section Algebra

/-- A finite étale algebra with connected spectrum over a noetherian normal domain is a domain:
`Spec B` is normal (I.9.5), hence irreducible, being connected and locally noetherian. -/
theorem isDomain_of_etale_of_connectedSpace {R B : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
    [ConnectedSpace (PrimeSpectrum B)] : IsDomain B := by
  have hR : ExposeI.IsNormalScheme (Spec (CommRingCat.of R)) := by
    intro x
    have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
    have hΓ : IsDomain Γ(Spec (CommRingCat.of R), ⊤) ∧
        IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) :=
      ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
        (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
        ⟨inferInstanceAs (IsDomain R), inferInstanceAs (IsIntegrallyClosed R)⟩
    obtain ⟨_, _⟩ := hΓ
    refine ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
      (ExposeI.stalkEquivLocalization hU x trivial).symm ⟨inferInstance, ?_⟩
    exact isIntegrallyClosed_of_isLocalization _
      (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : Etale f := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hB := ExposeI.isNormalScheme_of_etale f hR
  have : ConnectedSpace (Spec (CommRingCat.of B)) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum B))
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : IrreducibleSpace (Spec (CommRingCat.of B)) :=
    ExposeI.irreducibleSpace_of_isDomain_stalk fun y ↦ (hB y).1
  have : IsReduced (Spec (CommRingCat.of B)) := by
    have (y : Spec (CommRingCat.of B)) :
        _root_.IsReduced ((Spec (CommRingCat.of B)).presheaf.stalk y) := by
      have := (hB y).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := isIntegral_of_irreducibleSpace_of_isReduced (Spec (CommRingCat.of B))
  exact (affine_isIntegral_iff (CommRingCat.of B)).mp this

open CommAlgCat in
/-- The automorphisms of a finite étale covering `Spec A → Spec R` in `(FiniteEtale R)ᵒᵖ` are
the `R`-algebra automorphisms of `A`. -/
noncomputable def autOpEquivAlgEquiv {R : Type u} [CommRing R] (A : FiniteEtale.{u} R) :
    Aut (Opposite.op A) ≃ (A.obj ≃ₐ[R] A.obj) where
  toFun a := algEquivOfIso ((ObjectProperty.ι _).mapIso a.unop)
  invFun e := (FiniteEtale.isoMk e).op
  left_inv a := by
    ext
    rfl
  right_inv e := by
    ext
    rfl

end Algebra

section AffineLine

variable (k Ω : Type u) [Field k] [IsAlgClosed k] [Field Ω] [IsSepClosed Ω]

/-- An open normal subgroup of `π₁(𝔸¹_k)` of index prime to the characteristic is the whole
group: the corresponding connected Galois covering of `𝔸¹_k` is trivial
(`ExposeXI.finrank_eq_one_of_le_card`). -/
theorem eq_top_of_isOpen_of_index_ne_zero [Algebra k[X] Ω]
    (N : Subgroup (Aut (ExposeV.fiberFunctor k[X] Ω))) [N.Normal]
    (ho : IsOpen (N : Set (Aut (ExposeV.fiberFunctor k[X] Ω)))) (hk : (N.index : k) ≠ 0) :
    N = ⊤ := by
  obtain ⟨X, hc, hg, hcard⟩ :=
    exists_isGalois_card_fiber_eq_index (ExposeV.fiberFunctor k[X] Ω) N ho
  let A := X.unop
  have : ConnectedSpace (PrimeSpectrum A.obj) :=
    (ExposeV.isConnected_op_iff_connectedSpace k[X] A).mp hc
  have : IsDomain A.obj := isDomain_of_etale_of_connectedSpace (R := k[X])
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected (ExposeV.fiberFunctor k[X] Ω) X
  have hAut : Nat.card (A.obj ≃ₐ[k[X]] A.obj) = N.index := by
    rw [← Nat.card_congr (autOpEquivAlgEquiv A),
      Nat.card_congr (evaluationEquivOfIsGalois (ExposeV.fiberFunctor k[X] Ω) X x), hcard]
  have hN0 : N.index ≠ 0 := fun h ↦ hk (by rw [h, Nat.cast_zero])
  have : Finite (A.obj ≃ₐ[k[X]] A.obj) := Nat.finite_of_card_ne_zero (hAut ▸ hN0)
  have hrank : finrank k[X] A.obj = N.index := by
    have h := ExposeV.card_fiber_eq_rankAtStalk k[X] Ω A (Classical.arbitrary _)
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.symm.trans hcard
  have h1 := ExposeXI.finrank_eq_one_of_le_card (k := k) (A := A.obj) (by rw [hrank, hAut])
    (by rw [hrank]; exact hk)
  exact Subgroup.index_eq_one.mp (hrank ▸ h1)

/-- XIII.2.12 for `g = 0`, `n = 1` (the affine line), in terms of the fibre functor of finite
étale `k[T]`-algebras: the maximal prime-to-`p` quotient of `π₁(𝔸¹_k)` is trivial. -/
theorem proLKernel_aut_fiberFunctor_eq_top [Algebra k[X] Ω] (p : ℕ) [CharP k p] :
    proLKernel {ℓ | ℓ.Prime ∧ ℓ ≠ p} (Aut (ExposeV.fiberFunctor k[X] Ω)) = ⊤ := by
  refine eq_top_iff.mpr fun σ _ ↦ mem_proLKernel.mpr fun N hN ho hL ↦ ?_
  have hk : (N.index : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k p] at h
    rcases CharP.char_is_prime_or_zero k p with hp | rfl
    · exact (hL.2 p hp h).2 rfl
    · exact hL.1 (Nat.eq_zero_of_zero_dvd h)
  rw [eq_top_of_isOpen_of_index_ne_zero k Ω N ho hk]
  trivial

/-- XIII.2.12 for `g = 0`, `n = 1`: for `k` algebraically closed of characteristic `p`, the
maximal prime-to-`p` quotient of `π₁(𝔸¹_k, x)` is trivial, at every geometric point `x`. -/
theorem proLKernel_etaleFundamentalGroup_eq_top (p : ℕ) [CharP k p]
    (x : Spec (.of Ω) ⟶ Spec (.of k[X])) :
    proLKernel {ℓ | ℓ.Prime ∧ ℓ ≠ p} (ExposeV.etaleFundamentalGroup Ω x) = ⊤ := by
  let := ExposeV.algebraOfPoint (CommRingCat.of k[X]) Ω x
  let ψ := ExposeV.autContinuousMulEquiv (ExposeV.specEquivalence (CommRingCat.of k[X])).inverse
    (ExposeV.FEt.fiberSpecIso (CommRingCat.of k[X]) Ω x).symm
  have h : proLKernel {ℓ | ℓ.Prime ∧ ℓ ≠ p} (Aut (ExposeV.fiberFunctor k[X] Ω)) ≤
      (proLKernel {ℓ | ℓ.Prime ∧ ℓ ≠ p} (ExposeV.etaleFundamentalGroup Ω x)).comap
        ψ.toMonoidHom :=
    proLKernel_le_comap _ ψ.toMonoidHom ψ.continuous
  rw [proLKernel_aut_fiberFunctor_eq_top k Ω p, top_le_iff] at h
  refine eq_top_iff.mpr fun γ _ ↦ ?_
  have : ψ.symm γ ∈ (proLKernel {ℓ | ℓ.Prime ∧ ℓ ≠ p} (ExposeV.etaleFundamentalGroup Ω x)).comap
      ψ.toMonoidHom := by
    rw [h]
    trivial
  rw [Subgroup.mem_comap] at this
  convert this
  exact (ψ.apply_symm_apply γ).symm

end AffineLine

end SGA.SGA1.ExposeXIII
