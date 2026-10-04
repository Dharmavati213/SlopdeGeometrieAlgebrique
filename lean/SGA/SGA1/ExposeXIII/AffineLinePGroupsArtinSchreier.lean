/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup
import SGA.SGA1.ExposeXIII.AffineLinePGroups
import SGA.SGA1.ExposeXIII.AffineLinePGroupsPrincipal

/-!
# XIII.2.13: Artin–Schreier characters of `π₁`

Let `R` be a domain of characteristic `p` (with connected spectrum) and `R → Ω` a geometric point.
The Artin–Schreier covering `R[T]/(Tᵖ - T + a)` of XI.6.7 is a principal covering with group `ℤ/p`
(`SGA.SGA1.ExposeXIII.artinSchreierPrincipal`), so it defines (V.5.11) a continuous homomorphism
`χ_a : π₁(Spec R, a) → ℤ/p` (`AffineLinePGroups.artinSchreierChar`); since `ℤ/p` is commutative,
it does not depend on the choice of a point over `a`. We prove:

* `artinSchreierChar_eq_of_sub_eq`: `χ_a = χ_b` if `a - b = c - cᵖ` (XI.6.8);
* `artinSchreierChar_algebraMap`: naturality, `χ_{f(a)} = χ_a ∘ π₁(f)` for an `R`-algebra
  `f : R → S` (V.6), where `π₁(f) = AffineLinePGroups.fundamentalGroupMap`;
* `artinSchreierChar_autMap_id`: compatibility with the change of geometric point (V.7);
* `exists_artinSchreierChar_eq`: over a field `K`, every continuous homomorphism
  `π₁(Spec K, a) → ℤ/p` is some `χ_a` (Artin–Schreier theory: a `ℤ/p`-Galois algebra is
  `K[T]/(Tᵖ - T + a)`, by additive Hilbert 90).

These are the inputs of the Artin–Schreier step in Harbater–Stevenson's node lemma
(`SGA.SGA1.ExposeXIII.AbhyankarAffineLineNode`). For `R` affine, XI.6.9
(`SGA.SGA1.ExposeXI.artinSchreierEquivContinuousMonoidHom`) gives a bijection between `R/℘(R)` and
the continuous homomorphisms `π₁ → ℤ/p` by fpqc cohomology; it is not identified there with the
explicit `χ_a`, and its naturality is not proved, which is why the explicit characters are used
here.
-/

universe u

open CategoryTheory PreGaloisCategory Polynomial CommAlgCat TensorProduct

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

variable (p : ℕ) [hp : Fact p.Prime]

lemma discreteZMod_mul_comm (a b : DiscreteZMod.{u} p) : a * b = b * a :=
  (DiscreteZMod.equiv p).injective (by rw [map_mul, map_mul, mul_comm])

section Character

variable {R : Type u} [CommRing R] [CharP R p] [IsDomain R] [ConnectedSpace (PrimeSpectrum R)]
  (Ω : Type u) [Field Ω] [Algebra R Ω] [IsSepClosed Ω] [CharP Ω p]

/-- XI.6.7, V.5.11: the Artin–Schreier character `χ_a : π₁(Spec R, a) → ℤ/p` of `a ∈ R`, the
continuous homomorphism attached to the Artin–Schreier covering `R[T]/(Tᵖ - T + a)` (a principal
covering with group `ℤ/p`, `k` acting by `T ↦ T + k`). -/
noncomputable def artinSchreierChar (a : R) :
    ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) (DiscreteZMod.{u} p) :=
  ⟨(artinSchreierPrincipal (p := p) Ω a).hom (artinSchreierPrincipal (p := p) Ω a).nonempty.some,
    ExposeV.continuous_torsorHom _ _⟩

/-- `χ_a` may be computed at any point of the Artin–Schreier covering over the geometric point. -/
lemma artinSchreierChar_apply (a : R)
    (x : (ExposeV.fiberFunctor R Ω).obj (artinSchreierPrincipal (p := p) Ω a).X)
    (σ : Aut (ExposeV.fiberFunctor R Ω)) :
    artinSchreierChar p Ω a σ = (artinSchreierPrincipal (p := p) Ω a).hom x σ := by
  change (artinSchreierPrincipal (p := p) Ω a).hom _ σ = _
  rw [ExposeXI.PrincipalObject.hom_eq_hom_of_commute (discreteZMod_mul_comm p) _ _ x]

/-- XI.6.8 (part: `℘`-invariance of the characters): `χ_a = χ_b` when `a - b ∈ ℘(R)`. -/
theorem artinSchreierChar_eq_of_sub_eq (a b c : R) (h : a - b = c - c ^ p) :
    artinSchreierChar p Ω a = artinSchreierChar p Ω b := by
  obtain ⟨e, he⟩ := (ExposeXI.ArtinSchreier.nonempty_equivariant_iff (p := p) a b).mpr ⟨c, h⟩
  have hiso : (artinSchreierPrincipal (p := p) Ω a).IsIso
      (artinSchreierPrincipal (p := p) Ω b) := by
    refine ⟨(FiniteEtale.isoMk e.symm).op, fun g ↦ ?_⟩
    apply Quiver.Hom.unop_inj
    ext y
    change ExposeXI.ArtinSchreier.action p a (DiscreteZMod.equiv p g) (e.symm y) =
      e.symm (ExposeXI.ArtinSchreier.action p b (DiscreteZMod.equiv p g) y)
    apply e.injective
    rw [he]
    exact (congrArg _ (e.apply_symm_apply y)).trans (e.apply_symm_apply _).symm
  ext σ
  obtain ⟨φ, hφ⟩ := hiso
  have h₁ := (artinSchreierPrincipal (p := p) Ω a).torsorHom_map _ φ hφ
    (artinSchreierPrincipal (p := p) Ω a).nonempty.some
  change _ = (artinSchreierPrincipal (p := p) Ω b).hom _ σ
  rw [ExposeXI.PrincipalObject.hom_eq_hom_of_commute (discreteZMod_mul_comm p) _ _
    ((ExposeV.fiberFunctor R Ω).map φ.hom (artinSchreierPrincipal (p := p) Ω a).nonempty.some),
    h₁]
  rfl

variable {Ω} in
/-- V.7: `χ_a` is compatible with the change of geometric point along an isomorphism of fibre
functors (a class of paths). -/
theorem artinSchreierChar_autMap_id {Ω' : Type u} [Field Ω'] [Algebra R Ω'] [IsSepClosed Ω']
    [CharP Ω' p] (e : 𝟭 _ ⋙ ExposeV.fiberFunctor R Ω ≅ ExposeV.fiberFunctor R Ω') (a : R)
    (σ : Aut (ExposeV.fiberFunctor R Ω)) :
    artinSchreierChar p Ω' a (ExposeV.autMap (𝟭 _) e σ) = artinSchreierChar p Ω a σ := by
  have hiso : ((artinSchreierPrincipal (p := p) Ω' a).mapFunctor (𝟭 _) e).IsIso
      (artinSchreierPrincipal (p := p) Ω a) :=
    ⟨Iso.refl _, fun g ↦ (Category.comp_id _).trans (Category.id_comp _).symm⟩
  symm
  exact ExposeXI.PrincipalObject.hom_eq_of_isIso_mapFunctor (discreteZMod_mul_comm p) _ e _ _
    hiso _ _ σ

end Character

section BaseChange

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S] [CharP R p] [CharP S p]

/-- The Artin–Schreier covering of `f(a)` over `S` is the base change of the one of `a` over `R`:
`S[T]/(Tᵖ - T + f(a)) → S ⊗_R R[T]/(Tᵖ - T + a)`, `T ↦ 1 ⊗ T`. -/
noncomputable def artinSchreierToBaseChange (a : R) :
    ExposeXI.ArtinSchreierAlgebra S p (algebraMap R S a) →ₐ[S]
      S ⊗[R] ExposeXI.ArtinSchreierAlgebra R p a :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId S _) (1 ⊗ₜ AdjoinRoot.root _) (by
    change aeval _ (X ^ p - X + C (algebraMap R S a)) = 0
    rw [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C, Algebra.TensorProduct.tmul_pow,
      one_pow, ExposeXI.ArtinSchreier.root_pow, tmul_sub, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
    ring)

omit hp [CharP R p] [CharP S p] in
lemma artinSchreierToBaseChange_root (a : R) :
    artinSchreierToBaseChange p S a (AdjoinRoot.root _) = 1 ⊗ₜ AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The inverse map `S ⊗_R R[T]/(Tᵖ - T + a) → S[T]/(Tᵖ - T + f(a))`. -/
noncomputable def artinSchreierOfBaseChange (a : R) :
    S ⊗[R] ExposeXI.ArtinSchreierAlgebra R p a →ₐ[S]
      ExposeXI.ArtinSchreierAlgebra S p (algebraMap R S a) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (AdjoinRoot.root _) (by
      change aeval _ (X ^ p - X + C a) = 0
      rw [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C, ExposeXI.ArtinSchreier.root_pow,
        IsScalarTower.algebraMap_apply R S
          (ExposeXI.ArtinSchreierAlgebra S p (algebraMap R S a)) a]
      ring))
    fun _ _ ↦ Commute.all _ _

omit hp [CharP R p] [CharP S p] in
lemma artinSchreierOfBaseChange_tmul_root (a : R) (s : S) :
    artinSchreierOfBaseChange p S a (s ⊗ₜ AdjoinRoot.root _) =
      algebraMap S _ s * AdjoinRoot.root _ := by
  simp [artinSchreierOfBaseChange, Algebra.ofId_apply]

/-- XI.6.7: base change of Artin–Schreier coverings,
`S[T]/(Tᵖ - T + f(a)) ≅ S ⊗_R R[T]/(Tᵖ - T + a)`. -/
noncomputable def artinSchreierBaseChangeEquiv (a : R) :
    ExposeXI.ArtinSchreierAlgebra S p (algebraMap R S a) ≃ₐ[S]
      S ⊗[R] ExposeXI.ArtinSchreierAlgebra R p a :=
  AlgEquiv.ofAlgHom (artinSchreierToBaseChange p S a) (artinSchreierOfBaseChange p S a)
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AdjoinRoot.algHom_ext ?_)
      change artinSchreierToBaseChange p S a (artinSchreierOfBaseChange p S a
        (1 ⊗ₜ AdjoinRoot.root _)) = 1 ⊗ₜ AdjoinRoot.root _
      rw [artinSchreierOfBaseChange_tmul_root, map_one, one_mul, artinSchreierToBaseChange_root])
    (by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, artinSchreierToBaseChange_root,
        artinSchreierOfBaseChange_tmul_root, map_one, one_mul, AlgHom.id_apply])

lemma artinSchreierBaseChangeEquiv_action (a : R) (k : Multiplicative (ZMod p))
    (y : ExposeXI.ArtinSchreierAlgebra S p (algebraMap R S a)) :
    Algebra.TensorProduct.map (AlgHom.id S S)
        (ExposeXI.ArtinSchreier.action p a k).toAlgHom (artinSchreierBaseChangeEquiv p S a y) =
      artinSchreierBaseChangeEquiv p S a
        (ExposeXI.ArtinSchreier.action p (algebraMap R S a) k y) := by
  have : (Algebra.TensorProduct.map (AlgHom.id S S)
      (ExposeXI.ArtinSchreier.action p a k).toAlgHom).comp
        (artinSchreierBaseChangeEquiv p S a).toAlgHom =
      (artinSchreierBaseChangeEquiv p S a).toAlgHom.comp
        (ExposeXI.ArtinSchreier.action p (algebraMap R S a) k).toAlgHom := by
    refine AdjoinRoot.algHom_ext ?_
    change Algebra.TensorProduct.map (AlgHom.id S S) _
        (artinSchreierToBaseChange p S a (AdjoinRoot.root _)) =
      artinSchreierToBaseChange p S a (ExposeXI.ArtinSchreier.action p _ k (AdjoinRoot.root _))
    rw [artinSchreierToBaseChange_root, ExposeXI.ArtinSchreier.action_root,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom,
      ExposeXI.ArtinSchreier.action_root, map_add, AlgHom.commutes,
      artinSchreierToBaseChange_root, tmul_add]
    congr 1
    exact RingHom.congr_fun (RingHom.ext_zmod
      ((Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom.comp
        ((algebraMap R (ExposeXI.ArtinSchreierAlgebra R p a)).comp (ZMod.castHom (dvd_refl p) R)))
      ((algebraMap S (S ⊗[R] ExposeXI.ArtinSchreierAlgebra R p a)).comp
        (ZMod.castHom (dvd_refl p) S))) _
  exact AlgHom.congr_fun this y

end BaseChange

section Naturality

variable {R : Type u} [CommRing R] [CharP R p] [IsDomain R] [ConnectedSpace (PrimeSpectrum R)]
  {S : Type u} [CommRing S] [CharP S p] [IsDomain S] [ConnectedSpace (PrimeSpectrum S)]
  [Algebra R S] (Ω : Type u) [Field Ω] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  [IsSepClosed Ω] [CharP Ω p]

/-- V.6, XI.6.7: naturality of Artin–Schreier characters, `χ_{f(a)} = χ_a ∘ π₁(f)` for an
`R`-algebra `f : R → S` and a geometric point `S → Ω`. -/
theorem artinSchreierChar_algebraMap (a : R) (σ : Aut (ExposeV.fiberFunctor S Ω)) :
    artinSchreierChar p Ω (algebraMap R S a) σ =
      artinSchreierChar p Ω a (fundamentalGroupMap R S Ω σ) := by
  have hiso : ((artinSchreierPrincipal (p := p) Ω a).mapFunctor
      (FiniteEtale.baseChange.{u} R S).op
      (FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S).symm).IsIso
      (artinSchreierPrincipal (p := p) Ω (algebraMap R S a)) := by
    refine ⟨(FiniteEtale.isoMk (artinSchreierBaseChangeEquiv p S a)).op, fun g ↦ ?_⟩
    apply Quiver.Hom.unop_inj
    ext y
    exact artinSchreierBaseChangeEquiv_action p S a _ y
  exact ExposeXI.PrincipalObject.hom_eq_of_isIso_mapFunctor (discreteZMod_mul_comm p) _ _ _ _
    hiso _ _ σ

end Naturality

section Field

variable {R : Type u} [CommRing R] [CharP R p] [IsDomain R] [ConnectedSpace (PrimeSpectrum R)]
  (Ω : Type u) [Field Ω] [Algebra R Ω] [IsSepClosed Ω] [CharP Ω p]

/-- `χ₀ = 1`: the Artin–Schreier covering of `0` is trivial. -/
theorem artinSchreierChar_zero : artinSchreierChar p Ω (0 : R) = 1 := by
  have := ExposeXI.ArtinSchreier.etale hp.out (CharP.cast_eq_zero R p) (0 : R)
  -- the section `T ↦ 0`
  let s : ExposeXI.ArtinSchreierAlgebra R p (0 : R) →ₐ[R] R :=
    (ExposeXI.ArtinSchreier.pointsEquiv p (0 : R) R).symm ⟨0, by simp [hp.out.ne_zero]⟩
  let f : Opposite.op (FiniteEtale.of R R) ⟶ (artinSchreierPrincipal (p := p) Ω (0 : R)).X :=
    (FiniteEtale.ofHom s).op
  let pt : (ExposeV.fiberFunctor R Ω).obj (Opposite.op (FiniteEtale.of R R)) := Algebra.ofId R Ω
  ext σ
  rw [artinSchreierChar_apply p Ω 0 ((ExposeV.fiberFunctor R Ω).map f pt)]
  change _ = (1 : DiscreteZMod.{u} p)
  rw [ExposeXI.PrincipalObject.hom_eq_iff, ExposeXI.PrincipalObject.act_one,
    mulAction_naturality]
  congr 1
  exact Subsingleton.elim (α := R →ₐ[R] Ω) _ _

end Field

section Surjective

omit hp in
/-- The fixed points of a group of automorphisms of a finite field extension `T/K`, of order
`[T : K]`, lie in `K` (Artin). -/
lemma mem_range_algebraMap_of_forall_eq (K : Type*) [Field K] {T : Type*} [Field T]
    [Algebra K T] [FiniteDimensional K T] {G : Type*} [Group G] [Finite G]
    (ρ : G →* (T ≃ₐ[K] T)) (hρ : Function.Injective ρ) (hcard : Nat.card G = Module.finrank K T)
    {t : T} (ht : ∀ g, ρ g t = t) : t ∈ (algebraMap K T).range := by
  set H : Subgroup (T ≃ₐ[K] T) := ρ.range
  have hH : Nat.card H = Nat.card G := (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  have hfix : t ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨g, rfl⟩
    exact ht g
  have h2 := Module.finrank_mul_finrank K (IntermediateField.fixedField H) T
  rw [IntermediateField.finrank_fixedField_eq_card, hH, hcard] at h2
  have h3 : Module.finrank K (IntermediateField.fixedField H) = 1 :=
    Nat.eq_of_mul_eq_mul_right Module.finrank_pos (by rw [one_mul]; exact h2)
  rw [IntermediateField.finrank_eq_one_iff] at h3
  rw [h3] at hfix
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hfix
  exact ⟨a, ha⟩

lemma natCard_discreteZMod : Nat.card (DiscreteZMod.{u} p) = p := by
  rw [Nat.card_congr (DiscreteZMod.equiv p).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

variable (K : Type u) [Field K] [CharP K p] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  [CharP Ω p]

/-- XI.6.9 for a field (surjectivity half of the Artin–Schreier isomorphism
`K/℘(K) ≅ Hom(π₁, ℤ/p)`): every continuous homomorphism `π₁(Spec K, a) → ℤ/p` is an
Artin–Schreier character `χ_a`. If it is onto, its principal covering
(V.5.11) is a cyclic extension `T/K` of degree `p`; additive Hilbert 90 gives `α ∈ T` with
`g(α) = α + g`, and then `a = α - αᵖ ∈ K` and `T ≅ K[T]/(Tᵖ - T + a)`. -/
theorem exists_artinSchreierChar_eq
    (δ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor K Ω)) (DiscreteZMod.{u} p)) :
    ∃ a : K, artinSchreierChar p Ω a = δ := by
  classical
  by_cases hδ : Function.Surjective δ
  swap
  · refine ⟨0, ?_⟩
    have : Fact (Nat.card (DiscreteZMod.{u} p)).Prime := ⟨(natCard_discreteZMod p).symm ▸ hp.out⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card δ.toMonoidHom.range with h | h
    · rw [artinSchreierChar_zero]
      ext σ
      have : δ σ ∈ δ.toMonoidHom.range := ⟨σ, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this.symm
    · exact absurd (fun g ↦ (show g ∈ δ.toMonoidHom.range from h ▸ Subgroup.mem_top g)) hδ
  -- `δ` is onto: its principal covering `T` is a cyclic extension of degree `p`
  obtain ⟨X, α, hα, x₀, hx₀⟩ := ExposeV.exists_torsorHom_eq (F := ExposeV.fiberFunctor K Ω)
    δ.toMonoidHom δ.continuous
  set T : FiniteEtale.{u} K := X.unop
  let ρ : DiscreteZMod.{u} p →* (T.obj ≃ₐ[K] T.obj) :=
    (autOpMulEquivAlgEquiv T).toMonoidHom.comp α
  have hρapply (g : DiscreteZMod.{u} p) (x : T.obj →ₐ[K] Ω) :
      (ExposeV.fiberFunctor K Ω).map (α g).unop.hom x = x.comp (ρ g).toAlgHom :=
    fiberFunctor_map_unop_hom Ω T (α g) x
  have hH : ∀ x y : T.obj →ₐ[K] Ω, ∃! g, x.comp (ρ g).toAlgHom = y := by
    intro x y
    obtain ⟨g, hg, hu⟩ := hα x y
    exact ⟨g, (hρapply g x).symm.trans hg, fun g' hg' ↦ hu g' ((hρapply g' x).trans hg')⟩
  have hTi := galoisAlgebra_nontrivial_and_idempotent K Ω δ hδ hα x₀ hx₀
  have : Nontrivial T.obj := hTi.1
  have : Fintype (DiscreteZMod.{u} p) := Fintype.ofFinite _
  obtain ⟨θ, hθ⟩ := galoisAlgebra_exists_sum_smul_eq_one K Ω T ρ x₀ hH hTi.2
  let := MulSemiringAction.compHom T.obj ρ
  have hsmul (g : DiscreteZMod.{u} p) (b : T.obj) : g • b = ρ g b := rfl
  -- the cocycle `g ↦ g` with values in `𝔽_p ⊆ T`, and additive Hilbert 90
  let c : DiscreteZMod.{u} p → T.obj := fun g ↦
    algebraMap K T.obj (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd (DiscreteZMod.equiv p g)))
  have hc : ∀ σ τ, c (σ * τ) = σ • c τ + c σ := by
    intro σ τ
    simp only [c, hsmul, AlgEquiv.commutes, map_mul, toAdd_mul, map_add]
    ring
  obtain ⟨β, hβ⟩ := exists_eq_sub_smul_of_cocycle hθ c hc
  have hpT : ((p : ℕ) : T.obj) = 0 := by
    rw [← map_natCast (algebraMap K T.obj), CharP.cast_eq_zero, map_zero]
  have hαT (g : DiscreteZMod.{u} p) : ρ g (-β) = -β + c g := by
    rw [map_neg, ← hsmul]
    linear_combination -(hβ g)
  have hcp (g : DiscreteZMod.{u} p) : c g ^ p = c g := by
    simp only [c, ← map_pow, ZMod.pow_card]
  have hinv (g : DiscreteZMod.{u} p) : ρ g (-β - (-β) ^ p) = -β - (-β) ^ p := by
    rw [map_sub, map_pow, hαT,
      ExposeXI.ArtinSchreier.add_pow_of_natCast_eq_zero hp.out hpT, hcp]
    ring
  -- `T` is a field, and `T^G = K`
  obtain ⟨a, ha⟩ : ∃ a : K, algebraMap K T.obj a = -β - (-β) ^ p := by
    have hconn : IsConnected X := isConnected_of_torsorHom K Ω δ hδ hα x₀ hx₀
    have : ConnectedSpace (PrimeSpectrum T.obj) :=
      (ExposeV.isConnected_op_iff_connectedSpace K T).mp hconn
    have : Subsingleton (PrimeSpectrum T.obj) := PreconnectedSpace.trivial_of_discrete
    have : IsLocalRing T.obj := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal T.obj
      refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun I hI ↦ ?_⟩
      have := Subsingleton.elim (⟨I, hI.isPrime⟩ : PrimeSpectrum T.obj) ⟨M, hM.isPrime⟩
      exact congrArg PrimeSpectrum.asIdeal this
    have : IsReduced T.obj := Algebra.FormallyUnramified.isReduced_of_field K T.obj
    let : Field T.obj := (IsArtinianRing.isField_of_isReduced_of_isLocalRing T.obj).toField
    have hρinj : Function.Injective ρ := by
      intro g g' hgg'
      obtain ⟨h₀, -, hu⟩ := hH x₀ (x₀.comp (ρ g).toAlgHom)
      rw [hu g rfl, hu g' (by rw [hgg'])]
    have hcard : Nat.card (DiscreteZMod.{u} p) = Module.finrank K T.obj := by
      have h1 := ExposeV.card_fiber_eq_rankAtStalk K Ω T (Classical.arbitrary _)
      have h2 : Module.rankAtStalk (R := K) T.obj (Classical.arbitrary _) =
          Module.finrank K T.obj := by
        rw [Module.rankAtStalk_eq_finrank_of_free]
        rfl
      rw [← h2, ← h1]
      exact Nat.card_congr (Equiv.ofBijective _ (hα.bijective x₀))
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_forall_eq K ρ hρinj hcard hinv
    exact ⟨a, ha⟩
  -- the Artin–Schreier covering of `a` maps equivariantly to `T`
  let φ : ExposeXI.ArtinSchreierAlgebra K p a →ₐ[K] T.obj :=
    (ExposeXI.ArtinSchreier.pointsEquiv p a T.obj).symm ⟨-β, ha.symm⟩
  have hφroot : φ (AdjoinRoot.root _) = -β := by
    simp [φ, ExposeXI.ArtinSchreier.pointsEquiv]
  let P : ExposeXI.PrincipalObject (ExposeV.fiberFunctor K Ω) (DiscreteZMod.{u} p) :=
    ⟨X, α, hα, ⟨x₀⟩⟩
  let f : P.X ⟶ (artinSchreierPrincipal (p := p) Ω a).X :=
    (ObjectProperty.homMk (CommAlgCat.ofHom φ) : artinSchreierFE p a ⟶ T).op
  have hf : ∀ g, (P.α g).unop.hom ≫ f =
      f ≫ ((artinSchreierPrincipal (p := p) Ω a).α g).unop.hom := by
    intro g
    have key : (ρ g).toAlgHom.comp φ =
        φ.comp (ExposeXI.ArtinSchreier.action p a (DiscreteZMod.equiv p g)).toAlgHom := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
        hφroot, hαT, ExposeXI.ArtinSchreier.action_root, map_add, hφroot, AlgHom.commutes]
    apply Quiver.Hom.unop_inj
    ext y
    exact AlgHom.congr_fun key y
  refine ⟨a, ?_⟩
  ext σ
  rw [artinSchreierChar_apply p Ω a ((ExposeV.fiberFunctor K Ω).map f x₀),
    ExposeXI.PrincipalObject.hom_map_of_equivariant P _ f hf x₀]
  exact congrArg (fun h ↦ h σ) hx₀

end Surjective

end SGA.SGA1.ExposeXIII.AffineLinePGroups
