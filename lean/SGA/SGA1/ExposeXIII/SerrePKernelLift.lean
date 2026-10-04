/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.Matrix.ToLin
import SGA.SGA1.ExposeXIII.SerrePKernelVector

/-!
# Weak solutions of embedding problems with elementary abelian kernel

The first half of Serre's theorem on `p`-group kernels (used in Raynaud's proof of XIII.2.13),
for `π₁(Spec R)`, `R` of characteristic `p` with connected spectrum:
`exists_lift_of_elementary_ker` lifts a continuous surjection `π₁ → H` through any surjection
`G → H` with kernel `≅ (ℤ/p)ʳ`. The lift is the vector Artin–Schreier covering
(`SGA.SGA1.ExposeXIII.SerrePKernelVector`) of the Galois algebra `B` of `π₁ → H`, the class
`a ∈ B ⊗ (ℤ/p)ʳ` coming from the vanishing of the Galois cohomology of the semilinear module
`B ⊗ (ℤ/p)ʳ` (`AffineLinePGroups.exists_liftCochain_sub`, with the diagonal action
`vecDistribMulAction` and the conjugation matrices `conjMat`).
-/

universe u

namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

open Matrix

/-- A monoid homomorphism trivial on the kernel of a surjection `π : G → H` of groups factors
through `π` (the target need not be a group): `QuotientGroup.lift` composed with
`QuotientGroup.quotientKerEquivOfSurjective`. -/
lemma exists_comp_eq_of_ker {G H M : Type*} [Group G] [Group H] [Monoid M] (π : G →* H)
    (hπ : Function.Surjective π) (f : G →* M) (hf : ∀ z ∈ π.ker, f z = 1) :
    ∃ f' : H →* M, f'.comp π = f := by
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨(QuotientGroup.lift π.ker f hf).comp e.symm.toMonoidHom, MonoidHom.ext fun g ↦ ?_⟩
  change QuotientGroup.lift π.ker f hf (e.symm (e g)) = f g
  rw [e.symm_apply_apply]
  rfl

section ConjRep

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {r : ℕ}
  (e : Multiplicative (Fin r → ZMod p) ≃* N)

/-- The conjugation action of `G` on an elementary abelian normal subgroup `N ≅ (ℤ/p)ʳ`, in
coordinates. -/
noncomputable def conjRep : G →* Module.End (ZMod p) (Fin r → ZMod p) where
  toFun g := AddMonoidHom.toZModLinearMap p
    (AddEquiv.toMultiplicative.symm (e.trans ((MulAut.conjNormal g).trans e.symm))).toAddMonoidHom
  map_one' := by
    ext v i
    simp [AddEquiv.toMultiplicative]
  map_mul' g h := by
    ext v i
    simp [AddEquiv.toMultiplicative]

lemma conjRep_apply (g : G) (v : Fin r → ZMod p) :
    conjRep p e g v =
      Multiplicative.toAdd (e.symm (MulAut.conjNormal g (e (Multiplicative.ofAdd v)))) :=
  rfl

/-- The matrices of the conjugation action. -/
noncomputable def conjMat : G →* Matrix (Fin r) (Fin r) (ZMod p) :=
  (LinearMap.toMatrixAlgEquiv' : _ ≃ₐ[ZMod p] _).toRingEquiv.toMonoidHom.comp (conjRep p e)

lemma conjMat_mulVec (g : G) (v : Fin r → ZMod p) : conjMat p e g *ᵥ v = conjRep p e g v := by
  change LinearMap.toMatrix' (conjRep p e g) *ᵥ v = _
  exact LinearMap.toMatrix'_mulVec _ v

lemma conjRep_eq_one_of_mem {z : G} (hz : z ∈ N) : conjRep p e z = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  have hcomm : ∀ x y : N, x * y = y * x := fun x y ↦ by
    have := congrArg e (mul_comm (e.symm x) (e.symm y))
    simpa using this
  have : MulAut.conjNormal z (e (Multiplicative.ofAdd v)) = e (Multiplicative.ofAdd v) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := congrArg Subtype.val (hcomm ⟨z, hz⟩ (e (Multiplicative.ofAdd v)))
    simp only [Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
  simp [conjRep_apply, this]

lemma conjMat_eq_one_of_mem {z : G} (hz : z ∈ N) : conjMat p e z = 1 := by
  rw [conjMat, MonoidHom.comp_apply, conjRep_eq_one_of_mem p e hz, map_one]

end ConjRep

section Action

/-- `Bʳ = B ⊗ (ℤ/p)ʳ`, as a type synonym carrying the diagonal semilinear action. -/
def TwistedVec (r : ℕ) (B : Type*) : Type _ := Fin r → B

instance (r : ℕ) (B : Type*) [CommRing B] : AddCommGroup (TwistedVec r B) :=
  inferInstanceAs (AddCommGroup (Fin r → B))

instance (r : ℕ) (B : Type*) [CommRing B] : Module B (TwistedVec r B) :=
  inferInstanceAs (Module B (Fin r → B))

section TwistedVecLemmas

variable {r : ℕ} {B : Type*} [CommRing B]

@[simp] lemma TwistedVec.add_apply (w w' : TwistedVec r B) (i : Fin r) :
    (w + w') i = w i + w' i := rfl
@[simp] lemma TwistedVec.sub_apply (w w' : TwistedVec r B) (i : Fin r) :
    (w - w') i = w i - w' i := rfl
@[simp] lemma TwistedVec.zero_apply (i : Fin r) : (0 : TwistedVec r B) i = 0 := rfl
@[simp] lemma TwistedVec.smul_apply (b : B) (w : TwistedVec r B) (i : Fin r) :
    (b • w) i = b * w i := rfl

end TwistedVecLemmas

variable (p : ℕ) [Fact p.Prime] {r : ℕ} {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [CharP B p] {H : Type*} [Group H] (ρH : H →* (B ≃ₐ[R] B))
  (CmH : H →* Matrix (Fin r) (Fin r) (ZMod p))

omit [Fact p.Prime] in
lemma algEquiv_castMat_mulVec (σ : B ≃ₐ[R] B) (M : Matrix (Fin r) (Fin r) (ZMod p))
    (v : Fin r → B) :
    (fun i ↦ σ ((castMat p B M *ᵥ v) i)) = castMat p B M *ᵥ fun i ↦ σ (v i) :=
  funext fun i ↦ map_castMat_mulVec (σ : B →+* B) M v i

/-- The diagonal semilinear action `σ ⋆ w = Cm(σ) σ(w)` of `H` on `Bʳ = B ⊗ (ℤ/p)ʳ`. -/
@[reducible] noncomputable def vecDistribMulAction : DistribMulAction H (TwistedVec r B) where
  smul σ w := castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (w i)
  one_smul w := by
    change castMat p B (CmH 1) *ᵥ (fun i ↦ ρH 1 (w i)) = w
    simp
  mul_smul σ τ w := by
    change castMat p B (CmH (σ * τ)) *ᵥ (fun i ↦ ρH (σ * τ) (w i)) =
      castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ ((castMat p B (CmH τ) *ᵥ fun i ↦ ρH τ (w i)) i)
    rw [algEquiv_castMat_mulVec, mulVec_mulVec, ← castMat_mul, ← map_mul]
    simp [AlgEquiv.mul_apply]
  smul_zero σ := by
    change castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ ((0 : Fin r → B) i)) = 0
    simp only [Pi.zero_apply, map_zero]
    exact mulVec_zero _
  smul_add σ w w' := by
    change castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ ((w + w' : TwistedVec r B) i)) =
      castMat p B (CmH σ) *ᵥ (fun i ↦ ρH σ (w i)) + castMat p B (CmH σ) *ᵥ fun i ↦ ρH σ (w' i)
    rw [← mulVec_add]
    congr 1
    funext i
    simp only [TwistedVec.add_apply, map_add]
    rfl

end Action

section Lift

open CategoryTheory PreGaloisCategory CommAlgCat AffineLinePGroups

variable (p : ℕ) [hp : Fact p.Prime]

/-- Weak solvability of embedding problems with elementary abelian kernel for `π₁(Spec R)` in
characteristic `p` (the concrete form of `cd_p ≤ 1`): if `ψ : π₁ → H` is a continuous
surjection and `π : G → H` is onto with kernel `≅ (ℤ/p)ʳ`, then `ψ` lifts to a continuous
homomorphism `π₁ → G`. The lift is a vector Artin–Schreier covering of the Galois algebra of
`ψ`, with the semilinear action of `G`. -/
theorem exists_lift_of_elementary_ker (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    {H G : Type u} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G]
    [TopologicalSpace G] [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    (π : G →* H) (hπ : Function.Surjective π) {r : ℕ}
    (e : Multiplicative (Fin r → ZMod p) ≃* π.ker) :
    ∃ ψ' : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G,
      π.comp ψ'.toMonoidHom = ψ.toMonoidHom := by
  classical
  have : CharP Ω p := charP_of_algebra p R Ω
  obtain ⟨P, α, hα, x₀, hx₀⟩ := ExposeV.exists_torsorHom_eq
    (F := ExposeV.fiberFunctor R Ω) ψ.toMonoidHom ψ.continuous
  let A := P.unop
  let ρH : H →* (A.obj ≃ₐ[R] A.obj) := (autOpMulEquivAlgEquiv A).toMonoidHom.comp α
  have hH : ∀ x y : A.obj →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y := hα
  let x₀a : A.obj →ₐ[R] Ω := x₀
  obtain ⟨hnt, hidem⟩ := galoisAlgebra_nontrivial_and_idempotent R Ω ψ hψ hα x₀ hx₀
  have : CharP A.obj p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap R A.obj), CharP.cast_eq_zero, map_zero])
  have : Fintype H := Fintype.ofFinite H
  let : MulSemiringAction H A.obj := MulSemiringAction.compHom A.obj ρH
  obtain ⟨θ, hθ⟩ := galoisAlgebra_exists_sum_smul_eq_one R Ω A ρH x₀a hH hidem
  choose s hs using hπ
  -- the conjugation matrices, factored through `H`
  obtain ⟨CmH, hCmH⟩ := exists_comp_eq_of_ker π (fun σ ↦ ⟨s σ, hs σ⟩) (conjMat p e)
    fun z hz ↦ conjMat_eq_one_of_mem p e hz
  -- the semilinear module `W = A ⊗ (ℤ/p)ʳ`
  let : DistribMulAction H (TwistedVec r A.obj) := vecDistribMulAction p ρH CmH
  have hsmulW : ∀ (σ : H) (w : TwistedVec r A.obj),
      σ • w = castMat p A.obj (CmH σ) *ᵥ fun i ↦ ρH σ (w i) := fun _ _ ↦ rfl
  have hW : ∀ (σ : H) (b : A.obj) (w : TwistedVec r A.obj), σ • (b • w) = (σ • b) • (σ • w) := by
    intro σ b w
    rw [hsmulW, hsmulW]
    have : (fun i ↦ ρH σ ((b • w) i)) = ρH σ b • fun i ↦ ρH σ (w i) := by
      funext i
      simp
    rw [this, mulVec_smul]
    rfl
  -- the character of the kernel
  let χ : G → Fin r → ZMod p := fun g ↦
    if h : g ∈ π.ker then Multiplicative.toAdd (e.symm ⟨g, h⟩) else 0
  have hχ : ∀ z (hz : z ∈ π.ker), χ z = Multiplicative.toAdd (e.symm ⟨z, hz⟩) := fun z hz ↦ by
    simp only [χ]
    split_ifs
    rfl
  let κ : G → TwistedVec r A.obj := fun g i ↦ ZMod.castHom (dvd_refl p) A.obj (χ g i)
  have hκ : ∀ z ∈ π.ker, ∀ w ∈ π.ker, κ (z * w) = κ z + κ w := by
    intro z hz w hw
    funext i
    change ZMod.castHom (dvd_refl p) A.obj (χ (z * w) i) =
      ZMod.castHom (dvd_refl p) A.obj (χ z i) + ZMod.castHom (dvd_refl p) A.obj (χ w i)
    rw [hχ _ (mul_mem hz hw), hχ z hz, hχ w hw, ← map_add]
    congr 1
    rw [← Pi.add_apply, ← toAdd_mul, ← map_mul]
    rfl
  have hκc : ∀ g, ∀ z ∈ π.ker, κ (g * z * g⁻¹) = π g • κ z := by
    intro g z hz
    have hgz : g * z * g⁻¹ ∈ π.ker := (MonoidHom.normal_ker π).conj_mem z hz g
    rw [hsmulW]
    have hfix : (fun i ↦ ρH (π g) (κ z i)) = κ z := by
      funext i
      exact RingHom.congr_fun (RingHom.ext_zmod (((ρH (π g)) : A.obj →+* A.obj).comp
        (ZMod.castHom (dvd_refl p) A.obj)) (ZMod.castHom (dvd_refl p) A.obj)) _
    rw [hfix]
    have hCm : CmH (π g) = conjMat p e g := by rw [← MonoidHom.comp_apply, hCmH]
    funext i
    rw [hCm]
    have h1 := RingHom.map_mulVec (ZMod.castHom (dvd_refl p) A.obj) (conjMat p e g) (χ z) i
    change ZMod.castHom (dvd_refl p) A.obj (χ (g * z * g⁻¹) i) =
      ((conjMat p e g).map (ZMod.castHom (dvd_refl p) A.obj) *ᵥ
        (⇑(ZMod.castHom (dvd_refl p) A.obj) ∘ χ z)) i
    rw [← h1, conjMat_mulVec, conjRep_apply, hχ z hz, hχ _ hgz]
    have h2 : MulAut.conjNormal g (e (Multiplicative.ofAdd (Multiplicative.toAdd
        (e.symm ⟨z, hz⟩)))) = ⟨g * z * g⁻¹, hgz⟩ := by
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      exact Subtype.ext (MulAut.conjNormal_apply g ⟨z, hz⟩)
    rw [h2]
  -- the Frobenius of `W`
  let F : TwistedVec r A.obj →+ TwistedVec r A.obj :=
    { toFun := fun w i ↦ w i ^ p
      map_zero' := by
        funext i
        exact zero_pow hp.out.ne_zero
      map_add' := fun w w' ↦ by
        funext i
        exact add_pow_char _ _ _ }
  have hF : ∀ (σ : H) (w : TwistedVec r A.obj), F (σ • w) = σ • F w := by
    intro σ w
    rw [hsmulW, hsmulW]
    funext i
    change (castMat p A.obj (CmH σ) *ᵥ fun i ↦ ρH σ (w i)) i ^ p =
      (castMat p A.obj (CmH σ) *ᵥ fun j ↦ ρH σ (w j ^ p)) i
    rw [castMat_mulVec_pow]
    simp only [map_pow]
  have hκF : ∀ z ∈ π.ker, F (κ z) = κ z := fun z _ ↦ by
    funext i
    exact ExposeXI.ArtinSchreier.castHom_pow p _
  obtain ⟨a₀, ha⟩ := exists_liftCochain_sub hW π s hs κ F hF hθ hκ hκc hκF
  let a : Fin r → A.obj := fun i ↦ a₀ i
  let u : G → Fin r → A.obj := fun g i ↦ liftCochain π s κ θ g i
  have hu : ∀ g i, u g i ^ p - u g i = a i - vecAct p (ρH.comp π) (CmH.comp π) g a i := by
    intro g i
    exact congrFun (ha g) i
  have hmul : ∀ g h, u (g * h) = u g + vecAct p (ρH.comp π) (CmH.comp π) g (u h) := by
    intro g h
    funext i
    have := congrFun (liftCochain_mul (θ := θ) hW π s hs κ hκ hκc g h) i
    rw [TwistedVec.add_apply, add_comm] at this
    exact this
  -- the vector Artin–Schreier covering and its `G`-action
  let B' := VectorArtinSchreier p a
  have : Algebra.Etale R B' := Algebra.Etale.comp R A.obj _
  have : Module.Finite R B' := Module.Finite.trans A.obj _
  let A' : FiniteEtale.{u} R := FiniteEtale.of R B'
  -- a geometric point over `x₀`
  have hroot : ∀ i, ∃ t : Ω, t ^ p - t + x₀a (a i) = 0 := by
    intro i
    obtain ⟨t, ht⟩ := IsSepClosed.exists_root
      (Polynomial.X ^ p - Polynomial.X + Polynomial.C (x₀a (a i)) : Polynomial Ω) (by
        rw [Polynomial.degree_eq_natDegree (ExposeXI.ArtinSchreier.monic hp.out _).ne_zero,
          ExposeXI.ArtinSchreier.natDegree_eq hp.out]
        exact_mod_cast hp.out.ne_zero)
      (separable_artinSchreier p _)
    refine ⟨t, ?_⟩
    simpa using ht
  choose t ht using hroot
  let x₀' : A'.obj →ₐ[R] Ω := vasLiftAlgHom p a x₀a t ht
  have hx₀' : x₀'.comp (IsScalarTower.toAlgHom R A.obj B') = x₀a :=
    AlgHom.ext fun b ↦ vasLiftAlgHom_algebraMap p a x₀a t ht b
  exact exists_lift_of_principal R Ω ψ hψ π hα x₀ hx₀ A' (IsScalarTower.toAlgHom R A.obj B')
    (vasSemilinearAut p (ρH.comp π) (CmH.comp π) a u hu hmul)
    (fun g ↦ AlgHom.ext fun b ↦
      vasSemilinearHom_algebraMap p (ρH.comp π) (CmH.comp π) a u hu g b)
    (fun x y ↦ existsUnique_comp_vasSemilinearAut p ρH CmH π a u hu hmul Ω hH
      (fun σ ↦ ⟨s σ, hs σ⟩) χ (fun z hz i ↦ by
        exact congrFun (liftCochain_of_mem_ker π s κ hθ hz) i)
      (fun z hz h0 ↦ by
        rw [hχ z hz, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff,
          MulEquiv.map_eq_one_iff] at h0
        exact congrArg Subtype.val h0)
      (fun k ↦ ⟨(e (Multiplicative.ofAdd k) : G), (e _).2, by
        rw [hχ _ (e _).2]
        simp⟩) x y)
    x₀' hx₀'

end Lift

section KerCoord

variable (p : ℕ) [Fact p.Prime] {G H : Type*} [Group G] [Group H] (π : G →* H) {r : ℕ}
  (e : Multiplicative (Fin r → ZMod p) ≃* π.ker)

/-- The coordinates in `(ℤ/p)ʳ` of an element of the kernel (`0` outside it). -/
noncomputable def kerCoord (g : G) : Fin r → ZMod p :=
  open Classical in if h : g ∈ π.ker then Multiplicative.toAdd (e.symm ⟨g, h⟩) else 0

lemma kerCoord_of_mem {z : G} (hz : z ∈ π.ker) :
    kerCoord p π e z = Multiplicative.toAdd (e.symm ⟨z, hz⟩) := by
  simp [kerCoord, hz]

lemma kerCoord_mul {z w : G} (hz : z ∈ π.ker) (hw : w ∈ π.ker) :
    kerCoord p π e (z * w) = kerCoord p π e z + kerCoord p π e w := by
  rw [kerCoord_of_mem p π e (mul_mem hz hw), kerCoord_of_mem p π e hz, kerCoord_of_mem p π e hw,
    ← toAdd_mul, ← map_mul]
  rfl

lemma kerCoord_conj (g : G) {z : G} (hz : z ∈ π.ker) :
    kerCoord p π e (g * z * g⁻¹) = conjMat p e g *ᵥ kerCoord p π e z := by
  have hgz : g * z * g⁻¹ ∈ π.ker := (MonoidHom.normal_ker π).conj_mem z hz g
  rw [conjMat_mulVec, conjRep_apply, kerCoord_of_mem p π e hz, kerCoord_of_mem p π e hgz]
  have h2 : MulAut.conjNormal g (e (Multiplicative.ofAdd (Multiplicative.toAdd
      (e.symm ⟨z, hz⟩)))) = ⟨g * z * g⁻¹, hgz⟩ := by
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
    exact Subtype.ext (MulAut.conjNormal_apply g ⟨z, hz⟩)
  rw [h2]

lemma kerCoord_eq_zero {z : G} (hz : z ∈ π.ker) (h0 : kerCoord p π e z = 0) : z = 1 := by
  rw [kerCoord_of_mem p π e hz, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff,
    MulEquiv.map_eq_one_iff] at h0
  exact congrArg Subtype.val h0

lemma exists_kerCoord_eq (k : Fin r → ZMod p) : ∃ z ∈ π.ker, kerCoord p π e z = k :=
  ⟨(e (Multiplicative.ofAdd k) : G), (e _).2, by rw [kerCoord_of_mem p π e (e _).2]; simp⟩

end KerCoord

section Split

open CategoryTheory PreGaloisCategory CommAlgCat AffineLinePGroups

variable (p : ℕ) [hp : Fact p.Prime]

/-- Lifts through a split extension by `(ℤ/p)ʳ`, from an invariant `a ∈ (B ⊗ (ℤ/p)ʳ)^H`: the
vector Artin–Schreier covering of `a` with the action `(v, σ) : Y ↦ Cm(σ)⁻¹(Y + v)` gives a lift
`ψ_a`, and if `ker ψ ⊆ ker ψ_a` then `a ∈ ℘(Bʳ)` (domination). -/
theorem exists_lift_of_split (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    {H G : Type u} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    (π : G →* H) {r : ℕ} (e : Multiplicative (Fin r → ZMod p) ≃* π.ker)
    (s₀ : H →* G) (hs₀ : ∀ σ, π (s₀ σ) = σ)
    {P : (FiniteEtale.{u} R)ᵒᵖ} {α : H →* (Aut P)ᵐᵒᵖ}
    (hα : ExposeV.IsPrincipalHomogeneous (ExposeV.fiberFunctor R Ω) α)
    (x₀ : (ExposeV.fiberFunctor R Ω).obj P) (hx₀ : ExposeV.torsorHom hα x₀ = ψ.toMonoidHom)
    [CharP P.unop.obj p]
    (CmH : H →* Matrix (Fin r) (Fin r) (ZMod p)) (hCmH : CmH.comp π = conjMat p e)
    (a : Fin r → P.unop.obj)
    (ha : ∀ σ, castMat p P.unop.obj (CmH σ) *ᵥ
      (fun i ↦ (autOpMulEquivAlgEquiv P.unop (α σ)) (a i)) = a) :
    ∃ ψ' : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G,
      π.comp ψ'.toMonoidHom = ψ.toMonoidHom ∧
      (ψ.toMonoidHom.ker ≤ ψ'.toMonoidHom.ker →
        ∃ b : Fin r → P.unop.obj, ∀ i, b i ^ p - b i + a i = 0) := by
  classical
  have : CharP Ω p := charP_of_algebra p R Ω
  let A := P.unop
  let ρH : H →* (A.obj ≃ₐ[R] A.obj) := (autOpMulEquivAlgEquiv A).toMonoidHom.comp α
  have hH : ∀ x y : A.obj →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y := hα
  let x₀a : A.obj →ₐ[R] Ω := x₀
  have hfix : ∀ (σ : H) (v : Fin r → ZMod p),
      (fun i ↦ ρH σ (ZMod.castHom (dvd_refl p) A.obj (v i))) =
        fun i ↦ ZMod.castHom (dvd_refl p) A.obj (v i) := fun σ v ↦ funext fun i ↦
    RingHom.congr_fun (RingHom.ext_zmod (((ρH σ) : A.obj →+* A.obj).comp
      (ZMod.castHom (dvd_refl p) A.obj)) (ZMod.castHom (dvd_refl p) A.obj)) _
  have hcastMat : ∀ (M : Matrix (Fin r) (Fin r) (ZMod p)) (v : Fin r → ZMod p),
      (castMat p A.obj M *ᵥ fun i ↦ ZMod.castHom (dvd_refl p) A.obj (v i)) =
        fun i ↦ ZMod.castHom (dvd_refl p) A.obj ((M *ᵥ v) i) := fun M v ↦ funext fun i ↦
    (RingHom.map_mulVec (ZMod.castHom (dvd_refl p) A.obj) M v i).symm
  have hs₀1 : s₀ 1 = 1 := map_one s₀
  have hmemk : ∀ g : G, g * (s₀ (π g))⁻¹ ∈ π.ker := fun g ↦ by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs₀, mul_inv_cancel]
  let u : G → Fin r → A.obj := fun g i ↦
    ZMod.castHom (dvd_refl p) A.obj (kerCoord p π e (g * (s₀ (π g))⁻¹) i)
  have hCmπ : ∀ g, CmH (π g) = conjMat p e (s₀ (π g)) := fun g ↦ by
    rw [← hs₀ (π g), ← MonoidHom.comp_apply, hCmH, hs₀]
  have hu : ∀ g i, u g i ^ p - u g i = a i - vecAct p (ρH.comp π) (CmH.comp π) g a i := by
    intro g i
    have : vecAct p (ρH.comp π) (CmH.comp π) g a = a := ha (π g)
    rw [this, sub_self, ExposeXI.ArtinSchreier.castHom_pow, sub_self]
  have hmul : ∀ g h, u (g * h) = u g + vecAct p (ρH.comp π) (CmH.comp π) g (u h) := by
    intro g h
    have hsplit : g * h * (s₀ (π (g * h)))⁻¹ =
        g * (s₀ (π g))⁻¹ * (s₀ (π g) * (h * (s₀ (π h))⁻¹) * (s₀ (π g))⁻¹) := by
      rw [map_mul, map_mul]
      group
    have hconj := kerCoord_conj p π e (s₀ (π g)) (hmemk h)
    have hk := kerCoord_mul p π e (hmemk g)
      ((MonoidHom.normal_ker π).conj_mem _ (hmemk h) (s₀ (π g)))
    change (fun i ↦ ZMod.castHom (dvd_refl p) A.obj (kerCoord p π e (g * h * (s₀ (π (g * h)))⁻¹) i))
      = u g + castMat p A.obj (CmH (π g)) *ᵥ fun i ↦ ρH (π g) (u h i)
    rw [hfix, hcastMat, hCmπ, hsplit, hk, hconj]
    funext i
    simp [u]
  -- the vector Artin–Schreier covering and its `G`-action
  let B' := VectorArtinSchreier p a
  have : Algebra.Etale R B' := Algebra.Etale.comp R A.obj _
  have : Module.Finite R B' := Module.Finite.trans A.obj _
  let A' : FiniteEtale.{u} R := FiniteEtale.of R B'
  have hroot : ∀ i, ∃ t : Ω, t ^ p - t + x₀a (a i) = 0 := by
    intro i
    obtain ⟨t, ht⟩ := IsSepClosed.exists_root
      (Polynomial.X ^ p - Polynomial.X + Polynomial.C (x₀a (a i)) : Polynomial Ω) (by
        rw [Polynomial.degree_eq_natDegree (ExposeXI.ArtinSchreier.monic hp.out _).ne_zero,
          ExposeXI.ArtinSchreier.natDegree_eq hp.out]
        exact_mod_cast hp.out.ne_zero)
      (separable_artinSchreier p _)
    refine ⟨t, ?_⟩
    simpa using ht
  choose t ht using hroot
  let x₀' : A'.obj →ₐ[R] Ω := vasLiftAlgHom p a x₀a t ht
  have hx₀' : x₀'.comp (IsScalarTower.toAlgHom R A.obj B') = x₀a :=
    AlgHom.ext fun b ↦ vasLiftAlgHom_algebraMap p a x₀a t ht b
  obtain ⟨ψ', hψ', hdom⟩ := exists_lift_of_principal' R Ω ψ hψ π hα x₀ hx₀ A'
    (IsScalarTower.toAlgHom R A.obj B')
    (vasSemilinearAut p (ρH.comp π) (CmH.comp π) a u hu hmul)
    (fun g ↦ AlgHom.ext fun b ↦
      vasSemilinearHom_algebraMap p (ρH.comp π) (CmH.comp π) a u hu g b)
    (fun x y ↦ existsUnique_comp_vasSemilinearAut p ρH CmH π a u hu hmul Ω hH
      (fun σ ↦ ⟨s₀ σ, hs₀ σ⟩) (kerCoord p π e) (fun z hz i ↦ by
        change ZMod.castHom (dvd_refl p) A.obj (kerCoord p π e (z * (s₀ (π z))⁻¹) i) = _
        rw [(MonoidHom.mem_ker).mp hz, hs₀1, inv_one, mul_one])
      (fun z hz h0 ↦ kerCoord_eq_zero p π e hz h0) (exists_kerCoord_eq p π e) x y)
    x₀' hx₀'
  refine ⟨ψ', hψ', fun hker ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := hdom hker
  refine ⟨fun i ↦ φ (vasRoot p a i), fun i ↦ ?_⟩
  have h := congrArg φ (vasRoot_rel p a i)
  rw [map_add, map_sub, map_pow, map_zero] at h
  have hφa : φ (algebraMap A.obj B' (a i)) = a i := by
    have := congrArg (fun f ↦ f (a i)) hφ
    exact this
  rw [hφa] at h
  exact h

end Split

end SerrePKernel

end SGA.SGA1.ExposeXIII
