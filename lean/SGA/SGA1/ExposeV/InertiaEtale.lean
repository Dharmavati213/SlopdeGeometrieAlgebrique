/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.SmoothDescent
import SGA.SGA1.ExposeII.FieldEtale
import SGA.Foundations.CompleteLocalQuasiFinite
import SGA.Foundations.Formal.CompletionNoetherian
import SGA.SGA1.ExposeV.PrincipalCovering

/-!
# SGA 1, Exposé V, V.2.2: étaleness of `X/H` at a point whose inertia group lies in `H`

Let `B` be noetherian, `A` a finite `B`-algebra with an action of a finite group `G` such that
`B = A^G`, `Q` a prime of `A` over `P`, and `H ≤ G` (SGA: `Y` locally noetherian, `X` finite over
`Y`, `X' = X/H`). The final statement is `decompositionInertiaEtaleStatement`.

* (i) If `H ⊇ G_d(Q)`, then `A^H` is étale over `B` at `Q' = Q ∩ A^H` and `κ(Q') = κ(P)`
  (`isEtaleAt_and_bijective_of_stabilizer_le`): by EGA IV 17.6.3 this is SGA's statement that
  `𝒪_P → 𝒪_{Q'}` induces an isomorphism on completions. As in SGA we pass to the completion
  `B̂` of `B_P` (`completionAt`): `B̂ ⊗_B A` is finite over the complete local ring `B̂`, so it
  splits off its local factors (`IsLocalRing.exists_isIdempotentElem_forall_le_of_finite`), and the
  local factor of `(B̂ ⊗_B A)^H` at the point over `Q'` is `B̂`
  (`exists_isIdempotentElem_fixedPoints`, where SGA describes `A` as the induced ring
  `Hom_{G_d}(G, A₀)`). Étaleness at the point descends along the flat `B → B̂`
  (`isEtaleAt_of_isEtaleAt_tensorProduct`, via II.4.13).
* (ii) If `H ⊇ G_i(Q)`, then `A^H` is étale over `B` at `Q'` (`isEtaleAt_of_inertia_le`). SGA
  passes to a finite flat extension making the residue extension trivial. We use instead that
  `G_d/G_i` acts on `A^{G_i}` with invariants `A^{G_d}` and trivial inertia at `Q ∩ A^{G_i}`
  (`mem_inertia_of_forall_fixedPoints`), so that by V.2.3
  (`exists_etale_localization_of_inertia_eq_bot`) and (i), `A^{G_i}` is étale over `B` at
  `Q ∩ A^{G_i}` (`isEtaleAt_fixedPoints_inertia`); the general case follows by applying this to `H`
  acting on `A` over `A^H`, since étaleness at a point descends along a morphism étale at the point
  (`isEtaleAt_of_isEtaleAt_of_isEtaleAt`).
-/

universe u

open Algebra TensorProduct IsLocalRing Polynomial
open scoped Pointwise

namespace SGA.SGA1.ExposeV

section PointwiseDescent

/-- Flatness descends along a faithfully flat extension of the algebra: if `S → T` is faithfully
flat and `T` is flat over `R`, then `S` is flat over `R`. -/
theorem flat_of_faithfullyFlat_tower (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Module.FaithfullyFlat S T]
    [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have hT : Function.Injective (N.subtype.lTensor T) :=
    Module.Flat.iff_lTensor_injectiveₛ.mp inferInstance N
  let eN := AlgebraTensorModule.cancelBaseChange R S T T N
  let eP := AlgebraTensorModule.cancelBaseChange R S T T P
  have key : ⇑((N.subtype.baseChange S).lTensor T) = eP.symm ∘ (N.subtype.lTensor T) ∘ eN := by
    funext x
    apply eP.injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
      | tmul s n => simp [eN, eP]
  have : Function.Injective ((N.subtype.baseChange S).lTensor T) := by
    rw [key]
    exact eP.symm.injective.comp (hT.comp eN.injective)
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective S T _).mp this

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Étaleness at a point descends along a flat base change: let `T` be flat over `R`, `S` finitely
presented over `R` and `Q'` a prime of `T ⊗_R S` over the prime `Q` of `S`. If `T ⊗_R S` is étale
over `T` at `Q'`, then `S` is étale over `R` at `Q` (smoothness descends by II.4.13, and the
vanishing of `Ω¹` at the point descends as `Ω¹` commutes with base change). -/
theorem isEtaleAt_of_isEtaleAt_tensorProduct (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Module.Flat R T] [FinitePresentation R S]
    (Q' : Ideal (T ⊗[R] S)) [Q'.IsPrime] [IsEtaleAt T Q'] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q'.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) = Q) :
    IsEtaleAt R Q := by
  have hFE := (FormallyEtale.iff_formallyUnramified_and_formallySmooth (R := T)
    (A := Localization.AtPrime Q')).mp ‹_›
  have : IsSmoothAt T Q' := hFE.2
  have : IsSmoothAt R Q := ExposeII.isSmoothAt_of_isSmoothAt_tensorProduct R S T Q' Q hQ
  have : IsUnramifiedAt R Q := by
    have hQ'' : PrimeSpectrum.comap (algebraMap S (T ⊗[R] S)) ⟨Q', ‹_›⟩ = ⟨Q, ‹_›⟩ :=
      PrimeSpectrum.ext hQ
    have hur : (⟨Q', ‹_›⟩ : PrimeSpectrum (T ⊗[R] S)) ∈ unramifiedLocus T (T ⊗[R] S) := hFE.1
    rw [unramifiedLocus_eq_compl_support] at hur
    change (⟨Q, ‹_›⟩ : PrimeSpectrum S) ∈ unramifiedLocus R S
    rw [unramifiedLocus_eq_compl_support, ← hQ'']
    have : Module.Flat S (T ⊗[R] S) :=
      .of_linearEquiv (Algebra.TensorProduct.commRight R S T).symm.toLinearEquiv
    exact ExposeII.notMem_support_of_notMem_support_baseChange _ _
      (by rwa [(KaehlerDifferential.tensorKaehlerEquiv R T S (T ⊗[R] S)).support_eq])
  exact FormallyEtale.of_formallyUnramified_and_formallySmooth

end BaseChange

/-- Étaleness at a point descends along a morphism étale at the point: let `R → S → S'` with `S`
finitely presented over `R` and `S'` finitely presented over `S`, and `q'` a prime of `S'` over the
prime `q` of `S`. If `S'` is étale at `q'` over both `S` and `R`, then `S` is étale over `R` at
`q`: `S_q → S'_{q'}` is faithfully flat and formally étale, so flatness and the vanishing of `Ω¹`
descend. -/
theorem isEtaleAt_of_isEtaleAt_of_isEtaleAt {R S S' : Type u} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [FinitePresentation R S] [FinitePresentation S S'] [FinitePresentation R S']
    (q : Ideal S) (q' : Ideal S') [q.IsPrime] [q'.IsPrime] [q'.LiesOver q]
    [IsEtaleAt S q'] [IsEtaleAt R q'] : IsEtaleAt R q := by
  let := Localization.AtPrime.algebraOfLiesOver q q'
  have hS := (FormallyEtale.iff_formallyUnramified_and_formallySmooth (R := S)
    (A := Localization.AtPrime q')).mp ‹_›
  have hR := (FormallyEtale.iff_formallyUnramified_and_formallySmooth (R := R)
    (A := Localization.AtPrime q')).mp ‹_›
  have : IsSmoothAt S q' := hS.2
  have : IsSmoothAt R q' := hR.2
  have : Module.Flat S (Localization.AtPrime q') := ExposeII.IsSmoothAt.flat_localization q'
  have : Module.Flat R (Localization.AtPrime q') := ExposeII.IsSmoothAt.flat_localization q'
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime q') :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl _).mpr ‹_›
  have : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime q') :=
    .of_flat_of_isLocalHom
  have : IsScalarTower R (Localization.AtPrime q) (Localization.AtPrime q') :=
    .to₁₃₄ _ S _ _
  have hflat : Module.Flat R (Localization.AtPrime q) :=
    flat_of_faithfullyFlat_tower R (Localization.AtPrime q) (Localization.AtPrime q')
  have : FormallyEtale (Localization.AtPrime q) (Localization.AtPrime q') :=
    .localization_base q.primeCompl
  have : FormallyUnramified R (Localization.AtPrime q') := hR.1
  have : IsUnramifiedAt R q := by
    change FormallyUnramified R (Localization.AtPrime q)
    constructor
    have : Subsingleton (Localization.AtPrime q' ⊗[Localization.AtPrime q]
        Ω[Localization.AtPrime q⁄R]) :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (Localization.AtPrime q)
        (Localization.AtPrime q')).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality (Localization.AtPrime q)
      (Localization.AtPrime q') _
  exact ExposeII.isEtaleAt_of_flat_of_isUnramifiedAt q hflat

end PointwiseDescent

section Idempotent

variable {T : Type*} [CommRing T]

lemma eq_zero_of_isIdempotentElem_of_forall_mem {u : T} (hu : IsIdempotentElem u)
    (h : ∀ P : Ideal T, P.IsPrime → u ∈ P) : u = 0 :=
  hu.eq_zero_of_isNilpotent ((mem_nilradical).mp (by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    exact fun P hP ↦ h P hP))

/-- Two idempotents `e`, `e'` cutting out the local factors at distinct maximal ideals `M`, `M'`
(every prime not containing `e` is contained in `M`, and similarly for `e'`) are orthogonal. -/
lemma mul_eq_zero_of_isIdempotentElem {e e' : T} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') {M M' : Ideal T} [M.IsMaximal] [M'.IsMaximal] (heM : e ∉ M)
    (hle : ∀ P : Ideal T, P.IsPrime → e ∉ P → P ≤ M)
    (hle' : ∀ P : Ideal T, P.IsPrime → e' ∉ P → P ≤ M') (hMM' : M ≠ M') : e * e' = 0 := by
  have he'M : e' ∈ M := by
    by_contra h
    exact hMM' ((Ideal.IsMaximal.eq_of_le ‹M.IsMaximal› (Ideal.IsMaximal.ne_top ‹_›)
      (hle' M inferInstance h)))
  refine eq_zero_of_isIdempotentElem_of_forall_mem (he.mul he') fun P hP ↦ ?_
  by_cases heP : e ∈ P
  · exact P.mul_mem_right _ heP
  · have hPM := hle P hP heP
    have hv : e * (1 - e') ∉ P := fun h ↦ by
      rcases (Ideal.IsMaximal.isPrime ‹M.IsMaximal›).mem_or_mem (hPM h) with h | h
      · exact heM h
      · exact (Ideal.IsMaximal.ne_top ‹M.IsMaximal›)
          ((Ideal.eq_top_iff_one _).mpr (by simpa using M.add_mem h he'M))
    have h0 : e * e' * (e * (1 - e')) = 0 := by
      have : e' * (1 - e') = 0 := by rw [mul_sub, mul_one, he'.eq, sub_self]
      calc e * e' * (e * (1 - e')) = (e * e) * (e' * (1 - e')) := by ring
        _ = 0 := by rw [this, mul_zero]
    exact (hP.mem_or_mem (h0 ▸ P.zero_mem)).resolve_right hv

/-- Two idempotents cutting out the local factor at the same maximal ideal are equal. -/
lemma eq_of_isIdempotentElem {e e' : T} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    {M : Ideal T} (heM : e ∉ M) (hle : ∀ P : Ideal T, P.IsPrime → e ∉ P → P ≤ M) (he'M : e' ∉ M)
    (hle' : ∀ P : Ideal T, P.IsPrime → e' ∉ P → P ≤ M) : e = e' := by
  have key : ∀ {e e' : T}, IsIdempotentElem e → IsIdempotentElem e' → e ∉ M →
      (∀ P : Ideal T, P.IsPrime → e ∉ P → P ≤ M) → e' ∉ M → e = e * e' := by
    intro e e' he he' heM hle he'M
    have := eq_zero_of_isIdempotentElem_of_forall_mem (he.mul he'.one_sub) fun P hP ↦ by
      by_cases heP : e ∈ P
      · exact P.mul_mem_right _ heP
      · have he'P : e' ∉ P := fun h ↦ he'M (hle P hP heP h)
        have : e' * (1 - e') ∈ P := by rw [mul_sub, mul_one, he'.eq, sub_self]; exact P.zero_mem
        exact P.mul_mem_left _ ((hP.mem_or_mem this).resolve_left he'P)
    rw [mul_sub, mul_one, sub_eq_zero] at this
    exact this
  rw [key he he' heM hle he'M, mul_comm, ← key he' he he'M hle' heM]

/-- `y (1 - ∏ (1 - aᵢ)) = 0` as soon as `y aᵢ = 0` for all `i`. -/
lemma mul_one_sub_prod_eq_zero {ι : Type*} (s : Finset ι) (a : ι → T) (y : T)
    (h : ∀ i ∈ s, y * a i = 0) : y * (1 - ∏ i ∈ s, (1 - a i)) = 0 := by
  classical
  suffices y * ∏ i ∈ s, (1 - a i) = y by rw [mul_sub, mul_one, this, sub_self]
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ← mul_assoc, mul_sub, mul_one, h i (Finset.mem_insert_self i s),
      sub_zero, ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)]

lemma isIdempotentElem_one_sub_prod {ι : Type*} (s : Finset ι) (a : ι → T)
    (h : ∀ i ∈ s, IsIdempotentElem (a i)) : IsIdempotentElem (1 - ∏ i ∈ s, (1 - a i)) := by
  refine IsIdempotentElem.one_sub ?_
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsIdempotentElem.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).one_sub.mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

end Idempotent

section Split

variable {R T : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra R T] [Module.Finite R T]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G R T]
  [Algebra.IsInvariant R T G]

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite G]
  [Algebra.IsInvariant R T G] in
lemma comap_eq_maximalIdeal_of_isMaximal (N : Ideal T) [N.IsMaximal] :
    N.comap (algebraMap R T) = maximalIdeal R :=
  eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N)

/-- The splitting of a finite algebra over a complete local ring, with a group action (proof of
V.2.2): let `R` be a complete noetherian local ring, `T` a finite `R`-algebra, `G` a finite group
acting on `T` with `T^G = R`, `M` a maximal ideal of `T` and `H ≤ G` containing the decomposition
group `G_d(M)`. Then there is an `H`-invariant idempotent `f ∉ M` such that `R → T^H f`,
`r ↦ r f`, is bijective: the local factor of `T^H` at `M ∩ T^H` is `R`. (`f` is the sum of the
idempotents cutting out the local factors of `T` at the `H`-translates of `M`.) -/
theorem exists_isIdempotentElem_fixedPoints (hinj : Function.Injective (algebraMap R T))
    (M : Ideal T) [M.IsMaximal] (H : Subgroup G) (hH : MulAction.stabilizer G M ≤ H) :
    ∃ f : T, IsIdempotentElem f ∧ f ∉ M ∧ (∀ h ∈ H, h • f = f) ∧
      (∀ x : T, (∀ h ∈ H, h • x = x) → ∃ r : R, x * f = algebraMap R T r * f) ∧
      ∀ r : R, algebraMap R T r * f = 0 → r = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨e, he, heM, hle⟩ := IsLocalRing.exists_isIdempotentElem_forall_le_of_finite (A := R) T M
  have hmax : ∀ g : G, (g • M).IsMaximal := fun g ↦ by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ (MulSemiringAction.toRingEquiv G T g⁻¹).surjective
  have hge : ∀ g : G, IsIdempotentElem (g • e) ∧ g • e ∉ g • M ∧
      ∀ P : Ideal T, P.IsPrime → g • e ∉ P → P ≤ g • M := by
    intro g
    refine ⟨by rw [IsIdempotentElem, ← smul_mul', he.eq], fun h ↦ heM
      (Ideal.smul_mem_pointwise_smul_iff.mp h), fun P hP hgP ↦ ?_⟩
    rw [Ideal.subset_pointwise_smul_iff]
    exact hle _ (Ideal.IsPrime.smul g⁻¹) fun h ↦ hgP (Ideal.mem_inv_pointwise_smul_iff.mp h)
  -- orthogonality and stability
  have hK1 : ∀ g : G, g ∉ MulAction.stabilizer G M → e * (g • e) = 0 := by
    intro g hg
    have := hmax g
    exact mul_eq_zero_of_isIdempotentElem he (hge g).1 heM hle (hge g).2.2
      fun h ↦ hg (MulAction.mem_stabilizer_iff.mpr h.symm)
  have hK2 : ∀ g ∈ MulAction.stabilizer G M, g • e = e := by
    intro g hg
    have hg' : g • M = M := hg
    have h2 := (hge g).2
    rw [hg'] at h2
    exact eq_of_isIdempotentElem (hge g).1 he h2.1 h2.2 heM hle
  let f : T := 1 - ∏ h : H, (1 - (h : G) • e)
  have hf : IsIdempotentElem f :=
    isIdempotentElem_one_sub_prod _ _ fun h _ ↦ (hge h).1
  have h1e : 1 - e ∈ M := by
    have : e * (1 - e) ∈ M := by rw [mul_sub, mul_one, he.eq, sub_self]; exact M.zero_mem
    exact ((Ideal.IsMaximal.isPrime ‹_›).mem_or_mem this).resolve_left heM
  have hfM : f ∉ M := by
    intro hf
    have hprod : ∏ h : H, (1 - (h : G) • e) ∈ M :=
      (Ideal.IsPrime.prod_mem_iff (hp := Ideal.IsMaximal.isPrime ‹_›)).mpr
        ⟨1, Finset.mem_univ _, by simpa using h1e⟩
    exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr
      (by simpa [f] using M.add_mem hf hprod))
  have hfH : ∀ k ∈ H, k • f = f := by
    intro k hk
    simp only [f, smul_sub, smul_one, Finset.smul_prod', smul_smul]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨k, hk⟩ : H)) _ _ fun h ↦ rfl
  have hef : e * f = e := by
    have : e * ∏ h : H, (1 - (h : G) • e) = 0 := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ 1), ← mul_assoc]
      simp [mul_sub, he.eq]
    simp [f, mul_sub, this]
  have hF5 : ∀ y : T, (∀ h ∈ H, y * (h • e) = 0) → y * f = 0 := fun y hy ↦
    mul_one_sub_prod_eq_zero _ _ y fun h _ ↦ hy h h.2
  refine ⟨f, hf, hfM, hfH, fun x hx ↦ ?_, fun r hr ↦ ?_⟩
  · -- the coset sum
    let D := MulAction.stabilizer G M
    have : Fintype (G ⧸ D) := Fintype.ofFinite _
    let y := x * e
    have hy : ∀ d ∈ D, d • y = y := fun d hd ↦ by
      simp only [y, smul_mul', hx d (hH hd), hK2 d hd]
    let z : T := ∑ c : G ⧸ D, c.out • y
    have hze : z * e = y := by
      simp only [z, Finset.sum_mul]
      have hmem : ∀ c : G ⧸ D, c = ((1 : G) : G ⧸ D) ↔ c.out ∈ D := fun c ↦ by
        conv_lhs => rw [← QuotientGroup.out_eq' c]
        rw [QuotientGroup.eq, mul_one, inv_mem_iff]
      rw [Finset.sum_eq_single ((1 : G) : G ⧸ D)]
      · rw [hy _ ((hmem _).mp rfl), mul_assoc, he.eq]
      · intro c _ hc
        have hcD : c.out ∉ D := fun h ↦ hc ((hmem c).mpr h)
        simp only [y, smul_mul', mul_assoc, mul_comm (c.out • e) e, hK1 _ hcD, mul_zero]
      · simp
    have hzG : ∀ g : G, g • z = z := by
      intro g
      simp only [z, Finset.smul_sum, smul_smul]
      refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun c ↦ ?_
      obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul D (g * c.out)
      have hc : (MulAction.toPerm g c : G ⧸ D) = (g * c.out : G) := by
        conv_lhs => rw [← QuotientGroup.out_eq' c]
        rfl
      rw [hc, hd, mul_smul (g * c.out), hy d d.2, mul_smul]
    obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) z hzG
    refine ⟨r, ?_⟩
    rw [← sub_eq_zero, ← sub_mul]
    refine hF5 _ fun h hh ↦ ?_
    have h0 : (x - algebraMap R T r) * e = 0 := by rw [sub_mul, hr, hze, sub_self]
    have := congr_arg (h • ·) h0
    simp only [smul_mul', smul_sub, hx h hh, smul_algebraMap, smul_zero] at this
    exact this
  · -- injectivity
    have hre : algebraMap R T r * e = 0 := by rw [← hef, ← mul_assoc, mul_right_comm, hr, zero_mul]
    have hrg : ∀ g : G, algebraMap R T r * (g • e) = 0 := fun g ↦ by
      have := congr_arg (g • ·) hre
      simpa only [smul_mul', smul_algebraMap, smul_zero] using this
    have h0 := mul_one_sub_prod_eq_zero Finset.univ (fun g : G ↦ g • e) (algebraMap R T r)
      fun g _ ↦ hrg g
    have hunit : IsUnit (1 - ∏ g : G, (1 - g • e)) := by
      by_contra hnu
      obtain ⟨N, hN, hle'⟩ := Ideal.exists_le_maximal _ ((Ideal.span_singleton_ne_top hnu))
      have hN' := hle' (Ideal.mem_span_singleton_self _)
      obtain ⟨g, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R T G M N (by
        change M.comap _ = N.comap _
        rw [comap_eq_maximalIdeal_of_isMaximal, comap_eq_maximalIdeal_of_isMaximal])
      have h1 : 1 - g • e ∈ g • M := by
        have : g • e * (1 - g • e) ∈ g • M := by
          rw [mul_sub, mul_one, (hge g).1.eq, sub_self]; exact Ideal.zero_mem _
        exact ((Ideal.IsMaximal.isPrime hN).mem_or_mem this).resolve_left (hge g).2.1
      have hprod : ∏ g' : G, (1 - g' • e) ∈ g • M :=
        (Ideal.IsPrime.prod_mem_iff (hp := Ideal.IsMaximal.isPrime hN)).mpr
          ⟨g, Finset.mem_univ _, h1⟩
      exact (Ideal.IsMaximal.ne_top hN) ((Ideal.eq_top_iff_one _).mpr
        (by simpa using Ideal.add_mem _ hN' hprod))
    exact hinj (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp h0)

end Split

section FixedPointsBaseChange

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
  [Algebra C A] [IsScalarTower B C A] {G : Type*} [Group G] [MulSemiringAction G A]
  [SMulCommClass G B A] (H : Subgroup G)

lemma map_toAlgHom_eq_lTensor (B' : Type*) [CommRing B'] [Algebra B B'] (y : B' ⊗[B] C) :
    Algebra.TensorProduct.map (AlgHom.id B' B') (IsScalarTower.toAlgHom B C A) y =
      (IsScalarTower.toAlgHom B C A).toLinearMap.lTensor B' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- V.1.9 for the invariants of a subgroup: if `C → A` identifies `C` with `A^H`, then for `B'`
flat over `B`, every `H`-invariant element of `B' ⊗_B A` comes from `B' ⊗_B C`. -/
theorem exists_map_eq_of_forall_smul_eq (B' : Type*) [CommRing B'] [Algebra B B']
    [Module.Flat B B'] [Finite G]
    (hCH : ∀ a : A, a ∈ Set.range (algebraMap C A) ↔ ∀ h ∈ H, h • a = a)
    (x : B' ⊗[B] A)
    (hx : ∀ h ∈ H, Algebra.TensorProduct.map (AlgHom.id B B')
      (MulSemiringAction.toAlgHom B A h) x = x) :
    ∃ y : B' ⊗[B] C,
      Algebra.TensorProduct.map (AlgHom.id B' B') (IsScalarTower.toAlgHom B C A) y = x := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hex : Function.Exact (IsScalarTower.toAlgHom B C A).toLinearMap
      (invariantsDefect (B := B) (A := A) H) := by
    intro a
    constructor
    · intro ha
      exact (hCH a).mpr fun h hh ↦ sub_eq_zero.mp (congr_fun ha ⟨h, hh⟩)
    · rintro ⟨c, rfl⟩
      ext h
      rw [invariantsDefect_apply, Pi.zero_apply, sub_eq_zero]
      exact (hCH _).mp ⟨c, rfl⟩ h h.2
  have hex' := Module.Flat.lTensor_exact B' hex
  have h0 : (invariantsDefect (B := B) (A := A) H).lTensor B' x = 0 := by
    apply (TensorProduct.piRight B B B' fun _ : H ↦ A).injective
    ext h
    rw [lTensor_invariantsDefect_apply, map_zero, Pi.zero_apply]
    exact sub_eq_zero.mpr (hx h h.2)
  obtain ⟨y, hy⟩ := (hex' x).mp h0
  exact ⟨y, (map_toAlgHom_eq_lTensor B' y).trans hy⟩

end FixedPointsBaseChange

section Decomposition

variable {B A C : Type u} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
  [Algebra C A] [IsScalarTower B C A] {G : Type*} [Group G] [Finite G] [MulSemiringAction G A]
  [SMulCommClass G B A] [Algebra.IsInvariant B A G] [IsNoetherianRing B] [Module.Finite B A]

omit [Finite G] [Algebra.IsInvariant B A G] [IsNoetherianRing B] [Module.Finite B A] in
lemma comap_includeRight_smul (Bh : Type*) [CommRing Bh] [Algebra B Bh] (g : G)
    (I : Ideal (Bh ⊗[B] A)) :
    letI := tensorAction (B := B) (A := A) Bh G
    (g • I).comap (Algebra.TensorProduct.includeRight : A →ₐ[B] Bh ⊗[B] A) =
      g • I.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] Bh ⊗[B] A) := by
  let _ := tensorAction (B := B) (A := A) Bh G
  ext a
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    tensorAction_tmul]

/-- V.2.2 (i), over a complete local ring: let `B̂` be a complete noetherian local ring, flat over
`B`, such that every element of `B̂` is congruent modulo `𝔪_B̂` to a fraction `b/s` with `s ∉ P`,
and `Q̂` a maximal ideal of `B̂ ⊗_B A` over `Q` and `𝔪_B̂`. If `H` contains the decomposition group
of `Q` and `C = A^H`, then `C` is étale over `B` at `Q ∩ C`, and every element of `C` is congruent
modulo `Q ∩ C` to a fraction `b/s` with `s ∉ P`. -/
theorem isEtaleAt_of_stabilizer_le_aux (hinj : Function.Injective (algebraMap B A))
    (H : Subgroup G) (hC : Function.Injective (algebraMap C A))
    (hCH : ∀ a : A, a ∈ Set.range (algebraMap C A) ↔ ∀ h ∈ H, h • a = a)
    (Q : Ideal A) [Q.IsPrime] (hQH : MulAction.stabilizer G Q ≤ H)
    (Bh : Type u) [CommRing Bh] [IsLocalRing Bh] [IsNoetherianRing Bh]
    [IsAdicComplete (maximalIdeal Bh) Bh] [Algebra B Bh] [Module.Flat B Bh]
    (happ : ∀ r : Bh, ∃ s b : B, s ∉ Q.comap (algebraMap B A) ∧
      algebraMap B Bh s * r - algebraMap B Bh b ∈ maximalIdeal Bh)
    (Qh : Ideal (Bh ⊗[B] A)) [Qh.IsMaximal]
    (hQhA : Qh.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] Bh ⊗[B] A) = Q)
    (hQhB : Qh.comap (algebraMap Bh (Bh ⊗[B] A)) = maximalIdeal Bh) :
    Algebra.IsEtaleAt B (Q.comap (algebraMap C A)) ∧
      ∀ c : C, ∃ s b : B, s ∉ (Q.comap (algebraMap C A)).comap (algebraMap B C) ∧
        algebraMap B C s * c - algebraMap B C b ∈ Q.comap (algebraMap C A) := by
  classical
  let _ := tensorAction (B := B) (A := A) Bh G
  have := tensorAction_smulCommClass (B := B) (A := A) Bh G
  obtain ⟨hinjh, hinvh⟩ := isInvariant_tensorProduct (B := B) (A := A) Bh G hinj
  have hstab : MulAction.stabilizer G Qh ≤ H := by
    intro g hg
    apply hQH
    change g • Q = Q
    have hg' : g • Qh = Qh := hg
    rw [← hQhA, ← comap_includeRight_smul, hg']
  obtain ⟨f, hf, hfQ, hfH, hsurj, hinj'⟩ := exists_isIdempotentElem_fixedPoints hinjh Qh H hstab
  -- the local factor of `B̂ ⊗_B C` at the point over `Q ∩ C` is `B̂`
  let ι : Bh ⊗[B] C →ₐ[Bh] Bh ⊗[B] A :=
    Algebra.TensorProduct.map (AlgHom.id Bh Bh) (IsScalarTower.toAlgHom B C A)
  have hι : Function.Injective ι := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Bh)
      (IsScalarTower.toAlgHom B C A).toLinearMap hC
    intro x y hxy
    apply this
    rw [← map_toAlgHom_eq_lTensor, ← map_toAlgHom_eq_lTensor]
    exact hxy
  have hιH : ∀ x : Bh ⊗[B] C, ∀ h ∈ H, h • ι x = ι x := by
    intro x h hh
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul b c =>
      change h • (b ⊗ₜ[B] algebraMap C A c) = b ⊗ₜ[B] algebraMap C A c
      rw [tensorAction_tmul, (hCH _).mp ⟨c, rfl⟩ h hh]
    | add x y hx hy => rw [map_add, smul_add, hx, hy]
  obtain ⟨f', hf'⟩ := exists_map_eq_of_forall_smul_eq H Bh hCH f fun h hh ↦ hfH h hh
  change ι f' = f at hf'
  have hf'i : IsIdempotentElem f' := hι (by rw [map_mul, hf', hf.eq])
  let qh := Qh.comap ι.toRingHom
  have hfq : f' ∉ qh := by
    change ι f' ∉ Qh
    rwa [hf']
  have key : ∀ x : Bh ⊗[B] C, ∃ r : Bh, x * f' = algebraMap Bh _ r * f' := by
    intro x
    obtain ⟨r, hr⟩ := hsurj (ι x) (hιH x)
    exact ⟨r, hι (by rw [map_mul, map_mul, hf', AlgHom.commutes, hr])⟩
  have key' : ∀ r : Bh, algebraMap Bh (Bh ⊗[B] C) r * f' = 0 → r = 0 := by
    intro r hr
    apply hinj' r
    rw [← hf', ← AlgHom.commutes ι, ← map_mul, hr, map_zero]
  have hone : algebraMap (Bh ⊗[B] C) (Localization.Away f') f' = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit f')).mp
      (hf'i.map _)
  have hbij : Function.Bijective (algebraMap Bh (Localization.Away f')) := by
    rw [IsScalarTower.algebraMap_eq Bh (Bh ⊗[B] C) (Localization.Away f')]
    refine ⟨fun r s hrs ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f') _).mp hrs
      have hc' : f' ^ n * algebraMap Bh (Bh ⊗[B] C) r = f' ^ n * algebraMap Bh (Bh ⊗[B] C) s :=
        hc
      have h2 : algebraMap Bh (Bh ⊗[B] C) (r - s) * f' = 0 := by
        have := congr_arg (f' * ·) hc'
        rw [← mul_assoc, ← mul_assoc, ← pow_succ', hf'i.pow_succ_eq] at this
        rw [map_sub, sub_mul, mul_comm _ f', mul_comm _ f', this, sub_self]
      exact sub_eq_zero.mp (key' _ h2)
    · obtain ⟨⟨x, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f') z
      obtain ⟨r, hr⟩ := key x
      refine ⟨r, ?_⟩
      rw [RingHom.comp_apply, IsLocalization.eq_mk'_iff_mul_eq, map_pow, hone, one_pow, mul_one,
        ← mul_one (algebraMap _ _ x), ← hone, ← map_mul, hr, map_mul, hone, mul_one]
  have : FormallyEtale Bh (Localization.Away f') :=
    FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId Bh _) hbij)
  have hqh : IsEtaleAt Bh qh :=
    (basicOpen_subset_etaleLocus_iff (R := Bh)).mpr this
      (show (⟨qh, inferInstance⟩ : PrimeSpectrum (Bh ⊗[B] C)) ∈ PrimeSpectrum.basicOpen f' from hfq)
  -- every element of `C` is congruent to an element of `B_P` modulo `Q ∩ C`
  have hq : qh.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] Bh ⊗[B] C) =
      Q.comap (algebraMap C A) := by
    ext c
    exact Ideal.ext_iff.mp hQhA (algebraMap C A c)
  have hqB : qh.comap (algebraMap Bh (Bh ⊗[B] C)) = maximalIdeal Bh := by
    ext x
    change ι (algebraMap Bh _ x) ∈ Qh ↔ _
    rw [AlgHom.commutes, ← Ideal.mem_comap, hQhB]
  have happrox : ∀ c : C, ∃ s b : B, s ∉ (Q.comap (algebraMap C A)).comap (algebraMap B C) ∧
      algebraMap B C s * c - algebraMap B C b ∈ Q.comap (algebraMap C A) := by
    intro c
    obtain ⟨r, hr⟩ := key ((1 : Bh) ⊗ₜ c)
    obtain ⟨s, b, hs, hmem⟩ := happ r
    refine ⟨s, b, ?_, ?_⟩
    · change algebraMap C A (algebraMap B C s) ∉ Q
      rw [← IsScalarTower.algebraMap_apply]
      exact hs
    have hs1 : ((algebraMap B Bh s) ⊗ₜ[B] (1 : C) : Bh ⊗[B] C) = 1 ⊗ₜ algebraMap B C s := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hb1 : ((algebraMap B Bh b) ⊗ₜ[B] (1 : C) : Bh ⊗[B] C) = 1 ⊗ₜ algebraMap B C b := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have h1 : ((1 : Bh) ⊗ₜ[B] (algebraMap B C s * c - algebraMap B C b)) * f' =
        algebraMap Bh (Bh ⊗[B] C) (algebraMap B Bh s * r - algebraMap B Bh b) * f' := by
      have e1 : ((1 : Bh) ⊗ₜ[B] (algebraMap B C s * c - algebraMap B C b)) =
          algebraMap Bh (Bh ⊗[B] C) (algebraMap B Bh s) * ((1 : Bh) ⊗ₜ c) -
            algebraMap Bh (Bh ⊗[B] C) (algebraMap B Bh b) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, hs1, hb1,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sub]
      rw [e1, map_sub, map_mul]
      linear_combination (algebraMap Bh (Bh ⊗[B] C) (algebraMap B Bh s)) * hr
    have h2 : ((1 : Bh) ⊗ₜ[B] (algebraMap B C s * c - algebraMap B C b)) * f' ∈ qh := by
      rw [h1]
      exact qh.mul_mem_right _ (by rw [← Ideal.mem_comap, hqB]; exact hmem)
    have h3 := (Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_right hfq
    rw [← hq]
    exact h3
  have : Module.Finite B C :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom B C A).toLinearMap hC
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨isEtaleAt_of_isEtaleAt_tensorProduct B C Bh qh _ hq, happrox⟩

end Decomposition

/-- If every element of `C` is congruent modulo `Q'` to a fraction `b / s` of elements of `B`
with `s ∉ P = Q' ∩ B`, then `κ(P) → κ(Q')` is bijective. -/
theorem bijective_residueFieldMap_of_forall_exists {B C : Type*} [CommRing B] [CommRing C]
    [Algebra B C] (Q' : Ideal C) [Q'.IsPrime]
    (h : ∀ c : C, ∃ s b : B, s ∉ Q'.comap (algebraMap B C) ∧
      algebraMap B C s * c - algebraMap B C b ∈ Q') :
    Function.Bijective (Ideal.ResidueField.map (Q'.comap (algebraMap B C)) Q'
      (algebraMap B C) rfl) := by
  set φ := Ideal.ResidueField.map (Q'.comap (algebraMap B C)) Q' (algebraMap B C) rfl
  refine ⟨φ.injective, fun z ↦ ?_⟩
  have hc : ∀ c : C, algebraMap C Q'.ResidueField c ∈ Set.range φ := by
    intro c
    obtain ⟨s, b, hs, hsb⟩ := h c
    have hs' : algebraMap C Q'.ResidueField (algebraMap B C s) ≠ 0 := by
      rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
    refine ⟨algebraMap B _ b * (algebraMap B _ s)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, Ideal.ResidueField.map_algebraMap,
      Ideal.ResidueField.map_algebraMap, eq_comm, eq_mul_inv_iff_mul_eq₀ hs', mul_comm,
      ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    exact hsb
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q'.primeCompl y
  have ht : algebraMap C Q'.ResidueField (t : C) ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact t.2
  have he : residue (Localization.AtPrime Q') (IsLocalization.mk' _ c t) =
      algebraMap C Q'.ResidueField c * (algebraMap C Q'.ResidueField t)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ ht]
    have := congr_arg (residue (Localization.AtPrime Q'))
      (IsLocalization.mk'_spec (Localization.AtPrime Q') c t)
    rw [map_mul] at this
    exact this
  obtain ⟨u, hu⟩ := hc c
  obtain ⟨v, hv⟩ := hc t
  exact ⟨u * v⁻¹, by rw [map_mul, map_inv₀, hu, hv, he]⟩

section Completion

variable {B : Type u} [CommRing B] (P : Ideal B) [P.IsPrime]

/-- The completion `B̂_P` of the local ring of `B` at `P`. -/
abbrev completionAt : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)

instance [IsNoetherianRing B] : Module.Flat B (completionAt P) :=
  Module.Flat.trans B (Localization.AtPrime P) _

/-- The residue map `B̂_P → κ(P)`. -/
noncomputable def completionAtResidue : completionAt P →ₐ[B] P.ResidueField :=
  (AdicCompletion.evalOneₐ (maximalIdeal (Localization.AtPrime P))).restrictScalars B

lemma completionAtResidue_eq_zero_iff [IsNoetherianRing B] (r : completionAt P) :
    completionAtResidue P r = 0 ↔ r ∈ maximalIdeal (completionAt P) := by
  rw [AdicCompletion.maximalIdeal_eq_map,
    ← AdicCompletion.ker_evalOneₐ_eq_map _ (maximalIdeal _).fg_of_isNoetherianRing,
    RingHom.mem_ker]
  rfl

/-- Every element of `B̂_P` is congruent modulo its maximal ideal to a fraction `b/s`, `s ∉ P`. -/
lemma completionAt_exists_sub_mem [IsNoetherianRing B] (r : completionAt P) :
    ∃ s b : B, s ∉ P ∧
      algebraMap B (completionAt P) s * r - algebraMap B (completionAt P) b ∈
        maximalIdeal (completionAt P) := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (completionAtResidue P r)
  have hra : r - algebraMap (Localization.AtPrime P) (completionAt P) a₀ ∈
      maximalIdeal (completionAt P) := by
    rw [← completionAtResidue_eq_zero_iff]
    change AdicCompletion.evalOneₐ (maximalIdeal _) _ = 0
    rw [map_sub, AlgHom.commutes]
    change completionAtResidue P r - _ = 0
    rw [← ha₀, Ideal.Quotient.algebraMap_eq]
    exact sub_self _
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective P.primeCompl a₀
  refine ⟨s, b, s.2, ?_⟩
  have : algebraMap B (completionAt P) s * r - algebraMap B (completionAt P) b =
      algebraMap B (completionAt P) s *
        (r - algebraMap (Localization.AtPrime P) (completionAt P) a₀) := by
    rw [mul_sub, IsScalarTower.algebraMap_apply B (Localization.AtPrime P) (completionAt P) s,
      IsScalarTower.algebraMap_apply B (Localization.AtPrime P) (completionAt P) b, ← map_mul,
      ← hbs, IsLocalization.mk'_spec']
  rw [this]
  exact Ideal.mul_mem_left _ _ hra

end Completion

section Point

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- Let `B̂` be a local `B`-algebra with residue field `κ(P)` (through `ψ`), where `P = Q ∩ B`.
Then `B̂ ⊗_B A` has a prime over `Q` and the closed point of `B̂`, maximal if `A` is finite over
`B`. -/
lemma exists_isMaximal_tensorProduct [Module.Finite B A] (Q : Ideal A) [Q.IsPrime]
    (Bh : Type*) [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh]
    (ψ : Bh →ₐ[B] (Q.comap (algebraMap B A)).ResidueField)
    (hψ : ∀ r, ψ r = 0 ↔ r ∈ maximalIdeal Bh) :
    ∃ Qh : Ideal (Bh ⊗[B] A), Qh.IsMaximal ∧
      Qh.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] Bh ⊗[B] A) = Q ∧
      Qh.comap (algebraMap Bh (Bh ⊗[B] A)) = maximalIdeal Bh := by
  let P := Q.comap (algebraMap B A)
  let ψ₁ : Bh →ₐ[B] Q.ResidueField := (Ideal.ResidueField.mapₐ P Q (Algebra.ofId B A) rfl).comp ψ
  let ψ₂ : A →ₐ[B] Q.ResidueField := IsScalarTower.toAlgHom B A Q.ResidueField
  let φ : Bh ⊗[B] A →ₐ[B] Q.ResidueField :=
    Algebra.TensorProduct.lift ψ₁ ψ₂ fun _ _ ↦ Commute.all _ _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hB : (RingHom.ker φ).comap (algebraMap Bh (Bh ⊗[B] A)) = maximalIdeal Bh := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply]
    change φ (b ⊗ₜ 1) = 0 ↔ _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, ← hψ]
    exact map_eq_zero_iff (Ideal.ResidueField.mapₐ P Q (Algebra.ofId B A) rfl)
      (Ideal.ResidueField.mapₐ P Q (Algebra.ofId B A) rfl).toRingHom.injective
  refine ⟨RingHom.ker φ, Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Bh) _
    (by rw [hB]; infer_instance), ?_, hB⟩
  ext a
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change φ (1 ⊗ₜ a) = 0 ↔ a ∈ Q
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  exact Ideal.algebraMap_residueField_eq_zero

end Point

section DecompositionMain

variable {B A C : Type u} [CommRing B] [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
  [Algebra C A] [IsScalarTower B C A] {G : Type*} [Group G] [Finite G] [MulSemiringAction G A]
  [SMulCommClass G B A] [Algebra.IsInvariant B A G] [IsNoetherianRing B] [Module.Finite B A]

/-- V.2.2 (i), in the form of EGA IV 17.6.3: let `B` be noetherian, `A` finite over `B = A^G`,
`Q` a prime of `A`, `H ≤ G` containing the decomposition group `G_d(Q)`, and `C → A` an
isomorphism onto `A^H`. Then `C` is étale over `B` at `Q' = Q ∩ C`, and the residue extension
`κ(Q')/κ(P)` is trivial (so that `𝒪_{P} → 𝒪_{Q'}` induces an isomorphism on completions). -/
theorem isEtaleAt_and_bijective_of_stabilizer_le (hinj : Function.Injective (algebraMap B A))
    (H : Subgroup G) (hC : Function.Injective (algebraMap C A))
    (hCH : ∀ a : A, a ∈ Set.range (algebraMap C A) ↔ ∀ h ∈ H, h • a = a)
    (Q : Ideal A) [Q.IsPrime] (hQH : MulAction.stabilizer G Q ≤ H) :
    Algebra.IsEtaleAt B (Q.comap (algebraMap C A)) ∧
      Function.Bijective (Ideal.ResidueField.map ((Q.comap (algebraMap C A)).comap
        (algebraMap B C)) (Q.comap (algebraMap C A)) (algebraMap B C) rfl) := by
  obtain ⟨Qh, _, hA, hB⟩ := exists_isMaximal_tensorProduct Q
    (completionAt (Q.comap (algebraMap B A))) (completionAtResidue _)
    (completionAtResidue_eq_zero_iff _)
  obtain ⟨h1, h2⟩ := isEtaleAt_of_stabilizer_le_aux hinj H hC hCH Q hQH
    (completionAt (Q.comap (algebraMap B A))) (completionAt_exists_sub_mem _) Qh hA hB
  exact ⟨h1, bijective_residueFieldMap_of_forall_exists _ h2⟩

end DecompositionMain

section Inertia

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [MulSemiringAction G A]

/-- The inertia group is normalized by the decomposition group. -/
lemma mul_mul_inv_mem_inertia {Q : Ideal A} {g : G} (hg : g ∈ MulAction.stabilizer G Q) {i : G}
    (hi : i ∈ Q.inertia G) : g * i * g⁻¹ ∈ Q.inertia G := by
  intro x
  have hg' : g • Q = Q := hg
  have := Ideal.smul_mem_pointwise_smul (M := G) g _ Q (hi (g⁻¹ • x))
  rw [hg', smul_sub, smul_inv_smul] at this
  simpa [mul_smul] using this

/-- The key fact behind V.2.2 (ii) (SGA reduces instead to a trivial residue extension): an
element `g` of the decomposition group of `Q` acting trivially modulo `Q` on the invariants `A^I`
of the inertia group `I` acts trivially modulo `Q` on `A`, i.e. lies in `I`. Indeed `a` is a root
of `F = ∏_{i ∈ I} (X - i a)`, whose coefficients lie in `A^I`, so modulo `Q` the element `a` is a
root of `g F = ∏_{i ∈ I} (X - g i a)`, and `g i a ≡ g a` modulo `Q` as `g i g⁻¹ ∈ I`. -/
lemma mem_inertia_of_forall_fixedPoints [Finite G] {Q : Ideal A} [Q.IsPrime] {g : G}
    (hg : g ∈ MulAction.stabilizer G Q)
    (h : ∀ a : A, (∀ i ∈ Q.inertia G, i • a = a) → g • a - a ∈ Q) : g ∈ Q.inertia G := by
  classical
  have : Fintype (Q.inertia G) := Fintype.ofFinite _
  intro a
  let F : A[X] := ∏ i : Q.inertia G, (X - C ((i : G) • a))
  have hFmap : ∀ k : G, F.map (MulSemiringAction.toRingHom G A k) =
      ∏ i : Q.inertia G, (X - C ((k * i) • a)) := by
    intro k
    simp [F, Polynomial.map_prod, mul_smul]
  have hcoeff : ∀ n, ∀ i ∈ Q.inertia G, i • F.coeff n = F.coeff n := by
    intro n i hi
    have : F.map (MulSemiringAction.toRingHom G A i) = F := by
      rw [hFmap]
      exact Fintype.prod_equiv (Equiv.mulLeft (⟨i, hi⟩ : Q.inertia G)) _ _ fun _ ↦ rfl
    have := congr_arg (Polynomial.coeff · n) this
    simpa using this
  have hmod : (F.map (MulSemiringAction.toRingHom G A g)).map (Ideal.Quotient.mk Q) =
      F.map (Ideal.Quotient.mk Q) := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map,
      MulSemiringAction.toRingHom_apply, Ideal.Quotient.eq]
    exact h _ (hcoeff n)
  have hev : Ideal.Quotient.mk Q ((F.map (MulSemiringAction.toRingHom G A g)).eval a) =
      Ideal.Quotient.mk Q (F.eval a) := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
      ← Polynomial.eval_map, hmod]
  have hF0 : F.eval a = 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  rw [hF0, map_zero, Ideal.Quotient.eq_zero_iff_mem, hFmap, Polynomial.eval_prod] at hev
  simp only [eval_sub, eval_X, eval_C] at hev
  obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := ‹_›)).mp hev
  have hconj := mul_mul_inv_mem_inertia hg i.2 (g • a)
  rw [mul_smul, mul_smul, inv_smul_smul, ← mul_smul] at hconj
  change g • a - a ∈ Q
  have e : g • a - a = -(((g * i) • a - g • a) + (a - (g * i) • a)) := by ring
  rw [e]
  exact Q.neg_mem (Q.add_mem hconj hi)

end Inertia

section Localization

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If `B_s → B_s ⊗_B A` is étale for some `s ∈ B` outside `q ∩ B`, then `A` is étale over `B`
at `q`. -/
lemma isEtaleAt_of_etale_localization {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (q : Ideal R) [q.IsPrime] (s : R₀) (hs : s ∉ q.comap (algebraMap R₀ R))
    [Algebra.Etale (Localization.Away s) (Localization.Away s ⊗[R₀] R)] :
    Algebra.IsEtaleAt R₀ q := by
  have : FormallyEtale R₀ (Localization.Away s ⊗[R₀] R) :=
    FormallyEtale.comp R₀ (Localization.Away s) _
  let e := IsLocalization.Away.tensorRightEquiv (r := s) (A := Localization.Away s) R
  let e' : Localization.Away s ⊗[R₀] R ≃ₐ[R₀] Localization.Away (algebraMap R₀ R s) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun r ↦ by
      have h1 : algebraMap R₀ (Localization.Away s ⊗[R₀] R) r =
          algebraMap R (Localization.Away s ⊗[R₀] R) (algebraMap R₀ R r) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      change e (algebraMap R₀ _ r) = _
      rw [h1, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : FormallyEtale R₀ (Localization.Away (algebraMap R₀ R s)) := FormallyEtale.of_equiv e'
  exact (basicOpen_subset_etaleLocus_iff (R := R₀)).mpr this
    (show (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen _ from hs)

end Localization

/-- Étaleness at a prime is invariant under isomorphisms of algebras. -/
lemma isEtaleAt_comap_algEquiv {R C C₀ : Type*} [CommRing R] [CommRing C] [CommRing C₀]
    [Algebra R C] [Algebra R C₀] (e : C ≃ₐ[R] C₀) (q₀ : Ideal C₀) [q₀.IsPrime]
    [Algebra.IsEtaleAt R q₀] : Algebra.IsEtaleAt R (q₀.comap e.toRingHom) := by
  let q := q₀.comap e.toRingHom
  have H : q.primeCompl.map e.toRingEquiv.toMonoidHom = q₀.primeCompl := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨e.symm y, by simpa [q] using hy, by simp⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  let f := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q) (Localization.AtPrime q₀)
    e.toRingEquiv H
  let f' : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q₀ :=
    AlgEquiv.ofRingEquiv (f := f) fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R C (Localization.AtPrime q),
        IsLocalization.ringEquivOfRingEquiv_eq]
      simp [← IsScalarTower.algebraMap_apply]
  exact FormallyEtale.of_equiv f'.symm

section DecompositionModInertia

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G B A] (Q : Ideal A)

omit [Finite G] in
lemma smul_mem_fixedPoints_inertia (d : MulAction.stabilizer G Q)
    (x : FixedPoints.subalgebra B A (Q.inertia G)) :
    (d : G) • (x : A) ∈ FixedPoints.subalgebra B A (Q.inertia G) := by
  rintro ⟨i, hi⟩
  have hd : (d : G)⁻¹ ∈ MulAction.stabilizer G Q := inv_mem d.2
  have := mul_mul_inv_mem_inertia hd hi
  rw [inv_inv] at this
  change i • (d : G) • (x : A) = (d : G) • (x : A)
  have hx : ((d : G)⁻¹ * i * d) • (x : A) = x := x.2 ⟨_, this⟩
  calc i • (d : G) • (x : A) = (d : G) • (((d : G)⁻¹ * i * d) • (x : A)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
    _ = (d : G) • (x : A) := by rw [hx]

/-- The action of the decomposition group `G_d(Q)` on `A^{G_i(Q)}`. -/
noncomputable def decompositionAut : MulAction.stabilizer G Q →*
    RingAut (FixedPoints.subalgebra B A (Q.inertia G)) where
  toFun d :=
    { toFun x := ⟨(d : G) • (x : A), smul_mem_fixedPoints_inertia Q d x⟩
      invFun x := ⟨(d : G)⁻¹ • (x : A), by simpa using smul_mem_fixedPoints_inertia Q d⁻¹ x⟩
      left_inv x := Subtype.ext (by simp)
      right_inv x := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by simp)
      map_add' x y := Subtype.ext (by simp) }
  map_one' := RingEquiv.ext fun x ↦ Subtype.ext (by simp)
  map_mul' d e := RingEquiv.ext fun x ↦ Subtype.ext (by simp [mul_smul])

omit [Finite G] in
lemma decompositionAut_apply (d : MulAction.stabilizer G Q)
    (x : FixedPoints.subalgebra B A (Q.inertia G)) :
    ((decompositionAut Q d x : FixedPoints.subalgebra B A (Q.inertia G)) : A) =
      (d : G) • (x : A) := rfl

instance : ((Q.inertia G).subgroupOf (MulAction.stabilizer G Q)).Normal :=
  ⟨fun n hn g ↦ by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact mul_mul_inv_mem_inertia g.2 hn⟩

omit [Finite G] in
lemma subgroupOf_le_ker_decompositionAut :
    (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≤
      (decompositionAut (B := B) Q).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  exact RingEquiv.ext fun x ↦ Subtype.ext (x.2 ⟨n, hn⟩)

variable [Algebra.IsInvariant B A G] [IsNoetherianRing B] [Module.Finite B A]

/-- V.2.2 (ii) for `H = G_i(Q)`: `A^{G_i(Q)}` is étale over `B` at `Q ∩ A^{G_i(Q)}`. By (i),
`A^{G_d}` is étale over `B` at `Q ∩ A^{G_d}`; and `G_d/G_i` acts on `A^{G_i}` with invariants
`A^{G_d}` and trivial inertia at `Q ∩ A^{G_i}` (`mem_inertia_of_forall_fixedPoints`), so that
`A^{G_i}` is étale over `A^{G_d}` there (V.2.3). -/
theorem isEtaleAt_fixedPoints_inertia (hinj : Function.Injective (algebraMap B A)) [Q.IsPrime] :
    Algebra.IsEtaleAt B (Q.comap (FixedPoints.subalgebra B A (Q.inertia G)).val) := by
  classical
  let D := MulAction.stabilizer G Q
  let I := Q.inertia G
  let R := FixedPoints.subalgebra B A I
  let R₀ := FixedPoints.subalgebra B A D
  have hle : R₀ ≤ R := fun x hx i ↦ hx ⟨i, Ideal.inertia_le_stabilizer Q i.2⟩
  let _ : Algebra R₀ R := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower B R₀ R := IsScalarTower.of_algebraMap_eq fun b ↦ Subtype.ext rfl
  let Γ := D ⧸ I.subgroupOf D
  let ρ : Γ →* RingAut R :=
    QuotientGroup.lift _ (decompositionAut Q) (subgroupOf_le_ker_decompositionAut Q)
  let _ : MulSemiringAction Γ R := MulSemiringAction.compHom R ρ
  have hρ : ∀ (d : D) (x : R), (((d : Γ) • x : R) : A) = (d : G) • (x : A) := fun d x ↦ rfl
  have : SMulCommClass Γ R₀ R := ⟨fun γ r x ↦ by
    induction γ using QuotientGroup.induction_on with
    | H d =>
      apply Subtype.ext
      rw [hρ, Algebra.smul_def, Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_mul, hρ,
        smul_mul', show (d : G) • ((algebraMap R₀ R r : R) : A) = (algebraMap R₀ R r : A) from
          r.2 ⟨d, d.2⟩]⟩
  have : Algebra.IsInvariant R₀ R Γ := ⟨fun x hx ↦
    ⟨⟨x, fun d ↦ by have := congr_arg Subtype.val (hx (d : Γ)); exact this⟩, Subtype.ext rfl⟩⟩
  have hinj₀ : Function.Injective (algebraMap R₀ R) := Subalgebra.inclusion_injective hle
  let q : Ideal R := Q.comap R.val
  have hq : ∀ γ ∈ q.inertia Γ, γ = 1 := by
    intro γ hγ
    induction γ using QuotientGroup.induction_on with
    | H d =>
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine mem_inertia_of_forall_fixedPoints d.2 fun a ha ↦ ?_
      exact hγ ⟨a, fun i ↦ ha i i.2⟩
  obtain ⟨s, hs, het⟩ := exists_etale_localization_of_inertia_eq_bot hinj₀ q hq
  have h1 : Algebra.IsEtaleAt R₀ q := isEtaleAt_of_etale_localization q s hs
  have hCH : ∀ a : A, a ∈ Set.range (algebraMap R₀ A) ↔ ∀ h ∈ D, h • a = a := fun a ↦
    ⟨by rintro ⟨x, rfl⟩ h hh; exact x.2 ⟨h, hh⟩, fun ha ↦ ⟨⟨a, fun h ↦ ha h h.2⟩, rfl⟩⟩
  have h2 : Algebra.IsEtaleAt B (Q.comap (algebraMap R₀ A)) :=
    (isEtaleAt_and_bijective_of_stabilizer_le hinj D Subtype.val_injective hCH Q le_rfl).1
  have : q.LiesOver (Q.comap (algebraMap R₀ A)) := ⟨rfl⟩
  exact Algebra.IsEtaleAt.comp (R := B) (Q.comap (algebraMap R₀ A)) q

/-- V.2.2 (ii) for `H = G_i(Q)`, for any presentation `C → A` of `A^{G_i(Q)}`. -/
theorem isEtaleAt_of_range_eq_fixedPoints_inertia (hinj : Function.Injective (algebraMap B A))
    [Q.IsPrime] {C : Type u} [CommRing C] [Algebra B C] [Algebra C A] [IsScalarTower B C A]
    (hC : Function.Injective (algebraMap C A))
    (hCI : ∀ a : A, a ∈ Set.range (algebraMap C A) ↔ ∀ g ∈ Q.inertia G, g • a = a) :
    Algebra.IsEtaleAt B (Q.comap (algebraMap C A)) := by
  let R := FixedPoints.subalgebra B A (Q.inertia G)
  let φ : C →ₐ[B] R := (IsScalarTower.toAlgHom B C A).codRestrict R fun c i ↦
    (hCI _).mp ⟨c, rfl⟩ i i.2
  have hφ : Function.Bijective φ := ⟨fun x y h ↦ hC (congr_arg Subtype.val h), fun x ↦ by
    obtain ⟨c, hc⟩ := (hCI x).mpr fun g hg ↦ x.2 ⟨g, hg⟩
    exact ⟨c, Subtype.ext hc⟩⟩
  have := isEtaleAt_fixedPoints_inertia (G := G) Q hinj
  exact isEtaleAt_comap_algEquiv (AlgEquiv.ofBijective φ hφ) (Q.comap R.val)

end DecompositionModInertia

section InertiaLe

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G B A] [Algebra.IsInvariant B A G] [IsNoetherianRing B]
  [Module.Finite B A]

/-- V.2.2 (ii): let `B` be noetherian, `A` finite over `B = A^G`, `Q` a prime of `A` and `H ≤ G`
containing the inertia group `G_i(Q)`. Then `A^H` is étale over `B` at `Q ∩ A^H`. By the case
`H = G_i(Q)` (`isEtaleAt_fixedPoints_inertia`), `A^{G_i(Q)}` is étale at `Q ∩ A^{G_i(Q)}` both over
`B` and over `A^H` (the inertia group of `Q` in `H` is `G_i(Q)`), and étaleness descends along
`A^H → A^{G_i(Q)}` (`isEtaleAt_of_isEtaleAt_of_isEtaleAt`). -/
theorem isEtaleAt_of_inertia_le (hinj : Function.Injective (algebraMap B A)) (H : Subgroup G)
    (Q : Ideal A) [Q.IsPrime] (hIH : Q.inertia G ≤ H) :
    Algebra.IsEtaleAt B (Q.comap (FixedPoints.subalgebra B A H).val) := by
  let S := FixedPoints.subalgebra B A H
  have : Algebra.IsInvariant S A H := ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩
  have : Module.Finite B S :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom B S A).toLinearMap Subtype.val_injective
  have : IsNoetherianRing S := isNoetherian_of_tower B (inferInstance : IsNoetherian B S)
  have : Module.Finite S A := Module.Finite.of_restrictScalars_finite B S A
  let S' := FixedPoints.subalgebra S A (Q.inertia H)
  have h1 : Algebra.IsEtaleAt S (Q.comap S'.val) :=
    isEtaleAt_fixedPoints_inertia (B := S) (G := H) Q Subtype.val_injective
  have hCI : ∀ a : A, a ∈ Set.range (algebraMap S' A) ↔ ∀ g ∈ Q.inertia G, g • a = a := by
    intro a
    refine ⟨?_, fun ha ↦ ⟨⟨a, fun h ↦ ha h ?_⟩, rfl⟩⟩
    · rintro ⟨x, rfl⟩ g hg
      exact x.2 ⟨⟨g, hIH hg⟩, hg⟩
    · exact h.2
  have h2 : Algebra.IsEtaleAt B (Q.comap S'.val) :=
    isEtaleAt_of_range_eq_fixedPoints_inertia (G := G) Q hinj Subtype.val_injective hCI
  have : Module.Finite S S' :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom S S' A).toLinearMap Subtype.val_injective
  have : Module.Finite B S' :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom B S' A).toLinearMap Subtype.val_injective
  have : Algebra.FinitePresentation B S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation S S' :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation B S' :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : (Q.comap S'.val).LiesOver (Q.comap S.val) := ⟨rfl⟩
  exact isEtaleAt_of_isEtaleAt_of_isEtaleAt (R := B) (Q.comap S.val) (Q.comap S'.val)

end InertiaLe

/-- V.2.2 (`DecompositionInertiaEtaleStatement`), for `B` noetherian and `A` finite over
`B = A^G` (SGA: `Y` locally noetherian, `X` finite over `Y`): (i) if `H ⊇ G_d(Q)`, then `A^H` is
étale over `B` at `Q' = Q ∩ A^H` with `κ(Q') = κ(P)`, i.e. `𝒪_P → 𝒪_{Q'}` induces an
isomorphism on completions (EGA IV 17.6.3); (ii) if `H ⊇ G_i(Q)`, then `A^H` is étale over `B`
at `Q'`. -/
theorem decompositionInertiaEtaleStatement : DecompositionInertiaEtaleStatement := by
  intro B A G _ _ _ _ _ _ _ _ _ _ hinj H Q _
  refine ⟨fun hQH ↦ ⟨inferInstance, ?_⟩, fun hIH ↦ ⟨inferInstance, ?_⟩⟩
  · have hCH : ∀ a : A, a ∈ Set.range (algebraMap (FixedPoints.subalgebra B A H) A) ↔
        ∀ h ∈ H, h • a = a := fun a ↦
      ⟨by rintro ⟨x, rfl⟩ h hh; exact x.2 ⟨h, hh⟩, fun ha ↦ ⟨⟨a, fun h ↦ ha h h.2⟩, rfl⟩⟩
    exact isEtaleAt_and_bijective_of_stabilizer_le hinj H Subtype.val_injective hCH Q hQH
  · exact isEtaleAt_of_inertia_le hinj H Q hIH

end SGA.SGA1.ExposeV
