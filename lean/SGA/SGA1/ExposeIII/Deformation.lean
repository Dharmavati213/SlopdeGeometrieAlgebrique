/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# SGA 1, Exposé III, §§4–6: infinitesimal extensions of smooth schemes (affine case)

Theorem III.4.1: a smooth `Y₀`-scheme `X₀`, for `Y₀ ⊆ Y` defined by a nilpotent ideal, lifts
locally to a smooth `Y`-scheme, uniquely up to local isomorphism. Lemma III.4.2: a morphism of
`Y`-schemes with flat source is an isomorphism if its reduction modulo a nilpotent ideal is
one. Section 6 globalises: the obstruction to lifting lies in `H²(X₀, 𝔤 ⊗ grⁿ⁺¹)`, and lifts are
classified by `H¹`; for affine `X₀` a lift exists and is unique up to isomorphism (III.6.8).
Section 5 does the same for morphisms (III.5.4–III.5.6).

We formalize the affine content:

* III.4.2 for rings (`bijective_iff_bijective_quotientMap`), and its "closed immersion" variant
  without flatness (`surjective_of_surjective_mod`); the scheme form is in `Thickening.lean`;
* uniqueness of smooth lifts up to isomorphism (III.4.1 and III.6.8, `exists_algEquiv_lift`),
  and III.6.2 (a lift of an isomorphism is an isomorphism, `bijective_of_comp_eq`);
* existence of smooth lifts: for standard smooth algebras by lifting the equations
  (`exists_isStandardSmooth_lift`), hence locally for all smooth algebras
  (`exists_smooth_lift_localizationAway`, the local existence of III.4.1);
* III.5.4 and III.5.6 for an affine source: a morphism to a smooth affine `X` extends from
  `Yₙ` to the formal completion of `Y` (`exists_lift_adicCompletion`); III.5.7 levelwise
  (`bijective_baseChange_iff`; the scheme form is `isIso_of_isIso_reduction` in
  `Thickening.lean`).

The existence of a global lift of an arbitrary smooth affine algebra (III.6.8) is stated as
`SmoothLiftAffineStatement` and proved in `SmoothLift.lean`; the cohomological statements
III.6.3, III.6.7, III.6.9, III.6.10 and §7 need the tangent sheaf and coherent cohomology.
-/

universe u v w

open TensorProduct

namespace SGA.SGA1.ExposeIII


variable {R : Type u} {B' : Type v} {B : Type w} [CommRing R] [CommRing B'] [CommRing B]
  [Algebra R B'] [Algebra R B] {J : Ideal R}

/-- A module `N` with `N ≤ J • N` for a nilpotent ideal `J` is zero. -/
lemma submodule_eq_bot_of_le_smul {M : Type*} [AddCommGroup M] [Module R M] (hJ : IsNilpotent J)
    {N : Submodule R M} (h : N ≤ J • N) : N = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  have key : ∀ k : ℕ, N ≤ J ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc N ≤ J ^ k • N := ih
        _ ≤ J ^ k • (J • N) := smul_mono_right _ h
        _ = J ^ (k + 1) • N := by rw [← Submodule.mul_smul, pow_succ]
  have := key n
  rwa [hn, Submodule.zero_eq_bot, Submodule.bot_smul, le_bot_iff] at this

/-- III.4.2, surjectivity: the "closed immersion" variant noted after III.4.2, which needs no
flatness. A map `u : B' → B` of `R`-algebras which is surjective modulo a nilpotent ideal `J` of
`R` is surjective. -/
theorem surjective_of_surjective_mod (hJ : IsNilpotent J) (u : B' →ₐ[R] B)
    (h : ∀ b, ∃ b', u b' - b ∈ J.map (algebraMap R B)) : Function.Surjective u := by
  let M := LinearMap.range u.toLinearMap
  have htop : (⊤ : Submodule R B) ≤ M ⊔ J • ⊤ := by
    intro b _
    obtain ⟨b', hb'⟩ := h b
    have : b = u b' - (u b' - b) := by ring
    rw [this]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨b', rfl⟩) (Submodule.mem_sup_right ?_)
    rw [Ideal.smul_top_eq_map]
    exact hb'
  -- the quotient `B ⧸ M` is killed by `J`, hence zero
  have hq : (⊤ : Submodule R (B ⧸ M)) ≤ J • ⊤ := by
    intro x _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm, y, hy, hmy⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := b)))
    rw [← hmy, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr hm, zero_add]
    have := Submodule.map_le_iff_le_comap.mp (le_refl (Submodule.map M.mkQ (J • ⊤))) hy
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    exact this
  have := submodule_eq_bot_of_le_smul hJ hq
  intro b
  have hb : Submodule.Quotient.mk (p := M) b = 0 := by
    rw [← Submodule.mem_bot R, ← this]; exact Submodule.mem_top
  obtain ⟨b', hb'⟩ := (Submodule.Quotient.mk_eq_zero _).mp hb
  exact ⟨b', hb'⟩

/-- III.4.2, injectivity: if `B` is flat over `R`, a surjection `u : B' → B` which is injective
modulo a nilpotent ideal `J` of `R` is injective. As in the graded-ring argument of SGA, the
kernel `K` satisfies `K = J K` by flatness of `B`. -/
theorem injective_of_injective_mod [Module.Flat R B] (hJ : IsNilpotent J) (u : B' →ₐ[R] B)
    (hsurj : Function.Surjective u)
    (h : ∀ b', u b' ∈ J.map (algebraMap R B) → b' ∈ J.map (algebraMap R B')) :
    Function.Injective u := by
  let K := LinearMap.ker u.toLinearMap
  have hK : K ≤ J • ⊤ := by
    intro x hx
    rw [Ideal.smul_top_eq_map]
    refine h x ?_
    have : u x = 0 := LinearMap.mem_ker.mp hx
    rw [this]
    exact zero_mem _
  have : K = J • K := by
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J u.toLinearMap hsurj, inf_eq_left.mpr hK]
  have hbot : K = ⊥ := submodule_eq_bot_of_le_smul hJ this.le
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.ker_eq_bot]
  exact hbot

lemma map_le_comap (u : B' →ₐ[R] B) :
    J.map (algebraMap R B') ≤ (J.map (algebraMap R B)).comap u := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hr

lemma map_mem_map (u : B' →ₐ[R] B) {x : B'} (hx : x ∈ J.map (algebraMap R B')) :
    u x ∈ J.map (algebraMap R B) :=
  map_le_comap u hx

/-- III.4.2: a morphism `u : X → X'` of `Y`-schemes, with `X` flat over `Y`, is an isomorphism
if and only if its reduction modulo a nilpotent ideal of `Y` is one. Affine case: `u` is an
`R`-algebra map `B' → B` with `B` flat, and `J` is a nilpotent ideal of `R`. -/
theorem bijective_iff_bijective_quotientMap [Module.Flat R B] (hJ : IsNilpotent J)
    (u : B' →ₐ[R] B) :
    Function.Bijective u ↔
      Function.Bijective (Ideal.quotientMapₐ (J.map (algebraMap R B)) u (map_le_comap u)) := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
  · let e := AlgEquiv.ofBijective u hu
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hxy
      rw [Ideal.Quotient.eq]
      have := map_mem_map e.symm.toAlgHom hxy
      simpa [← map_sub, e] using this
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, rfl⟩ := hu.2 y
      exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  · have hsurj := surjective_of_surjective_mod hJ u fun b ↦ by
      obtain ⟨x, hx⟩ := hu.2 (Ideal.Quotient.mk _ b)
      obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨b', Ideal.Quotient.eq.mp hx⟩
    refine ⟨injective_of_injective_mod hJ u hsurj fun b' hb' ↦ ?_, hsurj⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine hu.1 ?_
    rw [map_zero, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hb'

lemma isNilpotent_map (hJ : IsNilpotent J) (T : Type*) [CommRing T] [Algebra R T] :
    IsNilpotent (J.map (algebraMap R T)) := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩

/-- III.6.2 (affine case), via III.4.2: a lift `B → B'` of an isomorphism
`B ⧸ J B ≃ B' ⧸ J B'` is an isomorphism when `B'` is flat. Hence the isomorphisms lifting a
given one are the lifts of `B → B' ⧸ J B'`, which form a torsor by III.5.1. -/
theorem bijective_of_comp_eq [Module.Flat R B'] (hJ : IsNilpotent J)
    (e₀ : (B ⧸ J.map (algebraMap R B)) ≃ₐ[R] (B' ⧸ J.map (algebraMap R B'))) (φ : B →ₐ[R] B')
    (hφ : ∀ x, Ideal.Quotient.mk _ (φ x) = e₀ (Ideal.Quotient.mk _ x)) :
    Function.Bijective φ := by
  have hsurj := surjective_of_surjective_mod hJ φ fun b' ↦ by
    obtain ⟨x, hx⟩ := e₀.surjective (Ideal.Quotient.mk _ b')
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, Ideal.Quotient.eq.mp ((hφ b).trans hx)⟩
  refine ⟨injective_of_injective_mod hJ φ hsurj fun b hb ↦ ?_, hsurj⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hb ⊢
  rw [hφ] at hb
  exact (map_eq_zero_iff e₀ e₀.injective).mp hb

/-- III.4.1, uniqueness, and III.6.8, uniqueness (affine case): two smooth lifts `B`, `B'` over
`R` of the same algebra over `R ⧸ J`, `J` nilpotent, are isomorphic by an isomorphism lifting
the given one (which is not unique, Remark III.4.3). Only formal smoothness of `B` and flatness
of `B'` are used. -/
theorem exists_algEquiv_lift [Algebra.FormallySmooth R B] [Module.Flat R B'] (hJ : IsNilpotent J)
    (e₀ : (B ⧸ J.map (algebraMap R B)) ≃ₐ[R] (B' ⧸ J.map (algebraMap R B'))) :
    ∃ e : B ≃ₐ[R] B', ∀ x, Ideal.Quotient.mk _ (e x) = e₀ (Ideal.Quotient.mk _ x) := by
  obtain ⟨φ, hφ⟩ := Algebra.FormallySmooth.exists_lift _ (isNilpotent_map hJ B')
    (e₀.toAlgHom.comp (Ideal.Quotient.mkₐ R _))
  have hφ' (x : B) : Ideal.Quotient.mk _ (φ x) = e₀ (Ideal.Quotient.mk _ x) := congr($hφ x)
  exact ⟨AlgEquiv.ofBijective φ (bijective_of_comp_eq hJ e₀ φ hφ'), hφ'⟩


/-- III.5.7 (affine case, one infinitesimal neighbourhood at a time): let `C` be flat over `R`
and `I` an ideal of `R`. A morphism `Yₙ → Xₙ` over `Sₙ = Spec (R ⧸ Iⁿ)`, i.e. an
`R ⧸ Iⁿ`-algebra map `u : (R ⧸ Iⁿ) ⊗ A → (R ⧸ Iⁿ) ⊗ C`, is an isomorphism as soon as its
reduction modulo `I` is one. "Proceeding as in III.4.2": `(R ⧸ Iⁿ) ⊗ C` is flat over `R ⧸ Iⁿ`
and `I ⧸ Iⁿ` is nilpotent. -/
theorem bijective_baseChange_iff {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Flat R C] (I : Ideal R) (n : ℕ)
    (u : (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] C) :
    Function.Bijective u ↔ Function.Bijective (Ideal.quotientMapₐ
      ((I.map (Ideal.Quotient.mk (I ^ n))).map (algebraMap _ ((R ⧸ I ^ n) ⊗[R] C))) u
      (map_le_comap u)) := by
  refine bijective_iff_bijective_quotientMap ⟨n, ?_⟩ u
  rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

section Lifting


variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  {C : Type w} [CommRing C] [Algebra R C]

/-- III.5.3 (affine case): `Iⁿ⁺¹ C ⧸ Iⁿ⁺² C` is a square-zero ideal of `C ⧸ Iⁿ⁺² C`. -/
lemma sq_map_pow_succ_eq_bot (I : Ideal C) (n : ℕ) :
    ((I ^ (n + 1)).map (Ideal.Quotient.mk (I ^ (n + 2)))) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, ← pow_mul, eq_bot_iff, ← Ideal.map_quotient_self (I ^ (n + 2))]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

/-- III.5.4 and III.5.6 (affine case): if `A` is formally smooth over `R`, every map
`A → C ⧸ Iⁿ⁺¹` extends to a map `A → Ĉ` into the `I`-adic completion. -/
theorem exists_lift_adicCompletion [Algebra.FormallySmooth R A] (I : Ideal C) (n : ℕ)
    (g : A →ₐ[R] C ⧸ I ^ (n + 1)) :
    ∃ ĝ : A →ₐ[R] AdicCompletion I C,
      ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R).comp ĝ = g := by
  have step (k : ℕ) (v : A →ₐ[R] C ⧸ I ^ (n + 1 + k)) :
      ∃ v' : A →ₐ[R] C ⧸ I ^ (n + 1 + (k + 1)),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))).comp v' = v := by
    have hle : I ^ (n + 1 + (k + 1)) ≤ I ^ (n + 1 + k) := Ideal.pow_le_pow_right (by omega)
    obtain ⟨v', hv'⟩ := Algebra.FormallySmooth.exists_lift
      ((I ^ (n + 1 + k)).map (Ideal.Quotient.mkₐ R (I ^ (n + 1 + (k + 1))))) ⟨2, by
        rw [← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot, eq_bot_iff,
          ← Ideal.map_quotient_self (I ^ (n + 1 + (k + 1)))]
        exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))⟩
      ((DoubleQuot.quotQuotEquivQuotOfLEₐ R hle).symm.toAlgHom.comp v)
    refine ⟨v', ?_⟩
    rw [← DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ R hle, AlgHom.comp_assoc, hv',
      ← AlgHom.comp_assoc]
    simp
  let seq : (k : ℕ) → (A →ₐ[R] C ⧸ I ^ (n + 1 + k)) := fun k ↦
    Nat.rec g (fun k v ↦ (step k v).choose) k
  have hseq (k : ℕ) : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))).comp
      (seq (k + 1)) = seq k := (step k (seq k)).choose_spec
  have hseq' {k l : ℕ} (hkl : k ≤ l) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))).comp (seq l) = seq k := by
    induction l, hkl using Nat.le_induction with
    | base => rw [Ideal.Quotient.factorₐ_refl]; rfl
    | succ l hkl ih => rw [← ih, ← hseq l, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  let f : (k : ℕ) → (A →ₐ[R] C ⧸ I ^ k) := fun k ↦
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))).comp (seq k)
  have hf {k l : ℕ} (hkl : k ≤ l) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hkl)).comp (f l) = f k := by
    simp only [f, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
    rw [← hseq' hkl, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  refine ⟨AdicCompletion.liftAlgHom I f hf, AlgHom.ext fun x ↦ ?_⟩
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', AdicCompletion.evalₐ_liftAlgHom]
  have := congr($(hseq' (Nat.zero_le (n + 1))) x)
  exact this


end Lifting


section StandardSmooth

variable {R R₀ S₀ : Type*} [CommRing R] [CommRing R₀] [CommRing S₀] [Algebra R R₀]
  [Algebra R₀ S₀] {ι σ : Type*} [Finite σ] (P₀ : Algebra.SubmersivePresentation R₀ S₀ ι σ)
  (hsurj : Function.Surjective (algebraMap R R₀))

/-- A choice of lifts to `R` of the relations of a presentation over `R₀`. -/
noncomputable def liftRelation (j : σ) : MvPolynomial ι R :=
  (MvPolynomial.map_surjective _ hsurj (P₀.relation j)).choose

lemma map_liftRelation (j : σ) :
    MvPolynomial.map (algebraMap R R₀) (liftRelation P₀ hsurj j) = P₀.relation j :=
  (MvPolynomial.map_surjective _ hsurj (P₀.relation j)).choose_spec

/-- The `R`-algebra obtained by lifting the relations of `P₀` to `R`. -/
abbrev LiftedAlgebra : Type _ :=
  MvPolynomial ι R ⧸ Ideal.span (Set.range (liftRelation P₀ hsurj))

/-- The pre-submersive presentation of the lifted algebra. -/
noncomputable def liftedPresentation :
    Algebra.PreSubmersivePresentation R (LiftedAlgebra P₀ hsurj) ι σ :=
  Algebra.PreSubmersivePresentation.naive P₀.map P₀.map_inj

variable [Algebra R S₀] [IsScalarTower R R₀ S₀]

/-- The map `R[X] → S₀` reducing modulo the kernel of `R → R₀`. -/
noncomputable def reductionAux : MvPolynomial ι R →ₐ[R] S₀ :=
  ((MvPolynomial.aeval P₀.val).restrictScalars R).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId R R₀))

lemma span_liftRelation_le_ker :
    Ideal.span (Set.range (liftRelation P₀ hsurj)) ≤ RingHom.ker (reductionAux P₀) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  change MvPolynomial.aeval P₀.val (MvPolynomial.map (algebraMap R R₀) _) = 0
  rw [map_liftRelation]
  exact P₀.aeval_val_relation j

/-- The reduction map from the lifted algebra to `S₀`. -/
noncomputable def liftedReduction : LiftedAlgebra P₀ hsurj →ₐ[R] S₀ :=
  Ideal.Quotient.liftₐ _ (reductionAux P₀) fun _ ha ↦ span_liftRelation_le_ker P₀ hsurj ha

lemma liftedReduction_mk (p : MvPolynomial ι R) :
    liftedReduction P₀ hsurj (Ideal.Quotient.mk _ p) =
      MvPolynomial.aeval P₀.val (MvPolynomial.map (algebraMap R R₀) p) := rfl

lemma liftedReduction_surjective : Function.Surjective (liftedReduction P₀ hsurj) := by
  intro y
  obtain ⟨q, rfl⟩ := P₀.algebraMap_surjective y
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ hsurj q
  exact ⟨Ideal.Quotient.mk _ p, by rw [liftedReduction_mk, Algebra.Generators.algebraMap_apply]⟩

lemma ker_liftedReduction_le : RingHom.ker (liftedReduction P₀ hsurj) ≤
    (RingHom.ker (algebraMap R R₀)).map (algebraMap R (LiftedAlgebra P₀ hsurj)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, liftedReduction_mk] at hx
  have hp : MvPolynomial.map (algebraMap R R₀) p ∈ (Ideal.span
      (Set.range (liftRelation P₀ hsurj))).map (MvPolynomial.map (algebraMap R R₀)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    have : MvPolynomial.map (algebraMap R R₀) ∘ liftRelation P₀ hsurj = P₀.relation :=
      funext (map_liftRelation P₀ hsurj)
    rw [this, P₀.span_range_relation_eq_ker]
    exact RingHom.mem_ker.mpr
      ((Algebra.Generators.algebraMap_apply (P := P₀.toGenerators) _).trans hx)
  obtain ⟨q, hq, hqp⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ hsurj)).mp hp
  have hpq : p - q ∈ (RingHom.ker (algebraMap R R₀)).map (MvPolynomial.C) := by
    rw [← MvPolynomial.ker_map, RingHom.mem_ker, map_sub, hqp, sub_self]
  have : Ideal.Quotient.mk (Ideal.span (Set.range (liftRelation P₀ hsurj))) p =
      Ideal.Quotient.mk _ (p - q) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
  rw [this]
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range (liftRelation P₀ hsurj))))
    hpq
  rwa [Ideal.map_map] at this

omit [Algebra R S₀] [IsScalarTower R R₀ S₀] in
lemma algebraMap_liftedPresentation (p : MvPolynomial ι R) :
    algebraMap (liftedPresentation P₀ hsurj).Ring (LiftedAlgebra P₀ hsurj) p =
      Ideal.Quotient.mk _ p := by
  rw [Algebra.Generators.algebraMap_apply]
  induction p using MvPolynomial.induction_on with
  | C r => simp; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.aeval_X]
    rfl

lemma liftedReduction_jacobian :
    liftedReduction P₀ hsurj (liftedPresentation P₀ hsurj).jacobian = P₀.jacobian := by
  classical
  have := Fintype.ofFinite σ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    algebraMap_liftedPresentation, liftedReduction_mk, RingHom.map_det,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_apply]
  congr 2
  refine Matrix.ext fun i j ↦ ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, liftedPresentation,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive, ← MvPolynomial.pderiv_map,
    map_liftRelation, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]

variable (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀)))
include hnil

lemma isUnit_liftedPresentation_jacobian : IsUnit (liftedPresentation P₀ hsurj).jacobian := by
  set x := (liftedPresentation P₀ hsurj).jacobian
  obtain ⟨y₀, hy₀⟩ := (P₀.jacobian_isUnit).exists_right_inv
  obtain ⟨y, rfl⟩ := liftedReduction_surjective P₀ hsurj y₀
  have hmem : x * y - 1 ∈ (RingHom.ker (algebraMap R R₀)).map
      (algebraMap R (LiftedAlgebra P₀ hsurj)) := by
    refine ker_liftedReduction_le P₀ hsurj ?_
    rw [RingHom.mem_ker, map_sub, map_mul, liftedReduction_jacobian, hy₀, map_one, sub_self]
  have hnil' : IsNilpotent (x * y - 1) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hmem n
    rwa [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at this
  have : IsUnit (x * y) := by simpa using hnil'.isUnit_add_one
  exact isUnit_of_mul_isUnit_left this

/-- The lift of a submersive presentation along a surjection `R → R₀` with nilpotent kernel. -/
noncomputable def liftedSubmersivePresentation :
    Algebra.SubmersivePresentation R (LiftedAlgebra P₀ hsurj) ι σ where
  __ := liftedPresentation P₀ hsurj
  jacobian_isUnit := isUnit_liftedPresentation_jacobian P₀ hsurj hnil

omit hnil in
/-- The lifted algebra reduces to `S₀`: `R₀ ⊗[R] L ≃ S₀`. -/
noncomputable def tensorLiftedAlgebraEquiv :
    R₀ ⊗[R] LiftedAlgebra P₀ hsurj ≃ₐ[R₀] S₀ :=
  let PB := (liftedPresentation P₀ hsurj).toPresentation.baseChange R₀
  have hrel : PB.relation = P₀.relation := funext fun j ↦ by
    simp only [PB, Algebra.Presentation.baseChange_relation]
    exact map_liftRelation P₀ hsurj j
  have hker : PB.ker = P₀.ker := by
    rw [← PB.span_range_relation_eq_ker, ← P₀.span_range_relation_eq_ker, hrel]
  ((PB.quotientEquiv.restrictScalars R₀).symm.trans (Ideal.quotientEquivAlgOfEq R₀ hker)).trans
    (P₀.quotientEquiv.restrictScalars R₀)

end StandardSmooth

section Existence

variable {R : Type u} {R₀ S₀ : Type*} [CommRing R] [CommRing R₀] [CommRing S₀] [Algebra R R₀]
  [Algebra R₀ S₀] [Algebra R S₀] [IsScalarTower R R₀ S₀]
  (hsurj : Function.Surjective (algebraMap R R₀))
  (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀)))
include hsurj hnil

/-- III.4.1, existence, for a standard smooth `X₀` (e.g. étale over an affine space): a standard
smooth `R₀`-algebra, `R₀ = R ⧸ J` with `J` nilpotent, lifts to a standard smooth `R`-algebra.
One lifts the equations; the Jacobian stays invertible since `J` is nilpotent. -/
theorem exists_isStandardSmooth_lift [Algebra.IsStandardSmooth R₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IsStandardSmooth R S ∧ Nonempty (R₀ ⊗[R] S ≃ₐ[R₀] S₀) := by
  obtain ⟨ι, σ, _, _, ⟨P₀⟩⟩ := Algebra.IsStandardSmooth.out (R := R₀) (S := S₀)
  exact ⟨LiftedAlgebra P₀ hsurj, inferInstance, inferInstance,
    (liftedSubmersivePresentation P₀ hsurj hnil).isStandardSmooth,
    ⟨tensorLiftedAlgebraEquiv P₀ hsurj⟩⟩

/-- III.4.1, existence (affine form): a smooth `R₀`-algebra `S₀`, `R₀ = R ⧸ J` with `J`
nilpotent, can be covered by basic opens `D(t)` each of which lifts to a smooth `R`-algebra. -/
theorem exists_smooth_lift_localizationAway [Algebra.Smooth R₀ S₀] :
    ∃ s : Set S₀, Ideal.span s = ⊤ ∧ ∀ t ∈ s, ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.Smooth R S ∧ Nonempty (R₀ ⊗[R] S ≃ₐ[R₀] Localization.Away t) := by
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R₀ S₀
  refine ⟨s, hs, fun t ht ↦ ?_⟩
  have := h t ht
  obtain ⟨S, _, _, hS, he⟩ := exists_isStandardSmooth_lift (S₀ := Localization.Away t) hsurj hnil
  exact ⟨S, inferInstance, inferInstance, inferInstance, he⟩

end Existence

/-- III.6.8, existence: an affine smooth scheme over `Y₀ ⊆ Y`, defined by a nilpotent ideal,
lifts to a smooth scheme over `Y`. In ring form: a smooth algebra over `R₀ = R ⧸ J`, `J`
nilpotent, is the reduction of a smooth `R`-algebra. SGA deduces this from the vanishing of `H²`
of quasi-coherent sheaves on affine schemes. Proved in `SmoothLift.lean`
(`smoothLiftAffineStatement`); uniqueness is `exists_algEquiv_lift`
(`exists_iso_of_smooth_of_isAffine` for schemes). -/
def SmoothLiftAffineStatement : Prop :=
  ∀ (R R₀ S₀ : Type u) [CommRing R] [CommRing R₀] [CommRing S₀] [Algebra R R₀] [Algebra R₀ S₀],
    Function.Surjective (algebraMap R R₀) → IsNilpotent (RingHom.ker (algebraMap R R₀)) →
      Algebra.Smooth R₀ S₀ → ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
        Algebra.Smooth R S ∧ Nonempty (R₀ ⊗[R] S ≃ₐ[R₀] S₀)


end SGA.SGA1.ExposeIII
