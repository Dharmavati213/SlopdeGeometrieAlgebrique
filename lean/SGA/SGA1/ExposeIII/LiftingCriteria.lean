/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.LocalComponents

/-!
# SGA 1, Exposé III, 2.1: the lifting properties characterising formal smoothness

Theorem III.2.1: for a local homomorphism `A → B` of noetherian local rings with finite residue
extension, the following are equivalent:
(i) `B` is formally smooth over `A` (Definition III.1.1);
(ii) maps `B → C ⧸ J` into quotients of complete local rings lift to `C`
(`CompleteLiftingProperty`);
(iii) continuous maps into nilpotent thickenings lift (`AdicFormallySmooth`);
(iv) maps into quotients of local artinian rings finite over `A` lift
(`LocalArtinianLiftingProperty`);
(iv bis) the same with `J² = 0` (`SqZeroLocalArtinianLiftingProperty`).

We prove all of them equivalent for complete `A`, `B` (`formallySmooth_tfae'`). The implication
(iv bis) ⇒ (i) follows SGA: the lifting property (iv bis) passes to the local components of
`A' ⊗[A] B` over `A'` for a finite local `A'`
(`SqZeroLocalArtinianLiftingProperty.artinianLiftingProperty_quotient`), and for `A'` making the
residue extensions trivial one concludes with Corollary III.2.2.
-/

universe u

open IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeIII

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- III.2.1 (ii): every local `A`-homomorphism `B → C ⧸ J`, for `C` a complete (noetherian) local
`A`-algebra and `J` a proper ideal of `C`, lifts to an `A`-homomorphism `B → C`. -/
def CompleteLiftingProperty : Prop :=
  ∀ ⦃C : Type u⦄ [CommRing C] [Algebra A C] [IsLocalRing C] [IsNoetherianRing C]
    [IsAdicComplete (maximalIdeal C) C] (J : Ideal C), J ≠ ⊤ →
      ∀ f : B →ₐ[A] C ⧸ J, IsLocalHom f → ∃ g : B →ₐ[A] C, (Ideal.Quotient.mkₐ A J).comp g = f

/-- III.2.1 (iv): every local `A`-homomorphism `B → C ⧸ J`, for `C` a local artinian `A`-algebra
finite over `A` and `J` a proper ideal, lifts to `B → C`. -/
def LocalArtinianLiftingProperty : Prop :=
  ∀ ⦃C : Type u⦄ [CommRing C] [Algebra A C] [IsLocalRing C] [IsArtinianRing C]
    [Module.Finite A C] (J : Ideal C), J ≠ ⊤ →
      ∀ f : B →ₐ[A] C ⧸ J, IsLocalHom f → ∃ g : B →ₐ[A] C, (Ideal.Quotient.mkₐ A J).comp g = f

/-- III.2.1 (iv bis): the lifting property (iv) for square-zero ideals `J`. -/
def SqZeroLocalArtinianLiftingProperty : Prop :=
  ∀ ⦃C : Type u⦄ [CommRing C] [Algebra A C] [IsLocalRing C] [IsArtinianRing C]
    [Module.Finite A C] (J : Ideal C), J ^ 2 = ⊥ →
      ∀ f : B →ₐ[A] C ⧸ J, IsLocalHom f → ∃ g : B →ₐ[A] C, (Ideal.Quotient.mkₐ A J).comp g = f

variable {A B}

/-- III.2.1, (iii) ⇒ (ii). -/
theorem AdicFormallySmooth.completeLiftingProperty [IsLocalRing B]
    (h : AdicFormallySmooth A (maximalIdeal B)) : CompleteLiftingProperty A B :=
  fun _ _ _ _ _ _ _ hJ f _ ↦ h.exists_lift_of_isLocalRing hJ f

/-- III.2.1, (ii) ⇒ (iv): a local artinian ring is a complete noetherian local ring. -/
theorem CompleteLiftingProperty.localArtinianLiftingProperty (h : CompleteLiftingProperty A B) :
    LocalArtinianLiftingProperty A B :=
  fun _ _ _ _ _ _ J hJ f hf ↦ h J hJ f hf

/-- III.2.1, (iv) ⇒ (iv bis). -/
theorem LocalArtinianLiftingProperty.sqZero (h : LocalArtinianLiftingProperty A B) :
    SqZeroLocalArtinianLiftingProperty A B := by
  intro C _ _ _ _ _ J hJ f hf
  refine h J (fun hJ' ↦ ?_) f hf
  have : (⊤ : Ideal C) = ⊥ := by rw [← hJ, hJ', Ideal.top_pow]
  exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (eq_top_iff.mpr (this ▸ bot_le))

/-- III.2.1, (iv bis) ⇒ (iv ter) of III.2.2 (restricting the test rings). -/
theorem SqZeroLocalArtinianLiftingProperty.artinianLiftingProperty
    (h : SqZeroLocalArtinianLiftingProperty A B) : ArtinianLiftingProperty A B :=
  fun _ _ _ _ _ _ _ J hJ f hf ↦ h J hJ f hf

section Components

variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- The step "(iv) remains verified for the local components of `B ⊗_A A'` over `A'`" of the proof
of III.2.1, (iv) ⇒ (i): the lifting property (iv bis) of `B` over `A` gives the lifting property
(iv ter) of the local component `(A' ⊗[A] B) ⧸ (1 - e)` over `A'`, for `A'` finite over `A`. A
map from the component into `C ⧸ J` gives a map `B → C ⧸ J`; its lift `B → C` extends to
`A' ⊗ B → C`, which kills `1 - e` since the image of the idempotent `1 - e` lies in `J`. -/
theorem SqZeroLocalArtinianLiftingProperty.artinianLiftingProperty_quotient
    (h : SqZeroLocalArtinianLiftingProperty A B) (A' : Type u) [CommRing A'] [Algebra A A']
    [Module.Finite A A'] (P : Ideal (A' ⊗[A] B)) [P.IsMaximal] (e : A' ⊗[A] B)
    (he : IsIdempotentElem e) (heP : e ∉ P)
    (hQ : ∀ Q : Ideal (A' ⊗[A] B), Q.IsMaximal → Q ≠ P → e ∈ Q) :
    ArtinianLiftingProperty A' ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}) := by
  intro C _ _ _ _ _ _ J hJ f hf
  let : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' C := .of_algebraMap_eq' rfl
  have : Module.Finite A C := Module.Finite.trans A' C
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalization_atPrime_quotient he heP hQ
  have := isLocalRing_quotient he heP hQ
  have hmS : P.map (algebraMap (A' ⊗[A] B) S) = maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P S
  let ι : B →ₐ[A] S :=
    ((Ideal.Quotient.mkₐ A' (Ideal.span {1 - e})).restrictScalars A).comp
      Algebra.TensorProduct.includeRight
  let f₀ : B →ₐ[A] C ⧸ J := (f.restrictScalars A).comp ι
  have hf₀ : IsLocalHom f₀ := ⟨fun b hb ↦ by
    by_contra hb'
    have hmem : ι b ∈ maximalIdeal S := by
      rw [← hmS]
      exact Ideal.mem_map_of_mem _ (map_maximalIdeal_le_of_isMaximal A' P
        (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hb')))
    exact (mem_maximalIdeal _).mp hmem (isUnit_of_map_unit f _ hb)⟩
  obtain ⟨g₀, hg₀⟩ := h J hJ f₀ hf₀
  let G : A' ⊗[A] B →ₐ[A'] C :=
    Algebra.TensorProduct.lift (Algebra.ofId A' C) g₀ fun _ _ ↦ Commute.all _ _
  have hG : (Ideal.Quotient.mkₐ A' J).comp G = f.comp (Ideal.Quotient.mkₐ A' _) := by
    refine Algebra.TensorProduct.ext (AlgHom.ext fun a ↦ ?_) (AlgHom.ext fun b ↦ ?_)
    · simp only [G, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.ofId_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_algebraMap]
      exact (f.commutes a).symm
    · have := congr($hg₀ b)
      simpa [G, f₀, ι] using this
  have hJ' : J ≠ ⊤ := fun hJ' ↦ by
    have : (⊤ : Ideal C) = ⊥ := by rw [← hJ, hJ', Ideal.top_pow]
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (eq_top_iff.mpr (this ▸ bot_le))
  have hG1 : G (1 - e) = 0 := by
    refine (he.one_sub.map G).eq_zero_of_mem_jacobson
      ((IsLocalRing.le_maximalIdeal hJ').trans (IsLocalRing.maximalIdeal_le_jacobson _) ?_)
    have := congr($hG (1 - e))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  let G' : S →ₐ[A'] C := Ideal.Quotient.liftₐ _ G fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hG1, mul_zero]
  refine ⟨G', Ideal.Quotient.algHom_ext _ ?_⟩
  rw [AlgHom.comp_assoc]
  exact hG

variable [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal B) B]

/-- III.2.1, (iv bis) ⇒ (i), for a finite residue extension: SGA takes `A'` finite free local
making the residue extensions of `A' ⊗ B` trivial (`exists_finite_free_residue_trivial`); the
local components of `A' ⊗ B` inherit the lifting property, and are power series rings by
Corollary III.2.2. -/
theorem SqZeroLocalArtinianLiftingProperty.formallySmoothLocal [Module.Finite A (ResidueField B)]
    (h : SqZeroLocalArtinianLiftingProperty A B) : FormallySmoothLocal A B := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := exists_finite_free_residue_trivial (A := A) (B := B)
  exact ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun P _ ↦ exists_algEquiv_localization_of_artinianLiftingProperty A' P (hA' P ‹_›)
      fun e he heP hQ _ _ _ _ _ _ _ ↦ h.artinianLiftingProperty_quotient A' P e he heP hQ⟩

/-- Theorem III.2.1: let `A → B` be a local homomorphism of complete noetherian local rings with
finite residue extension. The following are equivalent: (i) `B` is formally smooth over `A`
(Definition III.1.1); (ii) the lifting property for complete local rings; (iii) the lifting property
for nilpotent thickenings (continuous maps); (iv) the lifting property for local artinian rings
finite over `A`; (iv bis) the same for square-zero ideals. -/
theorem formallySmooth_tfae' [Module.Finite A (ResidueField B)] :
    List.TFAE [FormallySmoothLocal A B, CompleteLiftingProperty A B,
      AdicFormallySmooth A (maximalIdeal B), LocalArtinianLiftingProperty A B,
      SqZeroLocalArtinianLiftingProperty A B] := by
  tfae_have 1 → 3 := adicFormallySmooth_of_formallySmoothLocal'
  tfae_have 3 → 2 := AdicFormallySmooth.completeLiftingProperty
  tfae_have 2 → 4 := CompleteLiftingProperty.localArtinianLiftingProperty
  tfae_have 4 → 5 := LocalArtinianLiftingProperty.sqZero
  tfae_have 5 → 1 := SqZeroLocalArtinianLiftingProperty.formallySmoothLocal
  tfae_finish

end Components

end SGA.SGA1.ExposeIII
