/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.FiniteLimits
import SGA.SGA1.ExposeXII.RiemannCurvesSeparable

/-!
# Coverings that are algebraic over a dense open subset

A finite covering `E` of `X(ℂ)`, `X = Spec A`, is *generically algebraic*
(`RiemannHigher.IsGenericallyAlgebraic`) if there is a nonzerodivisor `g ∈ A` such that the
restriction of `E` to `D(g)(ℂ)` is `S(ℂ)` for a finite étale `A_g`-algebra `S`.
`GenericRiemannExistenceStatement` says that this holds for every finite covering of `X(ℂ)`,
`X` integral affine of finite type over `ℂ`; together with the extension of coverings across
divisors it gives XII.5.1 (see `SGA.SGA1.ExposeXII.RiemannHigher`).

This file has the bookkeeping for base change of coverings along maps of `ℂ`-algebras:

* `RiemannHigher.baseChangePointsFunctorIso`: `Ψ` commutes with base change,
  `(B ⊗_A S)(ℂ) ≅ B(ℂ) ×_{A(ℂ)} S(ℂ)` (XII.1.2, `Points.homeomorphTensorProduct`), hence
  `RiemannHigher.mem_essImage_baseChange`: the pullback of an algebraic covering is algebraic;
* `TopCat.FiniteCovering.baseChangeCompIso`, `baseChangeIdIso`: base change is functorial up to
  isomorphism;
* `RiemannHigher.mem_essImage_of_baseChange_bijective`: along an isomorphism of `ℂ`-algebras,
  algebraicity descends;
* `RiemannHigher.IsGenericallyAlgebraic.of_restrictAway`: generic algebraicity of the restriction
  to a dense basic open implies generic algebraicity.
-/

noncomputable section

open CategoryTheory Topology Opposite TensorProduct CommAlgCat

namespace TopCat.FiniteCovering

variable {X Y Z : TopCat.{0}}

/-- Base change along a composite is the composite of the base changes. -/
def baseChangeCompIso (f : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (h : g ≫ f = k) (E : FiniteCovering X) :
    (baseChange k).obj E ≅ (baseChange g).obj ((baseChange f).obj E) :=
  isoOfBijective
    ⟨fun q ↦ baseChangeMk g _ (((baseChange k).obj E).obj.hom q)
      (baseChangeMk f E (g (((baseChange k).obj E).obj.hom q)) (baseChangeSnd k E q) (by
        rw [hom_baseChangeSnd]
        change (g ≫ f) (((baseChange k).obj E).obj.hom q) = _
        rw [h])) rfl, by
      refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
      exact Continuous.subtype_mk (Continuous.prodMk (g.hom.continuous.comp (by fun_prop))
        (by fun_prop)) _⟩
    (fun _ ↦ rfl)
    ⟨fun q q' hqq' ↦ baseChange_ext (congrArg (fun x ↦ ((baseChange g).obj _).obj.hom x) hqq')
      (congrArg (fun x ↦ baseChangeSnd f E (baseChangeSnd g _ x)) hqq'), fun q ↦ by
      refine ⟨baseChangeMk k E (((baseChange g).obj _).obj.hom q)
        (baseChangeSnd f E (baseChangeSnd g _ q)) ?_, ?_⟩
      · rw [hom_baseChangeSnd, hom_baseChangeSnd]
        change _ = (g ≫ f) _
        rw [h]
      · refine baseChange_ext rfl (baseChange_ext ?_ rfl)
        exact (hom_baseChangeSnd g _ q).symm⟩

/-- Base change along the identity. -/
def baseChangeIdIso (E : FiniteCovering X) : (baseChange (𝟙 X)).obj E ≅ E :=
  isoOfBijective ⟨baseChangeSnd (𝟙 X) E, (baseChangeSnd (𝟙 X) E).hom.continuous⟩
    (fun q ↦ hom_baseChangeSnd (𝟙 X) E q)
    ⟨fun q q' hqq' ↦ baseChange_ext ((hom_baseChangeSnd (𝟙 X) E q).symm.trans
      ((congrArg E.obj.hom hqq').trans (hom_baseChangeSnd (𝟙 X) E q'))) hqq', fun e ↦
      ⟨baseChangeMk (𝟙 X) E (E.obj.hom e) e rfl, rfl⟩⟩

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII.RiemannHigher

open TopCat.FiniteCovering

section BaseChange

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The `ℂ`-algebra map `A → B` as an `A`-algebra structure on `B`. -/
abbrev algebraOfAlgHom (φ : A →ₐ[ℂ] B) : Algebra A B := φ.toRingHom.toAlgebra

lemma isScalarTower_of_algHom (φ : A →ₐ[ℂ] B) :
    letI := algebraOfAlgHom φ
    IsScalarTower ℂ A B :=
  letI := algebraOfAlgHom φ
  .of_algebraMap_eq fun c ↦ (φ.commutes c).symm

/-- XII.1.2 for `Ψ`: the finite étale `B`-algebra `B ⊗_A S` has `(B ⊗_A S)(ℂ) = B(ℂ) ×_{A(ℂ)} S(ℂ)`,
as a covering of `B(ℂ)`. -/
def baseChangePointsFunctorIso (φ : A →ₐ[ℂ] B) (S : FiniteEtale.{0} A) :
    letI := algebraOfAlgHom φ
    (pointsFunctor ℂ B).obj (op ((FiniteEtale.baseChange A B).obj S)) ≅
      (baseChange (pointsHom φ)).obj ((pointsFunctor ℂ A).obj (op S)) := by
  letI := algebraOfAlgHom φ
  haveI := isScalarTower_of_algHom φ
  letI := algebraOfFiniteEtale ℂ A S
  haveI := isScalarTower_of_finiteEtale ℂ A S
  letI iT := algebraOfFiniteEtale ℂ B ((FiniteEtale.baseChange A B).obj S)
  -- the identity of `B ⊗_A S`, from the `ℂ`-structure through `B` to the tensor product one
  let e : @AlgEquiv ℂ ((FiniteEtale.baseChange A B).obj S) (B ⊗[A] S) _ _ _ iT
      Algebra.TensorProduct.leftAlgebra :=
    @AlgEquiv.ofRingEquiv ℂ _ _ _ _ _ iT Algebra.TensorProduct.leftAlgebra (RingEquiv.refl _)
      (fun _ ↦ rfl)
  let h : Points ℂ ((FiniteEtale.baseChange A B).obj S) ≃ₜ Points.FiberProduct ℂ A B S :=
    (Points.homeomorph e).symm.trans (Points.homeomorphTensorProduct (K := ℂ) (A := A)
    (B := B) (C := S))
  refine isoOfBijective ⟨fun χ ↦ ⟨(h χ).1, (h χ).2⟩, ?_⟩ (fun χ ↦ rfl) ⟨?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp h.continuous) _
  · intro χ χ' hχ
    exact h.injective (Subtype.ext (congrArg Subtype.val hχ))
  · intro q
    refine ⟨h.symm ⟨q.1, q.2⟩, Subtype.ext ?_⟩
    change (h (h.symm ⟨q.1, _⟩)).1 = q.1
    rw [Homeomorph.apply_symm_apply]

/-- The pullback of an algebraic covering along a map of `ℂ`-algebras is algebraic. -/
theorem mem_essImage_baseChange (φ : A →ₐ[ℂ] B)
    {E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))} (hE : (pointsFunctor ℂ A).essImage E) :
    (pointsFunctor ℂ B).essImage ((baseChange (pointsHom φ)).obj E) := by
  obtain ⟨S, ⟨i⟩⟩ := hE
  let := algebraOfAlgHom φ
  exact ⟨op ((FiniteEtale.baseChange A B).obj S.unop),
    ⟨baseChangePointsFunctorIso φ S.unop ≪≫ (baseChange (pointsHom φ)).mapIso i⟩⟩

lemma pointsHom_comp {C : Type} [CommRing C] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    pointsHom ψ ≫ pointsHom φ = pointsHom (ψ.comp φ) := rfl

/-- Along an isomorphism of `ℂ`-algebras, a covering is algebraic if its pullback is. -/
theorem mem_essImage_of_baseChange_bijective (e : A ≃ₐ[ℂ] B)
    {E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))}
    (hE : (pointsFunctor ℂ B).essImage ((baseChange (pointsHom e.toAlgHom)).obj E)) :
    (pointsFunctor ℂ A).essImage E := by
  have h := mem_essImage_baseChange e.symm.toAlgHom hE
  refine Functor.essImage.ofIso ?_ h
  refine (baseChangeCompIso _ _ (𝟙 _) ?_ E).symm ≪≫ baseChangeIdIso E
  rw [pointsHom_comp]
  ext χ a
  change χ (e.symm (e a)) = χ a
  rw [AlgEquiv.symm_apply_apply]

end BaseChange

section Generic

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- A finite covering `E` of `X(ℂ)`, `X = Spec A`, is *generically algebraic*: for some
nonzerodivisor `g ∈ A` (so `D(g)` is dense in `X`, and `D(g)(ℂ)` dense in `X(ℂ)` for `A` of finite
type, `Points.dense_apply_ne_zero`), the restriction of `E` to `D(g)(ℂ)` is `S(ℂ)` for a finite
étale `A_g`-algebra `S`. -/
def IsGenericallyAlgebraic (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) : Prop :=
  ∃ g ∈ nonZeroDivisors A, (pointsFunctor ℂ (Localization.Away g)).essImage (restrictAway g E)

/-- An algebraic covering is generically algebraic (take `g = 1`). -/
theorem IsGenericallyAlgebraic.of_mem_essImage {E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))}
    (hE : (pointsFunctor ℂ A).essImage E) : IsGenericallyAlgebraic E :=
  ⟨1, one_mem _, mem_essImage_baseChange _ hE⟩

/-- Restriction to `D(g)` and then to `D(g')`, `g' ∈ A_g`, is restriction to `D(ga)` when `g'` is
associated to the image of `a`. -/
theorem mem_essImage_restrictAway_mul (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) (g a : A)
    (g' : Localization.Away g) (hg' : Associated (algebraMap A (Localization.Away g) a) g')
    (h : (pointsFunctor ℂ (Localization.Away g')).essImage (restrictAway g' (restrictAway g E))) :
    (pointsFunctor ℂ (Localization.Away (g * a))).essImage (restrictAway (g * a) E) := by
  have : IsLocalization.Away (g * a) (Localization.Away g') :=
    IsLocalization.Away.mul_of_associated (T := Localization.Away g') g a g' hg'
  let ε : Localization.Away (g * a) ≃ₐ[A] Localization.Away g' :=
    IsLocalization.algEquiv (Submonoid.powers (g * a)) (Localization.Away (g * a))
      (Localization.Away g')
  let ε' : Localization.Away (g * a) ≃ₐ[ℂ] Localization.Away g' := ε.restrictScalars ℂ
  refine mem_essImage_of_baseChange_bijective ε' ?_
  refine Functor.essImage.ofIso ?_ h
  refine (baseChangeCompIso _ _ _ ?_ E).symm ≪≫ baseChangeCompIso _ _ _ rfl E
  ext χ x
  change χ (algebraMap (Localization.Away g) (Localization.Away g')
    (algebraMap A (Localization.Away g) x)) = χ (ε (algebraMap A _ x))
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply A (Localization.Away g)
    (Localization.Away g')]

/-- Generic algebraicity of the restriction to a dense basic open subset `D(g)` implies generic
algebraicity. -/
theorem IsGenericallyAlgebraic.of_restrictAway {E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))}
    {g : A} (hg : g ∈ nonZeroDivisors A) (h : IsGenericallyAlgebraic (restrictAway g E)) :
    IsGenericallyAlgebraic E := by
  obtain ⟨g', hg', hE⟩ := h
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) g'
  dsimp only at hg' hE
  have hu : IsUnit (algebraMap A (Localization.Away g) (g ^ k)) :=
    IsLocalization.map_units _ (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
  have hass : Associated (algebraMap A (Localization.Away g) a)
      (IsLocalization.mk' (Localization.Away g) a (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)) := by
    have hinv : (↑hu.unit⁻¹ : Localization.Away g) * algebraMap A _ (g ^ k) = 1 :=
      hu.val_inv_mul
    refine ⟨hu.unit⁻¹, ?_⟩
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, mul_assoc]
    erw [hinv]
    rw [mul_one]
  have ha : a ∈ nonZeroDivisors A := by
    have ha' : algebraMap A (Localization.Away g) a ∈ nonZeroDivisors (Localization.Away g) := by
      obtain ⟨u, hu'⟩ := hass
      have : algebraMap A (Localization.Away g) a =
          IsLocalization.mk' (Localization.Away g) a (⟨g ^ k, k, rfl⟩ : Submonoid.powers g) *
            ↑u⁻¹ := by
        rw [← hu', mul_assoc, Units.mul_inv, mul_one]
      rw [this]
      exact mul_mem hg' (Units.isUnit _).mem_nonZeroDivisors
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
    have h0 : algebraMap A (Localization.Away g) x = 0 := by
      have := congrArg (algebraMap A (Localization.Away g)) hx
      rw [map_mul, map_zero] at this
      exact (mem_nonZeroDivisors_iff_right.mp ha') _ this
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ x).mp h0
    exact (mem_nonZeroDivisors_iff_left.mp (pow_mem hg m)) x (by simpa [mul_comm] using hm)
  exact ⟨g * a, mul_mem hg ha, mem_essImage_restrictAway_mul E g a _ hass hE⟩

/-- The localization of `A'` away from `e g` is the localization of `A` away from `g`, for an
isomorphism `e : A ≃ₐ[ℂ] A'`. -/
def awayAlgEquiv {A' : Type} [CommRing A'] [Algebra ℂ A'] (e : A ≃ₐ[ℂ] A') (g : A) :
    Localization.Away g ≃ₐ[ℂ] Localization.Away (e g) :=
  { IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers g) (T := Submonoid.powers (e g))
      (Localization.Away g) (Localization.Away (e g)) e.toRingEquiv
      (by rw [Submonoid.map_powers]; rfl) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply ℂ A (Localization.Away g),
        IsScalarTower.algebraMap_apply ℂ A' (Localization.Away (e g))]
      change IsLocalization.ringEquivOfRingEquiv _ _ _ _ _ = _
      rw [IsLocalization.ringEquivOfRingEquiv_eq]
      exact congrArg _ (e.commutes c) }

lemma awayAlgEquiv_algebraMap {A' : Type} [CommRing A'] [Algebra ℂ A'] (e : A ≃ₐ[ℂ] A') (g a : A) :
    awayAlgEquiv e g (algebraMap A _ a) = algebraMap A' _ (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (by rw [Submonoid.map_powers]; rfl) a

/-- Generic algebraicity is invariant under isomorphisms of `ℂ`-algebras: if the pullback of a
covering `E'` of `A'(ℂ)` to `A(ℂ)` along `e : A ≃ₐ[ℂ] A'` is generically algebraic, so is `E'`. -/
theorem IsGenericallyAlgebraic.of_algEquiv {A' : Type} [CommRing A'] [Algebra ℂ A']
    (e : A ≃ₐ[ℂ] A') {E' : TopCat.FiniteCovering (TopCat.of (Points ℂ A'))}
    (h : IsGenericallyAlgebraic ((baseChange (pointsHom e.symm.toAlgHom)).obj E')) :
    IsGenericallyAlgebraic E' := by
  obtain ⟨g, hg, hE⟩ := h
  refine ⟨e g, ?_, mem_essImage_of_baseChange_bijective (awayAlgEquiv e g).symm ?_⟩
  · refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ e.symm.injective ?_
    rw [map_zero]
    refine (mem_nonZeroDivisors_iff_right.mp hg) _ ?_
    rw [← e.symm_apply_apply g, ← map_mul, hy, map_zero]
  refine Functor.essImage.ofIso ?_ hE
  refine (baseChangeCompIso _ _ _ rfl _).symm ≪≫ baseChangeCompIso _ _ _ ?_ E'
  ext χ x
  change χ ((awayAlgEquiv e g).symm (algebraMap A' _ x)) = χ (algebraMap A _ (e.symm x))
  congr 1
  rw [AlgEquiv.symm_apply_eq, awayAlgEquiv_algebraMap, AlgEquiv.apply_symm_apply]

/-- The pullback of a covering along an isomorphism `e : A ≃ₐ[ℂ] A'` and back is the covering. -/
def baseChangeAlgEquivIso {A' : Type} [CommRing A'] [Algebra ℂ A'] (e : A ≃ₐ[ℂ] A')
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))) :
    (baseChange (pointsHom e.symm.toAlgHom)).obj ((baseChange (pointsHom e.toAlgHom)).obj E) ≅ E :=
  (baseChangeCompIso _ _ (𝟙 _) (by ext χ a; exact congrArg χ (e.symm_apply_apply a)) E).symm ≪≫
    baseChangeIdIso E

end Generic

/-- **Generic form of XII.5.1** (statement only): for `A` a domain of finite type over `ℂ`, every
finite covering of `X(ℂ)`, `X = Spec A`, is algebraic over a dense basic open subset `D(g)`,
`g ≠ 0` (`RiemannHigher.IsGenericallyAlgebraic`). This is the form in which the induction on the
dimension through families of punctured lines works (`SGA.SGA1.ExposeXII.RiemannHigher`, step 1);
XII.5.1 follows from it and the extension of coverings across divisors. -/
def GenericRiemannExistenceStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ A))), IsGenericallyAlgebraic E

end SGA.SGA1.ExposeXII.RiemannHigher
