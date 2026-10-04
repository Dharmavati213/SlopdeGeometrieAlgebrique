/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import SGA.Foundations.CommAlg.PurityScheme
import SGA.Foundations.NormalizationFinite

/-!
# The normalization of an integral scheme is birational

Let `Z` be an integral scheme and `ν : Z' ⟶ Z` its normalization (mathlib's relative normalization
of `Spec K(Z) ⟶ Z`, see `SGA.Foundations.NormalizationFinite`). We show that `ν` is an isomorphism
over a nonempty open when `Z` is locally of finite type over a perfect field, which is the
birationality needed to use `ν` as a desingularization in dimension `≤ 1`:

* `exists_ne_zero_forall_isIntegral_mul_mem`: if the integral closure `Ā` of a domain `A` in its
  fraction field is a finite `A`-module, some `s ≠ 0` of `A` satisfies `s Ā ⊆ A` (a nonzero
  element of the conductor);
* `isIntegrallyClosed_of_forall_isIntegral_mul_mem`: for such an `s`, `A[1/s]` is integrally
  closed;
* `AlgebraicGeometry.isIso_fromNormalization_restrict`: `ν` is an isomorphism over every nonempty
  affine open whose ring of sections is integrally closed;
* `AlgebraicGeometry.isIso_fromNormalization_restrict_of_isIntegrallyClosed`: `ν` is an isomorphism
  over every open whose local rings are integrally closed (the normal locus), e.g. a regular open;
* `AlgebraicGeometry.exists_isAffineOpen_isIntegrallyClosed`: if `Z` is locally of finite type over
  a perfect field, such an open exists (the integral closure is finite by E. Noether's theorem,
  `Algebra.FiniteType.finite_integralClosure`, and one inverts an element of the conductor).

Lemmas for the normal crossings structure of the boundary of a regular curve (used for the strong
form of desingularization in dimension `≤ 1`):

* `TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton`: in a
  noetherian quasi-sober space a closed set of closed points is finite;
* `Ideal.exists_notMem_map_eq_span_singleton`: an element generating `p A_p` generates `p A_t` for
  some `t ∉ p` (`p` finitely generated);
* `RingHom.etale_of_finiteType_of_field`: a field of finite type over a perfect field is étale over
  it;
* `AlgebraicGeometry.etale_subschemeι_ofIdealTop_comp`: the closed point `V(I)`, `I` maximal, of an
  affine scheme locally of finite type over a perfect field is étale over the field.

## References

* [A. Grothendieck, *EGA* II, 6.3][EGA2]; [*EGA* IV₂, 7.8.3][EGA4]
* [Stacks Project, Tag 00GB](https://stacks.math.columbia.edu/tag/00GB) (Zariski's lemma)
-/

universe u

open CategoryTheory Limits

section Algebra

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- If the integral closure `Ā` of a domain `R` in its fraction field is a finite `R`-module, there
is `s ≠ 0` in `R` with `s Ā ⊆ R` (a nonzero element of the conductor). -/
lemma exists_ne_zero_forall_isIntegral_mul_mem [Module.Finite R (integralClosure R K)] :
    ∃ s : R, s ≠ 0 ∧
      ∀ x : K, IsIntegral R x → ∃ a : R, algebraMap R K a = algebraMap R K s * x := by
  have hfg : (Subalgebra.toSubmodule (integralClosure R K)).FG :=
    Module.Finite.iff_fg.mp ‹Module.Finite R (integralClosure R K)›
  obtain ⟨s, hs, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hfg
  refine ⟨s, nonZeroDivisors.ne_zero hs, fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := h x hx
  exact ⟨a, by rw [ha, Algebra.smul_def]⟩

omit [IsDomain R] in
/-- Let `R'` be a domain with fraction field `K`, `s ∈ R'` such that `s x ∈ R'` for every `x ∈ K`
integral over `R'`, and `R = R'[1/s]`. Then `R` is integrally closed. -/
lemma isIntegrallyClosed_of_forall_isIntegral_mul_mem {R' : Type*} [CommRing R'] [IsDomain R']
    [Algebra R' K] [Algebra R' R] [IsScalarTower R' R K] (s : R') [IsLocalization.Away s R]
    (hs : ∀ x : K, IsIntegral R' x → ∃ a : R', algebraMap R' K a = algebraMap R' K s * x) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff K]
  intro y hy
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := hy.exists_multiple_integral_of_isLocalization
    (Submonoid.powers s) y
  obtain ⟨a, ha⟩ := hs _ hm
  have hu : IsUnit (algebraMap R' R s) := IsLocalization.Away.algebraMap_isUnit s
  obtain ⟨u, hu'⟩ := hu
  refine ⟨algebraMap R' R a * ↑(u ^ (m + 1))⁻¹, ?_⟩
  have hsK : algebraMap R' K s = algebraMap R K u := by
    rw [hu', ← IsScalarTower.algebraMap_apply]
  have hsm : (⟨s ^ m, m, rfl⟩ : Submonoid.powers s) • y = algebraMap R' K s ^ m * y := by
    rw [Submonoid.smul_def, Algebra.smul_def, map_pow]
  rw [hsm, ← mul_assoc, ← pow_succ'] at ha
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ha, hsK, ← map_pow, mul_comm, ← mul_assoc,
    ← map_mul, ← Units.val_pow_eq_pow_val, Units.inv_mul, map_one, one_mul]

end Algebra

namespace AlgebraicGeometry

variable {Z : Scheme.{u}} [IsIntegral Z]

/-- `Spec K(Z) ⟶ Z`, the generic point of the integral scheme `Z`. -/
local notation "η" => Z.fromSpecStalk (genericPoint Z)

/-- The normalization of an integral scheme is an isomorphism over every nonempty affine open
whose ring of sections is integrally closed. -/
theorem isIso_fromNormalization_restrict {V : Z.Opens} (hV : IsAffineOpen V) [Nonempty V]
    [IsIntegrallyClosed Γ(Z, V)] : IsIso ((η).fromNormalization ∣_ V) := by
  refine (isIso_morphismRestrict_iff_isIso_app _ hV).mpr
    ((ConcreteCategory.isIso_iff_bijective _).mpr ?_)
  rw [Scheme.Hom.fromNormalization_app (η) hV]
  let e := Scheme.functionFieldIsoSections V
  have he := Scheme.germToFunctionField_comp_functionFieldIsoSections V
  let := ((η).app V).hom.toAlgebra
  have : IsFractionRing Γ(Z, V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hV
  -- the `Γ(Z, V)`-algebra map `Γ(Spec K(Z), η⁻¹ V) → K(Z)`
  let φ : Γ(Spec Z.functionField, η ⁻¹ᵁ V) →ₐ[Γ(Z, V)] Z.functionField :=
    { e.inv.hom with
      commutes' := fun r ↦ by
        change e.inv ((η).app V r) = Z.germToFunctionField V r
        rw [← he, CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id,
          CommRingCat.id_apply] }
  have hinj : Function.Injective (algebraMap Γ(Z, V) Γ(Spec Z.functionField, η ⁻¹ᵁ V)) := by
    change Function.Injective ((η).app V).hom
    rw [← he, CommRingCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso e.hom).1.comp
      (Scheme.germToFunctionField_injective Z V)
  have hb : Function.Bijective
      (algebraMap Γ(Z, V) (integralClosure Γ(Z, V) Γ(Spec Z.functionField, η ⁻¹ᵁ V))) := by
    refine ⟨fun a b hab ↦ hinj (congrArg Subtype.val hab), fun x ↦ ?_⟩
    obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (K := Z.functionField)).mp
      (x.2.map φ)
    refine ⟨r, Subtype.ext ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e.inv).1
    change φ (algebraMap _ _ r) = φ x
    rw [AlgHom.commutes, ← hr]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Hom.normalizationObjIso (η) hV).inv).comp hb

/-- The ring of sections of an integral scheme over a nonempty affine open is integrally closed if
the local rings at the points of the open are. -/
lemma isIntegrallyClosed_of_isAffineOpen {V : Z.Opens} (hV : IsAffineOpen V) [Nonempty V]
    (h : ∀ z ∈ V, IsIntegrallyClosed (Z.presheaf.stalk z)) : IsIntegrallyClosed Γ(Z, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
  have := h _ (hV.fromSpec_mem ⟨P, hP.isPrime⟩)
  exact IsIntegrallyClosed.of_equiv (hV.localizationAtPrimeEquivStalk ⟨P, hP.isPrime⟩).symm

/-- The normalization of an integral scheme is an isomorphism over every open subset whose local
rings are integrally closed (EGA II 6.3: the normalization does not change the normal locus). -/
theorem isIso_fromNormalization_restrict_of_isIntegrallyClosed {U : Z.Opens}
    (h : ∀ z ∈ U, IsIntegrallyClosed (Z.presheaf.stalk z)) :
    IsIso ((η).fromNormalization ∣_ U) := by
  have hcov (x : U) : ∃ W : U.toScheme.Opens, IsAffineOpen W ∧ x ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨W, hW, hxW⟩
  choose W hWa hxW using hcov
  have hW : iSup W = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    W hW).mpr fun x ↦ ?_
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict _ U (W x))).mpr ?_
  have hV : IsAffineOpen (U.ι ''ᵁ W x) := (hWa x).image_of_isOpenImmersion U.ι
  have : Nonempty (U.ι ''ᵁ W x) := ⟨⟨U.ι x, ⟨x, hxW x, rfl⟩⟩⟩
  have : IsIntegrallyClosed Γ(Z, U.ι ''ᵁ W x) :=
    isIntegrallyClosed_of_isAffineOpen hV fun z hz ↦ h z (U.ι_image_le (W x) hz)
  exact isIso_fromNormalization_restrict hV

variable {k : Type u} [Field k] [PerfectField k] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
/-- An integral scheme locally of finite type over a perfect field has a nonempty affine open
whose ring of sections is integrally closed: on an affine open `U`, the normalization of
`Γ(Z, U)` is finite (E. Noether), and `Γ(Z, D(s))` is integrally closed for `s ≠ 0` in its
conductor. -/
theorem exists_isAffineOpen_isIntegrallyClosed :
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧ IsIntegrallyClosed Γ(Z, V) := by
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(Z, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U le_top
  have hft : ψ.hom.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv _).mpr
      (p.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let := ψ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(Z, U) := hft
  have : IsFractionRing Γ(Z, U) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z U hU
  have : Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) Z.functionField) :=
    Algebra.FiniteType.finite_integralClosure k Γ(Z, U) Z.functionField Z.functionField
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_forall_isIntegral_mul_mem (R := Γ(Z, U))
    (K := Z.functionField)
  have hV : IsAffineOpen (Z.basicOpen s) := hU.basicOpen s
  have hne : (Z.basicOpen s : Set Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hs0 ((basicOpen_eq_bot_iff s).mp (TopologicalSpace.Opens.ext h))
  have : Nonempty (Z.basicOpen s) := hne.to_subtype
  have : IsLocalization.Away s Γ(Z, Z.basicOpen s) := hU.isLocalization_basicOpen s
  have : IsFractionRing Γ(Z, Z.basicOpen s) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z _ hV
  have : IsScalarTower Γ(Z, U) Γ(Z, Z.basicOpen s) Z.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, Scheme.germToFunctionField]
    rw [← CommRingCat.hom_comp, Z.presheaf.germ_res]
  exact ⟨_, hV, hne,
    isIntegrallyClosed_of_forall_isIntegral_mul_mem (K := Z.functionField) s hs⟩

end AlgebraicGeometry

/-- In a noetherian quasi-sober space, a closed set all of whose points are closed is finite: its
irreducible components are the closures of their generic points, hence points. -/
lemma TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {Y : Set X} (hY : IsClosed Y)
    (h : ∀ y ∈ Y, IsClosed ({y} : Set X)) : Y.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hY
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have ht' : t = {ζ} := by rw [← hζ.def, (h ζ ⟨t, ht, hζ.mem⟩).closure_eq]
  rw [ht']
  exact Set.finite_singleton ζ

/-- Let `p` be a finitely generated prime of a ring `A` and `f ∈ p` an element generating `p A_p`.
Then `f` generates `p A_t` for some `t ∉ p`. -/
lemma Ideal.exists_notMem_map_eq_span_singleton {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hp : p.FG) (f : A) (hf : f ∈ p)
    (hfp : p.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span {algebraMap A (Localization.AtPrime p) f}) :
    ∃ t ∉ p, ∀ (At : Type*) [CommRing At] [Algebra A At] [IsLocalization.Away t At],
      p.map (algebraMap A At) = Ideal.span {algebraMap A At f} := by
  classical
  obtain ⟨S, rfl⟩ := hp
  have key (g : A) (hg : g ∈ S) : ∃ t ∉ Ideal.span (S : Set A), ∃ b : A, t * g = b * f := by
    have hmem : algebraMap A (Localization.AtPrime (Ideal.span (S : Set A))) g ∈
        Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span (S : Set A))) f} := by
      rw [← hfp]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span hg)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨⟨b, u⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Ideal.span (S : Set A)).primeCompl c
    have h₂ : algebraMap A (Localization.AtPrime (Ideal.span (S : Set A))) (b * f) =
        algebraMap A (Localization.AtPrime (Ideal.span (S : Set A))) (g * u) := by
      rw [map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]
    obtain ⟨v, hv⟩ := (IsLocalization.eq_iff_exists (Ideal.span (S : Set A)).primeCompl _).mp h₂
    refine ⟨v * u, (Ideal.span (S : Set A)).primeCompl.mul_mem v.2 u.2, v * b, ?_⟩
    linear_combination -hv
  choose t ht b hb using key
  refine ⟨∏ g ∈ S.attach, t g.1 g.2, ?_, fun At _ _ _ ↦ ?_⟩
  · exact (Ideal.span (S : Set A)).primeCompl.prod_mem fun g _ ↦ ht g.1 g.2
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hf))
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨g, hg, rfl⟩
  have hu : IsUnit (algebraMap A At (t g hg)) := by
    have hunit := IsLocalization.Away.algebraMap_isUnit (R := A) (∏ g ∈ S.attach, t g.1 g.2)
      (S := At)
    rw [← Finset.mul_prod_erase S.attach (fun g ↦ t g.1 g.2) (Finset.mem_attach _ ⟨g, hg⟩),
      map_mul] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  obtain ⟨w, hw⟩ := hu
  have : algebraMap A At g = ↑w⁻¹ * algebraMap A At (b g hg) * algebraMap A At f := by
    rw [mul_assoc, ← map_mul, ← hb g hg, map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
  rw [SetLike.mem_coe, this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- A field of finite type over a perfect field `k` is étale over `k` (Zariski's lemma: it is a
finite, hence separable, extension). -/
lemma RingHom.etale_of_finiteType_of_field {k L : Type u} [Field k] [PerfectField k] [Field L]
    (φ : k →+* L) (hφ : φ.FiniteType) : φ.Etale := by
  algebraize [φ]
  have : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  have : Algebra.FinitePresentation k L := Algebra.FinitePresentation.of_finiteType.mp hφ
  have : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  exact { formallyEtale := this, finitePresentation := inferInstance }

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be affine and locally of finite type over a perfect field `k`, and `I` a maximal ideal
of `Γ(X, ⊤)`. The closed subscheme `V(I)` (a closed point with its reduced structure) is étale
over `k`. -/
theorem etale_subschemeι_ofIdealTop_comp {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    (I : Ideal Γ(X, ⊤)) [I.IsMaximal] :
    Etale ((Scheme.IdealSheafData.ofIdealTop I).subschemeι ≫ g) := by
  set J := Scheme.IdealSheafData.ofIdealTop I
  let U₀ : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let j := J.subschemeCover.f U₀
  have : IsOpenImmersion j := inferInstance
  have hj : Surjective j := by
    refine ⟨fun y ↦ ?_⟩
    have hy : y ∈ j.opensRange := by
      rw [J.opensRange_subschemeCover_map U₀]
      exact Set.mem_univ (J.subschemeι y)
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, hj⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @Etale j, ← Category.assoc,
    J.subschemeCover_map_subschemeι U₀, Category.assoc, ← Category.assoc (J.glueDataObjι U₀),
    J.glueDataObjι_ι, Category.assoc]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (U₀.2.fromSpec ≫ g)
  rw [← hφ, ← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Etale)]
  have hJ : J.ideal U₀ = I := by
    simp only [J, Scheme.IdealSheafData.ofIdealTop_ideal]
    convert Ideal.map_id I
    ext x
    change X.presheaf.map (𝟙 _) x = x
    rw [X.presheaf.map_id]
    rfl
  have : (J.ideal U₀).IsMaximal := hJ ▸ inferInstance
  let := Ideal.Quotient.field (J.ideal U₀)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  exact RingHom.etale_of_finiteType_of_field (k := k) (L := Γ(X, U₀) ⧸ J.ideal U₀) _
    (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hft)

end AlgebraicGeometry
