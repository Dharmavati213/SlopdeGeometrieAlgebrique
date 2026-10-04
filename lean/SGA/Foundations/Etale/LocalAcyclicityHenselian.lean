/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.HenselianFinite
import SGA.Foundations.HenselianFiniteLocal
import SGA.Foundations.Cohomology.GeometricConnectedness

/-!
# Connected integral schemes over a strictly henselian local ring

Let `A` be a henselian local ring.

* `HenselianLocalRing.isLocalRing_of_isIntegral`: a nonzero integral `A`-algebra with only trivial
  idempotents is local. Two maximal ideals `𝔮 ≠ 𝔮'` are separated by an element `f`, and the finite
  subalgebra `A[f]` is a product of local rings (Stacks 04GG (10),
  `HenselianLocalRing.exists_isIdempotentElem_notMem_iff`), which gives an idempotent in `𝔮'` and
  not in `𝔮`.
* `IsStrictlyHenselian.bijective_algebraMap_of_isIntegral`: if moreover `A` is strictly henselian,
  `B` is such an algebra and `C` is a finite étale `B`-algebra with only trivial idempotents, then
  `B → C` is bijective: `B` and `C` are local, the residue field of `B` is algebraic over the
  separably closed residue field of `A`, hence separably closed, so `C` has a `B`-point in the
  residue field of `B`.
* `AlgebraicGeometry.isIso_of_isFinite_of_etale_of_isIntegralHom`: the scheme version. If
  `X ⟶ Spec A` is integral and `X` is connected, every connected finite étale `X`-scheme is
  isomorphic to `X`: `X` is simply connected. This applies to the Milnor fibres of a morphism to
  the spectrum of a field, which are purely inseparable base changes of strictly local schemes.

## References

* [EGA IV, 18.5, 18.8][ega4]
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

universe u

open CategoryTheory IsLocalRing AlgebraicGeometry.CohomologyAux

noncomputable section

namespace HenselianLocalRing

variable {C : Type*} [CommRing C]

/-- The maximal ideals of an integral algebra over a local ring lie over the maximal ideal. -/
lemma comap_eq_maximalIdeal_of_isMaximal {A : Type*} [CommRing A] [IsLocalRing A] [Algebra A C]
    [Algebra.IsIntegral A C] {M : Ideal C} (hM : M.IsMaximal) :
    M.comap (algebraMap A C) = maximalIdeal A :=
  eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)

/-- Over a henselian local ring `A`, a nonzero integral `A`-algebra with only trivial idempotents
(i.e. with connected spectrum) is local. -/
theorem isLocalRing_of_isIntegral (A : Type*) [CommRing A] [HenselianLocalRing A] [Algebra A C]
    [Algebra.IsIntegral A C] [Nontrivial C] (h : TrivialIdempotents C) : IsLocalRing C := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' ↦ ?_⟩
  by_contra hne
  obtain ⟨f, hfM', hfM⟩ : ∃ f ∈ M', f ∉ M := by
    by_contra! H
    exact hne (hM'.eq_of_le hM.ne_top H)
  let C' := Algebra.adjoin A ({f} : Set C)
  have : Module.Finite A C' :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral f)
  let q : PrimeSpectrum C' := ⟨M.comap C'.val.toRingHom, Ideal.comap_isPrime _ _⟩
  let q' : PrimeSpectrum C' := ⟨M'.comap C'.val.toRingHom, Ideal.comap_isPrime _ _⟩
  have hcomap (N : Ideal C) : (N.comap C'.val.toRingHom).comap (algebraMap A C') =
      N.comap (algebraMap A C) := by
    rw [Ideal.comap_comap]
    congr 1
  have hq : q.asIdeal.comap (algebraMap A C') = maximalIdeal A :=
    (hcomap M).trans (comap_eq_maximalIdeal_of_isMaximal hM)
  have hq' : q'.asIdeal.comap (algebraMap A C') = maximalIdeal A :=
    (hcomap M').trans (comap_eq_maximalIdeal_of_isMaximal hM')
  obtain ⟨e, he, hsep⟩ := exists_isIdempotentElem_notMem_iff (A := A) q hq
  have h₁ : (e : C) ∉ M := (hsep q hq).mpr rfl
  have h₂ : (e : C) ∈ M' := by
    by_contra h₂
    have hqq : q' = q := (hsep q' hq').mp h₂
    have hf : (⟨f, Algebra.self_mem_adjoin_singleton A f⟩ : C') ∈ q'.asIdeal := hfM'
    rw [hqq] at hf
    exact hfM hf
  rcases h (e : C) (he.map C'.val) with h₀ | h₀
  · exact h₁ (h₀ ▸ M.zero_mem)
  · exact hM'.ne_top ((Ideal.eq_top_iff_one _).mpr (h₀ ▸ h₂))

end HenselianLocalRing

namespace IsStrictlyHenselian

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
  [Algebra.Etale B C]

/-- Let `A` be strictly henselian, `B` a nonzero integral `A`-algebra with only trivial idempotents
and `C` a nonzero finite étale `B`-algebra with only trivial idempotents. Then `B → C` is
bijective. -/
theorem bijective_algebraMap_of_isIntegral (A : Type*) [CommRing A] [IsStrictlyHenselian A]
    [Algebra A B] [Algebra.IsIntegral A B] [Nontrivial B] [Nontrivial C]
    (hB : TrivialIdempotents B) (hC : TrivialIdempotents C) :
    Function.Bijective (algebraMap B C) := by
  have : IsLocalRing B := HenselianLocalRing.isLocalRing_of_isIntegral A hB
  let _ : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.trans B
  have : IsLocalRing C := HenselianLocalRing.isLocalRing_of_isIntegral A hC
  have : IsLocalHom (algebraMap B C) := IsLocalRing.isLocalHom_of_finite (A := B) C
  have : IsLocalHom (algebraMap A B) :=
    ((local_hom_TFAE (algebraMap A B)).out 1 5).mpr
      (HenselianLocalRing.comap_eq_maximalIdeal_of_isMaximal inferInstance)
  -- the residue field of `B` is separably closed
  have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective x
    have hb : IsIntegral A (residue B b) :=
      (Algebra.IsIntegral.isIntegral b).map (IsScalarTower.toAlgHom A B (ResidueField B))
    exact hb.tower_top
  have : IsSepClosed (ResidueField B) := Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)
  -- so it is the residue field of `C`
  have hsurj : Function.Surjective (algebraMap (ResidueField B) (ResidueField C)) :=
    IsSepClosed.algebraMap_surjective _ _
  let e : ResidueField B ≃ₐ[B] ResidueField C :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom B (ResidueField B) (ResidueField C))
      ⟨(algebraMap (ResidueField B) (ResidueField C)).injective, hsurj⟩
  exact IsLocalRing.bijective_algebraMap_of_finite_of_etale
    (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom B C (ResidueField C)))

end IsStrictlyHenselian

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be a strictly henselian local ring and `p : X ⟶ Spec A` integral with `X` connected.
Every finite étale `q : Z ⟶ X` with `Z` connected is an isomorphism: `X` is simply connected. -/
theorem isIso_of_isFinite_of_etale_of_isIntegralHom {A : CommRingCat.{u}} [IsStrictlyHenselian A]
    {X Z : Scheme.{u}} (p : X ⟶ Spec A) [IsIntegralHom p] [ConnectedSpace X] (q : Z ⟶ X)
    [IsFinite q] [Etale q] [ConnectedSpace Z] : IsIso q := by
  have : IsAffine X := isAffine_of_isAffineHom p
  have : IsAffine Z := isAffine_of_isAffineHom q
  -- `Γ(X, ⊤)` is integral over `A`
  let φ : A ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso A).inv ≫ p.appTop
  have hp : p = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have : Algebra.IsIntegral A Γ(X, ⊤) := by
    have : IsIntegralHom (Spec.map φ) := by
      have : Spec.map φ = X.isoSpec.inv ≫ p := by rw [hp, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    exact ⟨IsIntegralHom.SpecMap_iff.mp this⟩
  -- `Γ(Z, ⊤)` is finite étale over `Γ(X, ⊤)`
  let _ : Algebra Γ(X, ⊤) Γ(Z, ⊤) := q.appTop.hom.toAlgebra
  have : Module.Finite Γ(X, ⊤) Γ(Z, ⊤) :=
    (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance |>.2
  have : Algebra.Etale Γ(X, ⊤) Γ(Z, ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.appTop @Etale q inferInstance)
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  have hbij : Function.Bijective q.appTop.hom :=
    IsStrictlyHenselian.bijective_algebraMap_of_isIntegral A
      (trivialIdempotents_of_connectedSpace (W := X))
      (trivialIdempotents_of_connectedSpace (W := Z))
  have : IsIso q.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have h := Scheme.isoSpec_hom_naturality q
  have : IsIso (q ≫ X.isoSpec.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right q X.isoSpec.hom

end AlgebraicGeometry
