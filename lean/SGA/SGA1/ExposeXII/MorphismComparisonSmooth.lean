/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.MorphismComparisonGlobal
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeII.SmoothnessAux
import Mathlib.RingTheory.Smooth.Fiber

/-!
# SGA 1, Exposé XII, 3.1 (iv): smoothness of `f` and of `f^an`

SGA proves XII.3.1 (iv) like (i)–(iii): `f` is smooth at a closed point `x` iff it is flat there
and its fibre is regular at `x` (the residue fields being `ℂ`), these two properties transfer
along the comparison morphisms (XII.2.1), and the smooth locus is open, hence everything since
`X` is a Jacobson scheme.

* `formallySmooth_iff_isRegularLocalRing_of_surjective`: a local algebra essentially of finite
  type over a field `k`, with residue field `k`, is formally smooth over `k` iff it is regular
  (II.5.10 at a rational point);
* `formallySmooth_iff_flat_and_isRegularLocalRing`: for a local homomorphism `A → B` essentially of
  finite type of noetherian local rings with trivial residue field extension, `B` is formally
  smooth over `A` iff it is flat and the closed fibre `B/𝔪_A B` is regular (II.2.1 plus II.5.10);
* `smooth_iff_forall_of_comparison`: XII.3.1 (iv) for an abstract comparison square;
* `AffineAnalytification.smooth_iff_forall`, `AnalyticGluing.smooth_iff_forall_analyticMap`:
  XII.3.1 (iv) for affine schemes and for separated schemes.

"`f^an` is smooth at `x`" is taken to mean that `f^an` is flat at `x` and its fibre
`𝒪_{X^an,x}/𝔪_{f^an(x)} 𝒪_{X^an,x}` is a regular local ring (flat with regular fibres, which is
how SGA argues); it is not shown to be equivalent to `f^an` being locally a projection
`Y^an × ℂⁿ → Y^an`.

References: SGA 1 XII.3.1, II.2.1, II.5.10; EGA IV 17.5.1.
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Algebra
open scoped TensorProduct

namespace SGA.SGA1.ExposeXII

namespace LocallyRingedSpaceComparison

section Field

variable (k C : Type u) [CommRing k] [CommRing C] [IsLocalRing C] [Algebra k C] [EssFiniteType k C]

/-- II.5.10 at a rational point: a local algebra `C` essentially of finite type over a field `k`
whose residue field is `k` is formally smooth over `k` iff it is a regular local ring. (The field
`k` is given as a commutative ring with `IsField k`, so that this applies to `A ⧸ 𝔪_A` without
instance diamonds.) -/
theorem formallySmooth_iff_isRegularLocalRing_of_surjective (hfield : IsField k)
    (hk : ∀ c : C, ∃ a : k, c - algebraMap k C a ∈ maximalIdeal C) :
    FormallySmooth k C ↔ IsRegularLocalRing C := by
  let := hfield.toField
  let T := EssFiniteType.subalgebra k C
  let M := EssFiniteType.submonoid k C
  let q : Ideal T := (maximalIdeal C).comap (algebraMap T C)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hMq : M ≤ q.primeCompl := fun m hm hmq ↦
    (hmq : algebraMap T C m ∈ maximalIdeal C) (IsLocalization.map_units C ⟨m, hm⟩)
  have : IsLocalization.AtPrime C q := IsLocalization.of_le M q.primeCompl hMq fun r hr ↦ by
    by_contra h
    exact hr ((mem_maximalIdeal _).mpr h)
  let e : Localization.AtPrime q ≃ₐ[T] C := IsLocalization.algEquiv q.primeCompl _ _
  let e' : Localization.AtPrime q ≃ₐ[k] C := e.restrictScalars k
  -- `T / q = k`
  have hsurj : Function.Surjective (algebraMap k (T ⧸ q)) := by
    intro t
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨c, hc⟩ := hk (algebraMap T C t)
    refine ⟨c, ?_⟩
    rw [IsScalarTower.algebraMap_apply k T (T ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq]
    change algebraMap T C (algebraMap k T c - t) ∈ maximalIdeal C
    rw [map_sub, ← IsScalarTower.algebraMap_apply, ← neg_sub, Ideal.neg_mem_iff]
    exact hc
  have hbij : Function.Bijective (algebraMap k (T ⧸ q)) :=
    ⟨(algebraMap k (T ⧸ q)).injective, hsurj⟩
  have hmax : q.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact (RingEquiv.ofBijective _ hbij).symm.toMulEquiv.isField hfield
  have hsep : Algebra.IsSeparable k (T ⧸ q) := ⟨fun x ↦ by
    obtain ⟨c, rfl⟩ := hsurj x
    exact isSeparable_algebraMap c⟩
  constructor
  · intro _
    have : IsSmoothAt k q := FormallySmooth.of_equiv e'.symm
    have := ExposeII.isRegularLocalRing_of_isSmoothAt k q
    exact IsRegularLocalRing.of_ringEquiv e'.toRingEquiv
  · intro h
    have : IsRegularLocalRing (Localization.AtPrime q) :=
      IsRegularLocalRing.of_ringEquiv e'.symm.toRingEquiv
    have := ExposeII.isSmoothAt_of_isRegularLocalRing_of_isMaximal k T q hsep this
    exact FormallySmooth.of_equiv e'

end Field

section Local

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] [EssFiniteType A B]

omit [IsNoetherianRing A] [EssFiniteType A B] in
/-- The residue field of the closed fibre `B/𝔪_A B` is `κ(A)` when `κ(A) → κ(B)` is surjective. -/
lemma exists_sub_mem_maximalIdeal_fibre
    (hres : Function.Surjective (ResidueField.map (algebraMap A B))) :
    haveI := isLocalRing_fibre (algebraMap A B)
    ∀ z : B ⧸ (maximalIdeal A).map (algebraMap A B), ∃ a : A ⧸ maximalIdeal A,
      z - algebraMap _ _ a ∈ maximalIdeal (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have := isLocalRing_fibre (algebraMap A B)
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := hres (residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← neg_sub,
    Ideal.neg_mem_iff] at ha
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have h := map_maximalIdeal_of_surjective (Ideal.Quotient.mk ((maximalIdeal A).map
    (algebraMap A B))) Ideal.Quotient.mk_surjective
  rw [← h]
  convert Ideal.mem_map_of_mem (Ideal.Quotient.mk _) ha using 1
  rw [map_sub]
  rfl

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] [EssFiniteType A B] in
private lemma formallySmooth_residueField_tensor
    (h : FormallySmooth (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] B)) :
    FormallySmooth (ResidueField A) (ResidueField A ⊗[A] B) :=
  h

/-- Flat with formally smooth closed fibre implies formally smooth (mathlib's
`FormallySmooth.of_formallySmooth_residueField_tensor`, for `B` essentially of finite type). -/
private lemma formallySmooth_of_quotient_tensor [Module.Flat A B]
    (h : FormallySmooth (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] B)) :
    FormallySmooth A B := by
  have := formallySmooth_residueField_tensor h
  have : FinitePresentation A (EssFiniteType.subalgebra A B) :=
    FinitePresentation.of_finiteType.mp inferInstance
  exact FormallySmooth.of_formallySmooth_residueField_tensor (EssFiniteType.submonoid A B)

/-- XII.3.1 (iv), local form of the algebraic side (II.2.1 and II.5.10): let `A → B` be a local
homomorphism of local rings, essentially of finite type, with `A` noetherian and
`κ(A) → κ(B)` bijective. Then `B` is formally smooth over `A` iff it is flat over `A` and the
closed fibre `B/𝔪_A B` is a regular local ring. -/
theorem formallySmooth_iff_flat_and_isRegularLocalRing
    (hres : Function.Surjective (ResidueField.map (algebraMap A B))) :
    FormallySmooth A B ↔ Module.Flat A B ∧
      IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have := isLocalRing_fibre (algebraMap A B)
  have hF := formallySmooth_iff_isRegularLocalRing_of_surjective (A ⧸ maximalIdeal A)
    (B ⧸ (maximalIdeal A).map (algebraMap A B))
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
    (exists_sub_mem_maximalIdeal_fibre hres)
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
  constructor
  · intro _
    refine ⟨ExposeII.flat_of_formallySmooth_of_essFiniteType, hF.mp ?_⟩
    exact FormallySmooth.of_equiv e.symm
  · rintro ⟨_, hreg⟩
    have := hF.mpr hreg
    exact formallySmooth_of_quotient_tensor (FormallySmooth.of_equiv e)

end Local

section Scheme

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- XII.3.1 (iv), algebraic side at closed points: for a morphism `f : X → Y` of schemes locally of
finite type over an algebraically closed field, `Y` locally noetherian, and a closed point `x`
with `f(x)` closed, `f` is smooth at `x` iff it is flat at `x` and its fibre is regular at `x`:
`𝒪_x/𝔪_{f(x)} 𝒪_x` is a regular local ring. -/
theorem formallySmooth_stalkMap_iff_of_isClosed [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (x : X) (hx : IsClosed {x})
    (hfx : IsClosed {f x}) :
    (f.stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.Flat ∧
      IsRegularLocalRing (X.presheaf.stalk x ⧸ (maximalIdeal _).map (f.stalkMap x).hom) := by
  have hbij := bijective_residueFieldMap_of_isClosed sX sY f hf x hx hfx
  have hess := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact formallySmooth_iff_flat_and_isRegularLocalRing hbij.2

end Scheme

variable {X Y : Scheme.{u}} {X' Y' : LocallyRingedSpace.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {φX : X' ⟶ X.toLocallyRingedSpace} {φY : Y' ⟶ Y.toLocallyRingedSpace}
  {K : Type u} [Field K] [IsAlgClosed K] (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- XII.3.1 (iv): let `f : X → Y` be a morphism locally of finite presentation of schemes locally
of finite type over an algebraically closed field `K`, and `f' : X' → Y'` a morphism of locally
ringed spaces over `f` through comparison morphisms `φX`, `φY` with `φX` onto the closed points of
`X` and `φY` into the closed points of `Y` (e.g. `f^an`). Then `f` is smooth iff `f'` is, at every
point `x'`, flat with regular fibre `𝒪_{x'}/𝔪_{f'(x')} 𝒪_{x'}`. -/
theorem smooth_iff_forall_of_comparison [IsLocallyNoetherian Y] [LocallyOfFinitePresentation f]
    (hf : f ≫ sY = sX) (hsq : f' ≫ φY = φX ≫ f.toLRSHom) (hX : IsComparison φX)
    (hY : IsComparison φY) (hrangeX : Set.range φX.base = closedPoints X)
    (hrangeY : Set.range φY.base ⊆ closedPoints Y) :
    Smooth f ↔ ∀ x', (f'.stalkMap x').hom.Flat ∧
      IsRegularLocalRing (X'.presheaf.stalk x' ⧸ (maximalIdeal _).map (f'.stalkMap x').hom) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hcl (x' : X') : IsClosed {φX.base x'} := by
    have : φX.base x' ∈ closedPoints X := hrangeX ▸ Set.mem_range_self x'
    exact this
  have hfcl (x' : X') : IsClosed {f (φX.base x')} := by
    have : f (φX.base x') = φY.base (f'.base x') := base_apply_eq f.toLRSHom f' φX φY hsq x'
    rw [this]
    exact hrangeY ⟨_, rfl⟩
  have key (x' : X') : (f.stalkMap (φX.base x')).hom.FormallySmooth ↔
      (f'.stalkMap x').hom.Flat ∧
        IsRegularLocalRing (X'.presheaf.stalk x' ⧸ (maximalIdeal _).map (f'.stalkMap x').hom) := by
    exact (formallySmooth_stalkMap_iff_of_isClosed sX sY f hf _ (hcl x') (hfcl x')).trans
      (and_congr (flat_stalkMap_iff hsq hX hY x') (isRegularLocalRing_fibre_iff hsq hX hY x'))
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  constructor
  · intro h x'
    refine (key x').mp ?_
    have : φX.base x' ∈ f.smoothLocus := h ▸ trivial
    exact this
  · intro h
    have hU := eq_univ_of_isOpen_of_closedPoints_subset f.smoothLocus.2 fun y hy ↦ by
      rw [← hrangeX] at hy
      obtain ⟨x', rfl⟩ := hy
      exact (key x').mpr (h x')
    exact SetLike.coe_injective (hU.trans TopologicalSpace.Opens.coe_top.symm)

end LocallyRingedSpaceComparison

namespace AffineAnalytification

open AnalyticGeometry LocallyRingedSpaceComparison

variable {A B : Type} [CommRing A] [Algebra ℂ A] [Algebra.FinitePresentation ℂ A] [CommRing B]
  [Algebra ℂ B] [Algebra.FinitePresentation ℂ B] (e : A →ₐ[ℂ] B)

/-- XII.3.1 (iv), affine case: a homomorphism `e : A → B` of finitely presented `ℂ`-algebras is
smooth iff `f^an : Spec(B)^an → Spec(A)^an` is, at every point `x`, flat with regular fibre
`𝒪_x/𝔪_{f^an(x)} 𝒪_x`. -/
theorem smooth_iff_forall :
    e.toRingHom.Smooth ↔ ∀ x, ((affineAnalytificationMap e).stalkMap x).hom.Flat ∧
      IsRegularLocalRing
        (_ ⧸ (maximalIdeal _).map ((affineAnalytificationMap e).stalkMap x).hom) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  rw [← CommRingCat.hom_ofHom e.toRingHom, ← HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_iff_forall_of_comparison _ _
    (spec_map_comp_structureMorphism e) (affineAnalytificationMap_comp_affineToSpec_toLRSHom e)
    (isComparison_affineToSpec ℂ B) (isComparison_affineToSpec ℂ A) (range_affineToSpec_base B)
    (range_affineToSpec_base A).subset

end AffineAnalytification

namespace AnalyticGluing

open LocallyRingedSpaceComparison

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

/-- XII.3.1 (iv): a morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type is smooth
iff `f^an : X^an → Y^an` is, at every point `x`, flat with regular fibre
`𝒪_{X^an,x}/𝔪_{f^an(x)} 𝒪_{X^an,x}` ("smooth" for analytic morphisms in the sense of flat with
regular fibres, see the module docstring). -/
theorem smooth_iff_forall_analyticMap :
    Smooth f ↔ ∀ x, ((analyticMap f).stalkMap x).hom.Flat ∧
      IsRegularLocalRing (_ ⧸ (maximalIdeal _).map ((analyticMap f).stalkMap x).hom) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  have := locallyOfFiniteType_of_isOver f
  exact smooth_iff_forall_of_comparison (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
    (CategoryTheory.comp_over f _) (analyticMap_toScheme f) isComparison_toScheme
    isComparison_toScheme range_toScheme_base range_toScheme_base.subset

end AnalyticGluing

end SGA.SGA1.ExposeXII
