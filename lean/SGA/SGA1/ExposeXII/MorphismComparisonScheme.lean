/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.MorphismComparison
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeIV.Schemes
import SGA.SGA1.ExposeI.Etale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# SGA 1, Exposé XII, 3.1 (i)–(iii): from closed points to the whole scheme

SGA's proof of XII.3.1 (i)–(iii): `f^an` is flat (resp. unramified) at `x` iff `f` is flat
(resp. unramified) at the closed point `φ(x)` (`MorphismComparison.lean`), and the flat (resp.
unramified) locus of `f` is open (EGA IV 11.1.1, resp. I 3.3), hence everything since `X` is a
Jacobson scheme.

We prove this for an arbitrary commutative square
```
X' --f'--> Y'
|φX        |φY
v          v
X  --f-->  Y
```
of locally ringed spaces in which `f` is a morphism of schemes locally of finite type over an
algebraically closed field `K`, `φX` and `φY` are comparison morphisms (`IsComparison`: the
properties of `X^an → X` proved in XII.2.1), and `φX` reaches exactly the closed points of `X`.
For `X^an` this is XII.1.1. This file therefore gives XII.3.1 (i)–(iii) for every construction
of `X^an` with these properties: the affine one (`AnalyticAffine.lean`), and the glued one.

* XII.3.1 (i): `flat_iff_forall_flat_stalkMap_of_comparison`;
* XII.3.1 (ii): `formallyUnramified_iff_forall_map_maximalIdeal_of_comparison` (the analytic
  side: `𝔪_{f'(x')} 𝒪_{x'} = 𝔪_{x'}` at every point, SGA's "net");
* XII.3.1 (iii): `etale_iff_forall_of_comparison`.

References: SGA 1 XII.3.1; EGA IV 11.1.1, 17.4.1; SGA 1 I.3.3.
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Topology

namespace SGA.SGA1.ExposeXII

namespace LocallyRingedSpaceComparison

/-- In a Jacobson space, an open set containing every closed point is everything. (The sibling
`IsLocallyConstructible.eq_univ_of_closedPoints_subset`, `JacobsonConstructible.lean`, does the
same for locally constructible sets of a scheme.) -/
lemma eq_univ_of_isOpen_of_closedPoints_subset {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    {U : Set T} (hU : IsOpen U) (h : closedPoints T ⊆ U) : U = Set.univ := by
  by_contra hne
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    hU.isClosed_compl.isLocallyClosed
  exact hyZ (h hy)

section ResidueField

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- For a morphism `f : X → Y` of schemes locally of finite type over an algebraically closed
field `K`, and a closed point `x` with `f(x)` closed, `κ(f(x)) → κ(x)` is bijective (both are
`K`). -/
lemma bijective_residueFieldMap_of_isClosed (f : X ⟶ Y) (hf : f ≫ sY = sX) (x : X)
    (hx : IsClosed {x}) (hfx : IsClosed {f x}) : Function.Bijective (f.residueFieldMap x).hom := by
  have key : (residueFieldIsoBase sY (f x) hfx).inv ≫ f.residueFieldMap x =
      (residueFieldIsoBase sX x hx).inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, SpecMap_residueFieldIsoBase_inv,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hf]
  refine ⟨(f.residueFieldMap x).hom.injective, fun z ↦ ?_⟩
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (residueFieldIsoBase sX x hx).inv).2 z
  exact ⟨(residueFieldIsoBase sY (f x) hfx).inv c, by rw [← key]; rfl⟩

end ResidueField

variable {X Y : Scheme.{u}} {X' Y' : LocallyRingedSpace.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {φX : X' ⟶ X.toLocallyRingedSpace} {φY : Y' ⟶ Y.toLocallyRingedSpace}

/-- XII.3.1 (i): let `f : X → Y` be a morphism locally of finite type of schemes, `Y` locally
noetherian and `X` Jacobson, and `f' : X' → Y'` a morphism of locally ringed spaces over `f`
through comparison morphisms `φX`, `φY`, with `φX` reaching every closed point of `X` (e.g.
`f^an : X^an → Y^an`). Then `f` is flat iff `f'` is flat at every point. -/
theorem flat_iff_forall_flat_stalkMap_of_comparison [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [JacobsonSpace X] (hsq : f' ≫ φY = φX ≫ f.toLRSHom) (hX : IsComparison φX)
    (hY : IsComparison φY) (hrange : closedPoints X ⊆ Set.range φX.base) :
    Flat f ↔ ∀ x', (f'.stalkMap x').hom.Flat := by
  constructor
  · intro _ x'
    exact (flat_stalkMap_iff hsq hX hY x').mp (Flat.stalkMap f (φX.base x'))
  · intro h
    refine Flat.of_stalkMap f fun x ↦ ?_
    have hU := eq_univ_of_isOpen_of_closedPoints_subset (ExposeIV.isOpen_setOf_flat_stalkMap f)
      fun y hy ↦ by
        obtain ⟨x', rfl⟩ := hrange hy
        exact (flat_stalkMap_iff hsq hX hY x').mpr (h x')
    have : x ∈ {x : X | (f.stalkMap x).hom.Flat} := hU ▸ Set.mem_univ x
    exact this

variable {K : Type u} [Field K] [IsAlgClosed K] (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- At a closed point `x` with `f(x)` closed, `f` is formally unramified iff
`𝔪_{f(x)} 𝒪_x = 𝔪_x` (the residue field extension is trivial). -/
lemma formallyUnramified_stalkMap_iff_of_isClosed [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    (x : X) (hx : IsClosed {x}) (hfx : IsClosed {f x}) :
    (f.stalkMap x).hom.FormallyUnramified ↔
      (maximalIdeal _).map (f.stalkMap x).hom = maximalIdeal _ := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hbij := bijective_residueFieldMap_of_isClosed sX sY f hf x hx hfx
  have hsep : Algebra.IsSeparable (ResidueField (Y.presheaf.stalk (f x)))
      (ResidueField (X.presheaf.stalk x)) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨c, hc⟩ := hbij.2 z
    rw [← hc]
    exact isSeparable_algebraMap (F := ResidueField (Y.presheaf.stalk (f x)))
      (K := ResidueField (X.presheaf.stalk x)) c
  rw [show (f.stalkMap x).hom = algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) from rfl,
    RingHom.formallyUnramified_algebraMap, Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsep, h⟩⟩

/-- XII.3.1 (ii): in the situation of `flat_iff_forall_flat_stalkMap_of_comparison`, for `X`, `Y`
locally of finite type over an algebraically closed field and `φX`, `φY` landing in the closed
points, `f` is (formally) unramified iff `f'` is unramified at every point in the sense
`𝔪_{f'(x')} 𝒪_{x'} = 𝔪_{x'}` (SGA's "net" for analytic spaces, whose residue fields are `K`). -/
theorem formallyUnramified_iff_forall_map_maximalIdeal_of_comparison [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (hsq : f' ≫ φY = φX ≫ f.toLRSHom) (hX : IsComparison φX)
    (hY : IsComparison φY) (hrangeX : Set.range φX.base = closedPoints X)
    (hrangeY : Set.range φY.base ⊆ closedPoints Y) :
    FormallyUnramified f ↔ ∀ x', (maximalIdeal _).map (f'.stalkMap x').hom = maximalIdeal _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hcl (x' : X') : IsClosed {φX.base x'} := by
    have : φX.base x' ∈ closedPoints X := hrangeX ▸ Set.mem_range_self x'
    exact this
  have hfcl (x' : X') : IsClosed {f (φX.base x')} := by
    have : f (φX.base x') = φY.base (f'.base x') := base_apply_eq f.toLRSHom f' φX φY hsq x'
    rw [this]
    exact hrangeY ⟨_, rfl⟩
  have key (x' : X') : (f.stalkMap (φX.base x')).hom.FormallyUnramified ↔
      (maximalIdeal _).map (f'.stalkMap x').hom = maximalIdeal _ :=
    (formallyUnramified_stalkMap_iff_of_isClosed sX sY hf _ (hcl x') (hfcl x')).trans
      (map_maximalIdeal_stalkMap_eq_iff hsq hX hY x')
  constructor
  · intro _ x'
    exact (key x').mp (FormallyUnramified.stalkMap f _)
  · intro h
    refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
      fun x ↦ ?_
    have hU := eq_univ_of_isOpen_of_closedPoints_subset
      (ExposeI.isOpen_setOf_formallyUnramified_stalkMap f) fun y hy ↦ by
        rw [← hrangeX] at hy
        obtain ⟨x', rfl⟩ := hy
        exact (key x').mpr (h x')
    have : x ∈ {x : X | (f.stalkMap x).hom.FormallyUnramified} := hU ▸ Set.mem_univ x
    exact this

/-- XII.3.1 (iii): in the situation of
`formallyUnramified_iff_forall_map_maximalIdeal_of_comparison`, `f` is étale iff `f'` is flat and
unramified at every point. (For analytic spaces, "étale" in the sense of a local isomorphism is
not shown to be equivalent to this; see `AnalyticGluing.etale_iff_forall_analyticMap`.) -/
theorem etale_iff_forall_of_comparison [IsLocallyNoetherian Y] [LocallyOfFinitePresentation f]
    (hf : f ≫ sY = sX) (hsq : f' ≫ φY = φX ≫ f.toLRSHom) (hX : IsComparison φX)
    (hY : IsComparison φY) (hrangeX : Set.range φX.base = closedPoints X)
    (hrangeY : Set.range φY.base ⊆ closedPoints Y) :
    Etale f ↔ ∀ x', (f'.stalkMap x').hom.Flat ∧
      (maximalIdeal _).map (f'.stalkMap x').hom = maximalIdeal _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  rw [Etale.iff_flat_and_formallyUnramified,
    flat_iff_forall_flat_stalkMap_of_comparison hsq hX hY hrangeX.symm.subset,
    formallyUnramified_iff_forall_map_maximalIdeal_of_comparison sX sY hf hsq hX hY hrangeX
      hrangeY]
  exact ⟨fun ⟨h₁, h₂, _⟩ x' ↦ ⟨h₁ x', h₂ x'⟩,
    fun h ↦ ⟨fun x' ↦ (h x').1, fun x' ↦ (h x').2, inferInstance⟩⟩

end LocallyRingedSpaceComparison

/-! ### The affine case -/

namespace AffineAnalytification

open AnalyticGeometry LocallyRingedSpaceComparison

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (A : Type) [CommRing A]
  [Algebra 𝕜 A] [Algebra.FinitePresentation 𝕜 A]

/-- XII.1.1: `φ : X^an → X` sends the point of `X^an` attached to `x ∈ X(𝕜)` to the closed point
`ker x` of `X = Spec A`. -/
theorem affineToSpec_base_affinePointsHomeomorph (x : Points 𝕜 A) :
    (affineToSpec 𝕜 A).base (affinePointsHomeomorph 𝕜 A x) = Points.toPrimeSpectrum x := by
  refine PrimeSpectrum.ext (Ideal.ext fun a ↦ ?_)
  change a ∈ (((toSpec (presentationPolys 𝕜 A)).base _).asIdeal).comap
    (presentationEquiv 𝕜 A).symm.toRingHom ↔ _
  rw [Ideal.mem_comap, toSpec_base_asIdeal, affinePointsHomeomorph, Homeomorph.trans_apply,
    evalPoint_pointsHomeomorph, RingHom.mem_ker, Points.toPrimeSpectrum_asIdeal, Points.mem_ker]
  change x ((presentationEquiv 𝕜 A) ((presentationEquiv 𝕜 A).symm a)) = 0 ↔ _
  rw [AlgEquiv.apply_symm_apply]

/-- XII.1.1: the image of `φ : X^an → X` is the set of closed points of `X = Spec A`
(`A` of finite type over `ℂ`). -/
theorem range_affineToSpec_base (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FinitePresentation ℂ A] :
    Set.range (affineToSpec ℂ A).base = closedPoints (PrimeSpectrum A) := by
  rw [← Points.range_toPrimeSpectrum (K := ℂ)]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (affinePointsHomeomorph ℂ A).surjective y
    exact ⟨x, (affineToSpec_base_affinePointsHomeomorph ℂ A x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, affineToSpec_base_affinePointsHomeomorph ℂ A x⟩

end AffineAnalytification

namespace AffineAnalytification

open AnalyticGeometry LocallyRingedSpaceComparison

variable {A B : Type} [CommRing A] [Algebra ℂ A] [Algebra.FinitePresentation ℂ A] [CommRing B]
  [Algebra ℂ B] [Algebra.FinitePresentation ℂ B] (e : A →ₐ[ℂ] B)

/-- `affineAnalytificationMap_comp_affineToSpec`, with `Spec.locallyRingedSpaceMap` written as
`(Spec.map _).toLRSHom`, the form the comparison theorems for schemes take. -/
lemma affineAnalytificationMap_comp_affineToSpec_toLRSHom :
    affineAnalytificationMap e ≫ affineToSpec ℂ A =
      affineToSpec ℂ B ≫ (Spec.map (CommRingCat.ofHom e.toRingHom)).toLRSHom :=
  affineAnalytificationMap_comp_affineToSpec e

/-- The structure morphism `Spec A → Spec ℂ`. -/
abbrev structureMorphism (A : Type) [CommRing A] [Algebra ℂ A] :
    Spec (.of A) ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

instance (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FinitePresentation ℂ A] :
    LocallyOfFiniteType (structureMorphism A) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  algebraize [e.toRingHom]
  have : IsScalarTower ℂ A B := .of_algebraMap_eq fun c ↦ (e.commutes c).symm
  exact RingHom.finiteType_algebraMap.mpr (Algebra.FiniteType.of_restrictScalars_finiteType ℂ A B)

instance : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  algebraize [e.toRingHom]
  have : IsScalarTower ℂ A B := .of_algebraMap_eq fun c ↦ (e.commutes c).symm
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ A B
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  exact RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

omit [Algebra.FinitePresentation ℂ A] [Algebra.FinitePresentation ℂ B] in
lemma spec_map_comp_structureMorphism :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ structureMorphism A = structureMorphism B := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact e.commutes c

/-- XII.3.1 (i), affine case: a homomorphism `e : A → B` of finitely presented `ℂ`-algebras is
flat iff `f^an : Spec(B)^an → Spec(A)^an` is flat at every point. -/
theorem flat_iff_forall_flat_stalkMap :
    e.toRingHom.Flat ↔ ∀ x, ((affineAnalytificationMap e).stalkMap x).hom.Flat := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := ℂ)
  rw [← CommRingCat.hom_ofHom e.toRingHom, ← Flat.SpecMap_iff]
  exact flat_iff_forall_flat_stalkMap_of_comparison
    (affineAnalytificationMap_comp_affineToSpec_toLRSHom e)
    (isComparison_affineToSpec ℂ B) (isComparison_affineToSpec ℂ A)
    (range_affineToSpec_base B).symm.subset

/-- XII.3.1 (ii), affine case: a homomorphism `e : A → B` of finitely presented `ℂ`-algebras is
(formally) unramified iff `f^an` is unramified at every point `x`: `𝔪_{f^an(x)} 𝒪_x = 𝔪_x`. -/
theorem formallyUnramified_iff_forall_map_maximalIdeal :
    e.toRingHom.FormallyUnramified ↔ ∀ x, (maximalIdeal _).map
      ((affineAnalytificationMap e).stalkMap x).hom = maximalIdeal _ := by
  rw [← CommRingCat.hom_ofHom e.toRingHom,
    ← HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  exact formallyUnramified_iff_forall_map_maximalIdeal_of_comparison _ _
    (spec_map_comp_structureMorphism e) (affineAnalytificationMap_comp_affineToSpec_toLRSHom e)
    (isComparison_affineToSpec ℂ B) (isComparison_affineToSpec ℂ A) (range_affineToSpec_base B)
    (range_affineToSpec_base A).subset

/-- XII.3.1 (iii), affine case: a homomorphism `e : A → B` of finitely presented `ℂ`-algebras is
étale iff `f^an` is flat and unramified at every point (not shown to be equivalent to `f^an`
being a local isomorphism). -/
theorem etale_iff_forall :
    e.toRingHom.Etale ↔ ∀ x, ((affineAnalytificationMap e).stalkMap x).hom.Flat ∧
      (maximalIdeal _).map ((affineAnalytificationMap e).stalkMap x).hom = maximalIdeal _ := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  rw [← CommRingCat.hom_ofHom e.toRingHom, ← HasRingHomProperty.Spec_iff (P := @Etale)]
  exact etale_iff_forall_of_comparison _ _
    (spec_map_comp_structureMorphism e) (affineAnalytificationMap_comp_affineToSpec_toLRSHom e)
    (isComparison_affineToSpec ℂ B) (isComparison_affineToSpec ℂ A) (range_affineToSpec_base B)
    (range_affineToSpec_base A).subset

end AffineAnalytification

end SGA.SGA1.ExposeXII
