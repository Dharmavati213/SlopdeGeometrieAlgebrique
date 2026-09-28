/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.SGA1.ExposeIX.ConnectedFibres
import SGA.SGA1.ExposeIX.ExactSequence
import SGA.SGA1.ExposeX.EtaleCoverings
import SGA.SGA1.ExposeX.GaloisFunctors
import SGA.SGA1.ExposeX.Specialization

/-!
# SGA 1, Exposé X, §1: the homotopy exact sequence of a proper separable morphism

SGA proves X.1.3 (an étale covering of `X` whose geometric fibre over `y` has a section comes
from `Y`) from X.1.2 (the Stein factorization of a proper separable morphism is étale, EGA III
7.8.10), and deduces X.1.4, X.1.7, X.1.8, X.1.9 from it. This file contains the statements and
the formal parts; the statements are proved elsewhere: X.1.2 and X.1.3 in `SteinEtale` (through
`CoveringOfBase`), X.1.7 in `Product` and `SteinEtale`, X.1.8 in `BaseChangeAlgClosed`, X.1.9 in
`ConstantFamily`. Precisely:

* the statements X.1.2 (`SteinFactorizationEtaleStatement`, reduced to the étaleness of the
  relative normalization in `steinFactorizationEtaleStatement_of_etale_fromNormalization`),
  X.1.3 (`CoveringOfBaseStatement`; derived from X.1.2 in `CoveringOfBase`), X.1.8;
* X.1.4 from X.1.3: `ker_le_range_of_coveringOfBaseStatement` (any fibre functors),
  `range_map_eq_ker_map_of_coveringOfBaseStatement` and, with surjectivity (IX.3.4),
  `homotopyExactSequence_of_coveringOfBaseStatement` for the fundamental groups of Exposé V at
  a geometric point of `X̄_y`; the Galois-category form is `surjective_and_range_eq_ker`,
  `range_eq_ker_iff` (in `GaloisFunctors`);
* X.1.4, triviality of `π₁(X̄_y) → π₁(X) → π₁(Y)`: every étale covering of the spectrum of a
  separably closed field is completely decomposed (`FEt.isCompletelyDecomposed_of_isSepClosed`),
  so the composite, which factors through `π₁(Spec Ω) = 1`, is trivial
  (`map_comp_map_geometricFibre_eq_one`);
* X.1.7 from X.1.4 for abstract Galois categories, `bijective_autWhiskerLeft_prod` (the scheme
  version is in `Product`);
* X.1.8 gives the isomorphism `π₁(X ⊗ₖ k') ≅ π₁(X)` by V.6.10
  (`bijective_map_of_baseChangeAlgClosed`); its surjectivity half is proved in `ProperOverField`.

The counterexamples X.1.10 are in `ArtinSchreier`.
-/

universe u u₁ u₂ v₁ v₂ t₁ t₂ w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.PreGaloisCategory

namespace SGA.SGA1.ExposeX

/-- X.1.2 (statement only; EGA III 7.8.10 (i)): the Stein factorization `X → Y' → Y` of a proper
separable morphism, with `Y'` finite over `Y` and `g_* 𝒪_X = 𝒪_{Y'}`, has `Y'` étale over `Y`.
The factorization is characterized by these properties, so we state: such a factorization with
`Y'` an étale covering exists. -/
def SteinFactorizationEtaleStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y],
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y) (g : X ⟶ Y'), IsFinite π ∧ Etale π ∧ g ≫ π = f ∧
      ∀ U : Y'.Opens, IsIso (g.app U)

/-- X.1.2 reduces to the étaleness of the relative normalization `Y' = Spec_Y f_* 𝒪_X` of `Y` in
`X`, which is the Stein factorization (EGA III 4.3.3,
`AlgebraicGeometry.steinFactorizationStatement`): what is missing is EGA III 7.8.10 (i), i.e.
that `Y' ⟶ Y` is étale when `f` is proper and separable. -/
theorem steinFactorizationEtaleStatement_of_etale_fromNormalization
    (h : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y],
      Etale f.fromNormalization) :
    SteinFactorizationEtaleStatement.{u} := fun _ _ f _ _ _ ↦
  ⟨f.normalization, f.fromNormalization, f.toNormalization,
    CohomologyAux.isFinite_fromNormalization f, h f, f.toNormalization_fromNormalization,
    CohomologyAux.isIso_toNormalization_app f⟩

/-- X.1.3 (statement only). Let `f : X ⟶ Y` be proper and separable, `Y` locally noetherian and
connected, with `f_* 𝒪_X = 𝒪_Y`, and let `y ∈ Y`. A connected étale covering `X'` of `X` is
isomorphic over `X` to `X ×_Y Y'` for an étale covering `Y'` of `Y` iff the geometric fibre
`X̄'_y → X̄_y` (over an algebraic closure of `κ(y)`) admits a section. -/
def CoveringOfBaseStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y], (∀ U : Y.Opens, IsIso (f.app U)) → ∀ (y : Y)
    ⦃X' : Scheme.{u}⦄ (p : X' ⟶ X) [IsFinite p] [Etale p] [ConnectedSpace X'],
    (∃ (Y' : Scheme.{u}) (q : Y' ⟶ Y) (_ : IsFinite q) (_ : Etale q) (φ : X' ≅ pullback q f),
        φ.hom ≫ pullback.snd q f = p) ↔
      ∃ s : pullback f (geometricPoint Y y) ⟶ pullback p (pullback.fst f (geometricPoint Y y)),
        s ≫ pullback.snd _ _ = 𝟙 _

/-- X.1.4 from X.1.3, exactness at `π₁(X)` (via V.6.11). Let `f : X ⟶ Y` be as in X.1.3 and
`X̄_y` the geometric fibre at `y`. For fibre functors on the Galois categories of étale coverings
of `Y`, `X` and `X̄_y` compatible with the inverse-image functors (Exposé V), X.1.3 implies that
the kernel of `π₁(X) → π₁(Y)` is contained in the image of `π₁(X̄_y) → π₁(X)`. The composite
`π₁(X̄_y) → π₁(Y)` is trivial and `π₁(X) → π₁(Y)` is surjective by IX.3.4 (see
`surjective_and_range_eq_ker` for the full sequence). The categories of étale coverings are
Galois categories by V.7 (they have fibre functors). -/
theorem ker_le_range_of_coveringOfBaseStatement (h : CoveringOfBaseStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    {FY : FEt Y ⥤ FintypeCat.{u}} {FX : FEt X ⥤ FintypeCat.{u}}
    {FXbar : FEt (pullback f (geometricPoint Y y)) ⥤ FintypeCat.{u}}
    [FiberFunctor FY] [FiberFunctor FX] [FiberFunctor FXbar]
    (e : FEt.pullback f ⋙ FX ≅ FY)
    (e' : FEt.pullback (pullback.fst f (geometricPoint Y y)) ⋙ FXbar ≅ FX) :
    (autWhiskerLeft _ e).ker ≤ (autWhiskerLeft _ e').range := by
  have := ExposeV.galoisCategory_of_fiberFunctor FY
  have := ExposeV.galoisCategory_of_fiberFunctor FX
  have := ExposeV.galoisCategory_of_fiberFunctor FXbar
  refine ker_autWhiskerLeft_le_range_autWhiskerLeft _ e' fun Z hZ ⟨t⟩ ↦ ?_
  have : ConnectedSpace ((𝟭 Scheme.{u}).obj Z.left) := FEt.connectedSpace_of_isConnected Z
  obtain ⟨s, hs⟩ := FEt.exists_section_of_hom t
  obtain ⟨Y', q, hq, hqe, φ, hφ⟩ := (h f hf y Z.hom).mpr ⟨s, hs⟩
  let W : FEt Y := MorphismProperty.Over.mk ⊤ q ⟨hq, hqe⟩
  let ψ : Z ≅ (FEt.pullback f).obj W := MorphismProperty.Over.isoMk φ hφ
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected FX Z
  exact ⟨W, _, 𝟙 _, inferInstance, ψ.inv, ⟨FX.map ψ.hom z⟩⟩

/-- X.1.4 (geometric input): every étale covering of the spectrum of a separably closed field is
completely decomposed (a finite sum of copies of the final object). -/
theorem FEt.isCompletelyDecomposed_of_isSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (Z : FEt (Spec (.of Ω))) : IsCompletelyDecomposed Z :=
  ExposeV.FEt.exists_iso_sigma_terminal Ω Z

/-- X.1.4, first assertion: for `f : X ⟶ Y`, `y ∈ Y` and a geometric point `a` of the geometric
fibre `X̄_y`, the composite `π₁(X̄_y, a) → π₁(X, a) → π₁(Y, a)` is trivial: `X̄_y → Y` factors
through the geometric point `Spec κ(y)ᵃˡᵍ → Y`, and `π₁(Spec κ(y)ᵃˡᵍ) = 1`. No hypothesis on `f`
is needed. -/
theorem map_comp_map_geometricFibre_eq_one {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).comp
      (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a) = 1 :=
  ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω _ f (pullback.snd _ _)
    (geometricPoint Y y) pullback.condition a
    (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω _ _)

/-- X.1.4 from X.1.3, exactness at `π₁(X)`, for the fundamental groups of Exposé V at a geometric
point `a` of the geometric fibre `X̄_y`: X.1.3 implies
`Ker (π₁(X, a) → π₁(Y, a)) ⊆ Im (π₁(X̄_y, a) → π₁(X, a))`. The Galois structures of Exposé V are
used for `X` and `X̄_y`, which are connected by IX.5.6 and EGA III 4.3.4. -/
theorem ker_map_le_range_map_of_coveringOfBaseStatement (h : CoveringOfBaseStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).ker ≤
      (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a).range := by
  have : GeometricallyConnected f := CohomologyAux.geometricallyConnected_of_isIso_app f hf
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : ConnectedSpace ↥(pullback f (geometricPoint Y y)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (geometricPoint Y y) _ _
      (IsPullback.of_hasPullback f (geometricPoint Y y))
  exact ker_le_range_of_coveringOfBaseStatement h f hf y (ExposeV.FEt.pullbackFiberIso Ω f _)
    (ExposeV.FEt.pullbackFiberIso Ω _ a)

/-- X.1.4 from X.1.3, exactness at `π₁(X)`:
`Im (π₁(X̄_y, a) → π₁(X, a)) = Ker (π₁(X, a) → π₁(Y, a))` for the fundamental groups of
Exposé V. -/
theorem range_map_eq_ker_map_of_coveringOfBaseStatement (h : CoveringOfBaseStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a).range =
      (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).ker := by
  refine le_antisymm ?_ (ker_map_le_range_map_of_coveringOfBaseStatement h f hf y Ω a)
  rintro _ ⟨σ, rfl⟩
  rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, map_comp_map_geometricFibre_eq_one f y Ω a]
  rfl

/-- X.1.4, the homotopy exact sequence `π₁(X̄_y, a) → π₁(X, a) → π₁(Y, a) → e`, from X.1.3.
Let `f : X ⟶ Y` be proper and separable with `f_* 𝒪_X = 𝒪_Y`, `Y` locally noetherian and
connected, `y ∈ Y` and `a` a geometric point of the geometric fibre `X̄_y`. Then the image of
`π₁(X̄_y, a) → π₁(X, a)` is the kernel of `π₁(X, a) → π₁(Y, a)` (X.1.3, via V.6.11), and
`π₁(X, a) → π₁(Y, a)` is surjective (IX.3.4 with V.6.9: `f` is proper and surjective, with
geometrically connected fibres by EGA III 4.3.4). `X` and `X̄_y` are connected by IX.5.6 and
EGA III 4.3.4. -/
theorem homotopyExactSequence_of_coveringOfBaseStatement (h : CoveringOfBaseStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a).range =
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).ker ∧
      Function.Surjective
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))) := by
  have : GeometricallyConnected f := CohomologyAux.geometricallyConnected_of_isIso_app f hf
  exact ⟨range_map_eq_ker_map_of_coveringOfBaseStatement h f hf y Ω a,
    ExposeIX.surjective_etaleFundamentalGroup_map_of_isProper f Ω _⟩

/-- X.1.8 (statement only). If `X` is proper and connected over an algebraically closed field `k`
and `k'` is an algebraically closed extension of `k`, then `π₁(X ⊗ₖ k') → π₁(X)` is an
isomorphism; by V.6.10 this is the assertion that the inverse-image functor on étale coverings
`X' ↦ X' ⊗ₖ k'` is an equivalence. -/
def BaseChangeAlgClosedStatement : Prop :=
  ∀ (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X],
    (FEt.pullback (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence

/-- X.1.8, from the statement on coverings via V.6.10: for every geometric point `t` of
`X ⊗ₖ k'`, `π₁(X ⊗ₖ k', t) → π₁(X, t)` is bijective. -/
theorem bijective_map_of_baseChangeAlgClosed (h : BaseChangeAlgClosedStatement.{u})
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X] (Ω : Type u)
    [Field Ω] (t : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k')))) t) :=
  have := h k k' s
  ExposeV.autMap_bijective _ _

section ProductFormula

variable {CX : Type u₁} [Category.{u₂} CX] {CY : Type v₁} [Category.{v₂} CY]
  {CZ : Type t₁} [Category.{t₂} CZ]
  {FX : CX ⥤ FintypeCat.{w}} {FY : CY ⥤ FintypeCat.{w}} {FZ : CZ ⥤ FintypeCat.{w}}

/-- X.1.7 (formal part). Let `Z = X ×ₖ Y` with projections `pr₁`, `pr₂`, and let `j : X → Z` be
the fibre of `pr₂` at a rational point, so that `pr₁ ∘ j = id`. Write `P₁`, `P₂`, `J` for the
inverse-image functors on étale coverings (or on any categories with fibre functors), compatible
with the fibre functors through `e₁`, `e₂`, `eJ`, and `ρ : P₁ ⋙ J ≅ 𝟭` for `pr₁ ∘ j = id`
(compatibly with the fibre functors). If the homotopy sequence `π₁(X) → π₁(Z) → π₁(Y) → e` of
`pr₂` is exact (X.1.4), then `π₁(Z) → π₁(X) × π₁(Y)` is an isomorphism. -/
theorem bijective_autWhiskerLeft_prod (P₁ : CX ⥤ CZ) (P₂ : CY ⥤ CZ) (J : CZ ⥤ CX)
    (e₁ : P₁ ⋙ FZ ≅ FX) (e₂ : P₂ ⋙ FZ ≅ FY) (eJ : J ⋙ FX ≅ FZ) (ρ : P₁ ⋙ J ≅ 𝟭 CX)
    (hρ : Functor.associator P₁ J FX ≪≫ Functor.isoWhiskerLeft P₁ eJ ≪≫ e₁ =
      Functor.isoWhiskerRight ρ FX ≪≫ Functor.leftUnitor FX)
    (hsurj : Function.Surjective (autWhiskerLeft P₂ e₂))
    (hex : (autWhiskerLeft J eJ).range = (autWhiskerLeft P₂ e₂).ker) :
    Function.Bijective ((autWhiskerLeft P₁ e₁).prod (autWhiskerLeft P₂ e₂)) := by
  refine bijective_prod_of_retraction (autWhiskerLeft J eJ) _ _ ?_ hex hsurj
  rw [← autWhiskerLeft_comp, hρ, autWhiskerLeft_congr, autWhiskerLeft_id]

end ProductFormula

end SGA.SGA1.ExposeX
