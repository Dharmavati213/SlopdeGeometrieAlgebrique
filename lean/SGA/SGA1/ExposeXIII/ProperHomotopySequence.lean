/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeX.SteinEtale
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeXIII.NormalCrossings
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup

/-!
# SGA 1, Exposé XIII, 4.4–4.6: the homotopy exact sequence for proper separable morphisms

XIII.4.4 (first part) says that the hypotheses of XIII.4.1 hold for `f : X ⟶ S` proper, flat, of
finite presentation, with separable connected geometric fibres, `S` connected, and every set `L`
of primes; so `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact. We deduce this from the homotopy exact
sequence X.1.4 and the group theory of `SGA.SGA1.ExposeXIII.ProLQuotient`, for `S` locally
noetherian (the hypothesis of X.1.4) and at every geometric point `s̄ : Spec Ω₀ ⟶ S`, `Ω₀`
algebraically closed. X.1.4 assumes `f_* 𝒪_X = 𝒪_S` instead of geometrically connected fibres; we
prove that the latter implies the former for `f` proper, flat with geometrically reduced fibres
over a connected locally noetherian base (`isIso_app_of_geometricallyConnected`, EGA III 7.8.6),
using the étale Stein factorization X.1.2 and the Galois theory of Exposé V. X.1.3 is stated at
the geometric point `ȳ : Spec κ(y)ᵃˡᵍ ⟶ S`; an arbitrary `s̄` factors through the `ȳ` at its image
(`exists_eq_comp_geometricPoint`), `X_s̄ = X_ȳ ⊗ Ω₀`, and by X.1.8 an étale covering of `X` has a
section over `X_s̄` iff it has one over `X_ȳ` (`nonempty_section_geometricPoint_of_isAlgClosed`);
the exactness at `π₁(X)` then follows from the criterion V.6.11 (`ker_autHom_le_range_iff`).

We also deduce the semidirect product decomposition XIII.4.5 from a section (without the
injectivity of `π₁^L(X_s̄) → π'₁(X)`, which is XIII.4.3), and the Künneth formula XIII.4.6 for
maximal pro-`L` quotients when `X` is proper, from X.1.7. The second part of XIII.4.4 (smooth with
a section: injectivity, via XIII.4.3) and its third part (complement of a divisor with normal
crossings, via XIII.2.9) need the local constancy of `R¹f_*` and the cohomological properness of
tame coverings, and are recorded as statements.
-/

universe u

namespace SGA.SGA1.ExposeXIII

open AlgebraicGeometry CategoryTheory Limits PreGaloisCategory

section Stein

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- EGA III 7.8.6 (i) (for a connected locally noetherian base): if `f : X ⟶ S` is proper and flat
with geometrically reduced and geometrically connected fibres, then `f_* 𝒪_X = 𝒪_S`. The finite
part `S' ⟶ S` of the Stein factorization is étale (X.1.2), and `S'` is connected with a point of
its fibre fixed by `π₁(S)` (coming from the section `X → X ×_S S'`), since `π₁(X) → π₁(S)` is
onto; so `S' ⟶ S` is an isomorphism. -/
theorem isIso_app_of_geometricallyConnected [IsProper f] [Flat f] [GeometricallyReduced f]
    [GeometricallyConnected f] [IsLocallyNoetherian S] [ConnectedSpace S] (U : S.Opens) :
    IsIso (f.app U) := by
  -- the Stein factorization `X ⟶ S' ⟶ S`
  set g := f.toNormalization
  set h := f.fromNormalization
  have hgh : g ≫ h = f := f.toNormalization_fromNormalization
  have : IsFinite h := CohomologyAux.isFinite_fromNormalization f
  have : Etale h := etale_fromNormalization f
  have hg : ∀ V, IsIso (g.app V) := CohomologyAux.isIso_toNormalization_app f
  have : IsProper g := by
    have : IsProper (g ≫ h) := by rw [hgh]; infer_instance
    exact IsProper.of_comp g h
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian h
  have : GeometricallyConnected g := CohomologyAux.geometricallyConnected_of_isIso_app g hg
  have : ExposeIX.Submersive f := inferInstance
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_submersive f
  have : ConnectedSpace f.normalization := g.surjective.connectedSpace g.continuous
  suffices hh : IsIso h by
    have h₁ : IsIso (h.app U) := inferInstance
    have h₂ : IsIso (g.app (h ⁻¹ᵁ U)) := hg (h ⁻¹ᵁ U)
    have : IsIso ((g ≫ h).app U) := by
      rw [Scheme.Hom.comp_app]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
    rwa [hgh] at this
  -- a geometric point of `X` and the fibre functors
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Spec (.of K) ⟶ X := ExposeX.geometricPoint X x₀
  let S' : ExposeV.FEt S := MorphismProperty.Over.mk ⊤ h ⟨inferInstance, inferInstance⟩
  let F := ExposeV.FEt.fiber K (x ≫ f)
  let F' := ExposeV.FEt.fiber K x
  let H := ExposeV.FEt.pullback f
  let v : H ⋙ F' ≅ F := ExposeV.FEt.pullbackFiberIso K f x
  -- the section `X ⟶ X ×_S S'` gives a point of `F'(X ×_S S')` fixed by `π₁(X)`
  let σ : X ⟶ pullback h f := pullback.lift g (𝟙 X) (by rw [hgh, Category.id_comp])
  let T : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  have hT : IsTerminal T :=
    @ExposeV.FEt.isTerminalOfIsIso _ T (inferInstanceAs (IsIso (𝟙 X)))
  let φ : T ⟶ H.obj S' := MorphismProperty.Over.homMk σ (pullback.lift_snd _ _ _) trivial
  have : Subsingleton (F'.obj T) := subsingleton_fiber_of_isTerminal F' hT
  obtain ⟨t⟩ : Nonempty (F'.obj T) := (not_initial_iff_fiber_nonempty F' T).mp
    ((ExposeV.FEt.nonempty_left_iff_not_isInitial T).mp ⟨x₀⟩)
  have hfix : ∀ τ : Aut F', τ • F'.map φ t = F'.map φ t := fun τ ↦ by
    rw [mulAction_naturality, Subsingleton.elim (τ • t) t]
  -- its image in `F(S')` is fixed by `π₁(S)`, which acts transitively
  let s₀ := fiberEquiv H v S' (F'.map φ t)
  have hsurj : Function.Surjective (autHom H v) :=
    ExposeIX.surjective_etaleFundamentalGroup_map_of_isProper f K x
  have hfix' : ∀ τ : Aut F, τ • s₀ = s₀ := fun τ ↦ by
    obtain ⟨τ', rfl⟩ := hsurj τ
    rw [← fiberEquiv_smul, hfix]
  have : ConnectedSpace S'.left := inferInstanceAs (ConnectedSpace f.normalization)
  have : IsConnected S' := ExposeV.FEt.isConnected_of_connectedSpace S'
  have : Subsingleton (F.obj S') := ⟨fun y₁ y₂ ↦ by
    obtain ⟨τ₁, rfl⟩ := MulAction.exists_smul_eq (Aut F) s₀ y₁
    obtain ⟨τ₂, rfl⟩ := MulAction.exists_smul_eq (Aut F) s₀ y₂
    rw [hfix', hfix']⟩
  have : Nonempty (F.obj S') := ⟨s₀⟩
  obtain ⟨hS'⟩ := isTerminal_of_subsingleton_fiber F (Z := S')
  -- so `S' ⟶ S` is an isomorphism
  let TS : ExposeV.FEt S := MorphismProperty.Over.mk ⊤ (𝟙 S) ⟨inferInstance, inferInstance⟩
  let e : S' ≅ TS := hS'.uniqueUpToIso
    (@ExposeV.FEt.isTerminalOfIsIso _ TS (inferInstanceAs (IsIso (𝟙 S))))
  have he : e.hom.left ≫ 𝟙 S = h := MorphismProperty.Over.w e.hom
  have hiso : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).mapIso e).isIso_hom
  have he' : h = e.hom.left := he.symm.trans (Category.comp_id _)
  rw [he']
  exact hiso

end Stein

section HomotopySequence

/-- A geometric point `s̄ : Spec Ω₀ ⟶ S` (`Ω₀` algebraically closed) factors through the geometric
point `ȳ : Spec κ(y)ᵃˡᵍ ⟶ S` of X.1.3 at its image `y`, via an embedding `κ(y)ᵃˡᵍ → Ω₀` over
`κ(y)`. -/
theorem exists_eq_comp_geometricPoint {S : Scheme.{u}} (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ S) :
    ∃ (y : S) (_ : Algebra (AlgebraicClosure (S.residueField y)) Ω₀),
      s = Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (S.residueField y)) Ω₀)) ≫
        ExposeX.geometricPoint S y := by
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω₀ S).symm.surjective s
  let : Algebra (S.residueField y) Ω₀ := φ.hom.toAlgebra
  let ι : AlgebraicClosure (S.residueField y) →ₐ[S.residueField y] Ω₀ := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure (S.residueField y)) Ω₀ := ι.toRingHom.toAlgebra
  refine ⟨y, this, ?_⟩
  rw [Scheme.SpecToEquivOfField_symm_apply, ExposeX.geometricPoint, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext x
  exact (ι.commutes x).symm

/-- The hypothesis of X.1.3 does not depend on the geometric point (the step "cf. X 1.3" of
XIII.4.4 at an arbitrary geometric point). Let `f : X ⟶ S` be proper with geometrically connected
fibres, `ȳ : Spec κ(y)ᵃˡᵍ ⟶ S` the geometric point at `y` and `s̄ : Spec Ω₀ ⟶ Spec κ(y)ᵃˡᵍ ⟶ S`
with `Ω₀` algebraically closed. If an étale covering `Z` of `X` has a section over `X_s̄`, it has
one over `X_ȳ`: `X_s̄ = X_ȳ ⊗ Ω₀`, and base change of étale coverings along `X_ȳ ⊗ Ω₀ ⟶ X_ȳ` is an
equivalence (X.1.8, `SGA.SGA1.ExposeX.baseChangeAlgClosedStatement`). -/
theorem nonempty_section_geometricPoint_of_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (y : S) (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    [Algebra (AlgebraicClosure (S.residueField y)) Ω₀] (s : Spec (.of Ω₀) ⟶ S)
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (S.residueField y)) Ω₀)) ≫
      ExposeX.geometricPoint S y) (Z : ExposeV.FEt X)
    (h : Nonempty (⊤_ _ ⟶ (ExposeV.FEt.pullback (pullback.fst f s)).obj Z)) :
    Nonempty (⊤_ _ ⟶
      (ExposeV.FEt.pullback (pullback.fst f (ExposeX.geometricPoint S y))).obj Z) := by
  subst hs
  set yb := ExposeX.geometricPoint S y
  set j : Spec (.of Ω₀) ⟶ Spec (.of (AlgebraicClosure (S.residueField y))) :=
    Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure (S.residueField y)) Ω₀))
  have : ConnectedSpace ↥(pullback f yb) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) yb _ _
      (IsPullback.of_hasPullback f yb)
  have := ExposeX.baseChangeAlgClosedStatement (AlgebraicClosure (S.residueField y)) Ω₀
    (pullback.snd f yb)
  -- `m : X_s̄ ≅ X_ȳ ⊗ Ω₀ ⟶ X_ȳ`, along which base change is an equivalence `P`
  let e := pullbackLeftPullbackSndIso f yb j
  let m := e.inv ≫ pullback.fst (pullback.snd f yb) j
  have hm : pullback.fst f (j ≫ yb) = m ≫ pullback.fst f yb := by
    simp [m, e]
  have : (ExposeV.FEt.pullback m).IsEquivalence := ExposeV.FEt.isEquivalence_pullback_comp _ _
  let P := ExposeV.FEt.pullback m
  let ρ : ExposeV.FEt.pullback (pullback.fst f (j ≫ yb)) ≅
      ExposeV.FEt.pullback (pullback.fst f yb) ⋙ P :=
    MorphismProperty.Over.pullbackComp m (pullback.fst f yb) _ hm
  obtain ⟨t⟩ := h
  exact ⟨P.preimage (terminal.from _ ≫ t ≫ ρ.hom.app Z)⟩

/-- XIII.4.4, first part (the case of XIII.4.1 where `f` is proper, flat, with separable connected
geometric fibres; cf. X.1.3–X.1.4): for `S` connected and every set of primes `L`, the sequence
`π₁^L(X_s̄, a) → π'₁(X, a) → π₁(S, a) → 1` is exact, for every geometric point
`s̄ : Spec Ω₀ ⟶ S` (`Ω₀` algebraically closed) and every geometric point `a` of `X_s̄`. Stated,
as X.1.4 is here, for `S` locally noetherian (SGA has no noetherian hypothesis). -/
def ProperHomotopyExactSequenceStatement : Prop :=
  ∀ (L : Set ℕ) {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyConnected f]
    [GeometricallyReduced f] [IsLocallyNoetherian S] [ConnectedSpace S] (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s),
    IsProLExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s))

/-- X.1.4 in the situation of XIII.4.4: for `f` proper, flat, with separable connected geometric
fibres over a connected locally noetherian `S`, the sequence
`π₁(X_s̄, a) → π₁(X, a) → π₁(S, a) → 1` is exact, for every geometric point `s̄ : Spec Ω₀ ⟶ S`
(`Ω₀` algebraically closed) and every geometric point `a` of `X_s̄`. -/
def ProperHomotopyExactSequenceFullStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyConnected f]
    [GeometricallyReduced f] [IsLocallyNoetherian S] [ConnectedSpace S] (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s),
    (FundamentalGroup.map f (a ≫ pullback.fst f s)).comp
        (FundamentalGroup.map (pullback.fst f s) a) = 1 ∧
      Function.Surjective (FundamentalGroup.map f (a ≫ pullback.fst f s)) ∧
      (FundamentalGroup.map (pullback.fst f s) a).range =
        (FundamentalGroup.map f (a ≫ pullback.fst f s)).ker

/-- X.1.4 in the situation of XIII.4.4, at any geometric point. The composite is trivial
(`FundamentalGroup.map_comp_map_fst_eq_one`) and `π₁(X) → π₁(S)` is onto (IX.3.4). For the
exactness at `π₁(X)` we use the criterion `ker_autHom_le_range_iff` (V.6.11): a connected étale
covering `Z` of `X` with a section over `X_s̄` has one over the geometric fibre `X_ȳ` at the image
`y` of `s̄` (`nonempty_section_geometricPoint_of_isAlgClosed`, from X.1.8), so it comes from `S`
by X.1.3 (`SGA.SGA1.ExposeX.coveringOfBaseStatement`), which applies since `f_* 𝒪_X = 𝒪_S`
(EGA III 7.8.6, `isIso_app_of_geometricallyConnected`). -/
theorem properHomotopyExactSequenceFull : ProperHomotopyExactSequenceFullStatement.{u} := by
  intro X S f _ _ _ _ _ _ Ω₀ _ _ s Ω _ _ a
  have hcomp := FundamentalGroup.map_comp_map_fst_eq_one f s Ω a
  have hsurj : Function.Surjective (FundamentalGroup.map f (a ≫ pullback.fst f s)) :=
    ExposeIX.surjective_etaleFundamentalGroup_map_of_isProper f Ω _
  refine ⟨hcomp, hsurj, le_antisymm ((MonoidHom.range_le_ker_iff _ _).mpr hcomp) ?_⟩
  have : ExposeIX.Submersive f := inferInstance
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_submersive f
  have : ConnectedSpace ↥(pullback f s) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) s _ _
      (IsPullback.of_hasPullback f s)
  have hf := isIso_app_of_geometricallyConnected f
  have : ExposeX.IsSeparable f := ⟨⟩
  obtain ⟨y, _, hs⟩ := exists_eq_comp_geometricPoint Ω₀ s
  refine (ker_autHom_le_range_iff (ExposeV.FEt.pullback f) (fiberPullbackIso f _)
    (ExposeV.FEt.pullback (pullback.fst f s)) (fiberPullbackIso _ a)).mpr fun Z _ hsec ↦ ?_
  obtain ⟨t⟩ := nonempty_section_geometricPoint_of_isAlgClosed f y Ω₀ s hs Z hsec
  have : ConnectedSpace ((𝟭 Scheme.{u}).obj Z.left) := ExposeX.FEt.connectedSpace_of_isConnected Z
  obtain ⟨σ, hσ⟩ := ExposeX.FEt.exists_section_of_hom t
  obtain ⟨Y', q, hq, hqe, ψ, hψ⟩ := (ExposeX.coveringOfBaseStatement f hf y Z.hom).mpr ⟨σ, hσ⟩
  exact ⟨MorphismProperty.Over.mk ⊤ q ⟨hq, hqe⟩, (MorphismProperty.Over.isoMk ψ hψ).hom,
    inferInstance⟩

/-- XIII.4.4, first part, follows from X.1.4 ("cf. X 1.3"): the exactness of
`π₁(X_s̄) → π₁(X) → π₁(S) → 1` implies that of `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` for every set
of primes `L`. -/
theorem properHomotopyExactSequence_of_full
    (h : ProperHomotopyExactSequenceFullStatement.{u}) :
    ProperHomotopyExactSequenceStatement.{u} := by
  intro L X S f _ _ _ _ _ _ Ω₀ _ _ s Ω _ _ a
  obtain ⟨hcomp, hs, hex⟩ := h f Ω₀ s Ω a
  exact ⟨hcomp, hs, hex ▸ le_sup_left⟩

/-- XIII.4.4, first part: for `f` proper, flat, with separable connected geometric fibres over a
connected locally noetherian base, any geometric point `s̄` of `S` and any set of primes `L`, the
sequence `π₁^L(X_s̄, a) → π'₁(X, a) → π₁(S, a) → 1` of XIII.4.0 is exact (see
`isProLExact_iff`); in particular for `L` the primes different from a prime `p`. -/
theorem properHomotopyExactSequence : ProperHomotopyExactSequenceStatement.{u} :=
  properHomotopyExactSequence_of_full properHomotopyExactSequenceFull

/-- XIII.4.4, second part (XIII.4.3 in the smooth case) (statement only): if moreover `f` is
smooth and has a section, and `L` is the set of primes different from the residue
characteristics of `S`, then `1 → π₁^L(X_s̄, a) → π'₁(X, a) → π₁(S, a) → 1` is exact. The
missing part is the injectivity of `π₁^L(X_s̄) → π'₁(X)`, whose proof in XIII.4.3 needs the local
constancy of `R¹f_*` (XIII.1.16) and cohomological properness. Stated in the setting of
`ProperHomotopyExactSequenceStatement` (`S` locally noetherian). -/
def ProperSmoothHomotopyExactSequenceStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    [IsLocallyNoetherian S] [ConnectedSpace S] (g : S ⟶ X), g ≫ f = 𝟙 S →
    ∀ (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s),
    IsProLShortExact (primesInvertibleOn S) (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s))

/-- XIII.4.5, without the injectivity of `π₁^L(X_s̄) → π'₁(X)` (XIII.4.3): let `f` be as in
XIII.4.4 with a section `g : S ⟶ X`, and `a` a geometric point of `X_s̄` lying on `g(S)`. Then
`π'₁(X, a)` is a semidirect product of `π₁(S, a)` by the image of `π₁^L(X_s̄, a)`, the section
acting through `π₁(g)`. -/
theorem exists_semidirectProduct_of_section (L : Set ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
    [IsLocallyNoetherian S] [ConnectedSpace S] (g : S ⟶ X) (hgf : g ≫ f = 𝟙 S) (Ω₀ : Type u)
    [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s)
    (ha : ((a ≫ pullback.fst f s) ≫ f) ≫ g = a ≫ pullback.fst f s) :
    ∃ (hcomp : (FundamentalGroup.map f (a ≫ pullback.fst f s)).comp
        (FundamentalGroup.map (pullback.fst f s) a) = 1)
      (φ : FundamentalGroup ((a ≫ pullback.fst f s) ≫ f) →* MulAut (proLToPrimeQuotient L
        (FundamentalGroup.map (pullback.fst f s) a) (FundamentalGroup.map f _)
        (FundamentalGroup.continuous_map _ _) hcomp).range)
      (e : (proLToPrimeQuotient L (FundamentalGroup.map (pullback.fst f s) a)
          (FundamentalGroup.map f _) (FundamentalGroup.continuous_map _ _) hcomp).range ⋊[φ]
        FundamentalGroup ((a ≫ pullback.fst f s) ≫ f) ≃*
          PrimeQuotient L (FundamentalGroup.map f (a ≫ pullback.fst f s))),
      (∀ x, e (SemidirectProduct.inl x) = x) ∧
      ∀ c, primeQuotientLift L (FundamentalGroup.map f (a ≫ pullback.fst f s))
        (e (SemidirectProduct.inr c)) = c := by
  have hex := properHomotopyExactSequence L f Ω₀ s Ω a
  -- `w : π₁(S, b) → π₁(X, b ≫ g) ≅ π₁(X, a)`
  let w := (ExposeV.FEt.fiberCongr Ω ha).conjAut.toMonoidHom.comp
    (FundamentalGroup.map g ((a ≫ pullback.fst f s) ≫ f))
  have hw : Function.Bijective ((FundamentalGroup.map f (a ≫ pullback.fst f s)).comp w) := by
    obtain ⟨φ, hφ⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω g f hgf
      ((a ≫ pullback.fst f s) ≫ f)
    have : (FundamentalGroup.map f (a ≫ pullback.fst f s)).comp w =
        (ExposeV.FEt.fiberCongr Ω (congrArg (· ≫ f) ha)).conjAut.toMonoidHom.comp
          (φ.conjAut.toMonoidHom) := by
      simp only [w]
      rw [← MonoidHom.comp_assoc, FundamentalGroup.map_comp_conjAut_fiberCongr f ha,
        MonoidHom.comp_assoc]
      exact congrArg _ hφ
    rw [this]
    exact ((ExposeV.FEt.fiberCongr Ω (congrArg (· ≫ f) ha)).conjAut.bijective).comp
      φ.conjAut.bijective
  obtain ⟨φ, e, he₁, he₂⟩ := exists_semidirectProduct_range_of_isProLExact _ _
    (FundamentalGroup.continuous_map _ _) hex w hw
  exact ⟨hex.1, φ, e, he₁, he₂⟩

/-- XIII.4.4, third part (statement only): let `p : Z ⟶ S` be proper, flat, with separable
connected geometric fibres, `S` connected, `Y` the support of a divisor with normal crossings
relative to `S` (XIII.2.1), `X = Z - Y`, and `L` the set of primes different from the residue
characteristics of `S`. Then `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact; SGA deduces this from
XIII.4.1 and the cohomological properness XIII.2.9 of tamely ramified coverings. Stated in the
setting of `ProperHomotopyExactSequenceStatement` (`S` locally noetherian). -/
def NormalCrossingsHomotopyExactSequenceStatement : Prop :=
  ∀ {Z S : Scheme.{u}} (p : Z ⟶ S) [IsProper p] [Flat p] [GeometricallyConnected p]
    [GeometricallyReduced p] [IsLocallyNoetherian S] [ConnectedSpace S] (X : Z.Opens),
    IsNormalCrossingsSupport p (X : Set Z)ᶜ →
    ∀ (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback (X.ι ≫ p) s),
    IsProLExact (primesInvertibleOn S) (FundamentalGroup.map (pullback.fst (X.ι ≫ p) s) a)
      (FundamentalGroup.map (X.ι ≫ p) (a ≫ pullback.fst (X.ι ≫ p) s))

/-- XIII.4.4, third part, with a section (statement only): in the situation of
`NormalCrossingsHomotopyExactSequenceStatement`, if moreover `X ⟶ S` is smooth and has a section,
the sequence `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact (the hypotheses of XIII.4.3 hold). -/
def NormalCrossingsShortExactSequenceStatement : Prop :=
  ∀ {Z S : Scheme.{u}} (p : Z ⟶ S) [IsProper p] [Flat p] [GeometricallyConnected p]
    [GeometricallyReduced p] [IsLocallyNoetherian S] [ConnectedSpace S] (X : Z.Opens),
    IsNormalCrossingsSupport p (X : Set Z)ᶜ → Smooth (X.ι ≫ p) →
    ∀ g : S ⟶ X, g ≫ X.ι ≫ p = 𝟙 S →
    ∀ (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback (X.ι ≫ p) s),
    IsProLShortExact (primesInvertibleOn S) (FundamentalGroup.map (pullback.fst (X.ι ≫ p) s) a)
      (FundamentalGroup.map (X.ι ≫ p) (a ≫ pullback.fst (X.ι ≫ p) s))

end HomotopySequence

section Kunneth

/-- XIII.4.6 (Künneth formula) for maximal pro-`L` quotients, when `X` is proper (then the
desingularization hypotheses a), b) of XIII.4.6 are not needed): for `k` algebraically closed,
`X` proper, connected and reduced over `k`, `Y` connected and locally noetherian over `k`, and a
rational point `c` of `X ×ₖ Y`, the projections induce an isomorphism
`π₁^L(X ×ₖ Y, c) ≅ π₁^L(X, c) × π₁^L(Y, c)` for every set of primes `L` (in SGA, `L = p'`). This
follows from X.1.7 (`SGA.SGA1.ExposeX.bijective_map_prod`) and `bijective_proLMap_prod`. -/
theorem bijective_proLMap_prod_of_isProper (L : Set ℕ) {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsProper sX]
    [IsReduced X] [ConnectedSpace X] [IsLocallyNoetherian Y] [ConnectedSpace Y]
    (c : Spec (.of k) ⟶ pullback sX sY) (hc : c ≫ pullback.snd sX sY ≫ sY = 𝟙 _) :
    Function.Bijective
      ((proLMap L (FundamentalGroup.map (pullback.fst sX sY) c)
          (FundamentalGroup.continuous_map _ _)).prod
        (proLMap L (FundamentalGroup.map (pullback.snd sX sY) c)
          (FundamentalGroup.continuous_map _ _))) :=
  bijective_proLMap_prod L _ _ _ _ (ExposeX.bijective_map_prod sX sY c hc)

end Kunneth

end SGA.SGA1.ExposeXIII
