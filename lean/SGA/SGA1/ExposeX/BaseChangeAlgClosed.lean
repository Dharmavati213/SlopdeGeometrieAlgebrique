/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import SGA.Foundations.Limits.BaseChange
import SGA.SGA1.ExposeIX.FiniteEtaleLimit
import SGA.SGA1.ExposeIX.FundamentalGroupDescent
import SGA.SGA1.ExposeX.HomotopySequence
import SGA.SGA1.ExposeX.SteinEtale

/-!
# SGA 1, Exposé X, 1.8: base change of the fundamental group to a larger algebraically closed field

X.1.8 (`baseChangeAlgClosedStatement`): for `X` proper and connected over an algebraically closed
field `k` and `k'` an algebraically closed extension, `X' ↦ X' ⊗ₖ k'` is an equivalence of the
categories of étale coverings, i.e. `π₁(X ⊗ₖ k') → π₁(X)` is an isomorphism
(`bijective_map_pullback_fst`). We follow SGA's proof:

* the passage to the limit ("a matter of sorites"): an étale covering of `X ⊗ₖ k'` is the inverse
  image of an étale covering of `X ⊗ₖ A` for a finitely generated `k`-subalgebra `A` of `k'`
  (`exists_fgSubalgebra_isPullback`), by the limit theorem for étale coverings (EGA IV 8.8.2,
  17.7.8) for `k' = colim A` (`isColimitFgSubalgebraCocone`);
* the reduction to `X` reduced: étale coverings do not change along the surjective closed
  immersion `X_red ⟶ X` (IX.1.7, `FEt.isEquivalence_pullback_of_isClosedImmersion`);
* for `X` reduced, surjectivity of `π₁(X ⊗ₖ k') → π₁(X)` (`surjective_map_pullback_of_isAlgClosed`)
  and injectivity: an element of the kernel maps to `π₁(X ×ₖ Spec A)` into the kernel of
  `π₁(X ×ₖ Spec A) → π₁(X) × π₁(Spec A)`, which is trivial by X.1.7
  (`eq_one_of_hom_app_pullback_eq_id`, from `bijective_map_prod`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeX

section FGSubalgebra

variable (k : Type u) [CommRing k] (k' : Type u) [CommRing k'] [Algebra k k']

/-- The finitely generated `k`-subalgebras of `k'`, ordered by inclusion. -/
abbrev FGSubalgebra : Type u := {A : Subalgebra k k' // A.FG}

instance : IsDirectedOrder (FGSubalgebra k k') where
  directed A B := ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, (le_sup_left : A.1 ≤ A.1 ⊔ B.1),
    (le_sup_right : B.1 ≤ A.1 ⊔ B.1)⟩

instance : Nonempty (FGSubalgebra k k') := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram `A ↦ A` of the finitely generated `k`-subalgebras of `k'`. -/
@[simps]
noncomputable abbrev fgSubalgebraDiagram : FGSubalgebra k k' ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of A.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The cocone of the inclusions `A ⟶ k'`. -/
@[simps]
noncomputable abbrev fgSubalgebraCocone : Cocone (fgSubalgebraDiagram k k') where
  pt := CommRingCat.of k'
  ι := { app A := CommRingCat.ofHom A.1.val.toRingHom }

/-- A `k`-algebra is the filtered colimit of its finitely generated subalgebras. -/
noncomputable def isColimitFgSubalgebraCocone : IsColimit (fgSubalgebraCocone k k') := by
  have : ReflectsColimit (fgSubalgebraDiagram k k') (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun (x : k') ↦ ?_)
    fun (i j : FGSubalgebra k k') xi xj hij ↦ ?_)
  · classical
    exact ⟨⟨Algebra.adjoin k {x}, ⟨{x}, by simp⟩⟩, ⟨x, Algebra.subset_adjoin rfl⟩, rfl⟩
  · obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact ⟨m, homOfLE him, homOfLE hjm, Subtype.ext hij⟩

/-- The structure maps `k ⟶ A`. -/
@[simps]
noncomputable def fgSubalgebraAlgebraMap :
    (Functor.const (FGSubalgebra k k')).obj (CommRingCat.of k) ⟶ fgSubalgebraDiagram k k' where
  app A := CommRingCat.ofHom (algebraMap k A.1)
  naturality A B f := by ext; simp

end FGSubalgebra

/-- X.1.8, the passage to the limit in its proof: let `X` be a quasi-compact and
quasi-separated scheme over `k` and `k'` a `k`-algebra (an algebraically closed extension in
X.1.8). Every étale covering `Y` of `X ⊗ₖ k'` is the inverse image of an étale covering of
`X ⊗ₖ A` for some finitely generated `k`-subalgebra `A` of `k'`. -/
theorem exists_fgSubalgebra_isPullback (k : Type u) [CommRing k] (k' : Type u) [CommRing k']
    [Algebra k k'] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X] {Y : Scheme.{u}}
    (q : Y ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsFinite q]
    [Etale q] :
    ∃ (A : Subalgebra k k') (_ : A.FG) (YA : Scheme.{u})
      (qA : YA ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k A)))) (e : Y ⟶ YA),
      IsFinite qA ∧ Etale qA ∧
        IsPullback e q qA (pullback.map s _ s _ (𝟙 X)
          (Spec.map (CommRingCat.ofHom A.val.toRingHom)) (𝟙 _) (by simp) (by
            rw [Category.comp_id, ← Spec.map_comp]
            rfl)) := by
  obtain ⟨A, YA, qA, e, h₁, h₂, h₃⟩ :=
    Scheme.exists_isPullback_pullbackSpec_of_isFinite_of_etale (fgSubalgebraAlgebraMap k k') s
      (c := fgSubalgebraCocone k k') (CommRingCat.ofHom (algebraMap k k')) (fun _ ↦ rfl)
      (isColimitFgSubalgebraCocone k k') q
  exact ⟨A.1, A.2, YA, qA, e, h₁, h₂, h₃⟩

section Nil

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.7 (I.8.3) for étale coverings: base change along a surjective closed immersion
`i : S₀ ⟶ S` is an equivalence of the categories of étale coverings. -/
theorem FEt.isEquivalence_pullback_of_isClosedImmersion {S₀ S : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] : (FEt.pullback i).IsEquivalence := by
  have hff := ExposeIX.fullyFaithfulOverPullbackOfUniversallyInjective i ExposeV.finiteEtaleHom
    (fun _ _ _ h ↦ h.2)
  have := hff.full
  have := hff.faithful
  have := ExposeIX.essSurj_pullback_etale_of_isClosedImmersion i
  have : (FEt.pullback i).EssSurj := ⟨fun Y ↦ by
    obtain ⟨Z, q, e, hq, hq', h⟩ := ExposeIX.exists_isPullback_of_essSurj_pullback_etale i Y.hom
    exact ⟨MorphismProperty.Over.mk ⊤ q ⟨hq, hq'⟩,
      ⟨(MorphismProperty.Over.isoMk h.isoPullback (IsPullback.isoPullback_hom_snd h)).symm⟩⟩⟩
  exact { }

/-- The reduced closed subscheme `X_red` (mathlib's closed subscheme of the nilradical) is
reduced. -/
theorem isReduced_nilradical_subscheme (X : Scheme.{u}) : IsReduced X.nilradical.subscheme := by
  have (U : X.nilradical.subschemeCover.openCover.I₀) :
      IsReduced (X.nilradical.subschemeCover.openCover.X U) := by
    let V : X.affineOpens := U
    have : _root_.IsReduced (Γ(X, V) ⧸ X.nilradical.ideal V) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    exact (inferInstance : IsReduced (Spec (.of (Γ(X, V) ⧸ X.nilradical.ideal V))))
  exact IsReduced.of_openCover (𝒰 := X.nilradical.subschemeCover.openCover)

instance (X : Scheme.{u}) : Surjective X.nilradical.subschemeι :=
  ⟨by rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι]; rfl⟩

end Nil

section Reduced

/-- A nonempty quasi-compact scheme locally of finite type over an algebraically closed field `K`
has a rational point. -/
lemma exists_comp_eq_id {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [CompactSpace X] [Nonempty ↥X] :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = 𝟙 _ := by
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := X))
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- `π₁(p)(σ)` acts trivially on the fibre of `Z` when `σ` acts trivially on the fibre of the
pull-back of `Z`. -/
lemma map_hom_app_eq_id {T P : Scheme.{u}} {Ω : Type u} [Field Ω] (p : T ⟶ P)
    (t : Spec (.of Ω) ⟶ T) (σ : ExposeV.etaleFundamentalGroup Ω t) (Z : FEt P)
    (h : σ.hom.app ((FEt.pullback p).obj Z) = 𝟙 _) :
    (ExposeV.etaleFundamentalGroup.map Ω p t σ).hom.app Z = 𝟙 _ := by
  rw [ExposeV.etaleFundamentalGroup.map, ExposeV.autMap_hom_app]
  erw [h]
  simp

/-- If `σ` acts trivially on the fibres of all coverings pulled back along `p`, then `π₁(p)` kills
`σ` (converse of `ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id`). -/
lemma map_eq_one_of_forall_hom_app_eq_id {T P : Scheme.{u}} {Ω : Type u} [Field Ω] (p : T ⟶ P)
    (t : Spec (.of Ω) ⟶ T) (σ : ExposeV.etaleFundamentalGroup Ω t)
    (h : ∀ Z, σ.hom.app ((FEt.pullback p).obj Z) = 𝟙 _) :
    ExposeV.etaleFundamentalGroup.map Ω p t σ = 1 := by
  apply Iso.ext
  refine NatTrans.ext (funext fun Z ↦ ?_)
  have h1 : (Iso.hom (1 : ExposeV.etaleFundamentalGroup Ω (t ≫ p))).app Z = 𝟙 _ := rfl
  rw [h1]
  exact map_hom_app_eq_id p t σ Z (h Z)

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
  [IsProper s] [IsReduced X] [ConnectedSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- X.1.7, in the form used for X.1.8: let `X` be proper, connected and reduced over `k`
algebraically closed and `T` connected, locally noetherian, quasi-compact and locally of finite
type over `k`. An element `τ` of `π₁(X ×ₖ T)`, at any geometric point, which acts trivially on the
inverse images of the étale coverings of `X` and of `T` is trivial. SGA's rational base point
(of `X ×ₖ T`) is transported to the given geometric point by a path (V.5.7). -/
theorem eq_one_of_hom_app_pullback_eq_id {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    [IsLocallyNoetherian T] [ConnectedSpace T] [CompactSpace T] [LocallyOfFiniteType sT]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ pullback s sT)
    (τ : ExposeV.etaleFundamentalGroup Ω z)
    (h₁ : ∀ E : FEt X, τ.hom.app ((FEt.pullback (pullback.fst s sT)).obj E) = 𝟙 _)
    (h₂ : ∀ W : FEt T, τ.hom.app ((FEt.pullback (pullback.snd s sT)).obj W) = 𝟙 _) :
    τ = 1 := by
  -- rational points of `X` and `T`, and of `X ×ₖ T`
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨x₀, hx₀⟩ := exists_comp_eq_id s
  obtain ⟨t₀, ht₀⟩ := exists_comp_eq_id sT
  let c : Spec (.of k) ⟶ pullback s sT := pullback.lift x₀ t₀ (by rw [hx₀, ht₀])
  have hc : c ≫ pullback.snd s sT ≫ sT = 𝟙 _ := by
    rw [pullback.lift_snd_assoc, ht₀]
  -- `X ×ₖ T` is connected
  have : GeometricallyConnected (pullback.snd s sT) :=
    CohomologyAux.geometricallyConnected_of_isIso_app _ (isIso_app_snd s sT)
  have : Surjective s := ⟨fun _ ↦ ⟨Classical.arbitrary X, Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace ↥(pullback s sT) :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap (pullback.snd s sT)
      (ExposeIX.universally_isQuotientMap_of_universallyClosed _)
  -- a path from the rational point `c` to `z`
  obtain ⟨γ⟩ := ExposeV.nonempty_iso_of_fiberFunctor (ExposeV.FEt.fiber k c)
    (ExposeV.FEt.fiber Ω z)
  let ω : ExposeV.etaleFundamentalGroup k c := γ ≪≫ (τ : _ ≅ _) ≪≫ γ.symm
  have hω (W : FEt (pullback s sT)) (hW : τ.hom.app W = 𝟙 _) : ω.hom.app W = 𝟙 _ := by
    simp [ω, hW]
  have hω₁ : ω = 1 := by
    refine (bijective_map_prod s sT c hc).1 (Prod.ext ?_ ?_)
    · simp only [MonoidHom.prod_apply, map_one]
      exact map_eq_one_of_forall_hom_app_eq_id _ _ ω fun E ↦ hω _ (h₁ E)
    · simp only [MonoidHom.prod_apply, map_one]
      exact map_eq_one_of_forall_hom_app_eq_id _ _ ω fun W ↦ hω _ (h₂ W)
  have h := congrArg (fun ρ : ExposeV.etaleFundamentalGroup k c ↦ γ.inv ≫ ρ.hom ≫ γ.hom) hω₁
  have h1 : Iso.hom (1 : ExposeV.etaleFundamentalGroup k c) = 𝟙 _ := rfl
  have h2 : Iso.hom (1 : ExposeV.etaleFundamentalGroup Ω z) = 𝟙 _ := rfl
  apply Iso.ext
  rw [h2]
  simpa [ω, h1] using h

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8, the key step of SGA's proof, for `X` reduced: let `X` be proper, connected and reduced
over `k` algebraically closed, `k'` an algebraically closed extension and `σ ∈ π₁(X ⊗ₖ k')`
(at any geometric point) in the kernel of `π₁(X ⊗ₖ k') → π₁(X)`, i.e. acting trivially on the
inverse images of the étale coverings of `X`. Then `σ` acts trivially on every étale covering `Y`
of `X ⊗ₖ k'`. As in SGA: `Y` comes from an étale covering `Z` of `X ⊗ₖ A` for a finitely
generated `k`-subalgebra `A` of `k'` (`exists_fgSubalgebra_isPullback`); the image of `σ` in
`π₁(X ×ₖ Spec A)` acts trivially on the coverings coming from `X` (as `σ` is in the kernel) and
on those coming from `Spec A` (they become trivial over `Spec k'`), so it is trivial by X.1.7
(`eq_one_of_hom_app_pullback_eq_id`). -/
theorem hom_app_eq_id_of_forall_hom_app_pullback_eq_id (k' : Type u) [Field k'] [IsAlgClosed k']
    [Algebra k k'] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (σ : ExposeV.etaleFundamentalGroup Ω x)
    (hσ : ∀ E : FEt X, σ.hom.app ((FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj E) = 𝟙 _)
    (Y : FEt (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) :
    σ.hom.app Y = 𝟙 _ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s
  obtain ⟨A, hA, YA, qA, e, hqA, heA, hpb⟩ := exists_fgSubalgebra_isPullback k k' s Y.hom
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let sA : Spec (.of A) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let jA : Spec (.of k') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  let ι : pullback s ρ ⟶ pullback s sA := pullback.map s _ s _ (𝟙 X) jA (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← Spec.map_comp]
    rfl)
  have hpb' : IsPullback e Y.hom qA ι := hpb
  have hι₁ : ι ≫ pullback.fst s sA = pullback.fst s ρ := by simp [ι]
  have hι₂ : ι ≫ pullback.snd s sA = pullback.snd s ρ ≫ jA := by simp [ι]
  -- `Spec A` is noetherian, connected and of finite type over `k`
  have : Algebra.FiniteType k A := A.fg_iff_finiteType.mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : LocallyOfFiniteType sA :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr ‹_›)
  -- `Y = ι^* Z`
  let Z : FEt (pullback s sA) := MorphismProperty.Over.mk ⊤ qA ⟨hqA, heA⟩
  let φ : Y ≅ (FEt.pullback ι).obj Z :=
    MorphismProperty.Over.isoMk hpb'.isoPullback hpb'.isoPullback_hom_snd
  refine ExposeV.aut_app_eq_id_of_iso σ φ.symm ?_
  refine ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω ι x σ ?_ Z
  refine eq_one_of_hom_app_pullback_eq_id s sA Ω (x ≫ ι) _ (fun E ↦ ?_) (fun W ↦ ?_)
  · apply map_hom_app_eq_id
    let ψ : (FEt.pullback ι).obj ((FEt.pullback (pullback.fst s sA)).obj E) ≅
        (FEt.pullback (pullback.fst s ρ)).obj E :=
      ((MorphismProperty.Over.pullbackComp ι (pullback.fst s sA)).app E).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hι₁).app E
    exact ExposeV.aut_app_eq_id_of_iso σ ψ.symm (hσ E)
  · apply map_hom_app_eq_id
    let ψ : (FEt.pullback ι).obj ((FEt.pullback (pullback.snd s sA)).obj W) ≅
        (FEt.pullback (pullback.snd s ρ)).obj ((FEt.pullback jA).obj W) :=
      ((MorphismProperty.Over.pullbackComp ι (pullback.snd s sA)).app W).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hι₂).app W ≪≫
          (MorphismProperty.Over.pullbackComp (pullback.snd s ρ) jA).app W
    refine ExposeV.aut_app_eq_id_of_iso σ ψ.symm ?_
    exact ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω (pullback.snd s ρ) x σ
      (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω k' _ _) _

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8 for `X` reduced: for `X` proper, connected and reduced over `k` algebraically closed and
`k'` an algebraically closed extension of `k`, base change `X' ↦ X' ⊗ₖ k'` is an equivalence
of the categories of étale coverings. Surjectivity of `π₁(X ⊗ₖ k') → π₁(X)` is
`surjective_map_pullback_of_isAlgClosed`; injectivity is
`hom_app_eq_id_of_forall_hom_app_pullback_eq_id`; V.6.10 concludes. -/
theorem isEquivalence_pullback_fst_of_isReduced (k' : Type u) [Field k'] [IsAlgClosed k']
    [Algebra k k'] :
    (FEt.pullback (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence
    := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst s ρ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨x₀, hx₀⟩ := exists_comp_eq_id s
  let x : Spec (.of k') ⟶ pullback s ρ := pullback.lift (ρ ≫ x₀) (𝟙 _) (by
    rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])
  have : ConnectedSpace ↥(pullback s ρ) := connectedSpace_pullback_of_isAlgClosed s k'
  let F' := ExposeV.FEt.fiber k' x
  have : FiberFunctor (FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso k' π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (FEt.pullback π) F']
  refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_, ?_⟩
  · apply Iso.ext
    refine NatTrans.ext (funext fun Y ↦ ?_)
    refine hom_app_eq_id_of_forall_hom_app_pullback_eq_id s k' k' x σ (fun E ↦ ?_) Y
    exact congrArg (fun τ : Aut (FEt.pullback π ⋙ F') ↦ τ.hom.app E) hσ
  · have h := surjective_map_pullback_of_isAlgClosed s k' k' x
    rwa [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp, MonoidHom.coe_comp,
      MulEquiv.coe_toMonoidHom, Function.Surjective.of_comp_iff' (MulEquiv.bijective _)] at h

end Reduced

set_option backward.isDefEq.respectTransparency false in
/-- **X.1.8**: if `X` is proper and connected over an algebraically closed field `k` and `k'` is an
algebraically closed extension of `k`, then `X' ↦ X' ⊗ₖ k'` is an equivalence from the étale
coverings of `X` to those of `X ⊗ₖ k'`; equivalently (V.6.10,
`bijective_map_of_baseChangeAlgClosed`) `π₁(X ⊗ₖ k') → π₁(X)` is an isomorphism. As in SGA, we
reduce to `X` reduced (the étale coverings do not change on passing to `X_red`, IX.1.7), which is
`isEquivalence_pullback_fst_of_isReduced`. -/
theorem baseChangeAlgClosedStatement : BaseChangeAlgClosedStatement.{u} := by
  intro k k' _ _ _ _ _ X s _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let i := X.nilradical.subschemeι
  have := isReduced_nilradical_subscheme X
  have hi : IsHomeomorph i :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩
  have : ConnectedSpace X.nilradical.subscheme :=
    (IsHomeomorph.homeomorph _ hi).symm.surjective.connectedSpace
      (IsHomeomorph.homeomorph _ hi).symm.continuous
  have := isEquivalence_pullback_fst_of_isReduced (i ≫ s) k'
  let i' : pullback (i ≫ s) ρ ⟶ pullback s ρ :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hw : i' ≫ pullback.fst s ρ = pullback.fst (i ≫ s) ρ ≫ i := by simp [i']
  have h₂ : i' ≫ pullback.snd s ρ = pullback.snd (i ≫ s) ρ := by simp [i']
  have hsq : IsPullback i' (pullback.fst (i ≫ s) ρ) (pullback.fst s ρ) i :=
    IsPullback.of_right (h₁₁ := i') (h₁₂ := pullback.snd s ρ)
      (by rw [h₂]; exact (IsPullback.of_hasPullback (i ≫ s) ρ).flip) hw
      (IsPullback.of_hasPullback s ρ).flip
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback hsq.flip
    (inferInstance : IsClosedImmersion X.nilradical.subschemeι)
  have : Surjective i' := MorphismProperty.of_isPullback hsq.flip
    (inferInstance : Surjective X.nilradical.subschemeι)
  have := FEt.isEquivalence_pullback_of_isClosedImmersion i
  have := FEt.isEquivalence_pullback_of_isClosedImmersion i'
  have : (FEt.pullback (pullback.fst (i ≫ s) ρ ≫ i)).IsEquivalence :=
    ExposeV.FEt.isEquivalence_pullback_comp _ _
  have : (FEt.pullback (i' ≫ pullback.fst s ρ)).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackCongr hw.symm)
  have : (FEt.pullback (pullback.fst s ρ) ⋙ FEt.pullback i').IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp i' (pullback.fst s ρ))
  exact Functor.isEquivalence_of_comp_right _ (FEt.pullback i')

/-- X.1.8: for `X` proper and connected over an algebraically closed field `k`, `k'` an
algebraically closed extension of `k` and `t` a geometric point of `X ⊗ₖ k'`,
`π₁(X ⊗ₖ k', t) → π₁(X, t)` is bijective. -/
theorem bijective_map_pullback_fst (k k' : Type u) [Field k] [IsAlgClosed k] [Field k']
    [IsAlgClosed k'] [Algebra k k'] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s]
    [ConnectedSpace X] (Ω : Type u) [Field Ω]
    (t : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k')))) t) :=
  bijective_map_of_baseChangeAlgClosed baseChangeAlgClosedStatement k k' s Ω t

end SGA.SGA1.ExposeX
