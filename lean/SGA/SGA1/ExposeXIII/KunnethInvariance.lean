/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeXIII.KunnethMain

/-!
# SGA 1, XIII.4.6: invariance under algebraically closed base change from the Künneth formula

SGA proves X.1.8 (invariance of `π₁` of a proper `X` under algebraically closed base change
`k ⊆ k'`) from X.1.7: an étale covering of `X ⊗ₖ k'` comes from `X ×ₖ Spec A` for a finitely
generated `k`-subalgebra `A` of `k'`, and an element of `π₁(X ⊗ₖ k')` killed by `π₁(X ⊗ₖ k') →
π₁(X)` maps to an element of `π₁(X ×ₖ Spec A)` killed by both projections. The argument only uses
the injectivity half of the Künneth formula for `X ×ₖ Spec A`, and no properness otherwise.
We record it for quasi-compact quasi-separated `X`, with `A` running over any cofinal family of
finitely generated subalgebras of `k'` (for instance the smooth ones, in characteristic `0`):

* `isEquivalence_pullback_fst_of_injective_map_prod`: if `π₁(X ×ₖ Spec B) → π₁(X) × π₁(Spec B)`
  is injective for a cofinal family of finitely generated `k`-subalgebras `B` of `k'`, then
  `X' ↦ X' ⊗ₖ k'` is an equivalence `FEt(X) ≌ FEt(X ⊗ₖ k')`.
* `hasAlgClosedBaseChangeInvariance_of_cofinal`: with the main lemma
  (`bijective_map_prod_of_isNormalScheme_of_invariance`), for `X` normal: if every finitely
  generated `k`-subalgebra of `k'` is contained in a finitely generated `B` with `Spec B` smooth
  over `k` and having the invariance property, then `FEt(X) ≌ FEt(X ⊗ₖ k')`. This is the step of
  the transcendence-degree induction of the resolution-free route: for `k'` of transcendence
  degree `1` over `k`, the `Spec B` are smooth affine curves, which can be chosen étale over open
  subsets of `𝔸¹` (`exists_le_fg_invariance_of_trdeg_le_one`).

The surjectivity of `π₁(X ⊗ₖ k') → π₁(X)` holds in general
(`ExposeX.surjective_map_pullback_fst_of_isAlgClosed`). This is the reduction of invariance to the
Künneth formula used in the resolution-free route to XIII.4.6 in characteristic `0`.

The two lemmas here are SGA's X.1.8 argument
(`SGA.SGA1.ExposeX.hom_app_eq_id_of_forall_hom_app_pullback_eq_id`,
`SGA.SGA1.ExposeX.isEquivalence_pullback_fst_of_isReduced` in
`SGA/SGA1/ExposeX/BaseChangeAlgClosed.lean`) with X.1.7 replaced by the Künneth-injectivity
hypothesis and properness dropped; the proper versions are the special case where X.1.7 supplies
that hypothesis.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
/-- The key step of X.1.8, without properness: let `X` be quasi-compact and quasi-separated over
a field `k`, `k'` an algebraically closed extension, and assume the injectivity half of the
Künneth formula for `X ×ₖ Spec B`, `B` running over a cofinal family of finitely generated
`k`-subalgebras of `k'`. An element `σ` of `π₁(X ⊗ₖ k')` acting trivially on the inverse images
of the étale coverings of `X` acts trivially on every étale covering of `X ⊗ₖ k'`. -/
theorem hom_app_eq_id_of_injective_map_prod [QuasiCompact s] [QuasiSeparated s]
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'] (P : Subalgebra k k' → Prop)
    (hP : ∀ A : Subalgebra k k', A.FG → ∃ B, A ≤ B ∧ B.FG ∧ P B)
    (h : ∀ B : Subalgebra k k', B.FG → P B → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (c : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k B)))),
      Function.Injective ((FundamentalGroup.map (pullback.fst _ _) c).prod
        (FundamentalGroup.map (pullback.snd _ _) c)))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (σ : ExposeV.etaleFundamentalGroup Ω x)
    (hσ : ∀ E : ExposeV.FEt X, σ.hom.app ((ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj E) = 𝟙 _)
    (Y : ExposeV.FEt (pullback s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) :
    σ.hom.app Y = 𝟙 _ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s
  have hYf : IsFinite Y.hom := Y.prop.1
  have hYe : Etale Y.hom := Y.prop.2
  obtain ⟨A, hA, YA, qA, e, hqA, heA, hpb⟩ := ExposeX.exists_fgSubalgebra_isPullback k k' s Y.hom
  obtain ⟨B, hAB, hB, hPB⟩ := hP A hA
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let sA : Spec (.of A) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let sB : Spec (.of B) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k B))
  let jA : Spec (.of k') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  let jB : Spec (.of k') ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom B.val.toRingHom)
  let jBA : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAB).toRingHom)
  have hjB : jB ≫ sB = ρ := by
    rw [← Spec.map_comp]
    rfl
  have hjBA : jBA ≫ sA = sB := by
    rw [← Spec.map_comp]
    rfl
  have hjA : jB ≫ jBA = jA := by
    rw [← Spec.map_comp]
    rfl
  let ιA : pullback s ρ ⟶ pullback s sA := pullback.map s _ s _ (𝟙 X) jA (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← Spec.map_comp]
    rfl)
  let ιB : pullback s ρ ⟶ pullback s sB :=
    pullback.map s _ s _ (𝟙 X) jB (𝟙 _) (by simp) (by rw [Category.comp_id, hjB])
  let κ : pullback s sB ⟶ pullback s sA :=
    pullback.map s _ s _ (𝟙 X) jBA (𝟙 _) (by simp) (by rw [Category.comp_id, hjBA])
  have hι : ιB ≫ κ = ιA := by
    apply pullback.hom_ext
    · simp [ιA, ιB, κ]
    · simp only [ιA, ιB, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hjA]
  have hpb' : IsPullback e Y.hom qA ιA := hpb
  have hιB₁ : ιB ≫ pullback.fst s sB = pullback.fst s ρ := by simp [ιB]
  have hιB₂ : ιB ≫ pullback.snd s sB = pullback.snd s ρ ≫ jB := by simp [ιB]
  -- `Y = ιB^* (κ^* ZA)`
  let ZA : ExposeV.FEt (pullback s sA) := MorphismProperty.Over.mk ⊤ qA ⟨hqA, heA⟩
  let Z : ExposeV.FEt (pullback s sB) := (ExposeV.FEt.pullback κ).obj ZA
  let φ₀ : Y ≅ (ExposeV.FEt.pullback ιA).obj ZA :=
    MorphismProperty.Over.isoMk hpb'.isoPullback hpb'.isoPullback_hom_snd
  let φ : Y ≅ (ExposeV.FEt.pullback ιB).obj Z :=
    φ₀ ≪≫
      (MorphismProperty.Over.pullbackCongr hι.symm).app ZA ≪≫
        (MorphismProperty.Over.pullbackComp ιB κ).app ZA
  refine ExposeV.aut_app_eq_id_of_iso σ φ.symm ?_
  refine ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω ιB x σ ?_ Z
  -- the image of `σ` in `π₁(X ×ₖ Spec B)` is killed by both projections
  refine h B hB hPB Ω (x ≫ ιB) (Prod.ext ?_ ?_)
  · change ExposeV.etaleFundamentalGroup.map Ω _ _ _ = ExposeV.etaleFundamentalGroup.map Ω _ _ 1
    rw [map_one]
    refine ExposeX.map_eq_one_of_forall_hom_app_eq_id _ _ _ fun E ↦ ?_
    apply ExposeX.map_hom_app_eq_id
    let ψ : (ExposeV.FEt.pullback ιB).obj ((ExposeV.FEt.pullback (pullback.fst s sB)).obj E) ≅
        (ExposeV.FEt.pullback (pullback.fst s ρ)).obj E :=
      ((MorphismProperty.Over.pullbackComp ιB (pullback.fst s sB)).app E).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hιB₁).app E
    exact ExposeV.aut_app_eq_id_of_iso σ ψ.symm (hσ E)
  · change ExposeV.etaleFundamentalGroup.map Ω _ _ _ = ExposeV.etaleFundamentalGroup.map Ω _ _ 1
    rw [map_one]
    refine ExposeX.map_eq_one_of_forall_hom_app_eq_id _ _ _ fun W ↦ ?_
    apply ExposeX.map_hom_app_eq_id
    let ψ : (ExposeV.FEt.pullback ιB).obj ((ExposeV.FEt.pullback (pullback.snd s sB)).obj W) ≅
        (ExposeV.FEt.pullback (pullback.snd s ρ)).obj ((ExposeV.FEt.pullback jB).obj W) :=
      ((MorphismProperty.Over.pullbackComp ιB (pullback.snd s sB)).app W).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hιB₂).app W ≪≫
          (MorphismProperty.Over.pullbackComp (pullback.snd s ρ) jB).app W
    refine ExposeV.aut_app_eq_id_of_iso σ ψ.symm ?_
    exact ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω (pullback.snd s ρ) x σ
      (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω k' _ _) _

set_option backward.isDefEq.respectTransparency false in
/-- X.1.8 without properness, from the injectivity half of the Künneth formula: let `X` be
quasi-compact, quasi-separated and connected over an algebraically closed field `k`, and `k'` an
algebraically closed extension of `k`. If `π₁(X ×ₖ Spec B) → π₁(X) × π₁(Spec B)` is injective (at
every geometric point) for a cofinal family of finitely generated `k`-subalgebras `B` of `k'`,
then `X' ↦ X' ⊗ₖ k'` is an equivalence `FEt(X) ≌ FEt(X ⊗ₖ k')`. -/
theorem isEquivalence_pullback_fst_of_injective_map_prod [QuasiCompact s] [QuasiSeparated s]
    [ConnectedSpace X] (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k']
    (P : Subalgebra k k' → Prop) (hP : ∀ A : Subalgebra k k', A.FG → ∃ B, A ≤ B ∧ B.FG ∧ P B)
    (h : ∀ B : Subalgebra k k', B.FG → P B → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (c : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k B)))),
      Function.Injective ((FundamentalGroup.map (pullback.fst _ _) c).prod
        (FundamentalGroup.map (pullback.snd _ _) c))) :
    (ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst s ρ
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback s ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace s ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback s ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback s ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback s ρ := ExposeX.geometricPoint _ z
  let F' := ExposeV.FEt.fiber Ω x
  have : FiberFunctor (ExposeV.FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback π) F']
  refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_, ?_⟩
  · apply Iso.ext
    refine NatTrans.ext (funext fun Y ↦ ?_)
    refine hom_app_eq_id_of_injective_map_prod s k' P hP h Ω x σ (fun E ↦ ?_) Y
    exact congrArg (fun τ : Aut (ExposeV.FEt.pullback π ⋙ F') ↦ τ.hom.app E) hσ
  · -- surjectivity: connected coverings of `X` stay connected over `k'`
    have hsurj := ExposeX.surjective_map_pullback_fst_of_isAlgClosed s k' Ω x
    rwa [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.Surjective.of_comp_iff' (MulEquiv.bijective _)] at hsurj

/-- The step of the transcendence-degree induction (resolution-free route to XIII.4.6, any
characteristic): let `X` be connected, normal, quasi-compact, quasi-separated and locally of finite
type over an algebraically closed field `k`, and `k'` an algebraically closed extension of `k`.
If every finitely generated `k`-subalgebra of `k'` is contained in a finitely generated `B` such
that `Spec B` is smooth over `k` and has the invariance property, then `X' ↦ X' ⊗ₖ k'` is an
equivalence `FEt(X) ≌ FEt(X ⊗ₖ k')`. By the main lemma, `π₁(X ×ₖ Spec B) → π₁(X) × π₁(Spec B)`
is bijective for such `B`, and `isEquivalence_pullback_fst_of_injective_map_prod` applies. -/
theorem isEquivalence_pullback_fst_of_cofinal [QuasiCompact s] [QuasiSeparated s]
    [LocallyOfFiniteType s] [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X) (k' : Type u)
    [Field k'] [IsAlgClosed k'] [Algebra k k']
    (hP : ∀ A : Subalgebra k k', A.FG → ∃ B, A ≤ B ∧ B.FG ∧
      (Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) ∧
        HasAlgClosedBaseChangeInvariance (Spec.map (CommRingCat.ofHom (algebraMap k B))))) :
    (ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence := by
  refine isEquivalence_pullback_fst_of_injective_map_prod s k' _ hP fun B _ hB Ω _ _ c ↦ ?_
  obtain ⟨_, hinv⟩ := hB
  have : ConnectedSpace (Spec (.of B)) := inferInstance
  exact (bijective_map_prod_of_isNormalScheme_of_invariance s _ hX hinv Ω c).1

/-- `isEquivalence_pullback_fst_of_cofinal` in terms of `HasAlgClosedBaseChangeInvariance`: if for
every algebraically closed extension `k'` of `k`, the finitely generated `k`-subalgebras of `k'`
with smooth spectrum having the invariance property are cofinal, then every connected, normal,
quasi-compact, quasi-separated `X` locally of finite type over `k` has the invariance property. -/
theorem hasAlgClosedBaseChangeInvariance_of_cofinal [QuasiCompact s] [QuasiSeparated s]
    [LocallyOfFiniteType s] [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X)
    (hP : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'] (A : Subalgebra k k'),
      A.FG → ∃ B, A ≤ B ∧ B.FG ∧
        (Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) ∧
          HasAlgClosedBaseChangeInvariance (Spec.map (CommRingCat.ofHom (algebraMap k B))))) :
    HasAlgClosedBaseChangeInvariance s :=
  fun k' _ _ _ ↦ isEquivalence_pullback_fst_of_cofinal s hX k' (hP k')

end SGA.SGA1.ExposeXIII
