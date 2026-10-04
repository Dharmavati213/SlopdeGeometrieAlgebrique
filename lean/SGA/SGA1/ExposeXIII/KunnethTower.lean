/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import SGA.Foundations.Smooth.GenericSmoothness
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeXIII.KunnethCurveOpen
import SGA.SGA1.ExposeXIII.KunnethNormalProduct

/-!
# SGA 1, XIII.4.6 in characteristic `0`: invariance for smooth schemes from the case of curves

The resolution-free route to XIII.4.6 in characteristic `0` reduces the invariance of `π₁` under
algebraically closed base change (`InvarianceCharZeroStatement`) for smooth (and then normal)
schemes of finite type to the case of the open subsets of the affine line,
`AffineLineOpenInvarianceStatement` (milestone C1 of the route, proved as
`affineLineOpenInvarianceStatement` in `SGA.SGA1.ExposeXIII.KunnethCurveInvariance`; the results
below take it as a hypothesis `hC`), by induction on
the transcendence degree of `k'` over `k` (`hasAlgClosedBaseChangeInvariance_of_smooth`):

* the step: `isEquivalence_pullback_fst_of_trdeg_le_one` (`KunnethCurveOpen`): for `X` connected,
  normal, quasi-compact, quasi-separated and locally of finite type over an algebraically closed
  field `k` of characteristic `0`, and `k'` algebraically closed of transcendence degree at most
  `1` over `k`, `FEt(X) ≌ FEt(X ⊗ₖ k')`;
* `exists_isAlgClosed_trdeg_eq`: an algebraically closed field `L` of transcendence degree `n + 1`
  over `k` contains an algebraically closed `L'` with `trdeg_k L' = n` and `trdeg_{L'} L = 1` (the
  relative algebraic closure of `k(s ∖ {x})`, `s` a transcendence basis, `x ∈ s`);
* `isEquivalence_pullback_fst_of_trdeg_eq`: by induction on `n`, for `X` smooth, quasi-compact,
  quasi-separated and connected over `k` and `L` algebraically closed of transcendence degree `n`,
  `FEt(X) ≌ FEt(X ⊗ₖ L)`; each step is `isEquivalence_pullback_fst_of_trdeg_le_one` over `L'` for
  `X ⊗ₖ L'` (still smooth, hence normal);
* `hasAlgClosedBaseChangeInvariance_of_smooth`: for arbitrary `k'`, an étale covering of
  `X ⊗ₖ k'` comes from `X ⊗ₖ A`, `A ⊆ k'` finitely generated, hence from `X ⊗ₖ L` for `L` the
  algebraic closure of `k(A)` in `k'`, which has finite transcendence degree.

So `AffineLineOpenInvarianceStatement` implies the invariance for every smooth quasi-compact
quasi-separated connected scheme in characteristic `0`, then (by generic smoothness,
`Subalgebra.exists_le_fg_smooth`) for every normal one locally of finite type
(`hasAlgClosedBaseChangeInvariance_of_isNormalScheme`), and XIII.4.6 for `X` normal and `Y`
smooth (`bijective_map_prod_of_isNormalScheme_of_smooth`) or normal and quasi-compact
(`bijective_map_prod_of_isNormalScheme_of_isNormalScheme`, with the normality of `X ×ₖ Y`,
`isNormalScheme_pullback`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

section Tower

open Cardinal

/-- Finite cardinal arithmetic: `a + b = n + 1`, `n ≤ a` and `1 ≤ b` force `a = n`, `b = 1`. -/
private lemma eq_and_eq_of_add_eq {a b : Cardinal} {n : ℕ} (h : a + b = n + 1) (ha : n ≤ a)
    (hb : 1 ≤ b) : a = n ∧ b = 1 := by
  have hlt : a + b < ℵ₀ := h ▸ (by exact_mod_cast Cardinal.natCast_lt_aleph0 (n := n + 1))
  obtain ⟨p, rfl⟩ := Cardinal.lt_aleph0.mp ((le_self_add).trans_lt hlt)
  obtain ⟨q, rfl⟩ := Cardinal.lt_aleph0.mp ((le_add_self).trans_lt hlt)
  norm_cast at h ha hb ⊢
  omega

/-- An algebraically closed field `L` of transcendence degree `n + 1` over `k` contains an
algebraically closed subfield `L' ⊇ k` with `trdeg_k L' = n` and `trdeg_{L'} L = 1`: for a
transcendence basis `s` and `x ∈ s`, take the algebraic closure of `k(s ∖ {x})` in `L`. -/
theorem exists_isAlgClosed_trdeg_eq (k L : Type u) [Field k] [Field L] [IsAlgClosed L]
    [Algebra k L] (n : ℕ) (h : Algebra.trdeg k L = n + 1) :
    ∃ L' : IntermediateField k L, IsAlgClosed L' ∧ Algebra.trdeg k L' = n ∧
      Algebra.trdeg L' L = 1 := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hcard : #s = n + 1 := by rw [hs.cardinalMk_eq_trdeg, h]
  obtain ⟨x, hx⟩ : s.Nonempty := by
    rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hcard]
    exact_mod_cast Nat.succ_ne_zero n
  let F := IntermediateField.adjoin k (s \ {x})
  let L₀ := algebraicClosure F L
  let L' : IntermediateField k L := L₀.restrictScalars k
  have hL₀ : IsAlgClosed L₀ := IsAlgClosure.isAlgClosed F
  have hL' : IsAlgClosed L' := hL₀
  -- `x` is transcendental over `F`, hence over `L'`
  have hxF : Transcendental F x := by
    rw [IntermediateField.transcendental_adjoin_iff]
    have := (hs.1.transcendental_adjoin_iff (s := ({⟨x, hx⟩}ᶜ : Set s)) (i := ⟨x, hx⟩)).mpr
      (by simp)
    have hset : Subtype.val '' ({⟨x, hx⟩}ᶜ : Set s) = s \ {x} := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image, Set.mem_compl_iff]
      constructor
      · rintro ⟨⟨y, hy⟩, hyx, rfl⟩
        exact ⟨hy, fun h ↦ hyx (Subtype.ext h)⟩
      · rintro ⟨hy, hyx⟩
        exact ⟨⟨y, hy⟩, fun h ↦ hyx (congrArg Subtype.val h), rfl⟩
    rwa [hset] at this
  have hxL' : Transcendental L' x := hxF.algebraicClosure
  -- `s ∖ {x}` lies in `L'` and is algebraically independent there
  have hsub : ∀ y ∈ s \ {x}, y ∈ L' := fun y hy ↦ by
    change y ∈ L₀
    rw [mem_algebraicClosure_iff]
    exact isAlgebraic_algebraMap (⟨y, IntermediateField.subset_adjoin k _ hy⟩ : F)
  let f : (s \ {x} : Set L) → L' := fun y ↦ ⟨y, hsub y y.2⟩
  have hf : AlgebraicIndependent k f := by
    refine AlgebraicIndependent.of_comp (L'.val) ?_
    have : (L'.val ∘ f) = (fun y : (s \ {x} : Set L) ↦ (y : L)) := rfl
    rw [this]
    exact hs.1.comp (fun y : (s \ {x} : Set L) ↦ (⟨y, y.2.1⟩ : s))
      (fun a b h ↦ Subtype.ext (by simpa using congrArg (fun z : s ↦ (z : L)) h))
  have hdiff : #(s \ {x} : Set L) + 1 = n + 1 := by
    rw [← hcard, ← Cardinal.mk_insert (fun h ↦ h.2 rfl), Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem hx]
  have h₁ : (n : Cardinal) ≤ Algebra.trdeg k L' := by
    have := hf.cardinalMk_le_trdeg
    have hn : #(s \ {x} : Set L) = n := by
      have hlt : #(s \ {x} : Set L) < ℵ₀ := by
        have hle : #(s \ {x} : Set L) ≤ #(s \ {x} : Set L) + 1 := le_self_add
        rw [hdiff] at hle
        exact hle.trans_lt (by exact_mod_cast Cardinal.natCast_lt_aleph0 (n := n + 1))
      obtain ⟨p, hp⟩ := Cardinal.lt_aleph0.mp hlt
      rw [hp] at hdiff ⊢
      norm_cast at hdiff ⊢
      omega
    rwa [hn] at this
  have h₂ : 1 ≤ Algebra.trdeg L' L := by
    have := ((algebraicIndependent_unique_type_iff (ι := PUnit.{u + 1})
      (x := fun _ ↦ x)).mpr hxL').cardinalMk_le_trdeg
    simpa using this
  have htower : Algebra.trdeg k L' + Algebra.trdeg L' L = n + 1 := by
    rw [trdeg_add_eq, h]
  exact ⟨L', hL', eq_and_eq_of_add_eq htower h₁ h₂⟩

set_option backward.isDefEq.respectTransparency false in
/-- Base change of étale coverings along a tower `k ⊆ L ⊆ K` of fields: if `FEt(X) ≌ FEt(X ⊗ₖ L)`
and `FEt(X ⊗ₖ L) ≌ FEt((X ⊗ₖ L) ⊗_L K)`, then `FEt(X) ≌ FEt(X ⊗ₖ K)`. -/
theorem isEquivalence_pullback_fst_of_isScalarTower {k L K : Type u} [Field k] [Field L]
    [Field K] [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k))
    [h₁ : (ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k L))))).IsEquivalence]
    [h₂ : (ExposeV.FEt.pullback (pullback.fst (pullback.snd s
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom (algebraMap L K))))).IsEquivalence] :
    (ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K))))).IsEquivalence := by
  let ρL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let ρ' := Spec.map (CommRingCat.ofHom (algebraMap L K))
  let ρK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hρ : ρ' ≫ ρL = ρK := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hsq : IsPullback (pullback.fst (pullback.snd s ρL) ρ' ≫ pullback.fst s ρL)
      (pullback.snd _ _) s ρK := by
    rw [← hρ]
    exact (IsPullback.of_hasPullback (pullback.snd s ρL) ρ').paste_horiz
      (IsPullback.of_hasPullback s ρL)
  have : (ExposeV.FEt.pullback
      (pullback.fst (pullback.snd s ρL) ρ' ≫ pullback.fst s ρL)).IsEquivalence :=
    ExposeV.FEt.isEquivalence_pullback_comp _ _
  rw [← hsq.isoPullback_hom_fst] at this
  have : (ExposeV.FEt.pullback (pullback.fst s ρK) ⋙
      ExposeV.FEt.pullback hsq.isoPullback.hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp _ _)
  exact Functor.isEquivalence_of_comp_right _ (ExposeV.FEt.pullback hsq.isoPullback.hom)

/-- The transcendence-degree induction, given the case of the open subsets of the affine line
(`AffineLineOpenInvarianceStatement`): for `X` smooth, quasi-compact, quasi-separated and
connected over an algebraically closed field `k` of characteristic `0`, and `L` an algebraically
closed extension of finite transcendence degree `n`, base change is an equivalence
`FEt(X) ≌ FEt(X ⊗ₖ L)`. -/
theorem isEquivalence_pullback_fst_of_trdeg_eq (hC : AffineLineOpenInvarianceStatement.{u})
    (n : ℕ) : ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
      (s : X ⟶ Spec (.of k)) [QuasiCompact s] [QuasiSeparated s] [Smooth s] [ConnectedSpace X]
      (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L], Algebra.trdeg k L = n →
      (ExposeV.FEt.pullback
        (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k L))))).IsEquivalence := by
  -- a scheme smooth over a field is normal (II.5.3: it is regular)
  have hnormal : ∀ {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [Smooth s],
      ExposeI.IsNormalScheme X := fun s _ x ↦
    ExposeX.isNormalScheme_of_isRegularScheme
      (fun y ↦ ExposeII.isRegularLocalRing_stalk_of_smooth_field _ s y) x
  induction n with
  | zero =>
    intro k _ _ _ X s _ _ _ _ L _ _ _ hL
    exact isEquivalence_pullback_fst_of_trdeg_le_one hC s (hnormal s) L (by rw [hL]; simp)
  | succ n ih =>
    intro k _ _ _ X s _ _ _ _ L _ _ _ hL
    obtain ⟨L', hL', hkL', hL'L⟩ := exists_isAlgClosed_trdeg_eq k L n (by rw [hL]; push_cast; rfl)
    have : CharZero L' := charZero_of_injective_algebraMap (algebraMap k L').injective
    let ρ' := Spec.map (CommRingCat.ofHom (algebraMap k L'))
    have h₁ := ih s L' hkL'
    -- `X ⊗ₖ L'` is smooth, quasi-compact, quasi-separated and connected over `L'`
    have : ConnectedSpace (Spec (.of L')) := inferInstance
    have : ConnectedSpace ↥(pullback s ρ') :=
      connectedSpace_pullback_of_isAlgClosed_of_connectedSpace s ρ'
    have h₂ := isEquivalence_pullback_fst_of_trdeg_le_one hC (pullback.snd s ρ')
      (hnormal (pullback.snd s ρ')) L (hL'L.le)
    exact isEquivalence_pullback_fst_of_isScalarTower (L := L') s

set_option backward.isDefEq.respectTransparency false in
/-- XIII.4.6 for `Y = Spec k'` (X.1.8 without properness) for smooth `X` in characteristic `0`,
given the case of the open subsets of the affine line (`AffineLineOpenInvarianceStatement`):
every smooth, quasi-compact, quasi-separated and connected scheme `X` over an algebraically
closed field `k` of characteristic `0` has the invariance property
(`HasAlgClosedBaseChangeInvariance`). For an étale covering `Y` of `X ⊗ₖ k'`, coming from
`X ⊗ₖ A` with `A ⊆ k'` finitely generated, let `L`
be the algebraic closure in `k'` of the field generated by `A`; it has finite transcendence
degree, so `FEt(X) ≌ FEt(X ⊗ₖ L)` (`isEquivalence_pullback_fst_of_trdeg_eq`), and `Y` comes from
`X`. -/
theorem hasAlgClosedBaseChangeInvariance_of_smooth (hC : AffineLineOpenInvarianceStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    [QuasiCompact s] [QuasiSeparated s] [Smooth s] [ConnectedSpace X] :
    HasAlgClosedBaseChangeInvariance s := by
  intro k' _ _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst s ρ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback s ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace s ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback s ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback s ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback s ρ := ExposeX.geometricPoint _ z
  let F' := ExposeV.FEt.fiber Ω x
  have : PreGaloisCategory.FiberFunctor (ExposeV.FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback π) F']
  refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_, ?_⟩
  · apply Iso.ext
    refine NatTrans.ext (funext fun Y ↦ ?_)
    have hσE : ∀ E : ExposeV.FEt X, σ.hom.app ((ExposeV.FEt.pullback π).obj E) = 𝟙 _ :=
      fun E ↦ congrArg (fun τ : Aut (ExposeV.FEt.pullback π ⋙ F') ↦ τ.hom.app E) hσ
    change σ.hom.app Y = 𝟙 _
    have hYf : IsFinite Y.hom := Y.prop.1
    have hYe : Etale Y.hom := Y.prop.2
    obtain ⟨A, hA, YA, qA, e, hqA, heA, hpb⟩ :=
      ExposeX.exists_fgSubalgebra_isPullback k k' s Y.hom
    -- the algebraic closure `L` in `k'` of the field generated by `A`
    obtain ⟨t, ht⟩ := hA
    let Fld := IntermediateField.adjoin k (t : Set k')
    let L₀ := algebraicClosure Fld k'
    have hL₀ : IsAlgClosed L₀ := IsAlgClosure.isAlgClosed Fld
    let L : IntermediateField k k' := L₀.restrictScalars k
    have : IsAlgClosed L := hL₀
    have : Algebra.EssFiniteType k Fld :=
      IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite t.finite_toSet)
    have : FinTrdeg k L₀ := FinTrdeg.trans k Fld L₀
    have hfin : Algebra.trdeg k L < ℵ₀ := trdeg_lt_aleph0 k L₀
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
    have hequiv := isEquivalence_pullback_fst_of_trdeg_eq hC n s L hn
    -- `A ⊆ L`
    have hmem : ∀ a ∈ A, (a : k') ∈ L := fun a ha ↦ by
      change (a : k') ∈ L₀
      rw [mem_algebraicClosure_iff]
      have : a ∈ Fld := by
        rw [← ht] at ha
        exact (Algebra.adjoin_le (IntermediateField.subset_adjoin k _) :
          Algebra.adjoin k (t : Set k') ≤ Fld.toSubalgebra) ha
      exact isAlgebraic_algebraMap (⟨a, this⟩ : Fld)
    let ιAL : A →ₐ[k] L :=
      { toFun := fun a ↦ ⟨a, hmem a a.2⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    -- the factorization `Spec k' ⟶ Spec L ⟶ Spec A`
    let ρL := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let sA := Spec.map (CommRingCat.ofHom (algebraMap k A))
    let jA : Spec (.of k') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom A.val.toRingHom)
    let jL : Spec (.of k') ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom (algebraMap L k'))
    let jLA : Spec (.of L) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom ιAL.toRingHom)
    have hjLA : jLA ≫ sA = ρL := by
      rw [← Spec.map_comp]
      rfl
    have hjL : jL ≫ ρL = ρ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hj : jL ≫ jLA = jA := by
      rw [← Spec.map_comp]
      rfl
    let ιA : pullback s ρ ⟶ pullback s sA := pullback.map s _ s _ (𝟙 X) jA (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp]
      rfl)
    let ιLA : pullback s ρL ⟶ pullback s sA :=
      pullback.map s _ s _ (𝟙 X) jLA (𝟙 _) (by simp) (by rw [Category.comp_id, hjLA])
    let ιL : pullback s ρ ⟶ pullback s ρL :=
      pullback.map s _ s _ (𝟙 X) jL (𝟙 _) (by simp) (by rw [Category.comp_id, hjL])
    have hι : ιL ≫ ιLA = ιA := by
      apply pullback.hom_ext
      · simp [ιL, ιLA, ιA]
      · simp only [ιL, ιLA, ιA, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [hj]
    have hιL : ιL ≫ pullback.fst s ρL = π := by simp [ιL, π]
    -- `Y` is the inverse image of an étale covering of `X ⊗ₖ L`, which comes from `X`
    let Z : ExposeV.FEt (pullback s sA) := MorphismProperty.Over.mk ⊤ qA ⟨hqA, heA⟩
    let ZL := (ExposeV.FEt.pullback ιLA).obj Z
    let Y₀ := (ExposeV.FEt.pullback (pullback.fst s ρL)).objPreimage ZL
    let ψ₀ : (ExposeV.FEt.pullback (pullback.fst s ρL)).obj Y₀ ≅ ZL :=
      (ExposeV.FEt.pullback _).objObjPreimageIso ZL
    have hpb' : IsPullback e Y.hom qA ιA := hpb
    let φ₀ : Y ≅ (ExposeV.FEt.pullback ιA).obj Z :=
      MorphismProperty.Over.isoMk hpb'.isoPullback hpb'.isoPullback_hom_snd
    let φ : Y ≅ (ExposeV.FEt.pullback π).obj Y₀ :=
      φ₀ ≪≫ (MorphismProperty.Over.pullbackCongr hι.symm).app Z ≪≫
        (MorphismProperty.Over.pullbackComp ιL ιLA).app Z ≪≫
          (ExposeV.FEt.pullback ιL).mapIso ψ₀.symm ≪≫
            ((MorphismProperty.Over.pullbackComp ιL (pullback.fst s ρL)).app Y₀).symm ≪≫
              (MorphismProperty.Over.pullbackCongr hιL).app Y₀
    exact ExposeV.aut_app_eq_id_of_iso σ φ.symm (hσE Y₀)
  · -- surjectivity: connected coverings of `X` stay connected over `k'`
    have hsurj := ExposeX.surjective_map_pullback_fst_of_isAlgClosed s k' Ω x
    rwa [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.Surjective.of_comp_iff' (MulEquiv.bijective _)] at hsurj

end Tower

section Consequences

variable (hC : AffineLineOpenInvarianceStatement.{u}) {k : Type u} [Field k] [IsAlgClosed k]
  [CharZero k]
include hC

/-- XIII.4.6 for `Y = Spec k'` (X.1.8 without properness) for normal `X` of finite type in
characteristic `0`, given the case of the open subsets of the affine line
(`AffineLineOpenInvarianceStatement`): every connected, normal, quasi-compact, quasi-separated
scheme `X` locally of finite type over an algebraically closed field `k` of characteristic `0` has
the invariance property. The smooth finitely generated subalgebras of `k'` are cofinal (generic
smoothness, `Subalgebra.exists_le_fg_smooth`) and their spectra have the invariance property
(`hasAlgClosedBaseChangeInvariance_of_smooth`); `hasAlgClosedBaseChangeInvariance_of_cofinal`
concludes. -/
theorem hasAlgClosedBaseChangeInvariance_of_isNormalScheme {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [QuasiCompact s] [QuasiSeparated s] [LocallyOfFiniteType s]
    [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X) : HasAlgClosedBaseChangeInvariance s := by
  refine hasAlgClosedBaseChangeInvariance_of_cofinal s hX fun k' _ _ _ A hA ↦ ?_
  obtain ⟨B, hAB, hB, hsm⟩ := Subalgebra.exists_le_fg_smooth A hA
  have hB' : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  have : ConnectedSpace (Spec (.of B)) := inferInstance
  exact ⟨B, hAB, hB, hB', hasAlgClosedBaseChangeInvariance_of_smooth hC _⟩

/-- XIII.4.6 in characteristic `0` for `X` normal and `Y` smooth, given the case of the open
subsets of the affine line (`AffineLineOpenInvarianceStatement`): let `X` be connected, normal and
locally of finite type and `Y` smooth, quasi-compact, quasi-separated and connected over an
algebraically closed field `k` of characteristic `0`. Then `π₁(X ×ₖ Y) → π₁(X) × π₁(Y)` is
bijective at every geometric
point (the main lemma with `hasAlgClosedBaseChangeInvariance_of_smooth`). -/
theorem bijective_map_prod_of_isNormalScheme_of_smooth {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [ConnectedSpace X]
    (hX : ExposeI.IsNormalScheme X) [Smooth sY] [QuasiCompact sY] [QuasiSeparated sY]
    [ConnectedSpace Y] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : Spec (.of Ω) ⟶ pullback sX sY) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst sX sY) c).prod
      (FundamentalGroup.map (pullback.snd sX sY) c)) :=
  bijective_map_prod_of_isNormalScheme_of_invariance sX sY hX
    (hasAlgClosedBaseChangeInvariance_of_smooth hC sY) Ω c

/-- XIII.4.6 in characteristic `0` for `X` and `Y` normal, given the case of the open subsets of
the affine line (`AffineLineOpenInvarianceStatement`): let `X` be connected, normal and locally of
finite type and `Y` connected, normal, quasi-compact, quasi-separated and locally of finite type
over an algebraically closed field `k` of characteristic `0`. Then `π₁(X ×ₖ Y) → π₁(X) × π₁(Y)`
is bijective at every geometric point. (`X ×ₖ Y` is normal, `isNormalScheme_pullback`, and `Y` has
the invariance property, `hasAlgClosedBaseChangeInvariance_of_isNormalScheme`; the main lemma
`bijective_map_prod_of_isNormalScheme_pullback_of_invariance` concludes.) -/
theorem bijective_map_prod_of_isNormalScheme_of_isNormalScheme {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [ConnectedSpace X]
    (hX : ExposeI.IsNormalScheme X) [LocallyOfFiniteType sY] [QuasiCompact sY]
    [QuasiSeparated sY] [ConnectedSpace Y] (hY : ExposeI.IsNormalScheme Y) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (c : Spec (.of Ω) ⟶ pullback sX sY) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst sX sY) c).prod
      (FundamentalGroup.map (pullback.snd sX sY) c)) :=
  bijective_map_prod_of_isNormalScheme_pullback_of_invariance sX sY hX
    (isNormalScheme_pullback sX sY hX hY)
    (hasAlgClosedBaseChangeInvariance_of_isNormalScheme hC sY hY) Ω c

end Consequences

end SGA.SGA1.ExposeXIII
