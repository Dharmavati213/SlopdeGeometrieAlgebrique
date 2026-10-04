/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeXIII.KunnethField
import SGA.SGA1.ExposeXIII.KunnethNormal

/-!
# SGA 1, XIII.4.6: the Künneth formula with a normal factor, given invariance for the other

The main lemma of the resolution-free route to XIII.4.6 in characteristic `0`. Let `k` be
algebraically closed, `X` connected, normal and locally of finite type over `k`, and `T` smooth,
quasi-compact, quasi-separated and connected over `k`, with the invariance property
(`HasAlgClosedBaseChangeInvariance`, X.1.8 for `T`). Then
`π₁(X ×ₖ T) → π₁(X) × π₁(T)` is bijective (`bijective_map_prod_of_isNormalScheme_of_invariance`).
No characteristic assumption is made; in characteristic `0` the invariance is expected for every
quasi-compact quasi-separated `T` (`InvarianceCharZeroStatement`).

The proof uses the generic fibre `T_K = T ⊗ₖ K` of `pr₁ : X ×ₖ T → X` (`K` the function field of
`X`, `ι : T_K → X ×ₖ T`), a rational point `t₀` of `T`, and its constant section
`t₀ ⊗ₖ K : Spec K → T_K`:

* `π₁(T_K) → π₁(X ×ₖ T)` is surjective (`isConnected_pullback_of_isPullback_genericPoint`):
  `X ×ₖ T` is normal (smooth over `X`, II.3.1), so an étale covering `W` of it is normal (I.9.10),
  hence irreducible when connected (`irreducibleSpace_left_of_isNormalScheme`), and `W_K ⊆ W` is a
  subspace containing the generic point of `W`;
* an element `σ` of `π₁(X ×ₖ T)` killed by both projections lifts to `σ' ∈ π₁(T_K)` killed by
  `π₁(T_K) → π₁(T)`; by the Künneth formula with a field factor
  (`ker_map_fst_le_range_map_constSection`) `σ'` comes from `b ∈ π₁(Spec K)` through
  `t₀ ⊗ₖ K`, and `b` acts trivially on the coverings coming from `X` (as `σ` does);
* `ι ∘ (t₀ ⊗ₖ K)` is `Spec K → X → X ×ₖ T`, `x ↦ (x, t₀)`, so every étale covering of
  `X ×ₖ T`, pulled back along it, comes from `X`, and `σ` is trivial.

In SGA (XIII.4.6) the corresponding step is the exact homotopy sequence XIII.4.2 for `pr₂`, which
rests on resolution of singularities; here normality of `X` and the invariance for `T` replace it.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

section Formal

variable {T S S' P : Scheme.{u}}

/-- An automorphism of a functor on `FEt(T)` which is the identity on `f₁^* f₂^* E` is the
identity on `g₁^* g₂^* E` when `f₁ ≫ f₂ = g₁ ≫ g₂`. -/
lemma hom_app_pullback_pullback_eq_id {D : Type*} [Category D] {F : ExposeV.FEt T ⥤ D}
    (σ : F ≅ F) (f₁ : T ⟶ S) (f₂ : S ⟶ P) (g₁ : T ⟶ S') (g₂ : S' ⟶ P) (w : f₁ ≫ f₂ = g₁ ≫ g₂)
    (E : ExposeV.FEt P)
    (h : σ.hom.app ((ExposeV.FEt.pullback f₁).obj ((ExposeV.FEt.pullback f₂).obj E)) = 𝟙 _) :
    σ.hom.app ((ExposeV.FEt.pullback g₁).obj ((ExposeV.FEt.pullback g₂).obj E)) = 𝟙 _ :=
  ExposeV.aut_app_eq_id_of_iso σ
    (((MorphismProperty.Over.pullbackComp f₁ f₂).app E).symm ≪≫
      (MorphismProperty.Over.pullbackCongr w).app E ≪≫
        (MorphismProperty.Over.pullbackComp g₁ g₂).app E) h

/-- An automorphism of a functor on `FEt(T)` which is the identity on `f₁^* f₂^* E` is the
identity on `g^* E` when `f₁ ≫ f₂ = g`. -/
lemma hom_app_pullback_eq_id_of_comp {D : Type*} [Category D] {F : ExposeV.FEt T ⥤ D}
    (σ : F ≅ F) (f₁ : T ⟶ S) (f₂ : S ⟶ P) (g : T ⟶ P) (w : f₁ ≫ f₂ = g) (E : ExposeV.FEt P)
    (h : σ.hom.app ((ExposeV.FEt.pullback f₁).obj ((ExposeV.FEt.pullback f₂).obj E)) = 𝟙 _) :
    σ.hom.app ((ExposeV.FEt.pullback g).obj E) = 𝟙 _ :=
  ExposeV.aut_app_eq_id_of_iso σ
    (((MorphismProperty.Over.pullbackComp f₁ f₂).app E).symm ≪≫
      (MorphismProperty.Over.pullbackCongr w).app E) h

/-- An automorphism of a functor on `FEt(T)` which is the identity on `f₁^* f₂^* E` is the
identity on `E` when `f₁ ≫ f₂ = 𝟙`. -/
lemma hom_app_eq_id_of_comp_eq_id {D : Type*} [Category D] {F : ExposeV.FEt T ⥤ D}
    (σ : F ≅ F) (f₁ : T ⟶ S) (f₂ : S ⟶ T) (w : f₁ ≫ f₂ = 𝟙 T) (E : ExposeV.FEt T)
    (h : σ.hom.app ((ExposeV.FEt.pullback f₁).obj ((ExposeV.FEt.pullback f₂).obj E)) = 𝟙 _) :
    σ.hom.app E = 𝟙 _ :=
  ExposeV.aut_app_eq_id_of_iso σ
    (((MorphismProperty.Over.pullbackComp f₁ f₂).app E).symm ≪≫
      (MorphismProperty.Over.pullbackCongr w).app E ≪≫ (ExposeV.FEt.pullbackId T).app E) h

/-- `π₁(p)(σ)` acts trivially on the fibre of `Z` iff `σ` acts trivially on the fibre of
`p^* Z`. The direction `←` is `SGA.SGA1.ExposeX.map_hom_app_eq_id`; the direction `→`, for one
object, generalizes `ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id` (which assumes
`π₁(p)(σ) = 1`). -/
lemma map_hom_app_eq_id_iff {Ω : Type u} [Field Ω] (p : T ⟶ P)
    (t : Spec (.of Ω) ⟶ T) (σ : ExposeV.etaleFundamentalGroup Ω t) (Z : ExposeV.FEt P) :
    (ExposeV.etaleFundamentalGroup.map Ω p t σ).hom.app Z = 𝟙 _ ↔
      σ.hom.app ((ExposeV.FEt.pullback p).obj Z) = 𝟙 _ := by
  refine ⟨fun h ↦ ?_, ExposeX.map_hom_app_eq_id p t σ Z⟩
  simp only [ExposeV.etaleFundamentalGroup.map, ExposeV.autMap_hom_app] at h
  have := congrArg (fun k ↦ (ExposeV.FEt.pullbackFiberIso Ω p t).hom.app Z ≫ k ≫
    (ExposeV.FEt.pullbackFiberIso Ω p t).inv.app Z) h
  simpa using this

end Formal

section GenericFibre

/-- Let `p : Z ⟶ X` be surjective with `X` irreducible, and `ι : Y ⟶ Z` the base change of a
preimmersion `g : Spec K ⟶ X` with image the generic point of `X` (for instance
`X.fromSpecStalk (genericPoint X)`). For an étale covering `W` of `Z` which is irreducible and
connected, `ι^* W` is connected: it is a subspace of `W` containing the generic point of `W`. -/
theorem isConnected_pullback_of_isPullback_genericPoint {X Z Y : Scheme.{u}} [IrreducibleSpace X]
    [ConnectedSpace Z] (p : Z ⟶ X) [Surjective p] {K : Type u} [Field K]
    {g : Spec (.of K) ⟶ X} [IsPreimmersion g] (hg : ∀ s, g s = genericPoint X)
    {ι : Y ⟶ Z} {h : Y ⟶ Spec (.of K)} (hpb : IsPullback ι h p g) (W : ExposeV.FEt Z)
    [IsConnected W] [IrreducibleSpace W.left] :
    IsConnected ((ExposeV.FEt.pullback ι).obj W) := by
  let q : W.left ⟶ Z := W.hom
  have hWf : IsFinite q := W.prop.1
  have hWe : Etale q := W.prop.2
  let ξ := genericPoint W.left
  -- `W ⟶ Z` is surjective: its range is open, closed and nonempty
  have hsurj : Function.Surjective q := by
    have hcl : IsClopen (Set.range q) :=
      ⟨q.isClosedMap.isClosed_range, q.isOpenMap.isOpen_range⟩
    exact Set.range_eq_univ.mp (hcl.eq_univ ⟨_, ξ, rfl⟩)
  have hsurj' : Function.Surjective (q ≫ p) := fun x ↦ by
    obtain ⟨z, rfl⟩ := p.surjective x
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨w, rfl⟩
  -- the generic point of `W` lies over the generic point of `X`
  have hξ : p (q ξ) = genericPoint X := by
    have h1 := (genericPoint_spec W.left).image (q ≫ p).continuous
    have : closure ((q ≫ p) '' Set.univ) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj', closure_univ]
    rw [this] at h1
    exact h1.eq (genericPoint_spec X)
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := g) (q ξ) s
    (hξ.trans (hg s).symm)
  have ht : ι (hpb.isoPullback.inv y₀) = q ξ := by
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hy₀]
  obtain ⟨ζ, hζ, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom) (g := ι) ξ
    (hpb.isoPullback.inv y₀) ht.symm
  -- `ι` and its base change `W_K ⟶ W` are preimmersions, hence embeddings
  have : IsPreimmersion ι := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : IsPreimmersion (pullback.fst W.hom ι) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback W.hom ι).flip ‹_›
  have hemb := (pullback.fst W.hom ι).isEmbedding
  -- `ζ` is a generic point of `W_K`
  have hgen : IsGenericPoint ζ (Set.univ : Set ((ExposeV.FEt.pullback ι).obj W).left) := by
    refine isGenericPoint_iff_specializes.mpr fun z ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [← hemb.isInducing.specializes_iff, hζ]
    exact (genericPoint_spec W.left).specializes (Set.mem_univ _)
  have : IrreducibleSpace ((ExposeV.FEt.pullback ι).obj W).left :=
    (irreducibleSpace_def _).mpr hgen.isIrreducible
  exact ExposeV.FEt.isConnected_of_connectedSpace _

/-- The underlying scheme of a connected étale covering `W` of a locally noetherian normal
scheme is irreducible: it is normal (I.9.10, `ExposeI.isNormalScheme_of_etale`) and connected,
hence irreducible (`ExposeI.irreducibleSpace_of_isDomain_stalk`; compare I.9.11,
`ExposeI.isNormalScheme_and_irreducibleSpace_of_dominant_of_formallyUnramified`). -/
lemma irreducibleSpace_left_of_isNormalScheme {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hZ : ExposeI.IsNormalScheme Z) (W : ExposeV.FEt Z) [IsConnected W] :
    IrreducibleSpace W.left := by
  let q : W.left ⟶ Z := W.hom
  have hWf : IsFinite q := W.prop.1
  have hWe : Etale q := W.prop.2
  have : ConnectedSpace W.left := ExposeV.FEt.connectedSpace_of_isConnected W
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian q
  have hW := ExposeI.isNormalScheme_of_etale q hZ
  exact ExposeI.irreducibleSpace_of_isDomain_stalk fun x ↦ (hW x).1

end GenericFibre

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sT : T ⟶ Spec (.of k))

/-- Transport of the bijectivity of `π₁(Z) → π₁(X) × π₁(Y)` from one geometric point of `Z` to
another (`bijective_prod_autMap_of_iso`). -/
lemma bijective_map_prod_of_bijective_map_prod {Z Y₁ Y₂ : Scheme.{u}} [ConnectedSpace Z]
    (f₁ : Z ⟶ Y₁) (f₂ : Z ⟶ Y₂) {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂]
    [IsSepClosed Ω₂] (c₁ : Spec (.of Ω₁) ⟶ Z) (c₂ : Spec (.of Ω₂) ⟶ Z)
    (h : Function.Bijective ((FundamentalGroup.map f₁ c₁).prod (FundamentalGroup.map f₂ c₁))) :
    Function.Bijective ((FundamentalGroup.map f₁ c₂).prod (FundamentalGroup.map f₂ c₂)) := by
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor (ExposeV.FEt.fiber Ω₁ c₁)
    (ExposeV.FEt.fiber Ω₂ c₂)
  exact bijective_prod_autMap_of_iso _ _ φ _ _ _ _ h

set_option backward.isDefEq.respectTransparency false in
/-- The main lemma, in terms of the generic fibre: let `T` be quasi-compact, quasi-separated and
connected over the algebraically closed field `k` with the invariance property and a rational
point, `X` irreducible over `k`, and `g : Spec K ⟶ X` a preimmersion onto the generic point of `X`
(over `k`). If every connected étale covering of `X ×ₖ T` is irreducible, then
`π₁(X ×ₖ T) → π₁(X) × π₁(T)` is bijective (any characteristic; the full `π₁`, see
`bijective_map_prod_of_isNormalScheme_of_invariance`). -/
theorem bijective_map_prod_of_genericPoint_of_invariance [IrreducibleSpace X] [QuasiCompact sT]
    [QuasiSeparated sT] [ConnectedSpace T] (hinv : HasAlgClosedBaseChangeInvariance sT)
    (t₀ : Spec (.of k) ⟶ T) (ht₀ : t₀ ≫ sT = 𝟙 _)
    (hW : ∀ W : ExposeV.FEt (pullback sX sT), IsConnected W → IrreducibleSpace W.left)
    (K : Type u) [Field K] [Algebra k K] (g : Spec (.of K) ⟶ X) [IsPreimmersion g]
    (hg : ∀ s, g s = genericPoint X) (hρ : Spec.map (CommRingCat.ofHom (algebraMap k K)) = g ≫ sX)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (c : Spec (.of Ω) ⟶ pullback sX sT) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst sX sT) c).prod
      (FundamentalGroup.map (pullback.snd sX sT) c)) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pr₁ := pullback.fst sX sT
  let pr₂ := pullback.snd sX sT
  -- `X ×ₖ T` is connected and `pr₁` is surjective
  have : ConnectedSpace ↥(pullback sX sT) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sX sT
  have : Surjective sT := ExposeX.surjective_of_nonempty sT
  have : Surjective pr₁ := MorphismProperty.pullback_fst _ _ ‹_›
  let pT := pullback.fst sT ρ
  let h := pullback.snd sT ρ
  -- the generic fibre `ι : T_K ⟶ X ×ₖ T` of `pr₁`
  let ι : pullback sT ρ ⟶ pullback sX sT := pullback.lift (h ≫ g) pT (by
    rw [Category.assoc, ← hρ, ← pullback.condition])
  have hι₁ : ι ≫ pr₁ = h ≫ g := pullback.lift_fst _ _ _
  have hι₂ : ι ≫ pr₂ = pT := pullback.lift_snd _ _ _
  have hpb : IsPullback ι h pr₁ g := IsPullback.of_right
    (by rw [hι₂, ← hρ]; exact IsPullback.of_hasPullback sT ρ) hι₁
    (IsPullback.of_hasPullback sX sT).flip
  -- the constant section and the fibre inclusion `x ↦ (x, t₀)`
  let j := ExposeX.fibreInclusion sX sT t₀ ht₀
  let t₀K := constSection t₀ ht₀ K
  have hjι : t₀K ≫ ι = g ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, hι₁, constSection_snd_assoc, Category.assoc,
        ExposeX.fibreInclusion_fst, Category.comp_id]
    · rw [Category.assoc, hι₂, constSection_fst, Category.assoc,
        ExposeX.fibreInclusion_snd, hρ, Category.assoc]
  -- base points
  have : ConnectedSpace (Spec (.of K)) := inferInstance
  have : ConnectedSpace ↥(pullback sT ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sT ρ
  let Ω' := AlgebraicClosure K
  let ω : Spec (.of Ω') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω'))
  let c' := ω ≫ t₀K
  -- `π₁(T_K) → π₁(X ×ₖ T)` is surjective
  have hι : Function.Surjective (FundamentalGroup.map ι c') :=
    ExposeV.autMap_surjective _ _ fun W hW' ↦
      have := hW W hW'
      isConnected_pullback_of_isPullback_genericPoint pr₁ hg hpb W
  -- injectivity at `c' ≫ ι`
  have hinj : Function.Injective ((FundamentalGroup.map pr₁ (c' ≫ ι)).prod
      (FundamentalGroup.map pr₂ (c' ≫ ι))) := by
    refine (injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_
    have hσ₁ : FundamentalGroup.map pr₁ (c' ≫ ι) σ = 1 := congrArg Prod.fst hσ
    have hσ₂ : FundamentalGroup.map pr₂ (c' ≫ ι) σ = 1 := congrArg Prod.snd hσ
    obtain ⟨σ', rfl⟩ := hι σ
    -- `σ'` is trivial on the coverings coming from `T` and from `X`
    have h₂ : ∀ E : ExposeV.FEt T, σ'.hom.app ((ExposeV.FEt.pullback pT).obj E) = 𝟙 _ :=
      fun E ↦ hom_app_pullback_eq_id_of_comp σ' ι pr₂ pT hι₂ E
        ((map_hom_app_eq_id_iff ι c' σ' _).mp
          (ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω' pr₂ _ _ hσ₂ E))
    have h₁ : ∀ E : ExposeV.FEt X,
        σ'.hom.app ((ExposeV.FEt.pullback h).obj ((ExposeV.FEt.pullback g).obj E)) = 𝟙 _ :=
      fun E ↦ hom_app_pullback_pullback_eq_id σ' ι pr₁ h g hpb.w E
        ((map_hom_app_eq_id_iff ι c' σ' _).mp
          (ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω' pr₁ _ _ hσ₁ E))
    -- `σ'` comes from `π₁(Spec K)` through the constant section
    have hpT : FundamentalGroup.map pT c' σ' = 1 :=
      ExposeX.map_eq_one_of_forall_hom_app_eq_id _ _ σ' h₂
    obtain ⟨b, hb⟩ := ker_map_fst_le_range_map_constSection hinv t₀ ht₀ K Ω' ω
      (MonoidHom.mem_ker.mpr hpT)
    -- `b` acts trivially on the coverings coming from `X`
    have hb₁ : ∀ E : ExposeV.FEt X, b.hom.app ((ExposeV.FEt.pullback g).obj E) = 𝟙 _ := by
      intro E
      have h₁' := h₁ E
      rw [← hb] at h₁'
      exact hom_app_eq_id_of_comp_eq_id b t₀K h (constSection_snd t₀ ht₀ K) _
        ((map_hom_app_eq_id_iff t₀K ω b _).mp h₁')
    -- hence `σ` acts trivially on every covering of `X ×ₖ T`
    apply Iso.ext
    refine NatTrans.ext (funext fun W ↦ ?_)
    change _ = 𝟙 _
    apply ExposeX.map_hom_app_eq_id
    rw [← hb]
    apply ExposeX.map_hom_app_eq_id
    exact hom_app_pullback_pullback_eq_id b g j t₀K ι hjι.symm W (hb₁ _)
  exact bijective_map_prod_of_bijective_map_prod pr₁ pr₂ (c' ≫ ι) c
    ⟨hinj, surjective_map_prod_of_isAlgClosed sX sT Ω' (c' ≫ ι)⟩

/-- XIII.4.6 for `X` normal and `T` with the invariance property, assuming `X ×ₖ T` normal (the
main lemma of the resolution-free route; any characteristic): let `k` be algebraically closed,
`X` connected, normal and locally of finite type over `k`, and `T` quasi-compact,
quasi-separated, connected and locally of finite type over `k` with the invariance property
(`HasAlgClosedBaseChangeInvariance`, X.1.8 for `T`), such that `X ×ₖ T` is normal. Then for every
geometric point `c` of `X ×ₖ T`, `π₁(X ×ₖ T, c) → π₁(X, c) × π₁(T, c)` is bijective.

Deviations from SGA: as for `bijective_map_prod_of_isNormalScheme_of_invariance`, with the
smoothness of `T` replaced by the normality of `X ×ₖ T` (which holds when `T` is smooth, II.3.1,
or, in characteristic `0`, when `T` is normal of finite type, `isNormalScheme_pullback`). -/
theorem bijective_map_prod_of_isNormalScheme_pullback_of_invariance [LocallyOfFiniteType sX]
    [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X) [LocallyOfFiniteType sT] [QuasiCompact sT]
    [QuasiSeparated sT] [ConnectedSpace T] (hZ : ExposeI.IsNormalScheme (pullback sX sT))
    (hinv : HasAlgClosedBaseChangeInvariance sT)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (c : Spec (.of Ω) ⟶ pullback sX sT) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst sX sT) c).prod
      (FundamentalGroup.map (pullback.snd sX sT) c)) := by
  -- `X` is integral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsIntegral X := ExposeX.isIntegral_of_isNormalScheme hX
  -- a rational point of `T`
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨t₀, ht₀⟩ := ExposeX.exists_comp_eq_id sT
  -- `X ×ₖ T` is locally noetherian
  have : IsLocallyNoetherian (pullback sX sT) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst sX sT)
  -- the generic point of `X`
  let g := X.fromSpecStalk (genericPoint X)
  let _ : Algebra k X.functionField := (Spec.preimage (g ≫ sX)).hom.toAlgebra
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) = g ≫ sX :=
    Spec.map_preimage _
  have : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have hg : ∀ s, g s = genericPoint X := fun s ↦ by
    rw [Subsingleton.elim s (IsLocalRing.closedPoint _)]
    exact Scheme.fromSpecStalk_closedPoint
  exact bijective_map_prod_of_genericPoint_of_invariance sX sT hinv t₀ ht₀
    (fun W _ ↦ irreducibleSpace_left_of_isNormalScheme hZ W) X.functionField g hg hρ Ω c

/-- XIII.4.6 for `X` normal and `T` smooth with the invariance property (the main lemma of the
resolution-free route; any characteristic): let `k` be algebraically closed, `X` connected, normal
and locally of finite type over `k`, and `T` smooth, quasi-compact, quasi-separated and connected
over `k` with the invariance property (`HasAlgClosedBaseChangeInvariance`, X.1.8 for `T`). Then
for every geometric point `c` of `X ×ₖ T`, `π₁(X ×ₖ T, c) → π₁(X, c) × π₁(T, c)` is bijective.

Deviations from SGA:
* `k` is algebraically closed (SGA: separably closed);
* the conclusion is about the full `π₁` instead of `π₁^{p'}` (the same in characteristic `0`; in
  characteristic `p` it is the invariance hypothesis on `T` that makes this possible);
* SGA's desingularization hypotheses are replaced by the normality of `X`, the smoothness of `T`
  and the invariance property for `T` (in characteristic `0` this is
  `InvarianceCharZeroStatement` for `T`; it holds for `T` proper by X.1.8, and for smooth `T`
  given `AffineLineOpenInvarianceStatement`, `hasAlgClosedBaseChangeInvariance_of_smooth`). -/
theorem bijective_map_prod_of_isNormalScheme_of_invariance [LocallyOfFiniteType sX]
    [ConnectedSpace X] (hX : ExposeI.IsNormalScheme X) [Smooth sT] [QuasiCompact sT]
    [QuasiSeparated sT] [ConnectedSpace T] (hinv : HasAlgClosedBaseChangeInvariance sT)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (c : Spec (.of Ω) ⟶ pullback sX sT) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst sX sT) c).prod
      (FundamentalGroup.map (pullback.snd sX sT) c)) :=
  bijective_map_prod_of_isNormalScheme_pullback_of_invariance sX sT hX
    (isNormalScheme_of_smooth_of_isNormalScheme (pullback.fst sX sT) hX) hinv Ω c

end Main

end SGA.SGA1.ExposeXIII
