/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.FiniteEtaleLimit
import SGA.SGA1.ExposeIX.FundamentalGroupDescent
import SGA.SGA1.ExposeX.ConstantFamily
import SGA.SGA1.ExposeX.Product
import SGA.SGA1.ExposeXIII.KunnethSurjective

/-!
# SGA 1, XIII.4.6: invariance under algebraically closed base change and a field factor

The Künneth formula XIII.4.6 contains, for `Y = Spec k'` with `k'` an algebraically closed
extension of `k`, the invariance of `π₁` under algebraically closed base change: X.1.8 without
the properness of `X`. We record:

* `HasAlgClosedBaseChangeInvariance sT`: for every algebraically closed extension `k'` of `k`,
  `T' ↦ T' ⊗ₖ k'` is an equivalence `FEt(T) ≌ FEt(T ⊗ₖ k')` (X.1.8 for `T`). For `T` proper and
  connected over an algebraically closed `k` this is X.1.8,
  `SGA.SGA1.ExposeX.baseChangeAlgClosedStatement` (`hasAlgClosedBaseChangeInvariance_of_isProper`);
* `InvarianceCharZeroStatement` (statement only): the invariance holds for every quasi-compact
  quasi-separated connected scheme over an algebraically closed field of characteristic `0`.
  Proved here: `invarianceCharZeroStatement_of_kunnethCharZeroStatement`, it follows from XIII.4.6
  (`KunnethCharZeroStatement`), taking `Y = Spec k'`;
* `bijective_map_prod_field_of_invariance`, the Künneth formula with a field factor: if `T` is
  quasi-compact, quasi-separated and connected over an algebraically closed `k` and has the
  invariance property, then `π₁(T ⊗ₖ K) → π₁(T) × π₁(Spec K)` is an isomorphism for every field
  `K ⊇ k` (and `π₁(Spec K)` is the absolute Galois group of `K`). This is IX.6.1
  (`SGA.SGA1.ExposeIX.exactSequence_of_quasiSeparatedSpace`) for `T ⊗ₖ K → Spec K`, whose
  geometric fibre is `T ⊗ₖ K̄`, together with the group theory of X.1.7
  (`SGA.SGA1.ExposeX.bijective_prod_of_bijective_comp`).

Whether the product map is bijective does not depend on the fibre functor
(`bijective_prod_autMap_of_iso`).
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

section Transfer

variable {C C₁ C₂ : Type*} [Category* C] [Category* C₁] [Category* C₂]

/-- The bijectivity of `(π₁(H₁), π₁(H₂)) : Aut F → Aut F₁ × Aut F₂` does not depend on the fibre
functor `F`: conjugation by an isomorphism `F ≅ G` intertwines the two product maps. -/
theorem bijective_prod_autMap_of_iso (H₁ : C₁ ⥤ C) (H₂ : C₂ ⥤ C) {F G : C ⥤ FintypeCat.{w}}
    (φ : F ≅ G) {F₁ G₁ : C₁ ⥤ FintypeCat.{w}} {F₂ G₂ : C₂ ⥤ FintypeCat.{w}}
    (e₁ : H₁ ⋙ F ≅ F₁) (e₂ : H₂ ⋙ F ≅ F₂) (e₁' : H₁ ⋙ G ≅ G₁) (e₂' : H₂ ⋙ G ≅ G₂)
    (h : Function.Bijective ((ExposeV.autMap H₁ e₁).prod (ExposeV.autMap H₂ e₂))) :
    Function.Bijective ((ExposeV.autMap H₁ e₁').prod (ExposeV.autMap H₂ e₂')) := by
  let β₁ := (e₁.symm ≪≫ Functor.isoWhiskerLeft H₁ φ ≪≫ e₁').conjAut
  let β₂ := (e₂.symm ≪≫ Functor.isoWhiskerLeft H₂ φ ≪≫ e₂').conjAut
  have key : ⇑((ExposeV.autMap H₁ e₁').prod (ExposeV.autMap H₂ e₂')) =
      Prod.map β₁ β₂ ∘ ((ExposeV.autMap H₁ e₁).prod (ExposeV.autMap H₂ e₂)) ∘ φ.conjAut.symm := by
    funext τ
    obtain ⟨σ, rfl⟩ := φ.conjAut.surjective τ
    simp only [Function.comp_apply, MulEquiv.symm_apply_apply, MonoidHom.prod_apply,
      Prod.map_apply]
    exact Prod.ext (ExposeX.autMap_conjAut H₁ e₁ e₁' φ σ) (ExposeX.autMap_conjAut H₂ e₂ e₂' φ σ)
  rw [key]
  exact (β₁.bijective.prodMap β₂.bijective).comp (h.comp φ.conjAut.symm.bijective)

/-- `π₁(H)` for the identity isomorphism is `ExposeIX.autMap` (`ExposeIX.autMap_eq_conjAut_comp`
for `e = Iso.refl _`). -/
lemma autMap_refl (H : C₁ ⥤ C) (F : C ⥤ FintypeCat.{w}) :
    ExposeV.autMap H (Iso.refl (H ⋙ F)) = ExposeIX.autMap H F := by
  rw [ExposeIX.autMap_eq_conjAut_comp]
  ext σ : 1
  apply Iso.ext
  rfl

end Transfer

section Invariance

variable {k : Type u} [Field k] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))

/-- X.1.8 for `T`: the étale coverings of `T` are invariant under algebraically closed base
change, i.e. for every algebraically closed extension `k'` of `k`, `T' ↦ T' ⊗ₖ k'` is an
equivalence `FEt(T) ≌ FEt(T ⊗ₖ k')` (equivalently, by V.6.10, `π₁(T ⊗ₖ k') → π₁(T)` is an
isomorphism). -/
def HasAlgClosedBaseChangeInvariance : Prop :=
  ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
    (ExposeV.FEt.pullback
      (pullback.fst sT (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence

/-- X.1.8 (`ExposeX.baseChangeAlgClosedStatement`): a proper connected scheme over an
algebraically closed field has the invariance property. -/
theorem hasAlgClosedBaseChangeInvariance_of_isProper [IsAlgClosed k] [IsProper sT]
    [ConnectedSpace T] : HasAlgClosedBaseChangeInvariance sT :=
  fun k' _ _ _ ↦ ExposeX.baseChangeAlgClosedStatement k k' sT

variable {sT}

/-- The invariance property, for any pullback square over a geometric point
`Spec k' ⟶ Spec k` with `k'` algebraically closed. -/
theorem HasAlgClosedBaseChangeInvariance.isEquivalence_of_isPullback
    (hinv : HasAlgClosedBaseChangeInvariance sT) {k' : Type u} [Field k'] [IsAlgClosed k']
    (ι : Spec (.of k') ⟶ Spec (.of k)) {P : Scheme.{u}} {fst : P ⟶ T}
    {snd : P ⟶ Spec (.of k')} (h : IsPullback fst snd sT ι) :
    (ExposeV.FEt.pullback fst).IsEquivalence := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective ι
  let : Algebra k k' := φ.hom.toAlgebra
  have : (ExposeV.FEt.pullback (pullback.fst sT (Spec.map φ))).IsEquivalence := hinv k'
  rw [← h.isoPullback_hom_fst]
  exact ExposeV.FEt.isEquivalence_pullback_comp _ _

/-- XIII.4.6, the case `Y = Spec k'` (`k'` algebraically closed), in characteristic `0`
(statement only): X.1.8 without properness. For `X` quasi-compact, quasi-separated and connected
over an algebraically closed field `k` of characteristic `0`, the étale coverings of `X` are
invariant under algebraically closed base change. It follows from XIII.4.6
(`invarianceCharZeroStatement_of_kunnethCharZeroStatement`). It fails in characteristic `p > 0`
(Artin–Schreier coverings of `𝔸¹`, X.1.10). -/
def InvarianceCharZeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] ⦃X : Scheme.{u}⦄
    (s : X ⟶ Spec (.of k)) [QuasiCompact s] [QuasiSeparated s] [ConnectedSpace X],
    HasAlgClosedBaseChangeInvariance s

set_option backward.isDefEq.respectTransparency false in
/-- XIII.4.6 implies its case `Y = Spec k'`: the invariance of `π₁` under algebraically closed
base change in characteristic `0` (`π₁(Spec k')` is trivial). -/
theorem invarianceCharZeroStatement_of_kunnethCharZeroStatement
    (h : KunnethCharZeroStatement.{u}) : InvarianceCharZeroStatement.{u} := by
  intro k _ _ _ X s _ _ _ k' _ _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst s ρ
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback s ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace s ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback s ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback s ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback s ρ := ExposeX.geometricPoint _ z
  have hK := h k s ρ Ω x
  -- `π₁(Spec k') = 1`, so `π₁(X ⊗ₖ k') → π₁(X)` is bijective
  have hone : ∀ σ, FundamentalGroup.map (pullback.snd s ρ) x σ = 1 := fun σ ↦
    ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω k' _ _
  have hbij : Function.Bijective (FundamentalGroup.map π x) := by
    refine ⟨fun σ τ hστ ↦ hK.1 (Prod.ext hστ ((hone σ).trans (hone τ).symm)), fun a ↦ ?_⟩
    obtain ⟨σ, hσ⟩ := hK.2 (a, 1)
    exact ⟨σ, congrArg Prod.fst hσ⟩
  let F' := ExposeV.FEt.fiber Ω x
  have : FiberFunctor (ExposeV.FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback π) F']
  rwa [FundamentalGroup.map, ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp,
    MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.Bijective.of_comp_iff' (MulEquiv.bijective _)] at hbij

end Invariance

section Field

variable {k : Type u} [Field k] [IsAlgClosed k] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))

set_option backward.isDefEq.respectTransparency false in
/-- XIII.4.6 for `Y = Spec K` (`K` any field extension of `k`), assuming invariance for `T`
(`HasAlgClosedBaseChangeInvariance`, X.1.8 for `T`; no characteristic assumption). Let `T` be
quasi-compact, quasi-separated and connected over an algebraically closed field `k`. Then for
every field `K ⊇ k` and every geometric point `c` of `T ⊗ₖ K`,
`π₁(T ⊗ₖ K, c) → π₁(T, c) × π₁(Spec K, c)` is an isomorphism.

Deviations from SGA: `k` is algebraically closed (SGA: separably closed); the conclusion is about
the full `π₁` instead of `π₁^{p'}` (the same in characteristic `0`; in characteristic `p` it is
the invariance hypothesis on `T` that makes this possible); SGA's desingularization hypotheses are
replaced by the invariance property for `T`.

By IX.6.1 for `T ⊗ₖ K → Spec K`, the sequence `1 → π₁(T ⊗ₖ K̄) → π₁(T ⊗ₖ K) → π₁(Spec K) → 1` is
exact, and `π₁(T ⊗ₖ K̄) → π₁(T)` is bijective by the invariance; the group theory of X.1.7
concludes. -/
theorem bijective_map_prod_field_of_invariance [QuasiCompact sT] [QuasiSeparated sT]
    [ConnectedSpace T] (hinv : HasAlgClosedBaseChangeInvariance sT) (K : Type u) [Field K]
    [Algebra k K] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : Spec (.of Ω) ⟶ pullback sT (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Function.Bijective ((FundamentalGroup.map (pullback.fst _ _) c).prod
      (FundamentalGroup.map (pullback.snd _ _) c)) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Z := pullback sT ρ
  let pT := pullback.fst sT ρ
  let h := pullback.snd sT ρ
  have : GeometricallyConnected sT := geometricallyConnected_of_isAlgClosed sT
  have : ConnectedSpace Z := connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sT ρ
  have : ConnectedSpace (Spec (.of K)) := inferInstance
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨s⟩ : Nonempty (Spec (.of K)) := inferInstance
  -- the geometric fibre of `h` at `s` is `T ⊗ₖ κ̄`
  let κ := (Spec (.of K)).residueField s
  let ρκ := Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ)))
  let ι := ExposeIX.geometricFiberι h s
  have hsq : IsPullback (ι ≫ pT) (pullback.snd (h.fiberToSpecResidueField s) ρκ) sT
      ((ρκ ≫ (Spec (.of K)).fromSpecResidueField s) ≫ ρ) :=
    ((IsPullback.of_hasPullback (h.fiberToSpecResidueField s) ρκ).paste_horiz
      (IsPullback.of_hasPullback h ((Spec (.of K)).fromSpecResidueField s))).paste_horiz
      (IsPullback.of_hasPullback sT ρ)
  have hequiv : (ExposeV.FEt.pullback (ι ≫ pT)).IsEquivalence :=
    hinv.isEquivalence_of_isPullback _ hsq
  have : ConnectedSpace (ExposeIX.geometricFiber h s) :=
    (geometricallyConnected_of_isAlgClosed sT).geometrically_connectedSpace _ _ _ hsq
  -- fibre functors
  obtain ⟨g₀⟩ : Nonempty (ExposeIX.geometricFiber h s) := inferInstance
  let Ω'' := AlgebraicClosure ((ExposeIX.geometricFiber h s).residueField g₀)
  let x'' : Spec (.of Ω'') ⟶ ExposeIX.geometricFiber h s := ExposeX.geometricPoint _ g₀
  let F'' := ExposeV.FEt.fiber Ω'' x''
  let G := ExposeV.FEt.pullback ι ⋙ F''
  have : FiberFunctor G :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω'' ι x'').symm
  have : FiberFunctor (ExposeV.FEt.pullback h ⋙ G) :=
    ExposeV.fiberFunctor_of_iso ((ExposeV.FEt.pullbackFiberIso Ω'' h (x'' ≫ ι)).symm ≪≫
      Functor.isoWhiskerLeft (ExposeV.FEt.pullback h)
        (ExposeV.FEt.pullbackFiberIso Ω'' ι x'').symm)
  have : FiberFunctor (ExposeV.FEt.pullback pT ⋙ G) :=
    ExposeV.fiberFunctor_of_iso ((ExposeV.FEt.pullbackFiberIso Ω'' pT (x'' ≫ ι)).symm ≪≫
      Functor.isoWhiskerLeft (ExposeV.FEt.pullback pT)
        (ExposeV.FEt.pullbackFiberIso Ω'' ι x'').symm)
  have : CompactSpace (h.fiber s) :=
    QuasiCompact.compactSpace_of_compactSpace (h.fiberToSpecResidueField s)
  have : QuasiSeparated (h.fiberToSpecResidueField s) :=
    inferInstanceAs (QuasiSeparated (pullback.snd h _))
  have : QuasiSeparatedSpace (h.fiber s) :=
    quasiSeparatedSpace_of_quasiSeparated (h.fiberToSpecResidueField s)
  -- IX.6.1 for `h : T ⊗ₖ K ⟶ Spec K`
  obtain ⟨-, hex⟩ := ExposeIX.exactSequence_of_quasiSeparatedSpace h s
    ⟨.of K, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩ inferInstance F''
  let i := ExposeIX.autMap (ExposeV.FEt.pullback ι) F''
  let p := ExposeIX.autMap (ExposeV.FEt.pullback h) G
  let q := ExposeIX.autMap (ExposeV.FEt.pullback pT) G
  -- `π₁(T ⊗ₖ κ̄) → π₁(T)` is bijective
  have hqi : Function.Bijective (q.comp i) := by
    have hequiv' : (ExposeV.FEt.pullback pT ⋙ ExposeV.FEt.pullback ι).IsEquivalence :=
      Functor.isEquivalence_of_iso (MorphismProperty.Over.pullbackComp ι pT)
    have : FiberFunctor ((ExposeV.FEt.pullback pT ⋙ ExposeV.FEt.pullback ι) ⋙ F'') :=
      inferInstanceAs (FiberFunctor (ExposeV.FEt.pullback pT ⋙ G))
    have hb := (ExposeIX.bijective_autMap_iff
      (ExposeV.FEt.pullback pT ⋙ ExposeV.FEt.pullback ι) F'').mpr hequiv'
    have heq : ⇑(q.comp i) =
        ⇑(ExposeIX.autMap (ExposeV.FEt.pullback pT ⋙ ExposeV.FEt.pullback ι) F'') := by
      funext σ
      apply Iso.ext
      rfl
    rw [heq]
    exact hb
  -- `π₁(T ⊗ₖ K) → π₁(Spec K)` is surjective (IX.6.1)
  have hp : Function.Surjective p := by
    have := ExposeIX.preservesIsConnected_pullback_of_subsingleton h
    exact ExposeIX.surjective_of_preservesIsConnected (ExposeV.FEt.pullback h) G
  have hG : Function.Bijective ((ExposeIX.autMap (ExposeV.FEt.pullback pT) G).prod
      (ExposeIX.autMap (ExposeV.FEt.pullback h) G)) :=
    ExposeX.bijective_prod_of_bijective_comp i p q hqi hex hp
  -- change of fibre functor
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor G (ExposeV.FEt.fiber Ω c)
  rw [← autMap_refl, ← autMap_refl] at hG
  exact bijective_prod_autMap_of_iso _ _ φ _ _ _ _ hG

variable {sT}

omit [IsAlgClosed k] in
/-- The constant section `t₀ ⊗ₖ K : Spec K ⟶ T ⊗ₖ K` of `T ⊗ₖ K ⟶ Spec K` given by a rational
point `t₀` of `T`. It is X.1.9's fibre inclusion `id ×ₖ t₀ : Spec K ⟶ Spec K ×ₖ T`
(`SGA.SGA1.ExposeX.fibreInclusion`) followed by the symmetry of the fibre product. -/
noncomputable def constSection (t₀ : Spec (.of k) ⟶ T) (ht₀ : t₀ ≫ sT = 𝟙 _) (K : Type u)
    [Field K] [Algebra k K] :
    Spec (.of K) ⟶ pullback sT (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ExposeX.fibreInclusion _ sT t₀ ht₀ ≫ (pullbackSymmetry _ _).hom

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma constSection_fst (t₀ : Spec (.of k) ⟶ T) (ht₀ : t₀ ≫ sT = 𝟙 _) (K : Type u) [Field K]
    [Algebra k K] :
    constSection t₀ ht₀ K ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t₀ := by
  rw [constSection, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma constSection_snd (t₀ : Spec (.of k) ⟶ T) (ht₀ : t₀ ≫ sT = 𝟙 _) (K : Type u) [Field K]
    [Algebra k K] : constSection t₀ ht₀ K ≫ pullback.snd _ _ = 𝟙 _ := by
  rw [constSection, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `π₁(T ⊗ₖ K) → π₁(T)` is the image of `π₁(Spec K)` under the constant section
`t₀ ⊗ₖ K` (given the invariance property for `T`): by `bijective_map_prod_field_of_invariance`,
an element of the kernel is determined by its image in `π₁(Spec K)`, and the section is a right
inverse of `π₁(T ⊗ₖ K) → π₁(Spec K)` up to conjugation, killed by `π₁(T ⊗ₖ K) → π₁(T)` (it factors
through `π₁(Spec k) = 1`). The base point is `t₀ ⊗ₖ K` composed with any geometric point `ω` of
`Spec K`. -/
theorem ker_map_fst_le_range_map_constSection [QuasiCompact sT] [QuasiSeparated sT]
    [ConnectedSpace T] (hinv : HasAlgClosedBaseChangeInvariance sT) (t₀ : Spec (.of k) ⟶ T)
    (ht₀ : t₀ ≫ sT = 𝟙 _) (K : Type u) [Field K] [Algebra k K] (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (ω : Spec (.of Ω) ⟶ Spec (.of K)) :
    (FundamentalGroup.map (pullback.fst sT (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (ω ≫ constSection t₀ ht₀ K)).ker ≤
        (FundamentalGroup.map (constSection t₀ ht₀ K) ω).range := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pT := pullback.fst sT ρ
  let h := pullback.snd sT ρ
  let t₀K := constSection t₀ ht₀ K
  have : ConnectedSpace ↥(pullback sT ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sT ρ
  have : ConnectedSpace (Spec (.of K)) := inferInstance
  let c' := ω ≫ t₀K
  have hbij := bijective_map_prod_field_of_invariance sT hinv K Ω c'
  let q := FundamentalGroup.map pT c'
  let p := FundamentalGroup.map h c'
  let s₀ := FundamentalGroup.map t₀K ω
  -- `π₁(Spec K) → π₁(T ⊗ₖ K) → π₁(T)` is trivial, as `t₀K ≫ pT` factors through `Spec k`
  have hqs : q.comp s₀ = 1 :=
    ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω t₀K pT ρ t₀
      (constSection_fst t₀ ht₀ K) ω
      fun τ ↦ ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω k _ τ
  -- `π₁(Spec K) → π₁(T ⊗ₖ K) → π₁(Spec K)` is bijective, as `t₀K` is a section of `h`
  obtain ⟨φ, hφ⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω t₀K h
    (constSection_snd t₀ ht₀ K) ω
  intro g hg
  let τ := φ.conjAut.symm (p g)
  have hp : p (s₀ τ) = p g := by
    have := DFunLike.congr_fun hφ τ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    exact this.trans (φ.conjAut.apply_symm_apply _)
  have hq : q (s₀ τ) = q g := by
    rw [(MonoidHom.mem_ker).mp hg, ← MonoidHom.comp_apply, hqs, MonoidHom.one_apply]
  exact ⟨τ, hbij.1 (Prod.ext hq hp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The generic-fibre step of the resolution-free proof of XIII.4.6 in characteristic `0`. Let `T`
be quasi-compact, quasi-separated and connected over an algebraically closed field `k`, with the
invariance property, `t₀` a rational point of `T` and `K ⊇ k` a field. A connected étale covering
`C` of `T ⊗ₖ K` which has a `K`-point above the constant point `t₀ ⊗ₖ K` comes from an étale
covering of `T`.

In terms of `π₁(T ⊗ₖ K) ≅ π₁(T) × π₁(Spec K)` (`bijective_map_prod_field_of_invariance`): the
section `t₀ ⊗ₖ K` of `T ⊗ₖ K → Spec K` maps `π₁(Spec K)` onto the kernel of
`π₁(T ⊗ₖ K) → π₁(T)` (`ker_map_fst_le_range_map_constSection`), and this image fixes the point of
the fibre of `C` given by the `K`-point; V.6.11 (`SGA.SGA1.ExposeX.exists_iso_obj_of_ker_le_range`)
concludes. -/
theorem exists_iso_pullback_fst_of_section_of_invariance [QuasiCompact sT] [QuasiSeparated sT]
    [ConnectedSpace T] (hinv : HasAlgClosedBaseChangeInvariance sT) (t₀ : Spec (.of k) ⟶ T)
    (ht₀ : t₀ ≫ sT = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K]
    (C : ExposeV.FEt (pullback sT (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    [PreGaloisCategory.IsConnected C] (σ : Spec (.of K) ⟶ C.left)
    (hσ : σ ≫ C.hom = constSection t₀ ht₀ K) :
    ∃ W : ExposeV.FEt T, Nonempty (C ≅
      (ExposeV.FEt.pullback (pullback.fst sT (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
        W) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pT := pullback.fst sT ρ
  let t₀K := constSection t₀ ht₀ K
  have : ConnectedSpace ↥(pullback sT ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sT ρ
  have : ConnectedSpace (Spec (.of K)) := inferInstance
  -- geometric points
  let Ω := AlgebraicClosure K
  let ω : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let c' := ω ≫ t₀K
  have hbij := bijective_map_prod_field_of_invariance sT hinv K Ω c'
  have hsurj : Function.Surjective (FundamentalGroup.map pT c') := fun a ↦ by
    obtain ⟨g, hg⟩ := hbij.2 (a, 1)
    exact ⟨g, congrArg Prod.fst hg⟩
  have hker := ker_map_fst_le_range_map_constSection hinv t₀ ht₀ K Ω ω
  -- the `K`-point of `C` is a section of `t₀K^* C`
  let TS : ExposeV.FEt (Spec (.of K)) :=
    MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of K))) ⟨inferInstance, inferInstance⟩
  have hTS : IsTerminal TS :=
    @ExposeV.FEt.isTerminalOfIsIso _ TS (inferInstanceAs (IsIso (𝟙 (Spec (.of K)))))
  let sec : TS ⟶ (ExposeV.FEt.pullback t₀K).obj C :=
    MorphismProperty.Over.homMk (pullback.lift σ (𝟙 _) (hσ.trans (Category.id_comp t₀K).symm))
      (pullback.lift_snd _ _ _)
  have hs : Nonempty (⊤_ (ExposeV.FEt (Spec (.of K))) ⟶ (ExposeV.FEt.pullback t₀K).obj C) :=
    ⟨(terminalIsTerminal.uniqueUpToIso hTS).hom ≫ sec⟩
  obtain ⟨W, ⟨e⟩⟩ := ExposeX.exists_iso_obj_of_ker_le_range (F'' := ExposeV.FEt.fiber Ω ω)
    (ExposeV.FEt.pullback t₀K) (ExposeV.FEt.pullbackFiberIso Ω t₀K ω) hsurj hker C hs
  exact ⟨W, ⟨e⟩⟩

end Field

end SGA.SGA1.ExposeXIII
