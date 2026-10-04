/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExtensionCriterion
import SGA.SGA1.ExposeXII.RiemannExtensionClosure
import SGA.SGA1.ExposeXII.RiemannReductionNoether
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.RiemannReduction
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeXII.LocalTopologySLSC
import SGA.SGA1.ExposeXII.Connected
import SGA.SGA1.ExposeI.Permanence

/-!
# SGA 1, Exposé XII, 5.1 for normal affine curves

`isEquivalence_pointsFunctor_of_isIntegrallyClosed`: for `B` a normal domain of finite type and
dimension `1` over `ℂ` (a smooth affine curve), the functor `Ψ : S ↦ S(ℂ)` from finite étale
`B`-algebras to finite coverings of `X(ℂ)`, `X = Spec B`, is an equivalence. This is XII.5.1 for
`X`, by this project's route (not SGA's, which goes through resolution and GAGA):

1. on a dense open `{h ≠ 0}`, `X` is finite étale over some `ℂ ∖ S`, so XII.5.1 holds for
   `B[1/h]` (`NoetherCurve.exists_isEquivalence_pointsFunctor_away`);
2. a connected finite covering `E` of `X(ℂ)` restricts over `{h ≠ 0}` to `C'(ℂ)` for a finite étale
   `B[1/h]`-algebra `C'`, which is a domain (`p⁻¹{h ≠ 0}` is connected,
   `isPreconnected_preimage_of_preconnectedSpace`, and I.10.1,
   `isDomain_of_connectedSpace_of_etale`);
3. the integral closure `C` of `B` in `C'` is finite, flat, Dedekind, with `C[1/h] = C'`
   (`SGA.SGA1.ExposeXII.RiemannExtensionClosure`);
4. the extension criterion (`etale_and_mem_essImage`): the identification of `E` and `C(ℂ)` over
   `{h ≠ 0}` extends across the finitely many zeros of `h` (connected punctured neighbourhoods at
   points with a DVR local ring, `Points.hasConnectedPuncturedNhds_of_isDedekindDomain`), and point
   counting shows that `C` is étale and `E ≅ C(ℂ)`.

Also `TopCat.FiniteCovering.isOpenEmbedding_baseChangeSnd` (the pullback of a finite covering
along an open embedding `f` is an open embedding into the total space, with image the part over the
range of `f`) and `RiemannExtension.isDedekindDomain_of_ringKrullDim_le_one`.
-/

noncomputable section

open CategoryTheory Topology Set Filter Module CommAlgCat Opposite

namespace TopCat.FiniteCovering

variable {X Y : TopCat.{0}}

/-- The pullback of a finite covering `E → X` along an open embedding `f : Y → X` is, through the
second projection, an open embedding into `E` whose image is the part of `E` over the range of
`f`. -/
theorem isOpenEmbedding_baseChangeSnd {f : Y ⟶ X} (hf : IsOpenEmbedding f) (E : FiniteCovering X) :
    IsOpenEmbedding (baseChangeSnd f E) ∧
      range (baseChangeSnd f E) = E.obj.hom ⁻¹' range f := by
  let g : range f ≃ₜ Y := hf.isEmbedding.toHomeomorph.symm
  have hg (y : Y) : g ⟨f y, mem_range_self y⟩ = y :=
    hf.isEmbedding.toHomeomorph.symm_apply_apply y
  have hfg (z : range f) : f (g z) = z := by
    obtain ⟨_, y, rfl⟩ := z
    rw [hg]
  let H : ((baseChange f).obj E).obj.left ≃ₜ E.obj.hom ⁻¹' range f :=
    { toFun q := ⟨baseChangeSnd f E q, ⟨(((baseChange f).obj E).obj.hom q),
          (hom_baseChangeSnd f E q).symm⟩⟩
      invFun e := baseChangeMk f E (g ⟨E.obj.hom e.1, e.2⟩) e.1 (hfg _)
      left_inv q := baseChange_ext (by
          change g ⟨E.obj.hom (baseChangeSnd f E q), _⟩ = _
          simp only [hom_baseChangeSnd]
          exact hg _) rfl
      right_inv e := rfl
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (baseChangeSnd f E).hom.continuous
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_subtype_val) _
        exact g.continuous.comp (Continuous.subtype_mk
          (E.obj.hom.hom.continuous.comp continuous_subtype_val) _) }
  have hopen : IsOpen (E.obj.hom ⁻¹' range f) :=
    hf.isOpen_range.preimage E.obj.hom.hom.continuous
  refine ⟨hopen.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding, ?_⟩
  ext e
  constructor
  · rintro ⟨q, rfl⟩
    exact (H q).2
  · intro he
    exact ⟨H.symm ⟨e, he⟩, rfl⟩

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

namespace Points

/-- At a point `φ ∈ X(ℂ)` of a Dedekind domain `A` of finite type over `ℂ` whose kernel is
nonzero (i.e. `X` is not a point), `X(ℂ)` has connected punctured neighbourhoods: the local ring is
a discrete valuation ring (`hasConnectedPuncturedNhds_of_isDiscreteValuationRing`). -/
theorem hasConnectedPuncturedNhds_of_isDedekindDomain {A : Type*} [CommRing A] [IsDedekindDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] (φ : Points ℂ A) (hφ : ker φ ≠ ⊥) :
    HasConnectedPuncturedNhds φ := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hφ
    (Localization.AtPrime (ker φ))
  exact hasConnectedPuncturedNhds_of_isDiscreteValuationRing φ

end Points

namespace RiemannExtension

open RiemannHigher

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

/-- A normal domain of finite type over `ℂ` of dimension at most `1` is a Dedekind domain. -/
lemma isDedekindDomain_of_ringKrullDim_le_one [IsIntegrallyClosed B] (hdim : ringKrullDim B ≤ 1) :
    IsDedekindDomain B :=
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  have : Ring.DimensionLEOne B := ⟨fun hne hp ↦
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp (Ring.krullDimLE_iff.mpr hdim) _ hne hp⟩
  { }

/-- **XII.5.1 for normal affine curves, one connected covering** (this project's route): for `B`
a normal domain of finite type and dimension `1` over `ℂ`, every connected finite covering `E` of
`X(ℂ)`, `X = Spec B`, is isomorphic to `S(ℂ)` for a finite étale `B`-algebra `S`. -/
theorem mem_essImage_of_connectedSpace [IsIntegrallyClosed B] (hdim : ringKrullDim B = 1)
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ B))) [ConnectedSpace E.obj.left] :
    (pointsFunctor ℂ B).essImage E := by
  classical
  have hDed : IsDedekindDomain B := isDedekindDomain_of_ringKrullDim_le_one hdim.le
  have : CharZero B := charZero_of_injective_algebraMap (algebraMap ℂ B).injective
  have hmax (P : Ideal B) (hP : P.IsPrime) (hne : P ≠ ⊥) : P.IsMaximal := hP.isMaximal hne
  obtain ⟨h, hh, hZ, hRET⟩ := NoetherCurve.exists_isEquivalence_pointsFunctor_away B hdim
  set Bh := Localization.Away h
  have : IsDomain Bh := isDomain_away hh
  have : IsIntegrallyClosed Bh :=
    isIntegrallyClosed_of_isLocalization Bh (Submonoid.powers h)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  obtain ⟨T, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := pointsFunctor ℂ Bh) (restrictAway h E)
  -- the finite étale `B[1/h]`-algebra `C'` with `C'(ℂ) ≅ E|{h ≠ 0}`
  set C' := T.unop.obj
  let : Algebra ℂ C' := algebraOfFiniteEtale ℂ Bh T.unop
  have : IsScalarTower ℂ Bh C' := isScalarTower_of_finiteEtale ℂ Bh T.unop
  let : Algebra B C' := ((algebraMap Bh C').comp (algebraMap B Bh)).toAlgebra
  have : IsScalarTower B Bh C' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower ℂ B C' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ Bh C', IsScalarTower.algebraMap_apply ℂ B Bh]
    rfl
  -- `Γ : C'(ℂ) → E`, an open embedding onto the part of `E` over `{h ≠ 0}`
  let ι : TopCat.of (Points ℂ Bh) ⟶ TopCat.of (Points ℂ B) :=
    pointsHom (IsScalarTower.toAlgHom ℂ B Bh)
  have hι : IsOpenEmbedding ι := Points.isOpenEmbedding_map_of_isLocalizationAway h
  have hιrange : range ι = {φ : Points ℂ B | φ h ≠ 0} := Points.range_map_of_isLocalizationAway h
  let j := TopCat.homeoOfIso ((Over.forget _).mapIso ((ObjectProperty.ι _).mapIso i))
  let Γ : Points ℂ C' → E.obj.left := fun w ↦ TopCat.FiniteCovering.baseChangeSnd ι E (j w)
  obtain ⟨hsnd, hsndrange⟩ := TopCat.FiniteCovering.isOpenEmbedding_baseChangeSnd hι E
  have hΓ : IsOpenEmbedding Γ := hsnd.comp j.isOpenEmbedding
  have hΓrange : range Γ = E.obj.hom ⁻¹' {φ | φ h ≠ 0} := by
    rw [← hιrange, ← hsndrange]
    exact j.surjective.range_comp (TopCat.FiniteCovering.baseChangeSnd ι E)
  have hΓp (w : Points ℂ C') : E.obj.hom (Γ w) = ι (Points.proj Bh C' w) := by
    exact (TopCat.FiniteCovering.hom_baseChangeSnd ι E (j w)).trans
      (congrArg ι (TopCat.FiniteCovering.hom_left_apply i.hom w))
  -- `C'` is a domain: `C'(ℂ) ≅ p⁻¹{h ≠ 0}` is connected
  have hpunctB (φ : Points ℂ B) (hφ : φ h = 0) : HasConnectedPuncturedNhds φ :=
    Points.hasConnectedPuncturedNhds_of_isDedekindDomain φ fun h0 ↦ hh (by
      have : h ∈ Points.ker φ := Points.mem_ker.mpr hφ
      rwa [h0, Ideal.mem_bot] at this)
  have hiso : ∀ x ∉ {φ : Points ℂ B | φ h ≠ 0}, ∃ N ∈ 𝓝 x, N \ {x} ⊆ {φ | φ h ≠ 0} := by
    intro x _
    refine ⟨({φ : Points ℂ B | φ h = 0} \ {x})ᶜ,
      (hZ.sdiff).isClosed.isOpen_compl.mem_nhds fun hx ↦ hx.2 rfl, ?_⟩
    rintro y ⟨hy, hyx⟩ hyΩ
    exact hy ⟨hyΩ, hyx⟩
  have hpre : IsPreconnected (E.obj.hom ⁻¹' {φ : Points ℂ B | φ h ≠ 0}) :=
    isPreconnected_preimage_of_preconnectedSpace E.isCoveringMap
      (isOpen_compl_singleton.preimage (Points.continuous_apply h))
      (fun x hx ↦ hpunctB x (not_not.mp hx)) hiso
  have : Algebra.FiniteType ℂ C' := .trans (S := Bh) inferInstance inferInstance
  have hconn : ConnectedSpace (Points ℂ C') := by
    have hne : Nonempty (Points ℂ C') := by
      obtain ⟨e⟩ := (inferInstance : Nonempty E.obj.left)
      by_cases he : E.obj.hom e ∈ {φ : Points ℂ B | φ h ≠ 0}
      · obtain ⟨w, -⟩ : e ∈ range Γ := hΓrange ▸ he
        exact ⟨w⟩
      · obtain ⟨N, hN, hNΩ⟩ := hiso _ he
        obtain ⟨N', hN', hN'Ω⟩ := exists_mem_nhds_diff_subset E.isCoveringMap hN hNΩ
        have := (hasConnectedPuncturedNhds_of_isCoveringMap E.isCoveringMap
          (hpunctB _ (not_not.mp he))).neBot
        obtain ⟨e', he'⟩ := Filter.nonempty_of_mem (sdiff_mem_nhdsWithin_compl hN' {e})
        obtain ⟨w, -⟩ : e' ∈ range Γ := hΓrange ▸ hN'Ω he'
        exact ⟨w⟩
    refine connectedSpace_iff_univ.mpr ⟨univ_nonempty, ?_⟩
    rw [← hΓ.isInducing.isPreconnected_image, image_univ, hΓrange]
    exact hpre
  have : ConnectedSpace (PrimeSpectrum C') := Points.connectedSpace_iff'.mp hconn
  have : IsDomain C' := isDomain_of_connectedSpace_of_etale (A := Bh)
  have : IsIntegrallyClosed C' := ExposeI.isIntegrallyClosed_of_etale (A := Bh)
  -- the integral closure `C` of `B` in `C'`
  set C := integralClosure B C'
  have : Module.Finite B C := finite_integralClosure hh
  have : Module.Flat B C := flat_integralClosure hh
  have : IsDedekindDomain C := isDedekindDomain_integralClosure hh
  have : Algebra.FiniteType ℂ C := .trans (S := B) inferInstance inferInstance
  have hloc : IsLocalization.Away (algebraMap B C h) C' := isLocalization_away_integralClosure h
  have hinjC : Function.Injective (algebraMap B C) := injective_algebraMap_integralClosure hh
  -- `C[1/h] = C'` is unramified over `B`
  have hunr : Algebra.FormallyUnramified B (Localization.Away (algebraMap B C h)) := by
    have : Algebra.FormallyUnramified B Bh := .of_isLocalization (Submonoid.powers h)
    have : Algebra.FormallyUnramified B C' := .comp B Bh C'
    exact .of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap B C h)) C'
      (Localization.Away (algebraMap B C h))).restrictScalars B)
  -- `r : C'(ℂ) → C(ℂ)`, an open embedding onto `{h ≠ 0}`
  let r : Points ℂ C' → Points ℂ C := Points.map (IsScalarTower.toAlgHom ℂ C C')
  have hr : IsOpenEmbedding r := Points.isOpenEmbedding_map_of_isLocalizationAway (algebraMap B C h)
  have hrrange : range r = {ψ : Points ℂ C | ψ (algebraMap B C h) ≠ 0} :=
    Points.range_map_of_isLocalizationAway (algebraMap B C h)
  have hΓr (w : Points ℂ C') : E.obj.hom (Γ w) = Points.proj B C (r w) := by
    rw [hΓp]
    ext b
    rfl
  have hpunctC (ψ : Points ℂ C) (hψ : ψ (algebraMap B C h) = 0) : HasConnectedPuncturedNhds ψ :=
    Points.hasConnectedPuncturedNhds_of_isDedekindDomain ψ fun h0 ↦ hh (hinjC (by
      have : algebraMap B C h ∈ Points.ker ψ := Points.mem_ker.mpr hψ
      rwa [h0, Ideal.mem_bot, ← map_zero (algebraMap B C)] at this))
  exact (etale_and_mem_essImage hmax hh hZ hpunctB hunr hpunctC E hΓ hr hΓr hΓrange hrrange).2

end RiemannExtension

open RiemannExtension in
/-- **XII.5.1 for normal affine curves** (this project's route): for `B` a normal domain of finite
type and dimension `1` over `ℂ`, the functor `Ψ : S ↦ S(ℂ)` from finite étale `B`-algebras to
finite coverings of `X(ℂ)`, `X = Spec B`, is an equivalence of categories. -/
theorem isEquivalence_pointsFunctor_of_isIntegrallyClosed (B : Type) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra ℂ B] [Algebra.FiniteType ℂ B] (hdim : ringKrullDim B = 1) :
    (pointsFunctor ℂ B).IsEquivalence := by
  refine isEquivalence_pointsFunctor_of_forall_isConnected B fun E hE ↦ ?_
  have : ConnectedSpace (Points ℂ B) := Points.connectedComparison B inferInstance
  have : PathConnectedSpace (Points ℂ B) := .of_locallyPathConnectedSpace
  have := TopCat.FiniteCovering.connectedSpace_of_isConnected E
  exact mem_essImage_of_connectedSpace hdim E

end SGA.SGA1.ExposeXII
