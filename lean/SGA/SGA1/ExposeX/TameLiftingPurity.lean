/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.Normal
import SGA.Foundations.CommAlg.PurityScheme
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeX.Purity
import SGA.SGA1.ExposeX.TameLiftingAlgebra
import SGA.SGA1.ExposeXIII.AbhyankarPurity

/-!
# SGA 1, Exposé X, 3.1–3.4: extending a covering across a divisor, ring form

In the proof of X.3.8 an étale covering of the generic fibre `X_K` of a regular scheme `X` over a
discrete valuation ring is extended to `X` once its normalization is known to be étale at the
generic point of the closed fibre: by purity (X.3.1, SGA 2 X.3.4) the normalization is then étale
everywhere. Over an affine open `Spec S` with `X_K ∩ Spec S = Spec S[1/t]` this is the following
statement on rings, which `SGA.SGA1.ExposeXIII.etale_integralClosure_of_forall_isEtaleAt` proves
for a regular *local* ring `S`; we deduce it for every regular domain by localizing:

* `etale_integralClosure_of_isRegularRing`: let `S` be a regular domain, `t ≠ 0` in `S` and `C` a
  finite étale `S[1/t]`-algebra. If the normalization `B` of `S` in `C` is étale over `S` at the
  primes lying over the height-one primes of `S` containing `t`, then `B` is finite étale over `S`.
-/

universe u

open IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeX

section Localize

variable {S : Type u} [CommRing S] {t : S} (C : Type u) [CommRing C] [Algebra S C]
  [Algebra (Localization.Away t) C] [IsScalarTower S (Localization.Away t) C]

/-- The prime `Q.comap ψ` of the normalization `B` of `S` in `C` below a prime `q'` of the
normalization of `S_p` in `C_p`: étaleness of `S → B` at `Q.comap ψ` gives étaleness of
`S_p → B_p` at `q'`. -/
private theorem isEtaleAt_of_isLocalization {Sp Cp : Type u} [CommRing Sp] [CommRing Cp]
    [Algebra S Sp] [Algebra S Cp] [Algebra C Cp] [Algebra Sp Cp] [IsScalarTower S C Cp]
    [IsScalarTower S Sp Cp] (N : Submonoid S) [IsLocalization N Sp]
    [IsLocalization (Algebra.algebraMapSubmonoid C N) Cp]
    (q' : Ideal (integralClosure Sp Cp)) [q'.IsPrime]
    (h : ∀ (q : Ideal (integralClosure S C)) [q.IsPrime],
      q.comap (algebraMap S (integralClosure S C)) =
        (q'.comap (algebraMap Sp (integralClosure Sp Cp))).comap (algebraMap S Sp) →
      Algebra.IsEtaleAt S q) :
    Algebra.IsEtaleAt Sp q' := by
  let ψ : integralClosure S C →+* integralClosure Sp Cp :=
    { toFun x := ⟨algebraMap C Cp x.1, (x.2.map (IsScalarTower.toAlgHom S C Cp)).tower_top⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  let : Algebra (integralClosure S C) (integralClosure Sp Cp) := ψ.toAlgebra
  have : IsScalarTower (integralClosure S C) (integralClosure Sp Cp) Cp :=
    ⟨fun x y z ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
        mul_assoc]
      rfl⟩
  have : IsScalarTower S (integralClosure S C) (integralClosure Sp Cp) :=
    .of_algebraMap_eq fun s ↦ Subtype.ext (by
      change algebraMap S Cp s = algebraMap C Cp (algebraMap S C s)
      rw [← IsScalarTower.algebraMap_apply])
  have hloc := IsLocalization.integralClosure (R := S) (S := C) (Rf := Sp) (Sf := Cp) N
  let B := integralClosure S C
  let B' := integralClosure Sp Cp
  let Q : Ideal B := q'.comap (algebraMap B B')
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  -- `Q` lies over the prime of `S` below `q'`
  have hQS : Q.comap (algebraMap S B) =
      (q'.comap (algebraMap Sp B')).comap (algebraMap S Sp) := by
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hQe : Algebra.IsEtaleAt S Q := h Q hQS
  -- `B_Q ≅ B'_{q'}`
  have hd : Disjoint (Algebra.algebraMapSubmonoid B N : Set B) (Q : Set B) := by
    refine Set.disjoint_left.mpr fun _ ⟨s, hs, e⟩ hsQ ↦ ?_
    have hu : IsUnit (algebraMap B B' (algebraMap S B s)) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S Sp B']
      exact (IsLocalization.map_units Sp ⟨s, hs⟩).map _
    rw [← e] at hsQ
    exact (Ideal.IsPrime.ne_top ‹q'.IsPrime›) (Ideal.eq_top_of_isUnit_mem q' hsQ hu)
  have hL : IsLocalization.AtPrime (Localization.AtPrime q') Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid B N) (Localization.AtPrime q') q'
  let e : Localization.AtPrime Q ≃ₐ[B] Localization.AtPrime q' :=
    IsLocalization.algEquiv Q.primeCompl _ _
  have : Algebra.FormallyEtale S (Localization.AtPrime q') :=
    Algebra.FormallyEtale.of_equiv (e.restrictScalars S)
  have : Algebra.FormallyEtale S Sp := Algebra.FormallyEtale.of_isLocalization N
  exact Algebra.FormallyEtale.of_restrictScalars (R := S)

end Localize

section Regular

variable {S : Type u} [CommRing S] [IsDomain S] [IsRegularRing S] {t : S}
  (C : Type u) [CommRing C] [Algebra S C] [Algebra (Localization.Away t) C]
  [IsScalarTower S (Localization.Away t) C] [Module.Finite (Localization.Away t) C]
  [Algebra.Etale (Localization.Away t) C]

/-- X.3.1 for the normalization of a regular domain in a covering of `D(t)` (SGA 2 X.3.4; the case
of a regular local ring is `SGA.SGA1.ExposeXIII.etale_integralClosure_of_forall_isEtaleAt`): let
`S` be a regular domain, `t ≠ 0` in `S` and `C` a finite étale `S[1/t]`-algebra. If the
normalization of `S` in `C` is étale over `S` at every prime lying over a height-one prime of `S`
containing `t`, it is finite étale over `S`. At a prime `p` of `S` this is the local case for
`S_p` and `S_p[1/t] ⊗_{S[1/t]} C`. -/
theorem etale_integralClosure_of_isRegularRing (ht : t ≠ 0)
    (h : ∀ (q : Ideal (integralClosure S C)) [q.IsPrime],
      t ∈ q.comap (algebraMap S (integralClosure S C)) →
      (q.comap (algebraMap S (integralClosure S C))).height = 1 → Algebra.IsEtaleAt S q) :
    Module.Finite S (integralClosure S C) ∧ Algebra.Etale S (integralClosure S C) := by
  have : IsIntegrallyClosed S := IsRegularRing.isIntegrallyClosed
  have hfin : Module.Finite S (integralClosure S C) := finite_integralClosure_of_etale_away ht C
  refine ⟨hfin, ?_⟩
  have : Algebra.FinitePresentation S (integralClosure S C) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine Algebra.etaleLocus_eq_univ_iff_etale.mp (Set.eq_univ_of_forall fun Q ↦ ?_)
  let p := Q.asIdeal.comap (algebraMap S (integralClosure S C))
  let N := p.primeCompl
  let Sp := Localization.AtPrime p
  let St := Localization.Away t
  let tp := algebraMap S Sp t
  let Mt := Localization.Away tp
  let : Algebra St Mt := (Localization.awayMap (algebraMap S Sp) t).toAlgebra
  have : IsScalarTower S St Mt := .of_algebraMap_eq fun a ↦ by
    change _ = Localization.awayMap (algebraMap S Sp) t (algebraMap S St a)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp (Submonoid.powers t)) Mt := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid St N) Mt :=
    IsLocalization.commutes St Sp Mt (Submonoid.powers t) N
  let Cp := Mt ⊗[St] C
  let : Algebra C Cp := Algebra.TensorProduct.rightAlgebra
  have hCp : IsLocalization (Algebra.algebraMapSubmonoid C (Algebra.algebraMapSubmonoid St N))
      Cp := IsLocalization.tensorRight (A := Mt) (S := C) (Algebra.algebraMapSubmonoid St N)
  have : IsLocalization (Algebra.algebraMapSubmonoid C N) Cp := by
    convert hCp using 1
    ext x
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨algebraMap S St a, ⟨a, ha, rfl⟩, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, IsScalarTower.algebraMap_apply _ _ _ _⟩
  have : IsScalarTower S C Cp := .of_algebraMap_eq fun a ↦ by
    change algebraMap S Mt a ⊗ₜ[St] (1 : C) = (1 : Mt) ⊗ₜ[St] algebraMap S C a
    rw [IsScalarTower.algebraMap_apply S St C, IsScalarTower.algebraMap_apply S St Mt,
      Algebra.algebraMap_eq_smul_one (algebraMap S St a), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
  have htp : tp ≠ 0 := fun h0 ↦ ht (IsLocalization.injective Sp
    (p.primeCompl_le_nonZeroDivisors) (h0.trans (map_zero _).symm))
  have hloc := ExposeXIII.etale_integralClosure_of_forall_isEtaleAt htp Cp fun q' _ htq hq1 ↦
    isEtaleAt_of_isLocalization C N q' fun q _ hq ↦ h q (by rw [hq]; exact htq) (by
      rw [hq, IsLocalization.height_under N]; exact hq1)
  have := hloc.2.1
  exact ExposeXIII.isEtaleAt_integralClosure_of_isLocalization (S' := Sp) (C' := Cp) N Q.asIdeal
    fun s hs hsQ ↦ hs hsQ

end Regular

section Scheme

open CategoryTheory Limits AlgebraicGeometry

variable {X : Scheme.{u}} {U : X.Opens} {W : Scheme.{u}} (w : W ⟶ U)

set_option backward.isDefEq.respectTransparency false in
/-- X.3.1 (SGA 2 X.3.4) for a covering of the complement of a divisor in a regular integral scheme:
let `X` be a regular, integral, locally noetherian scheme, `U ⊆ X` a nonempty open and
`w : W ⟶ U` an étale covering. Let `X = ⋃ Vᵢ` be a cover by nonempty affine opens with
`Vᵢ ∩ U = D(tᵢ)`. If on each `Vᵢ` the normalization of `Γ(Vᵢ)` in `Γ(W, w⁻¹Vᵢ)` is étale at the
primes lying over the height-one primes containing `tᵢ` (the generic points of `Vᵢ \ U` of
codimension one), then the normalization of `X` in `W` is finite étale over `X`
(`etale_integralClosure_of_isRegularRing` on each `Vᵢ`). -/
theorem finite_etale_fromNormalization_of_isRegularScheme [IsLocallyNoetherian X] [IsIntegral X]
    [IsFinite w] [Etale w] (hX : IsRegularScheme X) (hU : (U : Set X).Nonempty) {ι : Type*}
    (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hne : ∀ i, (V i : Set X).Nonempty)
    (hcov : ⨆ i, V i = ⊤) (t : ∀ i, Γ(X, V i)) (ht : ∀ i, X.basicOpen (t i) = V i ⊓ U)
    (h : ∀ i, letI := ((w ≫ U.ι).app (V i)).hom.toAlgebra
      ∀ (q : Ideal (integralClosure Γ(X, V i) Γ(W, (w ≫ U.ι) ⁻¹ᵁ V i))) [q.IsPrime],
        t i ∈ q.comap (algebraMap Γ(X, V i) _) →
        (q.comap (algebraMap Γ(X, V i) _)).height = 1 → Algebra.IsEtaleAt Γ(X, V i) q) :
    IsFinite (w ≫ U.ι).fromNormalization ∧ Etale (w ≫ U.ι).fromNormalization := by
  set g := w ≫ U.ι with hg
  set n := g.fromNormalization
  have hn : ∀ i, (n.app (V i)).hom.Etale := by
    intro i
    let A := Γ(X, V i)
    let C := Γ(W, g ⁻¹ᵁ V i)
    let := (g.app (V i)).hom.toAlgebra
    have : Nonempty (V i) := (hne i).to_subtype
    have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V i, hV i⟩
    have : IsRegularRing A :=
      ExposeII.isRegularRing_of_isRegularLocalRing_stalk (hV i) fun x ↦ hX x
    -- `tᵢ ≠ 0`, as `Vᵢ ∩ U ≠ ∅`
    have ht0 : t i ≠ 0 := by
      intro h0
      obtain ⟨x, hxV, hxU⟩ := nonempty_preirreducible_inter (V i).2 U.2 (hne i) hU
      have hx : x ∈ X.basicOpen (t i) := by rw [ht]; exact ⟨hxV, hxU⟩
      rw [h0, Scheme.basicOpen_zero] at hx
      exact hx
    -- `C` is a finite étale `A[1/tᵢ]`-algebra
    let D := X.basicOpen (t i)
    have hD : IsAffineOpen D := (hV i).basicOpen (t i)
    have hDV : D = V i ⊓ U := ht i
    have hDU : D ≤ U := hDV.le.trans inf_le_right
    have hgU : g ⁻¹ᵁ U = ⊤ := by
      rw [hg, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
    have hO : g ⁻¹ᵁ V i = g ⁻¹ᵁ D := by
      rw [hDV, Scheme.Hom.preimage_inf, hgU, inf_top_eq]
    have e : g ⁻¹ᵁ V i ≤ g ⁻¹ᵁ D := hO.le
    have hfin := finite_appLE_of_le w hD hDU e hO
    have het := etale_appLE_of_le w hD hDU e hO
    have : IsLocalization.Away (t i) Γ(X, D) := (hV i).isLocalization_basicOpen (t i)
    let ψ := IsLocalization.algEquiv (Submonoid.powers (t i)) (Localization.Away (t i)) Γ(X, D)
    let φ : Localization.Away (t i) →+* C := (g.appLE D (g ⁻¹ᵁ V i) e).hom.comp ψ.toRingHom
    let : Algebra (Localization.Away (t i)) C := φ.toAlgebra
    have : IsScalarTower A (Localization.Away (t i)) C := .of_algebraMap_eq fun a ↦ by
      change g.app (V i) a = g.appLE D (g ⁻¹ᵁ V i) e (ψ (algebraMap A _ a))
      rw [AlgEquiv.commutes]
      change _ = g.appLE D (g ⁻¹ᵁ V i) e (X.presheaf.map (homOfLE (X.basicOpen_le (t i))).op a)
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]
    have hψ : Function.Bijective ψ.toRingHom := ψ.bijective
    have : Module.Finite (Localization.Away (t i)) C :=
      RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ hψ.2)
    have : Algebra.Etale (Localization.Away (t i)) C :=
      RingHom.etale_algebraMap.mp
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hψ) het)
    obtain ⟨-, hB⟩ := etale_integralClosure_of_isRegularRing C ht0 (h i)
    rw [Scheme.Hom.fromNormalization_app g (hV i), CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr hB)
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))
  have het : Etale n := by
    have : IsZariskiLocalAtTarget @Etale.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale.{u}) V hcov]
    intro i
    have : IsAffine (V i) := hV i
    have : IsAffine (n ⁻¹ᵁ V i) := (hV i).preimage n
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale.{u}), morphismRestrict_appTop]
    exact etale_app_comp_eqToHom n (Scheme.Opens.ι_image_top _) _ (hn i)
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType n).mpr ⟨inferInstance, inferInstance⟩,
    het⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the normalization of `X` in an étale covering `w : W ⟶ U` of an open `U ⊆ X` is finite
étale over `X`, it is an étale covering of `X` restricting to `W` over `U` (normalization commutes
with the open immersion `U ⟶ X`; this is the end of the proof of
`AlgebraicGeometry.essSurj_pullback_of_isRegularLocalRing`, isolated). -/
theorem exists_iso_pullback_of_fromNormalization [IsLocallyNoetherian X] [IsFinite w] [Etale w]
    [IsFinite (w ≫ U.ι).fromNormalization] [Etale (w ≫ U.ι).fromNormalization] :
    ∃ Y : ExposeV.FEt X, Nonempty ((ExposeV.FEt.pullback U.ι).obj Y ≅
      MorphismProperty.Over.mk ⊤ w ⟨inferInstance, inferInstance⟩) := by
  have hcomp : pullback.fst (w ≫ U.ι) U.ι ≫ w = pullback.snd (w ≫ U.ι) U.ι := by
    rw [← cancel_mono U.ι, Category.assoc]
    exact pullback.condition
  let l : W ⟶ pullback (w ≫ U.ι) U.ι := pullback.lift (𝟙 _) w (by simp)
  have : IsIso l := ⟨⟨pullback.fst (w ≫ U.ι) U.ι, pullback.lift_fst _ _ _, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hcomp, Category.id_comp]⟩⟩
  have : IsIntegralHom (pullback.snd (w ≫ U.ι) U.ι) := by
    rw [← hcomp]; infer_instance
  let E : W ⟶ pullback (w ≫ U.ι).fromNormalization U.ι :=
    l ≫ (pullback.snd (w ≫ U.ι) U.ι).toNormalization ≫ (w ≫ U.ι).normalizationPullback U.ι
  have : IsIso E := inferInstance
  have hE : E ≫ pullback.snd (w ≫ U.ι).fromNormalization U.ι = w := by
    simp only [E, l, Category.assoc, Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization, pullback.lift_snd]
  let Y : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (w ≫ U.ι).fromNormalization
    ⟨inferInstance, inferInstance⟩
  refine ⟨Y, ⟨MorphismProperty.Over.isoMk (asIso E).symm ?_⟩⟩
  change inv E ≫ w = pullback.snd (w ≫ U.ι).fromNormalization U.ι
  rw [IsIso.inv_comp_eq, hE]

end Scheme

end SGA.SGA1.ExposeX
