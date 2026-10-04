/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.SGA1.ExposeX.PurityDenseOpen
import SGA.SGA1.ExposeXIII.KunnethAbhyankar

/-!
# SGA 1, XIII.4.6 in characteristic `0`: Abhyankar's lemma on a chart of a covering curve

The curve case of the resolution-free route to XIII.4.6 in characteristic `0`
(`AffineLineOpenInvarianceStatement`) extends an étale covering `w : W' ⟶ f⁻¹(U)` over a normal
integral scheme `T` finite over a curve `P` by the purity theorem
`SGA.SGA1.ExposeX.finite_etale_fromNormalization_of_isRegularScheme`, whose local hypothesis is,
on an affine chart `f⁻¹(O)` with `Γ(P, O) ≅ k[X]` and `U = D(g₀) ⊆ O`: the normalization of
`Γ(T, f⁻¹ O)` in `Γ(W')` is étale at the primes over height-one primes containing `g₀`. This file
checks that hypothesis (`isEtaleAt_integralClosure_chart`) when `W'` is the pullback of a finite
étale covering `Z` of `U` and the function field of `T` contains, for every root `b` of `g₀`, an
`N`-th root of `X - b` up to a unit (`N` divisible by `1, …, rank Z`): this is the ring-level
Abhyankar lemma `SGA.SGA1.ExposeXIII.isEtaleAt_integralClosure_of_pow_eq_mul`, once
`Γ(W') = Γ(f⁻¹U) ⊗_{Γ(U)} Γ(Z)` (flat base change,
`AlgebraicGeometry.CohomologyAux.isPushout_app_of_isPullback`) and `Γ(f⁻¹ U) = Γ(f⁻¹ O)[1/g₀]`.

* `mem_adjoin_range_of_isPushout`: the fourth vertex of a pushout of commutative rings is
  generated over one corner by the image of the other.
* `appLE_eq_of_eq`: `appLE` of equal morphisms.
* `isEtaleAt_integralClosure_chart`: the local hypothesis of the purity theorem on a chart.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace SGA.SGA1.ExposeXIII.KummerCompactification

/-- The fourth vertex `D` of a pushout square of commutative rings `R → A`, `R → B`, `A → D`,
`B → D` is generated, as an `A`-algebra, by the image of `B`. -/
lemma mem_adjoin_range_of_isPushout {R A B D : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ D} {inr : B ⟶ D} (h : IsPushout f g inl inr) (d : D) :
    letI := inl.hom.toAlgebra
    d ∈ Algebra.adjoin A (Set.range inr) := by
  let := inl.hom.toAlgebra
  let D₀ := Algebra.adjoin A (Set.range inr)
  let a : A ⟶ CommRingCat.of D₀ := CommRingCat.ofHom (algebraMap A D₀)
  let b : B ⟶ CommRingCat.of D₀ := CommRingCat.ofHom
    ((inr.hom).codRestrict D₀.toSubring fun x ↦ Algebra.subset_adjoin ⟨x, rfl⟩)
  let i : CommRingCat.of D₀ ⟶ D := CommRingCat.ofHom D₀.val.toRingHom
  have hw : f ≫ a = g ≫ b := by
    ext x
    exact congr($(h.w).hom x)
  have hd : h.desc a b hw ≫ i = 𝟙 D := by
    refine h.hom_ext ?_ ?_
    · rw [h.inl_desc_assoc, Category.comp_id]
      rfl
    · rw [h.inr_desc_assoc, Category.comp_id]
      rfl
  have : d = (h.desc a b hw d : D) := (congr($(hd).hom d)).symm
  rw [this]
  exact (h.desc a b hw d).2

/-- `f.appLE U V e` only depends on the morphism `f` up to equality. -/
lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- XIII.5.2 in dimension one on a chart of a covering curve (the local hypothesis of the purity
theorem `SGA.SGA1.ExposeX.finite_etale_fromNormalization_of_isRegularScheme`). Let `k` be
algebraically closed of characteristic `0`, `f : T ⟶ P` finite with `T` integral and normal,
`O ⊆ P` affine with `φ : k[X] ≃ Γ(P, O)`, `g₀ ∈ k[X]`, `U = D(φ g₀) ⊆ O` with `f⁻¹ U` nonempty,
`p : Z ⟶ U` finite étale and `W'` (with `pW : W' ⟶ Z`, `w : W' ⟶ f⁻¹ U`) a pullback of `p` along
`f⁻¹ U ⟶ U`. Suppose every `m` with `0 < m ≤ rank_{Γ(U)} Γ(Z)` divides `N`, and that for every
root `b` of `g₀` there are `y ∈ Γ(f⁻¹ U)` and `v ∈ k[X]` with `v(b) ≠ 0` and
`y^N · f^*φ(v) = f^*φ(X - b)` on `f⁻¹ U`. Then, with `S = Γ(T, f⁻¹ O)` and
`D = Γ(W', (w ≫ ι)⁻¹(f⁻¹ O))`, the normalization of `S` in `D` is étale over `S` at every prime
lying over a height-one prime of `S` that contains `f^*φ(g₀)`. -/
theorem isEtaleAt_integralClosure_chart [IsAlgClosed k] [CharZero k] {P T Z : Scheme.{u}}
    (f : T ⟶ P) [IsFinite f] [IsIntegral T] (hT : ExposeX.IsNormalScheme T)
    {O : P.Opens} (hO : IsAffineOpen O) (φ : k[X] ≃+* Γ(P, O)) (g₀ : k[X])
    {U : P.Opens} (hUO : U ≤ O) (hU : P.basicOpen (φ g₀) = U)
    (hne : (f ⁻¹ᵁ U : Set T).Nonempty)
    (p : Z ⟶ U.toScheme) [IsFinite p] [Etale p] {W' : Scheme.{u}} {pW : W' ⟶ Z}
    {w : W' ⟶ (f ⁻¹ᵁ U).toScheme} (hpb : IsPullback pW w p (f ∣_ U)) (N : ℕ)
    (hN : ∀ m, 0 < m → m ≤ (letI := (p.appLE ⊤ ⊤ le_top).hom.toAlgebra;
      Module.finrank Γ(U.toScheme, ⊤) Γ(Z, ⊤)) → m ∣ N)
    (hy : ∀ b : k, g₀.IsRoot b → ∃ (y : Γ((f ⁻¹ᵁ U).toScheme, ⊤)) (v : k[X]), ¬ v.IsRoot b ∧
      y ^ N * ((f ⁻¹ᵁ U).ι ≫ f).appLE O ⊤ (fun x _ ↦ hUO x.2) (φ v) =
        ((f ⁻¹ᵁ U).ι ≫ f).appLE O ⊤ (fun x _ ↦ hUO x.2) (φ (X - C b))) :
    letI := ((w ≫ (f ⁻¹ᵁ U).ι).app (f ⁻¹ᵁ O)).hom.toAlgebra
    ∀ (q : Ideal (integralClosure Γ(T, f ⁻¹ᵁ O)
        Γ(W', (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O))))
      [q.IsPrime], f.app O (φ g₀) ∈ q.comap (algebraMap Γ(T, f ⁻¹ᵁ O) _) →
        (q.comap (algebraMap Γ(T, f ⁻¹ᵁ O) _)).height = 1 →
          Algebra.IsEtaleAt Γ(T, f ⁻¹ᵁ O) q := by
  intro q _ hq hq1
  have hU''V : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ O := f.preimage_mono hUO
  have hV : IsAffineOpen (f ⁻¹ᵁ O) := hO.preimage f
  have hU''eq : T.basicOpen (f.app O (φ g₀)) = f ⁻¹ᵁ U := by rw [← Scheme.preimage_basicOpen, hU]
  have : Nonempty (f ⁻¹ᵁ O) := ⟨⟨hne.some, hU''V hne.some_mem⟩⟩
  -- the elements `y` in the function field `L` of `S = Γ(f⁻¹ O)`
  obtain ⟨L, _, _, _⟩ : ∃ (L : Type u) (_ : Field L) (_ : Algebra Γ(T, f ⁻¹ᵁ O) L),
      IsFractionRing Γ(T, f ⁻¹ᵁ O) L :=
    ⟨FractionRing Γ(T, f ⁻¹ᵁ O), inferInstance, inferInstance, inferInstance⟩
  have ht0 : f.app O (φ g₀) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hne
    rw [← hU''eq, h0, Scheme.basicOpen_zero] at hx
    exact hx
  have htL : IsUnit (algebraMap Γ(T, f ⁻¹ᵁ O) L (f.app O (φ g₀))) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr ht0).isUnit
  have hy' : ∀ b : k, g₀.IsRoot b → ∃ (y : L) (v : k[X]),
      ¬ v.IsRoot b ∧ y ^ N * algebraMap Γ(T, f ⁻¹ᵁ O) L (f.app O (φ v)) =
        algebraMap Γ(T, f ⁻¹ᵁ O) L (f.app O (φ (X - C b))) := by
    have he : (f ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ f ⁻¹ᵁ O := by rw [Scheme.Opens.ι_image_top]; exact hU''V
    let : Algebra Γ(T, f ⁻¹ᵁ O) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
      (T.presheaf.map (homOfLE he).op).hom.toAlgebra
    have : IsLocalization.Away (f.app O (φ g₀)) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
      hV.isLocalization_of_eq_basicOpen _ (homOfLE he)
        (by rw [Scheme.Opens.ι_image_top, hU''eq])
    have hlam : ∀ a : k[X], IsLocalization.Away.lift (f.app O (φ g₀)) htL
        (((f ⁻¹ᵁ U).ι ≫ f).appLE O ⊤ (fun x _ ↦ hUO x.2) (φ a)) =
          algebraMap Γ(T, f ⁻¹ᵁ O) L (f.app O (φ a)) := by
      intro a
      rw [Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
      exact IsLocalization.Away.lift_eq (f.app O (φ g₀)) htL (f.app O (φ a))
    intro b hb
    obtain ⟨y, v, hv, hyv⟩ := hy b hb
    refine ⟨IsLocalization.Away.lift (f.app O (φ g₀)) htL y, v, hv, ?_⟩
    rw [← hlam, ← hlam, ← map_pow, ← map_mul, hyv]
  let := ((w ≫ (f ⁻¹ᵁ U).ι).app (f ⁻¹ᵁ O)).hom.toAlgebra
  have hUaff : IsAffineOpen U := hU ▸ hO.basicOpen (φ g₀)
  have : IsAffine U.toScheme := hUaff
  have : IsAffine Z := isAffine_of_isAffineHom p
  -- the chart ring `S = Γ(X, f⁻¹ O)`, finite over `k[X]`, a normal domain
  let : Algebra k[X] Γ(T, f ⁻¹ᵁ O) := ((f.app O).hom.comp φ.toRingHom).toAlgebra
  have : Module.Finite k[X] Γ(T, f ⁻¹ᵁ O) :=
    (IsFinite.finite_app f O hO).comp (RingHom.Finite.of_surjective _ φ.surjective)
  have : IsIntegrallyClosed Γ(T, f ⁻¹ᵁ O) := ExposeX.isIntegrallyClosed_of_isAffineOpen hT hV
  -- `t = f^* φ(g₀)` is a unit on the covering
  have hg₀ : IsUnit (algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
      (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O))
      (algebraMap k[X] Γ(T, f ⁻¹ᵁ O) g₀)) := by
    have e : (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O) ≤
        (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ T.basicOpen (f.app O (φ g₀)) := by
      have htop : (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
        rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
      rw [hU''eq, htop]
      exact le_top
    have h1 : algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
        (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O))
        (algebraMap k[X] Γ(T, f ⁻¹ᵁ O) g₀) =
        (w ≫ (f ⁻¹ᵁ U).ι).appLE (T.basicOpen (f.app O (φ g₀))) _ e
          (T.presheaf.map (homOfLE (T.basicOpen_le (f.app O (φ g₀)))).op (f.app O (φ g₀))) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      change ((w ≫ (f ⁻¹ᵁ U).ι).app (f ⁻¹ᵁ O)) _ = _
      rw [Scheme.Hom.app_eq_appLE]
      rfl
    rw [h1]
    exact (T.toRingedSpace.isUnit_res_basicOpen (f.app O (φ g₀))).map _
  -- `P₀ = Γ(U) = k[X][1/g₀]`
  have hle : ⊤ ≤ U.ι ⁻¹ᵁ O := fun x _ ↦ hUO x.2
  let : Algebra k[X] Γ(U.toScheme, ⊤) := ((U.ι.appLE O ⊤ hle).hom.comp φ.toRingHom).toAlgebra
  have : IsLocalization.Away g₀ Γ(U.toScheme, ⊤) := by
    have hle' : U.ι ''ᵁ ⊤ ≤ O := by rw [Scheme.Opens.ι_image_top]; exact hUO
    let : Algebra Γ(P, O) Γ(U.toScheme, ⊤) := (P.presheaf.map (homOfLE hle').op).hom.toAlgebra
    have : IsLocalization.Away (φ g₀) Γ(U.toScheme, ⊤) :=
      hO.isLocalization_of_eq_basicOpen (φ g₀) (homOfLE hle')
        (by rw [Scheme.Opens.ι_image_top, hU])
    have h := IsLocalization.isLocalization_of_base_ringEquiv
      (Submonoid.powers (φ g₀)) Γ(U.toScheme, ⊤) φ.symm
    rw [Submonoid.map_powers, RingEquiv.symm_apply_apply] at h
    convert h
    · rw [Scheme.Opens.ι_appLE]
      rfl
    · exact (RingEquiv.symm_symm φ).symm
  -- `W₀ = Γ(Z)`, finite étale over `P₀`
  let : Algebra Γ(U.toScheme, ⊤) Γ(Z, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.toAlgebra
  have : Module.Finite Γ(U.toScheme, ⊤) Γ(Z, ⊤) := by
    have h := IsFinite.finite_app p ⊤ (isAffineOpen_top _)
    rw [Scheme.Hom.app_eq_appLE] at h
    exact h
  have : Algebra.Etale Γ(U.toScheme, ⊤) Γ(Z, ⊤) :=
    HasRingHomProperty.appLE @Etale p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩
      le_top
  -- the map `ι : Γ(Z) → Γ(Z ×_U f⁻¹U)`
  let ι := ((pW).appLE ⊤
    ((w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) le_top).hom
  have hcomm : pW ≫ p ≫ U.ι =
      w ≫ (f ⁻¹ᵁ U).ι ≫ f := by
    rw [reassoc_of% hpb.w, morphismRestrict_ι]
  have hι : ∀ a : k[X], ι (algebraMap Γ(U.toScheme, ⊤) Γ(Z, ⊤)
      (algebraMap k[X] Γ(U.toScheme, ⊤) a)) =
      algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
        (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O))
        (algebraMap k[X] Γ(T, f ⁻¹ᵁ O) a) := by
    intro a
    change ((U.ι.appLE O ⊤ hle ≫ p.appLE ⊤ ⊤ le_top ≫
      (pW).appLE ⊤ _ le_top)) (φ a) =
        (f.app O ≫ (w ≫ (f ⁻¹ᵁ U).ι).app (f ⁻¹ᵁ O)) (φ a)
    congr 1
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE f,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq (by rw [Category.assoc, hcomm, Category.assoc] :
        (pW ≫ p) ≫ U.ι = (w ≫ (f ⁻¹ᵁ U).ι) ≫ f)]
  -- the inverse of `t` in `D` comes from `W₀`
  have hinv : algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
        (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) (f.app O (φ g₀)) *
      ι (algebraMap Γ(U.toScheme, ⊤) Γ(Z, ⊤) (IsLocalization.Away.invSelf g₀)) = 1 := by
    rw [show f.app O (φ g₀) = algebraMap k[X] Γ(T, f ⁻¹ᵁ O) g₀ from rfl, ← hι, ← map_mul,
      ← map_mul, IsLocalization.Away.mul_invSelf, map_one, map_one]
  -- `D = Γ(f⁻¹U) ⊗_{Γ(U)} Γ(Z)` (flat base change), and `Γ(f⁻¹U) = S[1/t]`
  have : IsFinite (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹_›
  have hpush := CohomologyAux.isPushout_app_of_isPullback
    hpb.flip (isAffineOpen_top U.toScheme)
    (isAffineOpen_top Z) le_top
  have hloc : ∀ a : Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ ⊤), ∃ (s : Γ(T, f ⁻¹ᵁ O)) (n : ℕ),
      a * (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ O) ((f ∣_ U) ⁻¹ᵁ ⊤) (fun x _ ↦ hU''V x.2)
        (f.app O (φ g₀) ^ n) =
        (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ O) ((f ∣_ U) ⁻¹ᵁ ⊤) (fun x _ ↦ hU''V x.2) s := by
    intro a
    have he : (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ ⊤) ≤ f ⁻¹ᵁ O := by
      rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]; exact hU''V
    let : Algebra Γ(T, f ⁻¹ᵁ O) Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ ⊤) :=
      (T.presheaf.map (homOfLE he).op).hom.toAlgebra
    have : IsLocalization.Away (f.app O (φ g₀)) Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ ⊤) :=
      hV.isLocalization_of_eq_basicOpen _ (homOfLE he)
        (by rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top, hU''eq])
    obtain ⟨⟨s, _, n, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (f.app O (φ g₀))) a
    refine ⟨s, n, ?_⟩
    rw [Scheme.Opens.ι_appLE]
    exact hs
  have hDop : (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O) ≤
      (pW) ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]; exact le_top
  have hDop' : (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O) =
      (pW) ⁻¹ᵁ ⊤ := by
    refine le_antisymm hDop ?_
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_top]
    intro x _
    exact hU''V (w x).2
  have hgen : ∀ c, c ∈ Algebra.adjoin Γ(T, f ⁻¹ᵁ O) (Set.range ι) := by
    intro c
    obtain ⟨c', rfl⟩ := (Scheme.bijective_presheaf_map_of_eq hDop hDop').2 c
    have hc' := mem_adjoin_range_of_isPushout hpush c'
    induction hc' using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      refine Algebra.subset_adjoin ⟨b, ?_⟩
      change _ = ((pW).app ⊤ ≫ _) b
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    | algebraMap a =>
      change ((w).appLE _ _ _ ≫ _) a ∈ _
      rw [Scheme.Hom.appLE_map]
      obtain ⟨s, n, hs⟩ := hloc a
      have h1 := congrArg ((w).appLE ((f ∣_ U) ⁻¹ᵁ ⊤)
        ((w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) (by
          rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]; exact le_top)) hs
      rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_eq_app] at h1
      set ιinv := ι (algebraMap Γ(U.toScheme, ⊤) Γ(Z, ⊤) (IsLocalization.Away.invSelf g₀))
      have h2 : algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
          (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) (f.app O (φ g₀) ^ n) *
          ιinv ^ n = 1 := by
        rw [map_pow, ← mul_pow, hinv, one_pow]
      have key : ((w).appLE ((f ∣_ U) ⁻¹ᵁ ⊤)
          ((w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) (by
            rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]; exact le_top)) a =
          algebraMap Γ(T, f ⁻¹ᵁ O) Γ(W',
            (w ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ (f ⁻¹ᵁ O)) s * ιinv ^ n := by
        rw [← mul_one (((w).appLE _ _ _) a), ← h2, ← mul_assoc]
        exact congrArg (· * ιinv ^ n) h1
      rw [key]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _)
    | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  exact isEtaleAt_integralClosure_of_pow_eq_mul g₀ hg₀ Γ(U.toScheme, ⊤) Γ(Z, ⊤) ι hι hgen N hN
    L hy' q hq hq1

end SGA.SGA1.ExposeXIII.KummerCompactification
