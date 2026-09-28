/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.SectionRingMaps
import SGA.SGA1.ExposeVIII.Effectiveness

/-!
# SGA 1, Exposé VIII, 7.8: descent of schemes with a relatively ample line bundle

Let `g : S' ⟶ S` be faithfully flat and quasi-compact, `D` a descent datum on `X' ⟶ S'` and `L'` a
line bundle on `X'` ample relative to `S'`, endowed with a descent datum `E` relative to `D`
(`DescentDatum.LineBundleDatum`). Then `D` is effective, and `L'` descends to a line bundle on the
descended scheme, ample relative to `S` (VIII.7.8).

As in SGA (the proof of VIII.5.8), for `S = Spec A` and `S' = Spec A'` affine the descent datum on
`L'` defines a descent datum on the graded ring `Γ_*(L') = ⊕ₙ Γ(X', L'^{⊗n})`, which descends by
VIII.1 (`isPushout_eqLocus_of_descent`): `Γ_*(L') = A' ⊗_A Γ_*(L')^{inv}`, where the invariant
sections are those whose two inverse images to `X''` correspond under `E`. Hence every point of
`X'` lies in the non-vanishing locus `X'_s` of an invariant section `s` of a positive power of
`L'`; `X'_s` is stable under the descent datum and quasi-affine, so the descent datum is effective
by VIII.7.9 and VIII.7.2. The general case reduces to this one by VIII.7.3 and an fppf covering of
`S'` by an affine scheme, along which descent data on line bundles are transported.

## Main results

- `DescentDatum.LineBundleDatum.exists_isInvariant_of_isAffine`: over affine `S`, `S'`, invariant
  sections of `L'^{⊗m}` do not vanish at a point as soon as some section of `L'^{⊗m}` does not.
- `DescentDatum.LineBundleDatum.transport`: the inverse image of a descent datum on `L'` under a
  morphism of descent data (in particular `restrictBase`, `pullbackBase`).
- `DescentDatum.LineBundleDatum.isEffective`: VIII.7.8, effectiveness of `D`.

The descent of `L'` itself is in `SGA.SGA1.ExposeVIII.LineBundleDescent`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  Scheme.LineBundle

namespace SGA.SGA1.ExposeVIII.DescentDatum

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {D : DescentDatum g} {L' : D.X'.LineBundle}
  (E : D.LineBundleDatum L')

section Cocycle

set_option backward.isDefEq.respectTransparency false in
/-- On the diagonal (for `r` with `q₁ r = q₂ r`), the descent datum is the identity: its diagonal
components are `1`. -/
lemma LineBundleDatum.φ_self_of_diag {T : Scheme.{u}} {x : T ⟶ D.X'} (r : T ⟶ D.X'')
    (h₁ : r ≫ D.q₁ = x) (h₂ : r ≫ D.q₂ = x) (i : L'.ι) :
    (E.iso.pullbackOfEq r h₁ h₂).φ i i = 1 := by
  subst h₁
  have hc := E.cocycle r r r h₂ rfl rfl i i i
  have hO : (L'.pullback (r ≫ D.q₁)).U i ⊓ (L'.pullback (r ≫ D.q₁)).U i ≤
      D.cocycleOpen L' r r i i i := by
    change (r ≫ D.q₁) ⁻¹ᵁ L'.U i ⊓ (r ≫ D.q₁) ⁻¹ᵁ L'.U i ≤ _
    rw [cocycleOpen, h₂]
    exact le_inf (le_inf inf_le_left inf_le_left) inf_le_left
  have := congrArg (T.presheaf.map (homOfLE hO).op) hc
  simp only [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at this
  ext
  rw [Iso.coe_pullbackOfEq_φ, Units.val_one]
  have h3 : ∀ {W : T.Opens} (a : Γ(T, W)), IsUnit a → a = a * a → a = 1 := fun a ha h ↦ by
    have := congrArg (· * (ha.unit⁻¹).1) h
    simpa only [mul_assoc, ha.mul_val_inv, mul_one] using this.symm
  exact h3 _ ((E.iso.φ i i).isUnit.map _) this

set_option backward.isDefEq.respectTransparency false in
/-- On the diagonal, the descent datum acts as the identity on sections. -/
lemma LineBundleDatum.mapFam_diag {T : Scheme.{u}} {x : T ⟶ D.X'} (r : T ⟶ D.X'')
    (h₁ : r ≫ D.q₁ = x) (h₂ : r ≫ D.q₂ = x) {V : T.Opens} {n : ℕ} {s : (L'.pullback x).Fam V}
    (hs : (L'.pullback x).IsSection n V s) : (E.iso.pullbackOfEq r h₁ h₂).mapFam hs = s := by
  refine Iso.mapFam_eq_self _ (fun i j ↦ ?_) hs
  have hc := (E.iso.pullbackOfEq r h₁ h₂).compat_left i j j
  rw [E.φ_self_of_diag r h₁ h₂ j, Units.val_one, map_one, mul_one] at hc
  apply CohomologyAux.presheaf_map_injective_of_eq (show (L'.pullback x).U i ⊓
    (L'.pullback x).U j ⊓ (L'.pullback x).U j = (L'.pullback x).U i ⊓ (L'.pullback x).U j by
      rw [inf_assoc, inf_idem])
  rw [CohomologyAux.presheaf_map_map]
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- The transitivity condition, on the action on sections: `r''*φ = r'*φ ∘ r*φ`. -/
lemma LineBundleDatum.mapFam_cocycle {T : Scheme.{u}} (r r' r'' : T ⟶ D.X'')
    (hr : r ≫ D.q₂ = r' ≫ D.q₁) (h₁ : r'' ≫ D.q₁ = r ≫ D.q₁) (h₂ : r'' ≫ D.q₂ = r' ≫ D.q₂)
    {V : T.Opens} {n : ℕ} {s : (L'.pullback (r ≫ D.q₁)).Fam V}
    (hs : (L'.pullback (r ≫ D.q₁)).IsSection n V s) :
    (E.iso.pullbackOfEq r'' h₁ h₂).mapFam hs =
      (E.iso.pullbackOfEq r' hr.symm rfl).mapFam
        ((E.iso.pullbackOfEq r rfl rfl).isSection_mapFam hs) := by
  refine Iso.mapFam_comp _ _ _ (fun i j k ↦ ?_) hs
  have hc := E.cocycle r r' r'' hr h₁ h₂ i j k
  simp only [Iso.coe_pullbackOfEq_φ, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact hc

end Cocycle

section Rings

variable (D L')

/-- The graded ring `Γ_*(L')` of sections of the powers of `L'` over `X'`. -/
noncomputable abbrev ringC : CommRingCat.{u} :=
  CommRingCat.of ((L'.pullback (𝟙 D.X')).sectionRing Γ(D.X', ⊤))

/-- The graded ring `Γ_*(q₂*L')` over `X''`. -/
noncomputable abbrev ringR : CommRingCat.{u} :=
  CommRingCat.of ((L'.pullback D.q₂).sectionRing Γ(D.X'', ⊤))

/-- The graded ring `Γ_*(q₁*L')` over `X''`. -/
noncomputable abbrev ringR₁ : CommRingCat.{u} :=
  CommRingCat.of ((L'.pullback D.q₁).sectionRing Γ(D.X'', ⊤))

/-- The graded ring `Γ_*((pr₁ q₂)*L')` over `X''' = X'' ×_{q₂, X', q₁} X''`. -/
noncomputable abbrev ringQ₀ : CommRingCat.{u} :=
  CommRingCat.of ((L'.pullback (pullback.fst D.q₂ D.q₁ ≫ D.q₂)).sectionRing
    Γ(pullback D.q₂ D.q₁, ⊤))

/-- The graded ring `Γ_*((pr₂ q₂)*L')` over `X'''`. -/
noncomputable abbrev ringQ : CommRingCat.{u} :=
  CommRingCat.of ((L'.pullback (pullback.snd D.q₂ D.q₁ ≫ D.q₂)).sectionRing
    Γ(pullback D.q₂ D.q₁, ⊤))

/-- `Γ(S') → Γ_*(L')`. -/
noncomputable def mapA : Γ(S', ⊤) ⟶ D.ringC L' :=
  D.a.appTop ≫ CommRingCat.ofHom (algebraMap Γ(D.X', ⊤) _)

/-- `Γ(S'') → Γ_*(q₂*L')`. -/
noncomputable def mapB : Γ(pullback g g, ⊤) ⟶ D.ringR L' :=
  D.b.appTop ≫ CommRingCat.ofHom (algebraMap Γ(D.X'', ⊤) _)

/-- `Γ(S'') → Γ_*(q₁*L')`. -/
noncomputable def mapB₁ : Γ(pullback g g, ⊤) ⟶ D.ringR₁ L' :=
  D.b.appTop ≫ CommRingCat.ofHom (algebraMap Γ(D.X'', ⊤) _)

/-- The inverse image `q₂^* : Γ_*(L') → Γ_*(q₂*L')`. -/
noncomputable def mapQ₂ : D.ringC L' ⟶ D.ringR L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf D.q₂ (Category.comp_id _) _ _)

/-- The inverse image `q₁^* : Γ_*(L') → Γ_*(q₁*L')`. -/
noncomputable def mapQ₁u : D.ringC L' ⟶ D.ringR₁ L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf D.q₁ (Category.comp_id _) _ _)

/-- `pr₁^* : Γ_*(q₂*L') → Γ_*((pr₁ q₂)*L')`. -/
noncomputable def mapInl₀ : D.ringR L' ⟶ D.ringQ₀ L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf (pullback.fst D.q₂ D.q₁) rfl _ _)

/-- `pr₂^* : Γ_*(q₁*L') → Γ_*((pr₂ q₁)*L') = Γ_*((pr₁ q₂)*L')`. -/
noncomputable def mapInr₀ : D.ringR₁ L' ⟶ D.ringQ₀ L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf (pullback.snd D.q₂ D.q₁) pullback.condition.symm _ _)

/-- `pr₂^* : Γ_*(q₂*L') → Γ_*((pr₂ q₂)*L')`. -/
noncomputable def mapInr : D.ringR L' ⟶ D.ringQ L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf (pullback.snd D.q₂ D.q₁) rfl _ _)

/-- The inverse image along a section `Δ` of `q₂`. -/
noncomputable def mapδ {Δ : D.X' ⟶ D.X''} (hΔ : Δ ≫ D.q₂ = 𝟙 _) : D.ringR L' ⟶ D.ringC L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf Δ hΔ _ _)

/-- The inverse image along the composition `r'' : X''' ⟶ X''`. -/
noncomputable def mapτ {r'' : pullback D.q₂ D.q₁ ⟶ D.X''}
    (h : r'' ≫ D.q₂ = pullback.snd D.q₂ D.q₁ ≫ D.q₂) : D.ringR L' ⟶ D.ringQ L' :=
  CommRingCat.ofHom (L'.sectionRingMapOf r'' h _ _)

variable {D L'}

/-- The isomorphism `Γ_*(q₁*L') ≅ Γ_*(q₂*L')` induced by the descent datum. -/
noncomputable def LineBundleDatum.isoR : D.ringR₁ L' ≅ D.ringR L' :=
  (E.iso.sectionRingEquiv Γ(D.X'', ⊤)).toCommRingCatIso

/-- The twisted inverse image `E ∘ q₁^* : Γ_*(L') → Γ_*(q₂*L')`. -/
noncomputable def LineBundleDatum.mapQ₁ : D.ringC L' ⟶ D.ringR L' :=
  D.mapQ₁u L' ≫ E.isoR.hom

/-- The isomorphism `Γ_*((pr₁ q₂)*L') ≅ Γ_*((pr₂ q₂)*L')` induced by `pr₂^* E`. -/
noncomputable def LineBundleDatum.isoQ : D.ringQ₀ L' ≅ D.ringQ L' :=
  ((E.iso.pullbackOfEq (pullback.snd D.q₂ D.q₁) pullback.condition.symm rfl).sectionRingEquiv
    Γ(pullback D.q₂ D.q₁, ⊤)).toCommRingCatIso

/-- The twisted inverse image `pr₂^* E ∘ pr₁^* : Γ_*(q₂*L') → Γ_*((pr₂ q₂)*L')`. -/
noncomputable def LineBundleDatum.mapInl : D.ringR L' ⟶ D.ringQ L' :=
  D.mapInl₀ L' ≫ E.isoQ.hom

end Rings

section Equations

lemma mapQ₂_of (n : ℕ) (s : (L'.pullback (𝟙 D.X')).sectionSubmodule Γ(D.X', ⊤) n) :
    D.mapQ₂ L' (DirectSum.of _ n s) = DirectSum.of _ n
      ⟨L'.famPullbackOf D.q₂ (Category.comp_id _) D.q₂.preimage_top.ge s.1,
        s.2.famPullbackOf D.q₂ (Category.comp_id _) _⟩ :=
  sectionRingMapOf_of n s

lemma LineBundleDatum.mapQ₁_of (n : ℕ)
    (s : (L'.pullback (𝟙 D.X')).sectionSubmodule Γ(D.X', ⊤) n) :
    E.mapQ₁ (DirectSum.of _ n s) = DirectSum.of _ n
      ⟨E.iso.mapFam (s.2.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge),
        E.iso.isSection_mapFam _⟩ := by
  change E.iso.sectionRingHom (D.X''.presheaf.obj (op ⊤))
    (L'.sectionRingMapOf D.q₁ (Category.comp_id _) (D.X'.presheaf.obj (op ⊤))
      (D.X''.presheaf.obj (op ⊤)) (DirectSum.of _ n s)) = _
  rw [sectionRingMapOf_of, Iso.sectionRingHom_of]

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.w₁ :
    D.mapA L' ≫ E.mapQ₁ = (pullback.fst g g).appTop ≫ D.mapB L' := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  change E.iso.sectionRingHom (D.X''.presheaf.obj (op ⊤))
      (L'.sectionRingMapOf D.q₁ (Category.comp_id _) (D.X'.presheaf.obj (op ⊤))
        (D.X''.presheaf.obj (op ⊤)) (algebraMap (D.X'.presheaf.obj (op ⊤))
          ((L'.pullback (𝟙 D.X')).sectionRing (D.X'.presheaf.obj (op ⊤))) (D.a.appTop r))) =
    algebraMap (D.X''.presheaf.obj (op ⊤))
      ((L'.pullback D.q₂).sectionRing (D.X''.presheaf.obj (op ⊤)))
      (D.b.appTop ((pullback.fst g g).appTop r))
  rw [sectionRingMapOf_algebraMap (r' := D.q₁.appTop (D.a.appTop r)) _ rfl,
    Iso.sectionRingHom_algebraMap]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, D.isPullback₁.w]

set_option backward.isDefEq.respectTransparency false in
lemma mapQ₂_mapδ {Δ : D.X' ⟶ D.X''} (hΔ : Δ ≫ D.q₂ = 𝟙 _) :
    D.mapQ₂ L' ≫ D.mapδ L' hΔ = 𝟙 _ := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change L'.sectionRingMapOf _ _ _ _ (L'.sectionRingMapOf _ _ _ _ x) = x
  rw [sectionRingMapOf_comp, sectionRingMapOf_congr hΔ _ (Category.id_comp _),
    sectionRingMapOf_id]

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.mapQ₁_mapδ {Δ : D.X' ⟶ D.X''} (hΔ₁ : Δ ≫ D.q₁ = 𝟙 _)
    (hΔ₂ : Δ ≫ D.q₂ = 𝟙 _) : E.mapQ₁ ≫ D.mapδ L' hΔ₂ = 𝟙 _ := by
  refine CommRingCat.hom_ext (sectionRing_ringHom_ext fun n s ↦ ?_)
  change D.mapδ L' hΔ₂ (E.mapQ₁ (DirectSum.of _ n s)) = DirectSum.of _ n s
  rw [E.mapQ₁_of]
  change L'.sectionRingMapOf _ _ _ _ _ = _
  rw [sectionRingMapOf_of]
  congr 1
  refine Subtype.ext ?_
  change L'.famPullbackOf Δ hΔ₂ Δ.preimage_top.ge
    (E.iso.mapFam (s.2.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge)) = s.1
  rw [← Iso.mapFam_pullbackOfEq E.iso Δ hΔ₁ hΔ₂ Δ.preimage_top.ge
    (s.2.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge), E.mapFam_diag]
  rw [famPullbackOf_famPullbackOf]
  exact (famPullbackOf_congr hΔ₁ _ (Category.id_comp _) _ le_rfl s.1).trans
    (famPullbackOf_id' _ s.1)

set_option backward.isDefEq.respectTransparency false in
lemma mapQ₂_mapτ {r'' : pullback D.q₂ D.q₁ ⟶ D.X''}
    (h : r'' ≫ D.q₂ = pullback.snd D.q₂ D.q₁ ≫ D.q₂) :
    D.mapQ₂ L' ≫ D.mapτ L' h = D.mapQ₂ L' ≫ D.mapInr L' := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change L'.sectionRingMapOf _ _ _ _ (L'.sectionRingMapOf _ _ _ _ x) =
    L'.sectionRingMapOf _ _ _ _ (L'.sectionRingMapOf _ _ _ _ x)
  rw [sectionRingMapOf_comp, sectionRingMapOf_comp]
  exact sectionRingMapOf_congr h _ _ x

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.mapQ₁_mapτ {r'' : pullback D.q₂ D.q₁ ⟶ D.X''}
    (h₁ : r'' ≫ D.q₁ = pullback.fst D.q₂ D.q₁ ≫ D.q₁)
    (h₂ : r'' ≫ D.q₂ = pullback.snd D.q₂ D.q₁ ≫ D.q₂) :
    E.mapQ₁ ≫ D.mapτ L' h₂ = E.mapQ₁ ≫ E.mapInl := by
  refine CommRingCat.hom_ext (sectionRing_ringHom_ext fun n s ↦ ?_)
  change D.mapτ L' h₂ (E.mapQ₁ (DirectSum.of _ n s)) = E.mapInl (E.mapQ₁ (DirectSum.of _ n s))
  rw [E.mapQ₁_of]
  change L'.sectionRingMapOf _ _ _ _ (DirectSum.of _ n _) =
    (E.iso.pullbackOfEq _ _ _).sectionRingHom _ (L'.sectionRingMapOf _ _ _ _ (DirectSum.of _ n _))
  rw [sectionRingMapOf_of, sectionRingMapOf_of, Iso.sectionRingHom_of]
  congr 1
  refine Subtype.ext ?_
  set pr₁ := pullback.fst D.q₂ D.q₁
  set pr₂ := pullback.snd D.q₂ D.q₁
  have hx := s.2.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge
  have e₁ : L'.famPullbackOf r'' h₁ r''.preimage_top.ge
      (L'.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge s.1) =
      L'.famPullbackOf pr₁ rfl pr₁.preimage_top.ge
        (L'.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge s.1) := by
    rw [famPullbackOf_famPullbackOf, famPullbackOf_famPullbackOf]
    exact famPullbackOf_congr h₁ _ _ _ _ _
  have hz := hx.famPullbackOf pr₁ rfl pr₁.preimage_top.ge
  change L'.famPullbackOf r'' h₂ r''.preimage_top.ge (E.iso.mapFam hx) =
    (E.iso.pullbackOfEq pr₂ pullback.condition.symm rfl).mapFam
      ((E.iso.isSection_mapFam hx).famPullbackOf pr₁ rfl pr₁.preimage_top.ge)
  rw [← Iso.mapFam_pullbackOfEq E.iso r'' h₁ h₂ r''.preimage_top.ge hx,
    Iso.mapFam_congr _ _ hz e₁, E.mapFam_cocycle pr₁ pr₂ r'' pullback.condition h₁ h₂ hz]
  exact Iso.mapFam_congr _ _ _ (Iso.mapFam_pullbackOfEq E.iso pr₁ rfl rfl _ hx)

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.mapInr₀_isoQ :
    D.mapInr₀ L' ≫ E.isoQ.hom = E.isoR.hom ≫ D.mapInr L' := by
  refine CommRingCat.hom_ext (sectionRing_ringHom_ext fun n s ↦ ?_)
  change (E.iso.pullbackOfEq _ _ _).sectionRingHom _ (L'.sectionRingMapOf _ _ _ _
      (DirectSum.of _ n s)) =
    L'.sectionRingMapOf _ _ _ _ (E.iso.sectionRingHom _ (DirectSum.of _ n s))
  rw [sectionRingMapOf_of, Iso.sectionRingHom_of, Iso.sectionRingHom_of, sectionRingMapOf_of]
  congr 1
  exact Subtype.ext (Iso.mapFam_pullbackOfEq E.iso _ _ rfl _ s.2)

end Equations

section Pushouts

variable [IsAffine S] [IsAffine S'] [Flat g] [CompactSpace D.X'] [QuasiSeparatedSpace D.X']

include L' in
lemma isPushout_mapQ₂ :
    IsPushout (D.mapA L') (pullback.snd g g).appTop (D.mapQ₂ L') (D.mapB L') :=
  L'.isPushout_sectionRingMapOf' (𝟙 D.X') D.isPullback₂ (Category.comp_id _)

include L' in
lemma isPushout_mapQ₁u :
    IsPushout (D.mapA L') (pullback.fst g g).appTop (D.mapQ₁u L') (D.mapB₁ L') :=
  L'.isPushout_sectionRingMapOf' (𝟙 D.X') D.isPullback₁ (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
include L' in
lemma isPushout_mapQ₂_mapQ₁u [CompactSpace D.X''] [QuasiSeparatedSpace D.X''] :
    IsPushout (D.mapQ₂ L') (D.mapQ₁u L') (D.mapInl₀ L') (D.mapInr₀ L') := by
  have hT : IsPullback (pullback.fst D.q₂ D.q₁) (pullback.snd D.q₂ D.q₁ ≫ D.b) (D.q₂ ≫ D.a)
      (pullback.fst g g) := (IsPullback.of_hasPullback D.q₂ D.q₁).paste_vert D.isPullback₁
  have outer := L'.isPushout_sectionRingMapOf' D.q₂ hT rfl
  have e₁ : (D.q₂ ≫ D.a).appTop ≫ CommRingCat.ofHom (algebraMap Γ(D.X'', ⊤)
      ((L'.pullback D.q₂).sectionRing Γ(D.X'', ⊤))) = D.mapA L' ≫ D.mapQ₂ L' := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    exact (sectionRingMapOf_algebraMap (L := L') (t := D.q₂) (hc := Category.comp_id _)
      (D.a.appTop r) ((D.q₂ ≫ D.a).appTop r) (by rw [Scheme.Hom.comp_appTop]; rfl)).symm
  have e₂ : (pullback.snd D.q₂ D.q₁ ≫ D.b).appTop ≫ CommRingCat.ofHom (algebraMap
      Γ(pullback D.q₂ D.q₁, ⊤) ((L'.pullback (pullback.fst D.q₂ D.q₁ ≫ D.q₂)).sectionRing
        Γ(pullback D.q₂ D.q₁, ⊤))) = D.mapB₁ L' ≫ D.mapInr₀ L' := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    exact (sectionRingMapOf_algebraMap (L := L') (t := pullback.snd D.q₂ D.q₁)
      (hc := pullback.condition.symm) (D.b.appTop r)
      ((pullback.snd D.q₂ D.q₁ ≫ D.b).appTop r) (by rw [Scheme.Hom.comp_appTop]; rfl)).symm
  rw [e₁, e₂] at outer
  refine outer.of_left ?_ (isPushout_mapQ₁u (L' := L'))
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change L'.sectionRingMapOf _ _ _ _ (L'.sectionRingMapOf _ _ _ _ x) =
    L'.sectionRingMapOf _ _ _ _ (L'.sectionRingMapOf _ _ _ _ x)
  rw [sectionRingMapOf_comp, sectionRingMapOf_comp]
  exact sectionRingMapOf_congr pullback.condition _ _ x

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.isPushout_mapQ₂_mapQ₁ [CompactSpace D.X''] [QuasiSeparatedSpace D.X''] :
    IsPushout (D.mapQ₂ L') E.mapQ₁ E.mapInl (D.mapInr L') :=
  (isPushout_mapQ₂_mapQ₁u (L' := L')).of_iso (CategoryTheory.Iso.refl _)
    (CategoryTheory.Iso.refl _) E.isoR E.isoQ (by simp) (by simp [LineBundleDatum.mapQ₁])
    (by simp [LineBundleDatum.mapInl]) E.mapInr₀_isoQ

end Pushouts

section Invariant

/-- A section `s` of `L'^{⊗n}` over `X'` (seen as a section of `(𝟙 X')*L'`) is invariant under
the descent datum `E` if its two inverse images by `q₁` and `q₂` correspond under `E`. -/
def LineBundleDatum.IsInvariant {n : ℕ} {s : (L'.pullback (𝟙 D.X')).Fam ⊤}
    (hs : (L'.pullback (𝟙 D.X')).IsSection n ⊤ s) : Prop :=
  E.iso.mapFam (hs.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge) =
    L'.famPullbackOf D.q₂ (Category.comp_id _) D.q₂.preimage_top.ge s

lemma LineBundleDatum.isInvariant_one
    (h : (L'.pullback (𝟙 D.X')).IsSection ((0 : ℕ) : ℤ) ⊤ 1) : E.IsInvariant h := by
  have h' : (L'.pullback D.q₁).IsSection ((0 : ℕ) : ℤ) ⊤ ((L'.pullback D.q₁).famConst ⊤ 1) :=
    (isSection_famConst (L := L'.pullback D.q₁) 1).of_eq Nat.cast_zero.symm
  rw [LineBundleDatum.IsInvariant, Iso.mapFam_congr _ _ h' (by rw [map_one, map_one]),
    Iso.mapFam_famConst, map_one, map_one]

lemma LineBundleDatum.IsInvariant.mul {m n : ℕ} {s t : (L'.pullback (𝟙 D.X')).Fam ⊤}
    {hs : (L'.pullback (𝟙 D.X')).IsSection m ⊤ s} {ht : (L'.pullback (𝟙 D.X')).IsSection n ⊤ t}
    (h₁ : E.IsInvariant hs) (h₂ : E.IsInvariant ht) :
    E.IsInvariant ((hs.mul ht).of_eq (Nat.cast_add m n).symm) := by
  have hs₁ := hs.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge
  have ht₁ := ht.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge
  have e := E.iso.mapFam_mul hs₁ ht₁
  unfold LineBundleDatum.IsInvariant at h₁ h₂ ⊢
  refine (E.iso.mapFam_congr _ ((hs₁.mul ht₁).of_eq (Nat.cast_add m n).symm)
    (map_mul _ s t)).trans ?_
  rw [e, h₁, h₂]
  exact (map_mul _ s t).symm

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.isInvariant_of_mapQ₁_eq {c : D.ringC L'}
    (hc : E.mapQ₁ c = D.mapQ₂ L' c) (k : ℕ) : E.IsInvariant (c k).2 := by
  have h := congrArg (fun z : D.ringR L' ↦ ((z k : (L'.pullback D.q₂).sectionSubmodule _ k) :
    (L'.pullback D.q₂).Fam ⊤)) hc
  change ((E.iso.sectionRingHom _ (L'.sectionRingMapOf _ _ _ _ c)) k).1 =
    ((L'.sectionRingMapOf _ _ _ _ c) k).1 at h
  simp only [Iso.sectionRingHom, sectionRingMapOf, sectionRingHom_apply] at h
  exact h

end Invariant

section Core

set_option backward.isDefEq.respectTransparency false in
/-- The key step of VIII.7.8 over an affine base: for `S`, `S'` affine, `g` faithfully flat and
`X'` quasi-compact and quasi-separated, if some section of `L'^{⊗m}` does not vanish at `x`,
then some section of `L'^{⊗m}` invariant under the descent datum `E` does not vanish at `x`.
By VIII.1 (`isPushout_eqLocus_of_descent`) applied to the graded ring `Γ_*(L')`, the invariant
sections generate `Γ_*(L')` over `Γ(S')`. -/
theorem LineBundleDatum.exists_isInvariant_of_isAffine [IsAffine S] [IsAffine S'] [Flat g]
    [Surjective g] [CompactSpace D.X'] [QuasiSeparatedSpace D.X'] (x : D.X') {m : ℕ}
    {t : (L'.pullback (𝟙 D.X')).Fam ⊤} (ht : (L'.pullback (𝟙 D.X')).IsSection m ⊤ t)
    (hx : x ∈ (L'.pullback (𝟙 D.X')).famLocus ⊤ t) :
    ∃ (s : (L'.pullback (𝟙 D.X')).Fam ⊤) (hs : (L'.pullback (𝟙 D.X')).IsSection m ⊤ s),
      E.IsInvariant hs ∧ x ∈ (L'.pullback (𝟙 D.X')).famLocus ⊤ s := by
  classical
  have : IsAffineHom D.q₁ :=
    MorphismProperty.of_isPullback D.isPullback₁.flip (isAffineHom_of_isAffine _)
  have : CompactSpace D.X'' := QuasiCompact.compactSpace_of_compactSpace D.q₁
  have : QuasiSeparatedSpace D.X'' := quasiSeparatedSpace_of_quasiSeparated D.q₁
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := D.refl (𝟙 D.X')
  obtain ⟨r'', hr₁, hr₂⟩ :=
    D.trans (pullback.fst D.q₂ D.q₁) (pullback.snd D.q₂ D.q₁) pullback.condition
  have hg : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨‹_›, ‹_›⟩
  have hP := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g g)
  have hpush := isPushout_eqLocus_of_descent g.appTop hg (D.mapA L') _ _ hP (D.mapB L')
    E.mapQ₁ (D.mapQ₂ L') E.w₁ (isPushout_mapQ₂ (D := D) (L' := L')) (D.mapδ L' hΔ₂)
    (E.mapQ₁_mapδ hΔ₁ hΔ₂) (mapQ₂_mapδ hΔ₂) E.mapInl (D.mapInr L') E.isPushout_mapQ₂_mapQ₁
    (D.mapτ L' hr₂) (E.mapQ₁_mapτ hr₁ hr₂) (mapQ₂_mapτ hr₂)
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpush
  let Good : ℕ → Prop := fun k ↦ ∃ (s : (L'.pullback (𝟙 D.X')).Fam ⊤)
    (hs : (L'.pullback (𝟙 D.X')).IsSection k ⊤ s),
      E.IsInvariant hs ∧ x ∈ (L'.pullback (𝟙 D.X')).famLocus ⊤ s
  have good0 : Good 0 := by
    have h1 : (L'.pullback (𝟙 D.X')).IsSection ((0 : ℕ) : ℤ) ⊤ 1 :=
      SetLike.GradedOne.one_mem (A := (L'.pullback (𝟙 D.X')).sectionSubmodule Γ(D.X', ⊤))
    refine ⟨1, h1, E.isInvariant_one h1, ?_⟩
    rw [famLocus_of_isUnit isUnit_one]
    trivial
  have goodmul (i j : ℕ) (hi : Good i) (hj : Good j) : Good (i + j) := by
    obtain ⟨s, hs, hsi, hxs⟩ := hi
    obtain ⟨s', hs', hsi', hxs'⟩ := hj
    refine ⟨s * s', (hs.mul hs').of_eq (Nat.cast_add i j).symm, hsi.mul E hsi', ?_⟩
    rw [famLocus_mul _ hs']
    exact ⟨hxs, hxs'⟩
  have key : ∀ y, y ∈ (⊤ : Subring (D.ringC L')) →
      ∀ k, x ∈ (L'.pullback (𝟙 D.X')).famLocus ⊤ (y k).1 → Good k := by
    rw [← hcl]
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      intro k hk
      rcases hy with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · by_cases h0 : k = 0
        · subst h0
          exact good0
        · exfalso
          change x ∈ (L'.pullback (𝟙 D.X')).famLocus ⊤
            ((algebraMap _ (D.ringC L') (D.a.appTop b)) k).1 at hk
          rw [DirectSum.algebraMap_apply, DirectSum.of_eq_of_ne _ _ _ h0] at hk
          simp only [ZeroMemClass.coe_zero, famLocus_zero] at hk
          exact hk
      · exact ⟨_, _, E.isInvariant_of_mapQ₁_eq c.2 k, hk⟩
    | zero =>
      intro k hk
      simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero, famLocus_zero] at hk
      exact hk.elim
    | one =>
      intro k hk
      by_cases h0 : k = 0
      · subst h0
        exact good0
      · exfalso
        rw [DirectSum.one_def, DirectSum.of_eq_of_ne _ _ _ h0] at hk
        simp only [ZeroMemClass.coe_zero, famLocus_zero] at hk
        exact hk
    | add y z _ _ hy hz =>
      intro k hk
      rw [DirectSum.add_apply, Submodule.coe_add] at hk
      rcases famLocus_add_le _ _ hk with hk | hk
      exacts [hy k hk, hz k hk]
    | neg y _ hy =>
      intro k hk
      rw [DFinsupp.neg_apply, Submodule.coe_neg, famLocus_neg] at hk
      exact hy k hk
    | mul y z _ _ hy hz =>
      intro k hk
      rw [DirectSum.coe_mul_apply] at hk
      obtain ⟨ij, hij, hk⟩ := Opens.mem_iSup.mp (famLocus_sum_le _ _ hk) |>.imp fun ij h ↦
        Opens.mem_iSup.mp h
      rw [Finset.mem_filter] at hij
      rw [famLocus_mul _ (z ij.2).2] at hk
      rw [← hij.2]
      exact goodmul _ _ (hy _ hk.1) (hz _ hk.2)
  refine key (DirectSum.of _ m ⟨t, ht⟩) (Subring.mem_top _) m ?_
  rwa [DirectSum.of_eq_same]

end Core

section Transport

variable {S₁ S₁' : Scheme.{u}} {g₁ : S₁' ⟶ S₁} (D₁ : DescentDatum g₁) {ρ : D₁.X' ⟶ D.X'}
  {ρ'' : D₁.X'' ⟶ D.X''} (h₁ : ρ'' ≫ D.q₁ = D₁.q₁ ≫ ρ) (h₂ : ρ'' ≫ D.q₂ = D₁.q₂ ≫ ρ)

/-- The isomorphism `q₁*ρ*L' ≅ q₂*ρ*L'` induced on `X''₁` by a descent datum on `L'` and a morphism
of descent data `(ρ, ρ'')`: the inverse image of `φ` under `ρ''`. -/
noncomputable def LineBundleDatum.transportIso :
    ((L'.pullback ρ).pullback D₁.q₁).Iso ((L'.pullback ρ).pullback D₁.q₂) :=
  Iso.ofPullbackComp (E.iso.pullbackOfEq ρ'' h₁ h₂)

include h₁ h₂ in
/-- The inclusion of opens underlying `transportIso`. -/
lemma transportIso_le (i j : L'.ι) :
    D₁.q₁ ⁻¹ᵁ (L'.pullback ρ).U i ⊓ D₁.q₂ ⁻¹ᵁ (L'.pullback ρ).U j ≤
      ρ'' ⁻¹ᵁ (D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U j) := by
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h₁, h₂]
  exact le_rfl

lemma LineBundleDatum.coe_transportIso_φ (i j : L'.ι) :
    ((E.transportIso D₁ h₁ h₂).φ i j).1 =
      ρ''.appLE (D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U j)
        (D₁.q₁ ⁻¹ᵁ (L'.pullback ρ).U i ⊓ D₁.q₂ ⁻¹ᵁ (L'.pullback ρ).U j)
        (transportIso_le D₁ h₁ h₂ i j) (E.iso.φ i j).1 :=
  rfl

lemma LineBundleDatum.coe_transportIso_φ' (i j : L'.ι) :
    ((E.transportIso D₁ h₁ h₂).φ i j).1 =
      ρ''.appLE ((L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U j)
        (((L'.pullback ρ).pullback D₁.q₁).U i ⊓ ((L'.pullback ρ).pullback D₁.q₂).U j)
        (transportIso_le D₁ h₁ h₂ i j) (E.iso.φ i j).1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a descent datum on `L'` under a morphism of descent data
`(ρ, ρ'') : (X'₁, X''₁) ⟶ (X', X'')`: the descent datum `ρ''*φ` on `ρ*L'`. -/
noncomputable def LineBundleDatum.transport : D₁.LineBundleDatum (L'.pullback ρ) where
  iso := E.transportIso D₁ h₁ h₂
  cocycle T r r' r'' hr e₁ e₂ i j k := by
    have hc := E.cocycle (r ≫ ρ'') (r' ≫ ρ'') (r'' ≫ ρ'')
      (by simp only [Category.assoc, h₁, h₂]; rw [reassoc_of% hr])
      (by simp only [Category.assoc, h₁]; rw [reassoc_of% e₁])
      (by simp only [Category.assoc, h₂]; rw [reassoc_of% e₂]) i j k
    have hO : D₁.cocycleOpen (L'.pullback ρ) r r' i j k ≤
        D.cocycleOpen L' (r ≫ ρ'') (r' ≫ ρ'') i j k := by
      have e : D.cocycleOpen L' (r ≫ ρ'') (r' ≫ ρ'') i j k = (r ≫ D₁.q₁ ≫ ρ) ⁻¹ᵁ L'.U i ⊓
          (r ≫ D₁.q₂ ≫ ρ) ⁻¹ᵁ L'.U j ⊓ (r' ≫ D₁.q₂ ≫ ρ) ⁻¹ᵁ L'.U k := by
        simp only [cocycleOpen, Category.assoc, h₁, h₂]
      rw [e]
      exact le_rfl
    have := congrArg (T.presheaf.map (homOfLE hO).op) hc
    simp only [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at this
    simp only [E.coe_transportIso_φ, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact this

lemma LineBundleDatum.transport_iso : (E.transport D₁ h₁ h₂).iso = E.transportIso D₁ h₁ h₂ :=
  rfl

end Transport

section Restrictions

/-- The descent datum induced by `E` on the inverse image of an open subset `V` of `S`
(VIII.7.3). -/
noncomputable def LineBundleDatum.restrictBase (V : S.Opens) :
    (D.restrictBase V).LineBundleDatum (L'.pullback (D.a ⁻¹ᵁ g ⁻¹ᵁ V).ι) :=
  E.transport (D.restrictBase V) (ρ'' := (D.q₁ ⁻¹ᵁ (D.a ⁻¹ᵁ g ⁻¹ᵁ V)).ι)
    (morphismRestrict_ι _ _).symm (D.restrictQ₂_ι (D.isStable_preimage_preimage V)).symm

/-- The descent datum induced by `E` on `X' ×_{S'} S₁`, for `π : S₁ ⟶ S'`. -/
noncomputable def LineBundleDatum.pullbackBase {S₁ : Scheme.{u}} (π : S₁ ⟶ S') :
    (D.pullbackBase π).LineBundleDatum (L'.pullback (pullback.fst D.a π)) :=
  E.transport (D.pullbackBase π) (ρ'' := pullback.fst D.b (pullbackBaseπ'' π))
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm

/-- The inverse image of a relatively ample line bundle on the inverse image of an open subset
of `S` is relatively ample (EGA II 4.6.13 (iii)). -/
lemma isRelativelyAmple_restrictBase (hL : L'.IsRelativelyAmple D.a) (V : S.Opens) :
    (L'.pullback (D.a ⁻¹ᵁ g ⁻¹ᵁ V).ι).IsRelativelyAmple (D.restrictBase V).a :=
  hL.of_isPullback (isPullback_morphismRestrict D.a (g ⁻¹ᵁ V)).flip

end Restrictions

section Effective

/-- The non-vanishing locus of an invariant section is stable under the descent datum. -/
lemma LineBundleDatum.isStable_famLocus {n : ℕ} {s : (L'.pullback (𝟙 D.X')).Fam ⊤}
    {hs : (L'.pullback (𝟙 D.X')).IsSection n ⊤ s} (hinv : E.IsInvariant hs) :
    D.IsStable ((L'.pullback (𝟙 D.X')).famLocus ⊤ s) := by
  have h₁ := famLocus_famPullbackOf (L := L') D.q₁ (Category.comp_id _)
    D.q₁.preimage_top.ge s
  have h₂ := famLocus_famPullbackOf (L := L') D.q₂ (Category.comp_id _)
    D.q₂.preimage_top.ge s
  have h₃ := E.iso.famLocus_mapFam
    (hs.famPullbackOf D.q₁ (Category.comp_id _) D.q₁.preimage_top.ge)
  rw [LineBundleDatum.IsInvariant] at hinv
  rw [hinv, h₁, h₂, top_inf_eq, top_inf_eq] at h₃
  exact congrArg (fun U : D.X''.Opens ↦ (U : Set D.X'')) h₃.symm

include E in
set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.8, effectiveness over affine bases: for `S`, `S'` affine, `g` faithfully flat and `L'`
ample, every point of `X'` lies in the non-vanishing locus of an invariant section of a positive
power of `L'`, which is stable and quasi-affine; hence `D` is effective by VIII.7.9 and
VIII.7.2. -/
theorem LineBundleDatum.isEffective_of_isAffine [IsAffine S] [IsAffine S'] [Flat g] [Surjective g]
    (hL : L'.IsAmple) : D.IsEffective := by
  have := hL.1
  have := hL.quasiSeparatedSpace
  have hM : (L'.pullback (𝟙 D.X')).IsAmple := hL.pullback (𝟙 D.X')
  have H (x : D.X') : ∃ (U : D.X'.Opens) (hU : D.IsStable U), x ∈ U ∧
      (D.restrict hU).IsEffective := by
    obtain ⟨n, hn, t, hxt, -⟩ := hM.2 x
    obtain ⟨s, hs, hinv, hxs⟩ :=
      E.exists_isInvariant_of_isAffine x t.isSection_toFam (by rwa [t.famLocus_toFam])
    have : ((L'.pullback (𝟙 D.X')).famLocus ⊤ s).toScheme.IsQuasiAffine := by
      have := hM.isQuasiAffine_secLocus (R := Γ(D.X', ⊤)) (ofIsSection_mem s hs) hn
      rwa [secLocus, coeFam_ofIsSection] at this
    exact ⟨_, E.isStable_famLocus hinv, hxs,
      (D.restrict (E.isStable_famLocus hinv)).isEffective_of_isQuasiAffine_of_isAffine⟩
  choose U hU hxU hUe using H
  exact (D.isEffective_iff_forall_isEffective_restrict U hU
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩)).mpr hUe

include E in
set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.8, effectiveness: for `g` faithfully flat and quasi-compact, a descent datum on an
`X'` endowed with a line bundle `L'` ample relative to `S'` and with a descent datum `E` on `L'`
is effective. VIII.7.3 reduces this to affine `S`, and then to affine `S'` by replacing `S'`
with a finite disjoint union of affine open subsets
(`isEffective_of_isEffective_pullbackBase`). -/
theorem LineBundleDatum.isEffective [Surjective g] [Flat g] [QuasiCompact g]
    (hL : L'.IsRelativelyAmple D.a) : D.IsEffective := by
  refine (D.isEffective_iff_forall_isEffective_restrictBase (fun V : S.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top S)).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  have : Flat (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : Surjective (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : QuasiCompact (g ∣_ V.1) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : CompactSpace (g ⁻¹ᵁ V.1) := QuasiCompact.compactSpace_of_compactSpace (g ∣_ V.1)
  have hL₁ := isRelativelyAmple_restrictBase hL V.1
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (g ⁻¹ᵁ V.1).toScheme.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : MorphismProperty.ContainsIdentities @LocallyOfFinitePresentation :=
    ⟨fun _ ↦ inferInstance⟩
  have : LocallyOfFinitePresentation π :=
    IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFinitePresentation _ _ π hπ
  have : Surjective π := hπs
  have : IsAffine S₁ := hS₁
  refine (D.restrictBase V.1).isEffective_of_isEffective_pullbackBase π ?_
  exact ((E.restrictBase V.1).pullbackBase π).isEffective_of_isAffine
    (hL₁.of_isPullback (IsPullback.of_hasPullback _ π)).isAmple

end Effective

end SGA.SGA1.ExposeVIII.DescentDatum
