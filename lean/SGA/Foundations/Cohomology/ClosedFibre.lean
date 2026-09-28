/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Formal.AdicRing

/-!
# Proper schemes over a complete base: `π₀` of the closed fibre

Let `A` be a noetherian ring, `I`-adically complete, and `f : X ⟶ Spec A` proper. By the theorem
on formal functions over a complete base (EGA III 4.1.7, `toFormalLimit_bijective`),
`Γ(X, 𝒪_X) = lim_n Γ(X, 𝒪_X / I^{n+1})`, so idempotents lift from the formal neighbourhood of
`W = f⁻¹ V(I)` (`exists_idempotent_separating`). Consequently (the `π₀` part of SGA 1 IX.1.10 and
X.2.1, which rest on EGA III 5.1.4):

* `existsUnique_isClopen_inter_eq`: every relatively clopen subset of `W` is the trace of a unique
  clopen subset of `X`;
* `isConnected_zeroLocusPreimage`: if `X` is connected, so is `W`;
* `connectedSpace_pullback_of_surjective`, `AlgebraicGeometry.connectedSpace_closedFibre`: the
  closed fibre `X ×_A A/I` (resp. `X ×_A k` for `A` complete local) of a connected `X` is
  connected;
* `existsUnique_isClopen_preimage_pullback_fst`,
  `AlgebraicGeometry.existsUnique_isClopen_preimage_closedFibre`: clopen subsets of the closed
  fibre are the preimages of unique clopen subsets of `X`.

Together with the local constancy of the degree of a finite étale covering, the last statement
gives the full faithfulness of `X' ↦ X' ×_X X₀` on étale coverings (SGA 1 IX.1.10): a morphism
`X' ⟶ X''` of coverings of `X` is a clopen subset of `X' ×_X X''` of degree one over `X'`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section ZeroLocus

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

lemma mem_zeroLocusPreimage_iff (x : X) :
    x ∈ zeroLocusPreimage I f ↔ I ≤ (f x).asIdeal := by
  refine forall₂_congr fun a _ ↦ ?_
  have e : X.basicOpen (f.specStructureRingHom a) =
      f ⁻¹ᵁ (Spec A).basicOpen ((Scheme.ΓSpecIso A).inv a) :=
    (Scheme.preimage_basicOpen f _).symm
  rw [e, basicOpen_eq_of_affine]
  change ¬ ¬ (a ∈ (f x).asIdeal) ↔ _
  exact not_not

/-- For `q : A → B` surjective with kernel `I`, the underlying set of `X ×_{Spec A} Spec B` is
`f⁻¹ V(I)`. -/
lemma range_pullback_fst_of_surjective {B : CommRingCat.{u}} (q : A ⟶ B)
    (hq : Function.Surjective q.hom) (hI : RingHom.ker q.hom = I) :
    Set.range (Limits.pullback.fst f (Spec.map q)) = zeroLocusPreimage I f := by
  rw [Scheme.Pullback.range_fst]
  have hr : Set.range (Spec.map q) = PrimeSpectrum.zeroLocus (I : Set A) :=
    (range_comap_of_surjective _ _ hq).trans (by rw [hI])
  ext x
  rw [mem_zeroLocusPreimage_iff, Set.mem_preimage, hr]
  exact Iff.rfl

end ZeroLocus

section Clopen

/-- The basic open set of an idempotent global section is clopen. -/
lemma isClopen_basicOpen_of_isIdempotentElem {W : Scheme.{u}} {e : Γ(W, ⊤)}
    (he : IsIdempotentElem e) : IsClopen ((W.basicOpen e : W.Opens) : Set W) := by
  have hgerm : ∀ x : W, W.presheaf.germ ⊤ x trivial e = 0 ∨ W.presheaf.germ ⊤ x trivial e = 1 :=
    fun x ↦ eq_zero_or_one_of_isIdempotentElem (he.map (W.presheaf.germ ⊤ x trivial).hom)
  refine ⟨?_, (W.basicOpen e).isOpen⟩
  have : ((W.basicOpen e : W.Opens) : Set W) = ((W.basicOpen (1 - e) : W.Opens) : Set W)ᶜ := by
    ext x
    rw [Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe,
      Scheme.mem_basicOpen W (U := ⊤) e x trivial,
      Scheme.mem_basicOpen W (U := ⊤) (1 - e) x trivial, map_sub, map_one]
    rcases hgerm x with h | h <;> simp [h]
  rw [this]
  exact (W.basicOpen (1 - e)).isOpen.isClosed_compl

end Clopen

section Complete

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

/-- **Over a complete base, `Hᵖ(X, M) → lim_n Hᵖ(X, M / I^{n+1} M)` is bijective** (EGA III
4.1.7): `Hᵖ(X, M)` is finite, hence `I`-adically complete, and the theorem on formal functions
identifies the limit with its completion. -/
theorem toFormalLimit_bijective (M : X.Modules) [M.IsCoherent] (p : ℕ) :
    Function.Bijective (M.toFormalLimit f I p) := by
  let _ := M.moduleOver f p ⊤
  have : Module.Finite A (M.H p) := properFinitenessStatement A X f M p
  have hc : IsAdicComplete I (M.H p) := IsAdicComplete.of_finite I (M.H p)
  have hof := AdicCompletion.of_bijective_iff.mpr hc
  obtain ⟨e, he⟩ := formalFunctionsStatement A I X f M p
  have h : ⇑(M.toFormalLimit f I p) = e ∘ AdicCompletion.of I (M.H p) :=
    funext fun x ↦ (he x).symm
  rw [h]
  exact e.bijective.comp hof

/-- **Idempotents lift from `f⁻¹ V(I)`** (a consequence of EGA III 4.1.7): over an `I`-adically
complete noetherian base, a decomposition of `f⁻¹ V(I)` into two disjoint closed pieces is
induced by an idempotent of `Γ(X, 𝒪_X)`. -/
theorem exists_idempotent_separating (G₁ G₂ : Set X) (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)
    (hcov : zeroLocusPreimage I f ⊆ G₁ ∪ G₂)
    (hdisj : ∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∉ G₂) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∈ X.basicOpen e) ∧
      (∀ x ∈ zeroLocusPreimage I f, x ∈ G₂ → x ∉ X.basicOpen e) := by
  obtain ⟨z, hcompat, hz₁, hz₂⟩ := exists_separatingFamily I f hG₁ hG₂ hcov hdisj
  let O := unitModule X
  have : O.IsCoherent := isCoherent_unitModule X
  have hbij := toFormalLimit_bijective I f O 0
  obtain ⟨y, hy⟩ := hbij.2 ⟨_, mem_formalLimit_of_compat z hcompat⟩
  let a : Γ(X, ⊤) := Scheme.Modules.H.equiv₀ _ y
  have ha : ∀ n, (O.toQuotientIdealPow f I n).app ⊤ a = z n := by
    intro n
    have h := congrArg (fun w : O.formalLimit f I 0 ↦ w.1 n) hy
    simp only at h
    rw [← equiv₀_H'_map_toQuotientIdealPow]
    change Scheme.Modules.H.equiv₀ _ ((O.toFormalLimit f I 0 y).1 n) = _
    rw [h]
    exact (Scheme.Modules.H.equiv₀ _).apply_symm_apply _
  have hcov' := sepOpen_cover hG₁ hG₂ hdisj
  -- `a • z n = z n`
  have hsmul : ∀ n, a • z n = z n := by
    intro n
    refine TopCat.Sheaf.eq_of_locally_eq₂ (O.quotientIdealPow f I n).toAbSheaf
      (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤) (homOfLE le_top : sepOpen₂ I f hG₁ ⟶ ⊤) hcov' _ _
      ?_ ?_
    · change (O.quotientIdealPow f I n).presheaf.map _ (a • z n) =
        (O.quotientIdealPow f I n).presheaf.map _ (z n)
      let s : Γ(O, sepOpen₁ hG₂) := (1 : Γ(X, sepOpen₁ hG₂))
      have h1 := Scheme.Modules.Hom.app_smul (O.toQuotientIdealPow f I n)
        (X.presheaf.map (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op a) s
      rw [Scheme.Modules.map_smul, hz₁]
      refine h1.symm.trans ?_
      have h2 : X.presheaf.map (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op a • s =
          O.presheaf.map (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op a :=
        mul_one (X.presheaf.map (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op a)
      rw [h2, hom_app_presheaf_map, ha]
      exact hz₁ n
    · change (O.quotientIdealPow f I n).presheaf.map _ (a • z n) =
        (O.quotientIdealPow f I n).presheaf.map _ (z n)
      rw [Scheme.Modules.map_smul, hz₂, smul_zero]
  have hidem : IsIdempotentElem a := by
    apply (Scheme.Modules.H.equiv₀ O).symm.injective
    apply hbij.1
    refine Subtype.ext (funext fun n ↦ ?_)
    apply (Scheme.Modules.H.equiv₀ _).injective
    change Scheme.Modules.H.equiv₀ _ (Scheme.Modules.H'.map (O.toQuotientIdealPow f I n) 0 ⊤
      ((Scheme.Modules.H.equiv₀ O).symm (a * a))) =
      Scheme.Modules.H.equiv₀ _ (Scheme.Modules.H'.map (O.toQuotientIdealPow f I n) 0 ⊤
      ((Scheme.Modules.H.equiv₀ O).symm a))
    have hs : ∀ c, Scheme.Modules.H.equiv₀ (unitModule X) ((Scheme.Modules.H.equiv₀ O).symm c) =
        c := fun c ↦ (Scheme.Modules.H.equiv₀ O).apply_symm_apply c
    rw [equiv₀_H'_map_toQuotientIdealPow, equiv₀_H'_map_toQuotientIdealPow]
    erw [hs, hs]
    change (O.toQuotientIdealPow f I n).app ⊤ (a • a) = _
    let t : Γ(O, ⊤) := a
    have h3 := Scheme.Modules.Hom.app_smul (O.toQuotientIdealPow f I n) a t
    have h4 : (O.toQuotientIdealPow f I n).app ⊤ t = z n := ha n
    refine h3.trans ?_
    rw [h4, hsmul]
  exact ⟨a, hidem, separating_of_toQuotientIdealPow_eq hG₁ hG₂ hdisj (z 0) (hz₁ 0) (hz₂ 0) a
    (ha 0)⟩

omit [IsNoetherianRing A] [IsProper f] in
/-- Over an `I`-adically complete base, a nonempty `D ⊆ X` with closed image in `Spec A` meets
`f⁻¹ V(I)`: `I` lies in the Jacobson radical of `A`, hence in the maximal ideal of a closed point
of `f(D)`. -/
lemma exists_mem_zeroLocusPreimage_of_isClosed_image {D : Set X} (hD : IsClosed (f '' D))
    (hne : D.Nonempty) : ∃ x ∈ D, x ∈ zeroLocusPreimage I f := by
  obtain ⟨p, ⟨x, hx, rfl⟩, hp⟩ := hD.exists_closed_singleton (hne.image f)
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hp
  exact ⟨x, hx, (mem_zeroLocusPreimage_iff I f x).mpr
    ((IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hmax⟩))⟩

omit [IsNoetherianRing A] in
/-- Over an `I`-adically complete base, every nonempty closed subset of `X` proper over `Spec A`
meets `f⁻¹ V(I)`. -/
lemma exists_mem_zeroLocusPreimage_of_isClosed {D : Set X} (hD : IsClosed D) (hne : D.Nonempty) :
    ∃ x ∈ D, x ∈ zeroLocusPreimage I f :=
  exists_mem_zeroLocusPreimage_of_isClosed_image I f (f.isClosedMap D hD) hne

omit [IsNoetherianRing A] in
/-- Over an `I`-adically complete base, `f⁻¹ V(I)` is nonempty for `X` nonempty and
proper over `Spec A`. -/
lemma nonempty_zeroLocusPreimage [Nonempty X] : (zeroLocusPreimage I f).Nonempty := by
  obtain ⟨x, -, hx⟩ :=
    exists_mem_zeroLocusPreimage_of_isClosed I f isClosed_univ Set.univ_nonempty
  exact ⟨x, hx⟩

omit [IsNoetherianRing A] in
/-- Over an `I`-adically complete base, a clopen subset of `X` proper over `Spec A` is determined
by its trace on `f⁻¹ V(I)`. -/
lemma eq_of_isClopen_of_inter_eq {U U' : Set X} (hU : IsClopen U) (hU' : IsClopen U')
    (h : U ∩ zeroLocusPreimage I f = U' ∩ zeroLocusPreimage I f) : U = U' := by
  have key : ∀ {U U' : Set X}, IsClopen U → IsClopen U' →
      U ∩ zeroLocusPreimage I f = U' ∩ zeroLocusPreimage I f → U ⊆ U' := by
    intro U U' hU hU' h x hx
    by_contra hx'
    obtain ⟨y, ⟨hyU, hyU'⟩, hyW⟩ := exists_mem_zeroLocusPreimage_of_isClosed I f
      (hU.isClosed.inter hU'.compl.isClosed) ⟨x, hx, hx'⟩
    exact hyU' ((Set.ext_iff.mp h y).mp ⟨hyU, hyW⟩).1
  exact (key hU hU' h).antisymm (key hU' hU h.symm)

/-- **Connectedness of `f⁻¹ V(I)` over a complete base** (SGA 1 IX.1.10, X.2.1; via EGA III
4.1.7): for `A` noetherian and `I`-adically complete and `X` connected and proper over `Spec A`,
`f⁻¹ V(I)` is preconnected: a decomposition into two disjoint closed pieces lifts to an idempotent
of `Γ(X, 𝒪_X)` (`exists_idempotent_separating`), which is trivial. -/
theorem isPreconnected_zeroLocusPreimage [ConnectedSpace X] :
    _root_.IsPreconnected (zeroLocusPreimage I f) := by
  rw [isPreconnected_closed_iff]
  intro G₁ G₂ hG₁ hG₂ hcov ⟨x₁, hx₁W, hx₁G⟩ ⟨x₂, hx₂W, hx₂G⟩
  by_contra hne
  have hdisj : ∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∉ G₂ :=
    fun x hx h₁ h₂ ↦ hne ⟨x, hx, h₁, h₂⟩
  obtain ⟨e, he, h₁, h₂⟩ := exists_idempotent_separating I f G₁ G₂ hG₁ hG₂ hcov hdisj
  have h₁' := h₁ x₁ hx₁W hx₁G
  have h₂' := h₂ x₂ hx₂W hx₂G
  rcases trivialIdempotents_of_connectedSpace X e he with rfl | rfl
  · rw [Scheme.basicOpen_zero] at h₁'
    exact h₁'
  · rw [Scheme.basicOpen_one] at h₂'
    exact h₂' trivial

/-- **Connectedness of `f⁻¹ V(I)` over a complete base**: `IsConnected` form. -/
theorem isConnected_zeroLocusPreimage [ConnectedSpace X] :
    _root_.IsConnected (zeroLocusPreimage I f) :=
  ⟨nonempty_zeroLocusPreimage I f, isPreconnected_zeroLocusPreimage I f⟩

/-- **Clopen subsets lift from `f⁻¹ V(I)`** (the `π₀` part of SGA 1 IX.1.10; via EGA III 4.1.7):
over an `I`-adically complete noetherian base, every relatively clopen subset `V` of `f⁻¹ V(I)`
is the trace of a unique clopen subset of `X`. -/
theorem existsUnique_isClopen_inter_eq (V : Set X) (hVW : V ⊆ zeroLocusPreimage I f)
    (hV : IsClosed V) (hV' : IsClosed (zeroLocusPreimage I f \ V)) :
    ∃! U : Set X, IsClopen U ∧ U ∩ zeroLocusPreimage I f = V := by
  obtain ⟨e, he, h₁, h₂⟩ := exists_idempotent_separating I f V (zeroLocusPreimage I f \ V) hV hV'
    (fun x hx ↦ by
      by_cases h : x ∈ V
      exacts [Or.inl h, Or.inr ⟨hx, h⟩])
    (fun x _ h₁ h₂ ↦ h₂.2 h₁)
  have hinter : (X.basicOpen e : Set X) ∩ zeroLocusPreimage I f = V := by
    ext x
    refine ⟨fun ⟨hxe, hxW⟩ ↦ ?_, fun hxV ↦ ⟨h₁ x (hVW hxV) hxV, hVW hxV⟩⟩
    by_contra hxV
    exact h₂ x hxW ⟨hxW, hxV⟩ hxe
  have hcl := isClopen_basicOpen_of_isIdempotentElem he
  exact ⟨_, ⟨hcl, hinter⟩, fun U hU ↦
    eq_of_isClopen_of_inter_eq I f hU.1 hcl (hU.2.trans hinter.symm)⟩

/-- **The closed fibre of a connected proper scheme over a complete base is connected** (SGA 1
IX.1.10, X.2.1; via EGA III 4.1.7): for `q : A → B` surjective with kernel `I`, `A`
noetherian and `I`-adically complete, and `X` connected and proper over `Spec A`, the scheme
`X ×_{Spec A} Spec B` is connected. -/
theorem connectedSpace_pullback_of_surjective [ConnectedSpace X] {B : CommRingCat.{u}}
    (q : A ⟶ B) (hq : Function.Surjective q.hom) (hI : RingHom.ker q.hom = I) :
    ConnectedSpace ↥(Limits.pullback (C := Scheme.{u}) f (Spec.map q)) := by
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_surjective q hq
  refine connectedSpace_of_isEmbedding
    (Limits.pullback.fst f (Spec.map q)).isClosedEmbedding.isEmbedding ?_
  rw [range_pullback_fst_of_surjective I f q hq hI]
  exact isConnected_zeroLocusPreimage I f

/-- **Clopen subsets lift from the closed fibre** (the `π₀` part of SGA 1 IX.1.10 / X.2.1; via EGA
III 4.1.7): for `q : A → B` surjective with kernel `I`, `A` noetherian and `I`-adically complete and
`X` proper over `Spec A`, every clopen subset of `X ×_{Spec A} Spec B` is the preimage of a unique
clopen subset of `X`. -/
theorem existsUnique_isClopen_preimage_pullback_fst {B : CommRingCat.{u}} (q : A ⟶ B)
    (hq : Function.Surjective q.hom) (hI : RingHom.ker q.hom = I)
    (V₀ : Set ↥(Limits.pullback (C := Scheme.{u}) f (Spec.map q))) (hV₀ : IsClopen V₀) :
    ∃! U : Set X, IsClopen U ∧ Limits.pullback.fst f (Spec.map q) ⁻¹' U = V₀ := by
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_surjective q hq
  set ι := Limits.pullback.fst f (Spec.map q)
  have hemb := ι.isClosedEmbedding
  have hr := range_pullback_fst_of_surjective I f q hq hI
  have hV' : zeroLocusPreimage I f \ ι '' V₀ = ι '' V₀ᶜ := by
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff hemb.injective, Set.image_univ, hr]
  obtain ⟨U, ⟨hU, hUV⟩, huniq⟩ := existsUnique_isClopen_inter_eq I f (ι '' V₀)
    (hr ▸ Set.image_subset_range _ _) (hemb.isClosedMap _ hV₀.isClosed)
    (hV' ▸ hemb.isClosedMap _ hV₀.compl.isClosed)
  have key : ∀ U : Set X, ι ⁻¹' U = V₀ ↔ U ∩ zeroLocusPreimage I f = ι '' V₀ := by
    intro U
    rw [← hr, ← Set.image_preimage_eq_inter_range]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ hemb.injective.image_injective h⟩
  exact ⟨U, ⟨hU, (key U).mpr hUV⟩, fun U' hU' ↦ huniq U' ⟨hU'.1, (key U').mp hU'.2⟩⟩

end Complete

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

/-- **The closed fibre of a connected proper scheme over a complete local ring is connected**
(SGA 1 X.2.1 / IX.1.10, the `π₀` part; via the theorem on formal functions, EGA III 4.1.7): for
`A` a complete noetherian local ring with residue field `k` and `X` connected and proper over
`Spec A`, the closed fibre `X₀ = X ×_A k` is connected. -/
theorem connectedSpace_closedFibre (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [ConnectedSpace X] :
    ConnectedSpace ↥(Limits.pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))) := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹_›
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) (CommRingCat.of A) := ‹_›
  exact connectedSpace_pullback_of_surjective (A := .of A) (IsLocalRing.maximalIdeal A) f _
    IsLocalRing.residue_surjective IsLocalRing.ker_residue


/-- **Clopen subsets lift from the closed fibre over a complete local ring** (the `π₀` part of
SGA 1 IX.1.10 / X.2.1): for `A` a complete noetherian local ring with residue field `k` and `X`
proper over `Spec A`, every clopen subset of the closed fibre `X₀ = X ×_A k` is the preimage of a
unique clopen subset of `X`. -/
theorem existsUnique_isClopen_preimage_closedFibre (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (V₀ : Set ↥(Limits.pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))))
    (hV₀ : IsClopen V₀) :
    ∃! U : Set X, IsClopen U ∧ Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)))) ⁻¹' U = V₀ := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹_›
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) (CommRingCat.of A) := ‹_›
  exact existsUnique_isClopen_preimage_pullback_fst (A := .of A) (IsLocalRing.maximalIdeal A) f _
    IsLocalRing.residue_surjective IsLocalRing.ker_residue V₀ hV₀

end AlgebraicGeometry
