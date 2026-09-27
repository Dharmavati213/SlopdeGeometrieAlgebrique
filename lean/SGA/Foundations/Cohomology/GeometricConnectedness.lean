/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.Foundations.Cohomology.TrivialIdempotents
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness of the fibres (Zariski, geometric form)

`CohomologyAux.geometricallyConnected_of_isIso_app` (EGA III 4.3.4; Stacks Tag 0BUI): for
`f : X ⟶ Y` proper, `Y` locally noetherian and `𝒪_Y ≅ f_* 𝒪_X`, the morphism `f` is
`GeometricallyConnected` (mathlib's notion: `X ×_Y Spec K` is connected for every field `K` over
`Y`); `connectedSpace_pullback_of_isIso_app` is the statement for a single `Spec K ⟶ Y`.

Ingredients:
* `flat_fromSpecStalk`: `Spec 𝒪_{Y,y} ⟶ Y` is flat;
* `trivialIdempotents_of_connectedSpace`, `connectedSpace_of_trivialIdempotents`: a non-empty
  scheme is connected iff `Γ(𝒪)` has only trivial idempotents;
* `trivialIdempotents_pullback_iff`: `Γ(Z_K, 𝒪) = Γ(Z, 𝒪) ⊗_k K` for `Z` qcqs over a field `k`
  (flat base change);
* `connectedSpace_pullback_adjoinRoot`: for a finite separable (indeed any) simple extension
  `L = κ(y)[t]/(p)`, `X_y ⊗ L` is the fibre of the flat base change
  `X ×_Y Spec 𝒪_{Y,y}[t]/(P) ⟶ Spec 𝒪_{Y,y}[t]/(P)` over a point, hence connected by Zariski's
  theorem (`zariskiConnectednessStatement`) and flat base change for `f_* 𝒪_X`
  (`isIso_app_pullback_snd`);
* the algebra of `SGA.Foundations.Cohomology.TrivialIdempotents` then gives every field `K`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.CohomologyAux

section Stalk

/-- `Spec 𝒪_{X,x} ⟶ X` is flat (a localization followed by an open immersion). -/
instance flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hxU, -⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [Flat.SpecMap_iff]
    let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  infer_instance

end Stalk

section Connected

lemma eq_zero_or_one_of_isIdempotentElem {R : Type*} [CommRing R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (sub_eq_zero.mp (h.mul_right_eq_zero.mp h0)).symm
  · exact Or.inl (h.mul_left_eq_zero.mp h0)

variable (W : Scheme.{u})

/-- On a connected scheme, `Γ(W, 𝒪_W)` has only trivial idempotents. -/
lemma trivialIdempotents_of_connectedSpace [ConnectedSpace W] :
    TrivialIdempotents Γ(W, ⊤) := by
  intro e he
  -- the germs of `e` are `0` or `1`
  have hgerm : ∀ x : W, W.presheaf.germ ⊤ x trivial e = 0 ∨ W.presheaf.germ ⊤ x trivial e = 1 :=
    fun x ↦ eq_zero_or_one_of_isIdempotentElem (he.map (W.presheaf.germ ⊤ x trivial).hom)
  have hU : IsClopen ((W.basicOpen e : W.Opens) : Set W) := by
    refine ⟨?_, (W.basicOpen e).isOpen⟩
    have : ((W.basicOpen e : W.Opens) : Set W) = ((W.basicOpen (1 - e) : W.Opens) : Set W)ᶜ := by
      ext x
      rw [Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe,
        Scheme.mem_basicOpen W (U := ⊤) e x trivial,
        Scheme.mem_basicOpen W (U := ⊤) (1 - e) x trivial, map_sub, map_one]
      rcases hgerm x with h | h <;> simp [h]
    rw [this]
    exact (W.basicOpen (1 - e)).isOpen.isClosed_compl
  rcases isClopen_iff.mp hU with h | h
  · left
    refine TopCat.Presheaf.section_ext W.sheaf ⊤ e 0 fun x _ ↦ ?_
    rw [map_zero]
    rcases hgerm x with h' | h'
    · exact h'
    · have : x ∈ ((W.basicOpen e : W.Opens) : Set W) := by
        rw [SetLike.mem_coe, Scheme.mem_basicOpen W (U := ⊤) e x trivial, h']
        exact isUnit_one
      rw [h] at this
      exact this.elim
  · right
    refine TopCat.Presheaf.section_ext W.sheaf ⊤ e 1 fun x _ ↦ ?_
    rw [map_one]
    rcases hgerm x with h' | h'
    · have : x ∈ ((W.basicOpen e : W.Opens) : Set W) := h ▸ Set.mem_univ x
      rw [SetLike.mem_coe, Scheme.mem_basicOpen W (U := ⊤) e x trivial, h'] at this
      exact absurd this not_isUnit_zero
    · exact h'

/-- Gluing two functions on an open cover `X = U₁ ∪ U₂`. -/
lemma exists_glue₂_sections {U₁ U₂ : W.Opens} (hcov : ⊤ ≤ U₁ ⊔ U₂) (s₁ : Γ(W, U₁))
    (s₂ : Γ(W, U₂))
    (h : W.presheaf.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op s₁ =
      W.presheaf.map (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op s₂) :
    ∃ s : Γ(W, ⊤), W.presheaf.map (homOfLE le_top : U₁ ⟶ ⊤).op s = s₁ ∧
      W.presheaf.map (homOfLE le_top : U₂ ⟶ ⊤).op s = s₂ := by
  have key : ∀ (V : W.Opens) (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂),
      W.presheaf.map (homOfLE hV₁).op s₁ = W.presheaf.map (homOfLE hV₂).op s₂ := by
    intro V hV₁ hV₂
    have e₁ : (homOfLE hV₁).op = (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op ≫
        (homOfLE (le_inf hV₁ hV₂)).op := rfl
    have e₂ : (homOfLE hV₂).op = (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op ≫
        (homOfLE (le_inf hV₁ hV₂)).op := rfl
    rw [e₁, e₂, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, h]
  let U : Bool → W.Opens := fun b ↦ cond b U₁ U₂
  let sf : ∀ b, Γ(W, U b) := fun b ↦ Bool.rec (motive := fun b ↦ Γ(W, U b)) s₂ s₁ b
  have hc : TopCat.Presheaf.IsCompatible W.sheaf.1 U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (key _ inf_le_right inf_le_left).symm
    · exact key _ inf_le_left inf_le_right
    · rfl
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' W.sheaf U ⊤
    (fun _ ↦ homOfLE le_top) (by
      refine hcov.trans (sup_le ?_ ?_)
      · exact le_iSup U true
      · exact le_iSup U false) sf hc
  exact ⟨t, ht true, ht false⟩

/-- A non-empty scheme whose ring of global functions has only trivial idempotents is connected
(a clopen decomposition gives the idempotent `1` on one piece and `0` on the other). -/
lemma connectedSpace_of_trivialIdempotents [Nonempty W] (h : TrivialIdempotents Γ(W, ⊤)) :
    ConnectedSpace W := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs ↦ ?_⟩
  let U : W.Opens := ⟨s, hs.isOpen⟩
  let V : W.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have hcov : ⊤ ≤ U ⊔ V := fun x _ ↦ by
    rw [Opens.mem_sup]
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · exact Or.inr hx
  have hUV : U ⊓ V = ⊥ := le_bot_iff.mp fun x hx ↦ hx.2 hx.1
  obtain ⟨e, he₁, he₀⟩ := exists_glue₂_sections W hcov 1 0 (by
    have : Subsingleton Γ(W, U ⊓ V) := by rw [hUV]; infer_instance
    exact Subsingleton.elim _ _)
  have hidem : IsIdempotentElem e := by
    refine TopCat.Sheaf.eq_of_locally_eq₂ W.sheaf (homOfLE le_top : U ⟶ ⊤)
      (homOfLE le_top : V ⟶ ⊤) hcov _ _ ?_ ?_
    · change W.presheaf.map _ (e * e) = W.presheaf.map _ e
      rw [map_mul, he₁, mul_one]
    · change W.presheaf.map _ (e * e) = W.presheaf.map _ e
      rw [map_mul, he₀, mul_zero]
  rcases h e hidem with rfl | rfl
  · left
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero] at he₁
    exact zero_ne_one he₁
  · right
    by_contra hne
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem s).mp hne
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    rw [map_one] at he₀
    exact one_ne_zero he₀

lemma TrivialIdempotents.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : TrivialIdempotents R) : TrivialIdempotents S := by
  intro x hx
  rcases h (e.symm x) (hx.map e.symm.toRingHom) with h' | h'
  · exact Or.inl (by simpa using congrArg e h')
  · exact Or.inr (by simpa using congrArg e h')

end Connected

section FieldBaseChange

variable {k : Type u} [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k))
  [QuasiCompact g] [QuasiSeparated g] (K : Type u) [Field K] [Algebra k K]

/-- **Global functions after a field extension** (flat base change, EGA IV 2.? / Stacks 02KH):
for `Z` quasi-compact and quasi-separated over a field `k` and a field `K ⊇ k`,
`Γ(Z_K, 𝒪) ≅ Γ(Z, 𝒪) ⊗_k K`; in particular the idempotents correspond. -/
lemma trivialIdempotents_pullback_iff :
    letI := g.specStructureRingHom.toAlgebra
    TrivialIdempotents
      ((Limits.pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.obj (op ⊤)) ↔
      TrivialIdempotents (Γ(Z, ⊤) ⊗[k] K) := by
  let _ := g.specStructureRingHom.toAlgebra
  let φ : CommRingCat.of k ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap k K)
  have hflat : Flat (Spec.map φ) := inferInstance
  have hUY : (⊤ : (pullback g (Spec.map φ)).Opens) =
      pullback.fst g (Spec.map φ) ⁻¹ᵁ ⊤ ⊓ pullback.snd g (Spec.map φ) ⁻¹ᵁ ⊤ := by simp
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback g (Spec.map φ)) (US := ⊤) (UT := ⊤) (UX := ⊤) le_top le_top hUY
    (isAffineOpen_top _) (isAffineOpen_top _) (g.isCompact_preimage (U := ⊤) isCompact_univ)
    (g.isQuasiSeparated_preimage (U := ⊤) (isAffineOpen_top _).isQuasiSeparated)
  replace h := (isIso_pushoutSection_iff _ _ _ _).mp h
  have h' : IsPushout (CommRingCat.ofHom g.specStructureRingHom) φ
      (pullback.fst g (Spec.map φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd g (Spec.map φ)).appTop) := by
    refine h.of_iso (Scheme.ΓSpecIso (CommRingCat.of k)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of K))
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.specStructureRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · exact Scheme.ΓSpecIso_naturality φ
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  let e := IsPushout.isoIsPushout _ _ h' (CommRingCat.isPushout_tensorProduct k Γ(Z, ⊤) K)
  exact ⟨fun h₀ ↦ h₀.of_ringEquiv e.commRingCatIsoToRingEquiv,
    fun h₀ ↦ h₀.of_ringEquiv e.commRingCatIsoToRingEquiv.symm⟩

end FieldBaseChange

section Geometric

lemma adjoinRoot_map_surjective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (P : Polynomial R) (p : Polynomial S) (h : p ∣ P.map f) :
    Function.Surjective (AdjoinRoot.map f P p h) := by
  intro z
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective f hf q
  refine ⟨AdjoinRoot.mk P Q, ?_⟩
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]

/-- Zariski's connectedness theorem, for the set-theoretic fibre. -/
lemma isConnected_preimage_singleton (hf : ∀ V : Y.Opens, IsIso (f.app V)) (y : Y) :
    _root_.IsConnected (f ⁻¹' {y}) := by
  have := zariskiConnectednessStatement X Y f hf y
  have : ConnectedSpace (f ⁻¹' {y}) :=
    (f.fiberHomeo y).surjective.connectedSpace (f.fiberHomeo y).continuous
  exact isConnected_iff_connectedSpace.mpr this

lemma connectedSpace_of_isEmbedding {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']
    {e : T → T'} (he : Topology.IsEmbedding e) (h : _root_.IsConnected (Set.range e)) :
    ConnectedSpace T := by
  have : ConnectedSpace (Set.range e) := isConnected_iff_connectedSpace.mp h
  exact he.toHomeomorph.symm.surjective.connectedSpace he.toHomeomorph.symm.continuous

/-- **Zariski's theorem over a finite separable extension of a residue field** (EGA III 4.3.4,
proof). Let `L = κ(y)[t]/(p)` for a monic irreducible `p`. Lifting `p` to a monic `P` over
`𝒪_{Y,y}`, the flat base change `Y' = Spec 𝒪_{Y,y}[t]/(P) ⟶ Y` keeps `𝒪 ≅ f_* 𝒪`, and its fibre
over the point with residue field `L` is `X_y ⊗_{κ(y)} L`, which is therefore connected. -/
theorem connectedSpace_pullback_adjoinRoot (hf : ∀ V : Y.Opens, IsIso (f.app V)) (y : Y)
    (p : Polynomial (Y.residueField y)) (hp : p.Monic) (hirr : Irreducible p) :
    ConnectedSpace ↥(Limits.pullback (C := Scheme.{u}) (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AdjoinRoot p))))) := by
  have : Fact (Irreducible p) := ⟨hirr⟩
  let k := Y.residueField y
  let A := Y.presheaf.stalk y
  have hres : Function.Surjective (Y.residue y).hom := IsLocalRing.residue_surjective
  obtain ⟨P, hPmap, -, hPmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hres p) hp
  let R := CommRingCat.of (AdjoinRoot P)
  let αR : A ⟶ R := CommRingCat.ofHom (AdjoinRoot.of P)
  let L := CommRingCat.of (AdjoinRoot p)
  have hdvd : p ∣ P.map (Y.residue y).hom := by rw [hPmap]
  let ρ : R ⟶ L := CommRingCat.ofHom (AdjoinRoot.map (Y.residue y).hom P p hdvd)
  have hρ : Function.Surjective ρ := adjoinRoot_map_surjective _ hres P p hdvd
  have hcomm : αR ≫ ρ = Y.residue y ≫ CommRingCat.ofHom (algebraMap k (AdjoinRoot p)) := by
    ext a
    change AdjoinRoot.map _ P p hdvd (AdjoinRoot.of P a) = AdjoinRoot.of p (Y.residue y a)
    rw [AdjoinRoot.map_of]
  let h : Spec R ⟶ Y := Spec.map αR ≫ Y.fromSpecStalk y
  have : Flat (Spec.map αR) := by
    rw [Flat.SpecMap_iff]
    change (algebraMap A (AdjoinRoot P)).Flat
    rw [RingHom.flat_algebraMap_iff]
    have : Module.Free A (AdjoinRoot P) := Module.Free.of_basis (AdjoinRoot.powerBasis' hPmon).basis
    infer_instance
  have : IsNoetherianRing R := isNoetherianRing_of_surjective _ _ (AdjoinRoot.mk P)
    AdjoinRoot.mk_surjective
  let f₁ := Limits.pullback.snd f h
  have hf₁ : ∀ V, IsIso (f₁.app V) := isIso_app_pullback_snd f h hf
  have : IsClosedImmersion (Spec.map ρ) := IsClosedImmersion.spec_of_surjective ρ hρ
  obtain ⟨pt⟩ : Nonempty (Spec L) := inferInstance
  let q := Spec.map ρ pt
  have hrange : Set.range (Spec.map ρ) = {q} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨pt, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x pt]
  have hconn := isConnected_preimage_singleton f₁ hf₁ q
  have h₁ : ConnectedSpace ↥(Limits.pullback f₁ (Spec.map ρ)) := by
    refine connectedSpace_of_isEmbedding (Limits.pullback.fst f₁ (Spec.map ρ)).isClosedEmbedding.1
      ?_
    rw [Scheme.Pullback.range_fst, hrange]
    exact hconn
  have heq : Spec.map ρ ≫ h = Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p))) ≫
      Y.fromSpecResidueField y := by
    rw [Scheme.fromSpecResidueField, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, hcomm]
    rfl
  let e : Limits.pullback f₁ (Spec.map ρ) ≅ Limits.pullback (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p)))) :=
    pullbackLeftPullbackSndIso f h (Spec.map ρ) ≪≫ pullback.congrHom rfl heq ≪≫
      (pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) _).symm
  exact e.hom.homeomorph.surjective.connectedSpace e.hom.homeomorph.continuous

/-- **Zariski's connectedness theorem, geometric form** (EGA III 4.3.4; Stacks Tag 0BUI): for
`f : X ⟶ Y` proper, `Y` locally noetherian and `𝒪_Y ≅ f_* 𝒪_X`, the fibres of `f` are
geometrically connected: `X ×_Y Spec K` is connected for every field `K` and `Spec K ⟶ Y`.

Proof: for `y ∈ Y` with fibre `Z = X_y` and `B = Γ(Z, 𝒪_Z)`, finite over `k = κ(y)`, the scheme
`Z_K` is connected iff `B ⊗_k K` has only trivial idempotents (`trivialIdempotents_pullback_iff`,
`connectedSpace_of_trivialIdempotents`). By Zariski's theorem after the flat base changes of
`connectedSpace_pullback_adjoinRoot`, this holds for `K = k` and for the finite separable
extensions `K = k[t]/(p)`; `trivialIdempotents_tensor_of_forall_separable` gives all `K`. -/
theorem geometricallyConnected_of_isIso_app (hf : ∀ V : Y.Opens, IsIso (f.app V)) :
    GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro y
  let k := Y.residueField y
  let Z := f.fiber y
  let g : Z ⟶ Spec (CommRingCat.of k) := f.fiberToSpecResidueField y
  have : IsProper g := inferInstanceAs (IsProper (Limits.pullback.snd f (Y.fromSpecResidueField y)))
  have hZ : ConnectedSpace Z := zariskiConnectednessStatement X Y f hf y
  have : Nonempty Z := hZ.toNonempty
  change GeometricallyConnected g
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let _ := g.specStructureRingHom.toAlgebra
  have hB : TrivialIdempotents Γ(Z, ⊤) := trivialIdempotents_of_connectedSpace Z
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Nonempty.some ‹_›, trivial⟩⟩
  have : Nontrivial Γ(Z, ⊤) := Scheme.component_nontrivial Z ⊤
  have hfin : Module.Finite k Γ(Z, ⊤) := by
    have h := finite_app_of_isProper g (W := ⊤) (isAffineOpen_top _)
    have hiso : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    exact RingHom.Finite.comp h hiso
  have hK : TrivialIdempotents (Γ(Z, ⊤) ⊗[k] K) := by
    refine trivialIdempotents_tensor_of_forall_separable k Γ(Z, ⊤) hB (fun p hp hirr _ ↦ ?_) K
    have : Fact (Irreducible p) := ⟨hirr⟩
    exact (trivialIdempotents_pullback_iff g (AdjoinRoot p)).mp
      (@trivialIdempotents_of_connectedSpace _
        (connectedSpace_pullback_adjoinRoot f hf y p hp hirr))
  exact connectedSpace_of_trivialIdempotents _ ((trivialIdempotents_pullback_iff g K).mpr hK)

/-- The geometric fibres `X ×_Y Spec K` of a proper `f` with `𝒪_Y ≅ f_* 𝒪_X` over a locally
noetherian base are connected (EGA III 4.3.4). -/
theorem connectedSpace_pullback_of_isIso_app (hf : ∀ V : Y.Opens, IsIso (f.app V))
    (K : Type u) [Field K] (ξ : Spec (CommRingCat.of K) ⟶ Y) :
    ConnectedSpace ↥(Limits.pullback f ξ) :=
  pullback_of_geometrically (geometricallyConnected_iff f |>.mp
    (geometricallyConnected_of_isIso_app f hf)) K ξ

end Geometric

end AlgebraicGeometry.CohomologyAux
