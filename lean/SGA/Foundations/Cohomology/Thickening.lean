/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.SeparatingSections
import SGA.Foundations.Cohomology.BaseChangeSections
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Modules on the thickenings `X_n = X ×_A A / I^{n+1}`

First steps towards Grothendieck's existence theorem (EGA III 5.1.4): for `f : X ⟶ Spec A` with
`A` noetherian, `I ⊆ A` and `ι : X_n ⟶ X` the thickening of `Statements`,

* `CohomologyAux.ker_thickening_app`: the ideal of `X_n` in an affine open `V` is
  `I^{n+1} Γ(X, V)` (affine base change, `ker_inl_of_isPushout_quotient`);
* `CohomologyAux.thickeningIso`: for `M` quasi-coherent, `M / I^{n+1} M ≅ ι_* ι^* M`, induced by
  the unit of `ι^* ⊣ ι_*` (EGA I 4.1.2);
* `CohomologyAux.isIso_of_bijective_app_affine`: a morphism to a quasi-coherent module which is
  bijective on sections over affine opens is an isomorphism.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.CohomologyAux

section PushoutQuotient

/-- In a pushout square of commutative rings `A → B`, `A → A ⧸ J`, the map `B → P` is surjective
with kernel `J B`: `P = B ⊗_A A ⧸ J = B ⧸ J B`. -/
lemma ker_inl_of_isPushout_quotient {A B P : CommRingCat.{u}} (J : Ideal A) {f : A ⟶ B}
    {inl : B ⟶ P} {inr : CommRingCat.of (A ⧸ J) ⟶ P}
    (h : IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk J)) inl inr) :
    RingHom.ker inl.hom = J.map f.hom ∧ Function.Surjective inl := by
  let _ := f.hom.toAlgebra
  have h' := CommRingCat.isPushout_tensorProduct A B (A ⧸ J)
  let e := IsPushout.isoIsPushout _ _ h h'
  have he : inl ≫ e.hom = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :=
    IsPushout.inl_isoIsPushout_hom _ _ h h'
  let q := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J
  have hq : ∀ b : B, q (Ideal.Quotient.mk _ b) = Algebra.TensorProduct.includeLeftRingHom b :=
    fun b ↦ rfl
  have hinl : ∀ b : B, inl b = e.inv (q (Ideal.Quotient.mk _ b)) := by
    intro b
    rw [hq]
    have := ConcreteCategory.congr_hom he b
    change (inl ≫ e.hom) b = Algebra.TensorProduct.includeLeftRingHom b at this
    rw [← this, ← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  · ext b
    rw [RingHom.mem_ker]
    change inl b = 0 ↔ _
    rw [hinl, map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv).1,
      map_eq_zero_iff _ q.injective, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · intro p
    obtain ⟨z, hz⟩ := q.surjective (e.hom p)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨b, ?_⟩
    rw [hinl, hz, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]

end PushoutQuotient

section IsoCriterion

variable {X : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules which is injective on sections over affine opens is injective on
all sections. -/
lemma app_injective_of_affine {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ V : X.Opens, IsAffineOpen V → Function.Injective (φ.app V)) (U : X.Opens) :
    Function.Injective (φ.app U) := by
  intro s t hst
  refine section_ext_affine fun V hV hVU ↦ h V hV ?_
  rw [hom_app_presheaf_map, hom_app_presheaf_map, hst]

/-- **Isomorphisms of quasi-coherent modules are detected on affine opens.** -/
lemma isIso_of_bijective_app_affine {M N : X.Modules} [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : ∀ V : X.Opens, IsAffineOpen V → Function.Bijective (φ.app V)) : IsIso φ := by
  have hepi : Epi φ := epi_of_surjective_app N φ (fun V : X.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top X) (fun V ↦ V.2) fun V ↦ (h V.1 V.2).2
  have hinj := app_injective_of_affine φ fun V hV ↦ (h V hV).1
  have hmono : Mono φ := by
    have : Mono (Scheme.Modules.Hom.toAbSheaf φ) := by
      have : Mono ((sheafToPresheaf _ _).map (Scheme.Modules.Hom.toAbSheaf φ)) := by
        have : ∀ U : X.Opensᵒᵖ,
            Mono (((sheafToPresheaf _ _).map (Scheme.Modules.Hom.toAbSheaf φ)).app U) :=
          fun U ↦ (AddCommGrpCat.mono_iff_injective _).mpr (hinj U.unop)
        exact NatTrans.mono_of_mono_app _
      exact (sheafToPresheaf _ _).mono_of_mono_map this
    exact (Scheme.Modules.toAbSheafFunctor X).mono_of_mono_map this
  exact isIso_of_mono_of_epi φ

end IsoCriterion

section Thickening

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A) (n : ℕ)

instance : IsClosedImmersion (thickening.ι f I n) :=
  inferInstanceAs (IsClosedImmersion (Limits.pullback.fst _ _))

lemma isPullback_thickening : IsPullback (thickening.ι f I n) (Limits.pullback.snd _ _) f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :=
  IsPullback.of_hasPullback _ _

/-- The ideal of `X_n = X ×_A A/I^{n+1}` in an affine open `V ⊆ X` is `I^{n+1} Γ(X, V)`. -/
lemma ker_thickening_app {V : X.Opens} (hV : IsAffineOpen V) :
    RingHom.ker ((thickening.ι f I n).app V).hom = idealV f I V (n + 1) := by
  have h := ker_inl_of_isPushout_quotient (I ^ (n + 1))
    (isPushout_baseChange (isPullback_thickening I f n) hV)
  rw [Scheme.Hom.app_eq_appLE]
  exact h.1

/-- Elements of `I^{n+1}` vanish on `X_n`. -/
lemma thickening_appTop_specStructureRingHom {a : A} (ha : a ∈ I ^ (n + 1)) :
    (thickening.ι f I n).appTop (f.specStructureRingHom a) = 0 := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))
  have hw : thickening.ι f I n ≫ f = Limits.pullback.snd _ _ ≫ Spec.map q := pullback.condition
  have h1 : (thickening.ι f I n).appTop (f.specStructureRingHom a) =
      (thickening.ι f I n ≫ f).appTop ((Scheme.ΓSpecIso A).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  have h2 : (thickening.ι f I n ≫ f).appTop ((Scheme.ΓSpecIso A).inv a) =
      (Limits.pullback.snd f (Spec.map q) ≫ Spec.map q).appTop ((Scheme.ΓSpecIso A).inv a) :=
    congrArg (fun φ : thickening f I n ⟶ Spec A ↦ φ.appTop ((Scheme.ΓSpecIso A).inv a)) hw
  have h3 : (Spec.map q).appTop ((Scheme.ΓSpecIso A).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (n + 1)))).inv (q a) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality q) a).symm
  rw [h1, h2, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h3]
  change Scheme.Hom.appTop (Limits.pullback.snd f (Spec.map q))
    ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ a)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

variable [IsNoetherianRing A] (M : X.Modules) [M.IsQuasicoherent]

omit [IsNoetherianRing A] [M.IsQuasicoherent] in
/-- The unit `M ⟶ ι_* ι^* M` of the thickening `ι : X_n ⟶ X` kills `I^{n+1} M`. -/
lemma idealPowSMul_comp_unit :
    M.idealPowSMul f I n ≫ (Scheme.Modules.pullbackPushforwardAdjunction
      (thickening.ι f I n)).unit.app M = 0 := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  rw [Scheme.Modules.idealPowSMul, Sigma.ι_desc_assoc, comp_zero]
  apply (Scheme.Modules.toAbSheafFunctor X).map_injective
  refine Scheme.Modules.toAbSheaf_hom_ext fun V s ↦ ?_
  rw [Functor.map_zero]
  change Scheme.Modules.pullbackApp (thickening.ι f I n) M V
    ((M.smulHom (f.specStructureRingHom a)).hom.app (op V) s) = 0
  rw [Scheme.Modules.smulHom_app_apply, Scheme.Modules.pullbackApp_smul]
  have hn := ConcreteCategory.congr_hom
    ((thickening.ι f I n).naturality (homOfLE (le_top : V ≤ ⊤)).op) (f.specStructureRingHom a)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  rw [hn]
  change (thickening f I n).presheaf.map _
    ((thickening.ι f I n).appTop (f.specStructureRingHom a)) • _ = 0
  rw [thickening_appTop_specStructureRingHom I f n a.2, map_zero, zero_smul]

/-- `ι_* ι^* M ≅ M / I^{n+1} M` for the thickening `ι : X_n ⟶ X`. -/
noncomputable def toThickening :
    M.quotientIdealPow f I n ⟶ (Scheme.Modules.pushforward (thickening.ι f I n)).obj
      ((Scheme.Modules.pullback (thickening.ι f I n)).obj M) :=
  cokernel.desc _ _ (idealPowSMul_comp_unit I f n M)

omit [IsNoetherianRing A] [M.IsQuasicoherent] in
@[reassoc (attr := simp)]
lemma toQuotientIdealPow_toThickening :
    M.toQuotientIdealPow f I n ≫ toThickening I f n M =
      (Scheme.Modules.pullbackPushforwardAdjunction (thickening.ι f I n)).unit.app M :=
  cokernel.π_desc _ _ _

instance isIso_toThickening : IsIso (toThickening I f n M) := by
  have : ((Scheme.Modules.pushforward (thickening.ι f I n)).obj
      ((Scheme.Modules.pullback (thickening.ι f I n)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward _ _
  refine isIso_of_bijective_app_affine _ fun V hV ↦ ?_
  have hfac : ∀ s : Γ(M, V), (toThickening I f n M).app V
      ((M.toQuotientIdealPow f I n).app V s) =
      Scheme.Modules.pullbackApp (thickening.ι f I n) M V s := by
    intro s
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      toQuotientIdealPow_toThickening]
    rfl
  have hsurjq := toQuotientIdealPow_app_surjective I f n hV (M := M)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨s, rfl⟩ := hsurjq t
    rw [hfac] at ht
    have h1 := Scheme.Modules.mem_smul_top_of_pullbackApp_eq_zero (thickening.ι f I n) M hV s ht
    rw [ker_thickening_app I f n hV] at h1
    rw [toQuotientIdealPow_app_eq_zero_iff]
    exact (mem_range_ιPow_app f I M hV (n + 1) s).mpr h1
  · intro y
    obtain ⟨s, rfl⟩ := Scheme.Modules.surjective_pullbackApp_of_isClosedImmersion
      (thickening.ι f I n) M hV y
    exact ⟨_, hfac s⟩

/-- **The restriction of `M` to the thickening `X_n`, pushed back to `X`, is `M / I^{n+1} M`.** -/
noncomputable def thickeningIso :
    M.quotientIdealPow f I n ≅ (Scheme.Modules.pushforward (thickening.ι f I n)).obj
      ((Scheme.Modules.pullback (thickening.ι f I n)).obj M) :=
  asIso (toThickening I f n M)

end Thickening

end AlgebraicGeometry.CohomologyAux
