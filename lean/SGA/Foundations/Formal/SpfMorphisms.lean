/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import SGA.Foundations.Formal.SpfBasicOpen
import SGA.Foundations.Formal.SpfCompletion

/-!
# Morphisms of formal spectra

Let `A` be a ring, complete for the `I`-adic topology with `I` finitely generated, and `B` a ring
complete for the `J`-adic topology. Every morphism of locally ringed spaces `Spf B ⟶ Spf A` is
`Spf.map φ` for a unique continuous ring map `φ : A → B` (EGA I, 10.2.2 and 10.4.6;
`AlgebraicGeometry.Spf.exists_eq_map`).

## Main definitions and results

* `Spf.toΓ`: the canonical map `A → Γ(Spf A, 𝒪)` (an isomorphism when `A` is complete).
* `Spf.basicOpen I a`: the basic open subset `D(a)` of `Spf A`; these form a basis
  (`Spf.isBasis_basicOpen`), and `D(a)` is the image of `Spf A_a` (`Spf.range_basicOpenMap`).
* `Spf.hom_ext_of_toΓ`: a morphism `T ⟶ Spf A` from a locally ringed space on which some power of
  `I` vanishes is determined by its effect on global sections.
* `Spf.exists_eq_map`: every morphism `Spf B ⟶ Spf A` comes from a continuous ring map.

The proof: the points of `Spf A` are separated by the basic opens `D(a)`, and the sections over
`D(a)` form the completion of `A_a`, in which `A_a` is dense; a ring map from it which kills a
power of `I` is therefore determined by its restriction to `A`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Spf

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The canonical map `A → Γ(Spf A, 𝒪) = lim← A ⧸ Iⁿ⁺¹`. -/
noncomputable def toΓ : CommRingCat.of A ⟶ LocallyRingedSpace.Γ.obj (op (Spf A I)) :=
  (Scheme.formalColimit.isLimitΓcone (diagram A I)).lift
    ((Cone.postcompose (diagramΓIso A I).inv).obj (adicCone A I))

@[reassoc]
lemma toΓ_comp_Γ_map_ι (n : ℕ) :
    toΓ I ≫ LocallyRingedSpace.Γ.map (ι A I n).op =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫ (ΓSpecIsoLRS _).inv :=
  (Scheme.formalColimit.isLimitΓcone (diagram A I)).fac _ (op n)

lemma toΓ_hom_ext {R : CommRingCat.{u}} {f g : R ⟶ LocallyRingedSpace.Γ.obj (op (Spf A I))}
    (h : ∀ n, f ≫ LocallyRingedSpace.Γ.map (ι A I n).op =
      g ≫ LocallyRingedSpace.Γ.map (ι A I n).op) : f = g :=
  (Scheme.formalColimit.isLimitΓcone (diagram A I)).hom_ext fun n ↦ h (unop n)

lemma toΓ_eq_ΓIso_inv [IsAdicComplete I A] : toΓ I = (ΓIso A I).inv :=
  toΓ_hom_ext I fun n ↦ by rw [toΓ_comp_Γ_map_ι, ΓIso_inv_comp_Γ_map_ι]

lemma toΓ_comp_Γ_map_fromSpec {C : CommRingCat.{u}} (ψ : A →+* C) (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) :
    toΓ I ≫ LocallyRingedSpace.Γ.map (fromSpec ψ n h).op =
      CommRingCat.ofHom ψ ≫ (ΓSpecIsoLRS C).inv := by
  rw [fromSpec, op_comp, Functor.map_comp, ← Category.assoc, toΓ_comp_Γ_map_ι,
    Category.assoc, ← ΓSpecIsoLRS_inv_naturality, ← Category.assoc, ← CommRingCat.ofHom_comp]
  congr 2

variable {B : Type u} [CommRing B] {J : Ideal B}

/-- Naturality of `toΓ`: `Γ(Spf.map φ) ∘ toΓ = toΓ ∘ φ`. -/
@[reassoc]
lemma toΓ_comp_Γ_map_map (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ) :
    toΓ I ≫ LocallyRingedSpace.Γ.map (map φ hφ).op = CommRingCat.ofHom φ ≫ toΓ J := by
  refine toΓ_hom_ext J fun n ↦ ?_
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, ι_map, toΓ_comp_Γ_map_fromSpec,
    Category.assoc, toΓ_comp_Γ_map_ι]
  rfl

variable (A) in
lemma toΓ_comp_ΓIsoAdicCompletion_hom (hI : I.FG) :
    toΓ I ≫ (ΓIsoAdicCompletion A I hI).hom =
      CommRingCat.ofHom (algebraMap A (AdicCompletion I A)) := by
  have : IsAdicComplete (AdicCompletion.completionIdeal I) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hI)
  change toΓ I ≫ LocallyRingedSpace.Γ.map (map (algebraMap A (AdicCompletion I A)) _).op ≫
    (ΓIso _ _).hom = _
  rw [toΓ_comp_Γ_map_map_assoc, toΓ_eq_ΓIso_inv, Iso.inv_hom_id, Category.comp_id]

/-! ### Basic open subsets -/

/-- The basic open subset `D(a)` of `Spf A`, where the section `a` does not vanish. -/
noncomputable def basicOpen (a : A) : Opens (Spf A I) :=
  (Spf A I).toRingedSpace.basicOpen (U := ⊤) ((toΓ I).hom a)

/-- The preimage of `D(a) ⊆ Spf A` in `Spec (A ⧸ Iⁿ⁺¹)` is `D(a)`. -/
lemma preimage_ι_basicOpen (n : ℕ) (a : A) :
    (Opens.map (ι A I n).base).obj (basicOpen I a) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) a) := by
  refine (LocallyRingedSpace.preimage_basicOpen (ι A I n) ((toΓ I).hom a)).trans ?_
  have h := congr($(toΓ_comp_Γ_map_ι I n).hom a)
  change (ι A I n).c.app (op ⊤) ((toΓ I).hom a) = _ at h
  erw [h]
  exact basicOpen_eq_of_affine _

/-- The basic open subsets `D(a)` form a basis of the topology of `Spf A`. -/
lemma isBasis_basicOpen : Opens.IsBasis (Set.range (basicOpen I)) := by
  let e := homeomorph A I
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hU : IsOpen (e ⁻¹' U) := U.2.preimage e.continuous
  have hy : e.symm x ∈ e ⁻¹' U := by simpa using hx
  obtain ⟨_, ⟨r, rfl⟩, hyr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy hU
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hpre : ∀ y, y ∈ e ⁻¹' (basicOpen I a) ↔
      y ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (0 + 1)) a) :=
    fun y ↦ SetLike.ext_iff.mp (preimage_ι_basicOpen I 0 a) y
  refine ⟨basicOpen I a, ⟨a, rfl⟩, ?_, fun z hz ↦ ?_⟩
  · have : e.symm x ∈ e ⁻¹' (basicOpen I a) := (hpre _).mpr hyr
    simpa using this
  · have : e.symm z ∈ e ⁻¹' (basicOpen I a) := by simpa using hz
    rw [hpre] at this
    have h := hrU this
    change e (e.symm z) ∈ U at h
    rwa [Homeomorph.apply_symm_apply] at h

instance : T0Space ((Spf A I).toPresheafedSpace : TopCat.{u}) :=
  have : T0Space (Spec (.of (A ⧸ I ^ (0 + 1)))) := inferInstanceAs (T0Space (PrimeSpectrum _))
  (homeomorph A I).symm.isEmbedding.t0Space

/-- For `a ∈ I`, the basic open `D(a)` of `Spf A` is empty. -/
lemma basicOpen_eq_bot_of_mem {a : A} (ha : a ∈ I) : basicOpen I a = ⊥ := by
  have h := preimage_ι_basicOpen I 0 a
  rw [(Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha)), PrimeSpectrum.basicOpen_zero] at h
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx.elim⟩
  have : (homeomorph A I).symm x ∈ (Opens.map (ι A I 0).base).obj (basicOpen I a) := by
    change (homeomorph A I) ((homeomorph A I).symm x) ∈ basicOpen I a
    simpa using hx
  rw [h] at this
  exact this.elim

/-- A section `a` with `D(a) = ∅` in `Spf A` is nilpotent modulo `I`. -/
lemma isNilpotent_of_basicOpen_eq_bot {a : A} (ha : basicOpen I a = ⊥) :
    IsNilpotent (Ideal.Quotient.mk (I ^ (0 + 1)) a) := by
  rw [← PrimeSpectrum.basicOpen_eq_bot_iff, ← preimage_ι_basicOpen, ha]
  rfl

/-- `D(a) ⊆ Spf A` is the image of the open immersion `Spf A_a ⟶ Spf A` (EGA I, §10.1). -/
lemma range_basicOpenMap (a : A) :
    Set.range (basicOpenMap I a).base = (basicOpen I a : Set (Spf A I)) := by
  have hsurj : Function.Surjective
      (ι (Localization.Away a) (I.map (algebraMap A (Localization.Away a))) 0).base :=
    (homeomorph _ _).surjective
  have hcomp : ι _ _ 0 ≫ basicOpenMap I a = ((diagramMapAway I a).app 0).toLRSHom ≫ ι A I 0 :=
    Scheme.formalColimit.ι_map _ 0
  have hrange : Set.range ((diagramMapAway I a).app 0).base =
      ((PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (0 + 1)) a) :
        Set (PrimeSpectrum (A ⧸ I ^ (0 + 1))))) := by
    let _ := (quotientMapAway I a 0).toAlgebra
    have := isLocalization_away_quotient I a 0
    exact PrimeSpectrum.localization_away_comap_range _ _
  have hpre : (ι A I 0).base ⁻¹' (basicOpen I a : Set (Spf A I)) =
      ((PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (0 + 1)) a) :
        Set (PrimeSpectrum (A ⧸ I ^ (0 + 1))))) := by
    ext y
    exact SetLike.ext_iff.mp (preimage_ι_basicOpen I 0 a) y
  have hsurj₀ : Function.Surjective (ι A I 0).base := (homeomorph A I).surjective
  rw [← hsurj.range_comp]
  change Set.range (ι _ _ 0 ≫ basicOpenMap I a).base = _
  rw [hcomp]
  change Set.range ((ι A I 0).base ∘ ((diagramMapAway I a).app 0).base) = _
  rw [Set.range_comp, hrange, ← hpre, Set.image_preimage_eq _ hsurj₀]

/-- `D(a) ⊆ Spf A` is the image of `Spf A_a`, as an open subset. -/
lemma basicOpen_eq_opensFunctor_obj_top (a : A) :
    basicOpen I a =
      (LocallyRingedSpace.IsOpenImmersion.opensFunctor (basicOpenMap I a)).obj ⊤ := by
  ext x
  change x ∈ (basicOpen I a : Set (Spf A I)) ↔ x ∈ (basicOpenMap I a).base '' Set.univ
  rw [Set.image_univ, range_basicOpenMap]

lemma preimage_basicOpenMap_basicOpen (a : A) :
    (Opens.map (basicOpenMap I a).base).obj (basicOpen I a) = ⊤ := by
  ext x
  change (basicOpenMap I a).base x ∈ (basicOpen I a : Set (Spf A I)) ↔ True
  rw [← range_basicOpenMap]
  exact iff_true_intro ⟨x, rfl⟩

/-! ### Sections over basic opens -/

section Sections

variable (a : A)

/-- The restriction map `Γ(Spf A) → 𝒪(D(a))`. -/
noncomputable abbrev resBasicOpen :
    LocallyRingedSpace.Γ.obj (op (Spf A I)) ⟶ (Spf A I).presheaf.obj (op (basicOpen I a)) :=
  (Spf A I).presheaf.map (homOfLE le_top : basicOpen I a ⟶ ⊤).op

/-- The isomorphism `𝒪_{Spf A}(D(a)) ≅ Γ(Spf A_a)` induced by the open immersion
`Spf A_a ⟶ Spf A` onto `D(a)`. -/
noncomputable def basicOpenSectionsToΓ :
    (Spf A I).presheaf.obj (op (basicOpen I a)) ⟶
      LocallyRingedSpace.Γ.obj (op (Spf (Localization.Away a)
        (I.map (algebraMap A (Localization.Away a))))) :=
  (basicOpenMap I a).c.app (op (basicOpen I a)) ≫
    (Spf _ _).presheaf.map (eqToHom (preimage_basicOpenMap_basicOpen I a).symm).op

instance : IsIso (basicOpenSectionsToΓ I a) := by
  have h₁ := PresheafedSpace.IsOpenImmersion.c_iso' (basicOpenMap I a).toHom ⊤
    (basicOpen_eq_opensFunctor_obj_top I a)
  have h₂ : IsIso ((Spf (Localization.Away a)
      (I.map (algebraMap A (Localization.Away a)))).presheaf.map
        (eqToHom (preimage_basicOpenMap_basicOpen I a).symm).op) := by
    rw [eqToHom_op, eqToHom_map]
    infer_instance
  unfold basicOpenSectionsToΓ
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

lemma toΓ_comp_resBasicOpen_comp_basicOpenSectionsToΓ :
    toΓ I ≫ resBasicOpen I a ≫ basicOpenSectionsToΓ I a =
      CommRingCat.ofHom (algebraMap A (Localization.Away a)) ≫ toΓ _ := by
  have h₁ : resBasicOpen I a ≫ (basicOpenMap I a).c.app (op (basicOpen I a)) =
      (basicOpenMap I a).c.app (op ⊤) ≫ (Spf _ _).presheaf.map
        ((Opens.map (basicOpenMap I a).base).map (homOfLE le_top)).op :=
    (basicOpenMap I a).c.naturality _
  have h₂ : (Spf (Localization.Away a) (I.map (algebraMap A (Localization.Away a)))).presheaf.map
      ((Opens.map (basicOpenMap I a).base).map (homOfLE le_top : basicOpen I a ⟶ ⊤)).op ≫
        (Spf _ _).presheaf.map (eqToHom (preimage_basicOpenMap_basicOpen I a).symm).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    congr 1
  have h₃ : toΓ I ≫ LocallyRingedSpace.Γ.map (basicOpenMap I a).op =
      CommRingCat.ofHom (algebraMap A (Localization.Away a)) ≫ toΓ _ := by
    rw [basicOpenMap_eq, toΓ_comp_Γ_map_map]
  rw [← h₃]
  congr 1
  rw [basicOpenSectionsToΓ]
  erw [← Category.assoc, h₁, Category.assoc, h₂, Category.comp_id]
  rfl

/-- The sections of `Spf A` over `D(a)` are the completion of `A_a` (EGA I, §10.1). -/
noncomputable def sectionsBasicOpenIso (hI : I.FG) :
    (Spf A I).presheaf.obj (op (basicOpen I a)) ≅
      .of (AdicCompletion (I.map (algebraMap A (Localization.Away a))) (Localization.Away a)) :=
  asIso (basicOpenSectionsToΓ I a) ≪≫ ΓIsoAdicCompletion _ _ (hI.map _)

lemma toΓ_comp_resBasicOpen_comp_sectionsBasicOpenIso_hom (hI : I.FG) :
    toΓ I ≫ resBasicOpen I a ≫ (sectionsBasicOpenIso I a hI).hom =
      CommRingCat.ofHom ((algebraMap (Localization.Away a) (AdicCompletion
        (I.map (algebraMap A (Localization.Away a))) (Localization.Away a))).comp
          (algebraMap A (Localization.Away a))) := by
  have := toΓ_comp_resBasicOpen_comp_basicOpenSectionsToΓ I a
  rw [sectionsBasicOpenIso, Iso.trans_hom, asIso_hom, reassoc_of% this,
    toΓ_comp_ΓIsoAdicCompletion_hom]
  rfl

/-- Two ring maps out of `𝒪(D(a))` which agree on the sections coming from `A` and kill a power
of `I` are equal: `A_a` is dense in `𝒪(D(a)) = (A_a)^`. -/
lemma sectionsBasicOpen_hom_ext (hI : I.FG) {R : CommRingCat.{u}}
    {G₁ G₂ : (Spf A I).presheaf.obj (op (basicOpen I a)) ⟶ R}
    (h : toΓ I ≫ resBasicOpen I a ≫ G₁ = toΓ I ≫ resBasicOpen I a ≫ G₂) {m : ℕ}
    (hm : I ^ m ≤ RingHom.ker (toΓ I ≫ resBasicOpen I a ≫ G₁).hom) : G₁ = G₂ := by
  have hΘ := toΓ_comp_resBasicOpen_comp_sectionsBasicOpenIso_hom I a hI
  suffices (sectionsBasicOpenIso I a hI).inv ≫ G₁ = (sectionsBasicOpenIso I a hI).inv ≫ G₂ by
    simpa using congr((sectionsBasicOpenIso I a hI).hom ≫ $this)
  have key (G : (Spf A I).presheaf.obj (op (basicOpen I a)) ⟶ R) :
      ((sectionsBasicOpenIso I a hI).inv ≫ G).hom.comp
        ((algebraMap (Localization.Away a) _).comp (algebraMap A (Localization.Away a))) =
        (toΓ I ≫ resBasicOpen I a ≫ G).hom := by
    have : CommRingCat.ofHom ((algebraMap (Localization.Away a) (AdicCompletion
        (I.map (algebraMap A (Localization.Away a))) (Localization.Away a))).comp
          (algebraMap A (Localization.Away a))) ≫ (sectionsBasicOpenIso I a hI).inv ≫ G =
        toΓ I ≫ resBasicOpen I a ≫ G := by
      rw [← hΘ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← this]
    rfl
  have hker (G : (Spf A I).presheaf.obj (op (basicOpen I a)) ⟶ R)
      (hG : I ^ m ≤ RingHom.ker (toΓ I ≫ resBasicOpen I a ≫ G).hom) :
      AdicCompletion.completionIdeal (I.map (algebraMap A (Localization.Away a))) ^ m ≤
        RingHom.ker ((sectionsBasicOpenIso I a hI).inv ≫ G).hom := by
    rw [← Ideal.map_pow, Ideal.map_pow, Ideal.map_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap,
      RingHom.comap_ker, key G]
    exact hG
  ext1
  refine AdicCompletion.ringHom_ext_of_pow _ (hI.map _) ?_ (hker G₁ hm)
    (hker G₂ (by rwa [← h]))
  refine IsLocalization.ringHom_ext (Submonoid.powers a) ?_
  rw [RingHom.comp_assoc, RingHom.comp_assoc, key, key, h]

end Sections

/-! ### Morphisms to `Spf A` -/

/-- The preimage of `D(a)` under `g : T ⟶ Spf A` is the basic open of the image of `a`. -/
lemma preimage_basicOpen {T : LocallyRingedSpace.{u}} (g : T ⟶ Spf A I) (a : A) :
    (Opens.map g.base).obj (basicOpen I a) =
      T.toRingedSpace.basicOpen (U := ⊤) ((toΓ I ≫ LocallyRingedSpace.Γ.map g.op).hom a) :=
  LocallyRingedSpace.preimage_basicOpen g _

/-- Morphisms `T ⟶ Spf A` with the same effect on the global sections coming from `A` have the
same underlying continuous map. -/
lemma base_eq_of_toΓ {T : LocallyRingedSpace.{u}} {g h : T ⟶ Spf A I}
    (H : toΓ I ≫ LocallyRingedSpace.Γ.map g.op = toΓ I ≫ LocallyRingedSpace.Γ.map h.op) :
    g.base = h.base := by
  ext t
  refine Inseparable.eq ((isBasis_basicOpen I).inseparable_iff.mpr ?_)
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  have e₁ : t ∈ (Opens.map g.base).obj (basicOpen I a) ↔
      t ∈ (Opens.map h.base).obj (basicOpen I a) := by
    rw [preimage_basicOpen, preimage_basicOpen, H]
  exact e₁

/-- A morphism `T ⟶ Spf A` from a locally ringed space on which a power of `I` vanishes is
determined by the induced map `A → Γ(T, 𝒪)` (EGA I, 10.4.6, uniqueness; `I` finitely generated).
-/
theorem hom_ext_of_toΓ (hI : I.FG) {T : LocallyRingedSpace.{u}} {g h : T ⟶ Spf A I}
    (H : toΓ I ≫ LocallyRingedSpace.Γ.map g.op = toΓ I ≫ LocallyRingedSpace.Γ.map h.op) {m : ℕ}
    (hm : I ^ m ≤ RingHom.ker (toΓ I ≫ LocallyRingedSpace.Γ.map g.op).hom) : g = h := by
  have hbase := base_eq_of_toΓ I H
  obtain ⟨⟨g₀, gc⟩, hg⟩ := g
  obtain ⟨⟨h₀, hc⟩, hh⟩ := h
  change g₀ = h₀ at hbase
  subst hbase
  have Hc : toΓ I ≫ gc.app (op ⊤) = toΓ I ≫ hc.app (op ⊤) := H
  have hmc : I ^ m ≤ RingHom.ker (toΓ I ≫ gc.app (op ⊤)).hom := hm
  congr
  refine TopCat.Sheaf.hom_ext (Spf A I).presheaf
    ((TopCat.Sheaf.pushforward CommRingCat g₀).obj T.sheaf) (isBasis_basicOpen I) fun a ↦ ?_
  have e₁ := gc.naturality (homOfLE le_top : basicOpen I a ⟶ ⊤).op
  have e₂ := hc.naturality (homOfLE le_top : basicOpen I a ⟶ ⊤).op
  refine sectionsBasicOpen_hom_ext I a hI ?_ (m := m) ?_
  · erw [e₁, e₂, reassoc_of% Hc]
    exact Category.assoc _ _ _
  · intro x hx
    have h0 : (toΓ I ≫ gc.app (op ⊤)).hom x = 0 := RingHom.mem_ker.mp (hmc hx)
    rw [RingHom.mem_ker]
    erw [e₁]
    have := congrArg (((TopCat.Presheaf.pushforward CommRingCat g₀).obj T.presheaf).map
      (homOfLE le_top : basicOpen I a ⟶ ⊤).op).hom h0
    rw [map_zero] at this
    exact this

/-! ### Morphisms between formal spectra -/

section Converse

variable {I} {B : Type u} [CommRing B] {J : Ideal B} [IsAdicComplete I A] [IsAdicComplete J B]

/-- The ring map `A = Γ(Spf A) → Γ(Spf B) = B` induced by a morphism `Spf B ⟶ Spf A`, for complete
rings `A` and `B`. -/
noncomputable def ringHomOfHom (f : Spf B J ⟶ Spf A I) : A →+* B :=
  ((ΓIso A I).inv ≫ LocallyRingedSpace.Γ.map f.op ≫ (ΓIso B J).hom).hom

@[reassoc]
lemma toΓ_comp_Γ_map (f : Spf B J ⟶ Spf A I) :
    toΓ I ≫ LocallyRingedSpace.Γ.map f.op = CommRingCat.ofHom (ringHomOfHom f) ≫ toΓ J := by
  rw [toΓ_eq_ΓIso_inv, toΓ_eq_ΓIso_inv, ringHomOfHom, CommRingCat.ofHom_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[simp]
lemma ringHomOfHom_map (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ) :
    ringHomOfHom (map φ hφ) = φ := by
  rw [ringHomOfHom, ΓIso_map]
  rfl

/-- The ring map induced by a morphism `Spf B ⟶ Spf A` is continuous (EGA I, 10.2.2): elements
of `I` vanish at every point of `Spf A`, so their images are nilpotent modulo `J`. -/
lemma exists_pow_le_comap_ringHomOfHom (hI : I.FG) (f : Spf B J ⟶ Spf A I) :
    ∃ k, I ^ k ≤ J.comap (ringHomOfHom f) := by
  have hrad : I.map (ringHomOfHom f) ≤ J.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h₁ := preimage_basicOpen I f a
    rw [basicOpen_eq_bot_of_mem I ha, toΓ_comp_Γ_map] at h₁
    have h₂ : basicOpen J (ringHomOfHom f a) = ⊥ := h₁.symm
    obtain ⟨n, hn⟩ := isNilpotent_of_basicOpen_eq_bot J h₂
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hn
    exact ⟨n, hn⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (hI.map _)
  refine ⟨k, ?_⟩
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact hk

/-- Every morphism of locally ringed spaces `Spf B ⟶ Spf A` between formal spectra of complete
rings (`I` finitely generated) is induced by a continuous ring map `A → B` (EGA I, 10.2.2). -/
theorem eq_map_ringHomOfHom (hI : I.FG) (f : Spf B J ⟶ Spf A I) :
    f = map (ringHomOfHom f) (exists_pow_le_comap_ringHomOfHom hI f) := by
  obtain ⟨k, hk⟩ := exists_pow_le_comap_ringHomOfHom hI f
  refine hom_ext fun n ↦ hom_ext_of_toΓ I hI ?_ (m := k * (n + 1)) ?_
  · rw [op_comp, Functor.map_comp, op_comp, Functor.map_comp, toΓ_comp_Γ_map_assoc,
      toΓ_comp_Γ_map_map_assoc]
  · intro a ha
    have : I ^ (k * (n + 1)) ≤ (J ^ (n + 1)).comap (ringHomOfHom f) := by
      rw [pow_mul]
      exact (Ideal.pow_right_mono hk _).trans (Ideal.le_comap_pow _ _)
    have hmem : ringHomOfHom f a ∈ J ^ (n + 1) := this ha
    rw [op_comp, Functor.map_comp, toΓ_comp_Γ_map_assoc, toΓ_comp_Γ_map_ι, RingHom.mem_ker]
    change (ΓSpecIsoLRS (.of (B ⧸ J ^ (n + 1)))).inv.hom
      (Ideal.Quotient.mk (J ^ (n + 1)) (ringHomOfHom f a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

/-- EGA I, 10.2.2: morphisms `Spf B ⟶ Spf A` of formal spectra of complete rings (`I` finitely
generated) are the continuous ring maps `A → B`. -/
theorem exists_eq_map (hI : I.FG) (f : Spf B J ⟶ Spf A I) :
    ∃ (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ), f = map φ hφ :=
  ⟨_, _, eq_map_ringHomOfHom hI f⟩

/-- EGA I, 10.2.2: `φ ↦ Spf.map φ` is a bijection between continuous ring maps `A → B` and
morphisms `Spf B ⟶ Spf A` (`A`, `B` complete, `I` finitely generated). -/
@[simps]
noncomputable def homEquiv (hI : I.FG) :
    {φ : A →+* B // ∃ k, I ^ k ≤ J.comap φ} ≃ (Spf B J ⟶ Spf A I) where
  toFun φ := map φ.1 φ.2
  invFun f := ⟨ringHomOfHom f, exists_pow_le_comap_ringHomOfHom hI f⟩
  left_inv φ := Subtype.ext (ringHomOfHom_map φ.1 φ.2)
  right_inv f := (eq_map_ringHomOfHom hI f).symm

end Converse

end AlgebraicGeometry.Spf
