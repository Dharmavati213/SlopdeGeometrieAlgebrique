/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.GroupSheaves
import SGA.SGA1.ExposeXI.PrincipalBundle

/-!
# fpqc sheaves on `S`-schemes over an affine scheme

Tools used in SGA 1, XI.5.1 (local triviality of principal homogeneous bundles under `𝔾_a` and
`𝔾_m`) to reduce statements about an fpqc sheaf `F` on the category of `S`-schemes over an affine
`a : Spec A ⟶ S` to a single faithfully flat ring map `A → B`:

* `subsingleton_of_isEmpty`: `F` has at most one section over an empty scheme;
* `exists_glue_sigma`: sections over finitely many `S`-schemes `Zᵢ` glue to a section over their
  disjoint union;
* `exists_faithfullyFlat_section`: if `F` has sections over the members of an fpqc covering
  sieve of `Spec A`, it has a section over `Spec B` for some faithfully flat `A → B` (a finite
  product of the rings of affine opens of the members);
* `exists_descend_of_faithfullyFlat`: a section over `Spec B` whose two inverse images to
  `Spec (B ⊗_A B)` agree comes from a section over `Spec A`.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presieve.IsSheaf (fpqc S) F)

include hF in
/-- An fpqc sheaf has at most one section over an `S`-scheme with empty underlying space. -/
lemma subsingleton_of_isEmpty (Y : Over S) [IsEmpty Y.left] : Subsingleton (F.obj (op Y)) := by
  have hbot : (⊥ : Sieve Y) ∈ fpqc S Y := by
    rw [GrothendieckTopology.mem_over_iff]
    have h := Precoverage.generate_mem_toGrothendieck
      (Scheme.bot_mem_propQCPrecoverage (P := @Flat) Y.left)
    rw [Sieve.generate_bot] at h
    rwa [OrderIso.map_bot]
  exact ⟨fun x y ↦ (hF _ hbot).isSeparatedFor.ext fun _ _ h ↦ h.elim⟩

section Sigma

variable {n : ℕ} (Z : Fin n → Over S)

/-- The disjoint union of finitely many `S`-schemes. -/
noncomputable def sigmaOver : Over S :=
  Over.mk (Sigma.desc fun i ↦ (Z i).hom)

/-- The inclusion of a summand into the disjoint union. -/
noncomputable def sigmaOverι (i : Fin n) : Z i ⟶ sigmaOver Z :=
  Over.homMk (Sigma.ι (fun i ↦ (Z i).left) i) (Sigma.ι_desc _ _)

include hF in
/-- Sections of an fpqc sheaf over finitely many `S`-schemes glue to a section over their
disjoint union. -/
lemma exists_glue_sigma (s : ∀ i, F.obj (op (Z i))) :
    ∃ t : F.obj (op (sigmaOver Z)), ∀ i, F.map (sigmaOverι Z i).op t = s i := by
  let R : Sieve (sigmaOver Z) := Sieve.generate (Presieve.ofArrows Z (sigmaOverι Z))
  have hR : R ∈ fpqc S (sigmaOver Z) := by
    rw [GrothendieckTopology.mem_over_iff]
    let 𝒰 := sigmaOpenCover (fun i ↦ (Z i).left)
    refine mem_fpqcTopology_of_openCover _ 𝒰 (fun i ↦ 𝒰.X i) (fun i ↦ 𝟙 _)
      (fun i ↦ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩) fun i ↦ ?_
    rw [Sieve.overEquiv_iff]
    refine ⟨Z i, Over.homMk (𝟙 _) ?_, sigmaOverι Z i, Presieve.ofArrows.mk i, ?_⟩
    · change 𝟙 _ ≫ (Z i).hom = (𝟙 _ ≫ Sigma.ι (fun i ↦ (Z i).left) i) ≫ Sigma.desc _
      simp
    · ext
      change 𝟙 _ ≫ Sigma.ι _ i = 𝒰.f i
      rw [Category.id_comp]
      rfl
  have hsh := (Presieve.isSheafFor_iff_generate _).2 (hF R hR)
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨t, ht, -⟩ := hsh s fun i j W gi gj h ↦ by
    have h' : gi.left ≫ Sigma.ι (fun i ↦ (Z i).left) i =
        gj.left ≫ Sigma.ι (fun i ↦ (Z i).left) j := by
      have := congr_arg CommaMorphism.left h
      exact this
    by_cases hij : i = j
    · subst hij
      have : gi = gj := Over.OverMorphism.ext ((cancel_mono _).1 h')
      rw [this]
    · have : IsEmpty W.left := isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hij
      exact (subsingleton_of_isEmpty hF W).elim _ _
  exact ⟨t, ht⟩

end Sigma

include hF in
/-- Descent of sections along a faithfully flat quasi-compact morphism `g : T ⟶ Y` of
`S`-schemes (the sheaf condition for the covering `{g}`): a section over `T` whose inverse
images under any two morphisms `p₁, p₂ : Z ⟶ T` with `p₁ ≫ g = p₂ ≫ g` agree comes from a section
over `Y`. -/
theorem exists_descend_of_fpqc {T Y : Over S} (g : T ⟶ Y) [Flat g.left] [Surjective g.left]
    [QuasiCompact g.left] (x : F.obj (op T))
    (hx : ∀ ⦃Z : Over S⦄ (p₁ p₂ : Z ⟶ T), p₁ ≫ g = p₂ ≫ g → F.map p₁.op x = F.map p₂.op x) :
    ∃ y : F.obj (op Y), F.map g.op y = x := by
  let R : Sieve Y := Sieve.generate (Presieve.singleton g)
  have hR : R ∈ fpqc S Y := by
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
      (Scheme.Hom.singleton_mem_fpqcPrecoverage g.left))
    rintro W w ⟨_, c, _, ⟨⟩, rfl⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨T, Over.homMk c (by simp), g, Presieve.singleton.mk, rfl⟩
  have hsh := (Presieve.isSheafFor_iff_generate _).2 (hF R hR)
  rw [Presieve.isSheafFor_singleton] at hsh
  obtain ⟨y, hy, -⟩ := hsh x fun {Z} p₁ p₂ e ↦ hx p₁ p₂ e
  exact ⟨y, hy⟩

section Affine

variable {A : CommRingCat.{u}} (a : Spec A ⟶ S)

/-- The `S`-scheme `Spec B`, for a ring map `φ : A → B` and `a : Spec A ⟶ S`. -/
noncomputable abbrev affOver {B : CommRingCat.{u}} (φ : A ⟶ B) : Over S :=
  Over.mk (Spec.map φ ≫ a)

/-- The morphism `Spec B ⟶ Spec A` of `S`-schemes. -/
noncomputable abbrev affOverπ {B : CommRingCat.{u}} (φ : A ⟶ B) : affOver a φ ⟶ Over.mk a :=
  Over.homMk (Spec.map φ)

set_option backward.isDefEq.respectTransparency.types false in
include hF in
/-- XI.5.1 (reduction to a single faithfully flat ring map): if an fpqc sheaf has sections over
the members of an fpqc covering sieve of `Spec A`, it has a section over `Spec B` for some
faithfully flat `A → B`. -/
theorem exists_faithfullyFlat_section (R : Sieve (Over.mk a)) (hR : R ∈ fpqc S (Over.mk a))
    (hne : ∀ ⦃Y : Over S⦄ (f : Y ⟶ Over.mk a), R f → Nonempty (F.obj (op Y))) :
    ∃ (B : CommRingCat.{u}) (φ : A ⟶ B), φ.hom.FaithfullyFlat ∧
      Nonempty (F.obj (op (affOver a φ))) := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨R', hR', hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.1 hR
  obtain ⟨𝒱, h𝒱, rfl⟩ := Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover.1 hR'
  have hc : IsCompact ((⊤ : (Spec A).Opens) : Set (Spec A)) := isCompact_univ
  obtain ⟨n, idx, V, hV, hVU⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    𝒱.toPreZeroHypercover hc
  let Z (k : Fin n) : Over S := Over.mk ((V k).ι ≫ 𝒱.f (idx k) ≫ a)
  have hZ (k : Fin n) : Nonempty (F.obj (op (Z k))) := by
    have hk := @hle _ (𝒱.f (idx k)) (Presieve.ofArrows.mk (idx k))
    rw [Sieve.overEquiv_iff] at hk
    obtain ⟨s⟩ := hne _ hk
    exact ⟨F.map (Over.homMk (V k).ι : Z k ⟶ Over.mk (𝒱.f (idx k) ≫ a)).op s⟩
  obtain ⟨t, -⟩ := exists_glue_sigma hF Z fun k ↦ (hZ k).some
  let w : (∐ fun k ↦ ((V k : Scheme) : Scheme)) ⟶ Spec A :=
    Sigma.desc fun k ↦ (V k).ι ≫ 𝒱.f (idx k)
  have : ∀ k, IsAffine (V k : Scheme) := hV
  have hw : Sigma.desc (fun k ↦ (Z k).hom) = w ≫ a := by
    ext k
    simp [w, Z]
  let W := ∐ fun k ↦ ((V k : Scheme) : Scheme)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ w)
  have hflat : Flat (Spec.map φ) := by
    have (k : Fin n) : Flat ((V k).ι ≫ 𝒱.f (idx k)) := by
      have : Flat (𝒱.f (idx k)) := 𝒱.map_prop _
      infer_instance
    rw [hφ]
    infer_instance
  have hsurj : Surjective (Spec.map φ) := by
    rw [hφ]
    refine ⟨fun x ↦ ?_⟩
    have hx : x ∈ ⋃ k, 𝒱.f (idx k) '' V k := by
      rw [hVU]
      trivial
    obtain ⟨_, ⟨k, rfl⟩, v, hv, rfl⟩ := hx
    refine ⟨W.isoSpec.hom (Sigma.ι (fun k ↦ ((V k : Scheme) : Scheme)) k ⟨v, hv⟩), ?_⟩
    have e : Sigma.ι (fun k ↦ ((V k : Scheme) : Scheme)) k ≫ w = (V k).ι ≫ 𝒱.f (idx k) :=
      Sigma.ι_desc _ _
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_apply, e]
    rfl
  refine ⟨_, φ, (flat_and_surjective_SpecMap_iff φ).1 ⟨hflat, hsurj⟩,
    ⟨F.map (Over.homMk W.isoSpec.inv ?_ : affOver a φ ⟶ sigmaOver Z).op t⟩⟩
  change W.isoSpec.inv ≫ Sigma.desc (fun k ↦ (Z k).hom) = Spec.map φ ≫ a
  refine (congrArg (fun m ↦ W.isoSpec.inv ≫ m) hw).trans ?_
  rw [hφ, Category.assoc]

/-- The morphism `Spec B' ⟶ Spec B` of `S`-schemes induced by `ψ : B ⟶ B'` under `A`. -/
noncomputable abbrev affOverHom {B B' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'} (ψ : B ⟶ B')
    (hψ : φ ≫ ψ = φ') : affOver a φ' ⟶ affOver a φ :=
  Over.homMk (Spec.map ψ) (by
    change Spec.map ψ ≫ Spec.map φ ≫ a = Spec.map φ' ≫ a
    rw [← hψ, Spec.map_comp, Category.assoc])

include hF in
/-- XI.5.1 (descent of sections): for a faithfully flat `φ : A → B`, a section of an fpqc sheaf
over `Spec B` whose two inverse images to `Spec (B ⊗_A B)` agree comes from a section over
`Spec A`. The ring `B ⊗_A B` is any pushout `P` of `φ` along itself. -/
theorem exists_descend_of_faithfullyFlat {B P : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) (inl inr : B ⟶ P) (h : IsPushout φ φ inl inr)
    (x : F.obj (op (affOver a φ)))
    (hx : F.map (affOverHom a inl rfl).op x = F.map (affOverHom a inr h.w.symm).op x) :
    ∃ y : F.obj (op (Over.mk a)), F.map (affOverπ a φ).op y = x := by
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  let R : Sieve (Over.mk a) := Sieve.generate (Presieve.singleton (affOverπ a φ))
  have hR : R ∈ fpqc S (Over.mk a) := by
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
      (Scheme.Hom.singleton_mem_fpqcPrecoverage (Spec.map φ)))
    rintro W g ⟨_, c, _, ⟨⟩, rfl⟩
    rw [Sieve.overEquiv_iff]
    refine ⟨affOver a φ, (Over.homMk c (by
      change c ≫ Spec.map φ ≫ a = (c ≫ Spec.map φ) ≫ a
      rw [Category.assoc]) : Over.mk ((c ≫ Spec.map φ) ≫ a) ⟶ affOver a φ), affOverπ a φ,
      Presieve.singleton.mk, rfl⟩
  have hsh := (Presieve.isSheafFor_iff_generate _).2 (hF R hR)
  rw [Presieve.isSheafFor_singleton] at hsh
  have hpb := isPullback_SpecMap_of_isPushout φ φ inl inr h
  obtain ⟨y, hy, -⟩ := hsh x fun {Z} p₁ p₂ e ↦ by
    have e' : p₁.left ≫ Spec.map φ = p₂.left ≫ Spec.map φ := congr_arg CommaMorphism.left e
    let k : Z ⟶ affOver a (φ ≫ inl) :=
      Over.homMk (hpb.lift p₁.left p₂.left e') (by
        change hpb.lift p₁.left p₂.left e' ≫ Spec.map (φ ≫ inl) ≫ a = Z.hom
        rw [Spec.map_comp, ← Category.assoc, ← Category.assoc, hpb.lift_fst, Category.assoc]
        exact Over.w p₁)
    have k₁ : k ≫ affOverHom a inl rfl = p₁ := by
      ext
      exact hpb.lift_fst _ _ _
    have k₂ : k ≫ affOverHom a inr h.w.symm = p₂ := by
      ext
      exact hpb.lift_snd _ _ _
    rw [← k₁, ← k₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hx]
  exact ⟨y, hy⟩

end Affine

end SGA.SGA1.ExposeXI
