/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.GroupObjectTorsor
import SGA.SGA1.ExposeVIII.MorphismDescent
import SGA.SGA1.ExposeVIII.PropertyDescent

/-!
# SGA 1, Exposé XI.4.1–XI.4.3: principal homogeneous bundles over a scheme

Let `G` be a group scheme over `S` (a group object of `Over S`) acting on an `S`-scheme `P`.
SGA writes the action on the right; we use left actions (`ModObj G P`, as in mathlib and
`SGA.Foundations.Etale`), which is equivalent through `g ↦ g⁻¹`.

* `P` is *formally principal homogeneous* if `G ×_S P → P ×_S P`, `(g, x) ↦ (g x, x)`, is an
  isomorphism (`ModObj.leftSMul`); then `P` is trivial if and only if it has a section
  (`IsTorsorObj.class_eq_trivialClass_iff`).
* XI.4.1: `P` is a *principal homogeneous bundle* (`IsPrincipalBundle`) if moreover there are an
  open covering `(Uᵢ)` of `S` and faithfully flat quasi-compact `S'ᵢ → Uᵢ` such that each
  `P ×_S S'ᵢ` has a section over `S'ᵢ`, i.e. is trivial.
* Principal homogeneous bundles are exactly the torsors for the fpqc topology on `S`-schemes
  (`isPrincipalBundle_iff_isTorsorObj`); so a bundle has a class in `H¹(S, G)`, trivial if and
  only if the bundle has a section, and two bundles have the same class if and only if they are
  equivariantly isomorphic (XI.4.4).
* XI.4.2: for `G` flat and quasi-compact over `S`, `P` is a principal homogeneous bundle if and
  only if it is formally principal homogeneous and faithfully flat and quasi-compact over `S`
  (`isPrincipalBundle_iff`). The proof is SGA's: `P ×_S S'ᵢ ≅ G ×_S S'ᵢ`, and flatness,
  surjectivity and quasi-compactness descend along `S'ᵢ → Uᵢ` (VIII.3.1, VIII.3.3, VIII.5.7).
* XI.4.3: if `G` is affine and flat over `S`, every principal homogeneous bundle is affine and
  flat over `S` (`IsPrincipalBundle.isAffineHom`), by VIII.5.6.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  MorphismProperty

namespace SGA.SGA1.ExposeXI

section Covering

/-- A sieve on a scheme `X` which, restricted to the members of an open covering, contains a
faithfully flat quasi-compact morphism, is an fpqc covering. -/
theorem mem_fpqcTopology_of_openCover {X : Scheme.{u}} (R : Sieve X) (𝒰 : X.OpenCover)
    (S' : 𝒰.I₀ → Scheme.{u}) (g : ∀ i, S' i ⟶ 𝒰.X i)
    (hg : ∀ i, (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (g i))
    (hR : ∀ i, R (g i ≫ 𝒰.f i)) :
    R ∈ Scheme.fpqcTopology X := by
  have h𝒰 : Sieve.generate 𝒰.presieve₀ ∈ Scheme.fpqcTopology X :=
    Precoverage.generate_mem_toGrothendieck (Scheme.zariskiPrecoverage_le_fpqcPrecoverage X 𝒰.mem₀)
  refine GrothendieckTopology.transitive _ h𝒰 R fun Y f hf ↦ ?_
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hf
  rw [Sieve.pullback_comp]
  refine GrothendieckTopology.pullback_stable _ h ?_
  obtain ⟨⟨_, _⟩, _⟩ := hg i
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    (Scheme.Hom.singleton_mem_fpqcPrecoverage (g i)))
  rintro W a ⟨_, b, _, ⟨⟩, rfl⟩
  exact (R.pullback (𝒰.f i)).downward_closed (hR i) b

end Covering

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (P : Over S) [ModObj G P]

/-- XI.4.1: `P` is a principal homogeneous bundle under `G`: it is formally principal
homogeneous (`G ×_S P ≅ P ×_S P`), and there are an open covering `(Uᵢ)` of `S` and faithfully
flat quasi-compact `gᵢ : S'ᵢ → Uᵢ` such that each `P ×_S S'ᵢ` has a section over `S'ᵢ`, i.e.
(SGA XI.4, before XI.4.1) is trivial. SGA takes `S'` the sum of the `S'ᵢ`; a section of
`P ×_S S'` is a family of sections of the `P ×_S S'ᵢ`. -/
structure IsPrincipalBundle : Prop where
  isIso_leftSMul : IsIso (ModObj.leftSMul G P)
  exists_trivialization : ∃ (𝒰 : Scheme.OpenCover.{u} S) (S' : 𝒰.I₀ → Scheme.{u})
    (g : ∀ i, S' i ⟶ 𝒰.X i),
      (∀ i, (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (g i)) ∧
      ∀ i, ∃ s : S' i ⟶ P.left, s ≫ P.hom = g i ≫ 𝒰.f i

variable {G P}

/-- XI.4.1: a principal homogeneous bundle is a torsor for the fpqc topology on `S`-schemes. -/
theorem IsPrincipalBundle.isTorsorObj (h : IsPrincipalBundle G P) :
    IsTorsorObj (Scheme.fpqcTopology.over S) G P := by
  obtain ⟨𝒰, S', g, hg, hs⟩ := h.exists_trivialization
  refine ⟨h.isIso_leftSMul, IsTorsorObj.locallyNonempty_of_covering ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine mem_fpqcTopology_of_openCover _ 𝒰 S' g hg fun i ↦ ?_
  rw [Sieve.overEquiv_iff]
  obtain ⟨s, hs⟩ := hs i
  exact ⟨(), ⟨Over.homMk s (by simpa using hs)⟩⟩

/-- XI.4.4: the class in `H¹(S, G)` of a principal homogeneous bundle. -/
noncomputable abbrev IsPrincipalBundle.class (h : IsPrincipalBundle G P) :
    H1 (Scheme.fpqcTopology.over S) (yonedaGrpObj G) :=
  h.isTorsorObj.class

/-- XI.4: a principal homogeneous bundle is trivial (has the trivial class) if and only if it has
a section over `S`. -/
theorem IsPrincipalBundle.class_eq_trivialClass_iff (h : IsPrincipalBundle G P) :
    h.class = H1.trivialClass _ (yonedaGrpObj G) (isSheaf_yonedaGrpObj G) ↔
      Nonempty (𝟙_ (Over S) ⟶ P) :=
  h.isTorsorObj.class_eq_trivialClass_iff

/-- XI.4.4: two principal homogeneous bundles have the same class in `H¹(S, G)` if and only if
they are isomorphic as `S`-schemes with `G`-action. -/
theorem IsPrincipalBundle.class_eq_class_iff {Q : Over S} [ModObj G Q]
    (hP : IsPrincipalBundle G P) (hQ : IsPrincipalBundle G Q) :
    hP.class = hQ.class ↔ ∃ e : P ≅ Q, IsModHom G e.hom :=
  ⟨hP.isTorsorObj.exists_isModHom_of_class_eq hQ.isTorsorObj,
    fun ⟨e, _⟩ ↦ hP.isTorsorObj.class_eq_of_isModHom hQ.isTorsorObj e.hom⟩

section BaseChange

variable {Q : MorphismProperty Scheme.{u}} [Q.RespectsLeft (isomorphisms Scheme.{u})]
  [Q.IsStableUnderBaseChange]

/-- For `P` formally principal homogeneous, `P ×_S P → P` (second projection) is isomorphic to
the base change `G ×_S P → P` of `G → S`. -/
lemma pullback_snd_self_of_isIso (h : IsIso (ModObj.leftSMul G P)) (hG : Q G.hom) :
    Q (pullback.snd P.hom P.hom) := by
  have e : (ModObj.leftSMul G P).left ≫ pullback.snd P.hom P.hom = pullback.snd G.hom P.hom :=
    congr_arg CommaMorphism.left (ModObj.leftSMul_snd (M := G) (X := P))
  have : IsIso (ModObj.leftSMul G P).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (ModObj.leftSMul G P)))
  have e' : pullback.snd P.hom P.hom =
      inv (ModObj.leftSMul G P).left ≫ pullback.snd G.hom P.hom := by
    rw [← e, IsIso.inv_hom_id_assoc]
  rw [e']
  exact RespectsLeft.precomp _ (inferInstance : IsIso _) _ (Q.pullback_snd _ _ hG)

/-- XI.4.2: if `P` is formally principal homogeneous and has a section `s` over `t : T → S`, then
`P ×_S T ≅ G ×_S T` over `T`; hence every property of `G → S` stable under base change holds for
`P ×_S T → T`. -/
lemma pullback_snd_of_section (h : IsIso (ModObj.leftSMul G P)) (hG : Q G.hom) {T : Scheme.{u}}
    (s : T ⟶ P.left) : Q (pullback.snd P.hom (s ≫ P.hom)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd]
  exact RespectsLeft.precomp _ (inferInstance : IsIso _) _
    (Q.pullback_snd _ _ (pullback_snd_self_of_isIso h hG))

variable [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] [IsZariskiLocalAtTarget Q]

omit [Q.RespectsLeft (isomorphisms Scheme.{u})] in
set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.2, (i) ⇒ (ii), and XI.4.3: a property of morphisms stable under base change, local on
the target and descending along faithfully flat quasi-compact morphisms passes from `G → S` to
every principal homogeneous bundle `P → S`. -/
theorem IsPrincipalBundle.of_descendsAlong (h : IsPrincipalBundle G P) (hG : Q G.hom) :
    Q P.hom := by
  have : Q.RespectsLeft (isomorphisms Scheme.{u}) := inferInstance
  obtain ⟨𝒰, S', g, hg, hs⟩ := h.exists_trivialization
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun i ↦ ?_
  obtain ⟨s, hs⟩ := hs i
  change Q (pullback.snd P.hom (𝒰.f i))
  refine of_pullback_fst_of_descendsAlong (hg i) ?_
  have h₁ := pullback_snd_of_section (Q := Q) h.isIso_leftSMul hG s
  rw [hs] at h₁
  rw [← pullbackSymmetry_hom_comp_snd, ← pullbackLeftPullbackSndIso_hom_snd, ← Category.assoc]
  exact RespectsLeft.precomp _ (inferInstance : IsIso _) _ h₁

end BaseChange

/-- The structure morphism of a group scheme is surjective: it has the unit section. -/
lemma surjective_hom_of_grpObj (G : Over S) [GrpObj G] : Surjective G.hom := by
  refine ⟨fun x ↦ ⟨η[G].left x, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, Over.w η[G]]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.2, (ii) ⇒ (i): the base change `S' = P` trivializes `P`, with the diagonal section. -/
theorem isPrincipalBundle_of_flat [Flat P.hom] [Surjective P.hom] [QuasiCompact P.hom]
    (h : IsIso (ModObj.leftSMul G P)) : IsPrincipalBundle G P :=
  ⟨h, Scheme.coverOfIsIso.{u} (𝟙 S), fun _ ↦ P.left, fun _ ↦ P.hom,
    fun _ ↦ ⟨⟨‹Surjective P.hom›, ‹Flat P.hom›⟩, ‹QuasiCompact P.hom›⟩,
    fun _ ↦ ⟨𝟙 _, by
      rw [Scheme.coverOfIsIso_f]
      exact (Category.id_comp P.hom).trans (Category.comp_id P.hom).symm⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.2: for `G` flat and quasi-compact over `S`, `P` is a principal homogeneous bundle if and
only if it is formally principal homogeneous and faithfully flat and quasi-compact over `S`. -/
theorem isPrincipalBundle_iff [Flat G.hom] [QuasiCompact G.hom] :
    IsPrincipalBundle G P ↔
      IsIso (ModObj.leftSMul G P) ∧ Flat P.hom ∧ Surjective P.hom ∧ QuasiCompact P.hom := by
  constructor
  · intro h
    have hG : Surjective G.hom := surjective_hom_of_grpObj G
    exact ⟨h.isIso_leftSMul, h.of_descendsAlong (Q := @Flat) inferInstance,
      h.of_descendsAlong (Q := @Surjective) hG, h.of_descendsAlong (Q := @QuasiCompact)
        inferInstance⟩
  · rintro ⟨h, hflat, hsurj, hqc⟩
    exact isPrincipalBundle_of_flat h

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.3: if `G` is affine and flat over `S`, every principal homogeneous bundle under `G` is
affine and flat over `S`. -/
theorem IsPrincipalBundle.isAffineHom [IsAffineHom G.hom] [Flat G.hom]
    (h : IsPrincipalBundle G P) : IsAffineHom P.hom ∧ Flat P.hom :=
  ⟨h.of_descendsAlong (Q := @IsAffineHom) inferInstance,
    h.of_descendsAlong (Q := @Flat) inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.1: conversely, a torsor for the fpqc topology on `S`-schemes is a principal homogeneous
bundle: over each affine open `U` of `S`, finitely many affine opens of the members of an fpqc
covering trivializing `P` give a faithfully flat quasi-compact `S'_U → U` trivializing `P`. -/
theorem isPrincipalBundle_of_isTorsorObj (h : IsTorsorObj (Scheme.fpqcTopology.over S) G P) :
    IsPrincipalBundle G P := by
  obtain ⟨R, hR, hne⟩ := h.locallyNonempty (𝟙_ (Over S))
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨R', hR', hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.1 hR
  obtain ⟨𝒱, h𝒱, rfl⟩ := Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover.1 hR'
  have hsec : ∀ i, ∃ t : 𝒱.X i ⟶ P.left, t ≫ P.hom = 𝒱.f i := by
    intro i
    have hi := @hle _ (𝒱.f i) (Presieve.ofArrows.mk i)
    rw [Sieve.overEquiv_iff] at hi
    obtain ⟨t⟩ := hne _ hi
    exact ⟨t.left, by simp⟩
  choose t ht using hsec
  have key (U : S.affineOpens) : ∃ (n : ℕ) (a : Fin n → 𝒱.I₀) (V : ∀ k, (𝒱.X (a k)).Opens),
      (∀ k, IsAffineOpen (V k)) ∧ ⋃ k, 𝒱.f (a k) '' V k = (U : Set S) :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒱.toPreZeroHypercover U.2.isCompact
  choose n a V hV hVU using key
  have hsub (U : S.affineOpens) (k : Fin (n U)) :
      Set.range ((V U k).ι ≫ 𝒱.f (a U k)) ⊆ Set.range U.1.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, ← hVU U]
    exact Set.subset_iUnion (fun k ↦ 𝒱.f (a U k) '' V U k) k
  let lift (U : S.affineOpens) (k : Fin (n U)) : (V U k : Scheme) ⟶ U.1 :=
    IsOpenImmersion.lift U.1.ι ((V U k).ι ≫ 𝒱.f (a U k)) (hsub U k)
  have hlift (U : S.affineOpens) (k : Fin (n U)) :
      lift U k ≫ U.1.ι = (V U k).ι ≫ 𝒱.f (a U k) :=
    IsOpenImmersion.lift_fac _ _ _
  have hsurj (U : S.affineOpens) : Surjective (Sigma.desc (lift U)) := by
    refine ⟨fun u ↦ ?_⟩
    have hu : U.1.ι u ∈ ⋃ k, 𝒱.f (a U k) '' V U k := by
      rw [hVU U, Scheme.Opens.ι_apply]
      exact u.2
    obtain ⟨_, ⟨k, rfl⟩, v, hv, hvu⟩ := hu
    refine ⟨(Sigma.ι (fun k : Fin (n U) ↦ (V U k : Scheme)) k) ⟨v, hv⟩,
      U.1.ι.isOpenEmbedding.injective ?_⟩
    have e : (Sigma.desc (lift U)) ((Sigma.ι (fun k : Fin (n U) ↦ (V U k : Scheme)) k)
        ⟨v, hv⟩) = lift U k ⟨v, hv⟩ := by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    rw [e, ← Scheme.Hom.comp_apply, hlift, Scheme.Hom.comp_apply, ← hvu]
    rfl
  have hflat (U : S.affineOpens) : Flat (Sigma.desc (lift U)) := by
    have (k : Fin (n U)) : Flat (lift U k) := by
      refine MorphismProperty.of_postcomp @Flat (W' := @IsOpenImmersion) (lift U k) U.1.ι
        inferInstance ?_
      rw [hlift]
      have : Flat (𝒱.f (a U k)) := 𝒱.map_prop _
      infer_instance
    infer_instance
  have hqc (U : S.affineOpens) : QuasiCompact (Sigma.desc (lift U)) := by
    have (k : Fin (n U)) : IsAffine (V U k : Scheme) := hV U k
    have : IsAffine U.1 := U.2
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have hsecU (U : S.affineOpens) : Sigma.desc (fun k ↦ (V U k).ι ≫ t (a U k)) ≫ P.hom =
      Sigma.desc (lift U) ≫ U.1.ι := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, hlift, Category.assoc, ht]
  let 𝒰 : Scheme.OpenCover.{u} S :=
    Scheme.Cover.mkOfCovers S.affineOpens (fun U ↦ U.1) (fun U ↦ U.1.ι) fun x ↦ by
      obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
        ((iSup_affineOpens_eq_top S).ge (Set.mem_univ x))
      exact ⟨U, ⟨x, hxU⟩, rfl⟩
  exact ⟨h.isIso_leftSMul, 𝒰, fun U ↦ ∐ fun k : Fin (n U) ↦ (V U k : Scheme),
    fun U ↦ Sigma.desc (lift U), fun U ↦ ⟨⟨hsurj U, hflat U⟩, hqc U⟩, fun U ↦ ⟨_, hsecU U⟩⟩

/-- XI.4.1: a principal homogeneous bundle is the same as a torsor for the fpqc topology on
`S`-schemes. -/
theorem isPrincipalBundle_iff_isTorsorObj :
    IsPrincipalBundle G P ↔ IsTorsorObj (Scheme.fpqcTopology.over S) G P :=
  ⟨IsPrincipalBundle.isTorsorObj, isPrincipalBundle_of_isTorsorObj⟩

end SGA.SGA1.ExposeXI
