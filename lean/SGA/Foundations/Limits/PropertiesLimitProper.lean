/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Devissage
import SGA.Foundations.Limits.PropertiesLimitSeparated
import SGA.Foundations.Limits.SpreadingOutGluing
import SGA.Foundations.Limits.SpreadingOutNoetherian

/-!
# Properness over a limit descends to a finite level

EGA IV 8.10.5 (xii) (Stacks 081F), by Chow's lemma as in Stacks:
`AlgebraicGeometry.Scheme.properLimitStatement` proves `Scheme.ProperLimitStatement` for every
cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps.
The proof reduces to affine diagrams (`Scheme.limitDescends_of_affine`), then to a model over a
noetherian affine scheme (noetherian approximation of the affine member), where Chow's lemma
applies.

* `AlgebraicGeometry.Scheme.universallyClosed_of_jointly_surjective`: `f : X ⟶ S` is universally
  closed if `X` is covered by the images of finitely many `g_a : W_a ⟶ X` with every `g_a ≫ f`
  universally closed.
* `AlgebraicGeometry.Scheme.exists_isProper_of_isImmersion`: a morphism `W_j ⟶ E j` which factors
  as an immersion into a proper `E j`-scheme becomes proper at a finite level as soon as its base
  change to the limit is proper (the immersion becomes a proper immersion, hence a closed
  immersion, over the limit; closed immersions descend).
* `AlgebraicGeometry.Scheme.exists_isProper_of_isNoetherian_model`: let `X_j = Y ×_T E j` with
  `Y` separated and of finite type over a noetherian affine scheme `T`. If `X_j ×_{E j} c.pt` is
  proper over `c.pt`, then `X_j ×_{E j} E k` is proper over `E k` for some `k`. By Chow's lemma
  (`exists_isHProjective_isIso_morphismRestrict`, for the integral closed subschemes on the
  finitely many irreducible components of `Y`), `Y` is covered by the images of proper morphisms
  `X'_a ⟶ Y` with `X'_a` H-quasi-projective over `T`.
* `AlgebraicGeometry.Scheme.limitDescends_isProper_of_isNoetherian`: EGA IV 8.10.5 (xii) for
  diagrams of noetherian affine schemes (separatedness descends first).
* `AlgebraicGeometry.Scheme.exists_isProper_of_isSeparated_of_isAffine`: a separated model over an
  affine member `E k`: spread it out over `Spec B`, `B ⊆ Γ(E k)` of finite type over `ℤ`
  (`Algebra.FGSubalgebra.isLimitSpecCone`, EGA IV 8.8.2 (ii)), make it separated there, and apply
  `exists_isProper_of_isNoetherian_model`.
* `AlgebraicGeometry.Scheme.limitDescendsAffine_isProper`, `Scheme.properLimitStatement`:
  EGA IV 8.10.5 (xii) for diagrams of affine schemes, and in general.

## References

* [EGA IV₃, 8.10.5][EGA4]
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ S` is universally closed if `X` is covered by the images of finitely many
morphisms `g_a : W_a ⟶ X` with every `g_a ≫ f` universally closed. -/
theorem Scheme.universallyClosed_of_jointly_surjective {ι : Type*} [Finite ι] {X S : Scheme.{u}}
    (f : X ⟶ S) {W : ι → Scheme.{u}} (g : ∀ a, W a ⟶ X) (hg : ∀ x, ∃ a, x ∈ Set.range (g a))
    (hW : ∀ a, UniversallyClosed (g a ≫ f)) : UniversallyClosed f := by
  constructor
  intro X' S' i₁ i₂ f' H
  have hc (a : ι) : IsClosedMap (pullback.snd (g a) i₁ ≫ f') :=
    (hW a).universally_isClosedMap _ _ _
      ((IsPullback.of_hasPullback (g a) i₁).flip.paste_horiz H)
  intro Z hZ
  have e : f' '' Z = ⋃ a, (pullback.snd (g a) i₁ ≫ f') '' (pullback.snd (g a) i₁ ⁻¹' Z) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, w, hw⟩ := hg (i₁ z)
      obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
      refine Set.mem_iUnion.mpr ⟨a, p, by rwa [Set.mem_preimage, hp], ?_⟩
      rw [Scheme.Hom.comp_apply, hp]
    · intro hy
      obtain ⟨a, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨_, hp, rfl⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun a ↦
    hc a _ (hZ.preimage (pullback.snd (g a) i₁).continuous)

/-- `(a ≫ b) ×_S S'` is `a ×_X (X ×_S S')` followed by `X ×_S S' ⟶ S'`: the base change of a
composite has a property stable under base change and composition if `a` has it and the base
change of `b` has it. -/
lemma Scheme.pullback_snd_comp_left {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.RespectsIso]
    {W X S S' : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ S) (g : S' ⟶ S) (ha : P a)
    (hb : P (pullback.snd b g)) : P (pullback.snd (a ≫ b) g) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd b g a,
    MorphismProperty.cancel_left_of_respectsIso P]
  exact P.comp_mem _ _ (MorphismProperty.pullback_snd _ _ ha) hb

/-- Transport of a property of `pullback.snd m g` along an equality `m = m'`. -/
lemma Scheme.of_pullback_snd_eq_left {P : MorphismProperty Scheme.{u}} {X S T : Scheme.{u}}
    {m m' : X ⟶ S} {g : T ⟶ S} (h : m = m') (hP : P (pullback.snd m g)) :
    P (pullback.snd m' g) := by
  subst h
  exact hP

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)] {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `W_j ⟶ E j` which factors as an immersion `i` of finite presentation into a proper
`E j`-scheme becomes proper over some `E k` if its base change to the limit is proper. -/
theorem Scheme.exists_isProper_of_isImmersion (hc : IsLimit c) {j : I} {Wj Pj : Scheme.{u}}
    (i : Wj ⟶ Pj) (p : Pj ⟶ E.obj j) [IsImmersion i] [LocallyOfFinitePresentation i]
    [QuasiCompact i] [IsProper p] (hW : IsProper (pullback.snd (i ≫ p) (c.π.app j))) :
    ∃ k : Over j, IsProper (pullback.snd (i ≫ p) (E.map k.hom)) := by
  let fP := pullback.fst p (c.π.app j)
  let sP := pullback.snd p (c.π.app j)
  have hP : IsPullback fP sP p (c.π.app j) := IsPullback.of_hasPullback _ _
  let i' := pullback.snd i fP
  have hY : IsPullback (pullback.fst i fP) i' i fP := IsPullback.of_hasPullback _ _
  -- over the limit, `i` becomes a proper immersion, i.e. a closed immersion
  have h1 : IsProper (i' ≫ sP) := by
    rw [← pullbackRightPullbackFstIso_hom_snd p (c.π.app j) i,
      MorphismProperty.cancel_left_of_respectsIso @IsProper]
    exact hW
  have : UniversallyClosed i' := UniversallyClosed.of_comp_of_isSeparated i' sP
  have : IsImmersion i' := MorphismProperty.pullback_snd _ _ inferInstance
  have hci : IsClosedImmersion i' := IsClosedImmersion.of_isImmersion_of_universallyClosed i'
  obtain ⟨k, hk⟩ := Scheme.limitDescends_relative Scheme.limitDescends_isClosedImmersion hc p i
    hP hY hci
  refine ⟨k, ?_⟩
  rw [← pullbackRightPullbackFstIso_inv_snd_snd p (E.map k.hom) i,
    MorphismProperty.cancel_left_of_respectsIso @IsProper]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) One piece of a Chow cover: let `X_j = Y ×_T E j` (`T` locally noetherian)
with proper base change to the limit, and `h : X' ⟶ Y` proper with `X'` H-quasi-projective over
`T`. Then the base change of `X' ×_T E j ⟶ X_j` to `X_j ×_{E j} E m` is universally closed over
`E m` for all `m` below some `k`. -/
theorem Scheme.exists_universallyClosed_of_isHQuasiProjective (hc : IsLimit c) {j : I}
    {T : Scheme.{u}} [IsLocallyNoetherian T] (t : E.obj j ⟶ T) {Y : Scheme.{u}} (p : Y ⟶ T)
    {X' : Scheme.{u}} (h : X' ⟶ Y) [IsProper h] (hq : IsHQuasiProjective (h ≫ p))
    (hX : IsProper (pullback.snd (pullback.snd p t) (c.π.app j))) :
    ∃ k : Over j, ∀ (m : Over j) (_ : m ⟶ k),
      UniversallyClosed (pullback.snd (pullback.snd h (pullback.fst p t))
        (pullback.fst (pullback.snd p t) (E.map m.hom)) ≫
          pullback.snd (pullback.snd p t) (E.map m.hom)) := by
  obtain ⟨σ, _, i, hi, hiqc, hfac⟩ := hq
  let π := ℙ(σ; T) ↘ T
  have : IsLocallyNoetherian ℙ(σ; T) := LocallyOfFiniteType.isLocallyNoetherian π
  have : LocallyOfFinitePresentation i := inferInstance
  let pP := pullback.snd π t
  let u := pullback.snd i (pullback.fst π t)
  have key : ∀ (m₁ m₂ : X' ⟶ T), m₁ = m₂ → ∃ φ : pullback m₂ t ≅ pullback m₁ t,
      φ.hom ≫ pullback.snd m₁ t = pullback.snd m₂ t := by
    rintro _ _ rfl
    exact ⟨Iso.refl _, by simp⟩
  obtain ⟨φ, hφ⟩ := key _ _ hfac
  let hj := pullback.snd h (pullback.fst p t)
  let qj := pullback.snd p t
  let ψ : pullback h (pullback.fst p t) ≅ pullback i (pullback.fst π t) :=
    pullbackRightPullbackFstIso p t h ≪≫ φ ≪≫ (pullbackRightPullbackFstIso π t i).symm
  have hψ : ψ.hom ≫ u ≫ pP = hj ≫ qj := by
    change (pullbackRightPullbackFstIso p t h).hom ≫ φ.hom ≫
      (pullbackRightPullbackFstIso π t i).inv ≫ u ≫ pP = hj ≫ qj
    rw [pullbackRightPullbackFstIso_inv_snd_snd]
    erw [hφ]
    exact pullbackRightPullbackFstIso_hom_snd _ _ _
  -- the base change of `u ≫ pP` to the limit is proper
  have hW : IsProper (pullback.snd (u ≫ pP) (c.π.app j)) := by
    have e : (ψ.inv ≫ hj) ≫ qj = u ≫ pP := by
      rw [Category.assoc, ← hψ, Iso.inv_hom_id_assoc]
    exact Scheme.of_pullback_snd_eq_left e
      (Scheme.pullback_snd_comp_left (P := @IsProper) _ _ _ inferInstance hX)
  obtain ⟨k, hk⟩ := Scheme.exists_isProper_of_isImmersion hc u pP hW
  refine ⟨k, fun m ψm ↦ ?_⟩
  have hkm : IsProper (pullback.snd (u ≫ pP) (E.map m.hom)) := by
    have := Scheme.pullback_snd_comp_of_isStableUnderBaseChange (P := @IsProper) (u ≫ pP)
      (E.map ψm.left) (E.map k.hom) hk
    exact Scheme.of_pullback_snd_eq (by rw [← E.map_comp, Over.w ψm]) this
  rw [← pullbackRightPullbackFstIso_hom_snd qj (E.map m.hom) hj]
  have : IsProper (pullback.snd (hj ≫ qj) (E.map m.hom)) :=
    Scheme.of_pullback_snd_eq_left hψ
      (Scheme.pullback_snd_comp_left (P := @IsProper) ψ.hom (u ≫ pP) _ inferInstance hkm)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (xii) for a model coming from a noetherian base: let `T` be a noetherian affine
scheme, `Y ⟶ T` separated and of finite type, `t : E j ⟶ T` and `X_j = Y ×_T E j`. If the base
change of `X_j` to the limit is proper, then `X_j ×_{E j} E k ⟶ E k` is proper for some `k`. The
proof uses Chow's lemma on the finitely many irreducible components of `Y`. -/
theorem Scheme.exists_isProper_of_isNoetherian_model (hc : IsLimit c) {j : I} {T : Scheme.{u}}
    [IsAffine T] [IsNoetherian T] (t : E.obj j ⟶ T) {Y : Scheme.{u}} (p : Y ⟶ T) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (hX : IsProper (pullback.snd (pullback.snd p t) (c.π.app j))) :
    ∃ k : Over j, IsProper (pullback.snd (pullback.snd p t) (E.map k.hom)) := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian Y := {}
  -- Chow's lemma on each irreducible component of `Y`
  have chow (C : irreducibleComponents Y) : ∃ (X' : Scheme.{u}) (h : X' ⟶ Y),
      IsProper h ∧ Set.range h = (C : Set Y) ∧ IsHQuasiProjective (h ≫ p) := by
    obtain ⟨Z, ι, hι, hZ, hrange⟩ := CohomologyAux.exists_integral_closedImmersion (C : Set Y)
      (isClosed_of_mem_irreducibleComponents _ C.2)
      C.2.1
    obtain ⟨X', π, -, hπ, hsurj, hq, -, -, -⟩ := exists_isHProjective_isIso_morphismRestrict (ι ≫ p)
    refine ⟨X', π ≫ ι, inferInstance, ?_, by rwa [Category.assoc]⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.surj.range_eq,
      Set.image_univ, hrange]
  choose X' h hhp hrange hq using chow
  have piece (C : irreducibleComponents Y) :=
    @Scheme.exists_universallyClosed_of_isHQuasiProjective I _ _ E _ _ _ c hc j T _ t Y p (X' C)
      (h C) (hhp C) (hq C) hX
  choose k hk using piece
  have : Finite (irreducibleComponents Y) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  have : Fintype (irreducibleComponents Y) := Fintype.ofFinite _
  obtain ⟨m, fm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  replace fm (C : irreducibleComponents Y) : m ⟶ k C :=
    (@fm (k C) (Finset.mem_image_of_mem k (Finset.mem_univ C))).some
  refine ⟨m, ?_⟩
  have hUC : UniversallyClosed (pullback.snd (pullback.snd p t) (E.map m.hom)) := by
    refine Scheme.universallyClosed_of_jointly_surjective _
      (fun C ↦ pullback.snd (pullback.snd (h C) (pullback.fst p t))
        (pullback.fst (pullback.snd p t) (E.map m.hom))) (fun x ↦ ?_) (fun C ↦ hk C m (fm C))
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp
      ((sUnion_irreducibleComponents (X := Y)).symm ▸ Set.mem_univ
        (pullback.fst p t (pullback.fst (pullback.snd p t) (E.map m.hom) x)))
    refine ⟨⟨C, hC⟩, ?_⟩
    rw [Scheme.Pullback.range_snd, Set.mem_preimage, Scheme.Pullback.range_snd, Set.mem_preimage,
      hrange]
    exact hxC
  exact { }

omit [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] in
set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (xii) for cofiltered diagrams of noetherian affine schemes with affine transition
maps: if the base change to the limit of a morphism of finite presentation `X_j ⟶ E j` is proper,
then so is its base change to some `E k`. -/
theorem Scheme.limitDescends_isProper_of_isNoetherian [∀ i, IsAffine (E.obj i)]
    [∀ i, IsNoetherian (E.obj i)] (hc : IsLimit c) {j : I} {X Xj : Scheme.{u}}
    (qj : Xj ⟶ E.obj j) [LocallyOfFinitePresentation qj] [QuasiCompact qj] [QuasiSeparated qj]
    {e : X ⟶ Xj} {q : X ⟶ c.pt} (h : IsPullback e q qj (c.π.app j)) [IsProper q] :
    ∃ (k : I) (g : k ⟶ j), IsProper (pullback.snd qj (E.map g)) := by
  obtain ⟨k₁, g₁, hsep⟩ := Scheme.limitDescends_isSeparated E c hc qj e q h inferInstance
  let p := pullback.snd qj (E.map g₁)
  -- `qj` over the limit, in canonical form
  have hq : IsProper (pullback.snd qj (c.π.app j)) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom _).mp
      (by rw [h.isoPullback_hom_snd]; infer_instance)
  have hp : IsProper (pullback.snd p (c.π.app k₁)) := by
    have := (MorphismProperty.arrow_mk_iso_iff @IsProper
      (Scheme.pullbackSndCompArrowIso qj (c.π.app k₁) (E.map g₁))).mp
      (Scheme.of_pullback_snd_eq (c.w g₁).symm hq)
    exact this
  -- `p` and `pullback.snd p (𝟙 _)` differ by an isomorphism
  have e₁ : pullback.fst p (𝟙 (E.obj k₁)) ≫ p = pullback.snd p (𝟙 (E.obj k₁)) := by
    rw [pullback.condition, Category.comp_id]
  have hX : IsProper (pullback.snd (pullback.snd p (𝟙 (E.obj k₁))) (c.π.app k₁)) :=
    Scheme.of_pullback_snd_eq_left e₁
      (Scheme.pullback_snd_comp_left (P := @IsProper) _ _ _ inferInstance hp)
  obtain ⟨k, hk⟩ := Scheme.exists_isProper_of_isNoetherian_model hc (𝟙 (E.obj k₁)) p hX
  have e₂ : inv (pullback.fst p (𝟙 (E.obj k₁))) ≫ pullback.snd p (𝟙 (E.obj k₁)) = p := by
    rw [← e₁, IsIso.inv_hom_id_assoc]
  have hk' : IsProper (pullback.snd p (E.map k.hom)) :=
    Scheme.of_pullback_snd_eq_left e₂
      (Scheme.pullback_snd_comp_left (P := @IsProper) _ _ _ inferInstance hk)
  refine ⟨k.left, k.hom ≫ g₁, ?_⟩
  have := (MorphismProperty.arrow_mk_iso_iff @IsProper
    (Scheme.pullbackSndCompArrowIso qj (E.map k.hom) (E.map g₁))).mpr hk'
  exact Scheme.of_pullback_snd_eq (E.map_comp k.hom g₁).symm this

omit [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] in
set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (xii) for a separated model over an affine member: let `E k` be affine and
`p : X_k ⟶ E k` separated and of finite presentation. If the base change of `p` to the limit is
proper, so is its base change to some `E m`. The model is spread out over a noetherian affine
`Spec B`, `B ⊆ Γ(E k)` of finite type over `ℤ` (noetherian approximation,
`Algebra.FGSubalgebra.isLimitSpecCone`, and EGA IV 8.8.2 (ii)), separated there after enlarging
`B` (`Scheme.limitDescends_isSeparated`), and Chow's lemma applies over `Spec B`
(`Scheme.exists_isProper_of_isNoetherian_model`). -/
theorem Scheme.exists_isProper_of_isSeparated_of_isAffine [∀ i, IsAffine (E.obj i)]
    (hc : IsLimit c) {k : I} {Xk : Scheme.{u}} (p : Xk ⟶ E.obj k) [LocallyOfFinitePresentation p]
    [QuasiCompact p] [IsSeparated p] (hp : IsProper (pullback.snd p (c.π.app k))) :
    ∃ m : Over k, IsProper (pullback.snd p (E.map m.hom)) := by
  -- the noetherian approximation of `Γ(E k)`
  let A := Γ(E.obj k, ⊤)
  let D := Algebra.FGSubalgebra.schemeDiagram ℤ A
  let cD := Algebra.FGSubalgebra.specCone ℤ A
  have hcD : IsLimit cD := Algebra.FGSubalgebra.isLimitSpecCone ℤ A
  let ι : E.obj k ≅ cD.pt := (E.obj k).isoSpec
  let q' : Xk ⟶ cD.pt := p ≫ ι.hom
  have : IsSeparated q' := inferInstance
  -- spreading out (EGA IV 8.8.2 (ii)) and separatedness at a lower level
  obtain ⟨B, YB, qB, eB, _, _, _, hB⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation hcD q'
  obtain ⟨B', gB, hsepB⟩ := Scheme.limitDescends_isSeparated D cD hcD qB eB q' hB inferInstance
  let M₀ : Scheme.LimitModel cD q' B := { obj := YB, hom := qB, proj := eB, isPullback := hB }
  let M := M₀.lower gB
  have : IsSeparated M.hom := hsepB
  let t : E.obj k ⟶ D.obj B' := ι.hom ≫ cD.π.app B'
  have hM : IsPullback M.proj p M.hom t :=
    M.isPullback.of_iso (Iso.refl _) (Iso.refl _) ι.symm (Iso.refl _) (by simp)
      (by simp [q']) (by simp) (by simp [t])
  -- `X_k = Y ×_{Spec B'} E k`
  let φ := hM.isoPullback
  have hφ : φ.hom ≫ pullback.snd M.hom t = p := hM.isoPullback_hom_snd
  have hφ' : φ.inv ≫ p = pullback.snd M.hom t := by rw [← hφ, Iso.inv_hom_id_assoc]
  have hX : IsProper (pullback.snd (pullback.snd M.hom t) (c.π.app k)) :=
    Scheme.of_pullback_snd_eq_left hφ'
      (Scheme.pullback_snd_comp_left (P := @IsProper) _ _ _ inferInstance hp)
  have : IsNoetherian (D.obj B') := inferInstance
  obtain ⟨m, hm⟩ := Scheme.exists_isProper_of_isNoetherian_model hc t M.hom hX
  exact ⟨m, Scheme.of_pullback_snd_eq_left hφ
    (Scheme.pullback_snd_comp_left (P := @IsProper) _ _ _ inferInstance hm)⟩

omit [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)] in
set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (xii) for cofiltered diagrams of affine schemes (with affine transition maps):
if the base change to the limit of a morphism of finite presentation `X_j ⟶ E j` is proper, then
so is its base change to some `E k`. -/
theorem Scheme.limitDescendsAffine_isProper :
    Scheme.LimitDescendsAffineStatement.{u} @IsProper := by
  intro I _ _ E _ _ c hc j X Xj qj _ _ _ e q h hq
  obtain ⟨k₁, g₁, hsep⟩ := Scheme.limitDescends_isSeparated E c hc qj e q h inferInstance
  let p := pullback.snd qj (E.map g₁)
  have hq' : IsProper (pullback.snd qj (c.π.app j)) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom _).mp
      (by rw [h.isoPullback_hom_snd]; exact hq)
  have hp : IsProper (pullback.snd p (c.π.app k₁)) :=
    (MorphismProperty.arrow_mk_iso_iff @IsProper
      (Scheme.pullbackSndCompArrowIso qj (c.π.app k₁) (E.map g₁))).mp
      (Scheme.of_pullback_snd_eq (c.w g₁).symm hq')
  obtain ⟨k, hk⟩ := Scheme.exists_isProper_of_isSeparated_of_isAffine hc p hp
  refine ⟨k.left, k.hom ≫ g₁, ?_⟩
  have := (MorphismProperty.arrow_mk_iso_iff @IsProper
    (Scheme.pullbackSndCompArrowIso qj (E.map k.hom) (E.map g₁))).mpr hk
  exact Scheme.of_pullback_snd_eq (E.map_comp k.hom g₁).symm this

/-- **EGA IV 8.10.5 (xii)** (Stacks 081F) holds: properness of a morphism of finite presentation
over the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes with affine
transition maps descends to a finite stage (`Scheme.ProperLimitStatement`). Properness is local on
the target, so the diagram may be taken affine (`Scheme.limitDescends_of_affine`). -/
@[stacks 081F]
theorem Scheme.properLimitStatement : Scheme.ProperLimitStatement.{u} :=
  Scheme.limitDescends_of_affine Scheme.limitDescendsAffine_isProper

end AlgebraicGeometry
