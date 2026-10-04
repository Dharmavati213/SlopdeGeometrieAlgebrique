/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalkProperLimit

/-!
# Stalks of direct images and sections over the strict localization

Let `f : X ⟶ S` be a morphism of schemes, `s̄ : Spec Ω ⟶ S` a geometric point (`Ω` separably
closed), `S̃ = Spec 𝒪^{sh}_{S,s̄}` the strict localization and `P = S̃ ×_S X`, with projection
`p : P ⟶ X`. For an étale sheaf of sets `F` on `X` there is a canonical map
`(f_* F)_{s̄} ⟶ Γ(P, p^* F)` (`AlgebraicGeometry.Scheme.Hom.pushforwardStalkToStrictLocalization`):
the germ at `(V, v)` of a section `t ∈ (f_* F)(V) = F(X ×_S V)` goes to the restriction of `t`
along the `X`-morphism `P ⟶ X ×_S V` induced by `S̃ ⟶ V` (`etaleNbhdHom`).

For `f` quasi-compact and quasi-separated this map is bijective (SGA 4 VIII 5.2, Stacks 03Q9 in
degree `0`), a consequence of the limit theorem SGA 4 VII 5.7 since `P` is the limit of the
`X ×_S V`. The statement is `PushforwardStalkStrictLocalizationStatement`. Injectivity is proved
here for every quasi-compact `f`
(`AlgebraicGeometry.Scheme.Hom.injective_pushforwardStalkToStrictLocalization`: the agreement
locus of two sections is open and contains the image of `P`, so it contains the image of some
`X ×_S V`, by `exists_map_eq_top`). Surjectivity, from the degree-`0` surjectivity half of
SGA 4 VII 5.7, and the statement itself are proved in
`SGA.Foundations.Limits.EtaleSectionsGluing`
(`AlgebraicGeometry.Scheme.Hom.surjective_pushforwardStalkToStrictLocalization`,
`AlgebraicGeometry.Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`,
`AlgebraicGeometry.Scheme.pushforwardStalkStrictLocalizationStatement`).

## References

* [SGA 4, Exposé VII, 5.7 and Exposé VIII, 5.2][sga4]
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The `X`-morphism `S̃ ×_S X ⟶ X ×_S V` induced by a point `v` over `s̄` of an étale
`S`-scheme `V`, through `S̃ ⟶ V`. -/
def strictLocalizationPullbackHom (V : S.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    pullback s.fromSpecStrictLocalization f ⟶ ((Etale.pullback f).obj V).left :=
  pullback.lift (pullback.fst _ _ ≫ s.etaleNbhdHom V v) (pullback.snd _ _)
    (by rw [Category.assoc, etaleNbhdHom_comp_hom, pullback.condition])

@[reassoc (attr := simp)]
lemma strictLocalizationPullbackHom_fst (V : S.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    f.strictLocalizationPullbackHom s V v ≫ pullback.fst V.hom f =
      pullback.fst _ _ ≫ s.etaleNbhdHom V v :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma strictLocalizationPullbackHom_snd (V : S.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    f.strictLocalizationPullbackHom s V v ≫ pullback.snd V.hom f =
      pullback.snd s.fromSpecStrictLocalization f :=
  pullback.lift_snd _ _ _

/-- The section `P ⟶ P ×_X (X ×_S V)` of étale `P`-schemes given by
`strictLocalizationPullbackHom`, for `P = S̃ ×_S X`. -/
def strictLocalizationSection (V : S.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    Etale.top (pullback s.fromSpecStrictLocalization f) ⟶
      (Etale.pullback (pullback.snd s.fromSpecStrictLocalization f)).obj
        ((Etale.pullback f).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (f.strictLocalizationPullbackHom s V v) (𝟙 _) (by
      rw [Category.id_comp]
      exact f.strictLocalizationPullbackHom_snd s V v))
    (pullback.lift_snd _ _ _)

lemma strictLocalizationSection_comp {V W : S.Etale} (g : V ⟶ W)
    (v : (pointSmallEtale s).fiber.obj V) :
    f.strictLocalizationSection s V v ≫
        (Etale.pullback (pullback.snd s.fromSpecStrictLocalization f)).map
          ((Etale.pullback f).map g) =
      f.strictLocalizationSection s W ((pointSmallEtale s).fiber.map g v) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [strictLocalizationSection, ← s.etaleNbhdHom_naturality]
    · simp [strictLocalizationSection]
  · simp [strictLocalizationSection]

variable (F : Sheaf X.smallEtaleTopology (Type u))

/-- The canonical map `(f_* F)_{s̄} ⟶ Γ(S̃ ×_S X, p^* F)` from the stalk of the direct image at a
geometric point to the sections of the inverse image of `F` over `X ×_S Spec 𝒪^{sh}_{S,s̄}`: the
germ at `(V, v)` of `t ∈ F(X ×_S V)` goes to its restriction along `S̃ ×_S X ⟶ X ×_S V`. -/
def pushforwardStalkToStrictLocalization :
    (pointSmallEtale s).presheafFiber.obj ((etalePushforward f).obj F).obj ⟶
      ((etalePullback (pullback.snd s.fromSpecStrictLocalization f)).obj F).obj.obj
        (op (Etale.top (pullback s.fromSpecStrictLocalization f))) :=
  (pointSmallEtale s).presheafFiberDesc
    (fun V v ↦ TypeCat.ofHom fun t ↦
      ((etalePullback (pullback.snd s.fromSpecStrictLocalization f)).obj F).obj.map
        (f.strictLocalizationSection s V v).op
        (((etaleAdjunction (pullback.snd s.fromSpecStrictLocalization f)).unit.app F).hom.app
          (op ((Etale.pullback f).obj V)) t))
    (fun V W g v ↦ by
      ext t
      change ((etalePullback _).obj F).obj.map _
          (((etaleAdjunction _).unit.app F).hom.app _ (F.obj.map ((Etale.pullback f).map g).op t)) =
        ((etalePullback _).obj F).obj.map _ _
      erw [NatTrans.naturality_apply ((etaleAdjunction
        (pullback.snd s.fromSpecStrictLocalization f)).unit.app F).hom]
      rw [← f.strictLocalizationSection_comp s g v, op_comp, Functor.map_comp_apply]
      rfl)

lemma pushforwardStalkToStrictLocalization_toPresheafFiber (V : S.Etale)
    (v : (pointSmallEtale s).fiber.obj V) (t : F.obj.obj (op ((Etale.pullback f).obj V))) :
    f.pushforwardStalkToStrictLocalization s F
        ((pointSmallEtale s).toPresheafFiber V v ((etalePushforward f).obj F).obj t) =
      ((etalePullback (pullback.snd s.fromSpecStrictLocalization f)).obj F).obj.map
        (f.strictLocalizationSection s V v).op
        (((etaleAdjunction (pullback.snd s.fromSpecStrictLocalization f)).unit.app F).hom.app
          (op ((Etale.pullback f).obj V)) t) :=
  ConcreteCategory.congr_hom ((pointSmallEtale s).toPresheafFiber_presheafFiberDesc
    (P := ((etalePushforward f).obj F).obj) _ _ V v) t

lemma affineEtaleNbhdPullbackDiagram_map_eq {k k' : s.AffineEtaleNbhd} (g : k ⟶ k') :
    (s.affineEtaleNbhdPullbackDiagram f).map g =
      ((Etale.pullback f).map (s.affineEtaleNbhdFunctor.map g).1).left := by
  apply pullback.hom_ext <;> simp [pullback.map]
  rfl

/-- The projection `X ×_S Spec 𝒪^{sh}_{S,s̄} ⟶ X ×_S V_k` to an affine étale neighbourhood is the
morphism induced by its point. -/
lemma affineEtaleNbhdPullbackCone_π_app_eq (k : s.AffineEtaleNbhd) :
    (s.affineEtaleNbhdPullbackCone f).π.app k =
      f.strictLocalizationPullbackHom s k.nbhd k.point := by
  apply pullback.hom_ext <;> simp [pullback.map]

/-- **Injectivity of `(f_* F)_{s̄} ⟶ Γ(X ×_S Spec 𝒪^{sh}_{S,s̄}, F)`** for `f` quasi-compact
(half of SGA 4 VIII 5.2, Stacks 03Q9 in degree `0`): two sections over `X ×_S V` with the same
restriction to `X ×_S Spec 𝒪^{sh}_{S,s̄}` agree over `X ×_S V'` for a smaller étale neighbourhood
`V'`. The
agreement locus is open and contains the image of `X ×_S Spec 𝒪^{sh}_{S,s̄}`, the limit of the
`X ×_S V`, so it contains the image of some `X ×_S V'` (`exists_map_eq_top`). -/
theorem injective_pushforwardStalkToStrictLocalization [QuasiCompact f] :
    Function.Injective (f.pushforwardStalkToStrictLocalization s F) := by
  intro a b hab
  obtain ⟨V, v, t₁, t₂, rfl, rfl⟩ := (pointSmallEtale s).toPresheafFiber_jointly_surjective₂
    (P := ((etalePushforward f).obj F).obj) a b
  rw [pushforwardStalkToStrictLocalization_toPresheafFiber,
    pushforwardStalkToStrictLocalization_toPresheafFiber] at hab
  have hagr := range_subset_etaleAgreementLocus (F := F) (W := (Etale.pullback f).obj V)
    (s := t₁) (t := t₂) (pullback.snd s.fromSpecStrictLocalization f)
    (f.strictLocalizationSection s V v) hab
  have hσ : (f.strictLocalizationSection s V v).left ≫
      pullback.fst ((Etale.pullback f).obj V).hom (pullback.snd s.fromSpecStrictLocalization f) =
        f.strictLocalizationPullbackHom s V v :=
    pullback.lift_fst _ _ _
  rw [hσ] at hagr
  -- an affine neighbourhood `k₀` refining `(V, v)`
  obtain ⟨k₀, ⟨h₀⟩⟩ := s.exists_affineEtaleNbhdFunctor_hom ⟨V, v⟩
  have h₀v : (pointSmallEtale s).fiber.map h₀.1 k₀.point = v := h₀.2
  let D := s.affineEtaleNbhdPullbackDiagram f
  let U : (D.obj k₀).Opens := ((Etale.pullback f).map h₀.1).left ⁻¹ᵁ
    ⟨etaleAgreementLocus F t₁ t₂, isOpen_etaleAgreementLocus (F := F) t₁ t₂⟩
  have hπ : (s.affineEtaleNbhdPullbackCone f).π.app k₀ ≫ ((Etale.pullback f).map h₀.1).left =
      f.strictLocalizationPullbackHom s V v := by
    rw [affineEtaleNbhdPullbackCone_π_app_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, Etale.pullback_map_left_fst, strictLocalizationPullbackHom_fst_assoc,
        strictLocalizationPullbackHom_fst, s.etaleNbhdHom_naturality, h₀v]
    · rw [Category.assoc, Etale.pullback_map_left_snd, strictLocalizationPullbackHom_snd,
        strictLocalizationPullbackHom_snd]
  have hU : (s.affineEtaleNbhdPullbackCone f).π.app k₀ ⁻¹ᵁ U = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hπ, eq_top_iff]
    rintro x -
    exact hagr ⟨x, rfl⟩
  obtain ⟨j, fj, hj⟩ := exists_map_eq_top D _ (s.isLimitAffineEtaleNbhdPullbackCone f) U hU
  let g := (s.affineEtaleNbhdFunctor.map fj).1 ≫ h₀.1
  have hg : (pointSmallEtale s).fiber.map g j.point = v := by
    simp only [g, Functor.map_comp, types_comp_apply]
    rw [(s.affineEtaleNbhdFunctor.map fj).2]
    exact h₀v
  refine ((pointSmallEtale s).toPresheafFiber_eq_iff' _ _ _ _).2 ⟨j.nbhd, g, j.point, hg, ?_⟩
  refine map_eq_of_range_subset_etaleAgreementLocus ((Etale.pullback f).map g) ?_
  have e : D.map fj ≫ ((Etale.pullback f).map h₀.1).left = ((Etale.pullback f).map g).left := by
    rw [f.affineEtaleNbhdPullbackDiagram_map_eq s fj, ← MorphismProperty.Comma.comp_left,
      ← Functor.map_comp]
  have hj' : ((Etale.pullback f).map g).left ⁻¹ᵁ
      ⟨etaleAgreementLocus F t₁ t₂, isOpen_etaleAgreementLocus (F := F) t₁ t₂⟩ = ⊤ := by
    rw [← e, Scheme.Hom.comp_preimage]
    exact hj
  rintro _ ⟨z, rfl⟩
  exact hj'.ge (Set.mem_univ z)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- SGA 4 VIII 5.2, Stacks 03Q9 in degree `0`: for `f : X ⟶ S` quasi-compact and
quasi-separated, a geometric point `s̄` of `S` and an étale sheaf of sets `F` on `X`, the canonical
map `(f_* F)_{s̄} ⟶ Γ(X ×_S Spec 𝒪^{sh}_{S,s̄}, F)` is bijective. It follows from the limit
theorem SGA 4 VII 5.7 in degree `0` (sections of étale sheaves over a cofiltered limit of
quasi-compact and quasi-separated schemes with affine transition morphisms,
`AlgebraicGeometry.Scheme.exists_toLimitSections_eq`), and is proved as
`AlgebraicGeometry.Scheme.pushforwardStalkStrictLocalizationStatement` in
`SGA.Foundations.Limits.EtaleSectionsGluing`. -/
def PushforwardStalkStrictLocalizationStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] ⦃Ω : Type u⦄ [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (Type u)),
    Function.Bijective (f.pushforwardStalkToStrictLocalization s F)

end AlgebraicGeometry.Scheme
