/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import SGA.Foundations.Etale.Points
import SGA.Foundations.Etale.RepresentableGluing
import SGA.Foundations.StrictLocalizationLimit
import SGA.Foundations.StrictlyHenselianFiniteScheme

/-!
# Stalks of direct images at geometric points

Let `f : X ⟶ Y` be a morphism of schemes, `ȳ : Spec Ω ⟶ Y` a geometric point (`Ω` separably
closed) and `F` an étale sheaf of sets on `X`. The stalk of `f_* F` at `ȳ` is the filtered
colimit of `(f_* F)(V) = F(X ×_Y V)` over the étale neighbourhoods `(V, v)` of `ȳ`. For every
geometric point `x̄` of `X` over `ȳ`, the point `(x̄, v)` of `X ×_Y V` makes `X ×_Y V` an étale
neighbourhood of `x̄`; taking germs there defines the canonical map
`(f_* F)_ȳ ⟶ ∏_{x̄ ↦ ȳ} F_x̄` (`AlgebraicGeometry.Scheme.Hom.etalePushforwardStalkMap`).

For `f` finite and `Ω` algebraically closed this map is bijective
(`AlgebraicGeometry.Scheme.Hom.bijective_etalePushforwardStalkMap`; SGA 4 VIII 5.5,
Stacks 03QP). The geometric input is
`AlgebraicGeometry.Scheme.Hom.exists_etaleNbhd_hom_sigma`: given étale neighbourhoods `U x̄` of
the geometric points `x̄` over `ȳ`, there is an étale neighbourhood `V` of `ȳ` such that
`X ×_Y V` is a disjoint union of pieces, one around each `(x̄, v)`, mapping to `U x̄`. It comes from
the decomposition of `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}` into the spectra of strictly henselian local rings,
one for each `x̄` (`AlgebraicGeometry.exists_hom_sigma_of_isFinite`), and the description of
`Spec 𝒪^{sh}_{Y,ȳ}` as the limit of the affine étale neighbourhoods of `ȳ`
(`AlgebraicGeometry.Scheme.Hom.isLimitAffineEtaleNbhdPullbackCone`). The sheaf property of `F`
for the disjoint unions is `AlgebraicGeometry.Scheme.Hom.existsUnique_section_sigmaPiece`.
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`: elements of fibre functors are only defeq to
-- morphisms over `X` beyond instance transparency.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric point `(x̄, v)` of `X ×_Y V`, for a geometric point `x̄` of `X` over `ȳ` and an
étale neighbourhood `(V, v)` of `ȳ`. -/
def pullbackPoint {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y} (hx : x ≫ f = y) {V : Y.Etale}
    (v : (pointSmallEtale y).fiber.obj V) :
    (pointSmallEtale x).fiber.obj ((Etale.pullback f).obj V) :=
  Over.homMk (pullback.lift v.left x ((Over.w v).trans hx.symm)) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma pullbackPoint_left_fst {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y} (hx : x ≫ f = y)
    {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) :
    (f.pullbackPoint hx v).left ≫ pullback.fst V.hom f = v.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackPoint_left_snd {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y} (hx : x ≫ f = y)
    {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) :
    (f.pullbackPoint hx v).left ≫ pullback.snd V.hom f = x :=
  pullback.lift_snd _ _ _

lemma fiber_map_pullbackPoint {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y} (hx : x ≫ f = y)
    {V W : Y.Etale} (g : V ⟶ W) (v : (pointSmallEtale y).fiber.obj V) :
    (pointSmallEtale x).fiber.map ((Etale.pullback f).map g) (f.pullbackPoint hx v) =
      f.pullbackPoint hx ((pointSmallEtale y).fiber.map g v) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [pointSmallEtale_fiber_map_apply]
  · simp [pointSmallEtale_fiber_map_apply]

variable (F : Sheaf X.smallEtaleTopology (Type u))

/-- The map `(f_* F)_ȳ ⟶ F_x̄` for a geometric point `x̄` of `X` over `ȳ`: the germ at `ȳ` of a
section `s ∈ (f_* F)(V) = F(X ×_Y V)` is sent to the germ of `s` at the point `(x̄, v)`. -/
def etalePushforwardStalkToStalk {x : Spec (.of Ω) ⟶ X} {y : Spec (.of Ω) ⟶ Y}
    (hx : x ≫ f = y) :
    (pointSmallEtale y).presheafFiber.obj ((etalePushforward f).obj F).obj ⟶
      (pointSmallEtale x).presheafFiber.obj F.obj :=
  (pointSmallEtale y).presheafFiberDesc
    (fun V v ↦ (pointSmallEtale x).toPresheafFiber _ (f.pullbackPoint hx v) F.obj)
    (fun V W g v ↦ by
      rw [← fiber_map_pullbackPoint]
      exact (pointSmallEtale x).toPresheafFiber_w ((Etale.pullback f).map g) _ F.obj)

@[simp]
lemma etalePushforwardStalkToStalk_toPresheafFiber {x : Spec (.of Ω) ⟶ X}
    {y : Spec (.of Ω) ⟶ Y} (hx : x ≫ f = y) (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : F.obj.obj (op ((Etale.pullback f).obj V))) :
    f.etalePushforwardStalkToStalk F hx
        ((pointSmallEtale y).toPresheafFiber V v ((etalePushforward f).obj F).obj s) =
      (pointSmallEtale x).toPresheafFiber _ (f.pullbackPoint hx v) F.obj s :=
  by
    unfold etalePushforwardStalkToStalk
    exact ConcreteCategory.congr_hom ((pointSmallEtale y).toPresheafFiber_presheafFiberDesc
      (P := ((etalePushforward f).obj F).obj) _ _ V v) s

/-- SGA 4 VIII 5.5: the canonical map `(f_* F)_ȳ ⟶ ∏_{x̄ ↦ ȳ} F_x̄` from the stalk of the direct
image at a geometric point `ȳ` to the product of the stalks of `F` at the geometric points `x̄`
of `X` over `ȳ`. -/
def etalePushforwardStalkMap (y : Spec (.of Ω) ⟶ Y) :
    (pointSmallEtale y).presheafFiber.obj ((etalePushforward f).obj F).obj →
      ∀ x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}, (pointSmallEtale x.1).presheafFiber.obj F.obj :=
  fun p x ↦ f.etalePushforwardStalkToStalk F x.2 p

lemma etalePushforwardStalkMap_toPresheafFiber (y : Spec (.of Ω) ⟶ Y) (V : Y.Etale)
    (v : (pointSmallEtale y).fiber.obj V) (s : F.obj.obj (op ((Etale.pullback f).obj V)))
    (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    f.etalePushforwardStalkMap F y
        ((pointSmallEtale y).toPresheafFiber V v ((etalePushforward f).obj F).obj s) x =
      (pointSmallEtale x.1).toPresheafFiber _ (f.pullbackPoint x.2 v) F.obj s :=
  f.etalePushforwardStalkToStalk_toPresheafFiber F x.2 V v s

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

section Sigma

/-! ### Sections over a disjoint union -/

variable {X : Scheme.{u}} (Z : X.Etale) {I : Type u} {U : I → Scheme.{u}} (a : Z.left ⟶ ∐ U)

/-- The piece `a⁻¹(U i)` of an étale `X`-scheme `Z` with a morphism `a : Z ⟶ ∐ U`. -/
abbrev sigmaPiece (i : I) : X.Etale :=
  Etale.mk (pullback.fst a (Sigma.ι U i) ≫ Z.hom)

/-- The inclusion of the piece `a⁻¹(U i)` into `Z`. -/
def sigmaPieceι (i : I) : sigmaPiece Z a i ⟶ Z :=
  MorphismProperty.Over.homMk (pullback.fst a (Sigma.ι U i)) rfl

@[simp]
lemma sigmaPieceι_left (i : I) : (sigmaPieceι Z a i).left = pullback.fst a (Sigma.ι U i) := rfl

/-- The sections of an étale sheaf over `Z` are the families of sections over the pieces
`a⁻¹(U i)` of a morphism `a : Z ⟶ ∐ U`: these pieces form a disjoint open cover of `Z`. -/
lemma existsUnique_section_sigmaPiece (F : Sheaf X.smallEtaleTopology (Type u))
    (r : ∀ i, F.obj.obj (op (sigmaPiece Z a i))) :
    ∃! s : F.obj.obj (op Z), ∀ i, F.obj.map (sigmaPieceι Z a i).op s = r i := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hcov : Sieve.ofArrows _ (sigmaPieceι Z a) ∈ X.smallEtaleTopology Z := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun z ↦ ?_
    obtain ⟨i, w, hw⟩ := Scheme.exists_sigmaι_eq (W := U) (a z)
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback z w hw.symm
    exact Set.mem_iUnion.2 ⟨i, t, ht⟩
  have hS := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  refine (Presieve.isSheafFor_arrows_iff _ _).1 hS r fun i j T gi gj h ↦ ?_
  have h' : gi.left ≫ pullback.fst a (Sigma.ι U i) = gj.left ≫ pullback.fst a (Sigma.ι U j) :=
    congrArg (fun k ↦ k.left) h
  by_cases hij : i = j
  · subst hij
    have : gi = gj := MorphismProperty.Over.Hom.ext ((cancel_mono _).1 h')
    rw [this]
  · have : IsEmpty T.left := isEmpty_of_commSq_sigmaι_of_ne
      (a := gi.left ≫ pullback.snd a (Sigma.ι U i)) (b := gj.left ≫ pullback.snd a (Sigma.ι U j))
      ⟨by rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition,
        reassoc_of% h']⟩ hij
    exact (Scheme.subsingleton_obj_of_isEmpty F).elim _ _

end Sigma

section Neighbourhoods

/-! ### Étale neighbourhoods splitting a finite morphism -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

/-- The geometric point `(x̄, s̄)` of `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}`, for a geometric point `x̄` of `X`
over `ȳ`. -/
def strictLocalizationPullbackPoint (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    Spec (.of Ω) ⟶ pullback y.fromSpecStrictLocalization f :=
  pullback.lift y.toSpecStrictLocalization x.1
    (by rw [toSpecStrictLocalization_fromSpecStrictLocalization, x.2])

omit [IsSepClosed Ω] in
@[reassoc (attr := simp)]
lemma strictLocalizationPullbackPoint_fst (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    f.strictLocalizationPullbackPoint y x ≫ pullback.fst _ _ = y.toSpecStrictLocalization :=
  pullback.lift_fst _ _ _

omit [IsSepClosed Ω] in
@[reassoc (attr := simp)]
lemma strictLocalizationPullbackPoint_snd (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    f.strictLocalizationPullbackPoint y x ≫ pullback.snd _ _ = x.1 :=
  pullback.lift_snd _ _ _

lemma strictLocalizationPullbackPoint_π (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
    (k : y.AffineEtaleNbhd) :
    f.strictLocalizationPullbackPoint y x ≫ (y.affineEtaleNbhdPullbackCone f).π.app k =
      (f.pullbackPoint x.2 k.point).left := by
  apply pullback.hom_ext
  · simp [affineEtaleNbhdPullbackCone, pullback.map]
  · simp [affineEtaleNbhdPullbackCone, pullback.map]

set_option backward.isDefEq.respectTransparency false in
/-- **Étale neighbourhoods splitting a finite morphism** (EGA IV 18.8.10, SGA 4 VIII 5.5,
Stacks 03QP): let `f : X ⟶ Y` be finite, `ȳ` a geometric point of `Y` with `Ω` algebraically
closed, `(V₀, v₀)` an étale neighbourhood of `ȳ` and, for each geometric point `x̄` of `X` over
`ȳ`, an étale morphism `q x̄ : U x̄ ⟶ X ×_Y V₀` with a point `u x̄` over `(x̄, v₀)`. There is an
étale neighbourhood `(V, v) ⟶ (V₀, v₀)` and a morphism `a : X ×_Y V ⟶ ∐ U x̄` over `X ×_Y V₀`
sending `(x̄, v)` to `u x̄`: `X ×_Y V` is the disjoint union of the pieces `a⁻¹(U x̄)`, which map
to `U x̄`. The proof splits `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}` into local pieces over which the `U x̄` have
sections (`AlgebraicGeometry.exists_hom_sigma_of_isFinite`) and descends the resulting morphism to
some `X ×_Y V` (`Spec 𝒪^{sh}_{Y,ȳ}` is the limit of the affine étale neighbourhoods). -/
theorem exists_etaleNbhd_hom_sigma [IsFinite f] [IsAlgClosed Ω] (V₀ : Y.Etale)
    (v₀ : (pointSmallEtale y).fiber.obj V₀) {U : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} → Scheme.{u}}
    (q : ∀ x, U x ⟶ pullback V₀.hom f) [∀ x, Etale (q x)] (u : ∀ x, Spec (.of Ω) ⟶ U x)
    (hu : ∀ x, u x ≫ q x = (f.pullbackPoint x.2 v₀).left) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) (g : V ⟶ V₀)
      (_ : (pointSmallEtale y).fiber.map g v = v₀) (a : pullback V.hom f ⟶ ∐ U),
      a ≫ Sigma.desc q = ((Etale.pullback f).map g).left ∧
        ∀ x, (f.pullbackPoint x.2 v).left ≫ a = u x ≫ Sigma.ι U x := by
  classical
  -- an affine neighbourhood `k₀` refining `(V₀, v₀)`
  obtain ⟨k₀, ⟨h₀⟩⟩ := y.exists_affineEtaleNbhdFunctor_hom ⟨V₀, v₀⟩
  let D := y.affineEtaleNbhdPullbackDiagram f
  let c := y.affineEtaleNbhdPullbackCone f
  let hc := y.isLimitAffineEtaleNbhdPullbackCone f
  let β : D.obj k₀ ⟶ pullback V₀.hom f := ((Etale.pullback f).map h₀.1).left
  have hDmap {k k' : y.AffineEtaleNbhd} (g : k ⟶ k') :
      D.map g = ((Etale.pullback f).map (y.affineEtaleNbhdFunctor.map g).1).left := by
    apply pullback.hom_ext <;> simp [D, pullback.map]
    rfl
  -- the neighbourhoods over `k₀`
  let D' := Over.forget k₀ ⋙ D
  let c' := c.whisker (Over.forget k₀)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget k₀) c).symm hc
  let t : D' ⟶ (Functor.const _).obj (pullback V₀.hom f) :=
    { app k := D.map k.hom ≫ β
      naturality k k' g := by
        simp only [D', Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [← Category.assoc, ← D.map_comp, Over.w g] }
  let ρ : c.pt ⟶ pullback V₀.hom f := c.π.app k₀ ≫ β
  -- the morphism over `Spec 𝒪^{sh}_{Y,ȳ}`
  let ι := f.strictLocalizationPullbackPoint y
  have hιfst (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
      ι x ≫ pullback.fst y.fromSpecStrictLocalization f = y.toSpecStrictLocalization :=
    strictLocalizationPullbackPoint_fst f y x
  have hinj : Function.Injective ι := fun x x' h ↦ Subtype.ext (by
    have h' : f.strictLocalizationPullbackPoint y x = f.strictLocalizationPullbackPoint y x' := h
    rw [← strictLocalizationPullbackPoint_snd f y x, ← strictLocalizationPullbackPoint_snd f y x',
      h'])
  have hsurj (z : ↥(pullback y.fromSpecStrictLocalization f : Scheme.{u}))
      (hz : pullback.fst y.fromSpecStrictLocalization f z =
        IsLocalRing.closedPoint y.strictLocalization) :
      ∃ x, ι x (IsLocalRing.closedPoint Ω) = z := by
    obtain ⟨⟨a, ha⟩, haz⟩ :=
      (pullback.fst y.fromSpecStrictLocalization f).exists_pointsOver_apply_eq'
        y.toSpecStrictLocalization z (by rw [hz, toSpecStrictLocalization_apply])
    have hx : (a ≫ pullback.snd _ _) ≫ f = y := by
      rw [Category.assoc, ← pullback.condition, reassoc_of% ha,
        toSpecStrictLocalization_fromSpecStrictLocalization]
    refine ⟨⟨_, hx⟩, ?_⟩
    have : ι ⟨_, hx⟩ = a := by
      apply pullback.hom_ext
      · rw [hιfst, ha]
      · exact strictLocalizationPullbackPoint_snd f y _
    rw [this, haz]
  have hu' (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : u x ≫ q x = ι x ≫ ρ := by
    rw [hu, ← Category.assoc, strictLocalizationPullbackPoint_π]
    have := f.fiber_map_pullbackPoint x.2 h₀.1 k₀.point
    rw [h₀.2] at this
    rw [← this, pointSmallEtale_fiber_map_apply]
    rfl
  obtain ⟨σ, hσ, hσι⟩ := exists_hom_sigma_of_isFinite (pullback.fst y.fromSpecStrictLocalization f)
    y.toSpecStrictLocalization (toSpecStrictLocalization_apply y _) ι hιfst hinj hsurj ρ q u hu'
  -- descent to some neighbourhood
  have : LocallyOfFinitePresentation (Sigma.desc q) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have hD'aff (k : Over k₀) : IsAffine (D'.obj k) := by
    change IsAffine (pullback k.left.nbhd.hom f)
    have : IsAffine ((𝟭 Scheme).obj k.left.nbhd.left) := inferInstanceAs (IsAffine k.left.nbhd.left)
    exact isAffine_of_isAffineHom (pullback.fst k.left.nbhd.hom f)
  have : ∀ {k k' : Over k₀} (g : k ⟶ k'), IsAffineHom (D'.map g) := fun _ ↦ inferInstance
  obtain ⟨k, a, hπa, ha⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t
    (Sigma.desc q) c' hc' σ (by
      ext k
      change c.π.app k.left ≫ D.map k.hom ≫ β = σ ≫ Sigma.desc q
      rw [hσ, ← Category.assoc, c.w k.hom])
  refine ⟨k.left.nbhd, k.left.point, (y.affineEtaleNbhdFunctor.map k.hom).1 ≫ h₀.1, ?_, a, ?_,
    fun x ↦ ?_⟩
  · rw [Functor.map_comp_apply, (y.affineEtaleNbhdFunctor.map k.hom).2, h₀.2]
  · rw [ha]
    change D.map k.hom ≫ β = _
    rw [hDmap, Functor.map_comp]
    rfl
  · rw [← strictLocalizationPullbackPoint_π, Category.assoc]
    change ι x ≫ c'.π.app k ≫ a = _
    rw [hπa, hσι]

end Neighbourhoods

section Bijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (F : Sheaf X.smallEtaleTopology (Type u))

set_option backward.isDefEq.respectTransparency false in
/-- The morphism in `X.Etale` from a piece `a⁻¹(U i)` to an étale neighbourhood `W` over
`X ×_Y V₀`, for `a` over `X ×_Y V₀`. -/
def sigmaPieceHom {V V₀ : Y.Etale} (g : V ⟶ V₀) {I : Type u} {W : I → X.Etale}
    (φ : ∀ i, (W i).left ⟶ pullback V₀.hom f) (hφ : ∀ i, φ i ≫ pullback.snd V₀.hom f = (W i).hom)
    (a : pullback V.hom f ⟶ ∐ fun i ↦ (W i).left)
    (ha : a ≫ Sigma.desc φ = ((Etale.pullback f).map g).left) (i : I) :
    sigmaPiece ((Etale.pullback f).obj V) a i ⟶ W i :=
  MorphismProperty.Over.homMk (pullback.snd a (Sigma.ι _ i)) (by
    change pullback.snd a (Sigma.ι _ i) ≫ (W i).hom =
      pullback.fst a (Sigma.ι _ i) ≫ pullback.snd V.hom f
    let ιi := Sigma.ι (fun i ↦ (W i).left) i
    calc pullback.snd a ιi ≫ (W i).hom
        = (pullback.snd a ιi ≫ ιi) ≫ Sigma.desc φ ≫ pullback.snd V₀.hom f := by
          rw [← hφ, Category.assoc, Sigma.ι_desc_assoc]
      _ = pullback.fst a ιi ≫ (a ≫ Sigma.desc φ) ≫ pullback.snd V₀.hom f := by
          rw [← pullback.condition, Category.assoc, Category.assoc]
      _ = pullback.fst a ιi ≫ pullback.snd V.hom f := by
          rw [ha]
          exact congrArg (pullback.fst a ιi ≫ ·) (Etale.pullback_map_left_snd f g))

@[simp]
lemma sigmaPieceHom_left {V V₀ : Y.Etale} (g : V ⟶ V₀) {I : Type u} {W : I → X.Etale}
    (φ : ∀ i, (W i).left ⟶ pullback V₀.hom f) (hφ : ∀ i, φ i ≫ pullback.snd V₀.hom f = (W i).hom)
    (a : pullback V.hom f ⟶ ∐ fun i ↦ (W i).left)
    (ha : a ≫ Sigma.desc φ = ((Etale.pullback f).map g).left) (i : I) :
    (sigmaPieceHom f g φ hφ a ha i).left = pullback.snd a (Sigma.ι _ i) := rfl

lemma sigmaPieceι_comp {V V₀ : Y.Etale} (g : V ⟶ V₀) {I : Type u} {W : I → X.Etale}
    (φ : ∀ i, W i ⟶ (Etale.pullback f).obj V₀)
    (a : pullback V.hom f ⟶ ∐ fun i ↦ (W i).left)
    (ha : a ≫ Sigma.desc (fun i ↦ (φ i).left) = ((Etale.pullback f).map g).left) (i : I) :
    sigmaPieceι ((Etale.pullback f).obj V) a i ≫ (Etale.pullback f).map g =
      sigmaPieceHom f g (fun i ↦ (φ i).left) (fun i ↦ Over.w ((Etale.forget X).map (φ i))) a ha i ≫
        φ i := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.fst a (Sigma.ι _ i) ≫ ((Etale.pullback f).map g).left =
    pullback.snd a (Sigma.ι _ i) ≫ (φ i).left
  rw [← ha, ← Category.assoc, pullback.condition, Category.assoc, Sigma.ι_desc]

/-- The point of the piece `a⁻¹(U x̄)` over `(x̄, v)`. -/
def sigmaPiecePoint {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) {I : Type u}
    {U : I → Scheme.{u}} (a : pullback V.hom f ⟶ ∐ U) (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
    (i : I) (u : Spec (.of Ω) ⟶ U i) (hu : (f.pullbackPoint x.2 v).left ≫ a = u ≫ Sigma.ι U i) :
    (pointSmallEtale x.1).fiber.obj (sigmaPiece ((Etale.pullback f).obj V) a i) :=
  Over.homMk (pullback.lift (f.pullbackPoint x.2 v).left u hu) (by
    change pullback.lift _ _ hu ≫ pullback.fst a (Sigma.ι U i) ≫ pullback.snd V.hom f = x.1
    rw [pullback.lift_fst_assoc]
    exact pullbackPoint_left_snd f x.2 v)

lemma fiber_map_sigmaPieceι {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) {I : Type u}
    {U : I → Scheme.{u}} (a : pullback V.hom f ⟶ ∐ U) (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
    (i : I) (u : Spec (.of Ω) ⟶ U i) (hu : (f.pullbackPoint x.2 v).left ≫ a = u ≫ Sigma.ι U i) :
    (pointSmallEtale x.1).fiber.map (sigmaPieceι ((Etale.pullback f).obj V) a i)
      (sigmaPiecePoint f y v a x i u hu) =
      f.pullbackPoint x.2 v := by
  apply Over.OverMorphism.ext
  rw [pointSmallEtale_fiber_map_apply]
  exact pullback.lift_fst _ _ _

/-- **SGA 4 VIII 5.5, Stacks 03QP (1)**: for `f : X ⟶ Y` finite, a geometric point
`ȳ : Spec Ω ⟶ Y` with `Ω` algebraically closed and an étale sheaf of sets `F` on `X`, the
canonical map `(f_* F)_ȳ ⟶ ∏_{x̄ ↦ ȳ} F_x̄` is bijective, the product running over the geometric
points `x̄ : Spec Ω ⟶ X` over `ȳ` (i.e. over the points of the geometric fibre `X_ȳ`).

Both injectivity and surjectivity come from the étale neighbourhoods of `ȳ` over which `X`
splits into pieces, one around each `x̄`, refining given neighbourhoods of the `x̄`
(`AlgebraicGeometry.Scheme.Hom.exists_etaleNbhd_hom_sigma`), and the sheaf property of `F` for
disjoint unions (`AlgebraicGeometry.Scheme.Hom.existsUnique_section_sigmaPiece`). -/
theorem bijective_etalePushforwardStalkMap [IsFinite f] :
    Function.Bijective (f.etalePushforwardStalkMap F y) := by
  classical
  let Φ := pointSmallEtale y
  refine ⟨fun b₁ b₂ hb ↦ ?_, fun σ ↦ ?_⟩
  · obtain ⟨V₀, v₀, s, t, rfl, rfl⟩ :=
      Φ.toPresheafFiber_jointly_surjective₂ (P := ((etalePushforward f).obj F).obj) b₁ b₂
    have hst (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
        (pointSmallEtale x.1).toPresheafFiber _ (f.pullbackPoint x.2 v₀) F.obj s =
          (pointSmallEtale x.1).toPresheafFiber _ (f.pullbackPoint x.2 v₀) F.obj t := by
      have := congrFun hb x
      rwa [etalePushforwardStalkMap_toPresheafFiber, etalePushforwardStalkMap_toPresheafFiber]
        at this
    choose W φ w hw hW using fun x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
      ((pointSmallEtale x.1).toPresheafFiber_eq_iff' _ _ s t).1 (hst x)
    obtain ⟨V, v, g, hg, a, ha, hax⟩ := exists_etaleNbhd_hom_sigma f y V₀ v₀
      (U := fun x ↦ (W x).left) (fun x ↦ (φ x).left) (fun x ↦ (w x).left) (fun x ↦ by
        rw [← hw x, pointSmallEtale_fiber_map_apply]
        rfl)
    rw [← hg, ← Φ.toPresheafFiber_w_apply, ← Φ.toPresheafFiber_w_apply]
    congr 1
    change F.obj.map ((Etale.pullback f).map g).op s = F.obj.map ((Etale.pullback f).map g).op t
    refine (existsUnique_section_sigmaPiece ((Etale.pullback f).obj V) a F _).unique
      (fun x ↦ rfl) fun x ↦ ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
      sigmaPieceι_comp f g φ a ha x, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (F.obj.map _) (hW x).symm
  · -- germs of the components
    choose W w r hr using fun x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
      (pointSmallEtale x.1).toPresheafFiber_jointly_surjective (P := F.obj) (σ x)
    -- the trivial neighbourhood `(Y, ȳ)`
    let V₀ : Y.Etale := Etale.mk (𝟙 Y)
    let v₀ : Φ.fiber.obj V₀ := Over.homMk y (by simp [V₀])
    let q (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (W x).left ⟶ pullback V₀.hom f :=
      pullback.lift ((W x).hom ≫ f) (W x).hom (by
        change ((W x).hom ≫ f) ≫ 𝟙 Y = _
        exact Category.comp_id _)
    have hq (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
        q x ≫ pullback.snd V₀.hom f = (W x).hom := pullback.lift_snd _ _ _
    have (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : Etale (q x) := by
      have : IsIso (pullback.snd V₀.hom f) := by
        change IsIso (pullback.snd (𝟙 Y) f)
        infer_instance
      have : q x = (W x).hom ≫ inv (pullback.snd V₀.hom f) := by
        rw [← hq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [this]
      infer_instance
    obtain ⟨V, v, g, -, a, ha, hax⟩ := exists_etaleNbhd_hom_sigma f y V₀ v₀ q (fun x ↦ (w x).left)
      (fun x ↦ by
        apply pullback.hom_ext
        · simp only [q, Category.assoc, pullback.lift_fst, pullbackPoint_left_fst]
          rw [← Category.assoc, show (w x).left ≫ (W x).hom = x.1 from Over.w (w x)]
          exact x.2
        · rw [Category.assoc, hq, pullbackPoint_left_snd]
          exact Over.w (w x))
    let ψ : ∀ x, sigmaPiece ((Etale.pullback f).obj V) a x ⟶ W x :=
      sigmaPieceHom f g (W := W) q hq a ha
    obtain ⟨s, hs, -⟩ := existsUnique_section_sigmaPiece ((Etale.pullback f).obj V) a F
      (fun x ↦ F.obj.map (ψ x).op (r x))
    refine ⟨Φ.toPresheafFiber V v ((etalePushforward f).obj F).obj s, ?_⟩
    ext x
    have hpt : (pointSmallEtale x.1).fiber.map (ψ x)
        (sigmaPiecePoint f y v a x x (w x).left (hax x)) = w x := by
      apply Over.OverMorphism.ext
      rw [pointSmallEtale_fiber_map_apply]
      exact pullback.lift_snd _ _ _
    rw [etalePushforwardStalkMap_toPresheafFiber, ← fiber_map_sigmaPieceι f y v a x x (w x).left
      (hax x), ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hs,
      GrothendieckTopology.Point.toPresheafFiber_w_apply, hpt, hr x]

end Bijective

/-- SGA 4 VIII 5.5, Stacks 03QP (1): for a finite morphism `f : X ⟶ Y`, a geometric
point `ȳ : Spec Ω ⟶ Y` with `Ω` algebraically closed and an étale sheaf of sets `F` on `X`, the
canonical map `(f_* F)_ȳ ⟶ ∏_{x̄ ↦ ȳ} F_x̄` is bijective
(`AlgebraicGeometry.Scheme.Hom.bijective_etalePushforwardStalkMap`). (For `Ω` only separably
closed, the fibre may have points without `Ω`-rational lifts, and the product has to be taken over
the points of `X_ȳ` with their own residue fields.) -/
theorem FinitePushforwardStalkStatement :
    ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [IsFinite f] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y) (F : Sheaf X.smallEtaleTopology (Type u)),
      Function.Bijective (f.etalePushforwardStalkMap F y) :=
  fun _ _ f _ _ _ _ y F ↦ bijective_etalePushforwardStalkMap f y F

end AlgebraicGeometry.Scheme.Hom

end
