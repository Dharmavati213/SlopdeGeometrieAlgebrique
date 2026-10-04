/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.EtaleSections
import SGA.Foundations.Limits.FiniteEtale

/-!
# Sections of étale sheaves over a cofiltered limit

Let `c.pt = lim E` be the limit of a cofiltered diagram `E` of quasi-compact and quasi-separated
schemes with affine transition maps, each `E k` étale over a scheme `X` compatibly with the
transition maps (`t : E ⟶ X`), and let `p : c.pt ⟶ X` be the induced morphism. For an étale sheaf
of sets `F` on `X`, every section of `p^* F` over `c.pt` comes from a section of `F` over some
`E k` (`AlgebraicGeometry.Scheme.exists_toLimitSections_eq`). This is the surjectivity half of
SGA 4 VII 5.7 in degree `0`, in the special case of the inverse images of one sheaf on `X`.

The proof glues local data:
* near every point, a section of `p^* F` is the image of a section `a ∈ F(W)` on an open
  `O ⊆ c.pt ×_X W` (germs at geometric points and agreement loci,
  `exists_mem_etaleAgreementLocus_etaleAdjunction_unit`); a quasi-compact `O` comes from a
  quasi-compact open of some `E k ×_X W` (mathlib's `exists_preimage_eq`, Stacks 01Z4), whence a
  *local model* `(Q ⟶ E k, b ∈ F(Q))` agreeing with the section (`LimitSections.AgreesWith`,
  `LimitSections.exists_agreesWith`);
* finitely many local models cover `c.pt`, so after passing to a lower level they cover some `E k`
  (mathlib's `exists_map_eq_top`);
* two local models agree on `c.pt ×_{E k} (Q ×_{E k} Q')`, so the closed complement of their
  agreement locus does not meet the image of the limit and becomes empty at a lower level
  (`exists_forall_pullback_fst_notMem`, from mathlib's `exists_mem_of_isClosed_of_nonempty`,
  Stacks 01Z3; `LimitSections.exists_forall_mem_etaleAgreementLocus`);
* the local models then glue by the sheaf property, and the glued section restricts to the given
  one since both agree on a covering of `c.pt`.

Applied to `X ×_S Spec 𝒪^{sh}_{S,s̄} = lim (X ×_S V)` over the affine étale neighbourhoods `V`
of a geometric point `s̄`, this gives the surjectivity of
`(f_* F)_{s̄} ⟶ Γ(X ×_S Spec 𝒪^{sh}_{S,s̄}, F)` for `f` quasi-compact and quasi-separated
(`AlgebraicGeometry.Scheme.Hom.surjective_pushforwardStalkToStrictLocalization`). With the
injectivity (`AlgebraicGeometry.Scheme.Hom.injective_pushforwardStalkToStrictLocalization`) this
proves SGA 4 VIII 5.2 in degree `0`
(`AlgebraicGeometry.Scheme.pushforwardStalkStrictLocalizationStatement`).

## References

* [SGA 4, Exposé VII, 5.7 and Exposé VIII, 5.2][sga4]
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ) (stated there for abelian
  sheaves in all degrees; the sheaves of sets analogue in degree `0`)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9) (degree `0`)
* [Stacks Project, Tag 01Z3](https://stacks.math.columbia.edu/tag/01Z3)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

section ClosedDescent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}} {c : Cone E}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]

/-- Let `c.pt = lim E` be a cofiltered limit of quasi-compact schemes with affine transition
maps, `q : T ⟶ E j` quasi-compact and `Z ⊆ T` closed. If no point of `T ×_{E j} c.pt` lies over
`Z`, then no point of `T ×_{E j} E k` lies over `Z`, for some `k ⟶ j` (Stacks 01Z3). -/
lemma exists_forall_pullback_fst_notMem (hc : IsLimit c) {j : I} {T : Scheme.{u}}
    (q : T ⟶ E.obj j) [QuasiCompact q] {Z : Set T} (hZ : IsClosed Z)
    (h : ∀ x, pullback.fst q (c.π.app j) x ∉ Z) :
    ∃ (k : I) (g : k ⟶ j), ∀ x, pullback.fst q (E.map g) x ∉ Z := by
  by_contra! H
  have hpb := IsPullback.of_hasPullback q (c.π.app j)
  have (k : Over j) : CompactSpace ((baseChangeDiagram E q).obj k) :=
    compactSpace_baseChangeDiagram q k
  obtain ⟨x, hx⟩ := exists_mem_of_isClosed_of_nonempty (baseChangeDiagram E q)
    (baseChangeCone hpb) (isLimitBaseChangeCone hc hpb)
    (fun k ↦ pullback.fst q (E.map k.hom) ⁻¹' Z)
    (fun k ↦ hZ.preimage (pullback.fst q (E.map k.hom)).continuous)
    (fun k ↦ by
      obtain ⟨x, hx⟩ := H k.left k.hom
      exact ⟨x, hx⟩)
    (fun k ↦ (hZ.preimage (pullback.fst q (E.map k.hom)).continuous).isCompact)
    (fun {k k'} g x hx ↦ by
      have e : (baseChangeDiagram E q).map g ≫ pullback.fst q (E.map k'.hom) =
          pullback.fst q (E.map k.hom) := by
        simp [pullback.map]
      have e' := congrArg (fun φ ↦ φ x) e
      simp only [Scheme.Hom.comp_apply] at e'
      exact (congrArg (· ∈ Z) e').mpr hx)
  apply h x
  have e : (baseChangeCone hpb).π.app (Over.mk (𝟙 j)) ≫ pullback.fst q (E.map (𝟙 j)) =
      pullback.fst q (c.π.app j) :=
    pullback.lift_fst _ _ _
  have := hx (Over.mk (𝟙 j))
  rw [← e, Scheme.Hom.comp_apply]
  exact this

end ClosedDescent

section PullbackDiagram

variable {I : Type u} [Category.{u} I] {X : Scheme.{u}} {E : I ⥤ Scheme.{u}}
  (t : E ⟶ (Functor.const I).obj X) {c : Cone E} {p : c.pt ⟶ X}
  (hp : ∀ k, c.π.app k ≫ t.app k = p) (W : Scheme.{u}) (w : W ⟶ X)

namespace LimitSections

/-- The cocone condition for `t : E ⟶ X` (`(Cocone.mk X t).w g`). -/
private lemma natTrans_app_comp_eq (t : E ⟶ (Functor.const I).obj X) {k k' : I} (g : k ⟶ k') :
    E.map g ≫ t.app k' = t.app k :=
  (Cocone.mk X t).w g

/-- The diagram `k ↦ W ×_X E k`, for `t : E ⟶ X` and `w : W ⟶ X`. -/
@[simps]
def pullbackDiagram : I ⥤ Scheme.{u} where
  obj k := pullback w (t.app k)
  map {k k'} g := pullback.map w (t.app k) w (t.app k') (𝟙 W) (E.map g) (𝟙 X) (by simp)
    (by rw [Category.comp_id, natTrans_app_comp_eq])
  map_id k := by
    apply pullback.hom_ext <;> simp
  map_comp g g' := by
    apply pullback.hom_ext <;> simp

lemma isPullback_pullbackDiagram_map {k k' : I} (g : k ⟶ k') :
    IsPullback ((pullbackDiagram t W w).map g) (pullback.snd w (t.app k))
      (pullback.snd w (t.app k')) (E.map g) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have h₁ : (pullbackDiagram t W w).map g ≫ pullback.fst w (t.app k') = pullback.fst w (t.app k) :=
    by simp
  rw [h₁, natTrans_app_comp_eq]
  exact IsPullback.of_hasPullback _ _

instance [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] {k k' : I} (g : k ⟶ k') :
    IsAffineHom ((pullbackDiagram t W w).map g) :=
  MorphismProperty.of_isPullback (isPullback_pullbackDiagram_map t W w g).flip inferInstance

/-- The cone over `k ↦ W ×_X E k` with vertex `W ×_X c.pt`. -/
@[simps]
def pullbackDiagramCone : Cone (pullbackDiagram t W w) where
  pt := pullback w p
  π :=
    { app k := pullback.map w p w (t.app k) (𝟙 W) (c.π.app k) (𝟙 X) (by simp)
        (by rw [Category.comp_id, hp])
      naturality k k' g := by
        apply pullback.hom_ext
        · simp
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            pullbackDiagram_map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [c.w g] }

lemma isPullback_pullbackDiagramCone (k : I) :
    IsPullback ((pullbackDiagramCone t hp W w).π.app k) (pullback.snd w p)
      (pullback.snd w (t.app k)) (c.π.app k) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback w (t.app k))
  have h₁ : (pullbackDiagramCone t hp W w).π.app k ≫ pullback.fst w (t.app k) =
      pullback.fst w p := by simp
  rw [h₁, hp]
  exact IsPullback.of_hasPullback _ _

attribute [local instance] IsCofiltered.isConnected in
/-- The limit of `k ↦ W ×_X E k` is `W ×_X c.pt`. -/
def isLimitPullbackDiagramCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (pullbackDiagramCone t hp W w) :=
  isLimitOfIsPullbackOfIsConnected
    ({ app k := pullback.snd w (t.app k)
       naturality k k' g := by simp } : pullbackDiagram t W w ⟶ E)
    (pullbackDiagramCone t hp W w) c
    { hom := pullback.snd w p
      w k := by simp }
    (isPullback_pullbackDiagramCone t hp W w) hc

end LimitSections

end PullbackDiagram

section Local

variable {X P : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u)) (p : P ⟶ X)

/-- Sections of an inverse image are étale-locally images of sections: for `p : P ⟶ X`, a
section `σ` of `p^* F` over `P` and a point `z` of `P`, there are an étale `X`-scheme `W`, a
section `a ∈ F(W)` and a point of `P ×_X W` over `z` in the agreement locus of `σ` and the
image of `a`. -/
lemma exists_mem_etaleAgreementLocus_etaleAdjunction_unit
    (σ : ((etalePullback p).obj F).obj.obj (op (Etale.top P))) (z : P) :
    ∃ (W : X.Etale) (a : F.obj.obj (op W)) (w : ((Etale.pullback p).obj W).left),
      ((Etale.pullback p).obj W).hom w = z ∧
      w ∈ etaleAgreementLocus ((etalePullback p).obj F)
        (((etalePullback p).obj F).obj.map
          ((Etale.isTerminalTop P).from ((Etale.pullback p).obj W)).op σ)
        (((etaleAdjunction p).unit.app F).hom.app (op W) a) := by
  let G := (etalePullback p).obj F
  let x := P.fromSpecAlgClosure z
  let top' : (pointSmallEtale x).fiber.obj (Etale.top P) :=
    Over.homMk x (Category.comp_id _)
  let e := (sheafFiberEtalePullbackIso p x).app F
  have he : Function.Bijective e.hom := (isIso_iff_bijective _).1 inferInstance
  obtain ⟨δ, hδ⟩ := he.2 ((pointSmallEtale x).toPresheafFiber (Etale.top P) top' G.obj σ)
  obtain ⟨W, v, a, rfl⟩ := (pointSmallEtale (x ≫ p)).toPresheafFiber_jointly_surjective
    (P := F.obj) δ
  let w₁ := (pointSmallEtaleFiberHom p x).app W v
  have hgerm : (pointSmallEtale x).toPresheafFiber (Etale.top P) top' G.obj σ =
      (pointSmallEtale x).toPresheafFiber ((Etale.pullback p).obj W) w₁ G.obj
        (((etaleAdjunction p).unit.app F).hom.app (op W) a) := by
    rw [← hδ]
    exact sheafFiberEtalePullbackIso_hom_app_toPresheafFiber p x F W v a
  have hres : (pointSmallEtale x).toPresheafFiber ((Etale.pullback p).obj W) w₁ G.obj
      (G.obj.map ((Etale.isTerminalTop P).from ((Etale.pullback p).obj W)).op σ) =
      (pointSmallEtale x).toPresheafFiber (Etale.top P) top' G.obj σ := by
    have hw : (pointSmallEtale x).fiber.map ((Etale.isTerminalTop P).from
        ((Etale.pullback p).obj W)) w₁ = top' := by
      apply Over.OverMorphism.ext
      rw [pointSmallEtale_fiber_map_apply]
      exact Over.w w₁
    rw [GrothendieckTopology.Point.toPresheafFiber_w_apply, hw]
  have hmem := apply_mem_etaleAgreementLocus w₁ (hres.trans hgerm)
    (IsLocalRing.closedPoint (AlgebraicClosure (P.residueField z)))
  refine ⟨W, a, _, ?_, hmem⟩
  have e₁ := congrArg (fun φ ↦ φ (IsLocalRing.closedPoint (AlgebraicClosure (P.residueField z))))
    (Over.w w₁)
  simp only [Scheme.Hom.comp_apply] at e₁
  exact e₁.trans (Scheme.fromSpecAlgClosure_apply _ _)

end Local

section Gluing

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))
  {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} (t : E ⟶ (Functor.const I).obj X)
  [∀ k, Etale (t.app k)] {c : Cone E} {p : c.pt ⟶ X} (hp : ∀ k, c.π.app k ≫ t.app k = p)

namespace LimitSections

/-- The section `c.pt ⟶ c.pt ×_X E k` of étale `c.pt`-schemes given by the projection. -/
def limitSection (k : I) : Etale.top c.pt ⟶ (Etale.pullback p).obj (Etale.mk (t.app k)) :=
  MorphismProperty.Over.homMk (pullback.lift (c.π.app k) (𝟙 _) (by
      rw [Category.id_comp]
      exact hp k))
    (pullback.lift_snd _ _ _) trivial

end LimitSections

open LimitSections in
/-- The map `F(E k) ⟶ Γ(c.pt, p^* F)` restricting a section of `F` over the étale `X`-scheme
`E k` to the limit `c.pt`. -/
def toLimitSections (k : I) (s : F.obj.obj (op (Etale.mk (t.app k)))) :
    ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt)) :=
  ((etalePullback p).obj F).obj.map (limitSection t hp k).op
    (((etaleAdjunction p).unit.app F).hom.app (op (Etale.mk (t.app k))) s)

namespace LimitSections

variable {t}

/-- For a morphism `φ : Q ⟶ E k` of étale `X`-schemes, the étale `c.pt`-scheme
`c.pt ×_{E k} Q`. -/
abbrev limitPullback {k : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) : c.pt.Etale :=
  Etale.mk (pullback.fst (c.π.app k) φ.left)

/-- The morphism `c.pt ×_{E k} Q ⟶ c.pt ×_X Q` of étale `c.pt`-schemes. -/
def limitPullbackHom {k : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) :
    limitPullback (c := c) φ ⟶ (Etale.pullback p).obj Q :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.snd (c.π.app k) φ.left) (pullback.fst (c.π.app k) φ.left) (by
      rw [← MorphismProperty.Over.w φ, ← pullback.condition_assoc]
      change pullback.fst (c.π.app k) φ.left ≫ c.π.app k ≫ t.app k = _
      rw [hp]))
    (pullback.lift_snd _ _ _) trivial

@[reassoc (attr := simp)]
lemma limitPullbackHom_left_fst {k : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) :
    (limitPullbackHom hp φ).left ≫ pullback.fst Q.hom p = pullback.snd (c.π.app k) φ.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma limitPullbackHom_left_snd {k : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) :
    (limitPullbackHom hp φ).left ≫ pullback.snd Q.hom p = pullback.fst (c.π.app k) φ.left :=
  pullback.lift_snd _ _ _

/-- A section `b` of `F` over `Q`, with `φ : Q ⟶ E k`, *agrees with* `σ ∈ Γ(c.pt, p^* F)` if the
images of `b` and `σ` in `(p^* F)(c.pt ×_{E k} Q)` are equal. -/
def AgreesWith (σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))) {k : I}
    {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (b : F.obj.obj (op Q)) : Prop :=
  ((etalePullback p).obj F).obj.map (limitPullbackHom hp φ).op
      (((etaleAdjunction p).unit.app F).hom.app (op Q) b) =
    ((etalePullback p).obj F).obj.map ((Etale.isTerminalTop c.pt).from _).op σ

variable {F hp}

lemma AgreesWith.comp {σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))} {k m : I}
    {Q Q' : X.Etale} {φ : Q ⟶ Etale.mk (t.app k)} {b : F.obj.obj (op Q)}
    (h : AgreesWith F hp σ φ b) (ψ : Q' ⟶ Q) (φ' : Q' ⟶ Etale.mk (t.app m)) (g : m ⟶ k)
    (w : ψ.left ≫ φ.left = φ'.left ≫ E.map g) :
    AgreesWith F hp σ φ' (F.obj.map ψ.op b) := by
  let G := (etalePullback p).obj F
  let η := (etaleAdjunction p).unit.app F
  let ρ : limitPullback (c := c) φ' ⟶ limitPullback (c := c) φ := MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ψ.left) (by
      rw [Category.assoc, w, ← c.w g, pullback.condition_assoc]))
    (pullback.lift_fst _ _ _) trivial
  have hρ : limitPullbackHom hp φ' ≫ (Etale.pullback p).map ψ = ρ ≫ limitPullbackHom hp φ := by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    apply pullback.hom_ext
    · simp [ρ]
    · simp [ρ]
  have nat : η.hom.app (op Q') (F.obj.map ψ.op b) =
      G.obj.map ((Etale.pullback p).map ψ).op (η.hom.app (op Q) b) :=
    NatTrans.naturality_apply η.hom ψ.op b
  unfold AgreesWith at h ⊢
  rw [nat, ← Functor.map_comp_apply, ← op_comp, hρ, op_comp, Functor.map_comp_apply, h,
    ← Functor.map_comp_apply, ← op_comp,
    (Etale.isTerminalTop c.pt).hom_ext (ρ ≫ (Etale.isTerminalTop c.pt).from _)
      ((Etale.isTerminalTop c.pt).from _)]

section Restrict

variable (t) in
/-- The restriction `Q ×_{E k} E m` of `φ : Q ⟶ E k` to a lower level `g : m ⟶ k`, an étale
`X`-scheme. -/
abbrev restrictObj {k m : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (g : m ⟶ k) :
    X.Etale :=
  Etale.mk (pullback.snd φ.left (E.map g) ≫ t.app m)

/-- The projection `Q ×_{E k} E m ⟶ E m`. -/
def restrictHom {k m : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (g : m ⟶ k) :
    restrictObj t φ g ⟶ Etale.mk (t.app m) :=
  MorphismProperty.Over.homMk (pullback.snd φ.left (E.map g)) rfl trivial

/-- The projection `Q ×_{E k} E m ⟶ Q`. -/
def restrictFst {k m : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (g : m ⟶ k) :
    restrictObj t φ g ⟶ Q :=
  MorphismProperty.Over.homMk (pullback.fst φ.left (E.map g)) (by
    rw [← MorphismProperty.Over.w φ, pullback.condition_assoc]
    change pullback.snd φ.left (E.map g) ≫ E.map g ≫ t.app k = _
    rw [natTrans_app_comp_eq]
    rfl) trivial

@[simp]
lemma restrictHom_left {k m : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (g : m ⟶ k) :
    (restrictHom φ g).left = pullback.snd φ.left (E.map g) := rfl

@[simp]
lemma restrictFst_left {k m : I} {Q : X.Etale} (φ : Q ⟶ Etale.mk (t.app k)) (g : m ⟶ k) :
    (restrictFst φ g).left = pullback.fst φ.left (E.map g) := rfl

lemma AgreesWith.restrict {σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))}
    {k m : I} {Q : X.Etale} {φ : Q ⟶ Etale.mk (t.app k)} {b : F.obj.obj (op Q)}
    (h : AgreesWith F hp σ φ b) (g : m ⟶ k) :
    AgreesWith F hp σ (restrictHom φ g) (F.obj.map (restrictFst φ g).op b) :=
  h.comp (restrictFst φ g) (restrictHom φ g) g pullback.condition

lemma mem_range_restrict {k m : I} {Q : X.Etale} {φ : Q ⟶ Etale.mk (t.app k)} (g : m ⟶ k)
    {z : c.pt} (hz : z ∈ Set.range (pullback.fst (c.π.app k) φ.left)) :
    z ∈ Set.range (pullback.fst (c.π.app m) (restrictHom φ g).left) := by
  obtain ⟨x, rfl⟩ := hz
  have e₁ := congrArg (fun f ↦ f (pullback.fst (c.π.app k) φ.left x)) (c.w g)
  have e₂ := congrArg (fun f ↦ f x) (pullback.condition (f := c.π.app k) (g := φ.left))
  simp only [Scheme.Hom.comp_apply] at e₁ e₂
  obtain ⟨q, hq₁, hq₂⟩ := Pullback.exists_preimage_pullback (f := φ.left) (g := E.map g)
    (pullback.snd (c.π.app k) φ.left x) (c.π.app m (pullback.fst (c.π.app k) φ.left x))
    (e₂.symm.trans e₁.symm)
  obtain ⟨y, hy₁, -⟩ := Pullback.exists_preimage_pullback (f := c.π.app m)
    (g := (restrictHom φ g).left) (pullback.fst (c.π.app k) φ.left x) q hq₂.symm
  exact ⟨y, hy₁⟩

end Restrict

variable (F hp) in
/-- Every point of the limit has a neighbourhood on which `σ ∈ Γ(c.pt, p^* F)` comes from a
section of `F` over a quasi-compact étale `X`-scheme over some `E k`. -/
theorem exists_agreesWith [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    (hc : IsLimit c) (σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))) (z : c.pt) :
    ∃ (k : I) (Q : X.Etale) (φ : Q ⟶ Etale.mk (t.app k)) (b : F.obj.obj (op Q)),
      CompactSpace Q.left ∧ AgreesWith F hp σ φ b ∧
        z ∈ Set.range (pullback.fst (c.π.app k) φ.left) := by
  let G := (etalePullback p).obj F
  let η := (etaleAdjunction p).unit.app F
  obtain ⟨W, a, w, hwz, hw⟩ := exists_mem_etaleAgreementLocus_etaleAdjunction_unit F p σ z
  obtain ⟨_, ⟨O, hO, rfl⟩, hwO, hOA⟩ :=
    (((Etale.pullback p).obj W).left.isBasis_affineOpens).exists_subset_of_mem_open hw
      (isOpen_etaleAgreementLocus _ _)
  let D := pullbackDiagram t W.left W.hom
  let cD := pullbackDiagramCone t hp W.left W.hom
  obtain ⟨l, O', hO'c, hO'⟩ := exists_preimage_eq D cD
    (isLimitPullbackDiagramCone t hp W.left W.hom hc) O hO.isCompact
  let Q : X.Etale := Etale.mk (O'.ι ≫ pullback.snd W.hom (t.app l) ≫ t.app l)
  let φ : Q ⟶ Etale.mk (t.app l) :=
    MorphismProperty.Over.homMk (O'.ι ≫ pullback.snd W.hom (t.app l)) (Category.assoc _ _ _)
      trivial
  let ψ : Q ⟶ W := MorphismProperty.Over.homMk (O'.ι ≫ pullback.fst W.hom (t.app l)) (by
      rw [Category.assoc, pullback.condition]
      rfl) trivial
  have hπ : cD.π.app l ≫ pullback.snd W.hom (t.app l) = pullback.snd W.hom p ≫ c.π.app l := by
    simp [cD]
  refine ⟨l, Q, φ, F.obj.map ψ.op a, isCompact_iff_compactSpace.mp hO'c, ?_, ?_⟩
  · -- the image of `Q` in `W ×_X c.pt` lies in `O`
    have key : (limitPullbackHom hp φ ≫ (Etale.pullback p).map ψ).left ≫ cD.π.app l =
        pullback.snd (c.π.app l) φ.left ≫ O'.ι := by
      rw [MorphismProperty.Comma.comp_left]
      apply pullback.hom_ext
      · simp [cD, ψ]
      · simp only [Category.assoc, hπ, Etale.pullback_map_left_snd_assoc,
          limitPullbackHom_left_snd_assoc]
        rw [pullback.condition]
        rfl
    have hrange : Set.range (limitPullbackHom hp φ ≫ (Etale.pullback p).map ψ).left ⊆
        etaleAgreementLocus G
          (G.obj.map ((Etale.isTerminalTop c.pt).from ((Etale.pullback p).obj W)).op σ)
          (η.hom.app (op W) a) := by
      rintro _ ⟨x, rfl⟩
      apply hOA
      have h₁ := congrArg (fun f ↦ f x) key
      simp only [Scheme.Hom.comp_apply] at h₁
      have h₂ : cD.π.app l ((limitPullbackHom hp φ ≫ (Etale.pullback p).map ψ).left x) ∈ O' :=
        (congrArg (· ∈ O') h₁).mpr ((Scheme.Opens.range_ι O').le ⟨_, rfl⟩)
      rw [← hO']
      exact h₂
    have H := map_eq_of_range_subset_etaleAgreementLocus _ hrange
    have nat : η.hom.app (op Q) (F.obj.map ψ.op a) =
        G.obj.map ((Etale.pullback p).map ψ).op (η.hom.app (op W) a) :=
      NatTrans.naturality_apply η.hom ψ.op a
    unfold AgreesWith
    change G.obj.map (limitPullbackHom hp φ).op (η.hom.app (op Q) (F.obj.map ψ.op a)) = _
    rw [nat, ← Functor.map_comp_apply, ← op_comp, ← H, ← Functor.map_comp_apply, ← op_comp,
      (Etale.isTerminalTop c.pt).hom_ext (_ ≫ (Etale.isTerminalTop c.pt).from _)
        ((Etale.isTerminalTop c.pt).from _)]
  · -- `z` lies under `Q`
    have hw' : cD.π.app l w ∈ O' := by
      rw [← hO'] at hwO
      exact hwO
    obtain ⟨q, hq⟩ := (Scheme.Opens.range_ι O').ge hw'
    have e₁ := congrArg (fun f ↦ f w) hπ
    simp only [Scheme.Hom.comp_apply] at e₁
    have e₂ : φ.left q = c.π.app l z := by
      change pullback.snd W.hom (t.app l) (O'.ι q) = _
      rw [hq]
      exact e₁.trans (congrArg (fun y ↦ c.π.app l y) hwz)
    obtain ⟨y, hy, -⟩ := Pullback.exists_preimage_pullback (f := c.π.app l) (g := φ.left) z q
      e₂.symm
    exact ⟨y, hy⟩

/-- Two sections of `F` over a quasi-compact `T ⟶ E k` which both agree with `σ` agree on
`T ×_{E k} E m` for some `m ⟶ k`: the closed complement of their agreement locus does not meet
the image of `T ×_{E k} c.pt`. -/
theorem exists_forall_mem_etaleAgreementLocus [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ k, CompactSpace (E.obj k)]
    [∀ k, QuasiSeparatedSpace (E.obj k)] (hc : IsLimit c)
    {σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))} {k : I} {T : X.Etale}
    [CompactSpace T.left] {φ : T ⟶ Etale.mk (t.app k)} {b b' : F.obj.obj (op T)}
    (hb : AgreesWith F hp σ φ b) (hb' : AgreesWith F hp σ φ b') :
    ∃ (m : I) (g : m ⟶ k), ∀ x, pullback.fst φ.left (E.map g) x ∈ etaleAgreementLocus F b b' := by
  have : QuasiSeparatedSpace (Etale.mk (t.app k)).left := inferInstanceAs
    (QuasiSeparatedSpace (E.obj k))
  have : QuasiCompact φ.left := quasiCompact_of_compactSpace _
  have hk := hb.trans hb'.symm
  have hr := range_subset_etaleAgreementLocus p (limitPullbackHom hp φ) hk
  have H (x) : pullback.fst φ.left (c.π.app k) x ∈ etaleAgreementLocus F b b' := by
    have e := congrArg (fun f ↦ f x) (pullback.condition (f := φ.left) (g := c.π.app k))
    simp only [Scheme.Hom.comp_apply] at e
    obtain ⟨y, -, hy⟩ := Pullback.exists_preimage_pullback (f := c.π.app k) (g := φ.left)
      (pullback.snd φ.left (c.π.app k) x) (pullback.fst φ.left (c.π.app k) x) e.symm
    refine hr ⟨y, ?_⟩
    rw [limitPullbackHom_left_fst]
    exact hy
  obtain ⟨m, g, hg⟩ := exists_forall_pullback_fst_notMem hc φ.left
    (isOpen_etaleAgreementLocus b b').isClosed_compl (fun x hx ↦ hx (H x))
  exact ⟨m, g, fun x ↦ not_not.mp (hg x)⟩

end LimitSections

open LimitSections

variable {t}

/-- **Sections over a cofiltered limit, surjectivity** (SGA 4 VII 5.7 in degree `0`, the gluing
half; the sheaves of sets analogue of Stacks 09YQ in degree `0`): let `c.pt = lim E` be the limit
of a cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps,
each `E k` étale over `X` compatibly with the transition maps, and `p : c.pt ⟶ X` the induced
map. Every section of `p^* F` over `c.pt` comes from a section of `F` over some `E k`. -/
theorem exists_toLimitSections_eq [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ k, CompactSpace (E.obj k)] [∀ k, QuasiSeparatedSpace (E.obj k)] (hc : IsLimit c)
    (σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))) :
    ∃ (k : I) (s : F.obj.obj (op (Etale.mk (t.app k)))), toLimitSections F t hp k s = σ := by
  classical
  let G := (etalePullback p).obj F
  let η := (etaleAdjunction p).unit.app F
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  -- local models around every point of the limit
  choose l Q φ b hQ hag hz using fun z ↦ exists_agreesWith F hp hc σ z
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit E c hc
  obtain ⟨Z, hZ⟩ := isCompact_univ.elim_finite_subcover
    (fun z ↦ Set.range (pullback.fst (c.π.app (l z)) (φ z).left))
    (fun z ↦ (isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)).isOpen_range)
    (fun z _ ↦ Set.mem_iUnion.2 ⟨z, hz z⟩)
  -- a common level `k₁`
  obtain ⟨k₁, hk₁⟩ := IsCofiltered.inf_objs_exists (Z.image l)
  let g₁ (z : Z) : k₁ ⟶ l z := (hk₁ (Finset.mem_image_of_mem l z.2)).some
  -- the images of the `Q z` in `E k₁` cover the image of the limit
  let U : (E.obj k₁).Opens := ⨆ z : Z, E.map (g₁ z) ⁻¹ᵁ
    (⟨Set.range (φ z).left,
      (isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)).isOpen_range⟩ : (E.obj (l z)).Opens)
  have hU : c.π.app k₁ ⁻¹ᵁ U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hzZ, x, rfl⟩ : ∃ z ∈ Z, y ∈ Set.range (pullback.fst (c.π.app (l z)) (φ z).left) := by
      simpa using hZ (Set.mem_univ y)
    have e₁ := congrArg (fun f ↦ f (pullback.fst (c.π.app (l z)) (φ z).left x))
      (c.w (g₁ ⟨z, hzZ⟩))
    have e₂ := congrArg (fun f ↦ f x) (pullback.condition (f := c.π.app (l z)) (g := (φ z).left))
    simp only [Scheme.Hom.comp_apply] at e₁ e₂
    change c.π.app k₁ (pullback.fst (c.π.app (l z)) (φ z).left x) ∈ U
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨z, hzZ⟩, pullback.snd (c.π.app (l z)) (φ z).left x, e₂.symm.trans e₁.symm⟩
  -- so the `Q z` cover `E k₂` for some `k₂ ⟶ k₁`
  obtain ⟨k₂, g₂, hg₂⟩ := exists_map_eq_top E c hc U hU
  let h₂ (z : Z) : k₂ ⟶ l z := g₂ ≫ g₁ z
  let Q₂ (z : Z) := restrictObj t (φ z) (h₂ z)
  let φ₂ (z : Z) : Q₂ z ⟶ Etale.mk (t.app k₂) := restrictHom (φ z) (h₂ z)
  obtain ⟨b₂, hag₂⟩ : ∃ b₂ : ∀ z : Z, F.obj.obj (op (Q₂ z)),
      ∀ z, AgreesWith F hp σ (φ₂ z) (b₂ z) :=
    ⟨_, fun z ↦ (hag z).restrict (h₂ z)⟩
  have hQ₂ (z : Z) : CompactSpace (Q₂ z).left := by
    have := hQ z
    change CompactSpace ↑(pullback (φ z).left (E.map (h₂ z)))
    infer_instance
  have hcov₂ (y : E.obj k₂) : ∃ (z : Z) (q : (Q₂ z).left), (φ₂ z).left q = y := by
    have hy : y ∈ E.map g₂ ⁻¹ᵁ U := by
      rw [hg₂]
      trivial
    obtain ⟨z, q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    have e := congrArg (fun f ↦ f y) (E.map_comp g₂ (g₁ z))
    simp only [Scheme.Hom.comp_apply] at e
    obtain ⟨r, -, hr⟩ := Pullback.exists_preimage_pullback (f := (φ z).left)
      (g := E.map (h₂ z)) q y (hq.trans e.symm)
    exact ⟨z, r, hr⟩
  -- the overlaps `Q₂ z ×_{E k₂} Q₂ z'`
  let T (zz : Z × Z) : X.Etale :=
    Etale.mk (pullback.fst (φ₂ zz.1).left (φ₂ zz.2).left ≫ (Q₂ zz.1).hom)
  let φT (zz : Z × Z) : T zz ⟶ Etale.mk (t.app k₂) := MorphismProperty.Over.homMk
    (pullback.fst (φ₂ zz.1).left (φ₂ zz.2).left ≫ (φ₂ zz.1).left)
    (by rw [Category.assoc]; rfl) trivial
  let ψ₁ (zz : Z × Z) : T zz ⟶ Q₂ zz.1 :=
    MorphismProperty.Over.homMk (pullback.fst (φ₂ zz.1).left (φ₂ zz.2).left) rfl trivial
  let ψ₂ (zz : Z × Z) : T zz ⟶ Q₂ zz.2 :=
    MorphismProperty.Over.homMk (pullback.snd (φ₂ zz.1).left (φ₂ zz.2).left) (by
      change pullback.snd _ _ ≫ (φ₂ zz.2).left ≫ t.app k₂ =
        pullback.fst _ _ ≫ (φ₂ zz.1).left ≫ t.app k₂
      rw [pullback.condition_assoc]) trivial
  have hT (zz : Z × Z) : CompactSpace (T zz).left := by
    have := hQ₂ zz.1
    have := hQ₂ zz.2
    have : QuasiSeparatedSpace (Etale.mk (t.app k₂)).left :=
      inferInstanceAs (QuasiSeparatedSpace (E.obj k₂))
    have : QuasiCompact (φ₂ zz.2).left := quasiCompact_of_compactSpace _
    change CompactSpace ↑(pullback (φ₂ zz.1).left (φ₂ zz.2).left)
    infer_instance
  have agr₁ (zz : Z × Z) : AgreesWith F hp σ (φT zz) (F.obj.map (ψ₁ zz).op (b₂ zz.1)) :=
    (hag₂ zz.1).comp (ψ₁ zz) (φT zz) (𝟙 k₂) (by
      rw [E.map_id]
      exact (Category.comp_id _).symm)
  have agr₂ (zz : Z × Z) : AgreesWith F hp σ (φT zz) (F.obj.map (ψ₂ zz).op (b₂ zz.2)) :=
    (hag₂ zz.2).comp (ψ₂ zz) (φT zz) (𝟙 k₂) (by
      rw [E.map_id]
      exact pullback.condition.symm.trans (Category.comp_id _).symm)
  choose m gm hm using fun zz : Z × Z ↦ by
    haveI := hT zz
    exact exists_forall_mem_etaleAgreementLocus hc (agr₁ zz) (agr₂ zz)
  -- a common level `k₃` over all the `m zz`
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image fun zz : Z × Z ↦ Over.mk (gm zz))
  let k₃ := S.left
  let g₃ : k₃ ⟶ k₂ := S.hom
  have hm₃ (zz : Z × Z) (x : ↑(pullback (φT zz).left (E.map g₃))) :
      pullback.fst (φT zz).left (E.map g₃) x ∈ etaleAgreementLocus F
        (F.obj.map (ψ₁ zz).op (b₂ zz.1)) (F.obj.map (ψ₂ zz).op (b₂ zz.2)) := by
    obtain ⟨a⟩ := hS (Finset.mem_image_of_mem _ (Finset.mem_univ zz))
    have e₀ : E.map a.left ≫ E.map (gm zz) = E.map g₃ := by
      rw [← E.map_comp]
      exact congrArg E.map (Over.w a)
    have e₀' := congrArg (fun f ↦ f (pullback.snd (φT zz).left (E.map g₃) x)) e₀
    have e₁ := congrArg (fun f ↦ f x) (pullback.condition (f := (φT zz).left) (g := E.map g₃))
    simp only [Scheme.Hom.comp_apply] at e₀' e₁
    obtain ⟨x', hx', -⟩ := Pullback.exists_preimage_pullback (f := (φT zz).left)
      (g := E.map (gm zz)) (pullback.fst (φT zz).left (E.map g₃) x)
      (E.map a.left (pullback.snd (φT zz).left (E.map g₃) x))
      (e₁.trans e₀'.symm)
    exact hx' ▸ hm zz x'
  -- the pieces at level `k₃`
  let Q₃ (z : Z) := restrictObj t (φ₂ z) g₃
  let φ₃ (z : Z) : Q₃ z ⟶ Etale.mk (t.app k₃) := restrictHom (φ₂ z) g₃
  let ψ₃ (z : Z) : Q₃ z ⟶ Q₂ z := restrictFst (φ₂ z) g₃
  let b₃ (z : Z) : F.obj.obj (op (Q₃ z)) := F.obj.map (ψ₃ z).op (b₂ z)
  have hag₃ (z : Z) : AgreesWith F hp σ (φ₃ z) (b₃ z) := (hag₂ z).restrict g₃
  have hcov₃ (y : E.obj k₃) : ∃ (z : Z) (q : (Q₃ z).left), (φ₃ z).left q = y := by
    obtain ⟨z, q, hq⟩ := hcov₂ (E.map g₃ y)
    obtain ⟨r, -, hr⟩ := Pullback.exists_preimage_pullback (f := (φ₂ z).left) (g := E.map g₃)
      q y hq
    exact ⟨z, r, hr⟩
  have hψφ (z : Z) : (ψ₃ z).left ≫ (φ₂ z).left = (φ₃ z).left ≫ E.map g₃ := pullback.condition
  -- glue the `b₃ z` to a section `s` over `E k₃`
  have hcov : Sieve.ofArrows Q₃ φ₃ ∈ X.smallEtaleTopology (Etale.mk (t.app k₃)) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨z, q, hq⟩ := hcov₃ y
    exact Set.mem_iUnion.2 ⟨z, q, hq⟩
  have hS' := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hS' b₃ (fun i j Y gi gj hij ↦ by
    have hij' : gi.left ≫ (φ₃ i).left = gj.left ≫ (φ₃ j).left :=
      congrArg (fun f ↦ f.left) hij
    have hu : (gi.left ≫ (ψ₃ i).left) ≫ (φ₂ i).left = (gj.left ≫ (ψ₃ j).left) ≫ (φ₂ j).left := by
      rw [Category.assoc, Category.assoc, hψφ, hψφ, reassoc_of% hij']
    let u : Y ⟶ T (i, j) := MorphismProperty.Over.homMk
      (pullback.lift (gi.left ≫ (ψ₃ i).left) (gj.left ≫ (ψ₃ j).left) hu) (by
        change pullback.lift _ _ hu ≫ pullback.fst _ _ ≫ (Q₂ i).hom = Y.hom
        rw [pullback.lift_fst_assoc, Category.assoc, MorphismProperty.Over.w (ψ₃ i),
          MorphismProperty.Over.w gi]) trivial
    have hu₁ : u ≫ ψ₁ (i, j) = gi ≫ ψ₃ i := by
      apply MorphismProperty.Over.Hom.ext
      rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
      exact pullback.lift_fst _ _ _
    have hu₂ : u ≫ ψ₂ (i, j) = gj ≫ ψ₃ j := by
      apply MorphismProperty.Over.Hom.ext
      rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
      exact pullback.lift_snd _ _ _
    have hrange : Set.range u.left ⊆ etaleAgreementLocus F
        (F.obj.map (ψ₁ (i, j)).op (b₂ i)) (F.obj.map (ψ₂ (i, j)).op (b₂ j)) := by
      rintro _ ⟨y, rfl⟩
      have e₀ : u.left ≫ (φT (i, j)).left = gi.left ≫ (φ₃ i).left ≫ E.map g₃ := by
        change pullback.lift _ _ hu ≫ pullback.fst _ _ ≫ (φ₂ i).left = _
        rw [pullback.lift_fst_assoc, Category.assoc, hψφ]
      have e := congrArg (fun f ↦ f y) e₀
      simp only [Scheme.Hom.comp_apply] at e
      obtain ⟨x, hx, -⟩ := Pullback.exists_preimage_pullback (f := (φT (i, j)).left)
        (g := E.map g₃) (u.left y) ((φ₃ i).left (gi.left y)) e
      exact hx ▸ hm₃ (i, j) x
    have H := map_eq_of_range_subset_etaleAgreementLocus u hrange
    change F.obj.map gi.op (F.obj.map (ψ₃ i).op (b₂ i)) =
      F.obj.map gj.op (F.obj.map (ψ₃ j).op (b₂ j))
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← hu₁, ← hu₂,
      op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact H)
  refine ⟨k₃, s, ?_⟩
  -- `s` restricts to `σ`, by separatedness on the cover `c.pt ×_{E k₃} Q₃ z` of `c.pt`
  have hcovP : Sieve.ofArrows (fun z : Z ↦ limitPullback (c := c) (φ₃ z))
      (fun z ↦ (Etale.isTerminalTop c.pt).from _) ∈ c.pt.smallEtaleTopology (Etale.top c.pt) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨z, q, hq⟩ := hcov₃ (c.π.app k₃ y)
    obtain ⟨x, hx, -⟩ := Pullback.exists_preimage_pullback (f := c.π.app k₃)
      (g := (φ₃ z).left) y q hq.symm
    exact Set.mem_iUnion.2 ⟨z, x, hx⟩
  refine (hG _ hcovP).isSeparatedFor.ext ?_
  rintro Y f ⟨_, h, _, ⟨z⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  congr 1
  have hsec : (Etale.isTerminalTop c.pt).from (limitPullback (c := c) (φ₃ z)) ≫
      limitSection t hp k₃ = limitPullbackHom hp (φ₃ z) ≫ (Etale.pullback p).map (φ₃ z) := by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    apply pullback.hom_ext
    · simp only [limitSection, Category.assoc, Etale.pullback_map_left_fst,
        limitPullbackHom_left_fst_assoc]
      change pullback.fst (c.π.app k₃) (φ₃ z).left ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      rw [pullback.lift_fst]
      exact pullback.condition
    · simp only [limitSection, Category.assoc, Etale.pullback_map_left_snd,
        limitPullbackHom_left_snd]
      change pullback.fst (c.π.app k₃) (φ₃ z).left ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd]
      exact Category.comp_id _
  have nat : η.hom.app (op (Q₃ z)) (F.obj.map (φ₃ z).op s) =
      G.obj.map ((Etale.pullback p).map (φ₃ z)).op
        (η.hom.app (op (Etale.mk (t.app k₃))) s) :=
    NatTrans.naturality_apply η.hom (φ₃ z).op s
  unfold toLimitSections
  rw [← Functor.map_comp_apply, ← op_comp, hsec, op_comp, Functor.map_comp_apply, ← nat, hs z]
  exact hag₃ z

end Gluing

section StrictLocalization

open LimitSections

namespace Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (Type u))

/-- The étale structure morphisms `X ×_S V_k ⟶ X` of the affine étale neighbourhoods. -/
@[simps]
def affineEtaleNbhdPullbackDiagramSnd :
    s.affineEtaleNbhdPullbackDiagram f ⟶ (Functor.const _).obj X where
  app k := pullback.snd k.nbhd.hom f
  naturality k k' g := by simp [pullback.map]

instance (k : s.AffineEtaleNbhd) : Etale ((affineEtaleNbhdPullbackDiagramSnd f s).app k) :=
  inferInstanceAs (Etale (pullback.snd k.nbhd.hom f))

lemma affineEtaleNbhdPullbackCone_π_app_snd (k : s.AffineEtaleNbhd) :
    (s.affineEtaleNbhdPullbackCone f).π.app k ≫ (affineEtaleNbhdPullbackDiagramSnd f s).app k =
      pullback.snd s.fromSpecStrictLocalization f := by
  simp [pullback.map]

/-- **Surjectivity of `(f_* F)_{s̄} ⟶ Γ(X ×_S Spec 𝒪^{sh}_{S,s̄}, F)`** for `f` quasi-compact and
quasi-separated (SGA 4 VIII 5.2, Stacks 03Q9 in degree `0`): a consequence of
`AlgebraicGeometry.Scheme.exists_toLimitSections_eq`, since `X ×_S Spec 𝒪^{sh}_{S,s̄}` is the
limit of the `X ×_S V` over the affine étale neighbourhoods `V` of `s̄`. -/
theorem surjective_pushforwardStalkToStrictLocalization [QuasiCompact f] [QuasiSeparated f] :
    Function.Surjective (f.pushforwardStalkToStrictLocalization s F) := by
  intro σ
  obtain ⟨k, a, ha⟩ := exists_toLimitSections_eq F (t := affineEtaleNbhdPullbackDiagramSnd f s)
    (affineEtaleNbhdPullbackCone_π_app_snd f s) (s.isLimitAffineEtaleNbhdPullbackCone f) σ
  refine ⟨(pointSmallEtale s).toPresheafFiber k.nbhd k.point ((etalePushforward f).obj F).obj a,
    ?_⟩
  have e : limitSection (affineEtaleNbhdPullbackDiagramSnd f s)
      (affineEtaleNbhdPullbackCone_π_app_snd f s) k =
        f.strictLocalizationSection s k.nbhd k.point := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst, affineEtaleNbhdPullbackCone_π_app_eq]
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
      rw [pullback.lift_snd, pullback.lift_snd]
      rfl
  rw [pushforwardStalkToStrictLocalization_toPresheafFiber, ← ha]
  unfold toLimitSections
  rw [e]
  rfl

/-- **SGA 4 VIII 5.2, Stacks 03Q9 in degree `0`**: for `f : X ⟶ S` quasi-compact and
quasi-separated, the map `(f_* F)_{s̄} ⟶ Γ(X ×_S Spec 𝒪^{sh}_{S,s̄}, F)` is bijective. -/
theorem bijective_pushforwardStalkToStrictLocalization [QuasiCompact f] [QuasiSeparated f] :
    Function.Bijective (f.pushforwardStalkToStrictLocalization s F) :=
  ⟨f.injective_pushforwardStalkToStrictLocalization s F,
    f.surjective_pushforwardStalkToStrictLocalization s F⟩

end Hom

/-- SGA 4 VIII 5.2 in degree `0` (`PushforwardStalkStrictLocalizationStatement`) holds. -/
theorem pushforwardStalkStrictLocalizationStatement :
    PushforwardStalkStrictLocalizationStatement.{u} :=
  fun _ _ f _ _ _ _ _ s F ↦ f.bijective_pushforwardStalkToStrictLocalization s F

end StrictLocalization

end AlgebraicGeometry.Scheme
