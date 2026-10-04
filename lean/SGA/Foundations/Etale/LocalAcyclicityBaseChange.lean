/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Sites.LocallyBijective
import SGA.Foundations.Etale.LocalAcyclicityConstant

/-!
# Sections of inverse images along geometrically connected morphisms

Let `p : T ⟶ S` be flat, quasi-compact and geometrically connected (mathlib's
`GeometricallyConnected`: every fibre over the spectrum of a field is nonempty and connected).
Then for every étale sheaf of sets `F` on `S`, the unit `F ⟶ p_* p^* F` is an isomorphism; in
particular `Γ(S, F) = Γ(T, p^* F)` (Stacks 0A3H;
`AlgebraicGeometry.Scheme.isIso_etaleAdjunction_unit_app_of_geometricallyConnected`).

We prove the relative form `AlgebraicGeometry.Scheme.bijective_map_etaleAdjunction_unit`: for
`g : T ⟶ Y`, an étale `Y`-scheme `V` and a morphism of étale `T`-schemes `ι : U ⟶ T ×_Y V` such that
`c : U ⟶ V` is flat, quasi-compact and geometrically connected, `s ↦ ι^*(η s)` is a bijection
`K(V) → (g^* K)(U)`. This is the form needed for the base change theorem Stacks 0EZX
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_forall_exists`): for a cartesian square
`X' = X ×_Y Y'` such that every étale `Y'`-scheme is covered by étale `Y'`-schemes `U` with
`U ⟶ Y' ×_Y V ⟶ V` flat, quasi-compact and geometrically connected for some `V` étale over `Y`, the
base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism; on sections over such a `U` both
sides are `F(X ×_Y V)` (`AlgebraicGeometry.Scheme.bijective_etaleBaseChangeMap_app`).

The proof works with germs at geometric points and the agreement loci of sections
(`AlgebraicGeometry.Scheme.etaleAgreementLocus`, from `SGA.Foundations.EtaleStalkProper`), and not
with fpqc descent as in Stacks:
* injectivity: two sections of `K` whose images agree have the same germs at the images of the
  geometric points of `U` (`AlgebraicGeometry.Scheme.range_subset_etaleAgreementLocus`), and `c`
  is surjective;
* the agreement locus of two sections of `g^* K` over `U` is a union of fibres of `c`
  (`AlgebraicGeometry.Scheme.mem_etaleAgreementLocus_of_eq`): on a geometric fibre `Z` of `c`,
  which is connected, the inverse image of `g^* K` is constant, being pulled back from a
  geometric point of `Y` (`AlgebraicGeometry.Scheme.isConstant_etalePullback_of_fac`), and two
  sections of a constant sheaf on a connected scheme which agree somewhere are equal;
* local surjectivity: a germ of a section `τ` of `g^* K` at a geometric point of `U` is the germ
  of the image of a section `a₁` of `K` (`AlgebraicGeometry.Scheme.sheafFiberEtalePullbackIso`);
  the agreement locus of `τ` and the image of `a₁` is open, nonempty and saturated for `c`, so its
  image in `V` is open (`c` is a quotient map, `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`)
  and `τ` comes from `a₁` over it (`AlgebraicGeometry.Scheme.exists_map_etaleAdjunction_unit_eq`);
* the local sections glue, by injectivity.

## References

* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [SGA 4, Exposé XV, 1][sga4]
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

section Main

variable {T Y : Scheme.{u}} (g : T ⟶ Y) (K : Sheaf Y.smallEtaleTopology (Type u))

/-- A morphism between étale `X`-schemes is étale. -/
lemma Etale.etale_left {X : Scheme.{u}} {V W : X.Etale} (φ : V ⟶ W) : Etale φ.left :=
  MorphismProperty.of_postcomp (W := @Etale) φ.left W.hom W.prop
    (by rw [MorphismProperty.Over.w φ]; exact V.prop)

/-- Two morphisms into `T ×_Y V` in the small étale site of `T` are equal if their compositions
with the projection to `V` are. -/
lemma Etale.pullback_hom_ext {V : Y.Etale} {U : T.Etale} {a b : U ⟶ (Etale.pullback g).obj V}
    (h : a.left ≫ pullback.fst V.hom g = b.left ≫ pullback.fst V.hom g) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext h
  change a.left ≫ ((Etale.pullback g).obj V).hom = b.left ≫ ((Etale.pullback g).obj V).hom
  rw [MorphismProperty.Over.w a, MorphismProperty.Over.w b]

variable {g K}

/-- Compatibility of the maps `s ↦ ι^*(η s)`, `K(V) → (g^* K)(U)` for `ι : U ⟶ T ×_Y V`, with
restrictions. -/
lemma map_etaleAdjunction_unit_comp {V₁ V₂ : Y.Etale} (φ : V₁ ⟶ V₂) {U₁ U₂ : T.Etale}
    (ι₁ : U₁ ⟶ (Etale.pullback g).obj V₁) (ι₂ : U₂ ⟶ (Etale.pullback g).obj V₂) (κ : U₁ ⟶ U₂)
    (h : ι₁ ≫ (Etale.pullback g).map φ = κ ≫ ι₂) (s : K.obj.obj (op V₂)) :
    ((etalePullback g).obj K).obj.map ι₁.op
        (((etaleAdjunction g).unit.app K).hom.app (op V₁) (K.obj.map φ.op s)) =
      ((etalePullback g).obj K).obj.map κ.op (((etalePullback g).obj K).obj.map ι₂.op
        (((etaleAdjunction g).unit.app K).hom.app (op V₂) s)) := by
  have n : ((etaleAdjunction g).unit.app K).hom.app (op V₁) (K.obj.map φ.op s) =
      ((etalePullback g).obj K).obj.map ((Etale.pullback g).map φ).op
        (((etaleAdjunction g).unit.app K).hom.app (op V₂) s) :=
    NatTrans.naturality_apply ((etaleAdjunction g).unit.app K).hom φ.op s
  rw [n, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h]

variable (g K)

/-- The agreement locus of two sections of `g^* K` over `U` is a union of fibres of any
geometrically connected `c : U ⟶ B` through which `U ⟶ Y` factors (with the rest of the
factorization `B ⟶ Y` arbitrary): on a geometric fibre `Z` of `c`, which is connected, the
inverse image of `g^* K` is constant, being pulled back from a geometric point of `Y`. -/
lemma mem_etaleAgreementLocus_of_eq {B : Scheme.{u}} (U : T.Etale) (c : U.left ⟶ B) (b : B ⟶ Y)
    (hc : U.hom ≫ g = c ≫ b) [GeometricallyConnected c]
    {τ α : ((etalePullback g).obj K).obj.obj (op U)} {z₁ z₂ : U.left} (hz : c z₁ = c z₂)
    (h₁ : z₁ ∈ etaleAgreementLocus _ τ α) : z₂ ∈ etaleAgreementLocus _ τ α := by
  let G := (etalePullback g).obj K
  let yb := B.fromSpecAlgClosure (c z₁)
  let P := pullback c yb
  let cP : P ⟶ U.left := pullback.fst _ _
  have : ConnectedSpace P := ‹GeometricallyConnected c›.geometrically_connectedSpace yb _ _
    (IsPullback.of_hasPullback c yb)
  let j : P ⟶ T := cP ≫ U.hom
  have hjU : cP ≫ U.hom = 𝟙 P ≫ j := (Category.id_comp _).symm
  let ι : Etale.top P ⟶ (Etale.pullback j).obj U :=
    MorphismProperty.Over.homMk (pullback.lift cP (𝟙 P) hjU) (pullback.lift_snd _ _ _) trivial
  let r : G.obj.obj (op U) → ((etalePullback j).obj G).obj.obj (op (Etale.top P)) := fun s ↦
    ((etalePullback j).obj G).obj.map ι.op (((etaleAdjunction j).unit.app G).hom.app (op U) s)
  have hpt (z : U.left) (hz : c z = c z₁) : ∃ ζ : P, cP ζ = z := by
    obtain ⟨ζ, hζ, -⟩ := Pullback.exists_preimage_pullback (f := c) (g := yb) z
      (IsLocalRing.closedPoint (AlgebraicClosure (B.residueField (c z₁))))
      (hz.trans (Scheme.fromSpecAlgClosure_apply _ _).symm)
    exact ⟨ζ, hζ⟩
  obtain ⟨ζ₁, hζ₁⟩ := hpt z₁ rfl
  obtain ⟨ζ₂, hζ₂⟩ := hpt z₂ hz.symm
  -- `r τ` and `r α` agree near `ζ₁`
  have hA : ζ₁ ∈ etaleAgreementLocus _ (r τ) (r α) := by
    obtain ⟨V', φ, v', hst, hv'⟩ := h₁
    have := Etale.etale_left φ
    let W : P.Etale := Etale.mk (pullback.snd φ.left cP)
    have hWc : pullback.fst φ.left cP ≫ V'.hom = pullback.snd φ.left cP ≫ j := by
      change pullback.fst φ.left cP ≫ V'.hom = pullback.snd φ.left cP ≫ cP ≫ U.hom
      rw [← MorphismProperty.Over.w φ, pullback.condition_assoc]
    let k : W ⟶ (Etale.pullback j).obj V' := MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst φ.left cP) (pullback.snd φ.left cP) hWc)
      (pullback.lift_snd _ _ _) trivial
    have hk : (Etale.isTerminalTop P).from W ≫ ι = k ≫ (Etale.pullback j).map φ := by
      apply Etale.pullback_hom_ext
      have e1 : ((Etale.isTerminalTop P).from W).left = W.hom := rfl
      rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, e1,
        Category.assoc, Category.assoc, Etale.pullback_map_left_fst]
      change pullback.snd φ.left cP ≫ pullback.lift cP (𝟙 P) hjU ≫ pullback.fst U.hom j =
        pullback.lift _ _ hWc ≫ pullback.fst V'.hom j ≫ φ.left
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.condition]
    obtain ⟨w, hw₁, hw₂⟩ := Pullback.exists_preimage_pullback (f := φ.left) (g := cP) v' ζ₁
      (hv'.trans hζ₁.symm)
    refine ⟨W, (Etale.isTerminalTop P).from W, w, ?_, hw₂⟩
    have nat (s : G.obj.obj (op U)) :
        ((etalePullback j).obj G).obj.map ((Etale.pullback j).map φ).op
          (((etaleAdjunction j).unit.app G).hom.app (op U) s) =
        ((etaleAdjunction j).unit.app G).hom.app (op V') (G.obj.map φ.op s) :=
      (NatTrans.naturality_apply ((etaleAdjunction j).unit.app G).hom φ.op s).symm
    simp only [r]
    rw [← Functor.map_comp_apply, ← op_comp, hk, op_comp, Functor.map_comp_apply, nat, hst,
      ← nat, ← Functor.map_comp_apply, ← op_comp, ← hk, op_comp, Functor.map_comp_apply]
  have hrr : r τ = r α := by
    have : Sheaf.IsConstant P.smallEtaleTopology ((etalePullback j).obj G) := by
      have := isConstant_etalePullback_of_fac (j ≫ g) (pullback.snd _ _) (yb ≫ b)
        (by simp only [j, cP, Category.assoc, hc, pullback.condition_assoc]) K
      exact Sheaf.isConstant_congr _ ((etalePullbackComp j g).app K).symm
    exact eq_of_etaleAgreementLocus_nonempty _ ⟨ζ₁, hA⟩
  refine range_subset_etaleAgreementLocus j ι hrr ⟨ζ₂, ?_⟩
  rw [← hζ₂]
  change (pullback.lift cP (𝟙 P) hjU ≫ pullback.fst U.hom j) ζ₂ = cP ζ₂
  rw [pullback.lift_fst]
  rfl

variable {g K}

/-- The base change `U ×_V V'` of an étale `T`-scheme `U` with `c : U ⟶ V` along `φ : V' ⟶ V`. -/
noncomputable abbrev etaleRefineObj {V V' : Y.Etale} (U : T.Etale) (c : U.left ⟶ V.left)
    (φ : V' ⟶ V) : T.Etale :=
  have := Etale.etale_left φ
  Etale.mk (pullback.fst c φ.left ≫ U.hom)

/-- The projection `U ×_V V' ⟶ U`. -/
noncomputable abbrev etaleRefineFst {V V' : Y.Etale} (U : T.Etale) (c : U.left ⟶ V.left)
    (φ : V' ⟶ V) : etaleRefineObj U c φ ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst c φ.left) rfl trivial

/-- The morphism `U ×_V V' ⟶ T ×_Y V'` induced by `ι : U ⟶ T ×_Y V`. -/
noncomputable abbrev etaleRefineHom {V V' : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) (φ : V' ⟶ V) :
    etaleRefineObj U (ι.left ≫ pullback.fst V.hom g) φ ⟶ (Etale.pullback g).obj V' :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.snd _ φ.left)
    (pullback.fst (ι.left ≫ pullback.fst V.hom g) φ.left ≫ U.hom) (by
      rw [← MorphismProperty.Over.w φ, ← pullback.condition_assoc, Category.assoc,
        Category.assoc, pullback.condition]
      change _ ≫ ι.left ≫ ((Etale.pullback g).obj V).hom ≫ g = _
      rw [MorphismProperty.Over.w_assoc ι]))
    (pullback.lift_snd _ _ _) trivial

@[reassoc]
lemma etaleRefineHom_left_fst {V V' : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) (φ : V' ⟶ V) :
    (etaleRefineHom ι φ).left ≫ pullback.fst V'.hom g = pullback.snd _ φ.left :=
  pullback.lift_fst _ _ _

/-- The morphism `U ×_V V'' ⟶ U ×_V V'` induced by `ψ : V'' ⟶ V'` over `φ : V' ⟶ V`. -/
noncomputable abbrev etaleRefineMap {V V' V'' : Y.Etale} (U : T.Etale) (c : U.left ⟶ V.left)
    (φ : V' ⟶ V) (ψ : V'' ⟶ V') :
    etaleRefineObj U c (ψ ≫ φ) ⟶ etaleRefineObj U c φ :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.fst c (ψ ≫ φ).left)
      (pullback.snd c (ψ ≫ φ).left ≫ ψ.left) (by
        rw [pullback.condition, Category.assoc]
        rfl))
    (pullback.lift_fst_assoc _ _ _ _) trivial

lemma etaleRefineMap_fst {V V' V'' : Y.Etale} (U : T.Etale) (c : U.left ⟶ V.left)
    (φ : V' ⟶ V) (ψ : V'' ⟶ V') :
    etaleRefineMap U c φ ψ ≫ etaleRefineFst U c φ = etaleRefineFst U c (ψ ≫ φ) :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

lemma etaleRefineHom_comp {V V' V'' : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) (φ : V' ⟶ V) (ψ : V'' ⟶ V') :
    etaleRefineHom ι (ψ ≫ φ) ≫ (Etale.pullback g).map ψ =
      etaleRefineMap U (ι.left ≫ pullback.fst V.hom g) φ ψ ≫ etaleRefineHom ι φ := by
  apply Etale.pullback_hom_ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
    Category.assoc, Etale.pullback_map_left_fst, etaleRefineHom_left_fst,
    etaleRefineHom_left_fst_assoc]
  exact (pullback.lift_snd _ _ _).symm

lemma etaleRefineHom_fst {V V' : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) (φ : V' ⟶ V) :
    etaleRefineHom ι φ ≫ (Etale.pullback g).map φ =
      etaleRefineFst U (ι.left ≫ pullback.fst V.hom g) φ ≫ ι := by
  apply Etale.pullback_hom_ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
    Etale.pullback_map_left_fst, etaleRefineHom_left_fst_assoc, Category.assoc]
  exact pullback.condition.symm

/-- Injectivity of `K(V) → (g^* K)(U)`, `s ↦ ι^* (η s)`, when `U ⟶ V` is surjective. -/
lemma injective_map_etaleAdjunction_unit {V : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) [Surjective (ι.left ≫ pullback.fst V.hom g)] :
    Function.Injective (fun s : K.obj.obj (op V) ↦ ((etalePullback g).obj K).obj.map ι.op
      (((etaleAdjunction g).unit.app K).hom.app (op V) s)) := by
  intro a b hab
  have hr := range_subset_etaleAgreementLocus g ι hab
  refine eq_of_etaleAgreementLocus_eq_univ fun v ↦ ?_
  obtain ⟨z, hz⟩ := (ι.left ≫ pullback.fst V.hom g).surjective v
  exact hr ⟨z, hz⟩

variable (K) in
/-- The key step of Stacks 0A3H: let `ι : U ⟶ T ×_Y V` be such that `c : U ⟶ V` is flat,
quasi-compact and geometrically connected. Then every section of `g^* K` over `U` comes, near any
given point of `V`, from a section of `K`. -/
lemma exists_map_etaleAdjunction_unit_eq {V : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) [Flat (ι.left ≫ pullback.fst V.hom g)]
    [QuasiCompact (ι.left ≫ pullback.fst V.hom g)]
    [GeometricallyConnected (ι.left ≫ pullback.fst V.hom g)]
    (τ : ((etalePullback g).obj K).obj.obj (op U)) (v : V.left) :
    ∃ (V' : Y.Etale) (φ : V' ⟶ V) (v' : V'.left) (a : K.obj.obj (op V')), φ.left v' = v ∧
      ((etalePullback g).obj K).obj.map (etaleRefineHom ι φ).op
          (((etaleAdjunction g).unit.app K).hom.app (op V') a) =
        ((etalePullback g).obj K).obj.map
          (etaleRefineFst U (ι.left ≫ pullback.fst V.hom g) φ).op τ := by
  let c := ι.left ≫ pullback.fst V.hom g
  let G := (etalePullback g).obj K
  let η := (etaleAdjunction g).unit.app K
  have hcV : U.hom ≫ g = c ≫ V.hom := by
    change U.hom ≫ g = ι.left ≫ pullback.fst V.hom g ≫ V.hom
    rw [pullback.condition, ← MorphismProperty.Over.w_assoc ι]
    rfl
  obtain ⟨z, hz⟩ := c.surjective v
  let x := U.left.fromSpecAlgClosure z
  let t := x ≫ U.hom
  let ŵ : (pointSmallEtale t).fiber.obj U := Over.homMk x rfl
  let e := (sheafFiberEtalePullbackIso g t).app K
  have he : Function.Bijective e.hom := (isIso_iff_bijective _).1 inferInstance
  obtain ⟨δ, hδ⟩ := he.2 ((pointSmallEtale t).toPresheafFiber U ŵ G.obj τ)
  obtain ⟨V₁, v₁, a₁, rfl⟩ := (pointSmallEtale (t ≫ g)).toPresheafFiber_jointly_surjective
    (P := K.obj) δ
  let w₁ := (pointSmallEtaleFiberHom g t).app V₁ v₁
  have hgerm : (pointSmallEtale t).toPresheafFiber U ŵ G.obj τ =
      (pointSmallEtale t).toPresheafFiber ((Etale.pullback g).obj V₁) w₁ G.obj
        (η.hom.app (op V₁) a₁) := by
    rw [← hδ]
    exact sheafFiberEtalePullbackIso_hom_app_toPresheafFiber g t K V₁ v₁ a₁
  -- the common refinement `V₂ = V ×_Y V₁` and `U₂ = U ×_V V₂`
  let V₂ : Y.Etale := Etale.mk (pullback.fst V.hom V₁.hom ≫ V.hom)
  let π₁ : V₂ ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom V₁.hom) rfl trivial
  let π₂ : V₂ ⟶ V₁ :=
    MorphismProperty.Over.homMk (pullback.snd V.hom V₁.hom) pullback.condition.symm trivial
  let U₂ := etaleRefineObj U c π₁
  let ι₂ := etaleRefineHom ι π₁
  let c₂ := pullback.snd c π₁.left
  have e₁ : (x ≫ c) ≫ V.hom = t ≫ g := by
    rw [Category.assoc, ← hcV, ← Category.assoc]
  have e₂ : (w₁.left ≫ pullback.fst V₁.hom g) ≫ V₁.hom = t ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w w₁)
  have hxc : (x ≫ c) ≫ V.hom = (w₁.left ≫ pullback.fst V₁.hom g) ≫ V₁.hom := e₁.trans e₂.symm
  let m : Spec (.of (AlgebraicClosure (U.left.residueField z))) ⟶ V₂.left :=
    pullback.lift (x ≫ c) (w₁.left ≫ pullback.fst V₁.hom g) hxc
  have hm : x ≫ c = m ≫ π₁.left := (pullback.lift_fst _ _ _).symm
  let ŵ₂ : (pointSmallEtale t).fiber.obj U₂ :=
    Over.homMk (pullback.lift x m hm) (pullback.lift_fst_assoc _ _ _ _)
  have h₁ : (pointSmallEtale t).fiber.map (etaleRefineFst U c π₁) ŵ₂ = ŵ := by
    rw [pointSmallEtale_fiber_map_apply]
    exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have h₂ : (pointSmallEtale t).fiber.map (ι₂ ≫ (Etale.pullback g).map π₂) ŵ₂ = w₁ := by
    rw [pointSmallEtale_fiber_map_apply]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change pullback.lift x m hm ≫ ((etaleRefineHom ι π₁).left ≫
        ((Etale.pullback g).map π₂).left) ≫ pullback.fst V₁.hom g = w₁.left ≫ _
      rw [Category.assoc, Etale.pullback_map_left_fst, etaleRefineHom_left_fst_assoc]
      change pullback.lift x m hm ≫ pullback.snd c π₁.left ≫ pullback.snd V.hom V₁.hom = _
      rw [pullback.lift_snd_assoc, pullback.lift_snd]
    · change pullback.lift x m hm ≫ ((etaleRefineHom ι π₁).left ≫
        ((Etale.pullback g).map π₂).left) ≫ pullback.snd V₁.hom g = w₁.left ≫ _
      rw [Category.assoc, Etale.pullback_map_left_snd]
      change pullback.lift x m hm ≫ (etaleRefineHom ι π₁).left ≫
        ((Etale.pullback g).obj V₂).hom = _
      rw [MorphismProperty.Over.w (etaleRefineHom ι π₁)]
      exact (Over.w ŵ₂).trans (Over.w w₁).symm
  let τ₂ := G.obj.map (etaleRefineFst U c π₁).op τ
  let α₂ := G.obj.map ι₂.op (η.hom.app (op V₂) (K.obj.map π₂.op a₁))
  have hα₂ : G.obj.map (ι₂ ≫ (Etale.pullback g).map π₂).op (η.hom.app (op V₁) a₁) = α₂ := by
    have n : η.hom.app (op V₂) (K.obj.map π₂.op a₁) =
        G.obj.map ((Etale.pullback g).map π₂).op (η.hom.app (op V₁) a₁) :=
      NatTrans.naturality_apply η.hom π₂.op a₁
    simp only [α₂]
    rw [n, ← Functor.map_comp_apply, ← op_comp]
  have hg₂ : (pointSmallEtale t).toPresheafFiber _ ŵ₂ G.obj τ₂ =
      (pointSmallEtale t).toPresheafFiber _ ŵ₂ G.obj α₂ := by
    rw [← hα₂]
    simp only [τ₂]
    rw [GrothendieckTopology.Point.toPresheafFiber_w_apply,
      GrothendieckTopology.Point.toPresheafFiber_w_apply, h₁, h₂]
    exact hgerm
  let pt : Spec (.of (AlgebraicClosure (U.left.residueField z))) := default
  have hmem := apply_mem_etaleAgreementLocus ŵ₂ hg₂ pt
  -- the agreement locus is the preimage of an open subset of `V₂`
  let A := etaleAgreementLocus G τ₂ α₂
  have hc₂ : U₂.hom ≫ g = c₂ ≫ V₂.hom := by
    change (pullback.fst c π₁.left ≫ U.hom) ≫ g = pullback.snd c π₁.left ≫ π₁.left ≫ V.hom
    rw [Category.assoc, hcV, pullback.condition_assoc]
  have hsat : c₂ ⁻¹' (c₂ '' A) = A := by
    refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
    rintro z ⟨z', hz', hzz'⟩
    exact mem_etaleAgreementLocus_of_eq g K U₂ c₂ V₂.hom hc₂ hzz' hz'
  have hB : IsOpen (c₂ '' A) := by
    rw [← (Flat.isQuotientMap_of_surjective c₂).isOpen_preimage, hsat]
    exact isOpen_etaleAgreementLocus _ _
  let B : V₂.left.Opens := ⟨c₂ '' A, hB⟩
  let V' : Y.Etale := Etale.mk (B.ι ≫ V₂.hom)
  let φ' : V' ⟶ V₂ := MorphismProperty.Over.homMk B.ι rfl trivial
  obtain ⟨b, hb⟩ : c₂ (ŵ₂.left pt) ∈ Set.range B.ι := by
    rw [Scheme.Opens.range_ι]
    exact ⟨_, hmem, rfl⟩
  refine ⟨V', φ' ≫ π₁, b, K.obj.map (φ' ≫ π₂).op a₁, ?_, ?_⟩
  · change π₁.left (B.ι b) = v
    rw [hb]
    change (ŵ₂.left ≫ c₂ ≫ π₁.left) pt = v
    have : ŵ₂.left ≫ c₂ ≫ π₁.left = x ≫ c := by
      change pullback.lift x m hm ≫ pullback.snd c π₁.left ≫ π₁.left = _
      rw [pullback.lift_snd_assoc, hm]
    rw [this, Scheme.Hom.comp_apply, Subsingleton.elim pt
      (IsLocalRing.closedPoint (AlgebraicClosure (U.left.residueField z)))]
    exact (congrArg c (Scheme.fromSpecAlgClosure_apply U.left z)).trans hz
  · let κ := etaleRefineMap U c π₁ φ'
    rw [op_comp, Functor.map_comp_apply,
      map_etaleAdjunction_unit_comp φ' (etaleRefineHom ι (φ' ≫ π₁)) ι₂ κ
        (etaleRefineHom_comp ι π₁ φ'), ← etaleRefineMap_fst U c π₁ φ', op_comp,
      Functor.map_comp_apply]
    refine (map_eq_of_range_subset_etaleAgreementLocus κ ?_).symm
    rintro _ ⟨z', rfl⟩
    refine hsat.subset ?_
    change ((etaleRefineMap U c π₁ φ').left ≫ pullback.snd c π₁.left) z' ∈ c₂ '' A
    rw [show (etaleRefineMap U c π₁ φ').left ≫ pullback.snd c π₁.left =
      pullback.snd c (φ' ≫ π₁).left ≫ φ'.left from pullback.lift_snd _ _ _]
    exact (Scheme.Opens.range_ι B).subset ⟨_, rfl⟩

variable (K) in
/-- **Stacks 0A3H, relative form.** Let `g : T ⟶ Y`, `K` an étale sheaf of sets on `Y`,
`V` étale over `Y` and `ι : U ⟶ T ×_Y V` a morphism of étale `T`-schemes such that the composite
`c : U ⟶ V` is flat, quasi-compact and geometrically connected. Then `s ↦ ι^*(η s)` is a
bijection `K(V) → (g^* K)(U)`. -/
theorem bijective_map_etaleAdjunction_unit {V : Y.Etale} {U : T.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) [Flat (ι.left ≫ pullback.fst V.hom g)]
    [QuasiCompact (ι.left ≫ pullback.fst V.hom g)]
    [GeometricallyConnected (ι.left ≫ pullback.fst V.hom g)] :
    Function.Bijective (fun s : K.obj.obj (op V) ↦ ((etalePullback g).obj K).obj.map ι.op
      (((etaleAdjunction g).unit.app K).hom.app (op V) s)) := by
  let c := ι.left ≫ pullback.fst V.hom g
  let G := (etalePullback g).obj K
  let η := (etaleAdjunction g).unit.app K
  refine ⟨injective_map_etaleAdjunction_unit ι, fun τ ↦ ?_⟩
  let P : ∀ ⦃V' : Y.Etale⦄, (V' ⟶ V) → Prop := fun V' φ ↦ ∃ a : K.obj.obj (op V'),
    G.obj.map (etaleRefineHom ι φ).op (η.hom.app (op V') a) =
      G.obj.map (etaleRefineFst U c φ).op τ
  have hP {V' V'' : Y.Etale} (φ : V' ⟶ V) (ψ : V'' ⟶ V') (a : K.obj.obj (op V'))
      (ha : G.obj.map (etaleRefineHom ι φ).op (η.hom.app (op V') a) =
        G.obj.map (etaleRefineFst U c φ).op τ) :
      G.obj.map (etaleRefineHom ι (ψ ≫ φ)).op (η.hom.app (op V'') (K.obj.map ψ.op a)) =
        G.obj.map (etaleRefineFst U c (ψ ≫ φ)).op τ := by
    rw [map_etaleAdjunction_unit_comp ψ _ _ _ (etaleRefineHom_comp ι φ ψ), ha,
      ← Functor.map_comp_apply, ← op_comp, etaleRefineMap_fst]
  let R : Sieve V :=
    { arrows := P
      downward_closed := by
        rintro V₁ V₂ φ ⟨a, ha⟩ ψ
        exact ⟨_, hP φ ψ a ha⟩ }
  have hR : R ∈ Y.smallEtaleTopology V := by
    rw [mem_smallEtaleTopology_iff]
    intro v
    obtain ⟨V', φ, v', a, hv, ha⟩ := exists_map_etaleAdjunction_unit_eq K ι τ v
    exact ⟨V', φ, v', ⟨a, ha⟩, hv⟩
  let x : Presieve.FamilyOfElements K.obj (R : Presieve V) := fun V' φ hφ ↦
    Classical.choose (hφ : P φ)
  have hx {V' : Y.Etale} (φ : V' ⟶ V) (hφ : R φ) :
      G.obj.map (etaleRefineHom ι φ).op (η.hom.app (op V') (x φ hφ)) =
        G.obj.map (etaleRefineFst U c φ).op τ :=
    Classical.choose_spec (hφ : P φ)
  have hcompat : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V₁ V₂ φ ψ hφ
    have : Surjective ((etaleRefineHom ι (ψ ≫ φ)).left ≫ pullback.fst V₂.hom g) := by
      rw [etaleRefineHom_left_fst]
      infer_instance
    apply injective_map_etaleAdjunction_unit (etaleRefineHom ι (ψ ≫ φ))
    exact (hx _ _).trans (hP φ ψ _ (hx φ hφ)).symm
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 K.property
  obtain ⟨a, ha, -⟩ := hF R hR x hcompat
  refine ⟨a, eq_of_etaleAgreementLocus_eq_univ (F := G) (W := U) fun z ↦ ?_⟩
  obtain ⟨V', φ, v', b, hv, hb⟩ := exists_map_etaleAdjunction_unit_eq K ι τ (c z)
  obtain ⟨z', hz', -⟩ := Pullback.exists_preimage_pullback (f := c) (g := φ.left) z v' hv.symm
  refine ⟨_, etaleRefineFst U c φ, z', ?_, hz'⟩
  have := map_etaleAdjunction_unit_comp φ (etaleRefineHom ι φ) ι (etaleRefineFst U c φ)
    (etaleRefineHom_fst ι φ) a
  dsimp only at this ⊢
  rw [← this, ha φ ⟨b, hb⟩, hx]

/-- **Stacks 0A3H** (Tag 0A3H): for `p : T ⟶ S` flat, quasi-compact and geometrically connected
(all geometric fibres nonempty and connected), the unit `F ⟶ p_* p^* F` is an isomorphism for every
étale sheaf of sets `F` on `S`; in particular `Γ(S, F) = Γ(T, p^* F)`. -/
theorem isIso_etaleAdjunction_unit_app_of_geometricallyConnected {S : Scheme.{u}} (p : T ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p] (F : Sheaf S.smallEtaleTopology (Type u)) :
    IsIso ((etaleAdjunction p).unit.app F) := by
  let η := (etaleAdjunction p).unit.app F
  have : IsIso η.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [isIso_iff_bijective]
    let ι : (Etale.pullback p).obj V.unop ⟶ (Etale.pullback p).obj V.unop := 𝟙 _
    have hι : ι.left ≫ pullback.fst V.unop.hom p = pullback.fst V.unop.hom p :=
      Category.id_comp _
    have : Flat (ι.left ≫ pullback.fst V.unop.hom p) := by rw [hι]; infer_instance
    have : QuasiCompact (ι.left ≫ pullback.fst V.unop.hom p) := by rw [hι]; infer_instance
    have : GeometricallyConnected (ι.left ≫ pullback.fst V.unop.hom p) := by
      rw [hι]; infer_instance
    have h := bijective_map_etaleAdjunction_unit F ι
    simp only [ι, op_id, Functor.map_id_apply] at h
    exact h
  have : IsIso ((sheafToPresheaf _ _).map η) := this
  exact isIso_of_reflects_iso η (sheafToPresheaf _ _)

end Main

/-- **Stacks 0A3H**, global sections: for `p : T ⟶ S` flat, quasi-compact and geometrically
connected, `Γ(S, F) → Γ(T, p^* F)` is bijective for every étale sheaf of sets `F` on `S`. -/
theorem bijective_sections_etalePullback_of_geometricallyConnected {T S : Scheme.{u}} (p : T ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p] (F : Sheaf S.smallEtaleTopology (Type u)) :
    Function.Bijective (fun s : F.obj.obj (op (Etale.top S)) ↦
      ((etalePullback p).obj F).obj.map (Etale.pullbackTopIso p).inv.op
        (((etaleAdjunction p).unit.app F).hom.app (op (Etale.top S)) s)) := by
  have := isIso_etaleAdjunction_unit_app_of_geometricallyConnected p F
  have h₁ : Function.Bijective (((etaleAdjunction p).unit.app F).hom.app (op (Etale.top S))) :=
    (isIso_iff_bijective _).1 inferInstance
  have h₂ : Function.Bijective
      (((etalePullback p).obj F).obj.map (Etale.pullbackTopIso p).inv.op) :=
    (isIso_iff_bijective _).1 inferInstance
  exact h₂.comp h₁



section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- For a cartesian square `X' = X ×_Y Y'` and `ι : U ⟶ Y' ×_Y V`, the morphism
`X' ×_{Y'} U ⟶ X ×_Y V` is the base change of `U ⟶ V` along `X ×_Y V ⟶ V`. -/
lemma isPullback_baseChangeComparison_left (hsq : IsPullback h f' f g) {V : Y.Etale}
    {U : Y'.Etale} (ι : U ⟶ (Etale.pullback g).obj V) :
    IsPullback (((Etale.pullback f').map ι ≫ (Etale.baseChangeComparison hsq.w).app V).left ≫
        pullback.fst ((Etale.pullback f).obj V).hom h)
      (pullback.fst U.hom f') (pullback.fst V.hom f) (ι.left ≫ pullback.fst V.hom g) := by
  have e₁ : (((Etale.pullback f').map ι ≫ (Etale.baseChangeComparison hsq.w).app V).left ≫
      pullback.fst ((Etale.pullback f).obj V).hom h) ≫ pullback.snd V.hom f =
        pullback.snd U.hom f' ≫ h := by
    rw [MorphismProperty.Comma.comp_left, Etale.baseChangeComparison_app_left, Category.assoc,
      Category.assoc, Etale.baseChangeComparisonHom_fst_snd', Etale.pullback_map_left_snd_assoc]
  have e₂ : (((Etale.pullback f').map ι ≫ (Etale.baseChangeComparison hsq.w).app V).left ≫
      pullback.fst ((Etale.pullback f).obj V).hom h) ≫ pullback.fst V.hom f =
        pullback.fst U.hom f' ≫ ι.left ≫ pullback.fst V.hom g := by
    rw [MorphismProperty.Comma.comp_left, Etale.baseChangeComparison_app_left, Category.assoc,
      Category.assoc, Etale.baseChangeComparisonHom_fst_fst', Etale.pullback_map_left_fst_assoc]
  have e₃ : (ι.left ≫ pullback.fst V.hom g) ≫ V.hom = U.hom ≫ g := by
    rw [Category.assoc, pullback.condition, ← MorphismProperty.Over.w_assoc ι]
    rfl
  refine IsPullback.of_right ?_ e₂ (IsPullback.of_hasPullback V.hom f).flip
  rw [e₁, e₃]
  exact (IsPullback.of_hasPullback U.hom f').flip.paste_horiz hsq

/-- The base change morphism `g^* f_* F ⟶ f'_* h^* F` is bijective on sections over an étale
`Y'`-scheme `U` with a morphism `ι : U ⟶ Y' ×_Y V` (`V` étale over `Y`) such that `U ⟶ V` is
flat, quasi-compact and geometrically connected: both sides are `F(X ×_Y V)` by Stacks 0A3H
(`Scheme.bijective_map_etaleAdjunction_unit`, applied to `g` and to `h`). -/
lemma bijective_etaleBaseChangeMap_app (hsq : IsPullback h f' f g)
    (F : Sheaf X.smallEtaleTopology (Type u)) {V : Y.Etale} {U : Y'.Etale}
    (ι : U ⟶ (Etale.pullback g).obj V) [Flat (ι.left ≫ pullback.fst V.hom g)]
    [QuasiCompact (ι.left ≫ pullback.fst V.hom g)]
    [GeometricallyConnected (ι.left ≫ pullback.fst V.hom g)] :
    Function.Bijective (((etaleBaseChangeMap hsq.w).app F).hom.app (op U)) := by
  let ψ := (Etale.pullback f').map ι ≫ (Etale.baseChangeComparison hsq.w).app V
  have hpb := (isPullback_baseChangeComparison_left hsq ι).flip
  have : Flat (ψ.left ≫ pullback.fst ((Etale.pullback f).obj V).hom h) :=
    MorphismProperty.of_isPullback hpb ‹_›
  have : QuasiCompact (ψ.left ≫ pullback.fst ((Etale.pullback f).obj V).hom h) :=
    MorphismProperty.of_isPullback hpb ‹_›
  have : GeometricallyConnected (ψ.left ≫ pullback.fst ((Etale.pullback f).obj V).hom h) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb ‹_›
  have h₁ := bijective_map_etaleAdjunction_unit ((etalePushforward f).obj F) ι
  have h₂ := bijective_map_etaleAdjunction_unit F ψ
  have hc : (⇑(((etaleBaseChangeMap hsq.w).app F).hom.app (op U)) ∘
      fun s : ((etalePushforward f).obj F).obj.obj (op V) ↦
        ((etalePullback g).obj ((etalePushforward f).obj F)).obj.map ι.op
          (((etaleAdjunction g).unit.app ((etalePushforward f).obj F)).hom.app (op V) s)) =
      fun s : F.obj.obj (op ((Etale.pullback f).obj V)) ↦
        ((etalePullback h).obj F).obj.map ψ.op
          (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) s) := by
    funext s
    rw [Function.comp_apply]
    erw [NatTrans.naturality_apply ((etaleBaseChangeMap hsq.w).app F).hom ι.op]
    erw [etaleBaseChangeMap_app_unit]
    change ((etalePullback h).obj F).obj.map ((Etale.pullback f').map ι).op
      (((etalePullback h).obj F).obj.map ((Etale.baseChangeComparison hsq.w).app V).op _) = _
    erw [← Functor.map_comp_apply]
    rfl
  rw [← Function.Bijective.of_comp_iff _ h₁, hc]
  exact h₂

/-- **Stacks 0EZX** (Lemma 59.87.1): for a cartesian square `X' = X ×_Y Y'`, suppose that every
point of every étale `Y'`-scheme lies in the image of an étale `Y'`-scheme `U` with a morphism
`ι : U ⟶ Y' ×_Y V` to the base change of an étale `Y`-scheme `V` such that `U ⟶ V` is flat,
quasi-compact and geometrically connected. Then the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is an isomorphism for every étale sheaf of sets `F` on `X`.

Stacks only asks `g` to be flat and `U ⟶ V` to be quasi-compact with geometrically connected
fibres; here `U ⟶ V` is asked to be flat (which follows from the flatness of `g` since `V ⟶ Y`
is étale). -/
theorem isIso_etaleBaseChangeMap_of_forall_exists (hsq : IsPullback h f' f g)
    (hg : ∀ (W : Y'.Etale) (w : W.left), ∃ (U : Y'.Etale) (ρ : U ⟶ W) (u : U.left)
      (V : Y.Etale) (ι : U ⟶ (Etale.pullback g).obj V), ρ.left u = w ∧
        Flat (ι.left ≫ pullback.fst V.hom g) ∧ QuasiCompact (ι.left ≫ pullback.fst V.hom g) ∧
        GeometricallyConnected (ι.left ≫ pullback.fst V.hom g))
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap hsq.w).app F) := by
  let β := (etaleBaseChangeMap hsq.w).app F
  have hβ {U : Y'.Etale} {V : Y.Etale} (ι : U ⟶ (Etale.pullback g).obj V)
      (h₁ : Flat (ι.left ≫ pullback.fst V.hom g))
      (h₂ : QuasiCompact (ι.left ≫ pullback.fst V.hom g))
      (h₃ : GeometricallyConnected (ι.left ≫ pullback.fst V.hom g)) :
      Function.Bijective (β.hom.app (op U)) :=
    bijective_etaleBaseChangeMap_app hsq F ι
  have : Presheaf.IsLocallyInjective Y'.smallEtaleTopology β.hom := by
    constructor
    intro W a b hab
    rw [mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨U, ρ, u, V, ι, hu, h₁, h₂, h₃⟩ := hg W.unop w
    refine ⟨U, ρ, u, (hβ ι h₁ h₂ h₃).1 ?_, hu⟩
    rw [NatTrans.naturality_apply β.hom ρ.op, NatTrans.naturality_apply β.hom ρ.op, hab]
  have : Presheaf.IsLocallySurjective Y'.smallEtaleTopology β.hom := by
    constructor
    intro W s
    rw [mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨U, ρ, u, V, ι, hu, h₁, h₂, h₃⟩ := hg W w
    exact ⟨U, ρ, u, (hβ ι h₁ h₂ h₃).2 _, hu⟩
  exact (Sheaf.isLocallyBijective_iff_isIso β).1 ⟨inferInstance, inferInstance⟩

end BaseChange

end AlgebraicGeometry.Scheme
