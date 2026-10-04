/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalkProper
import SGA.Foundations.Etale.Representable

/-!
# Base change for sheaves represented by étale schemes

Let `f : X ⟶ Y` be universally closed and `E` an étale `X`-scheme, with represented sheaf
`h_E : W ↦ Hom_X(W, E)`. We reduce the bijectivity of the base change morphism
`g^* f_* h_E ⟶ f'_* h^* h_E` (for every cartesian square) to a statement about the geometric fibres
of `f`: every `X`-morphism `X_ȳ = X ×_Y Spec Ω ⟶ E`, `Ω` algebraically closed, extends to
`X ×_Y V ⟶ E` for an étale neighbourhood `(V, v)` of `ȳ`
(`AlgebraicGeometry.Scheme.ExtendsAlongGeometricFibres`,
`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_etaleYoneda_of_extendsAlongGeometricFibres`).

Injectivity is `AlgebraicGeometry.Scheme.mono_etaleBaseChangeMap_of_universallyClosed`. For
surjectivity at a geometric point `ȳ'` of `Y'`, a section of `f'_* h^* h_E` near `ȳ'` is an
`X`-morphism `X' ×_{Y'} V' ⟶ E`; its restriction to the geometric fibre
`X'_{ȳ'} = X ×_Y Spec Ω` extends to some `X ×_Y V ⟶ E`, and the two sections agree on the open
subscheme where they agree as morphisms (`range_subset_etaleAgreementLocus_etaleYoneda`, the
diagonal of `E ⟶ X` being an open immersion), which contains the fibre over `ȳ'`; we conclude
with `toPresheafFiber_etalePushforward_eq_of_universallyClosed` for `f'`. The identification
`h^* h_E ≅ h_{X' ×_X E}` is made explicit on sections coming from `X`
(`AlgebraicGeometry.Scheme.etalePullbackYonedaIso_hom_unit`).

## References

* [SGA 4, Exposé XII, 5.1][sga4]
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
-/

universe v u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} [J.Subcanonical] [K.Subcanonical] {u : C ⥤ D}
  [u.IsContinuous J K] {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}

lemma yonedaObjLeftAdjointIso_hom
    (adj : L ⊣ u.sheafPushforwardContinuous (Type v) J K) (c : C) :
    (yonedaObjLeftAdjointIso adj c).hom =
      (adj.homEquiv _ _).symm (J.yonedaEquiv.symm (K.yonedaEquiv (𝟙 _))) :=
  rfl

/-- The isomorphism `L (yoneda c) ≅ yoneda (u c)` sends the image of `s : U ⟶ c` under the unit
of the adjunction to `u s : u U ⟶ u c`. -/
lemma yonedaObjLeftAdjointIso_hom_unit
    (adj : L ⊣ u.sheafPushforwardContinuous (Type v) J K) (c U : C) (s : U ⟶ c) :
    (yonedaObjLeftAdjointIso adj c).hom.hom.app (op (u.obj U))
      ((adj.unit.app (J.yoneda.obj c)).hom.app (op U) s) = u.map s := by
  have h := adj.homEquiv_unit (J.yoneda.obj c) (K.yoneda.obj (u.obj c))
    (yonedaObjLeftAdjointIso adj c).hom
  rw [yonedaObjLeftAdjointIso_hom adj c, Equiv.apply_symm_apply] at h
  have := congrArg (fun φ ↦ φ.hom.app (op U) s) h
  simp only at this
  rw [← yonedaObjLeftAdjointIso_hom adj c] at this
  refine this.symm.trans ?_
  erw [yonedaEquiv_symm_app_apply]
  change (K.yoneda.obj (u.obj c)).obj.map (u.map s).op (K.yonedaEquiv (𝟙 _)) = u.map s
  rw [yonedaEquiv_apply]
  simp

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Scheme

section Representable

variable {X X' : Scheme.{u}}

/-- The identification `h^* h_E ≅ h_{X' ×_X E}` sends the image of an `X`-morphism `s : W ⟶ E`
to its base change `X' ×_X W ⟶ X' ×_X E`. -/
lemma etalePullbackYonedaIso_hom_unit (h : X' ⟶ X) (E W : X.Etale) (s : W ⟶ E) :
    (etalePullbackYonedaIso h E).hom.hom.app (op ((Etale.pullback h).obj W))
      (((etaleAdjunction h).unit.app ((etaleYoneda X).obj E)).hom.app (op W) s) =
        (Etale.pullback h).map s :=
  GrothendieckTopology.yonedaObjLeftAdjointIso_hom_unit (etaleAdjunction h) E W s

/-- The agreement locus does not change under an isomorphism of sheaves. -/
lemma etaleAgreementLocus_iso {F G : Sheaf X.smallEtaleTopology (Type u)} (φ : F ≅ G)
    {W : X.Etale} (s t : F.obj.obj (op W)) :
    etaleAgreementLocus G (φ.hom.hom.app _ s) (φ.hom.hom.app _ t) =
      etaleAgreementLocus F s t := by
  have hinj (V : X.Etale) : Function.Injective (φ.hom.hom.app (op V)) := by
    have e (a : F.obj.obj (op V)) : φ.inv.hom.app (op V) (φ.hom.hom.app (op V) a) = a := by
      exact congrArg (fun ψ ↦ ψ.hom.app (op V) a) φ.hom_inv_id
    intro a b hab
    rw [← e a, ← e b, hab]
  ext w
  constructor
  · rintro ⟨V, g, v, hst, rfl⟩
    refine ⟨V, g, v, hinj V ?_, rfl⟩
    rw [NatTrans.naturality_apply φ.hom.hom, NatTrans.naturality_apply φ.hom.hom]
    exact hst
  · rintro ⟨V, g, v, hst, rfl⟩
    refine ⟨V, g, v, ?_, rfl⟩
    rw [← NatTrans.naturality_apply φ.hom.hom, ← NatTrans.naturality_apply φ.hom.hom, hst]

/-- Two `X`-morphisms `a b : W ⟶ E` into an étale `X`-scheme, seen as sections of the represented
sheaf, agree near every point at which they agree as morphisms: if `z ≫ a = z ≫ b` for
`z : Z ⟶ W`, the image of `z` lies in the agreement locus of `a` and `b`. (The diagonal of
`E ⟶ X` is an open immersion.) -/
lemma range_subset_etaleAgreementLocus_etaleYoneda (E : X.Etale) {W : X.Etale} (a b : W ⟶ E)
    {Z : Scheme.{u}} (z : Z ⟶ W.left) (h : z ≫ a.left = z ≫ b.left) :
    Set.range z ⊆ etaleAgreementLocus ((etaleYoneda X).obj E) a b := by
  have hab : a.left ≫ E.hom = b.left ≫ E.hom := by
    rw [MorphismProperty.Over.w a, MorphismProperty.Over.w b]
  let d := pullback.lift a.left b.left hab
  let U : W.left.Opens := ⟨d ⁻¹' Set.range (pullback.diagonal E.hom),
    (pullback.diagonal E.hom).isOpenEmbedding.isOpen_range.preimage d.continuous⟩
  have hU : Set.range (U.ι ≫ d) ⊆ Set.range (pullback.diagonal E.hom) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  let l := IsOpenImmersion.lift (pullback.diagonal E.hom) (U.ι ≫ d) hU
  have hl : l ≫ pullback.diagonal E.hom = U.ι ≫ d := IsOpenImmersion.lift_fac _ _ _
  have hUab : U.ι ≫ a.left = U.ι ≫ b.left := by
    have h₁ := congrArg (· ≫ pullback.fst E.hom E.hom) hl
    have h₂ := congrArg (· ≫ pullback.snd E.hom E.hom) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      d, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
    rw [← h₁, h₂]
  let V : X.Etale := Etale.mk (U.ι ≫ W.hom)
  let ι : V ⟶ W := MorphismProperty.Over.homMk U.ι rfl trivial
  rintro _ ⟨p, rfl⟩
  have hp : z p ∈ U := by
    change d (z p) ∈ Set.range (pullback.diagonal E.hom)
    refine ⟨(z ≫ a.left) p, ?_⟩
    have e : (z ≫ a.left) ≫ pullback.diagonal E.hom = z ≫ d := by
      apply pullback.hom_ext <;> simp [d, h]
    have := congrArg (fun φ ↦ φ p) e
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  refine ⟨V, ι, ⟨z p, hp⟩, ?_, rfl⟩
  change ι ≫ a = ι ≫ b
  exact MorphismProperty.Over.Hom.ext hUab

end Representable

section GeometricFibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

/-- The morphism from the geometric fibre `X_ȳ = X ×_Y Spec Ω` to `X ×_Y V` given by a point `v`
over `ȳ` of an étale `Y`-scheme `V`. -/
def Hom.geometricFibreToPullback {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) :
    pullback f y ⟶ ((Etale.pullback f).obj V).left :=
  pullback.lift (pullback.snd f y ≫ v.left) (pullback.fst f y) (by
    have hv : v.left ≫ V.hom = y := Over.w v
    rw [Category.assoc, hv, pullback.condition])

@[reassoc (attr := simp)]
lemma Hom.geometricFibreToPullback_fst {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) :
    f.geometricFibreToPullback v ≫ pullback.fst V.hom f = pullback.snd f y ≫ v.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma Hom.geometricFibreToPullback_snd {V : Y.Etale} (v : (pointSmallEtale y).fiber.obj V) :
    f.geometricFibreToPullback v ≫ pullback.snd V.hom f = pullback.fst f y :=
  pullback.lift_snd _ _ _

/-- The geometric fibre `X_ȳ` is the fibre of `X ×_Y V ⟶ V` at the point `v` over `ȳ`. -/
lemma Hom.isPullback_geometricFibreToPullback {V : Y.Etale}
    (v : (pointSmallEtale y).fiber.obj V) :
    IsPullback (f.geometricFibreToPullback v) (pullback.snd f y) (pullback.fst V.hom f)
      v.left := by
  have hv : v.left ≫ V.hom = y := Over.w v
  refine IsPullback.of_right ?_ (f.geometricFibreToPullback_fst v)
    (IsPullback.of_hasPullback V.hom f).flip
  rw [f.geometricFibreToPullback_snd v, hv]
  exact IsPullback.of_hasPullback f y

end GeometricFibre

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- Sections of an étale `X`-scheme `E` over the geometric fibres of `f : X ⟶ Y` extend to étale
neighbourhoods: every `X`-morphism `X_ȳ = X ×_Y Spec Ω ⟶ E`, for a geometric point
`ȳ : Spec Ω ⟶ Y` with `Ω` algebraically closed, is the restriction of an `X`-morphism
`X ×_Y V ⟶ E` for some étale neighbourhood `(V, v)` of `ȳ`. (This is the surjectivity of the
map `(f_* h_E)_ȳ ⟶ Γ(X_ȳ, h_E)`, Stacks 0A3T, for the sheaf `h_E` represented by `E`.) -/
def ExtendsAlongGeometricFibres (f : X ⟶ Y) (E : X.Etale) : Prop :=
  ∀ ⦃Ω : Type u⦄ [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (τ : pullback f y ⟶ E.left),
    τ ≫ E.hom = pullback.fst f y → ∃ (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
      (s : (Etale.pullback f).obj V ⟶ E), f.geometricFibreToPullback v ≫ s.left = τ

/-- The comparison `X'_{ȳ'} = X' ×_{Y'} Spec Ω ⟶ X ×_Y Spec Ω = X_{g ȳ'}` of geometric fibres. -/
def geometricFibreBaseChange (hsq : IsPullback h f' f g) {Ω : Type u} [Field Ω]
    (y : Spec (.of Ω) ⟶ Y') : pullback f' y ⟶ pullback f (y ≫ g) :=
  pullback.lift (pullback.fst f' y ≫ h) (pullback.snd f' y) (by
    rw [Category.assoc, hsq.w, pullback.condition_assoc])

/-- The inverse of `geometricFibreBaseChange`. -/
def geometricFibreBaseChangeInv (hsq : IsPullback h f' f g) {Ω : Type u} [Field Ω]
    (y : Spec (.of Ω) ⟶ Y') : pullback f (y ≫ g) ⟶ pullback f' y :=
  pullback.lift (hsq.lift (pullback.fst f (y ≫ g)) (pullback.snd f (y ≫ g) ≫ y)
    (by rw [pullback.condition, Category.assoc])) (pullback.snd f (y ≫ g)) (by simp)

lemma geometricFibreBaseChange_inv (hsq : IsPullback h f' f g) {Ω : Type u} [Field Ω]
    (y : Spec (.of Ω) ⟶ Y') :
    geometricFibreBaseChange hsq y ≫ geometricFibreBaseChangeInv hsq y = 𝟙 _ := by
  apply pullback.hom_ext
  · apply hsq.hom_ext
    · simp [geometricFibreBaseChange, geometricFibreBaseChangeInv]
    · simp [geometricFibreBaseChange, geometricFibreBaseChangeInv, pullback.condition]
  · simp [geometricFibreBaseChange, geometricFibreBaseChangeInv]

/-- **Base change for represented sheaves, surjectivity on stalks**: for a cartesian square with
`f` universally closed and an étale `X`-scheme `E` whose sections over the geometric fibres of `f`
extend to étale neighbourhoods, the base change morphism `g^* f_* h_E ⟶ f'_* h^* h_E` is surjective
on the stalk at every geometric point `ȳ'` of `Y'` with algebraically closed residue field. -/
theorem surjective_sheafFiber_etaleBaseChangeMap_etaleYoneda [UniversallyClosed f]
    (hsq : IsPullback h f' f g) (E : X.Etale) (hE : ExtendsAlongGeometricFibres f E)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y') :
    Function.Surjective ((pointSmallEtale y).sheafFiber.map
      ((etaleBaseChangeMap hsq.w).app ((etaleYoneda X).obj E))) := by
  let F := (etaleYoneda X).obj E
  let Φ := pointSmallEtale y
  let e₁ := (sheafFiberEtalePullbackIso g y).app ((etalePushforward f).obj F)
  let P := ((etalePushforward f').obj ((etalePullback h).obj F)).obj
  have key (V : Y.Etale) (v : (pointSmallEtale (y ≫ g)).fiber.obj V)
      (σ : F.obj.obj (op ((Etale.pullback f).obj V))) :
      Φ.sheafFiber.map ((etaleBaseChangeMap hsq.w).app F)
        (e₁.hom ((pointSmallEtale (y ≫ g)).toPresheafFiber V v
          ((etalePushforward f).obj F).obj σ)) =
      Φ.toPresheafFiber ((Etale.pullback g).obj V) ((pointSmallEtaleFiberHom g y).app V v) P
        (((etalePullback h).obj F).obj.map ((Etale.baseChangeComparison hsq.w).app V).op
          (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) σ)) := by
    simp only [e₁, Iso.app_hom]
    rw [sheafFiberEtalePullbackIso_hom_app_toPresheafFiber]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    erw [etaleBaseChangeMap_app_unit]
    rfl
  intro b
  obtain ⟨V', v', σ, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) b
  let ι := etalePullbackYonedaIso h E
  let σ' : (Etale.pullback f').obj V' ⟶ (Etale.pullback h).obj E := ι.hom.hom.app _ σ
  let τ' := f'.geometricFibreToPullback v' ≫ σ'.left ≫ pullback.fst E.hom h
  let τ := geometricFibreBaseChangeInv hsq y ≫ τ'
  have hτ : τ ≫ E.hom = pullback.fst f (y ≫ g) := by
    have h₁ : σ'.left ≫ pullback.snd E.hom h = pullback.snd V'.hom f' :=
      MorphismProperty.Over.w σ'
    simp only [τ, τ', Category.assoc, pullback.condition, reassoc_of% h₁,
      Hom.geometricFibreToPullback_snd_assoc]
    simp [geometricFibreBaseChangeInv]
  obtain ⟨V, v, s, hs⟩ := hE (y ≫ g) τ hτ
  refine ⟨e₁.hom ((pointSmallEtale (y ≫ g)).toPresheafFiber V v
    ((etalePushforward f).obj F).obj s), ?_⟩
  rw [key]
  obtain ⟨⟨V'', v''⟩, ⟨φ₁, hφ₁⟩, ⟨φ₂, hφ₂⟩, -⟩ :=
    IsCofilteredOrEmpty.cone_objs (C := Φ.fiber.Elements)
    ⟨(Etale.pullback g).obj V, (pointSmallEtaleFiberHom g y).app V v⟩ ⟨V', v'⟩
  dsimp only at φ₁ φ₂ hφ₁ hφ₂
  let σ₁ := ((etalePullback h).obj F).obj.map ((Etale.baseChangeComparison hsq.w).app V).op
    (((etaleAdjunction h).unit.app F).hom.app (op ((Etale.pullback f).obj V)) s)
  have e₁' := Φ.toPresheafFiber_w_apply φ₁ v'' P σ₁
  have e₂' := Φ.toPresheafFiber_w_apply φ₂ v'' P σ
  rw [hφ₁] at e₁'
  rw [hφ₂] at e₂'
  rw [← e₁', ← e₂']
  have : UniversallyClosed f' := MorphismProperty.of_isPullback hsq inferInstance
  refine toPresheafFiber_etalePushforward_eq_of_universallyClosed f' v'' fun x p₀ hx ↦ ?_
  obtain ⟨z, rfl, -⟩ :=
    exists_preimage_of_isPullback (f'.isPullback_geometricFibreToPullback v'') x p₀ hx
  rw [← etaleAgreementLocus_iso ι]
  have ha : ι.hom.hom.app _ (P.map φ₁.op σ₁) = ((Etale.pullback f').map φ₁ ≫
      (Etale.baseChangeComparison hsq.w).app V) ≫ (Etale.pullback h).map s := by
    change ι.hom.hom.app _ (((etalePullback h).obj F).obj.map
      ((Etale.pullback f').map φ₁).op σ₁) = _
    rw [NatTrans.naturality_apply ι.hom.hom]
    simp only [σ₁]
    erw [NatTrans.naturality_apply ι.hom.hom]
    have hu := etalePullbackYonedaIso_hom_unit h E _ s
    simp only [ι, F] at hu ⊢
    erw [hu]
    rfl
  have hb : ι.hom.hom.app _ (P.map φ₂.op σ) = (Etale.pullback f').map φ₂ ≫ σ' := by
    change ι.hom.hom.app _ (((etalePullback h).obj F).obj.map
      ((Etale.pullback f').map φ₂).op σ) = _
    rw [NatTrans.naturality_apply ι.hom.hom]
    rfl
  have hmem := range_subset_etaleAgreementLocus_etaleYoneda _
    (((Etale.pullback f').map φ₁ ≫ (Etale.baseChangeComparison hsq.w).app V) ≫
      (Etale.pullback h).map s) ((Etale.pullback f').map φ₂ ≫ σ')
    (f'.geometricFibreToPullback v'') ?_ ⟨z, rfl⟩
  · convert hmem using 2
    · exact ha
    · exact hb
  have hsnd (α : (Etale.pullback f').obj V'' ⟶ (Etale.pullback h).obj E) :
      α.left ≫ pullback.snd E.hom h = pullback.snd V''.hom f' :=
    MorphismProperty.Over.w α
  have hv₁ : v''.left ≫ φ₁.left ≫ pullback.fst V.hom g = v.left := by
    have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom g) hφ₁
    simp only at this
    rw [← Category.assoc]
    refine this.trans ?_
    exact pullback.lift_fst _ _ _
  have hv₂ : v''.left ≫ φ₂.left = v'.left := congrArg (fun a ↦ a.left) hφ₂
  have h₁ : f'.geometricFibreToPullback v'' ≫ ((Etale.pullback f').map φ₁).left ≫
      ((Etale.baseChangeComparison hsq.w).app V).left ≫
        pullback.fst ((Etale.pullback f).obj V).hom h =
      geometricFibreBaseChange hsq y ≫ f.geometricFibreToPullback v := by
    apply pullback.hom_ext
    · simp [geometricFibreBaseChange, hv₁]
    · simp [geometricFibreBaseChange]
  have h₂ : f'.geometricFibreToPullback v'' ≫ ((Etale.pullback f').map φ₂).left =
      f'.geometricFibreToPullback v' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Etale.pullback_map_left_fst,
        Hom.geometricFibreToPullback_fst_assoc, Hom.geometricFibreToPullback_fst]
      exact congrArg (pullback.snd f' y ≫ ·) hv₂
    · simp
  have h₃ : geometricFibreBaseChange hsq y ≫ f.geometricFibreToPullback v ≫ s.left = τ' := by
    rw [hs, ← Category.assoc, geometricFibreBaseChange_inv, Category.id_comp]
  apply pullback.hom_ext
  · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      MorphismProperty.Comma.comp_left]
    simp only [Category.assoc]
    rw [Etale.pullback_map_left_fst h s, reassoc_of% h₁, h₃, reassoc_of% h₂]
  · simp only [Category.assoc]
    exact (congrArg (f'.geometricFibreToPullback v'' ≫ ·) (hsnd _)).trans
      (congrArg (f'.geometricFibreToPullback v'' ≫ ·)
        (hsnd ((Etale.pullback f').map φ₂ ≫ σ'))).symm

/-- **Base change for represented sheaves**: for a cartesian square with `f` universally closed
and an étale `X`-scheme `E` whose sections over the geometric fibres of `f` extend to étale
neighbourhoods (`ExtendsAlongGeometricFibres`), the base change morphism
`g^* f_* h_E ⟶ f'_* h^* h_E` is an isomorphism. -/
theorem isIso_etaleBaseChangeMap_etaleYoneda_of_extendsAlongGeometricFibres [UniversallyClosed f]
    (hsq : IsPullback h f' f g) (E : X.Etale) (hE : ExtendsAlongGeometricFibres f E) :
    IsIso ((etaleBaseChangeMap hsq.w).app ((etaleYoneda X).obj E)) := by
  have hcons := isConservative_pointSmallEtale (fun y : Y' ↦ Y'.fromSpecAlgClosure y) (by
    refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨y, _, Y'.fromSpecAlgClosure_apply y⟩)
  rw [hcons.jointlyReflectIsomorphisms_type.isIso_iff]
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨y, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΨ
  rw [isIso_iff_bijective]
  exact ⟨injective_sheafFiber_etaleBaseChangeMap_of_universallyClosed hsq _ _,
    surjective_sheafFiber_etaleBaseChangeMap_etaleYoneda hsq E hE _⟩

end BaseChange

end AlgebraicGeometry.Scheme
