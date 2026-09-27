/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import SGA.SGA1.ExposeV.GaloisCategories

/-!
# SGA 1, Exposé V, §6: exact functors from one Galois category into another

Let `H : C ⥤ C'` be a functor between Galois categories and `F'` a fibre functor on `C'`.
V.6.1 says that `H` is exact iff `F = F' ∘ H` is a fibre functor. An exact `H` then induces a
continuous homomorphism `u : π_{F'} = Aut F' → π_F = Aut F` (`autWhiskerLeft`), and conversely
every continuous homomorphism comes from an exact functor (V.6.2, `functorOfHom`). V.6.3: exact
functors are the functors of fundamental groupoids with continuous induced homomorphisms
(`transposeFunctorFunctorLift`). The properties of `H` are read off from `u`:

* V.6.4, V.6.5: the image of `u` and sections, completely decomposed objects;
* V.6.6–V.6.8: the kernel of `u`, and the criterion for `u` to be injective;
* V.6.9, V.6.10: `u` is surjective iff `H` preserves connectedness iff `H` is fully faithful;
  `u` is an isomorphism iff `H` is an equivalence;
* V.6.11: exactness of a sequence of fundamental groups;
* V.6, after V.6.3: the extension `proMap` of `H` to pro-objects and the homomorphism of
  fundamental pro-groups `Π' ⟶ H(Π)` (`fundamentalProGroupHom`), which is `u` on fibres, with
  their transitivity for composite functors (`proMapCompIso`, `autContinuousHomConj_comp`).

Throughout, "`H` exact" is encoded as `[FiberFunctor (H ⋙ F')]`, which is equivalent by V.6.1.
V.6.13 (slice categories) is in `SGA.SGA1.ExposeV.OverCategories`. Remark V.6.12 is not
formalized: its second claim seems false as stated (for `A₃ ⊂ S₃` every `A₃`-set is the
restriction of an `S₃`-set, but `A₃` is not a direct factor of `S₃`).
-/

universe u₁ u₂ v₁ v₂ v₃ v₄ w

namespace SGA.SGA1.ExposeV

open CategoryTheory Limits PreGaloisCategory Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
  {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']

/-! ### V.6.1: exact functors -/

section Exact

variable (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

include F' in
/-- In a Galois category an object is not initial iff its morphism to the final object is an
epimorphism. -/
lemma not_initial_iff_epi_terminal_from (X : C') :
    (IsInitial X → False) ↔ Epi (terminal.from X) := by
  rw [epi_iff_surjective_map F', not_initial_iff_fiber_nonempty F']
  have := subsingleton_obj_terminal F'
  obtain ⟨p⟩ := nonempty_obj_terminal F'
  exact ⟨fun ⟨x⟩ y ↦ ⟨x, Subsingleton.elim _ _⟩, fun h ↦ ⟨(h p).choose⟩⟩

/-- V.6.1: for a functor `H` between Galois categories and a fibre functor `F'` on the target,
the following are equivalent: (i) `H` is exact; (ii) `H` is left exact and commutes with finite
sums and epimorphisms; (ii') `H` is left exact, commutes with finite sums and transforms
non-initial objects into non-initial objects; (iii) `F' ∘ H` is a fibre functor. -/
theorem exact_tfae : List.TFAE
    [PreservesFiniteLimits H ∧ PreservesFiniteColimits H,
      PreservesFiniteLimits H ∧ PreservesFiniteCoproducts H ∧ H.PreservesEpimorphisms,
      PreservesFiniteLimits H ∧ PreservesFiniteCoproducts H ∧
        ∀ X : C, (IsInitial X → False) → IsInitial (H.obj X) → False,
      FiberFunctor (H ⋙ F')] := by
  let F₀ := CategoryTheory.GaloisCategory.getFiberFunctor C
  have := hasFiniteColimits F₀
  have := hasFiniteColimits F'
  tfae_have 1 → 2 := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, inferInstance, inferInstance⟩
  tfae_have 2 → 3 := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, fun X hX hHX ↦ by
    have := (not_initial_iff_epi_terminal_from F₀ X).1 hX
    have hT : IsTerminal (H.obj (⊤_ C)) :=
      IsTerminal.isTerminalObj H (⊤_ C) terminalIsTerminal
    obtain ⟨y⟩ := (nonempty_obj_terminal F').map (F'.map (hT.from (⊤_ C')))
    obtain ⟨x, -⟩ := surjective_on_fiber_of_epi F' (H.map (terminal.from X)) y
    exact ((initial_iff_fiber_empty F' (H.obj X)).1 ⟨hHX⟩).false x⟩
  tfae_have 3 → 4 := fun ⟨h₁, h₂, h₃⟩ ↦ by
    let F := F₀ ⋙ FintypeCat.uSwitch.{u₂, w}
    have : FiberFunctor F := FiberFunctor.comp_right _
    have := comp_preservesFiniteLimits H F'
    obtain ⟨e⟩ := nonempty_iso_of_leftExact (H ⋙ F') F fun X hX ↦
      (not_initial_iff_fiber_nonempty F' (H.obj X)).1 (h₃ X hX)
    exact fiberFunctor_of_natIso e
  tfae_have 4 → 1 := fun _ ↦ by
    have := preservesFiniteColimits F'
    have : ReflectsFiniteColimits F' :=
      @ReflectsFiniteColimits.mk _ _ _ _ F' fun _ _ _ ↦
        reflectsColimitsOfShape_of_reflectsIsomorphisms
    have := preservesFiniteColimits (H ⋙ F')
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves H F',
      preservesFiniteColimits_of_reflects_of_preserves H F'⟩
  tfae_finish

end Exact

/-- V.6.1: an exact functor composed with a fibre functor is a fibre functor. -/
theorem fiberFunctor_comp (H : C ⥤ C') [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F'] : FiberFunctor (H ⋙ F') := by
  have := (exact_tfae H F').out 1 4
  exact this.1 ⟨inferInstance, inferInstance⟩

/-- V.6.1: if `F' ∘ H` is a fibre functor, then `H` is exact. -/
theorem exact_of_fiberFunctor_comp (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
    [FiberFunctor (H ⋙ F')] : PreservesFiniteLimits H ∧ PreservesFiniteColimits H := by
  have := (exact_tfae H F').out 4 1
  exact this.1 inferInstance

/-! ### The homomorphism of fundamental groups induced by an exact functor -/

section AutMap

variable {C'' : Type v₃} [Category.{v₄} C''] (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w})

/-- V.6, after V.6.1: the homomorphism `ᵗH : π_{F'} → π_{F' ∘ H}` induced by `H`, sending an
automorphism `σ` of `F'` to its restriction `σ ∘ H`. -/
def autWhiskerLeft : Aut F' →* Aut (H ⋙ F') :=
  ((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F'

omit [GaloisCategory C] [GaloisCategory C'] in
@[simp]
lemma autWhiskerLeft_hom_app (σ : Aut F') (X : C) :
    (autWhiskerLeft H F' σ).hom.app X = σ.hom.app (H.obj X) :=
  rfl

omit [GaloisCategory C] [GaloisCategory C'] in
lemma autWhiskerLeft_smul (σ : Aut F') {X : C} (x : (H ⋙ F').obj X) :
    autWhiskerLeft H F' σ • x = σ • (show F'.obj (H.obj X) from x) :=
  rfl

omit [GaloisCategory C] [GaloisCategory C'] in
/-- V.6, after V.6.1: the homomorphism `ᵗH : π_{F'} → π_{F' ∘ H}` is continuous. -/
lemma continuous_autWhiskerLeft : Continuous (autWhiskerLeft H F') := by
  rw [(autEmbedding_isClosedEmbedding (H ⋙ F')).isInducing.continuous_iff, continuous_pi_iff]
  intro X
  exact (continuous_apply (H.obj X)).comp (autEmbedding_isClosedEmbedding F').continuous

/-- V.6, after V.6.1: `ᵗH` as a continuous homomorphism. -/
def autContinuousHom : Aut F' →ₜ* Aut (H ⋙ F') :=
  ⟨autWhiskerLeft H F', continuous_autWhiskerLeft H F'⟩

omit [GaloisCategory C] [GaloisCategory C'] in
/-- V.6: transitivity `ᵗ(H' H) = ᵗH ᵗH'` of the induced homomorphisms (an equality, not only
an isomorphism). -/
lemma autWhiskerLeft_comp (H' : C' ⥤ C'') (F'' : C'' ⥤ FintypeCat.{w}) :
    autWhiskerLeft (H ⋙ H') F'' = (autWhiskerLeft H (H' ⋙ F'')).comp (autWhiskerLeft H' F'') :=
  rfl

/-- V.6, after V.6.1: an exact functor `H` induces the functor `ᵗH : Γ' ⥤ Γ`, `F' ↦ F' ∘ H`,
between the fundamental groupoids. -/
def transposeFunctor (H : C ⥤ C') [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (whiskeringLeft C C' FintypeCat.{w}).obj H)
    fun F' ↦ fiberFunctor_comp H F'.obj

/-- V.6, after V.6.1: `ᵗ(H' H) = ᵗH ᵗH'` as an identity of functors. -/
lemma transposeFunctor_comp [GaloisCategory C''] (H : C ⥤ C') (H' : C' ⥤ C'')
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] :
    haveI := comp_preservesFiniteLimits H H'
    haveI := comp_preservesFiniteColimits H H'
    transposeFunctor.{u₁, u₂, v₃, v₄, w} (H ⋙ H') =
      transposeFunctor.{v₁, v₂, v₃, v₄, w} H' ⋙ transposeFunctor.{u₁, u₂, v₁, v₂, w} H :=
  rfl

end AutMap

/-! ### V.6.2: exact functors correspond to continuous homomorphisms -/

section Correspondence

open scoped FintypeCatDiscrete

variable (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w})

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.2: under the equivalences `C ≃ C(π_F)` and `C' ≃ C(π_{F'})` defined by `F = F' ∘ H`
and `F'` (V.4.1), the functor `H` becomes the restriction of operations along `ᵗH`. -/
def functorToContActionCompIso :
    H ⋙ functorToContAction F' ≅
      functorToContAction (H ⋙ F') ⋙ ContAction.res _ (autContinuousHom H F') :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun _ ↦ rfl))
    fun _ ↦ rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.2: a functor between Galois categories is exact iff there are equivalences
`C(π) ≃ C` and `C' ≃ C(π')` transforming it into the restriction functor `C(π) ⥤ C(π')`
along a continuous homomorphism `π' → π`. -/
theorem exact_iff_exists_equivalence :
    (PreservesFiniteLimits H ∧ PreservesFiniteColimits H) ↔
      ∃ (π : Type (max u₁ w)) (π' : Type (max v₁ w)) (_ : Group π) (_ : TopologicalSpace π)
        (_ : IsTopologicalGroup π) (_ : Group π') (_ : TopologicalSpace π')
        (_ : IsTopologicalGroup π') (ρ : π' →ₜ* π) (e : ContAction FintypeCat.{w} π ≌ C)
        (e' : C' ≌ ContAction FintypeCat.{w} π'),
        Nonempty (e.functor ⋙ H ⋙ e'.functor ≅ ContAction.res _ ρ) := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨π, π', _, _, _, _, _, _, ρ, e, e', ⟨i⟩⟩ ↦ ?_⟩
  · let F' := CategoryTheory.GaloisCategory.getFiberFunctor C' ⋙ FintypeCat.uSwitch.{v₂, w}
    have : FiberFunctor F' := FiberFunctor.comp_right _
    have := fiberFunctor_comp H F'
    let E := equivalenceContAction (H ⋙ F')
    refine ⟨Aut (H ⋙ F'), Aut F', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, autContinuousHom H F', E.symm, equivalenceContAction F',
      ⟨?_⟩⟩
    exact isoWhiskerLeft E.inverse (functorToContActionCompIso H F') ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _
  · let G : ContAction FintypeCat.{w} π ⥤ FintypeCat.{w} := ObjectProperty.ι _ ⋙ Action.forget _ _
    let G' : ContAction FintypeCat.{w} π' ⥤ FintypeCat.{w} :=
      ObjectProperty.ι _ ⋙ Action.forget _ _
    have := fiberFunctor_comp_equivalence e' G'
    have : FiberFunctor (e.inverse ⋙ G) := fiberFunctor_comp_equivalence e.symm G
    have j : e.inverse ⋙ G ≅ H ⋙ e'.functor ⋙ G' :=
      isoWhiskerLeft e.inverse (isoWhiskerRight i.symm G') ≪≫
        (isoWhiskerRight e.counitIso (H ⋙ e'.functor ⋙ G'))
    have := fiberFunctor_of_natIso j
    exact exact_of_fiberFunctor_comp H (e'.functor ⋙ G')

end Correspondence

section Converse

open scoped FintypeCatDiscrete

variable (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F] [FiberFunctor F']
  (ρ : Aut F' →ₜ* Aut F)

/-- V.6, after V.6.1 (converse): the functor `C ⥤ C'` associated with a continuous homomorphism
`ρ : π_{F'} → π_F`, namely `C ≃ C(π_F) ⥤ C(π_{F'}) ≃ C'`, restriction along `ρ` in the
middle. -/
noncomputable def functorOfHom : C ⥤ C' :=
  functorToContAction F ⋙ ContAction.res _ ρ ⋙ (equivalenceContAction F').inverse

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor associated with `ρ` satisfies `F' ∘ H ≅ F`. -/
noncomputable def functorOfHomCompIso : functorOfHom F F' ρ ⋙ F' ≅ F :=
  isoWhiskerLeft (functorToContAction F ⋙ ContAction.res _ ρ)
    (isoWhiskerRight (equivalenceContAction F').counitIso
      (ObjectProperty.ι _ ⋙ Action.forget _ _))

instance : FiberFunctor (functorOfHom F F' ρ ⋙ F') :=
  fiberFunctor_of_natIso (functorOfHomCompIso F F' ρ).symm

/-- V.6, after V.6.1: the functor associated with a continuous homomorphism is exact. -/
theorem exact_functorOfHom : PreservesFiniteLimits (functorOfHom F F' ρ) ∧
    PreservesFiniteColimits (functorOfHom F F' ρ) :=
  exact_of_fiberFunctor_comp _ F'

omit [GaloisCategory C] [FiberFunctor F] in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.6, after V.6.1: the homomorphism `ᵗH` induced by the functor `H` associated with `ρ` is
`ρ`, once `π_{F' ∘ H}` is identified with `π_F` by the isomorphism `F' ∘ H ≅ F`. -/
theorem conjAut_autWhiskerLeft_functorOfHom (σ : Aut F') :
    (functorOfHomCompIso F F' ρ).conjAut (autWhiskerLeft (functorOfHom F F' ρ) F' σ) = ρ σ := by
  apply Aut.ext
  ext X : 2
  have key : σ.hom.app ((functorOfHom F F' ρ).obj X) ≫ (functorOfHomCompIso F F' ρ).hom.app X =
      (functorOfHomCompIso F F' ρ).hom.app X ≫ (ρ σ).hom.app X :=
    ((equivalenceContAction F').counitIso.hom.app
      ((ContAction.res _ ρ).obj ((functorToContAction F).obj X))).hom.comm σ
  rw [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app, NatTrans.comp_app, autWhiskerLeft_hom_app,
    key, Iso.inv_hom_id_app_assoc]

end Converse

/-! ### V.6.3: the category of exact functors -/

section ExactFunctorCategory

variable (C C')

/-- V.6.3: the category of exact functors from `C` to `C'`. -/
abbrev ExactFunctorCat : Type _ :=
  ObjectProperty.FullSubcategory fun H : C ⥤ C' ↦
    PreservesFiniteLimits H ∧ PreservesFiniteColimits H

variable {C C'}

instance (H : ExactFunctorCat C C') : PreservesFiniteLimits H.obj := H.property.1
instance (H : ExactFunctorCat C C') : PreservesFiniteColimits H.obj := H.property.2

variable (C C') in
/-- V.6.3: the functor `H ↦ ᵗH` from exact functors `C ⥤ C'` to functors between the
fundamental groupoids `Γ' ⥤ Γ`. -/
@[simps]
def transposeFunctorFunctor :
    ExactFunctorCat C C' ⥤ (FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C) where
  obj H := transposeFunctor H.obj
  map {H₁ H₂} α :=
    { app := fun F' ↦ ObjectProperty.homMk (whiskerRight α.hom F'.obj)
      naturality := fun F' G' t ↦ by
        ext X : 3
        exact (t.hom.naturality (α.hom.app X)).symm }

instance : (transposeFunctorFunctor.{u₁, u₂, v₁, v₂, w} C C').Faithful where
  map_injective {H₁ H₂} α β h := by
    obtain ⟨F'⟩ : Nonempty (FiberFunctors.{v₁, v₂, w} C') := inferInstance
    ext X
    apply F'.obj.map_injective
    exact congrArg (fun θ ↦ (θ.app F').hom.app X) h

set_option backward.isDefEq.respectTransparency.types false in
instance : (transposeFunctorFunctor.{u₁, u₂, v₁, v₂, w} C C').Full where
  map_surjective {H₁ H₂} θ := by
    obtain ⟨F₀⟩ : Nonempty (FiberFunctors.{v₁, v₂, w} C') := inferInstance
    have hφ (X : C) :
        ∃ f : H₁.obj.obj X ⟶ H₂.obj.obj X, F₀.obj.map f = (θ.app F₀).hom.app X := by
      let φ : (functorToAction F₀.obj).obj (H₁.obj.obj X) ⟶
          (functorToAction F₀.obj).obj (H₂.obj.obj X) :=
        { hom := (θ.app F₀).hom.app X
          comm := fun σ ↦ congrArg (fun t ↦ t.hom.app X)
            (θ.naturality (ObjectProperty.homMk σ.hom)) }
      obtain ⟨f, hf⟩ := (functorToAction F₀.obj).map_surjective φ
      exact ⟨f, congrArg Action.Hom.hom hf⟩
    choose α hα using hφ
    let a : H₁.obj ⟶ H₂.obj :=
      { app := α
        naturality := fun X Y f ↦ F₀.obj.map_injective (by
          rw [F₀.obj.map_comp, F₀.obj.map_comp, hα, hα]
          exact ((θ.app F₀).hom.naturality f)) }
    refine ⟨ObjectProperty.homMk a, ?_⟩
    ext F' : 2
    apply ObjectProperty.hom_ext
    ext X : 2
    obtain ⟨t⟩ := nonempty_iso_fiberFunctors C' F₀ F'
    have h1 := congrArg (fun s ↦ s.hom.app X) (θ.naturality t.hom)
    have h2 := t.hom.hom.naturality (α X)
    change F'.obj.map (α X) = (θ.app F').hom.app X
    have : t.hom.hom.app (H₁.obj.obj X) ≫ F'.obj.map (α X) =
        t.hom.hom.app (H₁.obj.obj X) ≫ (θ.app F').hom.app X := by
      rw [← h2, hα]
      exact h1.symm
    exact (cancel_epi _).1 this

/-- The homomorphism `π_{F'} → π_{U(F')}` defined by a functor `U : Γ' ⥤ Γ` between
fundamental groupoids. -/
noncomputable def groupoidAutHom (U : FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C)
    (F' : FiberFunctors.{v₁, v₂, w} C') : Aut F'.obj →* Aut (U.obj F').obj :=
  ((ObjectProperty.fullyFaithfulι _).autMulEquivOfFullyFaithful (U.obj F')).toMonoidHom.comp
    ((U.mapAut F').comp
      ((ObjectProperty.fullyFaithfulι _).autMulEquivOfFullyFaithful F').symm.toMonoidHom)

lemma groupoidAutHom_hom (U : FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C)
    (F' : FiberFunctors.{v₁, v₂, w} C') (σ : Aut F'.obj) :
    (groupoidAutHom U F' σ).hom = (U.map (ObjectProperty.homMk σ.hom)).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.3: a functor `U : Γ' ⥤ Γ` between the fundamental groupoids is isomorphic to `ᵗH` for an
exact functor `H : C ⥤ C'` iff the homomorphisms `π_{F'} → π_{U(F')}` it defines are
continuous. -/
theorem mem_essImage_transposeFunctorFunctor_iff
    (U : FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C) :
    (transposeFunctorFunctor C C').essImage U ↔ ∀ F', Continuous (groupoidAutHom U F') := by
  constructor
  · rintro ⟨H, ⟨i⟩⟩ F'
    let φ : H.obj ⋙ F'.obj ≅ (U.obj F').obj := (ObjectProperty.ι _).mapIso (i.app F')
    have : ⇑(groupoidAutHom U F') = φ.conjAut ∘ autWhiskerLeft H.obj F'.obj := by
      ext σ : 1
      apply Aut.ext
      rw [groupoidAutHom_hom, Function.comp_apply, Iso.conjAut_hom, Iso.conj_apply]
      have h := i.hom.naturality (ObjectProperty.homMk σ.hom)
      have hB : U.map (ObjectProperty.homMk σ.hom) = i.inv.app F' ≫
          ((transposeFunctorFunctor C C').obj H).map (ObjectProperty.homMk σ.hom) ≫
            i.hom.app F' := by
        rw [h, Iso.inv_hom_id_app_assoc]
      rw [hB]
      rfl
    rw [this]
    exact (continuous_conjAut φ).comp (continuous_autWhiskerLeft H.obj F'.obj)
  · intro hU
    obtain ⟨F'₀⟩ : Nonempty (FiberFunctors.{v₁, v₂, w} C') := inferInstance
    let F₀ := U.obj F'₀
    let ρ : Aut F'₀.obj →ₜ* Aut F₀.obj := ⟨groupoidAutHom U F'₀, hU F'₀⟩
    let H := functorOfHom F₀.obj F'₀.obj ρ
    have hH := exact_functorOfHom F₀.obj F'₀.obj ρ
    let e₀ : H ⋙ F'₀.obj ≅ F₀.obj := functorOfHomCompIso F₀.obj F'₀.obj ρ
    let t (F' : FiberFunctors.{v₁, v₂, w} C') : F'₀ ≅ F' :=
      (nonempty_iso_fiberFunctors C' F'₀ F').some
    let ψ (F' : FiberFunctors.{v₁, v₂, w} C') : H ⋙ F'.obj ≅ (U.obj F').obj :=
      isoWhiskerLeft H ((ObjectProperty.ι _).mapIso (t F')).symm ≪≫ e₀ ≪≫
        (ObjectProperty.ι _).mapIso (U.mapIso (t F'))
    refine ⟨⟨H, hH⟩, ⟨NatIso.ofComponents (fun F' ↦ ObjectProperty.isoMk _ (ψ F'))
      fun {F' G'} s ↦ ?_⟩⟩
    let τ : F'₀ ⟶ F'₀ := (t F').hom ≫ s ≫ (t G').inv
    have : IsIso τ.hom := isIso_of_fiberFunctor τ.hom
    have key := conjAut_autWhiskerLeft_functorOfHom F₀.obj F'₀.obj ρ (asIso τ.hom)
    have key' : e₀.hom ≫ (U.map τ).hom = whiskerLeft H τ.hom ≫ e₀.hom := by
      have h := congrArg (fun a : Aut F₀.obj ↦ a.hom) key
      change e₀.inv ≫ whiskerLeft H τ.hom ≫ e₀.hom = (U.map τ).hom at h
      rw [← h]
      simp
    have hτ : τ ≫ (t G').hom = (t F').hom ≫ s := by simp [τ]
    have hτ' : (t F').inv ≫ τ = s ≫ (t G').inv := by simp [τ]
    apply ObjectProperty.hom_ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    change s.hom.app (H.obj X) ≫ (t G').inv.hom.app (H.obj X) ≫ e₀.hom.app X ≫
        (U.map (t G').hom).hom.app X =
      ((t F').inv.hom.app (H.obj X) ≫ e₀.hom.app X ≫ (U.map (t F').hom).hom.app X) ≫
        (U.map s).hom.app X
    have h1 : e₀.hom.app X ≫ (U.map τ).hom.app X = τ.hom.app (H.obj X) ≫ e₀.hom.app X :=
      congrArg (fun a ↦ a.app X) key'
    have h2 : (U.map (t F').hom).hom.app X ≫ (U.map s).hom.app X =
        (U.map τ).hom.app X ≫ (U.map (t G').hom).hom.app X := by
      have := congrArg (fun a ↦ (U.map a).hom.app X) hτ
      simp only [U.map_comp] at this
      exact this.symm
    have h3 : (t F').inv.hom.app (H.obj X) ≫ τ.hom.app (H.obj X) =
        s.hom.app (H.obj X) ≫ (t G').inv.hom.app (H.obj X) :=
      congrArg (fun a ↦ a.hom.app (H.obj X)) hτ'
    calc s.hom.app (H.obj X) ≫ (t G').inv.hom.app (H.obj X) ≫ e₀.hom.app X ≫
          (U.map (t G').hom).hom.app X
        = ((t F').inv.hom.app (H.obj X) ≫ τ.hom.app (H.obj X)) ≫ e₀.hom.app X ≫
          (U.map (t G').hom).hom.app X := by rw [h3, Category.assoc]
      _ = (t F').inv.hom.app (H.obj X) ≫ (e₀.hom.app X ≫ (U.map τ).hom.app X) ≫
          (U.map (t G').hom).hom.app X := by rw [h1]; simp only [Category.assoc]
      _ = ((t F').inv.hom.app (H.obj X) ≫ e₀.hom.app X ≫ (U.map (t F').hom).hom.app X) ≫
          (U.map s).hom.app X := by simp only [Category.assoc, h2]


variable (C C') in
/-- V.6.3: the functors `U : Γ' ⥤ Γ` whose induced homomorphisms `π_{F'} → π_{U(F')}` are
continuous. -/
def IsContinuousGroupoidFunctor :
    ObjectProperty (FiberFunctors.{v₁, v₂, w} C' ⥤ FiberFunctors.{u₁, u₂, w} C) :=
  fun U ↦ ∀ F', Continuous (groupoidAutHom U F')

variable (C C') in
/-- V.6.3: `H ↦ ᵗH` as a functor to the category of functors `Γ' ⥤ Γ` with continuous
induced homomorphisms. -/
def transposeFunctorFunctorLift :
    ExactFunctorCat C C' ⥤
      (IsContinuousGroupoidFunctor.{u₁, u₂, v₁, v₂, w} C C').FullSubcategory :=
  ObjectProperty.lift _ (transposeFunctorFunctor C C') fun H ↦
    (mem_essImage_transposeFunctorFunctor_iff _).1 ⟨H, ⟨Iso.refl _⟩⟩

instance : (transposeFunctorFunctorLift.{u₁, u₂, v₁, v₂, w} C C').Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (transposeFunctorFunctorLift.{u₁, u₂, v₁, v₂, w} C C').Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (transposeFunctorFunctorLift.{u₁, u₂, v₁, v₂, w} C C').EssSurj where
  mem_essImage U := by
    obtain ⟨H, ⟨i⟩⟩ := (mem_essImage_transposeFunctorFunctor_iff U.obj).2 U.property
    exact ⟨H, ⟨ObjectProperty.isoMk _ i⟩⟩

/-- V.6.3: the category of exact functors `C ⥤ C'` is equivalent to the category of functors
`U : Γ' ⥤ Γ` between the fundamental groupoids whose induced homomorphisms
`π_{F'} → π_{U(F')}` are continuous. -/
instance : (transposeFunctorFunctorLift.{u₁, u₂, v₁, v₂, w} C C').IsEquivalence where

end ExactFunctorCategory

/-! ### V.6.4–V.6.11: properties of `H` in terms of `u = ᵗH` -/

/-- In a profinite group whose open subgroups separate points from `1`, if the kernel of a
continuous homomorphism `u` from a compact group is contained in an open subgroup `U'`, then so
is `u⁻¹(V)` for some open subgroup `V`. -/
lemma exists_openSubgroup_comap_le {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [CompactSpace G'] (u : G' →* G) (hu : Continuous u)
    (h1 : ∀ g : G, g ≠ 1 → ∃ V : OpenSubgroup G, g ∉ V) (U' : OpenSubgroup G')
    (hker : u.ker ≤ U'.toSubgroup) : ∃ V : OpenSubgroup G, V.toSubgroup.comap u ≤ U' := by
  let V' (V : OpenSubgroup G) : OpenSubgroup G' := V.comap u hu
  obtain ⟨V, hV⟩ := isCompact_univ.elim_directed_family_closed
    (fun V : OpenSubgroup G ↦ (V' V : Set G') \ U') (fun V ↦ (V' V).isClosed.sdiff U'.isOpen)
    (by
      rw [Set.disjoint_iff]
      rintro x ⟨-, hx⟩
      simp only [Set.mem_iInter, Set.mem_sdiff, SetLike.mem_coe] at hx
      obtain ⟨V⟩ : Nonempty (OpenSubgroup G) := inferInstance
      refine (hx V).2 (hker ?_)
      by_contra h
      obtain ⟨W, hW⟩ := h1 (u x) h
      exact hW (hx W).1)
    (fun V W ↦ ⟨V ⊓ W,
      fun x hx ↦ ⟨(inf_le_left : V ⊓ W ≤ V) (show u x ∈ V ⊓ W from hx.1), hx.2⟩,
      fun x hx ↦ ⟨(inf_le_right : V ⊓ W ≤ W) (show u x ∈ V ⊓ W from hx.1), hx.2⟩⟩)
  refine ⟨V, fun x hx ↦ ?_⟩
  by_contra h
  exact Set.disjoint_left.1 hV (Set.mem_univ x) ⟨hx, h⟩

section Homomorphism

variable (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F'] [FiberFunctor (H ⋙ F')]

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] in
/-- The open subgroups of `π_F` separate the points from `1`. -/
lemma exists_openSubgroup_notMem (g : Aut F) (hg : g ≠ 1) : ∃ V : OpenSubgroup (Aut F), g ∉ V := by
  obtain ⟨A, -, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.1
    (isOpen_compl_singleton.mem_nhds (Ne.symm hg))
  exact ⟨⟨_, stabilizer_isOpen (Aut F) A.pt⟩, fun h ↦ hA h rfl⟩

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
/-- The stabilizer in `π_{F'}` of a point of `F(X) = F'(H(X))` is the inverse image under `u`
of its stabilizer in `π_F`. -/
lemma comap_stabilizer {X : C} (x : (H ⋙ F').obj X) :
    (MulAction.stabilizer (Aut (H ⋙ F')) x).comap (autWhiskerLeft H F') =
      MulAction.stabilizer (Aut F') (show F'.obj (H.obj X) from x) :=
  rfl

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- Along a monomorphism, stabilizers of points of the fibres agree. -/
lemma stabilizer_map_of_mono {Y Z : C'} (i : Y ⟶ Z) [Mono i] (y : F'.obj Y) :
    MulAction.stabilizer (Aut F') (F'.map i y) = MulAction.stabilizer (Aut F') y := by
  have hi : Function.Injective (F'.map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  ext σ
  simp only [MulAction.mem_stabilizer_iff, mulAction_naturality, hi.eq_iff]

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- V.6.4, first part: the stabilizer `U` of a point `x` of `F(X)` contains `u(π_{F'})` iff
`H(X)` admits a section through `x` ("a pointed section"). -/
theorem range_le_stabilizer_iff {X : C} (x : (H ⋙ F').obj X) :
    (autWhiskerLeft H F').range ≤ MulAction.stabilizer (Aut (H ⋙ F')) x ↔
      ∃ s : ⊤_ C' ⟶ H.obj X, x ∈ Set.range (F'.map s) := by
  rw [← forall_smul_eq_iff_exists_section F']
  exact ⟨fun h σ ↦ h ⟨σ, rfl⟩, fun h _ ⟨σ, hσ⟩ ↦ hσ ▸ h σ⟩

/-- V.6.4, second part: for `X` connected and `x ∈ F(X)`, the stabilizer `U` of `x` contains the
closed normal subgroup generated by `u(π_{F'})` iff `H(X)` is completely decomposed. -/
theorem topologicalClosure_normalClosure_le_stabilizer_iff {X : C} [IsConnected X]
    (x : (H ⋙ F').obj X) :
    (Subgroup.normalClosure ((autWhiskerLeft H F').range : Set (Aut (H ⋙ F')))).topologicalClosure ≤
      MulAction.stabilizer (Aut (H ⋙ F')) x ↔ IsCompletelyDecomposed (H.obj X) := by
  have hU : IsClosed (MulAction.stabilizer (Aut (H ⋙ F')) x : Set (Aut (H ⋙ F'))) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ x)
  rw [isCompletelyDecomposed_iff F']
  constructor
  · intro h σ y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut (H ⋙ F')) x (show (H ⋙ F').obj X from y)
    have hmem : g⁻¹ * autWhiskerLeft H F' σ * g⁻¹⁻¹ ∈ MulAction.stabilizer (Aut (H ⋙ F')) x :=
      h (Subgroup.le_topologicalClosure _ ((Subgroup.normalClosure_normal).conj_mem _
        (Subgroup.subset_normalClosure
          (show autWhiskerLeft H F' σ ∈ ((autWhiskerLeft H F').range : Set (Aut (H ⋙ F')))
            from ⟨σ, rfl⟩)) g⁻¹))
    rw [MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at hmem
    exact hmem
  · intro h
    refine Subgroup.topologicalClosure_minimal _ ?_ hU
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨a, ⟨σ, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    have key (y : (H ⋙ F').obj X) : autWhiskerLeft H F' σ • y = y := h σ y
    change (c * autWhiskerLeft H F' σ * c⁻¹) • x = x
    rw [mul_smul, mul_smul, key, smul_inv_smul]

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- V.6.5: `u` is trivial iff `H(X)` is completely decomposed for every `X`. -/
theorem autWhiskerLeft_eq_one_iff :
    autWhiskerLeft H F' = 1 ↔ ∀ X : C, IsCompletelyDecomposed (H.obj X) := by
  simp_rw [isCompletelyDecomposed_iff F']
  refine ⟨fun h X σ y ↦ ?_, fun h ↦ ?_⟩
  · have h1 : autWhiskerLeft H F' σ = 1 := by rw [h]; rfl
    have key (z : (H ⋙ F').obj X) : autWhiskerLeft H F' σ • z = z := by rw [h1, one_smul]
    exact key y
  · ext σ X y
    exact h X σ y

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- V.6.6, sufficiency: if a connected component `Y` of `H(X)` through `x` maps to `X'`, sending
the point `y` to `x'`, then the stabilizer of `x'` contains `Ker u`. -/
theorem ker_le_stabilizer_of_hom {X : C} {X' Y : C'} (i : Y ⟶ H.obj X) [Mono i] (f : Y ⟶ X')
    [IsConnected Y] (y : F'.obj Y) :
    (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') (F'.map f y) := by
  intro σ hσ
  have key (z : (H ⋙ F').obj X) : autWhiskerLeft H F' σ • z = z := by
    rw [(MonoidHom.mem_ker).1 hσ, one_smul]
  have h1 : σ ∈ MulAction.stabilizer (Aut F') y := by
    rw [← stabilizer_map_of_mono F' i y]
    exact key _
  exact (exists_hom_iff_stabilizer_le F' y (F'.map f y)).1 ⟨f, rfl⟩ h1

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- V.6.6, sufficiency in the case `u` surjective. -/
theorem ker_le_stabilizer_of_iso {X : C} {X' : C'} (e : H.obj X ≅ X') (x : (H ⋙ F').obj X) :
    (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') (F'.map e.hom x) := by
  intro σ hσ
  have key (z : (H ⋙ F').obj X) : autWhiskerLeft H F' σ • z = z := by
    rw [(MonoidHom.mem_ker).1 hσ, one_smul]
  rw [stabilizer_map_of_mono F' e.hom]
  exact key x

/-- V.6.6: for a connected pointed object `(X', x')` of `C'` with stabilizer `U'`, `U'` contains
`Ker u` iff there is a connected pointed object `(X, x)` of `C` and a pointed morphism from the
connected component `(Y, y)` of `H(X)` through `x` to `(X', x')`. -/
theorem ker_le_stabilizer_iff {X' : C'} [IsConnected X'] (x' : F'.obj X') :
    (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') x' ↔
      ∃ (X : C) (x : (H ⋙ F').obj X) (Y : C') (i : Y ⟶ H.obj X) (y : F'.obj Y) (f : Y ⟶ X'),
        IsConnected X ∧ IsConnected Y ∧ Mono i ∧ F'.map i y = x ∧ F'.map f y = x' := by
  constructor
  · intro h
    obtain ⟨V, hV⟩ := exists_openSubgroup_comap_le (autWhiskerLeft H F')
      (continuous_autWhiskerLeft H F')
      (exists_openSubgroup_notMem (H ⋙ F')) ⟨_, stabilizer_isOpen _ x'⟩ h
    obtain ⟨X, x, hX, hx⟩ := exists_isConnected_stabilizer_eq (H ⋙ F') V
    obtain ⟨Y, i, y, hy, hY, hi⟩ := fiber_in_connected_component F' (H.obj X) x
    have hle : MulAction.stabilizer (Aut F') y ≤ MulAction.stabilizer (Aut F') x' := by
      rw [← stabilizer_map_of_mono F' i y, hy]
      change (MulAction.stabilizer (Aut (H ⋙ F')) x).comap (autWhiskerLeft H F') ≤ _
      rw [hx]
      exact hV
    obtain ⟨f, hf⟩ := (exists_hom_iff_stabilizer_le F' y x').2 hle
    exact ⟨X, x, Y, i, y, f, hX, hY, hi, hy, hf⟩
  · rintro ⟨X, x, Y, i, y, f, -, hY, hi, -, rfl⟩
    exact ker_le_stabilizer_of_hom H F' i f y

/-- V.6.6, case `u` surjective: `U'` contains `Ker u` iff `(X', x')` is isomorphic, as a pointed
object, to `H(X)` for a connected pointed object `(X, x)` of `C`. -/
theorem ker_le_stabilizer_iff_of_surjective (hu : Function.Surjective (autWhiskerLeft H F'))
    {X' : C'}
    [IsConnected X'] (x' : F'.obj X') :
    (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') x' ↔
      ∃ (X : C) (x : (H ⋙ F').obj X) (e : H.obj X ≅ X'), IsConnected X ∧ F'.map e.hom x = x' := by
  constructor
  · intro h
    let U' := MulAction.stabilizer (Aut F') x'
    have hU'o : IsOpen (U' : Set (Aut F')) := stabilizer_isOpen _ x'
    let V := U'.map (autWhiskerLeft H F')
    have hVc : IsClosed (V : Set (Aut (H ⋙ F'))) := by
      rw [Subgroup.coe_map]
      exact ((Subgroup.isClosed_of_isOpen _ hU'o).isCompact.image
        (continuous_autWhiskerLeft H F')).isClosed
    have : Finite (Aut F' ⧸ U') := Subgroup.quotient_finite_of_isOpen U' hU'o
    have : U'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have : V.FiniteIndex := ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero
      (Subgroup.index_map_dvd U' hu)⟩
    obtain ⟨X, x, hX, hx⟩ := exists_isConnected_stabilizer_eq (H ⋙ F')
      ⟨V, Subgroup.isOpen_of_isClosed_of_finiteIndex V hVc⟩
    have hstab : MulAction.stabilizer (Aut F') (show F'.obj (H.obj X) from x) = U' := by
      change (MulAction.stabilizer (Aut (H ⋙ F')) x).comap (autWhiskerLeft H F') = U'
      rw [hx]
      change V.comap _ = U'
      rw [Subgroup.comap_map_eq, sup_eq_left.2 h]
    have : Nonempty (F'.obj (H.obj X)) := ⟨x⟩
    have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := ⟨fun y z ↦ by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut (H ⋙ F'))
        (show (H ⋙ F').obj X from y) (show (H ⋙ F').obj X from z)
      obtain ⟨σ, rfl⟩ := hu g
      exact ⟨σ, hg⟩⟩
    have := isConnected_of_isPretransitive F' (H.obj X)
    obtain ⟨f, hf⟩ := (exists_hom_iff_stabilizer_le F' (show F'.obj (H.obj X) from x) x').2
      hstab.le
    obtain ⟨g, hg⟩ := (exists_hom_iff_stabilizer_le F' x' (show F'.obj (H.obj X) from x)).2
      hstab.ge
    refine ⟨X, x, ⟨f, g, ?_, ?_⟩, hX, hf⟩
    · apply hom_ext_of_isConnected F' (show F'.obj (H.obj X) from x)
      rw [F'.map_comp, FintypeCat.comp_apply, hf, hg, F'.map_id, FintypeCat.id_apply]
    · apply hom_ext_of_isConnected F' x'
      rw [F'.map_comp, FintypeCat.comp_apply, hg, hf, F'.map_id, FintypeCat.id_apply]
  · rintro ⟨X, x, e, -, rfl⟩
    exact ker_le_stabilizer_of_iso H F' e x

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
/-- `Ker u` is contained in the stabilizer of one point of a connected object iff it is contained
in the stabilizers of all its points (it is a normal subgroup). -/
lemma ker_le_stabilizer_smul {X' : C'} (x' : F'.obj X') (σ : Aut F')
    (h : (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') x') :
    (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') (σ • x') := by
  intro τ hτ
  have := h ((autWhiskerLeft H F').normal_ker.conj_mem τ hτ σ⁻¹)
  rw [MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at this
  exact this

/-- V.6.7: for a connected object `X'` of `C'` (with stabilizers `U'`), `U'` contains `Ker u`
iff there is an object `X` of `C` and a morphism from a connected component of `H(X)` to `X'`. -/
theorem ker_le_stabilizer_iff_exists_hom {X' : C'} [IsConnected X'] :
    (∀ x' : F'.obj X', (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') x') ↔
      ∃ (X : C) (Y : C') (i : Y ⟶ H.obj X) (_ : Y ⟶ X'), IsConnected Y ∧ Mono i := by
  refine ⟨fun h ↦ ?_, fun ⟨X, Y, i, f, hY, hi⟩ x' ↦ ?_⟩
  · obtain ⟨x'⟩ := nonempty_fiber_of_isConnected F' X'
    obtain ⟨X, -, Y, i, -, f, -, hY, hi, -⟩ := (ker_le_stabilizer_iff H F' x').1 (h x')
    exact ⟨X, Y, i, f, hY, hi⟩
  · obtain ⟨y⟩ := nonempty_fiber_of_isConnected F' Y
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F') (F'.map f y) x'
    exact ker_le_stabilizer_smul H F' _ σ (ker_le_stabilizer_of_hom H F' i f y)

/-- V.6.7, case `u` surjective: `U'` contains `Ker u` iff `X'` is isomorphic to some `H(X)`. -/
theorem ker_le_stabilizer_iff_exists_iso_of_surjective
    (hu : Function.Surjective (autWhiskerLeft H F'))
    {X' : C'} [IsConnected X'] :
    (∀ x' : F'.obj X', (autWhiskerLeft H F').ker ≤ MulAction.stabilizer (Aut F') x') ↔
      ∃ X : C, Nonempty (H.obj X ≅ X') := by
  refine ⟨fun h ↦ ?_, fun ⟨X, ⟨e⟩⟩ x' ↦ ?_⟩
  · obtain ⟨x'⟩ := nonempty_fiber_of_isConnected F' X'
    obtain ⟨X, -, e, -⟩ := (ker_le_stabilizer_iff_of_surjective H F' hu x').1 (h x')
    exact ⟨X, ⟨e⟩⟩
  · have hx : F'.map e.hom (F'.map e.inv x') = x' := by
      rw [← FintypeCat.comp_apply, ← F'.map_comp, e.inv_hom_id, F'.map_id, FintypeCat.id_apply]
    exact hx ▸ ker_le_stabilizer_of_iso H F' e (F'.map e.inv x')

/-- V.6.8: `u` is injective iff for every connected object `X'` of `C'` there are an object `X`
of `C` and a morphism from a connected component of `H(X)` to `X'`. (SGA says "for every object
`X'`"; the condition fails for the initial object, so connected objects are meant.) -/
theorem injective_autWhiskerLeft_iff : Function.Injective (autWhiskerLeft H F') ↔
    ∀ X' : C', IsConnected X' →
      ∃ (X : C) (Y : C') (i : Y ⟶ H.obj X) (_ : Y ⟶ X'), IsConnected Y ∧ Mono i := by
  refine ⟨fun h X' _ ↦ (ker_le_stabilizer_iff_exists_hom H F').1 fun x' ↦ ?_, fun h ↦ ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).2 h]
    exact bot_le
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    ext X' x'
    obtain ⟨Y, i, y, rfl, hY, hi⟩ := fiber_in_connected_component F' X' x'
    have := (ker_le_stabilizer_iff_exists_hom H F' (X' := Y)).2 (h Y hY) y hσ
    change σ • F'.map i y = F'.map i y
    rw [mulAction_naturality, this]

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
lemma isClosed_range_autWhiskerLeft :
    IsClosed ((autWhiskerLeft H F').range : Set (Aut (H ⋙ F'))) := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range (continuous_autWhiskerLeft H F')).isClosed

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.9: the following are equivalent: `u` is surjective; `H` transforms connected objects
into connected objects; `H` is fully faithful. -/
theorem surjective_autWhiskerLeft_tfae : List.TFAE
    [Function.Surjective (autWhiskerLeft H F'), PreservesIsConnected H, H.Full ∧ H.Faithful] := by
  tfae_have 1 → 2 := fun hu ↦ ⟨fun {X} _ ↦ by
    obtain ⟨x⟩ := nonempty_fiber_of_isConnected (H ⋙ F') X
    have : Nonempty (F'.obj (H.obj X)) := ⟨x⟩
    have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := ⟨fun y z ↦ by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut (H ⋙ F'))
        (show (H ⋙ F').obj X from y) (show (H ⋙ F').obj X from z)
      obtain ⟨σ, rfl⟩ := hu g
      exact ⟨σ, hg⟩⟩
    exact isConnected_of_isPretransitive F' (H.obj X)⟩
  tfae_have 2 → 1 := fun hH g ↦ by
    by_contra hg
    obtain ⟨V, hV, hgV⟩ := exists_openSubgroup_le_of_notMem (H ⋙ F') _
      (isClosed_range_autWhiskerLeft H F') (g := g) fun ⟨σ, hσ⟩ ↦ hg ⟨σ, hσ⟩
    obtain ⟨X, x, hX, hx⟩ := exists_isConnected_stabilizer_eq (H ⋙ F') V
    have : IsConnected (H.obj X) := hH.preserves
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F') (show F'.obj (H.obj X) from x)
      (show F'.obj (H.obj X) from g • x)
    have hmem : g⁻¹ * autWhiskerLeft H F' σ ∈ MulAction.stabilizer (Aut (H ⋙ F')) x := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
      exact hσ
    rw [hx] at hmem
    have h2 : autWhiskerLeft H F' σ ∈ V := hV ⟨σ, rfl⟩
    exact hgV (by simpa using V.mul_mem h2 (V.inv_mem hmem))
  tfae_have 1 → 3 := fun hu ↦ by
    have := exact_of_fiberFunctor_comp H F'
    have : H.Faithful := Faithful.of_comp H F'
    refine ⟨⟨fun {X Y} f' ↦ ?_⟩, this⟩
    let φ : (functorToAction (H ⋙ F')).obj X ⟶ (functorToAction (H ⋙ F')).obj Y :=
      { hom := F'.map f'
        comm := fun g ↦ by
          obtain ⟨σ, rfl⟩ := hu g
          ext (y : F'.obj (H.obj X))
          exact (mulAction_naturality F' σ f' y).symm }
    obtain ⟨f, hf⟩ := (functorToAction (H ⋙ F')).map_surjective φ
    exact ⟨f, F'.map_injective (congrArg Action.Hom.hom hf)⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ g ↦ by
    have := (exact_of_fiberFunctor_comp H F').1
    by_contra hg
    obtain ⟨V, hV, hgV⟩ := exists_openSubgroup_le_of_notMem (H ⋙ F') _
      (isClosed_range_autWhiskerLeft H F') (g := g) fun ⟨σ, hσ⟩ ↦ hg ⟨σ, hσ⟩
    obtain ⟨X, x, hX, hx⟩ := exists_isConnected_stabilizer_eq (H ⋙ F') V
    have hV' : (autWhiskerLeft H F').range ≤ MulAction.stabilizer (Aut (H ⋙ F')) x := by
      rw [hx]
      exact hV
    obtain ⟨s', q, hq⟩ := (forall_smul_eq_iff_exists_section F'
      (show F'.obj (H.obj X) from x)).1 fun σ ↦ hV' ⟨σ, rfl⟩
    let e : H.obj (⊤_ C) ≅ ⊤_ C' :=
      (IsTerminal.isTerminalObj H (⊤_ C) terminalIsTerminal).uniqueUpToIso terminalIsTerminal
    obtain ⟨s, hs⟩ := H.map_surjective (e.hom ≫ s')
    have hmem : x ∈ Set.range ((H ⋙ F').map s) := ⟨F'.map e.inv q, by
      change F'.map (H.map s) (F'.map e.inv q) = x
      rw [hs, ← FintypeCat.comp_apply, ← F'.map_comp, e.inv_hom_id_assoc, hq]⟩
    have : g ∈ MulAction.stabilizer (Aut (H ⋙ F')) x :=
      (forall_smul_eq_iff_exists_section (H ⋙ F') x).2 ⟨s, hmem⟩ g
    rw [hx] at this
    exact hgV this
  tfae_finish

open scoped FintypeCatDiscrete in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.10: the following are equivalent: `u` is an isomorphism; `H` is an equivalence; `H`
transforms connected objects into connected objects and every object of `C'` is isomorphic to an
object `H(X)`. -/
theorem bijective_autWhiskerLeft_tfae : List.TFAE
    [Function.Bijective (autWhiskerLeft H F'), H.IsEquivalence,
      PreservesIsConnected H ∧ H.EssSurj] := by
  have h9 := surjective_autWhiskerLeft_tfae H F'
  tfae_have 1 → 2 := fun hbij ↦ by
    have h13 := h9.out 1 3
    obtain ⟨_, _⟩ := h13.1 hbij.2
    let e : Aut F' ≃ₜ* Aut (H ⋙ F') :=
      { MulEquiv.ofBijective (autWhiskerLeft H F') hbij with
        continuous_toFun := continuous_autWhiskerLeft H F'
        continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
          (f := (MulEquiv.ofBijective (autWhiskerLeft H F') hbij).toEquiv)
          (continuous_autWhiskerLeft H F') }
    have : H.EssSurj := ⟨fun X' ↦ by
      let Z := (functorToContAction F').obj X'
      let Y := (ContAction.resEquiv FintypeCat.{w} e).inverse.obj Z
      let X := (functorToContAction (H ⋙ F')).objPreimage Y
      let i : (functorToContAction (H ⋙ F')).obj X ≅ Y :=
        (functorToContAction (H ⋙ F')).objObjPreimageIso Y
      let j : (ContAction.res _ (autContinuousHom H F')).obj Y ≅ Z :=
        ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun σ ↦ by
          have : e.symm (autWhiskerLeft H F' σ) = σ := e.symm_apply_apply σ
          simp only [Iso.refl_hom]
          change Z.obj.ρ (e.symm (autWhiskerLeft H F' σ)) = Z.obj.ρ σ
          rw [this])
      exact ⟨X, ⟨(functorToContAction F').preimageIso ((functorToContActionCompIso H F').app X ≪≫
        (ContAction.res _ (autContinuousHom H F')).mapIso i ≪≫ j)⟩⟩⟩
    exact {}
  tfae_have 2 → 3 := fun _ ↦ by
    have := h9.out 3 2
    exact ⟨this.1 ⟨inferInstance, inferInstance⟩, inferInstance⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ ↦ by
    have h21 := h9.out 2 1
    refine ⟨(injective_autWhiskerLeft_iff H F').2 fun X' _ ↦ ?_, h21.1 inferInstance⟩
    exact ⟨H.objPreimage X', X', (H.objObjPreimageIso X').inv, 𝟙 X', inferInstance,
      inferInstance⟩
  tfae_finish

end Homomorphism

/-! ### V.6.11: exactness of a sequence of fundamental groups -/

section Sequence

variable {C'' : Type v₃} [Category.{v₄} C''] [GaloisCategory C''] (H : C ⥤ C') (H' : C' ⥤ C'')
  (F'' : C'' ⥤ FintypeCat.{w}) [FiberFunctor F''] [FiberFunctor (H' ⋙ F'')]
  [FiberFunctor (H ⋙ H' ⋙ F'')]

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor (H' ⋙ F'')]
  [FiberFunctor (H ⋙ H' ⋙ F'')] in
/-- V.6.11, first part: with `u' = ᵗH' : π_{F''} → π_{F'}` and `u = ᵗH : π_{F'} → π_F`,
`u ∘ u'` is trivial iff `H'(H(X))` is completely decomposed for every `X`. (SGA writes
"`Ker u ⊂ Im u'`, i.e. `u u'` trivial"; the condition meant is `Im u' ⊂ Ker u`.) -/
theorem comp_autWhiskerLeft_eq_one_iff :
    (autWhiskerLeft H (H' ⋙ F'')).comp (autWhiskerLeft H' F'') = 1 ↔
    ∀ X : C, IsCompletelyDecomposed (H'.obj (H.obj X)) :=
  autWhiskerLeft_eq_one_iff (H ⋙ H') F''

/-- V.6.11, second part: `Ker u ⊂ Im u'` iff for every connected pointed object `(X', x')` of `C'`
such that `H'(X')` admits a pointed section, there are an object `X` of `C` and a morphism from a
connected component of `H(X)` to `X'`. (SGA writes `Ker u ⊃ Im u'` here: the two inclusions of
V.6.11 are interchanged in SGA. By V.6.4 and V.6.6 the condition says that every open subgroup
containing `Im u'` contains `Ker u`, i.e. `Ker u ⊂ Im u'`, the image being compact.) -/
theorem ker_le_range_iff : (autWhiskerLeft H (H' ⋙ F'')).ker ≤ (autWhiskerLeft H' F'').range ↔
    ∀ (X' : C') [IsConnected X'] (x' : (H' ⋙ F'').obj X'),
      (∃ s : ⊤_ C'' ⟶ H'.obj X', x' ∈ Set.range (F''.map s)) →
        ∃ (X : C) (Y : C') (i : Y ⟶ H.obj X) (_ : Y ⟶ X'), IsConnected Y ∧ Mono i := by
  refine ⟨fun h X' _ x' hs ↦ ?_, fun h g hg ↦ ?_⟩
  · have h1 := (range_le_stabilizer_iff H' F'' x').2 hs
    refine (ker_le_stabilizer_iff_exists_hom H (H' ⋙ F'')).1 fun y ↦ ?_
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut (H' ⋙ F'')) x' y
    exact ker_le_stabilizer_smul H (H' ⋙ F'') x' σ (h.trans h1)
  · by_contra hg'
    obtain ⟨V, hV, hgV⟩ := exists_openSubgroup_le_of_notMem (H' ⋙ F'') _
      (isClosed_range_autWhiskerLeft H' F'') hg'
    obtain ⟨X', x', hX', hx'⟩ := exists_isConnected_stabilizer_eq (H' ⋙ F'') V
    have hs := (range_le_stabilizer_iff H' F'' x').1 (by rw [hx']; exact hV)
    have := (ker_le_stabilizer_iff_exists_hom H (H' ⋙ F'')).2 (h X' x' hs) x' hg
    rw [hx'] at this
    exact hgV this

end Sequence

/-! ### V.6: pro-objects, and the homomorphism of fundamental pro-groups -/

section ProMap

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {C₁ : Type u₁} [Category.{u₂} C₁] [GaloisCategory C₁]
  {C₂ : Type v₁} [Category.{u₂} C₂] [GaloisCategory C₂]
  (H : C₁ ⥤ C₂) (F' : C₂ ⥤ FintypeCat.{u₂}) [FiberFunctor F'] [FiberFunctor (H ⋙ F')]

/-- V.6: the extension of an exact functor `H : C ⥤ C'` to pro-objects. Under the equivalences
`Pro C ≃ C'(π_F)` and `Pro C' ≃ C'(π_{F'})` of V.5.2 (for `F = F' ∘ H`), it is the restriction
of operations along `u = ᵗH : π_{F'} → π_F`, as `H` itself is on `C ≃ C(π_F)` (V.6.2); it extends
`H` (`proMapObjOfIso`). -/
noncomputable def proMap : Pro C₁ ⥤ Pro C₂ :=
  (proEquivalenceOfFiberFunctor (H ⋙ F')).functor ⋙ ContAction.res _ (autContinuousHom H F') ⋙
    (proEquivalenceOfFiberFunctor F').inverse

/-- V.6: the extension of `H` to pro-objects extends `H`. -/
noncomputable def proMapObjOfIso (X : C₁) :
    (proMap H F').obj (Pro.of.obj X) ≅ Pro.of.obj (H.obj X) :=
  (proEquivalenceOfFiberFunctor F').inverse.mapIso
    ((ContAction.res _ (autContinuousHom H F')).mapIso
      (proEquivalenceOfFiberFunctorObjOfIso (H ⋙ F') X) ≪≫
      resFiniteToProfiniteIso _ _ ≪≫
      (finiteToProfinite _).mapIso ((functorToContActionCompIso H F').app X).symm ≪≫
      (proEquivalenceOfFiberFunctorObjOfIso F' (H.obj X)).symm) ≪≫
    (proEquivalenceOfFiberFunctor F').unitIso.symm.app _

omit [GaloisCategory C₁] [GaloisCategory C₂] in
/-- `ᵗ(H' H) = ᵗH ᵗH'` as continuous homomorphisms. -/
lemma autContinuousHom_comp {C₃ : Type*} [Category.{u₂} C₃] (H' : C₂ ⥤ C₃)
    (F'' : C₃ ⥤ FintypeCat.{u₂}) :
    autContinuousHom (H ⋙ H') F'' = (autContinuousHom H (H' ⋙ F'')).comp
      (autContinuousHom H' F'') :=
  rfl

/-- V.6: transitivity: the extension of `H' ∘ H` to pro-objects is the composite of the
extensions of `H` and `H'`. -/
noncomputable def proMapCompIso {C₃ : Type*} [Category.{u₂} C₃] [GaloisCategory C₃]
    (H' : C₂ ⥤ C₃) (F'' : C₃ ⥤ FintypeCat.{u₂}) [FiberFunctor F''] [FiberFunctor (H' ⋙ F'')]
    [FiberFunctor (H ⋙ H' ⋙ F'')] :
    haveI : FiberFunctor ((H ⋙ H') ⋙ F'') := inferInstanceAs (FiberFunctor (H ⋙ H' ⋙ F''))
    proMap (H ⋙ H') F'' ≅ proMap H (H' ⋙ F'') ⋙ proMap H' F'' :=
  haveI : FiberFunctor ((H ⋙ H') ⋙ F'') := inferInstanceAs (FiberFunctor (H ⋙ H' ⋙ F''))
  Functor.isoWhiskerLeft (proEquivalenceOfFiberFunctor (H ⋙ H' ⋙ F'')).functor
    (Functor.isoWhiskerRight (ContAction.resComp Profinite (autContinuousHom H' F'')
      (autContinuousHom H (H' ⋙ F''))) (proEquivalenceOfFiberFunctor F'').inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (ContAction.res _ (autContinuousHom H (H' ⋙ F'')))
      (Functor.isoWhiskerRight (proEquivalenceOfFiberFunctor (H' ⋙ F'')).counitIso.symm
        (ContAction.res _ (autContinuousHom H' F''))))
      (proEquivalenceOfFiberFunctor F'').inverse)

end ProMap

section ProGroupHom

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {C₁ : Type u₂} [SmallCategory C₁] [GaloisCategory C₁]
  {C₂ : Type u₂} [SmallCategory C₂] [GaloisCategory C₂]
  (H : C₁ ⥤ C₂) (F' : C₂ ⥤ FintypeCat.{u₂}) [FiberFunctor F'] [FiberFunctor (H ⋙ F')]

/-- The pro-group `H(Π)`: the image of the fundamental pro-group of `C` under `H` is the pro-object
of `C'` corresponding to `π_F` with `π_{F'}` acting by conjugation through `u = ᵗH`. -/
noncomputable def proMapFundamentalProGroupIso :
    (proMap H F').obj (fundamentalProGroup (H ⋙ F')) ≅
      (proEquivalenceOfFiberFunctor F').inverse.obj (conjVia (autContinuousHom H F')) :=
  (proEquivalenceOfFiberFunctor F').inverse.mapIso
    ((ContAction.res _ (autContinuousHom H F')).mapIso
      ((proEquivalenceOfFiberFunctor (H ⋙ F')).counitIso.app _) ≪≫ resConjViaIso _ _)

/-- The group structure of the pro-group `H(Π)`: the groups `Hom(Q, H(Π))`, natural in `Q`. -/
noncomputable def proMapFundamentalProGroupGrp : (Pro C₂)ᵒᵖ ⥤ GrpCat.{u₂} :=
  (proEquivalenceOfFiberFunctor F').functor.op ⋙ conjGrp (autContinuousHom H F')

/-- `H(Π)` is a pro-group: it represents `proMapFundamentalProGroupGrp H F'`. -/
noncomputable def proMapFundamentalProGroupRepresentableBy :
    (proMapFundamentalProGroupGrp H F' ⋙ forget _).RepresentableBy
      ((proMap H F').obj (fundamentalProGroup (H ⋙ F'))) :=
  Functor.RepresentableBy.ofIsoObj
    { homEquiv := ((proEquivalenceOfFiberFunctor F').toAdjunction.homEquiv _ _).symm
      homEquiv_comp f g :=
        (proEquivalenceOfFiberFunctor F').toAdjunction.homEquiv_naturality_left_symm f g }
    (proMapFundamentalProGroupIso H F')

/-- `u = ᵗH : π_{F'} → π_F` as a morphism of group objects of `C'(π_{F'})`. -/
noncomputable def autContinuousHomConj :
    conj (Aut F') ⟶ conjVia (autContinuousHom H F') :=
  conjViaMap (u := ContinuousMonoidHom.id _) (autContinuousHom H F') fun _ ↦ rfl

/-- V.6: the homomorphism of fundamental pro-groups `Π' ⟶ H(Π)` associated with `H`. Under
V.5.2 it is `u = ᵗH : π_{F'} → π_F`, which commutes with the actions by conjugation. -/
noncomputable def fundamentalProGroupHom :
    fundamentalProGroup F' ⟶ (proMap H F').obj (fundamentalProGroup (H ⋙ F')) :=
  (proEquivalenceOfFiberFunctor F').inverse.map (autContinuousHomConj H F') ≫
    (proMapFundamentalProGroupIso H F').inv

lemma fundamentalProGroupHom_comp_hom :
    fundamentalProGroupHom H F' ≫ (proMapFundamentalProGroupIso H F').hom =
      (proEquivalenceOfFiberFunctor F').inverse.map (autContinuousHomConj H F') :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id _))).trans (Category.comp_id _)

/-- V.6: `fundamentalProGroupHom` is a homomorphism of pro-groups: on the points with values in
any pro-object `Q`, composition with it is the group homomorphism
`Hom(Q, Π') → Hom(Q, H(Π))` induced by `u`. -/
noncomputable def fundamentalProGroupHomGrp :
    fundamentalProGroupGrp F' ⟶ proMapFundamentalProGroupGrp H F' where
  app _ := GrpCat.ofHom
    { toFun f := f ≫ autContinuousHomConj H F'
      map_one' := conj_hom_ext fun _ ↦ map_one (autContinuousHom H F')
      map_mul' f f' := conjViaMap_mul _ _ f f' }
  naturality _ _ _ := rfl

/-- V.6: the natural transformation `fundamentalProGroupHomGrp` is the one represented by the
morphism `fundamentalProGroupHom`. -/
lemma fundamentalProGroupHomGrp_app_homEquiv {Q : Pro C₂} (f : Q ⟶ fundamentalProGroup F') :
    (fundamentalProGroupHomGrp H F').app (op Q)
        ((fundamentalProGroupRepresentableBy F').homEquiv f) =
      (proMapFundamentalProGroupRepresentableBy H F').homEquiv
        (f ≫ fundamentalProGroupHom H F') := by
  have key : (f ≫ fundamentalProGroupHom H F') ≫ (proMapFundamentalProGroupIso H F').hom =
      f ≫ (proEquivalenceOfFiberFunctor F').inverse.map (autContinuousHomConj H F') := by
    rw [Category.assoc, fundamentalProGroupHom_comp_hom]
  calc _ = ((proEquivalenceOfFiberFunctor F').toAdjunction.homEquiv _ _).symm
        (f ≫ (proEquivalenceOfFiberFunctor F').inverse.map (autContinuousHomConj H F')) :=
          ((proEquivalenceOfFiberFunctor F').toAdjunction.homEquiv_naturality_right_symm f _).symm
    _ = _ := by
      rw [← key]
      rfl

/-- The group `F'(H(Π)) = Hom(P_{F'}, H(Π))` is `π_F`, `F = F' ∘ H`. -/
noncomputable def proMapFundamentalProGroupFiberMulEquiv :
    (proMapFundamentalProGroupGrp H F').obj (op (fundamentalProObject F')) ≃* Aut (H ⋙ F') :=
  (((conjGrp (autContinuousHom H F')).mapIso
    ((proEquivalenceOfFiberFunctor F').counitIso.app
      (regular (Aut F'))).op).groupIsoToMulEquiv.symm).trans (regularHomConjMulEquiv _ _)

omit [GaloisCategory C₁] [FiberFunctor (H ⋙ F')] in
/-- V.6: on the fibres at `F'`, the homomorphism of fundamental pro-groups `Π' ⟶ H(Π)` is the
natural homomorphism `Aut F' → Aut (F' ∘ H)`, `σ ↦ σ ∘ H`. -/
theorem proMapFundamentalProGroupFiberMulEquiv_fundamentalProGroupHomGrp (σ : Aut F') :
    proMapFundamentalProGroupFiberMulEquiv H F'
      ((fundamentalProGroupHomGrp H F').app (op (fundamentalProObject F'))
        ((fundamentalProGroupFiberMulEquiv F').symm σ)) = autWhiskerLeft H F' σ := by
  let c := (proEquivalenceOfFiberFunctor F').counitIso.app (regular (Aut F'))
  let r := (regularHomConjMulEquiv (Aut F') (ContinuousMonoidHom.id _)).symm σ
  have h : c.inv ≫ (c.hom ≫ r) ≫ autContinuousHomConj H F' = r ≫ autContinuousHomConj H F' := by
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  change conjVal (c.inv ≫ (c.hom ≫ r) ≫ autContinuousHomConj H F') (toRegular _ 1) = _
  rw [h]
  change autWhiskerLeft H F' (1 * σ * 1⁻¹) = _
  simp

/-- V.6: transitivity of the homomorphisms of fundamental pro-groups: for exact functors
`H : C ⥤ C'`, `H' : C' ⥤ C''`, under V.5.2 the homomorphism associated with `H' ∘ H` is the
composite of the one associated with `H'` and the image under `H'` of the one associated with
`H` (as for the fundamental groups, `ᵗ(H' H) = ᵗH ᵗH'`). -/
lemma autContinuousHomConj_comp {C₃ : Type u₂} [SmallCategory C₃] [GaloisCategory C₃]
    (H' : C₂ ⥤ C₃) (F'' : C₃ ⥤ FintypeCat.{u₂}) [FiberFunctor F''] [FiberFunctor (H' ⋙ F'')]
    [FiberFunctor (H ⋙ H' ⋙ F'')] :
    haveI : FiberFunctor ((H ⋙ H') ⋙ F'') := inferInstanceAs (FiberFunctor (H ⋙ H' ⋙ F''))
    autContinuousHomConj (H ⋙ H') F'' =
      autContinuousHomConj H' F'' ≫
        (resConjViaIso (autContinuousHom H' F'') (ContinuousMonoidHom.id _)).inv ≫
        (ContAction.res _ (autContinuousHom H' F'')).map (autContinuousHomConj H (H' ⋙ F'')) ≫
        (resConjViaIso _ _).hom :=
  conj_hom_ext fun _ ↦ rfl

end ProGroupHom

end SGA.SGA1.ExposeV
