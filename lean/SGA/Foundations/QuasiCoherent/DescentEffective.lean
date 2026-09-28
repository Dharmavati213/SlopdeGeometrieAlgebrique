/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.DescentLocalizing

/-!
# Effectiveness of fpqc descent for quasi-coherent modules

Let `g : S' ⟶ S` be faithfully flat and quasi-compact, and `E` a quasi-coherent module on `S'`
with a descent datum `D` relative to `g`. The descended module `M = descentModule D` is
quasi-coherent (`isQuasicoherent_descentModule`, in `DescentLocalizing`). Here we show that the
counit `g^* M ⟶ E` is an isomorphism (`isIso_descentCounit`), so that `D` is isomorphic to the
descent datum of `g^* M` (`descentIso`). This is SGA 1 VIII.1.3 (Stacks, Tag 023T).

Over an affine chart `h : Spec B ⟶ S'` over an affine open `j : Spec A ⟶ S`, the global sections
of `j^* M` are the `A`-submodule of `Γ(Spec B, h^* E)` cut out by the descent datum
(`range_ψL`), so `B ⊗_A Γ(j^* M) ≅ Γ(h^* E)` by the flat-descent computation
`bijective_liftBaseChange_invariants`; hence `(Spec φ ≫ j)^* M ≅ h^* E`
(`isIso_mapT`), and the counit is an isomorphism locally on `S'`.

## Main results

* `Scheme.Modules.isIso_descentCounit`: the counit `g^* M ⟶ E` is an isomorphism.
* `Scheme.Modules.descentIso`: the isomorphism of descent data `g^* M ≅ D`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

/-- If `ψ : P → N` is an injective `A`-linear map onto a submodule `L` of a `B`-module `N` with
`B ⊗_A L ≅ N`, then `B ⊗_A P ≅ N`. -/
lemma LinearMap.bijective_liftBaseChange_of_range {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {N P : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [AddCommGroup P] [Module A P] (L : Submodule A N)
    (hL : Function.Bijective (LinearMap.liftBaseChange B L.subtype))
    (ψ : P →ₗ[A] N) (hinj : Function.Injective ψ) (hrange : LinearMap.range ψ = L) :
    Function.Bijective (LinearMap.liftBaseChange B ψ) := by
  let e : P ≃ₗ[A] L := (LinearEquiv.ofInjective ψ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have h : ⇑(LinearMap.liftBaseChange B ψ) =
      ⇑(LinearMap.liftBaseChange B L.subtype) ∘ ⇑(LinearEquiv.baseChange A B P L e) := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, Function.comp_apply]
    | add y y' hy hy' =>
      simp only [map_add, Function.comp_apply] at hy hy' ⊢
      rw [hy, hy']
    | tmul b p =>
      simp only [Function.comp_apply, LinearEquiv.baseChange_tmul, LinearMap.liftBaseChange_tmul,
        Submodule.coe_subtype]
      rfl
  rw [h]
  exact hL.comp (LinearEquiv.baseChange A B P L e).bijective

namespace AlgebraicGeometry

open Scheme.Modules

namespace Scheme.Modules.AffineChart

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {A : CommRingCat.{u}} {j : Spec A ⟶ S}
  [IsOpenImmersion j] (c : AffineChart g j) (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

attribute [local instance] AffineChart.algebra AffineChart.moduleN AffineChart.moduleBG
  AffineChart.moduleAG

omit [IsOpenImmersion j] in
lemma mapΨ_app_top_smul (a : A) (x : Γ((Scheme.Modules.pullback j).obj (descentModule D), ⊤)) :
    (c.mapΨ D).app ⊤ (a • x) = c.φ a • (c.mapT D).app _
      (pullbackApp (Spec.map c.φ) ((Scheme.Modules.pullback j).obj (descentModule D)) ⊤ x) := by
  rw [mapΨ_app, pullbackApp_SpecMap_smul, Hom.app_smul_Spec]

omit [IsOpenImmersion j] in
/-- `Ψ` on global sections, as an `A`-linear map. -/
noncomputable def ψL :
    ((Scheme.Modules.pullback j).obj (descentModule D)).ΓSpec →ₗ[A]
      Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) where
  toFun x := (c.mapΨ D).app ⊤ x
  map_add' := map_add _
  map_smul' a x := c.mapΨ_app_top_smul D a x

omit [IsOpenImmersion j] in
lemma ψL_apply (x : Γ((Scheme.Modules.pullback j).obj (descentModule D), ⊤)) :
    c.ψL D x = (c.mapΨ D).app ⊤ x := rfl

omit [IsOpenImmersion j] in
lemma mapT_app_pullbackAppTop (p : Γ((Scheme.Modules.pullback j).obj (descentModule D), ⊤)) :
    (c.mapT D).app ⊤ (pullbackAppTop (Spec.map c.φ) _ ⊤ (top_le_preimage_top _) p) =
      (c.mapΨ D).app ⊤ p := by
  rw [mapΨ_app]
  have h := Hom.app_map (c.mapT D) (homOfLE (top_le_preimage_top (Spec.map c.φ)))
    (pullbackApp (Spec.map c.φ) _ ⊤ p)
  have e : homOfLE (top_le_preimage_top (Spec.map c.φ)) = 𝟙 (⊤ : (Spec c.B).Opens) :=
    Subsingleton.elim _ _
  rw [e] at h
  exact h.trans (presheaf_map_id_apply _ _ _)

lemma range_ψL :
    LinearMap.range (c.ψL D) = LinearMap.eqLocus ((c.θL D).restrictScalars A) (c.πL D) := by
  ext t
  rw [LinearMap.mem_eqLocus, LinearMap.restrictScalars_apply, θL_apply, πL_apply]
  constructor
  · rintro ⟨x, rfl⟩
    have h : (c.mapΘ D).app ⊤ ((c.mapΨ D).app ⊤ x) = (c.mapΞ D).app ⊤ ((c.mapΨ D).app ⊤ x) := by
      have h := congrArg (fun f ↦ f.app ⊤ x) (c.mapΨ_comp_mapΘ D)
      exact (Hom.comp_app_apply _ _ _ _).symm.trans (h.trans (Hom.comp_app_apply _ _ _ _))
    exact (mapΘ_app_top c D _).symm.trans (h.trans (mapΞ_app_top c D _))
  · intro ht
    obtain ⟨x, hx⟩ := c.exists_mapΨ_app_top_eq D t 
      ((mapΘ_app_top c D t).trans (ht.trans (mapΞ_app_top c D t).symm))
    exact ⟨x, hx⟩

variable [(descentObj D).IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in
lemma bijective_mapT_app_top : Function.Bijective ((c.mapT D).app ⊤) := by
  have := c.isQuasicoherent_pullback_descentModule D
  let P := (Scheme.Modules.pullback j).obj (descentModule D)
  let e := pullbackSpecMapΓAddEquiv c.φ P
  have hψ := LinearMap.bijective_liftBaseChange_of_range _
    (c.bijective_liftBaseChange_invariants D) (c.ψL D) (c.mapΨ_app_injective D ⊤) (c.range_ψL D)
  let f₁ : (ModuleCat.extendScalars c.φ.hom).obj P.ΓSpec →+
      Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) :=
    ((c.mapT D).app ⊤).hom.comp e.symm.toAddMonoidHom
  let f₂ : (ModuleCat.extendScalars c.φ.hom).obj P.ΓSpec →+
      Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) :=
    (LinearMap.liftBaseChange c.B (c.ψL D)).toAddMonoidHom
  have h₁₂ : f₁ = f₂ := by
    refine extendScalars_addHom_ext f₁ f₂ (fun b y ↦ ?_) (fun b y ↦ ?_) (fun p ↦ ?_)
    · change (c.mapT D).app ⊤ (e.symm (b • y)) = b • (c.mapT D).app ⊤ (e.symm y)
      rw [← Hom.app_smul_Spec]
      congr 1
      rw [AddEquiv.symm_apply_eq, pullbackSpecMapΓAddEquiv_smul, AddEquiv.apply_symm_apply]
    · exact (LinearMap.liftBaseChange c.B (c.ψL D)).map_smul b y
    · change (c.mapT D).app ⊤ (e.symm (oneTmul P.ΓSpec c.φ p)) =
        LinearMap.liftBaseChange c.B (c.ψL D) ((1 : c.B) ⊗ₜ p)
      rw [LinearMap.liftBaseChange_tmul, one_smul, ψL_apply, ← mapT_app_pullbackAppTop,
        ← pullbackSpecMapΓAddEquiv_pullbackAppTop c.φ P p, AddEquiv.symm_apply_apply]
  have e' : ⇑((c.mapT D).app ⊤) = ⇑f₂ ∘ ⇑e := by
    funext z
    rw [← h₁₂]
    change _ = (c.mapT D).app ⊤ (e.symm (e z))
    rw [AddEquiv.symm_apply_apply]
  rw [e']
  exact hψ.comp e.bijective

instance isIso_mapT : IsIso (c.mapT D) := by
  have := c.isQuasicoherent_pullback_descentModule D
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  refine isLocalizing_of_isIso_app_top ?_ ?_ ?_
  · rw [ConcreteCategory.isIso_iff_bijective]
    exact c.bijective_mapT_app_top D
  · rw [← isIso_fromTildeΓ_iff_isLocalizing]
    infer_instance
  · rw [← isIso_fromTildeΓ_iff_isLocalizing]
    infer_instance

lemma isIso_pullback_map_descentCounit :
    IsIso ((Scheme.Modules.pullback c.h).map (descentCounit D)) := by
  have : IsIso (((pullbackCompIso' (Spec.map c.φ) j (Spec.map c.φ ≫ j) rfl
      (descentModule D)).inv ≫ (pullbackCompIso' c.h g (Spec.map c.φ ≫ j) c.comm
      (descentModule D)).hom) ≫ (Scheme.Modules.pullback c.h).map (descentCounit D)) := by
    rw [Category.assoc]
    exact c.isIso_mapT D
  exact IsIso.of_isIso_comp_left ((pullbackCompIso' (Spec.map c.φ) j (Spec.map c.φ ≫ j) rfl
      (descentModule D)).inv ≫ (pullbackCompIso' c.h g (Spec.map c.φ ≫ j) c.comm
      (descentModule D)).hom) ((Scheme.Modules.pullback c.h).map (descentCounit D))

end Scheme.Modules.AffineChart

namespace Scheme.Modules

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- VIII.1.3: for a faithfully flat quasi-compact `g`, the counit `g^* M ⟶ E` of the module `M`
obtained by descent of a quasi-coherent module `E` is an isomorphism. -/
theorem isIso_descentCounit [Flat g] [Surjective g] [QuasiCompact g]
    [(descentObj D).IsQuasicoherent] : IsIso (descentCounit D) := by
  let c : ∀ V : S.affineOpens, AffineChart g V.2.fromSpec :=
    fun V ↦ haveI := V.2.isOpenImmersion_fromSpec
      (AffineChart.nonempty (g := g) V.2.fromSpec).some
  choose U hU hU' using fun p : Σ V : S.affineOpens, Spec (c V).B ↦
    @IsLocalIso.exists_isOpenImmersion _ _ _ (c p.1).isLocalIso p.2
  have : ∀ p, IsOpenImmersion ((fun p ↦ (U p).ι ≫ (c p.1).h) p) := hU'
  have : ∀ p, IsIso ((Scheme.Modules.pullback ((fun p ↦ (U p).ι ≫ (c p.1).h) p)).map
      (descentCounit D)) := by
    intro p
    have : IsOpenImmersion p.1.2.fromSpec := p.1.2.isOpenImmersion_fromSpec
    have := (c p.1).isIso_pullback_map_descentCounit D
    exact (NatIso.isIso_map_iff (pullbackComp (U p).ι (c p.1).h) _).mp
      (inferInstanceAs (IsIso ((Scheme.Modules.pullback (U p).ι).map
        ((Scheme.Modules.pullback (c p.1).h).map (descentCounit D)))))
  refine isIso_of_isIso_pullback (fun p ↦ (U p).ι ≫ (c p.1).h) (fun x ↦ ?_) (descentCounit D)
  obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g x ∈ (⊤ : S.Opens) from trivial)
  have hx : x ∈ Set.range (c ⟨V, hV⟩).h := by
    rw [(c ⟨V, hV⟩).range_eq]
    change g x ∈ Set.range hV.fromSpec
    rw [hV.range_fromSpec]
    exact hxV
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨⟨V, hV⟩, y⟩, ⟨⟨y, hU _⟩, rfl⟩⟩

/-- VIII.1.3: a descent datum on a quasi-coherent module relative to a faithfully flat
quasi-compact morphism is isomorphic to the descent datum of the inverse image of the descended
module. -/
noncomputable def descentIso [Flat g] [Surjective g] [QuasiCompact g]
    [(descentObj D).IsQuasicoherent] :
    (pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj (descentModule D) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun _ ↦ @asIso _ _ _ _ (descentCounit D) (isIso_descentCounit D))
    (fun _ q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ descentCounit_comm'' D q i₁ i₂ f₁ f₂ hf₁ hf₂)

end Scheme.Modules

end AlgebraicGeometry
