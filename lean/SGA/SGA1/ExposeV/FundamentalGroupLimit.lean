/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Passing to the limit over the finite subextensions of an algebraic extension

Let `E/k` be an algebraic field extension. Then `E` is the filtered colimit of its finite
subextensions `L` (`isColimitFiniteSubextCocone`), so `Spec E` is the limit of the `Spec L`, and for
a `k`-scheme `X` the base change `X ⊗_k E` is the limit of the `X ⊗_k L`
(`isLimitBaseChangeCone`), with affine transition morphisms. By EGA IV 8.8.2 (mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`), if `X` is quasi-compact and
quasi-separated, every morphism from `X ⊗_k E` to a scheme locally of finite presentation over a
base comes from some `X ⊗_k L` (`exists_finiteSubext_hom`).

This is the limit argument in the proof of SGA 1 IX.6.1 ("an étale covering of `X̄` comes from an
étale covering of some `X_i`"), in the part concerning morphisms.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Pasting

variable {C : Type*} [Category C] [HasPullbacks C]

/-- The morphism `X ×_B Y₁ ⟶ X ×_B Y₂` induced by `φ : Y₁ ⟶ Y₂` over `B` is the base change
of `φ`. -/
lemma isPullback_pullbackMap {X Y₁ Y₂ B : C} (h : X ⟶ B) (g₁ : Y₁ ⟶ B) (g₂ : Y₂ ⟶ B)
    (φ : Y₁ ⟶ Y₂) (hφ : φ ≫ g₂ = g₁) :
    IsPullback (pullback.map h g₁ h g₂ (𝟙 X) φ (𝟙 B) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hφ]))
      (pullback.snd h g₁) (pullback.snd h g₂) φ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst h g₂) (v₁₃ := h) (h₂₂ := g₂) ?_ ?_
    (IsPullback.of_hasPullback h g₂)
  · rw [pullback.lift_fst, Category.comp_id, hφ]
    exact IsPullback.of_hasPullback h g₁
  · exact pullback.lift_snd _ _ _

end Pasting

section FiniteSubextensions

variable (k : Type u) [Field k] (E : Type u) [Field E] [Algebra k E]

/-- The finite subextensions of `E/k`, ordered by inclusion. -/
abbrev FiniteSubext : Type u := {L : IntermediateField k E // FiniteDimensional k L}

instance : IsDirected (FiniteSubext k E) (· ≤ ·) where
  directed L₁ L₂ := by
    have := L₁.2
    have := L₂.2
    exact ⟨⟨L₁.1 ⊔ L₂.1, inferInstance⟩, (le_sup_left : L₁.1 ≤ L₁.1 ⊔ L₂.1),
      (le_sup_right : L₂.1 ≤ L₁.1 ⊔ L₂.1)⟩

instance : Nonempty (FiniteSubext k E) := ⟨⟨⊥, inferInstance⟩⟩



/-- The diagram of rings `L ↦ L` over the finite subextensions of `E/k`. -/
@[simps]
noncomputable abbrev finiteSubextDiagram : FiniteSubext k E ⥤ CommRingCat.{u} where
  obj L := CommRingCat.of L.1
  map {L L'} f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom

/-- The cocone of the inclusions `L ⟶ E`. -/
@[simps]
noncomputable abbrev finiteSubextCocone : Cocone (finiteSubextDiagram k E) where
  pt := CommRingCat.of E
  ι := { app L := CommRingCat.ofHom L.1.val.toRingHom }

variable [Algebra.IsAlgebraic k E]

/-- An algebraic extension `E/k` is the filtered colimit of its finite subextensions. -/
noncomputable def isColimitFiniteSubextCocone : IsColimit (finiteSubextCocone k E) := by
  have : ReflectsColimit (finiteSubextDiagram k E) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun (x : E) ↦ ?_)
    fun (i j : FiniteSubext k E) xi xj hij ↦ ?_)
  · have hx : _root_.IsIntegral k x := Algebra.IsIntegral.isIntegral x
    exact ⟨⟨IntermediateField.adjoin k {x}, IntermediateField.adjoin.finiteDimensional hx⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩, rfl⟩
  · obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact ⟨m, homOfLE him, homOfLE hjm, Subtype.ext hij⟩

/-- The morphism `Spec L ⟶ Spec k`. -/
noncomputable abbrev specFiniteSubextι (L : FiniteSubext k E) :
    Spec (CommRingCat.of L.1) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L.1))

omit [Algebra.IsAlgebraic k E] in
@[reassoc (attr := simp)]
lemma algebraMap_comp_finiteSubextDiagram_map {L L' : FiniteSubext k E} (f : L ⟶ L') :
    CommRingCat.ofHom (algebraMap k L.1) ≫ (finiteSubextDiagram k E).map f =
      CommRingCat.ofHom (algebraMap k L'.1) :=
  rfl

omit [Algebra.IsAlgebraic k E] in
@[reassoc (attr := simp)]
lemma algebraMap_comp_finiteSubextCocone_ι (L : FiniteSubext k E) :
    CommRingCat.ofHom (algebraMap k L.1) ≫ (finiteSubextCocone k E).ι.app L =
      CommRingCat.ofHom (algebraMap k E) :=
  rfl

/-- The diagram of the `Spec L`. -/
@[simps]
noncomputable abbrev specFiniteSubextDiagram : (FiniteSubext k E)ᵒᵖ ⥤ Scheme.{u} where
  obj L := Spec (CommRingCat.of L.unop.1)
  map f := Spec.map ((finiteSubextDiagram k E).map f.unop)
  map_id L := by
    rw [unop_id, CategoryTheory.Functor.map_id]
    exact Spec.map_id _
  map_comp f g := by
    rw [unop_comp, CategoryTheory.Functor.map_comp]
    exact Spec.map_comp _ _

omit [Algebra.IsAlgebraic k E] in
@[reassoc (attr := simp)]
lemma specFiniteSubextDiagram_map_ι {L L' : (FiniteSubext k E)ᵒᵖ} (f : L ⟶ L') :
    (specFiniteSubextDiagram k E).map f ≫ specFiniteSubextι k E L'.unop =
      specFiniteSubextι k E L.unop := by
  rw [specFiniteSubextDiagram_map, ← Spec.map_comp, algebraMap_comp_finiteSubextDiagram_map]

/-- The cone of the `Spec L` with vertex `Spec E`. -/
@[simps]
noncomputable abbrev specFiniteSubextCone : Cone (specFiniteSubextDiagram k E) where
  pt := Spec (CommRingCat.of E)
  π :=
    { app L := Spec.map ((finiteSubextCocone k E).ι.app L.unop)
      naturality L L' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (congrArg Spec.map ((finiteSubextCocone k E).w f.unop)).symm.trans
          (Spec.map_comp _ _) }

omit [Algebra.IsAlgebraic k E] in
@[reassoc (attr := simp)]
lemma specFiniteSubextCone_π_app_ι (L : (FiniteSubext k E)ᵒᵖ) :
    (specFiniteSubextCone k E).π.app L ≫ specFiniteSubextι k E L.unop =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  rw [specFiniteSubextCone_π_app, ← Spec.map_comp, algebraMap_comp_finiteSubextCocone_ι]

/-- `Spec E` is the limit of the `Spec L`, `L` running over the finite subextensions of `E/k`. -/
noncomputable def isLimitSpecFiniteSubextCone : IsLimit (specFiniteSubextCone k E) :=
  isLimitOfPreserves Scheme.Spec (isColimitFiniteSubextCocone k E).op

variable {k E} {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of k))

/-- The diagram of the base changes `X ⊗_k L` over the finite subextensions `L` of `E/k`. -/
noncomputable abbrev baseChangeDiagram : (FiniteSubext k E)ᵒᵖ ⥤ Scheme.{u} where
  obj L := pullback h (specFiniteSubextι k E L.unop)
  map {L L'} f := pullback.map _ _ _ _ (𝟙 X) ((specFiniteSubextDiagram k E).map f) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by simp only [Category.comp_id]; exact (specFiniteSubextDiagram_map_ι k E f).symm)
  map_id L := by
    convert pullback.map_id using 2
    exact (specFiniteSubextDiagram k E).map_id L
  map_comp f g := by
    rw [pullback.map_comp]
    congr 1
    exact (specFiniteSubextDiagram k E).map_comp f g

/-- The projections `X ⊗_k L ⟶ Spec L`. -/
noncomputable def baseChangeDiagramSnd :
    baseChangeDiagram (E := E) h ⟶ specFiniteSubextDiagram k E where
  app _ := pullback.snd _ _
  naturality _ _ _ := pullback.lift_snd _ _ _

/-- The projections `X ⊗_k E ⟶ X ⊗_k L`. -/
noncomputable abbrev baseChangeConeπ (L : (FiniteSubext k E)ᵒᵖ) :
    pullback h (Spec.map (CommRingCat.ofHom (algebraMap k E))) ⟶
      pullback h (specFiniteSubextι k E L.unop) :=
  pullback.map _ _ _ _ (𝟙 X) ((specFiniteSubextCone k E).π.app L) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by simp only [Category.comp_id]; exact (specFiniteSubextCone_π_app_ι k E L).symm)

omit [Algebra.IsAlgebraic k E] in
lemma baseChangeConeπ_comp_map {L L' : (FiniteSubext k E)ᵒᵖ} (f : L ⟶ L') :
    baseChangeConeπ h L ≫ (baseChangeDiagram h).map f = baseChangeConeπ h L' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    congr 1
    exact (specFiniteSubextCone k E).w f

/-- The cone of the `X ⊗_k L` with vertex `X ⊗_k E`. -/
noncomputable abbrev baseChangeCone : Cone (baseChangeDiagram (E := E) h) where
  pt := pullback h (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  π :=
    { app L := baseChangeConeπ h L
      naturality _ _ f := (Category.id_comp _).trans (baseChangeConeπ_comp_map h f).symm }

omit [Algebra.IsAlgebraic k E] in
lemma isPullback_baseChangeConeπ (L : (FiniteSubext k E)ᵒᵖ) :
    IsPullback (baseChangeConeπ h L)
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (pullback.snd h (specFiniteSubextι k E L.unop)) ((specFiniteSubextCone k E).π.app L) :=
  isPullback_pullbackMap h _ _ _ (specFiniteSubextCone_π_app_ι k E L)

instance {L L' : (FiniteSubext k E)ᵒᵖ} (f : L ⟶ L') : IsAffineHom ((baseChangeDiagram h).map f) :=
  MorphismProperty.of_isPullback (isPullback_pullbackMap h _ _ _
    (specFiniteSubextDiagram_map_ι k E f)).flip inferInstance

attribute [local instance] IsCofiltered.isConnected in
/-- The base change `X ⊗_k E` is the limit of the `X ⊗_k L`, `L` running over the finite
subextensions of the algebraic extension `E/k`. -/
noncomputable def isLimitBaseChangeCone : IsLimit (baseChangeCone (E := E) h) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramSnd h) (baseChangeCone h)
    (specFiniteSubextCone k E)
    { hom := pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      w _ := (pullback.lift_snd _ _ _).symm }
    (fun L ↦ isPullback_baseChangeConeπ h L) (isLimitSpecFiniteSubextCone k E)

instance [CompactSpace X] (L : (FiniteSubext k E)ᵒᵖ) :
    CompactSpace ((baseChangeDiagram h).obj L) := by
  have : QuasiCompact (pullback.fst h (specFiniteSubextι k E L.unop)) := inferInstance
  exact isCompact_univ_iff.mp (by
    simpa using QuasiCompact.isCompact_preimage (f := pullback.fst h (specFiniteSubextι k E L.unop))
      Set.univ isOpen_univ isCompact_univ)

instance [QuasiSeparatedSpace X] (L : (FiniteSubext k E)ᵒᵖ) :
    QuasiSeparatedSpace ((baseChangeDiagram h).obj L) := by
  have : QuasiSeparated (pullback.fst h (specFiniteSubextι k E L.unop)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst h (specFiniteSubextι k E L.unop))

/-- EGA IV 8.8.2 for morphisms (Stacks 01ZC): let `X` be a quasi-compact and quasi-separated
scheme over a field `k`, `E/k` an algebraic extension, `p : V ⟶ W` locally of finite presentation
and `π : X ⟶ W`. Every `W`-morphism `X ⊗_k E ⟶ V` comes from a `W`-morphism `X ⊗_k L ⟶ V` for some
finite subextension `L` of `E/k`. -/
theorem exists_finiteSubext_hom [CompactSpace X] [QuasiSeparatedSpace X] {V W : Scheme.{u}}
    (p : V ⟶ W) [LocallyOfFinitePresentation p] (π : X ⟶ W)
    (a : pullback h (Spec.map (CommRingCat.ofHom (algebraMap k E))) ⟶ V)
    (ha : a ≫ p = pullback.fst _ _ ≫ π) :
    ∃ (L : FiniteSubext k E) (b : pullback h (specFiniteSubextι k E L) ⟶ V),
      (baseChangeCone h).π.app (op L) ≫ b = a ∧ b ≫ p = pullback.fst _ _ ≫ π := by
  let t : baseChangeDiagram (E := E) h ⟶ (Functor.const _).obj W :=
    { app L := pullback.fst _ _ ≫ π
      naturality L L' f := by
        simp only [Functor.const_obj_map]
        exact (pullback.lift_fst_assoc _ _ _ _).trans
          (by rw [Category.comp_id]; exact (Category.comp_id _).symm) }
  obtain ⟨L, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram h) t p (baseChangeCone h) (isLimitBaseChangeCone h) a (by
      ext L
      simp only [NatTrans.comp_app, Functor.const_map_app, t]
      exact (pullback.lift_fst_assoc _ _ _ _).trans (by rw [Category.comp_id, ha]))
  exact ⟨L.unop, b, hb, hb'⟩

end FiniteSubextensions

end SGA.SGA1.ExposeV
