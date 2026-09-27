/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.ClovenFunctors
import SGA.SGA1.ExposeVI.FamilyProducts

/-!
# SGA 1, Exposé VI, end of VI.12: `E`-functors between cloven categories

Let `K`, `K'` be cleavages of `𝒳` and `𝒴` over `E`. An `E`-functor `F : 𝒳 ⥤ 𝒴` gives functors
`F_S : 𝒳_S ⥤ 𝒴_S` and homomorphisms `φ_f : F_T f^* ⟶ f^* F_S` (`basedConstraint`) satisfying
a′) and b′). SGA leaves to the reader "the statement and the proof of the analogue of VI.12.1,
implying that one thus obtains a bijective correspondence between the set of `E`-functors from
`𝒳` to `𝒴` and the set of systems `(F_S), (φ_f)` satisfying a′) and b′)": this is
`BasedFunctorSystem.equiv`. As in `ClovenFunctors.lean`, the cleavages need not be normalized;
a′) then reads `φ_{𝟙_S} ≫ α′_{𝟙_S} = F_S(α_{𝟙_S})`, which is SGA's `φ_{𝟙_S} = id` for normalized
cleavages. The cartesian functors are those with invertible `φ_f`
(`isCartesianFunctor_iff_basedConstraint_isIso`).
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {X : BasedCategory.{v₁, u₁} E}
  {Y : BasedCategory.{v₂, u₂} E} (K : Cleavage X.p) (K' : Cleavage Y.p)

/-- VI.12: systems `(F_S), (φ_f)` of functors between the fibers and homomorphisms
`φ_f : F_T f^* ⟶ f^* F_S` satisfying a′) and b′). -/
structure BasedFunctorSystem where
  /-- The functors `F_S : 𝒳_S ⥤ 𝒴_S`. -/
  obj (S : E) : Fiber X.p S ⥤ Fiber Y.p S
  /-- The homomorphisms `φ_f : F_T f^* ⟶ f^* F_S`. -/
  φ {T S : E} (f : T ⟶ S) : K.pullback f ⋙ obj T ⟶ obj S ⋙ K'.pullback f
  /-- a′), for arbitrary cleavages: `φ_{𝟙_S} ≫ α′_{𝟙_S} = F_S(α_{𝟙_S})`. -/
  φ_id (S : E) (ξ : Fiber X.p S) :
    (φ (𝟙 S)).app ξ ≫ K'.transportId S ((obj S).obj ξ) = (obj S).map (K.transportId S ξ)
  /-- b′): `φ_{fg} ∘ F_U(c_{f,g}) = c′_{f,g}(F_S) ∘ g^*(φ_f) ∘ φ_g(f^*)`. -/
  φ_comp {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber X.p S) :
    (obj U).map (K.comparison f g ξ) ≫ (φ (g ≫ f)).app ξ =
      (φ g).app ((K.pullback f).obj ξ) ≫ (K'.pullback g).map ((φ f).app ξ) ≫
        K'.comparison f g ((obj S).obj ξ)

namespace BasedFunctorSystem

variable {K K'}

/-- Systems are equal when their fiber functors are equal and their `φ_f` agree up to the
resulting identifications. -/
theorem ext' {Φ Ψ : BasedFunctorSystem K K'} (h : ∀ S, Φ.obj S = Ψ.obj S)
    (hφ : ∀ {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S), ((Φ.φ f).app ξ).val =
      eqToHom (by rw [h T]) ≫ ((Ψ.φ f).app ξ).val ≫ eqToHom (by rw [h S])) : Φ = Ψ := by
  obtain ⟨obj, φ, _, _⟩ := Φ
  obtain ⟨obj', φ', _, _⟩ := Ψ
  obtain rfl : obj = obj' := funext h
  obtain rfl : @φ = @φ' := by
    funext T S f
    ext ξ
    have := hφ f ξ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at this
    exact this
  rfl

variable (K K')

/-- VI.12: the system `((F_S), (φ_f))` of an `E`-functor. -/
noncomputable def ofBasedFunctor (F : BasedFunctor X Y) : BasedFunctorSystem K K' where
  obj S := fiberMap F S
  φ f := basedConstraint K K' F f
  φ_id S ξ := Subtype.ext (basedConstraintApp_fac K K' F (𝟙 S) ξ)
  φ_comp f g ξ := Subtype.ext (basedConstraint_comp K K' F f g ξ)

variable {K K'}

/-- The underlying system of functors to the total category `𝒴` (VI.12.1 with `𝒞 = 𝒴`). -/
noncomputable def toFiberFunctorSystem (Φ : BasedFunctorSystem K K') :
    FiberFunctorSystem K Y.obj where
  obj S := Φ.obj S ⋙ Fiber.fiberInclusion
  φ {T S} f :=
    { app := fun ξ ↦ ((Φ.φ f).app ξ).val ≫ K'.transport f ((Φ.obj S).obj ξ)
      naturality := fun {ξ η} u ↦ by
        have h₁ := congrArg Subtype.val ((Φ.φ f).naturality u)
        simp only [Functor.comp_map, fiber_comp_val] at h₁
        change ((Φ.obj T).map ((K.pullback f).map u)).val ≫ ((Φ.φ f).app η).val ≫
            K'.transport f ((Φ.obj S).obj η) =
          (((Φ.φ f).app ξ).val ≫ K'.transport f ((Φ.obj S).obj ξ)) ≫ ((Φ.obj S).map u).val
        rw [reassoc_of% h₁, Category.assoc, K'.transport_naturality] }
  φ_id S ξ := by
    change ((Φ.φ (𝟙 S)).app ξ).val ≫ K'.transport (𝟙 S) ((Φ.obj S).obj ξ) =
      ((Φ.obj S).map (K.transportId S ξ)).val
    exact congrArg Subtype.val (Φ.φ_id S ξ)
  φ_comp {U T S} f g ξ := by
    change ((Φ.obj U).map (K.comparison f g ξ)).val ≫ ((Φ.φ (g ≫ f)).app ξ).val ≫
        K'.transport (g ≫ f) ((Φ.obj S).obj ξ) =
      (((Φ.φ g).app ((K.pullback f).obj ξ)).val ≫
        K'.transport g ((Φ.obj T).obj ((K.pullback f).obj ξ))) ≫
          ((Φ.φ f).app ξ).val ≫ K'.transport f ((Φ.obj S).obj ξ)
    have h := congrArg Subtype.val (Φ.φ_comp f g ξ)
    simp only [fiber_comp_val] at h
    rw [reassoc_of% h, Cleavage.comparison_fac, Cleavage.transport_naturality_assoc]
    simp only [Category.assoc]

/-- VI.12: the `E`-functor reconstructed from a system satisfying a′) and b′). -/
noncomputable def toBasedFunctor (Φ : BasedFunctorSystem K K') : BasedFunctor X Y where
  toFunctor := Φ.toFiberFunctorSystem.toFunctor
  w := by
    refine functor_comp_eq_of_isHomLift _ _ _ (fun x ↦ ((Φ.obj _).obj _).property)
      fun {x y} φ ↦ ?_
    change IsHomLift Y.p (X.p.map φ)
      (((Φ.obj (X.p.obj x)).map (FiberFunctorSystem.verticalPart (K := K)
        (FiberFunctorSystem.fiberOf x) (FiberFunctorSystem.fiberOf y) (X.p.map φ) φ)).val ≫
      ((Φ.φ (X.p.map φ)).app (FiberFunctorSystem.fiberOf y)).val ≫
        K'.transport (X.p.map φ) ((Φ.obj _).obj (FiberFunctorSystem.fiberOf y)))
    infer_instance

theorem toFiberFunctorSystem_ofBasedFunctor (F : BasedFunctor X Y) :
    (ofBasedFunctor K K' F).toFiberFunctorSystem = FiberFunctorSystem.ofFunctorObj F.toFunctor :=
  FiberFunctorSystem.ext' (fun _ ↦ rfl) fun {T S} f ξ ↦ by
    change _ = eqToHom rfl ≫ _ ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp]
    exact (basedConstraintApp_fac K K' F f ξ).trans (Category.comp_id _).symm

/-- VI.12: `F ↦ ((F_S), (φ_f)) ↦ F` is the identity. -/
theorem toBasedFunctor_ofBasedFunctor (F : BasedFunctor X Y) :
    (ofBasedFunctor K K' F).toBasedFunctor = F := by
  apply basedFunctor_ext
  change (ofBasedFunctor K K' F).toFiberFunctorSystem.toFunctor = F.toFunctor
  rw [toFiberFunctorSystem_ofBasedFunctor]
  exact FiberFunctorSystem.toFunctor_ofFunctorObj F.toFunctor

theorem toBasedFunctor_obj (Φ : BasedFunctorSystem K K') {S : E} (ξ : Fiber X.p S) :
    Φ.toBasedFunctor.obj ξ.val = ((Φ.obj S).obj ξ).val :=
  Φ.toFiberFunctorSystem.toFunctor_obj_eq ξ

/-- The fiber functors of the reconstructed `E`-functor are the given ones. -/
theorem fiberMap_toBasedFunctor (Φ : BasedFunctorSystem K K') (S : E) :
    fiberMap Φ.toBasedFunctor S = Φ.obj S := by
  have h := congrArg (fun Θ ↦ Θ.obj S) Φ.toFiberFunctorSystem.ofFunctorObj_toFunctor
  refine CategoryTheory.Functor.ext (fun ξ ↦ Subtype.ext (Φ.toBasedFunctor_obj ξ))
    fun ξ η u ↦ Subtype.ext ?_
  have := Functor.congr_hom h u
  erw [fiber_comp_val, fiber_comp_val, fiber_eqToHom_val, fiber_eqToHom_val]
  exact this

theorem toBasedFunctor_map_transport (Φ : BasedFunctorSystem K K') {T S : E} (f : T ⟶ S)
    (ξ : Fiber X.p S) :
    Φ.toBasedFunctor.map (K.transport f ξ) =
      eqToHom (Φ.toBasedFunctor_obj _) ≫ ((Φ.φ f).app ξ).val ≫
        K'.transport f ((Φ.obj S).obj ξ) ≫ eqToHom (Φ.toBasedFunctor_obj ξ).symm := by
  change Φ.toFiberFunctorSystem.mapAux (FiberFunctorSystem.fiberOf _)
    (FiberFunctorSystem.fiberOf ξ.val) (X.p.map (K.transport f ξ)) (K.transport f ξ) = _
  rw [Φ.toFiberFunctorSystem.mapAux_rep ((K.pullback f).obj ξ) ξ f (K.transport f ξ)]
  have : FiberFunctorSystem.verticalPart (K := K) ((K.pullback f).obj ξ) ξ f (K.transport f ξ) =
      𝟙 _ := Subtype.ext (IsCartesian.map_self X.p f _)
  simp only [FiberFunctorSystem.mapAux, this, Functor.map_id, Category.id_comp]
  change eqToHom _ ≫ (((Φ.φ f).app ξ).val ≫ K'.transport f ((Φ.obj S).obj ξ)) ≫ eqToHom _ = _
  simp only [Category.assoc]
  rfl

omit [Category.{v, u} E] in
theorem eqToHom_sandwich {C : Type*} [Category C] {P A B B' D Q : C} (v : A ⟶ B) (t : B ⟶ D)
    (h₁ h₁' : P = A) (h₂ : B = B') (h₃ : B' = B) (h₄ h₄' : D = Q) :
    eqToHom h₁ ≫ v ≫ t ≫ eqToHom h₄ =
      (eqToHom h₁' ≫ v ≫ eqToHom h₂) ≫ eqToHom h₃ ≫ t ≫ eqToHom h₄' := by
  subst h₂
  simp

omit [Category.{v, u} E] in
theorem transport_eq_eqToHom {E : Type u} [Category.{v} E] {Y : BasedCategory.{v₂, u₂} E}
    (K' : Cleavage Y.p) {R S : E} (f : R ⟶ S) {ζ ζ' : Fiber Y.p S} (h : ζ = ζ') :
    K'.transport f ζ = eqToHom (by rw [h]) ≫ K'.transport f ζ' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- VI.12: `((F_S), (φ_f)) ↦ F ↦ ((F_S), (φ_f))` is the identity. -/
theorem ofBasedFunctor_toBasedFunctor (Φ : BasedFunctorSystem K K') :
    ofBasedFunctor K K' Φ.toBasedFunctor = Φ := by
  refine ext' (fiberMap_toBasedFunctor Φ) fun {T S} f ξ ↦ ?_
  have hζ := Functor.congr_obj (fiberMap_toBasedFunctor Φ S) ξ
  have ht := transport_eq_eqToHom K' f hζ
  have hv : IsHomLift Y.p (𝟙 T) ((Φ.φ f).app ξ).val := ((Φ.φ f).app ξ).property
  change basedConstraintApp K K' Φ.toBasedFunctor f ξ = _
  refine @IsCartesian.ext _ _ _ _ Y.p _ _ _ _ f
    (K'.transport f ((fiberMap Φ.toBasedFunctor S).obj ξ)) inferInstance _ _ _ inferInstance
    (IsHomLift.of_fac' _ _ _ ((fiberMap Φ.toBasedFunctor T).obj ((K.pullback f).obj ξ)).property
      ((K'.pullback f).obj ((fiberMap Φ.toBasedFunctor S).obj ξ)).property
      (by
        erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
          IsHomLift.fac' Y.p (𝟙 T) ((Φ.φ f).app ξ).val]
        simp)) ?_
  rw [basedConstraintApp_fac, toBasedFunctor_map_transport, ht]
  exact eqToHom_sandwich _ _ _ _ _ _ _ _

/-- VI.12: `E`-functors between cloven categories correspond bijectively to systems
`(F_S), (φ_f)` satisfying a′) and b′). -/
noncomputable def equiv : BasedFunctor X Y ≃ BasedFunctorSystem K K' where
  toFun := ofBasedFunctor K K'
  invFun := toBasedFunctor
  left_inv := toBasedFunctor_ofBasedFunctor
  right_inv := ofBasedFunctor_toBasedFunctor

end BasedFunctorSystem

end SGA.SGA1.ExposeVI
