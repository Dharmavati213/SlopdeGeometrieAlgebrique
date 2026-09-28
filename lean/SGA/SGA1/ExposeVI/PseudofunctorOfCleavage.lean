/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.LaxCoGrothendieck
import SGA.SGA1.ExposeVI.FamilyProducts
import SGA.SGA1.ExposeVI.TransportClasses
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# SGA 1, Exposé VI, end of VI.7 and VI.8: the pseudofunctor of a cloven category

A cleavage `K` of `p : 𝒳 ⥤ E` gives SGA's data a) `S ↦ 𝒳_S`, b) `f ↦ f^*`, c) `(f, g) ↦ c_{f,g}`,
satisfying VI.7.4 `A)` and `B)`: a lax functor `K.laxFunctor : Eᵒᵖ → Cat` (its unit is the inverse
of the vertical transports `α_{𝟙_S}`, see SGA's N.B. at the end of VI.7). It is strictly unitary
(SGA's normalized pseudofunctor) iff `K` is normalized (`Cleavage.strictlyUnitaryLaxFunctor`),
and a pseudofunctor when `𝒳` is fibered (VI.7.2, `Cleavage.pseudofunctor`).

The end of VI.8 ("it remains to specify how one obtains a natural isomorphism between `𝒳'` and
`𝒳`") is `Cleavage.laxCoGrothendieckIso`: the functor `(S, ξ) ↦ ξ`, `(f, u) ↦ α_f(ξ) ∘ u` is an
isomorphism of categories over `E` from the category of VI.8 defined by `K.laxFunctor` to `𝒳`
(for any cleavage, not only normalized ones). For fibered `𝒳` the same holds for mathlib's
`∫ᶜ K.pseudofunctor` (`Cleavage.coGrothendieckIso`), and it sends the canonical transports of
`∫ᶜ` to those of `K`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite Bicategory

variable {E : Type u₁} [Category.{v₁} E] {C : Type u₂} [Category.{v₂} C] {p : C ⥤ E}

namespace Cleavage

variable (K : Cleavage p)

@[simp] theorem pullbackIdIso_inv_app_val (S : E) (ξ : Fiber p S) :
    ((K.pullbackIdIso S).inv.app ξ).val ≫ K.transport (𝟙 S) ξ = 𝟙 _ := by
  have := congrArg Subtype.val ((K.pullbackIdIso S).inv_hom_id_app ξ)
  simpa [transportId] using this

/-- VI.7: the (lax) pseudofunctor `Eᵒᵖ → Cat` of a cloven category: `S ↦ 𝒳_S`, `f ↦ f^*`, with
comparisons `c_{f,g}` and unit `(α_{𝟙_S})⁻¹ : 𝟭 ⟶ (𝟙_S)^*`. -/
noncomputable abbrev laxFunctor : LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂} :=
  laxFunctorOfComponents (fun S ↦ Cat.of (Fiber p S)) (fun f ↦ K.pullback f)
    (fun S ↦ (K.pullbackIdIso S).inv) (fun f g ↦ K.comparisonNatTrans f g)
    (fun {T S} f ξ ↦ by
      apply Subtype.ext
      change ((K.pullback f).map ((K.pullbackIdIso S).inv.app ξ)).val ≫
        (K.comparison (𝟙 S) f ξ).val = _
      rw [comparison_id_left, ← Category.assoc, ← fiber_comp_val, ← Functor.map_comp]
      simp)
    (fun {T S} f ξ ↦ by
      apply Subtype.ext
      change ((K.pullbackIdIso T).inv.app ((K.pullback f).obj ξ)).val ≫
        (K.comparison f (𝟙 T) ξ).val = _
      rw [comparison_id_right, ← Category.assoc, pullbackIdIso_inv_app_val]
      simp)
    (fun {V U T S} f g h ξ ↦ by
      apply Subtype.ext
      change (K.comparison g h ((K.pullback f).obj ξ)).val ≫ (K.comparison f (h ≫ g) ξ).val = _
      rw [comparison_assoc]
      simp)

@[simp] theorem laxPullback_laxFunctor {T S : E} (f : T ⟶ S) :
    laxPullback K.laxFunctor f = K.pullback f := rfl

@[simp] theorem laxComparison_laxFunctor {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    laxComparison K.laxFunctor f g = K.comparisonNatTrans f g := rfl

@[simp] theorem laxUnit_laxFunctor (S : E) :
    laxUnit K.laxFunctor S = (K.pullbackIdIso S).inv := rfl

/-! ### The isomorphism `∫ F_𝒳 ≅ 𝒳` -/

/-- The arrow `α_f(ξ) ∘ u : η ⟶ ξ` of `𝒳` attached to `u : η ⟶ f^* ξ`. -/
abbrev homOfPullback {T S : E} (f : T ⟶ S) {η : Fiber p T} {ξ : Fiber p S}
    (u : η ⟶ (K.pullback f).obj ξ) : η.val ⟶ ξ.val :=
  u.val ≫ K.transport f ξ

instance isHomLift_homOfPullback {T S : E} (f : T ⟶ S) {η : Fiber p T} {ξ : Fiber p S}
    (u : η ⟶ (K.pullback f).obj ξ) : IsHomLift p f (K.homOfPullback f u) := by
  have : IsHomLift p (𝟙 T) u.val := u.property
  infer_instance

/-- VI.8: the functor `(S, ξ) ↦ ξ`, `(f, u) ↦ α_f(ξ) ∘ u` from the category defined by the
pseudofunctor of `K` to `𝒳`. -/
noncomputable def fromLaxCoGrothendieck : LaxCoGrothendieck K.laxFunctor ⥤ C where
  obj X := X.fiber.val
  map {X Y} φ := K.homOfPullback φ.base φ.fiber
  map_id X := K.pullbackIdIso_inv_app_val X.base X.fiber
  map_comp {X Y Z} φ ψ := by
    obtain ⟨B, ξ⟩ := X
    obtain ⟨B', η⟩ := Y
    obtain ⟨B'', ζ⟩ := Z
    change Fiber p B at ξ
    change Fiber p B' at η
    change Fiber p B'' at ζ
    obtain ⟨φb, φf⟩ := φ
    obtain ⟨ψb, ψf⟩ := ψ
    change ξ ⟶ (K.pullback φb).obj η at φf
    change η ⟶ (K.pullback ψb).obj ζ at ψf
    change (φf.val ≫ ((K.pullback φb).map ψf).val ≫ (K.comparison ψb φb ζ).val) ≫
      K.transport (φb ≫ ψb) ζ = (φf.val ≫ K.transport φb η) ≫ ψf.val ≫ K.transport ψb ζ
    rw [Category.assoc, Category.assoc, comparison_fac, transport_naturality_assoc,
      Category.assoc]

@[simp] theorem fromLaxCoGrothendieck_obj (X : LaxCoGrothendieck K.laxFunctor) :
    K.fromLaxCoGrothendieck.obj X = X.fiber.val := rfl

@[simp] theorem fromLaxCoGrothendieck_map {X Y : LaxCoGrothendieck K.laxFunctor} (φ : X ⟶ Y) :
    K.fromLaxCoGrothendieck.map φ = K.homOfPullback φ.base φ.fiber := rfl

instance {X Y : LaxCoGrothendieck K.laxFunctor} (φ : X ⟶ Y) :
    IsHomLift p φ.base (K.fromLaxCoGrothendieck.map φ) :=
  K.isHomLift_homOfPullback φ.base φ.fiber

/-- VI.8: `(S, ξ) ↦ ξ` is an `E`-functor. -/
theorem fromLaxCoGrothendieck_comp_p :
    K.fromLaxCoGrothendieck ⋙ p = LaxCoGrothendieck.forget K.laxFunctor :=
  functor_comp_eq_of_isHomLift _ _ _ (fun X ↦ X.fiber.property) fun φ ↦
    K.isHomLift_homOfPullback φ.base φ.fiber

instance : K.fromLaxCoGrothendieck.Faithful where
  map_injective {X Y} {φ ψ} h := by
    have hb : φ.base = ψ.base := by
      have : IsHomLift p ψ.base (K.fromLaxCoGrothendieck.map φ) := by rw [h]; infer_instance
      exact eq_of_isHomLift_of_isHomLift (p := p) (K.fromLaxCoGrothendieck.map φ)
    obtain ⟨B, ξ⟩ := X
    obtain ⟨B', η⟩ := Y
    change Fiber p B at ξ
    change Fiber p B' at η
    obtain ⟨φb, φf⟩ := φ
    obtain ⟨ψb, ψf⟩ := ψ
    change φb = ψb at hb
    subst hb
    change ξ ⟶ (K.pullback φb).obj η at φf ψf
    have : φf = ψf := by
      have : IsHomLift p (𝟙 B) φf.val := φf.property
      have : IsHomLift p (𝟙 B) ψf.val := ψf.property
      exact Subtype.ext (IsCartesian.ext p φb (K.transport φb η) _ _ h)
    rw [this]

instance : K.fromLaxCoGrothendieck.Full where
  map_surjective {X Y} m := by
    obtain ⟨B, ξ⟩ := X
    obtain ⟨B', η⟩ := Y
    change Fiber p B at ξ
    change Fiber p B' at η
    change ξ.val ⟶ η.val at m
    let f : B ⟶ B' := eqToHom ξ.property.symm ≫ p.map m ≫ eqToHom η.property
    have : IsHomLift p f m := IsHomLift.of_fac' p f m ξ.property η.property (by simp [f])
    have := K.transport_isCartesian f η
    refine ⟨⟨f, ⟨IsCartesian.map p f (K.transport f η) m,
      (IsCartesian.map_isHomLift p f (K.transport f η) m : IsHomLift p (𝟙 B) _)⟩⟩, ?_⟩
    exact IsCartesian.fac p f (K.transport f η) m

instance : K.fromLaxCoGrothendieck.IsIso where
  bijective_obj := by
    constructor
    · rintro ⟨B, x, hx⟩ ⟨B', y, hy⟩ (h : x = y)
      subst h
      obtain rfl : B = B' := hx.symm.trans hy
      rfl
    · intro x
      exact ⟨⟨p.obj x, ⟨x, rfl⟩⟩, rfl⟩

/-- VI.8: the isomorphism of categories between the category defined by the pseudofunctor of a
cloven category `𝒳` and `𝒳`. -/
noncomputable def laxCoGrothendieckIso : IsoCat (LaxCoGrothendieck K.laxFunctor) C :=
  K.fromLaxCoGrothendieck.asIsomorphism

/-- VI.8: `(S, ξ) ↦ ξ` as an `E`-functor. -/
noncomputable def fromLaxCoGrothendieckBased :
    BasedFunctor (BasedCategory.ofFunctor (LaxCoGrothendieck.forget K.laxFunctor))
      (BasedCategory.ofFunctor p) where
  toFunctor := K.fromLaxCoGrothendieck
  w := K.fromLaxCoGrothendieck_comp_p

/-! ### Normalized cleavages and fibered categories -/

variable {K}

/-- VI.7, VI.8: the pseudofunctor of a normalized cloven category is normalized, i.e. a strictly
unitary lax functor. -/
noncomputable abbrev IsNormalized.strictlyUnitaryLaxFunctor (hK : K.IsNormalized) :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂} where
  toLaxFunctor := K.laxFunctor
  map_id S := Cat.Hom.ext (hK.pullback_id S.as.unop)
  mapId_eq_eqToHom S := by
    ext ξ
    change Fiber p S.as.unop at ξ
    apply Subtype.ext
    rw [Cat.eqToHom_app]
    change ((K.pullbackIdIso S.as.unop).inv.app ξ).val = (eqToHom _ : ξ ⟶ _).val
    rw [fiber_eqToHom_val]
    obtain ⟨h, ht⟩ := hK S.as.unop ξ
    have h1 := K.pullbackIdIso_inv_app_val S.as.unop ξ
    rw [ht, comp_eqToHom_iff] at h1
    rw [h1]
    simp

/-- For a normalized cleavage, the inverse vertical transports are identifications. -/
theorem IsNormalized.pullbackIdIso_inv_app (hK : K.IsNormalized) (S : E) (ξ : Fiber p S) :
    (K.pullbackIdIso S).inv.app ξ = eqToHom (hK.pullback_obj ξ).symm := by
  apply Subtype.ext
  have h₁ := K.pullbackIdIso_inv_app_val S ξ
  obtain ⟨h, ht⟩ := hK S ξ
  rw [ht, comp_eqToHom_iff] at h₁
  rw [h₁, fiber_eqToHom_val]
  simp

variable (K)

/-- VI.7.2: the pseudofunctor of a fibered cloven category, a pseudofunctor in mathlib's sense
(its comparisons `c_{f,g}` are invertible). -/
noncomputable def pseudofunctor [IsFibered p] :
    Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂} :=
  Pseudofunctor.mkOfLax K.laxFunctor
    { mapIdIso := fun S ↦ Cat.Hom.isoMk (K.pullbackIdIso S.as.unop)
      mapCompIso := fun f g ↦ Cat.Hom.isoMk (K.comparisonNatIso f.as.unop g.as.unop).symm }

/-- For a fibered cloven category, mathlib's `∫ᶜ` of its pseudofunctor is (by definition) the
category of VI.8 defined by its lax functor. -/
noncomputable def coGrothendieckToLax [IsFibered p] :
    Pseudofunctor.CoGrothendieck K.pseudofunctor ⥤ LaxCoGrothendieck K.laxFunctor where
  obj X := ⟨X.base, X.fiber⟩
  map f := ⟨f.base, f.fiber⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- VI.8, for a fibered cloven category: mathlib's `∫ᶜ` of its pseudofunctor is isomorphic to `𝒳`
over `E`, by `(S, ξ) ↦ ξ`, `(f, u) ↦ α_f(ξ) ∘ u`. -/
noncomputable def fromCoGrothendieck [IsFibered p] :
    Pseudofunctor.CoGrothendieck K.pseudofunctor ⥤ C :=
  K.coGrothendieckToLax ⋙ K.fromLaxCoGrothendieck

@[simp] theorem fromCoGrothendieck_map [IsFibered p]
    {X Y : Pseudofunctor.CoGrothendieck K.pseudofunctor} (φ : X ⟶ Y) :
    K.fromCoGrothendieck.map φ = φ.fiber.val ≫ K.transport φ.base Y.fiber := rfl

instance [IsFibered p] : K.coGrothendieckToLax.IsIso where
  faithful := ⟨fun {_ _} {f g} h ↦ by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    cases h
    rfl⟩
  full := ⟨fun {_ _} f ↦ ⟨⟨f.base, f.fiber⟩, rfl⟩⟩
  bijective_obj := ⟨fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by cases h; rfl, fun X ↦ ⟨⟨X.base, X.fiber⟩, rfl⟩⟩

instance [IsFibered p] : K.fromCoGrothendieck.IsIso where
  faithful := inferInstanceAs (K.coGrothendieckToLax ⋙ K.fromLaxCoGrothendieck).Faithful
  full := inferInstanceAs (K.coGrothendieckToLax ⋙ K.fromLaxCoGrothendieck).Full
  bijective_obj := (K.fromLaxCoGrothendieck.bijective_obj).comp
    (Functor.IsIso.bijective_obj K.coGrothendieckToLax)

/-- VI.8, for a fibered cloven category: `∫ᶜ` of its pseudofunctor is isomorphic to `𝒳`. -/
noncomputable def coGrothendieckIso [IsFibered p] :
    IsoCat (Pseudofunctor.CoGrothendieck K.pseudofunctor) C :=
  K.fromCoGrothendieck.asIsomorphism

theorem fromCoGrothendieck_comp_p [IsFibered p] :
    K.fromCoGrothendieck ⋙ p = Pseudofunctor.CoGrothendieck.forget K.pseudofunctor := by
  rw [fromCoGrothendieck, Functor.assoc, fromLaxCoGrothendieck_comp_p]
  rfl

/-- VI.8: the isomorphism `∫ᶜ F_𝒳 ≅ 𝒳` sends the canonical transport `(f, 𝟙) : (T, f^* ξ) ⟶ (S, ξ)`
of `∫ᶜ` to the transport `α_f(ξ)` of `K`. -/
theorem fromCoGrothendieck_map_cartesianLift [IsFibered p] {T S : E} (f : T ⟶ S)
    (ξ : Fiber p S) :
    K.fromCoGrothendieck.map
        (Pseudofunctor.CoGrothendieck.cartesianLift (F := K.pseudofunctor) ξ f) =
      K.transport f ξ := by
  change Subtype.val (𝟙 ((K.pullback f).obj ξ)) ≫ K.transport f ξ = _
  simp

end Cleavage

end SGA.SGA1.ExposeVI
