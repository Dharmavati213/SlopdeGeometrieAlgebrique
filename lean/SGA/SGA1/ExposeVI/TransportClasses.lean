/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Splittings
import SGA.SGA1.ExposeVI.Subcategories

/-!
# SGA 1, Exposé VI, VI.7.1 and VI.9: cleavages as classes of transport morphisms

VI.7.1: the cleavages of `p : 𝒳 ⥤ E` correspond bijectively to the classes `K` of arrows of `𝒳`
such that a) the arrows of `K` are cartesian, and b) for every `f : T ⟶ S` of `E` and every `ξ`
over `S` there is exactly one arrow of `K` over `f` with target `ξ`
(`Cleavage.equivTransportClass`). The cleavage is normalized iff c) `K` contains the identities
(`Cleavage.isNormalized_iff_id_mem`), and (VI.9) it is a splitting iff moreover `K` is closed
under composition (`Cleavage.isSplitting_iff_isMultiplicative`).
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]

variable (p : C ⥤ E) in
/-- VI.7.1: a class of transport morphisms for `p`: a) its arrows are cartesian, b) for every
`f : R ⟶ S` and every `ξ` over `S` there is exactly one arrow of the class over `f` with
target `ξ`. -/
structure IsTransportClass (K : MorphismProperty C) : Prop where
  isCartesian {a b : C} (φ : a ⟶ b) : K φ → IsCartesian p (p.map φ) φ
  existsUnique {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    ∃! x : Σ a : C, a ⟶ ξ.val, IsHomLift p f x.2 ∧ K x.2

/-- Equal elements of `Σ a, a ⟶ b` differ by the identification of their sources. -/
theorem sigma_hom_eq {b : C} {x y : Σ a : C, a ⟶ b} (h : x = y) :
    ∃ e : x.1 = y.1, x.2 = eqToHom e ≫ y.2 := by
  subst h
  exact ⟨rfl, by simp⟩

/-- An arrow cartesian over `f` is cartesian over its own image `p φ`. -/
theorem isCartesian_map_self {p : C ⥤ E} {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [h : IsCartesian p f φ] : IsCartesian p (p.map φ) φ := by
  subst_hom_lift p f φ
  exact h

/-- Two base arrows lifted by the same arrow are equal. -/
theorem eq_of_isHomLift_of_isHomLift {p : C ⥤ E} {R S : E} {f f' : R ⟶ S} {a b : C}
    (φ : a ⟶ b) [IsHomLift p f φ] [IsHomLift p f' φ] : f = f' := by
  rw [IsHomLift.fac p f φ, IsHomLift.fac p f' φ]

namespace Cleavage

variable {p : C ⥤ E} (K : Cleavage p)

/-- VI.7.1: the transport morphisms of a cleavage, the arrows `α_f(ξ) : f^* ξ ⟶ ξ` (up to the
identification of their endpoints). -/
def transports : MorphismProperty C := fun a b φ ↦
  ∃ (R S : E) (f : R ⟶ S) (ξ : Fiber p S) (h₁ : ((K.pullback f).obj ξ).val = a)
    (h₂ : ξ.val = b), φ = eqToHom h₁.symm ≫ K.transport f ξ ≫ eqToHom h₂

theorem transports_transport {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    K.transports (K.transport f ξ) :=
  ⟨R, S, f, ξ, rfl, rfl, by simp⟩

/-- VI.7.1: a transport morphism lying over `f` with target `ξ` is `α_f(ξ)`. -/
theorem eq_transport_of_mem {R S : E} (f : R ⟶ S) (ξ : Fiber p S) {a : C} (φ : a ⟶ ξ.val)
    [IsHomLift p f φ] (hφ : K.transports φ) :
    ∃ h : ((K.pullback f).obj ξ).val = a, φ = eqToHom h.symm ≫ K.transport f ξ := by
  obtain ⟨R', S', f', ξ', h₁, h₂, hφ⟩ := hφ
  subst h₁
  have hS : S' = S := ξ'.property.symm.trans ((congrArg p.obj h₂).trans ξ.property)
  subst hS
  obtain rfl : ξ' = ξ := Subtype.ext h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hφ
  subst hφ
  have hR : R' = R := ((K.pullback f').obj ξ').property.symm.trans
    (IsHomLift.domain_eq p f (K.transport f' ξ'))
  subst hR
  obtain rfl : f' = f := eq_of_isHomLift_of_isHomLift (p := p) (K.transport f' ξ')
  exact ⟨rfl, by simp⟩

/-- VI.7.1: the transport morphisms of a cleavage satisfy a) and b). -/
theorem transports_isTransportClass : IsTransportClass p K.transports where
  isCartesian {a b} φ hφ := by
    obtain ⟨R, S, f, ξ, h₁, h₂, rfl⟩ := hφ
    subst h₁ h₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact isCartesian_map_self f _
  existsUnique {R S} f ξ := by
    refine ⟨⟨_, K.transport f ξ⟩, ⟨inferInstance, K.transports_transport f ξ⟩, ?_⟩
    rintro ⟨a, φ⟩ ⟨hφ₁, hφ₂⟩
    have : IsHomLift p f φ := hφ₁
    obtain ⟨h, rfl⟩ := K.eq_transport_of_mem f ξ φ hφ₂
    subst h
    simp

end Cleavage

/-! ### From a class of transport morphisms to a cleavage -/

namespace IsTransportClass

variable {p : C ⥤ E} {K : MorphismProperty C} (hK : IsTransportClass p K)

/-- The arrow of `K` over `f` with target `ξ`. -/
noncomputable def lift {R S : E} (f : R ⟶ S) (ξ : Fiber p S) : Σ a : C, a ⟶ ξ.val :=
  (hK.existsUnique f ξ).exists.choose

theorem lift_spec {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsHomLift p f (hK.lift f ξ).2 ∧ K (hK.lift f ξ).2 :=
  (hK.existsUnique f ξ).exists.choose_spec

theorem lift_unique {R S : E} (f : R ⟶ S) (ξ : Fiber p S) (x : Σ a : C, a ⟶ ξ.val)
    (h₁ : IsHomLift p f x.2) (h₂ : K x.2) : x = hK.lift f ξ :=
  (hK.existsUnique f ξ).unique ⟨h₁, h₂⟩ (hK.lift_spec f ξ)

/-- VI.7.1: the cleavage whose transports are the arrows of the class `K`. -/
noncomputable def cleavage : Cleavage p :=
  Cleavage.ofLifts
    (fun {R _} f ξ ↦ ⟨(hK.lift f ξ).1,
      haveI := (hK.lift_spec f ξ).1
      IsHomLift.domain_eq p f (hK.lift f ξ).2⟩)
    (fun f ξ ↦ (hK.lift f ξ).2)
    (fun f ξ ↦ by
      have := (hK.lift_spec f ξ).1
      exact isCartesian_of_isCartesian_map p f _ (hK.isCartesian _ (hK.lift_spec f ξ).2))

theorem cleavage_transport {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    hK.cleavage.transport f ξ = (hK.lift f ξ).2 := rfl

end IsTransportClass

namespace Cleavage

variable {p : C ⥤ E}

theorem cleavage_transports (K : Cleavage p) :
    K.transports_isTransportClass.cleavage = K := by
  have key : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S),
      K.transports_isTransportClass.lift f ξ = ⟨_, K.transport f ξ⟩ := fun f ξ ↦
    (K.transports_isTransportClass.lift_unique f ξ (⟨_, K.transport f ξ⟩ : Σ a : C, a ⟶ ξ.val)
      (inferInstance : IsHomLift p f (K.transport f ξ)) (K.transports_transport f ξ)).symm
  refine Cleavage.ext' (fun f ξ ↦ Subtype.ext (congrArg Sigma.fst (key f ξ))) fun f ξ ↦ ?_
  obtain ⟨e, he⟩ := sigma_hom_eq (key f ξ)
  exact he

theorem transports_cleavage {K : MorphismProperty C} (hK : IsTransportClass p K) :
    hK.cleavage.transports = K := by
  refine MorphismProperty.ext _ _ fun a b φ ↦ ⟨?_, fun hφ ↦ ?_⟩
  · rintro ⟨R, S, f, ξ, h₁, h₂, rfl⟩
    subst h₁ h₂
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (hK.lift_spec f ξ).2
  · have e := hK.lift_unique (p.map φ) (⟨b, rfl⟩ : Fiber p (p.obj b)) ⟨a, φ⟩
      (IsHomLift.map p φ) hφ
    obtain ⟨h, hh⟩ := sigma_hom_eq e
    exact ⟨_, _, p.map φ, (⟨b, rfl⟩ : Fiber p (p.obj b)), h.symm, rfl,
      hh.trans (by simp only [eqToHom_refl, Category.comp_id]; rfl)⟩

/-- VI.7.1: cleavages of `p` correspond bijectively to classes of transport morphisms, i.e.
classes `K` of arrows satisfying a) and b). -/
noncomputable def equivTransportClass :
    Cleavage p ≃ {K : MorphismProperty C // IsTransportClass p K} where
  toFun K := ⟨K.transports, K.transports_isTransportClass⟩
  invFun K := K.2.cleavage
  left_inv K := K.cleavage_transports
  right_inv K := Subtype.ext (transports_cleavage K.2)

/-- VI.7.1: a cleavage is normalized iff c) its class of transport morphisms contains the
identities. -/
theorem isNormalized_iff_id_mem (K : Cleavage p) :
    K.IsNormalized ↔ ∀ a : C, K.transports (𝟙 a) := by
  constructor
  · intro hK a
    obtain ⟨h, ht⟩ := hK (p.obj a) ⟨a, rfl⟩
    exact ⟨p.obj a, p.obj a, 𝟙 _, ⟨a, rfl⟩, h, rfl, by simp [ht]⟩
  · intro h S ξ
    have : IsHomLift p (𝟙 S) (𝟙 ξ.val) := IsHomLift.id ξ.property
    obtain ⟨e, he⟩ := K.eq_transport_of_mem (𝟙 S) ξ (𝟙 ξ.val) (h ξ.val)
    exact ⟨e, by rw [← eqToHom_comp_iff] at he; simpa using he.symm⟩

/-- VI.7.1: the cleavage attached to a class of transport morphisms is normalized iff c) the class
contains the identities. -/
theorem isNormalized_cleavage_iff {K : MorphismProperty C} (hK : IsTransportClass p K) :
    hK.cleavage.IsNormalized ↔ ∀ a : C, K (𝟙 a) := by
  rw [isNormalized_iff_id_mem, transports_cleavage]

/-- VI.9: a cleavage is a splitting iff its class of transport morphisms contains the identities
and is closed under composition. -/
theorem isSplitting_iff_isMultiplicative (K : Cleavage p) :
    K.IsSplitting ↔ K.transports.IsMultiplicative := by
  constructor
  · intro hK
    have hid := (K.isNormalized_iff_id_mem).mp hK.1
    refine { id_mem := hid, comp_mem := ?_ }
    rintro a b c φ ψ ⟨R₁, S₁, g, η, h₁, h₂, rfl⟩ ⟨R₂, S₂, f, ξ, h₃, h₄, rfl⟩
    subst h₁ h₂ h₄
    have hS : S₁ = R₂ := η.property.symm.trans
      ((congrArg p.obj h₃).symm.trans ((K.pullback f).obj ξ).property)
    subst hS
    obtain rfl : η = (K.pullback f).obj ξ := Subtype.ext h₃.symm
    obtain ⟨h, hc⟩ := hK.2 f g ξ
    refine ⟨_, _, g ≫ f, ξ, h.symm, rfl, ?_⟩
    simp [hc]
  · intro hK
    refine ⟨(K.isNormalized_iff_id_mem).mpr hK.id_mem, fun {U T S} f g ξ ↦ ?_⟩
    have hmem := hK.comp_mem _ _ (K.transports_transport g ((K.pullback f).obj ξ))
      (K.transports_transport f ξ)
    obtain ⟨h, hh⟩ := K.eq_transport_of_mem (g ≫ f) ξ _ hmem
    exact ⟨h.symm, hh⟩

end Cleavage

end SGA.SGA1.ExposeVI
