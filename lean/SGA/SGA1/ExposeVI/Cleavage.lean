/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered

/-!
# SGA 1, Exposé VI, §7: cloven categories

A cleavage of `p : 𝒳 ⥤ E` chooses, for every `f : R ⟶ S`, an inverse image functor
`f^* : 𝒳_S ⥤ 𝒳_R` together with cartesian transports `α_f(ξ) : f^*ξ ⟶ ξ`, natural in `ξ`.
We prove:

* VI.7.1: a cleavage is determined by its transports; cleavages exist iff `𝒳` is prefibered,
  and then normalized cleavages exist; functors preserving transports are cartesian;
* the comparison `c_{f,g} : g^* f^* ⟶ (fg)^*` is a natural transformation;
* VI.7.2: a cloven category is fibered iff all `c_{f,g}` are isomorphisms;
* VI.7.3: in the fibered case `f^*` is an equivalence for `f` an isomorphism;
* VI.7.4: the unit relations A) (and A′) for normalized cleavages) and the cocycle
  relation B); as in VI.11 d), for inverse arrows `f, g` relation B) gives the triangle
  identity of the pair `(f^*, g^*)`.

Lean writes `g ≫ f` for SGA's `fg = f ∘ g`, and `u ≫ v` for `v · u`. Since `𝟙 ≫ f = f` and
`(h ≫ g) ≫ f = h ≫ (g ≫ f)` hold only propositionally, the relations A) and B) carry the
canonical identifications `eqToHom` between the corresponding inverse images.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]

section FiberLemmas

variable {p : C ⥤ E} {S : E}

instance fiberHom_isHomLift {a b : Fiber p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) φ.val :=
  φ.property

@[simp] theorem fiber_comp_val {a b c : Fiber p S} (φ : a ⟶ b) (ψ : b ⟶ c) :
    (φ ≫ ψ).val = φ.val ≫ ψ.val := rfl

@[simp] theorem fiber_id_val (a : Fiber p S) : (𝟙 a : a ⟶ a).val = 𝟙 a.val := rfl

@[simp] theorem fiber_eqToHom_val {a b : Fiber p S} (h : a = b) :
    (eqToHom h).val = eqToHom (congrArg Subtype.val h) := by
  subst h
  rfl

theorem isHomLift_eqToHom_id {a b : C} (h : a = b) (ha : p.obj a = S) :
    IsHomLift p (𝟙 S) (eqToHom h) :=
  IsHomLift.eqToHom_domain_lift_id h ha

/-- A morphism of a fiber is invertible as soon as it is invertible in the total category. -/
theorem fiber_isIso_of_isIso_val {a b : Fiber p S} (φ : a ⟶ b) [h : IsIso φ.val] : IsIso φ :=
  haveI : IsIso ((Fiber.fiberInclusion : Fiber p S ⥤ C).map φ) := h
  isIso_of_reflects_iso φ (Fiber.fiberInclusion : Fiber p S ⥤ C)

end FiberLemmas

/-- VI.7.1: a cleavage of `p : 𝒳 ⥤ E`: for every `f : R ⟶ S` an inverse image functor
`f^* : 𝒳_S ⥤ 𝒳_R` and cartesian transports `α_f(ξ) : f^*ξ ⟶ ξ`, natural in `ξ`. The functor
structure of `f^*` is forced by the transports (`Cleavage.pullback_map_val`). -/
structure Cleavage (p : C ⥤ E) where
  pullback {R S : E} (f : R ⟶ S) : Fiber p S ⥤ Fiber p R
  transport {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    ((pullback f).obj ξ).val ⟶ ξ.val
  transport_isCartesian {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsCartesian p f (transport f ξ)
  transport_natural {R S : E} (f : R ⟶ S) {ξ η : Fiber p S} (u : ξ ⟶ η) :
    ((pullback f).map u).val ≫ transport f η = transport f ξ ≫ u.val

namespace Cleavage

variable {p : C ⥤ E} (K : Cleavage p)

instance transport_isCartesian_inst {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsCartesian p f (K.transport f ξ) :=
  K.transport_isCartesian f ξ

@[reassoc (attr := simp)]
theorem transport_naturality {R S : E} (f : R ⟶ S) {ξ η : Fiber p S} (u : ξ ⟶ η) :
    ((K.pullback f).map u).val ≫ K.transport f η = K.transport f ξ ≫ u.val :=
  K.transport_natural f u

/-- VI.7: the transports form a natural transformation `α_f : i_R ∘ f^* ⟶ i_S`. -/
@[simps]
def transportNatTrans {R S : E} (f : R ⟶ S) :
    K.pullback f ⋙ Fiber.fiberInclusion ⟶ Fiber.fiberInclusion where
  app ξ := K.transport f ξ
  naturality _ _ u := K.transport_natural f u

include K in
/-- VI.7.1: a cleavage supplies cartesian lifts, so `p` is prefibered. -/
theorem toIsPreFibered : IsPreFibered p where
  exists_isCartesian' {a _} f :=
    ⟨((K.pullback f).obj ⟨a, rfl⟩).val, K.transport f ⟨a, rfl⟩,
      K.transport_isCartesian f ⟨a, rfl⟩⟩

/-- VI.5.1, VI.7.1: the action of `f^*` on arrows is the one forced by the transports. -/
theorem pullback_map_val {R S : E} (f : R ⟶ S) {ξ η : Fiber p S} (u : ξ ⟶ η) :
    ((K.pullback f).map u).val =
      IsCartesian.map p f (K.transport f η) (K.transport f ξ ≫ u.val) :=
  IsCartesian.map_uniq p f _ _ _ (K.transport_natural f u)

/-- Transports along equal arrows differ by the canonical identification. -/
theorem transport_congr {R S : E} {f f' : R ⟶ S} (h : f = f') (ξ : Fiber p S) :
    K.transport f ξ =
      eqToHom (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) h) ≫ K.transport f' ξ := by
  subst h
  simp

/-- VI.7: the vertical transport `α_{𝟙_S}(ξ) : (𝟙_S)^* ξ ⟶ ξ`, an arrow of the fiber. -/
def transportId (S : E) (ξ : Fiber p S) : (K.pullback (𝟙 S)).obj ξ ⟶ ξ :=
  ⟨K.transport (𝟙 S) ξ, inferInstance⟩

instance transportId_isIso (S : E) (ξ : Fiber p S) : IsIso (K.transportId S ξ) := by
  have : IsIso (K.transport (𝟙 S) ξ) := isIso_of_vertical_isCartesian p (S := S) _
  exact fiber_isIso_of_isIso_val (K.transportId S ξ) (h := this)

/-- VI.7: `(𝟙_S)^* ≅ 𝟭`, through the vertical transports. -/
@[simps!]
noncomputable def pullbackIdIso (S : E) : K.pullback (𝟙 S) ≅ 𝟭 (Fiber p S) :=
  NatIso.ofComponents (fun ξ ↦ @asIso _ _ _ _ (K.transportId S ξ) (K.transportId_isIso S ξ))
    (fun u ↦ Subtype.ext (K.transport_natural (𝟙 S) u))

/-! ### The comparison `c_{f,g}` -/

/-- VI.7: the comparison `c_{f,g}(ξ) : g^* f^* ξ ⟶ (g ≫ f)^* ξ`, the unique vertical arrow
compatible with the transports. -/
noncomputable def comparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    (K.pullback g).obj ((K.pullback f).obj ξ) ⟶ (K.pullback (g ≫ f)).obj ξ :=
  ⟨IsCartesian.map p (g ≫ f) (K.transport (g ≫ f) ξ)
      (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ), inferInstance⟩

@[reassoc (attr := simp)]
theorem comparison_fac {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    (K.comparison f g ξ).val ≫ K.transport (g ≫ f) ξ =
      K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ :=
  IsCartesian.fac p (g ≫ f) (K.transport (g ≫ f) ξ) _

/-- VI.7: `c_{f,g}` is natural in `ξ`, i.e. a homomorphism of functors `g^* f^* ⟶ (fg)^*`. -/
@[simps]
noncomputable def comparisonNatTrans {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    K.pullback f ⋙ K.pullback g ⟶ K.pullback (g ≫ f) where
  app := K.comparison f g
  naturality {ξ η} u := by
    apply Subtype.ext
    apply IsCartesian.ext p (g ≫ f) (K.transport (g ≫ f) η)
    simp

/-- VI.7.2, necessity: in a fibered category the comparisons are isomorphisms. -/
instance comparison_isIso [IsFibered p] {U T S : E} (f : T ⟶ S) (g : U ⟶ T)
    (ξ : Fiber p S) : IsIso (K.comparison f g ξ) := by
  have : IsIso (K.comparison f g ξ).val :=
    (IsCartesian.domainUniqueUpToIso p (g ≫ f) (K.transport (g ≫ f) ξ)
      (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ)).isIso_hom
  exact fiber_isIso_of_isIso_val _

/-- VI.7.2, sufficiency: if all comparisons are isomorphisms, the category is fibered. -/
theorem isFibered_of_comparison_isIso
    (h : ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S), IsIso (K.comparison f g ξ)) :
    IsFibered p := by
  have := K.toIsPreFibered
  refine (isFibered_iff_comp p).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
  let ζ : Fiber p T := ⟨c, IsHomLift.codomain_eq p g ψ⟩
  -- `ψ` and `φ ≫ e₁` are, up to vertical isomorphisms, the transports.
  let e₁ := IsCartesian.domainUniqueUpToIso p g (K.transport g ζ) ψ
  have h₁ : e₁.hom ≫ K.transport g ζ = ψ := IsCartesian.fac p g (K.transport g ζ) ψ
  have : IsCartesian p f (φ ≫ e₁.hom) := IsCartesian.of_comp_iso p f φ e₁
  let e₂ := IsCartesian.domainUniqueUpToIso p f (K.transport f ((K.pullback g).obj ζ))
    (φ ≫ e₁.hom)
  have h₂ : e₂.hom ≫ K.transport f ((K.pullback g).obj ζ) = φ ≫ e₁.hom :=
    IsCartesian.fac p f _ _
  have : IsIso (K.comparison g f ζ) := h g f ζ
  have : IsIso (K.comparison g f ζ).val :=
    inferInstanceAs (IsIso (Fiber.fiberInclusion.map (K.comparison g f ζ)))
  let e₃ := asIso (e₂.hom ≫ (K.comparison g f ζ).val)
  have : IsHomLift p (𝟙 R) e₃.hom := by
    simp only [e₃, asIso_hom]
    infer_instance
  have hcomp : φ ≫ ψ = e₃.hom ≫ K.transport (f ≫ g) ζ := by
    simp only [e₃, asIso_hom, Category.assoc, comparison_fac, reassoc_of% h₂, h₁]
  rw [hcomp]
  exact IsCartesian.of_iso_comp p (f ≫ g) (K.transport (f ≫ g) ζ) e₃

/-- VI.7.2: a cloven category is fibered iff all the comparisons `c_{f,g}` are
isomorphisms. -/
theorem isFibered_iff_comparison_isIso :
    IsFibered p ↔
      ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S), IsIso (K.comparison f g ξ) :=
  ⟨fun _ _ _ _ _ _ _ ↦ inferInstance, K.isFibered_of_comparison_isIso⟩

/-- VI.7.2: in the fibered case, `c_{f,g} : g^* f^* ≅ (fg)^*`. -/
noncomputable def comparisonNatIso [IsFibered p] {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    K.pullback f ⋙ K.pullback g ≅ K.pullback (g ≫ f) :=
  NatIso.ofComponents (fun ξ ↦ asIso (K.comparison f g ξ))
    (fun u ↦ (K.comparisonNatTrans f g).naturality u)

/-- Inverse images along equal arrows are canonically isomorphic. -/
def pullbackCongr {R S : E} {f g : R ⟶ S} (h : f = g) : K.pullback f ≅ K.pullback g :=
  eqToIso (congrArg K.pullback h)

/-- VI.7.3: in a fibered cloven category, `f^*` is an equivalence for `f` an isomorphism,
with quasi-inverse `(f⁻¹)^*`, using `c_{f,f⁻¹}` and `c_{f⁻¹,f}`. -/
noncomputable def pullbackEquivOfIso [IsFibered p] {T S : E} (f : T ≅ S) :
    Fiber p S ≌ Fiber p T :=
  CategoryTheory.Equivalence.mk (K.pullback f.hom) (K.pullback f.inv)
    ((K.pullbackIdIso S).symm ≪≫ K.pullbackCongr f.inv_hom_id.symm ≪≫
      (K.comparisonNatIso f.hom f.inv).symm)
    (K.comparisonNatIso f.inv f.hom ≪≫ K.pullbackCongr f.hom_inv_id ≪≫ K.pullbackIdIso T)

/-- VI.7.3: in a fibered cloven category, `f^*` is an equivalence when `f` is invertible. -/
theorem pullback_isEquivalence [IsFibered p] {T S : E} (f : T ⟶ S) [IsIso f] :
    (K.pullback f).IsEquivalence :=
  (K.pullbackEquivOfIso (asIso f)).isEquivalence_functor

/-! ### VI.7.4: unit and cocycle relations -/

/-- VI.7.4 A), first relation: `c_{f,𝟙_T}(ξ) = α_{𝟙_T}(f^* ξ)`, up to the canonical
identification `(𝟙 ≫ f)^* = f^*`. -/
theorem comparison_id_right {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    (K.comparison f (𝟙 T) ξ).val = K.transport (𝟙 T) ((K.pullback f).obj ξ) ≫
      eqToHom (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) (Category.id_comp f).symm) := by
  have := isHomLift_eqToHom_id (p := p)
    (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) (Category.id_comp f).symm)
    ((K.pullback f).obj ξ).property
  apply IsCartesian.ext p (𝟙 T ≫ f) (K.transport (𝟙 T ≫ f) ξ)
  rw [comparison_fac, Category.assoc, K.transport_congr (Category.id_comp f)]
  simp

/-- VI.7.4 A), second relation: `c_{𝟙_S,f}(ξ) = f^*(α_{𝟙_S}(ξ))`, up to the canonical
identification `(f ≫ 𝟙)^* = f^*`. -/
theorem comparison_id_left {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    (K.comparison (𝟙 S) f ξ).val = ((K.pullback f).map (K.transportId S ξ)).val ≫
      eqToHom (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) (Category.comp_id f).symm) := by
  have := isHomLift_eqToHom_id (p := p)
    (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) (Category.comp_id f).symm)
    ((K.pullback f).obj ξ).property
  apply IsCartesian.ext p (f ≫ 𝟙 S) (K.transport (f ≫ 𝟙 S) ξ)
  rw [comparison_fac, Category.assoc, K.transport_congr (Category.comp_id f)]
  simp [transportId]

/-- VI.7.4 B): the cocycle relation `c_{f,gh} · c_{g,h}(f^*) = c_{fg,h} · h^*(c_{f,g})`,
up to the canonical identification `(h ≫ (g ≫ f))^* = ((h ≫ g) ≫ f)^*`. -/
theorem comparison_assoc {V U T S : E} (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U)
    (ξ : Fiber p S) :
    (K.comparison g h ((K.pullback f).obj ξ)).val ≫ (K.comparison f (h ≫ g) ξ).val =
      ((K.pullback h).map (K.comparison f g ξ)).val ≫ (K.comparison (g ≫ f) h ξ).val ≫
        eqToHom (congrArg (fun k ↦ ((K.pullback k).obj ξ).val)
          (Category.assoc h g f).symm) := by
  have := isHomLift_eqToHom_id (p := p)
    (congrArg (fun k ↦ ((K.pullback k).obj ξ).val) (Category.assoc h g f).symm)
    ((K.pullback (h ≫ g ≫ f)).obj ξ).property
  apply IsCartesian.ext p ((h ≫ g) ≫ f) (K.transport ((h ≫ g) ≫ f) ξ)
  rw [Category.assoc, comparison_fac, K.transport_congr (Category.assoc h g f)]
  simp

/-- The comparisons along equal arrows agree up to the identification of the objects. -/
theorem comparison_congr {U T S : E} {f f' : T ⟶ S} {g g' : U ⟶ T} (hf : f = f')
    (hg : g = g') (ξ : Fiber p S) : ∃ h₁ h₂, (K.comparison f g ξ).val =
      eqToHom h₁ ≫ (K.comparison f' g' ξ).val ≫ eqToHom h₂ := by
  subst hf hg
  exact ⟨rfl, rfl, by simp⟩

/-- VI.7.1: the cleavage is normalized: `(𝟙_S)^* ξ = ξ` and `α_{𝟙_S}(ξ)` is the identity,
i.e. the identity arrows are transport arrows. -/
def IsNormalized : Prop :=
  ∀ (S : E) (ξ : Fiber p S), ∃ h : ((K.pullback (𝟙 S)).obj ξ).val = ξ.val,
    K.transport (𝟙 S) ξ = eqToHom h

namespace IsNormalized

variable {K}

theorem pullback_obj (hK : K.IsNormalized) {S : E} (ξ : Fiber p S) :
    (K.pullback (𝟙 S)).obj ξ = ξ :=
  Subtype.ext (hK S ξ).1

/-- VI.7.1: for a normalized cleavage, `(𝟙_S)^* = 𝟭` as functors. -/
theorem pullback_id (hK : K.IsNormalized) (S : E) : K.pullback (𝟙 S) = 𝟭 (Fiber p S) := by
  refine Functor.ext hK.pullback_obj fun ξ η u ↦ Subtype.ext ?_
  obtain ⟨hξ, htξ⟩ := hK S ξ
  obtain ⟨hη, htη⟩ := hK S η
  have := K.transport_natural (𝟙 S) u
  rw [htξ, htη] at this
  simp only [fiber_comp_val, fiber_eqToHom_val, Functor.id_map]
  rw [← Category.assoc, ← this]
  simp

/-- VI.7.4 A′): for a normalized cleavage `c_{f,𝟙_T}` is the identity of `f^*`
(up to the canonical identification). -/
theorem comparison_id_right (hK : K.IsNormalized) {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    ∃ h, (K.comparison f (𝟙 T) ξ).val = eqToHom h := by
  obtain ⟨h₁, ht⟩ := hK T ((K.pullback f).obj ξ)
  have := K.comparison_id_right f ξ
  rw [ht, eqToHom_trans] at this
  exact ⟨_, this⟩

/-- VI.7.4 A′): for a normalized cleavage `c_{𝟙_S,f}` is the identity of `f^*`
(up to the canonical identification). -/
theorem comparison_id_left (hK : K.IsNormalized) {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    ∃ h, (K.comparison (𝟙 S) f ξ).val = eqToHom h := by
  obtain ⟨h₁, ht⟩ := hK S ξ
  have hid : K.transportId S ξ = eqToHom (hK.pullback_obj ξ) :=
    Subtype.ext (by simpa [transportId] using ht)
  have := K.comparison_id_left f ξ
  rw [hid, eqToHom_map, fiber_eqToHom_val, eqToHom_trans] at this
  exact ⟨_, this⟩

/-- VI.11 d): over a pair of inverse arrows `f : T ⟶ S`, `g : S ⟶ T`, the comparisons
`c_{f,g} : g^* f^* ⟶ (fg)^* = 𝟙` and `c_{g,f} : f^* g^* ⟶ 𝟙` of a normalized cleavage satisfy
the triangle identity `c_{f,g}(g^* ξ) = g^*(c_{g,f}(ξ))` (up to the identification of the
objects): the compatibility condition making `(f^*, g^*)` an adjoint equivalence is VI.7.4 B)
for the composite `gfg`. -/
theorem comparison_triangle (hK : K.IsNormalized) {T S : E} (f : T ⟶ S) (g : S ⟶ T)
    (hgf : g ≫ f = 𝟙 S) (hfg : f ≫ g = 𝟙 T) (ξ : Fiber p T) :
    ∃ h, (K.comparison f g ((K.pullback g).obj ξ)).val =
      ((K.pullback g).map (K.comparison g f ξ)).val ≫ eqToHom h := by
  have hB := K.comparison_assoc g f g ξ
  obtain ⟨a₁, a₂, ha⟩ := K.comparison_congr (rfl : g = g) hgf ξ
  obtain ⟨b₁, b₂, hb⟩ := K.comparison_congr hfg (rfl : g = g) ξ
  obtain ⟨c, hc⟩ := hK.comparison_id_right g ξ
  obtain ⟨d, hd⟩ := hK.comparison_id_left g ξ
  rw [ha, hc, hb, hd] at hB
  simp only [eqToHom_trans] at hB
  have := (comp_eqToHom_iff _ _ _).mp hB
  simp only [Category.assoc, eqToHom_trans] at this
  exact ⟨_, this⟩

end IsNormalized

/-! ### Constructions of cleavages -/

/-- VI.7.1: a choice of cartesian lifts `α_f(ξ)` determines a cleavage; the functor
structure of `f^*` is forced by the universal property. -/
noncomputable def ofLifts (obj : ∀ {R S : E} (_ : R ⟶ S) (_ : Fiber p S), Fiber p R)
    (lift : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S), (obj f ξ).val ⟶ ξ.val)
    (isCartesian : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S), IsCartesian p f (lift f ξ)) :
    Cleavage p where
  pullback {R S} f :=
    { obj := obj f
      map := fun {ξ η} u ↦ ⟨IsCartesian.map p f (lift f η) (lift f ξ ≫ u.val), inferInstance⟩
      map_id := fun ξ ↦ by
        have : IsHomLift p (𝟙 R) (𝟙 (obj f ξ).val) := IsHomLift.id (obj f ξ).property
        exact Subtype.ext (IsCartesian.map_uniq p f (lift f ξ) _ (𝟙 _) (by simp)).symm
      map_comp := fun {ξ η ζ} u v ↦ Subtype.ext
        (IsCartesian.map_uniq p f (lift f ζ) _ _ (by simp)).symm }
  transport := lift
  transport_isCartesian := isCartesian
  transport_natural {R S} f {ξ η} u := IsCartesian.fac p f (lift f η) (lift f ξ ≫ u.val)

/-- VI.7.1: a prefibered category admits a cleavage (by choice). -/
noncomputable def ofIsPreFibered [IsPreFibered p] : Cleavage p :=
  ofLifts (fun f ξ ↦ ⟨IsPreFibered.pullbackObj ξ.property f,
      IsPreFibered.pullbackObj_proj ξ.property f⟩)
    (fun f ξ ↦ IsPreFibered.pullbackMap ξ.property f)
    (fun f ξ ↦ IsPreFibered.pullbackMap.IsCartesian ξ.property f)

/-- VI.7.1: `𝒳` admits a cleavage iff it is prefibered over `E`. -/
theorem nonempty_iff_isPreFibered : Nonempty (Cleavage p) ↔ IsPreFibered p :=
  ⟨fun ⟨K⟩ ↦ K.toIsPreFibered, fun _ ↦ ⟨ofIsPreFibered⟩⟩

/-- An identity arrow over an identification `f = eqToHom e` of the base is cartesian. -/
theorem isCartesian_id_of_eq {R S : E} (f : R ⟶ S) (e : R = S) (hf : f = eqToHom e) (a : C)
    (ha : p.obj a = S) : IsCartesian p f (𝟙 a) := by
  subst e hf ha
  simp only [eqToHom_refl]
  infer_instance

/-- The lift used by `normalize`: the identity at identity arrows, `K`'s transport
elsewhere. -/
private noncomputable def normalizedLift {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    Σ' (η : Fiber p R) (φ : η.val ⟶ ξ.val), IsCartesian p f φ := by
  classical
  exact if h : ∃ e : R = S, f = eqToHom e then
    ⟨⟨ξ.val, ξ.property.trans h.choose.symm⟩, 𝟙 ξ.val,
      isCartesian_id_of_eq f h.choose h.choose_spec ξ.val ξ.property⟩
  else ⟨(K.pullback f).obj ξ, K.transport f ξ, inferInstance⟩

/-- VI.7.1: every cloven category can be given a normalized cleavage, by replacing the
transports along identity arrows with identities. -/
noncomputable def normalize : Cleavage p :=
  ofLifts (fun f ξ ↦ (K.normalizedLift f ξ).1) (fun f ξ ↦ (K.normalizedLift f ξ).2.1)
    (fun f ξ ↦ (K.normalizedLift f ξ).2.2)

theorem normalize_isNormalized : K.normalize.IsNormalized := by
  intro S ξ
  change ∃ h : (K.normalizedLift (𝟙 S) ξ).1.val = ξ.val,
    (K.normalizedLift (𝟙 S) ξ).2.1 = eqToHom h
  have hl : K.normalizedLift (𝟙 S) ξ = ⟨⟨ξ.val, ξ.property⟩, 𝟙 ξ.val,
      isCartesian_id_of_eq (𝟙 S) rfl rfl ξ.val ξ.property⟩ := by
    have h : ∃ e : S = S, 𝟙 S = eqToHom e := ⟨rfl, rfl⟩
    rw [normalizedLift, dite_eq_left h]
  rw [hl]
  exact ⟨rfl, rfl⟩

/-- VI.7.1: a prefibered category admits a normalized cleavage. -/
theorem exists_isNormalized [IsPreFibered p] : ∃ K : Cleavage p, K.IsNormalized :=
  ⟨ofIsPreFibered.normalize, normalize_isNormalized _⟩

end Cleavage

/-! ### Morphisms of cloven categories -/

section Morphisms

variable {X : BasedCategory.{v₂, u₂} E} {Y : BasedCategory.{v₃, u₃} E}

/-- VI.7.1: an `E`-functor sending the transports of a cleavage of `𝒳` to cartesian arrows
(e.g. to the transports of a cleavage of `𝒴`) is a cartesian functor. -/
theorem isCartesianFunctor_of_map_transport (K : Cleavage X.p) (F : BasedFunctor X Y)
    (hF : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber X.p S), IsCartesian Y.p f (F.map (K.transport f ξ))) :
    IsCartesianFunctor F where
  map_isCartesian {R S a b} f φ hφ := by
    let ξ : Fiber X.p S := ⟨b, IsHomLift.codomain_eq X.p f φ⟩
    let e := IsCartesian.domainUniqueUpToIso X.p f (K.transport f ξ) φ
    have he : e.hom ≫ K.transport f ξ = φ := IsCartesian.fac X.p f _ φ
    have := hF f ξ
    let e' := F.toFunctor.mapIso e
    have : IsHomLift Y.p (𝟙 R) e'.hom := F.preserves_isHomLift (𝟙 R) e.hom
    rw [← he, F.map_comp]
    exact IsCartesian.of_iso_comp Y.p f _ e'

/-- VI.7.1: a morphism of cloven categories sends transports to transports (up to the
identification of the inverse images); in particular it is a cartesian functor. -/
def IsClovenFunctor (K : Cleavage X.p) (K' : Cleavage Y.p) (F : BasedFunctor X Y) : Prop :=
  ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber X.p S),
    ∃ h : F.obj ((K.pullback f).obj ξ).val = ((K'.pullback f).obj ((fiberMap F S).obj ξ)).val,
      F.map (K.transport f ξ) = eqToHom h ≫ K'.transport f ((fiberMap F S).obj ξ)

theorem IsClovenFunctor.isCartesianFunctor {K : Cleavage X.p} {K' : Cleavage Y.p}
    {F : BasedFunctor X Y} (hF : IsClovenFunctor K K' F) : IsCartesianFunctor F := by
  refine isCartesianFunctor_of_map_transport K F fun {R S} f ξ ↦ ?_
  obtain ⟨h, hmap⟩ := hF f ξ
  rw [hmap]
  change IsCartesian Y.p f ((eqToIso h).hom ≫ K'.transport f ((fiberMap F S).obj ξ))
  have : IsHomLift Y.p (𝟙 R) (eqToIso h).hom :=
    isHomLift_eqToHom_id h ((F.w_obj _).trans ((K.pullback f).obj ξ).property)
  exact IsCartesian.of_iso_comp Y.p f _ (eqToIso h)

end Morphisms

end SGA.SGA1.ExposeVI
