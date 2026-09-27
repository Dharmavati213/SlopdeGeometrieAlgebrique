/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cleavage
import SGA.SGA1.ExposeVI.Groupoids
import Mathlib.CategoryTheory.Category.Cat

/-!
# SGA 1, Exposé VI, §9: split categories

A splitting is a normalized cleavage whose transport arrows are closed under composition;
equivalently all `c_{f,g}` are identities, and then `(g ≫ f)^* = f^* ⋙ g^*`, so that
`S ↦ 𝒳_S` is a functor `Eᵒᵖ ⥤ Cat`.

For a surjective homomorphism of groups `φ : F →* E`, cleavages of `SingleObj F` over
`SingleObj E` correspond to set-theoretic sections of `φ`, and splittings to homomorphic
sections; so a splitting exists iff the extension splits.

If the fibers of a fibered category are rigid and reduced, every cleavage is a splitting,
and any two cleavages agree.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C] {p : C ⥤ E}

namespace Cleavage

/-- Two cleavages with the same inverse images and transports (up to the identification of
the objects) are equal. -/
theorem ext' {K K' : Cleavage p}
    (hobj : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S), (K.pullback f).obj ξ = (K'.pullback f).obj ξ)
    (htr : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S),
      K.transport f ξ = eqToHom (congrArg Subtype.val (hobj f ξ)) ≫ K'.transport f ξ) :
    K = K' := by
  have hpb : ∀ {R S : E} (f : R ⟶ S), K.pullback f = K'.pullback f := by
    intro R S f
    refine CategoryTheory.Functor.ext (hobj f) fun ξ η u ↦ Subtype.ext ?_
    simp only [fiber_comp_val, fiber_eqToHom_val]
    have := isHomLift_eqToHom_id (p := p) (congrArg Subtype.val (hobj f ξ))
      ((K.pullback f).obj ξ).property
    have := isHomLift_eqToHom_id (p := p) (congrArg Subtype.val (hobj f η)).symm
      ((K'.pullback f).obj η).property
    apply IsCartesian.ext p f (K.transport f η)
    rw [K.transport_naturality, htr f ξ, htr f η]
    simp
  obtain ⟨pb, tr, cart, nat⟩ := K
  obtain ⟨pb', tr', cart', nat'⟩ := K'
  obtain rfl : @pb = @pb' := by
    funext R S f
    exact hpb f
  obtain rfl : @tr = @tr' := by
    funext R S f ξ
    simpa using htr f ξ
  rfl

variable (K : Cleavage p)

/-- VI.9: a splitting is a normalized cleavage whose transport arrows are closed under
composition. -/
def IsSplitting : Prop :=
  K.IsNormalized ∧ ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S),
    ∃ h : ((K.pullback g).obj ((K.pullback f).obj ξ)).val = ((K.pullback (g ≫ f)).obj ξ).val,
      K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ = eqToHom h ≫ K.transport (g ≫ f) ξ

/-- VI.9: a normalized cleavage is a splitting iff all the comparisons `c_{f,g}` are
identities (up to the identification of the objects). -/
theorem isSplitting_iff : K.IsSplitting ↔ K.IsNormalized ∧
    ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S),
      ∃ h, (K.comparison f g ξ).val = eqToHom h := by
  refine and_congr_right fun _ ↦ ⟨fun hs U T S f g ξ ↦ ?_, fun hc U T S f g ξ ↦ ?_⟩
  · obtain ⟨h, ht⟩ := hs f g ξ
    refine ⟨h, ?_⟩
    have := isHomLift_eqToHom_id (p := p) h ((K.pullback g).obj ((K.pullback f).obj ξ)).property
    apply IsCartesian.ext p (g ≫ f) (K.transport (g ≫ f) ξ)
    rw [comparison_fac, ht]
  · obtain ⟨h, hc⟩ := hc f g ξ
    exact ⟨h, by rw [← comparison_fac, hc]⟩

variable {K}

/-- VI.9: for a splitting, `(g ≫ f)^* = f^* ⋙ g^*` as functors. -/
theorem IsSplitting.pullback_comp (hK : K.IsSplitting) {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    K.pullback f ⋙ K.pullback g = K.pullback (g ≫ f) := by
  have hc := fun ξ ↦ ((K.isSplitting_iff).mp hK).2 f g ξ
  have hobj : ∀ ξ, (K.pullback g).obj ((K.pullback f).obj ξ) = (K.pullback (g ≫ f)).obj ξ :=
    fun ξ ↦ Subtype.ext (hc ξ).1
  refine CategoryTheory.Functor.ext hobj fun ξ η u ↦ Subtype.ext ?_
  have hnat := congrArg Subtype.val ((K.comparisonNatTrans f g).naturality u)
  obtain ⟨hξ, hcξ⟩ := hc ξ
  obtain ⟨hη, hcη⟩ := hc η
  simp only [Functor.comp_map, fiber_comp_val, comparisonNatTrans_app, hcξ, hcη] at hnat
  simp only [fiber_comp_val, fiber_eqToHom_val]
  rw [← Category.assoc, ← hnat]
  simp

/-- VI.9: a splitting makes `S ↦ 𝒳_S`, `f ↦ f^*` a functor `Eᵒᵖ ⥤ Cat`. -/
def IsSplitting.toFunctor (hK : K.IsSplitting) : Eᵒᵖ ⥤ Cat.{v₂, u₂} where
  obj S := Cat.of (Fiber p S.unop)
  map f := (K.pullback f.unop).toCatHom
  map_id S := by
    rw [unop_id, hK.1.pullback_id]
    rfl
  map_comp f g := by
    rw [unop_comp, ← hK.pullback_comp]
    rfl

end Cleavage

/-! ### Group extensions -/

section Groups

variable {F G : Type*} [Group F] [Group G] (φ : F →* G)

/-- VI.9: the cleavage of `SingleObj F ⥤ SingleObj G` defined by a set-theoretic section `s`
of `φ`: the transport along `g` is `s g`. -/
noncomputable def cleavageOfSection (s : G → F) (hs : ∀ g, φ (s g) = g) :
    Cleavage (SingleObj.mapHom F G φ) :=
  Cleavage.ofLifts (fun _ _ ↦ ⟨SingleObj.star F, rfl⟩)
    (fun g _ ↦ (s g : SingleObj.star F ⟶ SingleObj.star F))
    (fun {R S} g ξ ↦ by
      let x : SingleObj.star F ⟶ ξ.val := s g
      have : IsHomLift (SingleObj.mapHom F G φ) g x := by
        have h := IsHomLift.map (SingleObj.mapHom F G φ) x
        have hx : (SingleObj.mapHom F G φ).map x = g := hs g
        rwa [hx] at h
      infer_instance)

/-- VI.9: the section of `φ` given by the transports of a cleavage. -/
def sectionOfCleavage (K : Cleavage (SingleObj.mapHom F G φ)) : G → F :=
  fun g ↦ K.transport (R := SingleObj.star G) (S := SingleObj.star G) g ⟨SingleObj.star F, rfl⟩

theorem sectionOfCleavage_spec (K : Cleavage (SingleObj.mapHom F G φ)) (g : G) :
    φ (sectionOfCleavage φ K g) = g := by
  have := K.transport_isCartesian (R := SingleObj.star G) (S := SingleObj.star G) g
    ⟨SingleObj.star F, rfl⟩
  have h := IsHomLift.fac' (SingleObj.mapHom F G φ) (R := SingleObj.star G)
    (S := SingleObj.star G) g (K.transport (R := SingleObj.star G) (S := SingleObj.star G) g
      ⟨SingleObj.star F, rfl⟩)
  change φ (sectionOfCleavage φ K g) = (1 * g) * 1 at h
  rw [h, mul_one, one_mul]

/-- VI.9: cleavages of `SingleObj F` over `SingleObj G` correspond bijectively to the
set-theoretic sections of `φ` (systems of representatives of `F` modulo `ker φ`). -/
noncomputable def cleavageEquivSections :
    Cleavage (SingleObj.mapHom F G φ) ≃ {s : G → F // ∀ g, φ (s g) = g} where
  toFun K := ⟨sectionOfCleavage φ K, sectionOfCleavage_spec φ K⟩
  invFun s := cleavageOfSection φ s.1 s.2
  left_inv K := by
    refine Cleavage.ext' (fun _ _ ↦ rfl) fun g ξ ↦ ?_
    change sectionOfCleavage φ K g = 𝟙 _ ≫ K.transport g ξ
    rw [Category.id_comp]
    rfl
  right_inv _ := rfl

/-- VI.9: the cleavage defined by a section `s` is a splitting iff `s` is a homomorphism. -/
theorem cleavageOfSection_isSplitting_iff (s : G → F) (hs : ∀ g, φ (s g) = g) :
    (cleavageOfSection φ s hs).IsSplitting ↔ ∀ a b, s (a * b) = s a * s b := by
  constructor
  · rintro ⟨-, hc⟩ a b
    obtain ⟨h, hab⟩ := hc (U := SingleObj.star G) (T := SingleObj.star G)
      (S := SingleObj.star G) a b ⟨SingleObj.star F, rfl⟩
    change s a * s b = s (a * b) * 1 at hab
    rw [hab, mul_one]
  · intro hs'
    have h1 : s 1 = 1 := by
      have := hs' 1 1
      rw [one_mul] at this
      exact left_eq_mul.mp this
    refine ⟨fun S ξ ↦ ⟨rfl, ?_⟩, fun {U T S} f g ξ ↦ ⟨rfl, ?_⟩⟩
    · change s 1 = 1
      exact h1
    · change s f * s g = s (f * g) * 1
      rw [hs', mul_one]

/-- VI.9: `SingleObj F` admits a splitting over `SingleObj G` iff the extension `φ` splits, i.e.
`φ` has a homomorphic section. -/
theorem exists_isSplitting_iff :
    (∃ K : Cleavage (SingleObj.mapHom F G φ), K.IsSplitting) ↔
      ∃ σ : G →* F, ∀ g, φ (σ g) = g := by
  constructor
  · rintro ⟨K, hK⟩
    let s := (cleavageEquivSections φ K).1
    have hs : ∀ a b, s (a * b) = s a * s b := by
      have : K = cleavageOfSection φ s (cleavageEquivSections φ K).2 :=
        ((cleavageEquivSections φ).left_inv K).symm
      rw [this] at hK
      exact (cleavageOfSection_isSplitting_iff φ s _).mp hK
    exact ⟨MonoidHom.mk' s hs, (cleavageEquivSections φ K).2⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨cleavageOfSection φ σ hσ, (cleavageOfSection_isSplitting_iff φ σ hσ).mpr (map_mul σ)⟩

end Groups

/-! ### Rigid and reduced fibers -/

section Rigid

variable (A : Type*) [Category A]

/-- VI.9: a category is rigid if every automorphism is an identity. -/
def IsRigidCategory : Prop := ∀ (a : A) (e : a ≅ a), e = Iso.refl a

/-- VI.9: a category is reduced if isomorphic objects are equal. -/
def IsReducedCategory : Prop := ∀ a b : A, Nonempty (a ≅ b) → a = b

variable {A}

/-- In a rigid and reduced category every isomorphism is an identification `eqToIso`. -/
theorem eq_eqToIso_of_rigid_reduced (hr : IsRigidCategory A) (hred : IsReducedCategory A)
    {a b : A} (e : a ≅ b) : ∃ h : a = b, e = eqToIso h := by
  obtain rfl := hred a b ⟨e⟩
  exact ⟨rfl, hr a e⟩

end Rigid

namespace Cleavage

variable [IsFibered p] (hr : ∀ S, IsRigidCategory (Fiber p S))
  (hred : ∀ S, IsReducedCategory (Fiber p S))
include hr hred

/-- VI.9: if the fibers of a fibered category are rigid and reduced, every cleavage is a
splitting. -/
theorem isSplitting_of_rigid_reduced (K : Cleavage p) : K.IsSplitting := by
  refine (K.isSplitting_iff).mpr ⟨fun S ξ ↦ ?_, fun {U T S} f g ξ ↦ ?_⟩
  · obtain ⟨h, he⟩ := eq_eqToIso_of_rigid_reduced (hr S) (hred S) (asIso (K.transportId S ξ))
    refine ⟨congrArg Subtype.val h, ?_⟩
    have := congrArg (fun e ↦ e.hom.val) he
    simpa [transportId] using this
  · obtain ⟨h, he⟩ := eq_eqToIso_of_rigid_reduced (hr U) (hred U) (asIso (K.comparison f g ξ))
    exact ⟨congrArg Subtype.val h, by simpa using congrArg (fun e ↦ e.hom.val) he⟩

/-- VI.9: if the fibers of a fibered category are rigid and reduced, it has exactly one
cleavage. -/
theorem eq_of_rigid_reduced (K K' : Cleavage p) : K = K' := by
  have key : ∀ {R S : E} (f : R ⟶ S) (ξ : Fiber p S), ∃ h : (K.pullback f).obj ξ =
      (K'.pullback f).obj ξ, K.transport f ξ =
        eqToHom (congrArg Subtype.val h) ≫ K'.transport f ξ := by
    intro R S f ξ
    let e := IsCartesian.domainUniqueUpToIso p f (K'.transport f ξ) (K.transport f ξ)
    have : IsHomLift p (𝟙 R) e.hom := inferInstance
    let e' : (K.pullback f).obj ξ ≅ (K'.pullback f).obj ξ := fiberIso e
    obtain ⟨h, he⟩ := eq_eqToIso_of_rigid_reduced (hr R) (hred R) e'
    refine ⟨h, ?_⟩
    have hval : e.hom = eqToHom (congrArg Subtype.val h) := by
      have := congrArg (fun i ↦ i.hom.val) he
      simp only [eqToIso.hom, fiber_eqToHom_val] at this
      exact this
    rw [← hval]
    exact (IsCartesian.fac p f (K'.transport f ξ) (K.transport f ξ)).symm
  exact ext' (fun f ξ ↦ (key f ξ).1) (fun f ξ ↦ (key f ξ).2)

end Cleavage

end SGA.SGA1.ExposeVI
