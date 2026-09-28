/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.QuotientBaseChange
import SGA.SGA1.ExposeV.RelativeQuotient
import SGA.SGA1.ExposeVIII.MorphismDescent
import SGA.SGA1.ExposeV.SumOfCopies
import SGA.SGA1.ExposeV.QuotientPrincipal

/-!
# SGA 1, Exposé V: faithfully flat descent of quotients, and V.2.6 for schemes

* The converse of V.1.9 for a faithfully flat quasi-compact change of base, "which we had
  forgotten to make explicit" (proof of V.2.6): if `p : X ⟶ Y` is affine and invariant and
  `X ×_Y Y₁ ⟶ Y₁` is a quotient by `G` for some faithfully flat quasi-compact `Y₁ ⟶ Y`, then
  `p` satisfies the conditions of V.1.3 (`sectionsAreInvariant_of_isQuotient_pullback`). The
  relative quotient `X/G ⟶ Y` of Cor. V.1.8 becomes an isomorphism after base change (V.1.9 and
  uniqueness of quotients), hence is one by fpqc descent of isomorphisms (Exp. VIII).
* The trivial covering `Y × G` with `G` acting by right translations
  (`sumCopiesRightAction`), which is finite over `Y` (`isFinite_sigmaDesc`) with quotient `Y`
  (`isQuotient_sumCopiesRightAction`).
* V.2.6 for any base scheme (`principalCovering_tfae`): the conditions (i) finite with
  `Y = X/G` and trivial inertia, (ii) trivial after a faithfully flat quasi-compact base change,
  (ii bis) trivial after a finite étale surjective base change, (iii) faithfully flat,
  quasi-compact and formally principal homogeneous, are equivalent. The implication
  (ii) ⇒ (i) is `principal_of_isTrivialization`; SGA assumes `Y` locally noetherian, which is not
  needed here.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite MorphismProperty

namespace SGA.SGA1.ExposeV

section Descent

variable {G : Type*} {X Y Q : Scheme.{u}} {T : G → (X ⟶ X)}

lemma SectionsAreInvariant.congr_hom {p p' : X ⟶ Y} (h : p = p') {hTp : ∀ g, T g ≫ p = p}
    {hTp' : ∀ g, T g ≫ p' = p'} {U : Y.Opens} (hs : SectionsAreInvariant T p hTp U) :
    SectionsAreInvariant T p' hTp' U := by
  subst h
  exact hs

/-- The condition of V.1.3 is transported along an isomorphism of the target. -/
lemma SectionsAreInvariant.comp_isIso {q : X ⟶ Q} (r : Q ⟶ Y) [IsIso r]
    {hTq : ∀ g, T g ≫ q = q} {hTqr : ∀ g, T g ≫ q ≫ r = q ≫ r} {U : Y.Opens}
    (hs : SectionsAreInvariant T q hTq (r ⁻¹ᵁ U)) : SectionsAreInvariant T (q ≫ r) hTqr U := by
  have hr : Function.Bijective (r.app U) := ConcreteCategory.bijective_of_isIso _
  refine ⟨?_, fun s hs' ↦ ?_⟩
  · rw [Scheme.Hom.comp_app]
    exact hs.1.comp hr.1
  · obtain ⟨t, ht⟩ := hs.2 s hs'
    obtain ⟨t', rfl⟩ := hr.2 t
    exact ⟨t', by rw [Scheme.Hom.comp_app]; exact ht⟩

variable [Group G] [Finite G] (hT : IsRightAction T) {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- Auxiliary to `sectionsAreInvariant_of_isQuotient_pullback`: if `p = q ≫ r` with `q` an affine
morphism satisfying the conditions of V.1.3 and `X ×_Y Y₁ ⟶ Y₁` is a quotient, where `Y₁ ⟶ Y` is
faithfully flat and quasi-compact, then `r` is an isomorphism. -/
lemma isIso_of_isQuotient_pullback {q : X ⟶ Q} (r : Q ⟶ Y) (hqr : q ≫ r = p)
    (hTq : ∀ k, T k ≫ q = q) [IsAffineHom q] (hsecq : ∀ W, SectionsAreInvariant T q hTq W)
    {Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [Surjective g] [Flat g] [QuasiCompact g]
    (h₁ : IsQuotient (pullbackAction hTp g) (pullback.snd p g)) : IsIso r := by
  subst hqr
  have hq' := isQuotient_pullback_snd hTq (pullback.fst r g) hT hsecq
  let e : pullback q (pullback.fst r g) ≅ pullback (q ≫ r) g := pullbackRightPullbackFstIso r g q
  have he' : ∀ k, pullbackAction hTq (pullback.fst r g) k ≫ e.hom =
      e.hom ≫ pullbackAction hTp g k := by
    intro k
    apply pullback.hom_ext
    · simp [e, pullbackAction, pullback.map]
    · simp [e, pullbackAction, pullback.map]
  have he : ∀ k, pullbackAction hTp g k ≫ e.symm.hom =
      e.symm.hom ≫ pullbackAction hTq (pullback.fst r g) k := by
    intro k
    simp only [Iso.symm_hom]
    rw [eq_comm, Iso.inv_comp_eq, ← reassoc_of% (he' k), Iso.hom_inv_id, Category.comp_id]
  have hq'' := hq'.iso_comp e.symm he
  have hsnd : (e.symm.hom ≫ pullback.snd q (pullback.fst r g)) ≫ pullback.snd r g =
      pullback.snd (q ≫ r) g := by
    simp [e]
  have hdesc : hq''.desc (pullback.snd (q ≫ r) g) h₁.comp_eq = pullback.snd r g :=
    hq''.hom_ext (by rw [hq''.fac, hsnd])
  have : IsIso (pullback.snd r g) := by
    rw [← hdesc]
    exact (hq''.uniqueIso h₁).isIso_hom
  exact of_pullback_snd_of_descendsAlong (P := isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ (this : IsIso _)

include hT in
/-- The converse of V.1.9 for a faithfully flat quasi-compact change of base (used in the proof of
V.2.6): let `p : X ⟶ Y` be affine and invariant, and `g : Y₁ ⟶ Y` faithfully flat and
quasi-compact. If `X ×_Y Y₁ ⟶ Y₁` is a quotient by `G`, then `p` satisfies the conditions of
V.1.3, so `Y = X/G`. The relative quotient `X/G = Spec_Y (p_* 𝒪_X)^G ⟶ Y` (Cor. V.1.8) becomes an
isomorphism after the base change (V.1.9 and uniqueness of quotients), hence is one (descent of
isomorphisms). -/
theorem sectionsAreInvariant_of_isQuotient_pullback [IsAffineHom p] {Y₁ : Scheme.{u}}
    (g : Y₁ ⟶ Y) [Surjective g] [Flat g] [QuasiCompact g]
    (h₁ : IsQuotient (pullbackAction hTp g) (pullback.snd p g)) (U : Y.Opens) :
    SectionsAreInvariant T p hTp U := by
  have hqr : toQuotient hTp ≫ fromQuotient hTp = p := toQuotient_fromQuotient hTp
  have hTq : ∀ k, T k ≫ toQuotient hTp = toQuotient hTp := comp_toQuotient hTp
  have hsecq := sectionsAreInvariant_toQuotient hTp
  have := isIso_of_isQuotient_pullback hT hTp (fromQuotient hTp) hqr hTq hsecq g h₁
  exact ((hsecq (fromQuotient hTp ⁻¹ᵁ U)).comp_isIso (fromQuotient hTp)
    (hTqr := fun k ↦ by rw [reassoc_of% (hTq k)])).congr_hom hqr

include hT in
/-- The converse of V.1.9 in the form "the conditions of V.1.3 descend": if `g : Y₁ ⟶ Y` is
faithfully flat and quasi-compact and `X ×_Y Y₁ ⟶ Y₁` is affine with
`𝒪_{Y₁} = (p₁_* 𝒪_{X₁})^G`, then `p` is affine (fpqc descent, Exp. VIII) and
`𝒪_Y = (p_* 𝒪_X)^G`. -/
theorem isAffineHom_and_sectionsAreInvariant_of_pullback {Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y)
    [Surjective g] [Flat g] [QuasiCompact g] [IsAffineHom (pullback.snd p g)]
    (hsec₁ : ∀ V, SectionsAreInvariant (pullbackAction hTp g) (pullback.snd p g)
      (fun k ↦ pullbackAction_snd hTp g k) V) :
    IsAffineHom p ∧ ∀ U, SectionsAreInvariant T p hTp U := by
  have : IsAffineHom p := of_pullback_snd_of_descendsAlong (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ‹_›
  exact ⟨this, sectionsAreInvariant_of_isQuotient_pullback hT hTp g
    (isQuotient_of_sectionsAreInvariant (isRightAction_pullbackAction hTp g hT)
      fun V _ ↦ hsec₁ V)⟩

end Descent

section TrivialCovering

set_option backward.isDefEq.respectTransparency false in
/-- A finite sum of finite morphisms is finite (the index type is `Fin n`). -/
lemma isFinite_sigmaDesc_fin : ∀ (n : ℕ) {Z : Fin n → Scheme.{u}} {X : Scheme.{u}}
    (f : ∀ i, Z i ⟶ X), (∀ i, IsFinite (f i)) → IsFinite (Sigma.desc f)
  | 0, Z, X, f, _ => by
    have : IsEmpty (show Scheme.{u} from ∐ Z) := isInitial_iff_isEmpty.mp
      ⟨isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit (Discrete.functor Z))⟩
    infer_instance
  | n + 1, Z, X, f, hf => by
    have := isFinite_sigmaDesc_fin n (fun i ↦ f i.succ) (fun i ↦ hf i.succ)
    have := hf 0
    let hc := extendCofanIsColimit Z (colimit.isColimit (Discrete.functor fun i : Fin n ↦ Z i.succ))
      (coprodIsCoprod (Z 0) (∐ fun i : Fin n ↦ Z i.succ))
    let e := hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor Z))
    have he : e.hom ≫ Sigma.desc f = coprod.desc (f 0) (Sigma.desc fun i : Fin n ↦ f i.succ) := by
      refine hc.hom_ext fun ⟨j⟩ ↦ ?_
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp [extendCofan, Fin.cases_zero]
      · simp [extendCofan, Fin.cases_succ]
    have : IsFinite (e.hom ≫ Sigma.desc f) := by rw [he]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom _).mp this

set_option backward.isDefEq.respectTransparency false in
/-- A finite sum of finite morphisms is finite. -/
lemma isFinite_sigmaDesc {ι : Type u} [Finite ι] {Z : ι → Scheme.{u}} {X : Scheme.{u}}
    (f : ∀ i, Z i ⟶ X) (hf : ∀ i, IsFinite (f i)) : IsFinite (Sigma.desc f) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have := isFinite_sigmaDesc_fin n (fun i ↦ f (e.symm i)) (fun i ↦ hf _)
  have he : (Sigma.reindex e.symm Z).hom ≫ Sigma.desc f = Sigma.desc fun i ↦ f (e.symm i) :=
    Sigma.hom_ext _ _ fun i ↦ by
      simp only [Sigma.ι_reindex_hom_assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
      exact (Sigma.ι_desc (fun i ↦ f (e.symm i)) i).symm
  have : IsFinite ((Sigma.reindex e.symm Z).hom ≫ Sigma.desc f) := by rw [he]; infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).mp this

variable (Y : Scheme.{u}) (G : Type u) [Group G]

/-- The right action of `G` on the trivial covering `Y × G` by right translations,
`(y, e) · g = (y, e g)`. -/
noncomputable def sumCopiesRightAction (g : G) : sumCopies Y G ⟶ sumCopies Y G :=
  Sigma.desc fun e ↦ Sigma.ι (fun _ : G ↦ Y) (e * g)

@[reassoc (attr := simp)]
lemma ι_sumCopiesRightAction (g e : G) :
    Sigma.ι (fun _ : G ↦ Y) e ≫ sumCopiesRightAction Y G g = Sigma.ι (fun _ : G ↦ Y) (e * g) :=
  Sigma.ι_desc _ _

lemma isRightAction_sumCopiesRightAction : IsRightAction (sumCopiesRightAction Y G) where
  map_one := Sigma.hom_ext _ _ fun e ↦ by simp
  map_mul g h := Sigma.hom_ext _ _ fun e ↦ by simp [mul_assoc]

@[reassoc (attr := simp)]
lemma sumCopiesRightAction_comp_toBase (g : G) :
    sumCopiesRightAction Y G g ≫ sumCopiesToBase Y G = sumCopiesToBase Y G :=
  Sigma.hom_ext _ _ fun e ↦ by simp

/-- The trivial covering: `Y = (Y × G)/G`. -/
theorem isQuotient_sumCopiesRightAction :
    IsQuotient (sumCopiesRightAction Y G) (sumCopiesToBase Y G) := by
  have hsplit : Sigma.ι (fun _ : G ↦ Y) 1 ≫ sumCopiesToBase Y G = 𝟙 Y := by simp
  refine ⟨sumCopiesRightAction_comp_toBase Y G, fun {Z} f hf ↦ ?_⟩
  refine ⟨Sigma.ι (fun _ : G ↦ Y) 1 ≫ f, Sigma.hom_ext _ _ fun e ↦ ?_, fun h hh ↦ ?_⟩
  · have := Sigma.ι (fun _ : G ↦ Y) 1 ≫= hf e
    simp only [ι_sumCopiesRightAction_assoc, one_mul] at this
    simp [this]
  · rw [← hh, reassoc_of% hsplit]

/-- The trivial covering `Y × G ⟶ Y` is finite. -/
instance [Finite G] : IsFinite (sumCopiesToBase Y G) :=
  isFinite_sigmaDesc _ fun _ ↦ inferInstance

end TrivialCovering

section Principal

variable {G : Type u} [Group G] [Finite G] {X Y : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

/-- Condition (ii) of V.2.6 for a given change of base `g : Y₁ ⟶ Y`: `Φ` is an isomorphism of
`Y₁`-schemes with operators from the trivial covering `Y₁ × G` onto `X ×_Y Y₁`. -/
structure IsTrivialization {Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) (Φ : sumCopies Y₁ G ⟶ pullback p g) :
    Prop where
  isIso : IsIso Φ
  comp_snd : Φ ≫ pullback.snd p g = sumCopiesToBase Y₁ G
  equivariant : ∀ h, sumCopiesRightAction Y₁ G h ≫ Φ = Φ ≫ pullbackAction hTp g h

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.2.6, (ii) ⇒ (i), for any `Y` (SGA assumes `Y` locally noetherian): if `X` becomes trivial
after a faithfully flat quasi-compact change of base `Y₁ ⟶ Y`, then `X` is finite over `Y`,
`Y = X/G` (conditions of V.1.3) and the inertia groups are trivial. Finiteness descends
(Exp. VIII), `Y = X/G` by the converse of V.1.9 (`sectionsAreInvariant_of_isQuotient_pullback`)
and the inertia groups by V.2.1. -/
theorem principal_of_isTrivialization {Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [Surjective g] [Flat g]
    [QuasiCompact g] {Φ : sumCopies Y₁ G ⟶ pullback p g} (hΦ : IsTrivialization hTp g Φ) :
    IsFinite p ∧ (∀ U, SectionsAreInvariant T p hTp U) ∧
      ∀ x h, h ∈ inertiaGroup T x → h = 1 := by
  have := hΦ.isIso
  have hsnd : pullback.snd p g = inv Φ ≫ sumCopiesToBase Y₁ G := by
    rw [IsIso.eq_inv_comp, hΦ.comp_snd]
  have hfin : IsFinite p := by
    have : IsFinite (pullback.snd p g) := by rw [hsnd]; infer_instance
    exact of_pullback_snd_of_descendsAlong (P := @IsFinite)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ this
  have he : ∀ h, pullbackAction hTp g h ≫ (asIso Φ).symm.hom =
      (asIso Φ).symm.hom ≫ sumCopiesRightAction Y₁ G h := by
    intro h
    simp only [Iso.symm_hom, asIso_inv]
    rw [IsIso.comp_inv_eq, Category.assoc, hΦ.equivariant, IsIso.inv_hom_id_assoc]
  have hq := (isQuotient_sumCopiesRightAction Y₁ G).iso_comp (asIso Φ).symm he
  simp only [Iso.symm_hom, asIso_inv, ← hsnd] at hq
  refine ⟨hfin, sectionsAreInvariant_of_isQuotient_pullback hT hTp g hq, fun x h hh ↦ ?_⟩
  obtain ⟨x', rfl⟩ := (pullback.fst p g).surjective x
  have hh' : h ∈ inertiaGroup (pullbackAction hTp g) x' := by
    exact (Set.ext_iff.mp (inertiaGroup_pullback hTp g x') h).mpr hh
  have hd := inertiaGroup_subset_decompositionGroup _ x' hh'
  obtain ⟨e, y, hy⟩ := exists_sigmaι_eq (inv Φ x')
  have hx' : x' = Φ (Sigma.ι (fun _ : G ↦ Y₁) e y) := by
    rw [hy, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have key : Φ (Sigma.ι (fun _ : G ↦ Y₁) (e * h) y) = Φ (Sigma.ι (fun _ : G ↦ Y₁) e y) := by
    have h₁ := congr($(Sigma.ι (fun _ : G ↦ Y₁) e ≫= hΦ.equivariant h) y)
    simp only [ι_sumCopiesRightAction_assoc, Scheme.Hom.comp_apply] at h₁
    rw [h₁, ← hx']
    exact hd
  have hinj : Function.Injective Φ := (asIso Φ).hom.homeomorph.injective
  have := eq_of_sigmaι_apply_eq (hinj key)
  simpa using this

variable (T) in
/-- The morphism `X × G ⟶ X ×_Y X`, `(x, e) ↦ (T e x, x)`, which exhibits `X ×_Y X` over the
second factor as the trivial covering when `X` is formally principal homogeneous. -/
noncomputable def selfTrivialization : sumCopies X G ⟶ pullback p p :=
  Sigma.desc fun e : G ↦ pullback.lift (T e) (𝟙 X) (by rw [hTp, Category.id_comp])

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] in
include hT in
/-- The base change of `X` along `p` itself is trivial exactly when `X` is formally principal
homogeneous: `selfTrivialization` is a trivialization iff `X × G ⟶ X ×_Y X`,
`(x, e) ↦ (x, T e x)`, is an isomorphism. -/
lemma isTrivialization_selfTrivialization_iff :
    IsTrivialization hTp p (selfTrivialization T hTp) ↔
      IsIso (Sigma.desc fun h : G ↦ pullback.lift (𝟙 X) (T h) (by rw [Category.id_comp, hTp])
        : ∐ (fun _ : G ↦ X) ⟶ pullback p p) := by
  have hsym : selfTrivialization T hTp = (Sigma.desc fun h : G ↦ pullback.lift (𝟙 X) (T h)
      (by rw [Category.id_comp, hTp])) ≫ (pullbackSymmetry p p).hom := by
    refine Sigma.hom_ext _ _ fun e ↦ pullback.hom_ext ?_ ?_ <;> simp [selfTrivialization]
  have hsnd : selfTrivialization T hTp ≫ pullback.snd p p = sumCopiesToBase X G :=
    Sigma.hom_ext _ _ fun e ↦ by simp [selfTrivialization]
  have heq : ∀ h, sumCopiesRightAction X G h ≫ selfTrivialization T hTp =
      selfTrivialization T hTp ≫ pullbackAction hTp p h := by
    intro h
    refine Sigma.hom_ext _ _ fun e ↦ pullback.hom_ext ?_ ?_
    · simp [selfTrivialization, pullbackAction, pullback.map, hT.map_mul]
    · simp [selfTrivialization, pullbackAction, pullback.map]
  constructor
  · intro h
    have := h.isIso
    rw [hsym] at this
    exact IsIso.of_isIso_comp_right _ (pullbackSymmetry p p).hom
  · intro h
    exact ⟨by rw [hsym]; infer_instance, hsnd, heq⟩

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.2.6, for any `Y` (SGA assumes `Y` locally noetherian): for a finite group `G` acting on
the right on `X` over `Y`, the following are equivalent:
(i) `X` is finite over `Y`, `Y = X/G` (conditions of V.1.3) and all inertia groups are trivial;
(ii) `X` becomes trivial after a faithfully flat quasi-compact change of base `Y₁ ⟶ Y`;
(ii bis) the same with `Y₁ ⟶ Y` finite, étale and surjective (one can take `Y₁ = X`);
(iii) `X` is faithfully flat and quasi-compact over `Y` and formally principal homogeneous:
`X × G ⟶ X ×_Y X`, `(x, h) ↦ (x, T h x)`, is an isomorphism. -/
theorem principalCovering_tfae : List.TFAE
    [IsFinite p ∧ (∀ U, SectionsAreInvariant T p hTp U) ∧ ∀ x h, h ∈ inertiaGroup T x → h = 1,
      ∃ (Y₁ : Scheme.{u}) (g : Y₁ ⟶ Y) (Φ : sumCopies Y₁ G ⟶ pullback p g),
        Surjective g ∧ Flat g ∧ QuasiCompact g ∧ IsTrivialization hTp g Φ,
      ∃ (Y₁ : Scheme.{u}) (g : Y₁ ⟶ Y) (Φ : sumCopies Y₁ G ⟶ pullback p g),
        IsFinite g ∧ Etale g ∧ Surjective g ∧ IsTrivialization hTp g Φ,
      Surjective p ∧ Flat p ∧ QuasiCompact p ∧
        IsIso (Sigma.desc fun h : G ↦ pullback.lift (𝟙 X) (T h) (by rw [Category.id_comp, hTp])
          : ∐ (fun _ : G ↦ X) ⟶ pullback p p)] := by
  tfae_have 1 → 4 := by
    rintro ⟨hfin, hsec, hfree⟩
    have : Etale p := etale_of_inertiaGroup_eq hT hTp hsec hfree
    exact ⟨⟨(surjective_and_orbit_of_sectionsAreInvariant hT fun U _ ↦ hsec U).1⟩,
      inferInstance, inferInstance, isIso_sigmaDesc_pullbackLift hT hTp hsec hfree⟩
  tfae_have 4 → 2 := by
    rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨X, p, selfTrivialization T hTp, h₁, h₂, h₃,
      (isTrivialization_selfTrivialization_iff hT hTp).mpr h₄⟩
  tfae_have 1 → 3 := by
    rintro ⟨hfin, hsec, hfree⟩
    have : Etale p := etale_of_inertiaGroup_eq hT hTp hsec hfree
    exact ⟨X, p, selfTrivialization T hTp, hfin, this,
      ⟨(surjective_and_orbit_of_sectionsAreInvariant hT fun U _ ↦ hsec U).1⟩,
      (isTrivialization_selfTrivialization_iff hT hTp).mpr
        (isIso_sigmaDesc_pullbackLift hT hTp hsec hfree)⟩
  tfae_have 3 → 2 := by
    rintro ⟨Y₁, g, Φ, h₁, h₂, h₃, h₄⟩
    exact ⟨Y₁, g, Φ, h₃, inferInstance, inferInstance, h₄⟩
  tfae_have 2 → 1 := by
    rintro ⟨Y₁, g, Φ, h₁, h₂, h₃, h₄⟩
    exact principal_of_isTrivialization hT hTp g h₄
  tfae_finish

end Principal

end SGA.SGA1.ExposeV
