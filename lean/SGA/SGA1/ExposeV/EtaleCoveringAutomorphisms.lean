/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Etale.Kaehler
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeV.FiniteQuotientProperties
import SGA.SGA1.ExposeV.PrincipalCovering

/-!
# SGA 1, Exposé V, §3: automorphisms and morphisms of étale coverings

* V.3.5: a morphism `f : X ⟶ X'` of étale coverings of `Y` is étale, its image `X''` is open and
  closed, and `X ⟶ X''` is surjective étale (`exists_isClopen_range_factorization`).
* V.3.6: `X ⟶ X''` is an effective (strict) epimorphism and `X'' ⟶ X'` a strict (regular)
  monomorphism (`regularMonoOfIsClopen`); a factorization "strict epi followed by mono" is unique
  up to unique isomorphism.
* V.3.3 (the case needed by SGA): étaleness descends along faithfully flat étale maps
  (`etale_of_etale_of_faithfullyFlat`); the other cases are I.4.6 and I.4.8.
* V.3.2 and V.3.4 for `X = Spec A` connected with `G` acting faithfully: `A^G → A` is finite
  étale, and `A^G` is finite étale over the base.
* V.2.2 (ii) when all inertia groups are trivial: `A^H` is étale over `A^G` for every `H`.
* V.3.7 for any connected base (`isIso_of_bijective_on_geometricPoints`): the diagonal of `u` is
  open and closed, and a geometric point off it (resp. off the image of `u`) would contradict
  injectivity (resp. surjectivity) on geometric points; then `u` is a flat surjective
  monomorphism.
* V.3.4 in general is proved in `QuotientEtale.lean`, V.3.1 and V.3.2 in general in
  `QuotientComponents.lean`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace SGA.SGA1.ExposeV

section Covering

variable {X X' Y : Scheme.{u}} (f : X ⟶ X') (q : X ⟶ Y) (q' : X' ⟶ Y)

/-- V.3.5: let `X` be an étale covering of `Y` (finite étale) and `X'` unramified and separated
over `Y` (for instance an étale covering). A `Y`-morphism `f : X ⟶ X'` is étale, and its image is
open and closed. -/
theorem etale_and_isClopen_range [IsFinite q] [Etale q] [LocallyOfFiniteType q']
    [FormallyUnramified q'] [IsSeparated q'] (hf : f ≫ q' = q) :
    Etale f ∧ IsClopen (Set.range f) := by
  subst hf
  have : Etale f := Etale.of_comp f q'
  have : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f q'
  exact ⟨inferInstance, ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩⟩

/-- V.3.5: `f` factors as a surjective étale morphism `X ⟶ X''` followed by the inclusion of the
open and closed subscheme `X'' = f(X)` of `X'`. -/
theorem exists_isClopen_range_factorization [IsFinite q] [Etale q] [LocallyOfFiniteType q']
    [FormallyUnramified q'] [IsSeparated q'] (hf : f ≫ q' = q) :
    ∃ (U : X'.Opens) (g : X ⟶ U.toScheme), IsClopen (U : Set X') ∧ g ≫ U.ι = f ∧
      Etale g ∧ Surjective g := by
  obtain ⟨_, hclopen⟩ := etale_and_isClopen_range f q q' hf
  let U : X'.Opens := ⟨Set.range f, hclopen.isOpen⟩
  have hU : Set.range f ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; rfl
  refine ⟨U, IsOpenImmersion.lift U.ι f hU, hclopen, IsOpenImmersion.lift_fac _ _ _, ?_, ⟨?_⟩⟩
  · have : Etale (IsOpenImmersion.lift U.ι f hU ≫ U.ι) := by
      rw [IsOpenImmersion.lift_fac]; infer_instance
    exact Etale.of_comp _ U.ι
  · rintro ⟨_, x, rfl⟩
    refine ⟨x, Subtype.ext ?_⟩
    have := congr($(IsOpenImmersion.lift_fac U.ι f hU) x)
    rw [Scheme.Hom.comp_apply] at this
    exact this

/-- V.3.6: with the notation of V.3.5, `X ⟶ X''` is a strict (effective) epimorphism and
`X'' ⟶ X'` a monomorphism in the category of schemes. -/
theorem exists_effectiveEpi_mono_factorization [IsFinite q] [Etale q] [LocallyOfFiniteType q']
    [FormallyUnramified q'] [IsSeparated q'] (hf : f ≫ q' = q) :
    ∃ (U : X'.Opens) (g : X ⟶ U.toScheme), IsClopen (U : Set X') ∧ g ≫ U.ι = f ∧
      EffectiveEpi g ∧ Mono U.ι := by
  obtain ⟨U, g, hU, hg, _, _⟩ := exists_isClopen_range_factorization f q q' hf
  exact ⟨U, g, hU, hg, inferInstance, inferInstance⟩

/-- The inclusion of an open and closed subscheme `U` of `S` is a strict (regular) monomorphism:
it is the equalizer of the two morphisms `S ⟶ S ⨿ S` which agree on `U` and send `S ∖ U` into
different summands. -/
noncomputable def regularMonoOfIsClopen {S : Scheme.{u}} (U : S.Opens) (hU : IsClopen (U : Set S)) :
    RegularMono U.ι := by
  let W : S.Opens := ⟨(U : Set S)ᶜ, hU.isClosed.isOpen_compl⟩
  have hUW : IsCompl U.ι.opensRange W.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]; ext x; simp [W]
    · rw [codisjoint_iff]; ext x; simp [W]
  have H := (nonempty_isColimit_binaryCofanMk_of_isCompl U.ι W.ι hUW).some
  let a : S ⟶ S ⨿ S := coprod.inl
  let b : S ⟶ S ⨿ S := H.desc (BinaryCofan.mk (U.ι ≫ coprod.inl) (W.ι ≫ coprod.inr))
  have hb : U.ι ≫ b = U.ι ≫ a := H.fac _ ⟨.left⟩
  have hbW : W.ι ≫ b = W.ι ≫ coprod.inr := H.fac _ ⟨.right⟩
  refine ⟨S ⨿ S, a, b, hb.symm, Fork.IsLimit.mk' _ fun s ↦ ?_⟩
  have hs : Set.range s.ι ⊆ Set.range U.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra h
    have e1 : a (s.ι t) = b (s.ι t) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, s.condition]
    have e2 : b (s.ι t) = (coprod.inr : S ⟶ S ⨿ S) (s.ι t) := by
      have := congr($(hbW) ⟨s.ι t, h⟩)
      exact this
    rw [e2] at e1
    exact Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr S S).1 ⟨_, rfl⟩ ⟨_, rfl⟩ e1
  exact ⟨IsOpenImmersion.lift U.ι s.ι hs, IsOpenImmersion.lift_fac _ _ _,
    fun {m} hm ↦ by rw [← cancel_mono U.ι, IsOpenImmersion.lift_fac]; exact hm⟩

/-- V.3.6, with "strict monomorphism": with the notation of V.3.5, `X ⟶ X''` is a strict
(effective) epimorphism and `X'' ⟶ X'` a strict (regular) monomorphism. -/
theorem exists_effectiveEpi_isRegularMono_factorization [IsFinite q] [Etale q]
    [LocallyOfFiniteType q'] [FormallyUnramified q'] [IsSeparated q'] (hf : f ≫ q' = q) :
    ∃ (U : X'.Opens) (g : X ⟶ U.toScheme), IsClopen (U : Set X') ∧ g ≫ U.ι = f ∧
      EffectiveEpi g ∧ IsRegularMono U.ι := by
  obtain ⟨U, g, hU, hg, _, _⟩ := exists_isClopen_range_factorization f q q' hf
  exact ⟨U, g, hU, hg, inferInstance, isRegularMono_of_regularMono (regularMonoOfIsClopen U hU)⟩

end Covering

section Factorization

variable {C : Type*} [Category C]

/-- Remark after V.3.6: in any category, a factorization `f = e ≫ m` with `e` a strict
(effective) epimorphism and `m` a monomorphism is unique up to a unique isomorphism. -/
theorem exists_iso_of_effectiveEpi_mono {X Y I₁ I₂ : C} (e₁ : X ⟶ I₁) (m₁ : I₁ ⟶ Y)
    (e₂ : X ⟶ I₂) (m₂ : I₂ ⟶ Y) [EffectiveEpi e₁] [EffectiveEpi e₂] [Mono m₁] [Mono m₂]
    (h : e₁ ≫ m₁ = e₂ ≫ m₂) :
    ∃ φ : I₁ ≅ I₂, e₁ ≫ φ.hom = e₂ ∧ φ.hom ≫ m₂ = m₁ := by
  have key : ∀ {I I' : C} (e : X ⟶ I) (m : I ⟶ Y) (e' : X ⟶ I') (m' : I' ⟶ Y) [EffectiveEpi e]
      [Mono m'], e ≫ m = e' ≫ m' → ∀ {Z} (g₁ g₂ : Z ⟶ X), g₁ ≫ e = g₂ ≫ e → g₁ ≫ e' = g₂ ≫ e' :=
    fun e m e' m' _ _ h Z g₁ g₂ hg ↦ by
      rw [← cancel_mono m', Category.assoc, Category.assoc, ← h, reassoc_of% hg]
  let φ := EffectiveEpi.desc e₁ e₂ (key e₁ m₁ e₂ m₂ h)
  let ψ := EffectiveEpi.desc e₂ e₁ (key e₂ m₂ e₁ m₁ h.symm)
  have hφ : e₁ ≫ φ = e₂ := EffectiveEpi.fac _ _ _
  have hψ : e₂ ≫ ψ = e₁ := EffectiveEpi.fac _ _ _
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ, ?_⟩
  · rw [← cancel_epi e₁, reassoc_of% hφ, hψ, Category.comp_id]
  · rw [← cancel_epi e₂, reassoc_of% hψ, hφ, Category.comp_id]
  · rw [← cancel_epi e₁, reassoc_of% hφ, h]

end Factorization

section Descent

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra B A]
  [Algebra R A] [IsScalarTower R B A]

/-- Flatness descends along a faithfully flat `B → A`: if `A` is flat over `R`, so is `B`. -/
theorem flat_of_flat_of_faithfullyFlat [Module.Flat R A] [Module.FaithfullyFlat B A] :
    Module.Flat R B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let g : B ⊗[R] N →ₗ[B] B ⊗[R] P := AlgebraTensorModule.lTensor B B f
  change Function.Injective g
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B A g]
  let eN := AlgebraTensorModule.cancelBaseChange R B A A N
  let eP := AlgebraTensorModule.cancelBaseChange R B A A P
  have hcomm : ∀ x, eP (g.lTensor A x) = f.lTensor A (eN x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => simp [eP, eN, g]
      | add y y' hy hy' => simp only [tmul_add, map_add, hy, hy']
    | add x x' hx hx' => simp only [map_add, hx, hx']
  intro x x' hxx'
  apply eN.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap f hf
  rw [← hcomm, ← hcomm, hxx']

/-- Unramifiedness descends along a faithfully flat formally étale `B → A`. -/
theorem formallyUnramified_of_formallyUnramified_of_faithfullyFlat
    [Algebra.FormallyUnramified R A] [Algebra.FormallyEtale B A] [Module.FaithfullyFlat B A] :
    Algebra.FormallyUnramified R B := by
  rw [Algebra.formallyUnramified_iff]
  have : Subsingleton (A ⊗[B] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B A).toEquiv.subsingleton
  exact (Module.FaithfullyFlat.lTensor_reflects_triviality B A _)

/-- V.3.3, the case used in SGA (`X ⟶ X'` étale and surjective): if `R → A` is étale and
`B → A` is faithfully flat and étale, then `R → B` is étale, provided `B` is of finite
presentation over `R` (automatic for `R` noetherian and `B` of finite type). -/
theorem etale_of_etale_of_faithfullyFlat [Algebra.Etale R A] [Algebra.FormallyEtale B A]
    [Module.FaithfullyFlat B A] [Algebra.FinitePresentation R B] : Algebra.Etale R B :=
  have := flat_of_flat_of_faithfullyFlat (R := R) (B := B) (A := A)
  have := formallyUnramified_of_formallyUnramified_of_faithfullyFlat (R := R) (B := B) (A := A)
  .of_formallyUnramified_of_flat

end Descent

section Quotient

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {G : Type*} [Group G]
  [MulSemiringAction G A] [SMulCommClass G R A]

instance : Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G :=
  ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

instance : SMulCommClass G (FixedPoints.subalgebra R A G) A :=
  ⟨fun g b a ↦ by
    change g • (b.1 * a) = b.1 * g • a
    rw [smul_mul', b.2 g]⟩

variable [Finite G]

/-- V.3.2, for `X = Spec A` connected with `G` acting faithfully by `R`-automorphisms: if `A` is
unramified (e.g. étale) over `R`, the inertia groups are trivial (I.5.4), so `A` is a principal
covering of `A^G`; in particular `X ⟶ X/G` is (finite) étale. -/
theorem isPrincipalCovering_fixedPoints [Algebra.FormallyUnramified R A]
    [Algebra.EssFiniteType R A] (hA : ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ g : G, (∀ a : A, g • a = a) → g = 1) :
    IsPrincipalCovering (FixedPoints.subalgebra R A G) A G :=
  .of_inertia_eq_bot Subtype.val_injective fun Q hQ g hg ↦
    eq_one_of_mem_inertia (B := R) hA hfaith Q hQ.ne_top g hg

/-- V.3.4, for `X = Spec A` connected with `G` acting faithfully by `R`-automorphisms and `R`
noetherian: if `A` is finite étale over `R`, so is `A^G`. -/
theorem etale_and_finite_fixedPoints [IsNoetherianRing R] [Module.Finite R A] [Algebra.Etale R A]
    (hA : ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ g : G, (∀ a : A, g • a = a) → g = 1) :
    Algebra.Etale R (FixedPoints.subalgebra R A G) ∧
      Module.Finite R (FixedPoints.subalgebra R A G) := by
  have h := isPrincipalCovering_fixedPoints (R := R) hA hfaith
  have := h.etale
  have := h.galoisMap_bijective_and_faithfullyFlat.2
  have hfin : Module.Finite R (FixedPoints.subalgebra R A G) :=
    .of_injective (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective
  have : Algebra.FinitePresentation R (FixedPoints.subalgebra R A G) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨etale_of_etale_of_faithfullyFlat (A := A), hfin⟩

end Quotient

section FreeSubgroup

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G B A]

instance (H : Subgroup G) : Algebra.IsInvariant (FixedPoints.subalgebra B A H) A H :=
  ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

instance (H : Subgroup G) : SMulCommClass H (FixedPoints.subalgebra B A H) A :=
  ⟨fun g b a ↦ by
    change g • (b.1 * a) = b.1 * g • a
    rw [smul_mul', b.2 g]⟩

/-- V.2.2 (ii) when `G` acts freely (all inertia groups trivial), which is the case used in
SGA: for every subgroup `H` of `G`, `A^H` is étale over `B = A^G` (`B` noetherian). The proof
combines V.2.3 for `G` and for `H` with the descent V.3.3. -/
theorem etale_fixedPoints_of_inertia_eq_bot [IsNoetherianRing B] [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A))
    (hfree : ∀ Q : Ideal A, Q.IsPrime → ∀ g ∈ Q.inertia G, g = 1) (H : Subgroup G) :
    Algebra.Etale B (FixedPoints.subalgebra B A H) := by
  have hG := IsPrincipalCovering.of_inertia_eq_bot hinj hfree
  have := hG.etale
  have := hG.finite
  have hH : IsPrincipalCovering (FixedPoints.subalgebra B A H) A H :=
    .of_inertia_eq_bot Subtype.val_injective fun Q hQ g hg ↦ Subtype.ext (hfree Q hQ g hg)
  have := hH.etale
  have := hH.galoisMap_bijective_and_faithfullyFlat.2
  have : Module.Finite B (FixedPoints.subalgebra B A H) :=
    .of_injective (FixedPoints.subalgebra B A H).val.toLinearMap Subtype.val_injective
  have : Algebra.FinitePresentation B (FixedPoints.subalgebra B A H) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact etale_of_etale_of_faithfullyFlat (A := A)

end FreeSubgroup

section GeometricPoints

variable {P Y : Scheme.{u}}

/-- If `π : P ⟶ Y` is open and closed, `Y` is connected and `W ⊆ P` is a nonempty open and
closed subset, then `W` meets every fibre of `π`. -/
lemma exists_mem_fiber_of_isClopen [ConnectedSpace Y] (π : P ⟶ Y) (ho : IsOpenMap π)
    (hc : IsClosedMap π) {W : Set P} (hW : IsClopen W) (hne : W.Nonempty) (y : Y) :
    ∃ w ∈ W, π w = y := by
  have h : IsClopen (π '' W) := ⟨hc _ hW.isClosed, ho _ hW.isOpen⟩
  have := (isClopen_iff.mp h).resolve_left (hne.image _).ne_empty
  obtain ⟨w, hw, rfl⟩ : y ∈ π '' W := this ▸ Set.mem_univ y
  exact ⟨w, hw, rfl⟩

/-- A point `w` of a scheme unramified and locally of finite type (e.g. étale) over `Y`, lying
over the image of a geometric point `y : Spec Ω ⟶ Y` (`Ω` algebraically closed), is the image of
a geometric point of `P` over `y`: the residue extension at `w` is algebraic. -/
lemma exists_geometricPoint_lift (π : P ⟶ Y) [FormallyUnramified π] [LocallyOfFiniteType π]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (w : P)
    (hw : π w = y (IsLocalRing.closedPoint Ω)) :
    ∃ w' : Spec (.of Ω) ⟶ P, w' ≫ π = y ∧ w' (IsLocalRing.closedPoint Ω) = w := by
  let φ := Y.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map φ ≫ Y.fromSpecResidueField _ = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω Y y
  let φ' := (Y.residueFieldCongr hw).hom ≫ φ
  let _ : Algebra (Y.residueField (π w)) (P.residueField w) := (π.residueFieldMap w).hom.toAlgebra
  let _ : Algebra (Y.residueField (π w)) Ω := φ'.hom.toAlgebra
  have : Algebra.IsSeparable (Y.residueField (π w)) (P.residueField w) := inferInstance
  have : Algebra.IsAlgebraic (Y.residueField (π w)) (P.residueField w) := inferInstance
  let l := IsAlgClosed.lift (R := Y.residueField (π w)) (S := P.residueField w) (M := Ω)
  let ψ : P.residueField w ⟶ .of Ω := CommRingCat.ofHom l.toRingHom
  have hψ : π.residueFieldMap w ≫ ψ = φ' := by
    ext a
    exact l.commutes a
  refine ⟨Spec.map ψ ≫ P.fromSpecResidueField w, ?_, Scheme.fromSpecResidueField_apply w _⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, hψ, Spec.map_comp_assoc, Scheme.residueFieldCongr_fromSpecResidueField,
    hy]

end GeometricPoints

section IsIso

variable {Y X X' : Scheme.{u}} [ConnectedSpace Y] (q : X ⟶ Y) (q' : X' ⟶ Y) [IsFinite q] [Etale q]
  [IsFinite q'] [Etale q'] (u : X ⟶ X') (hu : u ≫ q' = q) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

include hu in
/-- V.3.7, injectivity half: a `Y`-morphism of étale coverings of a connected `Y` which is
injective on the geometric points over `y` is a monomorphism. -/
theorem mono_of_injective_on_geometricPoints
    (h : ∀ x₁ x₂ : Spec (.of Ω) ⟶ X, x₁ ≫ q = y → x₂ ≫ q = y → x₁ ≫ u = x₂ ≫ u → x₁ = x₂) :
    Mono u := by
  subst hu
  have : Etale u := Etale.of_comp u q'
  have : IsFinite u := MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) u q'
    inferInstance ‹_›
  rw [← pullback.isIso_diagonal_iff, isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
  by_contra hz
  let Δ := pullback.diagonal u
  let π : pullback u u ⟶ Y := pullback.fst u u ≫ u ≫ q'
  have hW : IsClopen (Set.range Δ)ᶜ :=
    ⟨Δ.isOpenEmbedding.isOpen_range.isClosed_compl,
      (Δ.isClosedEmbedding.isClosed_range).isOpen_compl⟩
  obtain ⟨w, hw, hwy⟩ := exists_mem_fiber_of_isClopen π π.isOpenMap π.isClosedMap hW ⟨z, hz⟩
    (y (IsLocalRing.closedPoint Ω))
  obtain ⟨w', hw'y, rfl⟩ := exists_geometricPoint_lift π y w hwy
  have h₁ : (w' ≫ pullback.fst u u) ≫ u ≫ q' = y := by simpa [π] using hw'y
  have h₂ : (w' ≫ pullback.snd u u) ≫ u ≫ q' = y := by
    rw [Category.assoc, ← pullback.condition_assoc]; simpa [π] using hw'y
  have h₁₂ := h _ _ h₁ h₂ (by rw [Category.assoc, Category.assoc, pullback.condition])
  apply hw
  refine ⟨(w' ≫ pullback.fst u u) (IsLocalRing.closedPoint Ω), ?_⟩
  have : (w' ≫ pullback.fst u u) ≫ Δ = w' := by
    apply pullback.hom_ext
    · simp [Δ]
    · simp [Δ, h₁₂]
  exact congr($this (IsLocalRing.closedPoint Ω))

include hu in
/-- V.3.7, surjectivity half: a `Y`-morphism of étale coverings of a connected `Y` which is
surjective on the geometric points over `y` is surjective. -/
theorem surjective_of_surjective_on_geometricPoints
    (h : ∀ x' : Spec (.of Ω) ⟶ X', x' ≫ q' = y → ∃ x : Spec (.of Ω) ⟶ X, x ≫ u = x') :
    Surjective u := by
  subst hu
  have : Etale u := Etale.of_comp u q'
  have : UniversallyClosed u := UniversallyClosed.of_comp_of_isSeparated u q'
  refine ⟨fun z ↦ ?_⟩
  by_contra hz
  have hW : IsClopen (Set.range u)ᶜ :=
    ⟨u.isOpenMap.isOpen_range.isClosed_compl, u.isClosedMap.isClosed_range.isOpen_compl⟩
  obtain ⟨w, hw, hwy⟩ := exists_mem_fiber_of_isClopen q' q'.isOpenMap q'.isClosedMap hW ⟨z, hz⟩
    (y (IsLocalRing.closedPoint Ω))
  obtain ⟨w', hw'y, rfl⟩ := exists_geometricPoint_lift q' y w hwy
  obtain ⟨x, rfl⟩ := h w' hw'y
  exact hw ⟨x (IsLocalRing.closedPoint Ω), rfl⟩

include hu in
/-- V.3.7: let `Y` be connected, `y : Spec Ω ⟶ Y` a geometric point (`Ω` algebraically closed)
and `u : X ⟶ X'` a `Y`-morphism of étale coverings of `Y` inducing a bijection between the
points of `X` and of `X'` with values in `Ω` over `y`. Then `u` is an isomorphism. SGA assumes `Y`
locally noetherian, which is not needed here. -/
theorem isIso_of_bijective_on_geometricPoints
    (hbij : Function.Bijective (fun x : {x : Spec (.of Ω) ⟶ X // x ≫ q = y} ↦
        (⟨x.1 ≫ u, by rw [Category.assoc, hu, x.2]⟩ : {x' : Spec (.of Ω) ⟶ X' // x' ≫ q' = y}))) :
    IsIso u := by
  have hmono := mono_of_injective_on_geometricPoints q q' u hu y fun x₁ x₂ h₁ h₂ h₁₂ ↦
    congr_arg Subtype.val (hbij.1 (a₁ := ⟨x₁, h₁⟩) (a₂ := ⟨x₂, h₂⟩) (Subtype.ext h₁₂))
  have hsurj := surjective_of_surjective_on_geometricPoints q q' u hu y fun x' hx' ↦ by
    obtain ⟨x, hx⟩ := hbij.2 ⟨x', hx'⟩
    exact ⟨x.1, congr_arg Subtype.val hx⟩
  subst hu
  have : Etale u := Etale.of_comp u q'
  have : IsFinite u := MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) u q'
    inferInstance ‹_›
  exact Flat.isIso_of_surjective_of_mono u

end IsIso

section Statements

/-- V.3.1 and V.3.2: let `Y` be locally noetherian, `f : X ⟶ Y` étale, separated and of finite
type, and `G` a finite group acting on the right on `X` by `Y`-automorphisms. Then `G` acts
admissibly, and for the quotient `p : X ⟶ X/G` both `p` (V.3.2) and `X/G ⟶ Y` (V.3.1) are étale.
Proved as `etaleQuotientStatement` in `QuotientComponents.lean`. -/
def EtaleQuotientStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    [IsLocallyNoetherian Y] (G : Type u) [Group G] [Finite G] (T : G → (X ⟶ X)),
    IsRightAction T → (hf : ∀ g, T g ≫ f = f) →
      IsAdmissible T ∧ ∀ (Z : Scheme.{u}) (p : X ⟶ Z) (hp : IsQuotient T p),
        Etale p ∧ Etale (hp.desc f hf)

/-- V.3.4: if moreover `X` is finite over `Y`, then `X/G` is finite étale over `Y`. Proved as
`finiteEtaleQuotientStatement` in `QuotientEtale.lean` (for any base `Y`). -/
def FiniteEtaleQuotientStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] [Etale f] [IsLocallyNoetherian Y]
    (G : Type u) [Group G] [Finite G] (T : G → (X ⟶ X)),
    IsRightAction T → (hf : ∀ g, T g ≫ f = f) →
      ∀ (Z : Scheme.{u}) (p : X ⟶ Z) (hp : IsQuotient T p),
        IsFinite (hp.desc f hf) ∧ Etale (hp.desc f hf)

/-- V.3.7: let `Y` be connected and locally noetherian, `y : Spec Ω ⟶ Y` a geometric point
(`Ω` algebraically closed), and `u : X ⟶ X'` a `Y`-morphism of étale coverings of `Y` inducing a
bijection `X(Ω) → X'(Ω)` on points over `y`. Then `u` is an isomorphism. Proved in
`isIsoOfBijectiveOnGeometricPointsStatement` (from `isIso_of_bijective_on_geometricPoints`). -/
def IsIsoOfBijectiveOnGeometricPointsStatement : Prop :=
  ∀ (Y X X' : Scheme.{u}) [ConnectedSpace Y] [IsLocallyNoetherian Y] (q : X ⟶ Y) (q' : X' ⟶ Y)
    [IsFinite q] [Etale q] [IsFinite q'] [Etale q'] (u : X ⟶ X') (hu : u ≫ q' = q)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Function.Bijective (fun x : {x : Spec (.of Ω) ⟶ X // x ≫ q = y} ↦
        (⟨x.1 ≫ u, by rw [Category.assoc, hu, x.2]⟩ :
          {x' : Spec (.of Ω) ⟶ X' // x' ≫ q' = y})) →
      IsIso u

/-- V.3.7 holds (the noetherian hypothesis is not used). -/
theorem isIsoOfBijectiveOnGeometricPointsStatement :
    IsIsoOfBijectiveOnGeometricPointsStatement.{u} := by
  intro Y X X' _ _ q q' _ _ _ _ u hu Ω _ _ y hbij
  exact isIso_of_bijective_on_geometricPoints q q' u hu y hbij

end Statements

end SGA.SGA1.ExposeV
