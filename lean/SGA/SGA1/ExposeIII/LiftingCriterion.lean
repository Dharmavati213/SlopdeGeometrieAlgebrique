/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.ArtinianCriterion
import SGA.SGA1.ExposeIII.GlobalExtension
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# SGA 1, Exposé III, 3.1: the infinitesimal lifting criterion for smoothness of schemes

Theorem III.3.1 (`smooth_tfae`): for `f : X → Y` locally of finite type (`Y` locally noetherian,
as everywhere in SGA 1), the following are equivalent: (i) `f` is smooth; (ii) morphisms into `X`
extend locally along closed subschemes with the same underlying space (`LocalExtensionProperty`);
(iii) they extend along `Spec (C ⧸ J) ⊆ Spec C` for `C` local artinian finite over a local ring
`𝒪_{Y,y}` (`LocalArtinianExtensionProperty`). The variants (ii bis), (iii bis) with sections of
`X ×_Y Y'`, which SGA calls trivially equivalent, are not stated separately.

* (i) ⇒ (ii) is `exists_extension_of_smooth` (`Schemes.lean`), (ii) ⇒ (iii) is immediate since
  `Spec C` is a point, and (i) ⇒ (iii) is also a case of III.5.5
  (`exists_extension_SpecMap_quotient`);
* (iii) ⇒ (i) follows SGA: the smooth locus is open, so it suffices that it contains every point
  `x` closed in its fibre (`eq_top_of_forall_isClosed_fiber`, using that the fibres are Jacobson).
  For such `x` the residue extension `κ(x)/κ(y)` is finite
  (`finite_residueFieldMap_of_isClosed_fiber`); (iii) gives the lifting property III.2.1 (iv) for
  `𝒪_{Y,y} → 𝒪_{X,x}` (`LocalArtinianExtensionProperty.localArtinianLiftingProperty`), hence
  formal smoothness for the adic topology (III.2.1, `ArtinianCriterion.lean`) and smoothness at
  `x` (III.1.9, `SmoothLocal.lean`).

Corollary III.3.2 (`etale_tfae`) adds uniqueness: the uniqueness in (iii) kills the derivations of
`𝒪_{X,x}` into `κ(x)` at the points closed in their fibre (with the test ring `κ(x)[ε]`), hence
`Ω_{X/Y}` vanishes there, and everywhere since the unramified locus is open.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace SGA.SGA1.ExposeIII

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- III.3.1 (iii): for every `Y`-scheme `Y' = Spec C`, with `C` a local artinian ring finite over
some `𝒪_{Y,y}` (the structure map being `Spec C → Spec 𝒪_{Y,y} → Y`), every nonempty closed
subscheme `Y'₀ = Spec (C ⧸ J)` of `Y'` and every `Y`-morphism `g₀ : Y'₀ → X`, there is a
`Y`-morphism `g : Y' → X` extending `g₀`. -/
def LocalArtinianExtensionProperty : Prop :=
  ∀ (y : Y) ⦃C : Type u⦄ [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (φ : Y.presheaf.stalk y ⟶ CommRingCat.of C), φ.hom.Finite → ∀ J : Ideal C, J ≠ ⊤ →
    ∀ g₀ : Spec (.of (C ⧸ J)) ⟶ X,
      g₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map φ ≫
        Y.fromSpecStalk y →
      ∃ g : Spec (.of C) ⟶ X, g ≫ f = Spec.map φ ≫ Y.fromSpecStalk y ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g = g₀

/-- Two local homomorphisms `𝒪_{X,x} → R` into a local ring are equal if the induced morphisms
`Spec R → X` are. -/
lemma SpecMap_fromSpecStalk_injective {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    {x : X} {φ ψ : X.presheaf.stalk x ⟶ R} [IsLocalHom φ.hom] [IsLocalHom ψ.hom]
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ := by
  have := (SpecToEquivOfLocalRing X R).symm.injective (a₁ := ⟨x, φ, ‹_›⟩) (a₂ := ⟨x, ψ, ‹_›⟩) h
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)

set_option backward.isDefEq.respectTransparency false in
/-- III.3.1, (iii) ⇒ (iii) of III.2.1 at the local rings: "a morphism from `Spec B`, with `B`
local, into `X` is determined bijectively by a local homomorphism from an `𝒪_x` into `B`", so
the property (iii) gives the lifting property III.2.1 (iv) for `𝒪_{Y,f x} → 𝒪_{X,x}`. -/
theorem LocalArtinianExtensionProperty.localArtinianLiftingProperty
    (hf : LocalArtinianExtensionProperty f) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    LocalArtinianLiftingProperty (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  intro C _ _ _ _ _ J hJ u hu
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (C ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot C
  have hJnil : IsNilpotent J := ⟨N, by
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hN]; exact Ideal.pow_right_mono (le_maximalIdeal hJ) N⟩
  let φ : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C :=
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) C)
  let u' : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom u.toRingHom
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom :=
    ⟨fun c hc ↦ AdicFormallySmooth.isUnit_of_isUnit_mk hJnil hc⟩
  have : IsLocalHom u'.hom := ⟨fun a ha ↦ isUnit_of_map_unit u a ha⟩
  have hcomm : f.stalkMap x ≫ u' = φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    ext a
    change u (algebraMap _ _ a) = Ideal.Quotient.mk J (algebraMap _ C a)
    rw [u.commutes]
    rfl
  have : IsLocalHom φ.hom := ⟨fun a ha ↦ by
    have h1 : IsUnit ((φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)).hom a) :=
      ha.map (Ideal.Quotient.mk J)
    rw [← hcomm] at h1
    exact isUnit_of_map_unit (f.stalkMap x).hom a (isUnit_of_map_unit u'.hom _ h1)⟩
  have hφ : φ.hom.Finite :=
    show (algebraMap (Y.presheaf.stalk (f x)) C).Finite from RingHom.finite_algebraMap.mpr ‹_›
  obtain ⟨g, hgf, hgg₀⟩ := hf (f x) φ hφ J hJ (Spec.map u' ≫ X.fromSpecStalk x) (by
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
      hcomm, Spec.map_comp_assoc])
  obtain ⟨⟨x', v, hv⟩, rfl⟩ := (SpecToEquivOfLocalRing X (.of C)).symm.surjective g
  simp only [SpecToEquivOfLocalRing_symm_apply] at hgf hgg₀
  have hx' : x = x' := by
    have := congrArg (fun g ↦ g (closedPoint (C ⧸ J))) hgg₀
    have e₁ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) (closedPoint (C ⧸ J)) =
        closedPoint C := Spec_closedPoint
    have e₂ : (Spec.map v) (closedPoint C) = closedPoint (X.presheaf.stalk x') := Spec_closedPoint
    have e₃ : (Spec.map u') (closedPoint (C ⧸ J)) = closedPoint (X.presheaf.stalk x) :=
      Spec_closedPoint
    simp only [Scheme.Hom.comp_apply] at this
    rw [e₁, e₂, e₃, Scheme.fromSpecStalk_closedPoint, Scheme.fromSpecStalk_closedPoint] at this
    exact this.symm
  subst hx'
  have hv₁ : f.stalkMap x ≫ v = φ := by
    have : IsLocalHom (f.stalkMap x ≫ v).hom :=
      inferInstanceAs (IsLocalHom (v.hom.comp (f.stalkMap x).hom))
    refine SpecMap_fromSpecStalk_injective ?_
    rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← hgf, Category.assoc]
  have hv₂ : v ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = u' := by
    have : IsLocalHom (v ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)).hom :=
      inferInstanceAs (IsLocalHom ((Ideal.Quotient.mk J).comp v.hom))
    refine SpecMap_fromSpecStalk_injective ?_
    rw [Spec.map_comp_assoc, hgg₀]
  exact ⟨{ v.hom with commutes' := fun a ↦ congrArg (fun h ↦ CommRingCat.Hom.hom h a) hv₁ },
    AlgHom.ext fun b ↦ congrArg (fun h ↦ CommRingCat.Hom.hom h b) hv₂⟩

/-- If `κ(x)` is finite over `κ(f x)`, then it is finite over `𝒪_{Y,f x}`. -/
lemma finite_residueField_stalk (x : X) (hfin : (f.residueFieldMap x).hom.Finite) :
    letI := (f.stalkMap x).hom.toAlgebra
    Module.Finite (Y.presheaf.stalk (f x)) (ResidueField (X.presheaf.stalk x)) := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [← RingHom.finite_algebraMap]
  have e : algebraMap (Y.presheaf.stalk (f x)) (ResidueField (X.presheaf.stalk x)) =
      (f.residueFieldMap x).hom.comp (residue _) := by
    ext a
    exact (congrArg (fun h ↦ CommRingCat.Hom.hom h a) (Scheme.residue_residueFieldMap f x)).symm
  rw [e]
  exact hfin.comp (RingHom.Finite.of_surjective _ residue_surjective)

set_option backward.isDefEq.respectTransparency false in
/-- The end of the proof of III.3.1, (iii) ⇒ (i): if `κ(x)` is finite over `κ(f x)` and
`𝒪_{Y,f x} → 𝒪_{X,x}` has the lifting property III.2.1 (iv), then `f` is smooth at `x`. By III.2.1
the local ring `𝒪_x` is formally smooth over `𝒪_y` for its adic topology, and III.1.9 applies
since `𝒪_x` is a localization of an algebra of finite type over `Γ(Y, U)`. -/
theorem formallySmooth_stalkMap_of_localArtinianLiftingProperty [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (x : X) (hfin : (f.residueFieldMap x).hom.Finite)
    (h : letI := (f.stalkMap x).hom.toAlgebra
      LocalArtinianLiftingProperty (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :
    (f.stalkMap x).hom.FormallySmooth := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := finite_residueField_stalk f x hfin
  have hA := adicFormallySmooth_of_localArtinianLiftingProperty h
  -- affine charts around `x` and `f x`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  let := Y.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hU.isLocalization_stalk ⟨f x, hxU⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((algebraMap Γ(X, V) _).comp (algebraMap Γ(Y, U) Γ(X, V))).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, V) (X.presheaf.stalk x) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_algebraMap_eq fun r ↦ by
      change X.presheaf.germ V x hxV (f.appLE U V hVU r) =
        f.stalkMap x (Y.presheaf.germ U (f x) hxU r)
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
  have hR : AdicFormallySmooth Γ(Y, U) (maximalIdeal (X.presheaf.stalk x)) :=
    AdicFormallySmooth.of_isLocalization (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal.primeCompl hA
  have hsm : Algebra.FormallySmooth Γ(Y, U) (X.presheaf.stalk x) :=
    (formallySmooth_iff_adicFormallySmooth (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).mpr hR
  have : Algebra.FormallyEtale Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    .of_isLocalization (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal.primeCompl
  exact (Algebra.FormallySmooth.iff_restrictScalars (R := Γ(Y, U))).mp hsm

set_option backward.isDefEq.respectTransparency.types false in
/-- A point `x` closed in its fibre `f⁻¹(f x)` (no proper specialization of `x` in the fibre)
has a residue field finite over that of `f x`, for `f` locally of finite type: `Spec κ(x)` is then
a closed subscheme of the fibre, which is of finite type over `κ(f x)`, and one concludes with
Zariski's lemma. -/
lemma finite_residueFieldMap_of_isClosed_fiber [LocallyOfFiniteType f] (x : X)
    (hx : ∀ x', x ⤳ x' → f x' = f x → x' = x) : (f.residueFieldMap x).hom.Finite := by
  have hcl : IsClosed {f.asFiber x} := by
    rw [← closure_subset_iff_isClosed]
    intro w hw
    rw [← specializes_iff_mem_closure] at hw
    have h₁ := hw.map (f.fiberι (f x)).continuous
    rw [Scheme.Hom.fiberι_asFiber] at h₁
    have h₂ : f (f.fiberι (f x) w) = f x := by
      have : f.fiberι (f x) w ∈ f ⁻¹' {f x} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self w
      exact this
    exact (f.fiberι (f x)).isEmbedding.injective
      ((hx _ h₁ h₂).trans (f.fiberι_asFiber x).symm)
  have : IsClosedImmersion (f.asFiberHom x) :=
    .of_isPreimmersion _ (by rw [Scheme.Hom.range_asFiberHom]; exact hcl)
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) := by
    rw [← f.asFiberHom_fiberToSpecResidueField]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
  exact RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr this

/-- An open subset of `X` containing every point which is closed in its fibre is all of `X`,
for `f` locally of finite type: a nonempty closed subset of a fibre contains a closed point of
the fibre, since the fibres are Jacobson. -/
lemma eq_top_of_forall_isClosed_fiber [LocallyOfFiniteType f] (W : X.Opens)
    (hW : ∀ x : X, (∀ x', x ⤳ x' → f x' = f x → x' = x) → x ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  by_contra hx
  let T : Set (f.fiber (f x)) := f.fiberι (f x) ⁻¹' (W : Set X)ᶜ
  have hT : IsClosed T := W.2.isClosed_compl.preimage (f.fiberι _).continuous
  obtain ⟨z, hzT, hzc⟩ := nonempty_inter_closedPoints
    ⟨f.asFiber x, show f.fiberι _ (f.asFiber x) ∉ W by rwa [Scheme.Hom.fiberι_asFiber]⟩
    hT.isLocallyClosed
  refine hzT (hW _ fun x' hx' hfx' ↦ ?_)
  have hfz : f (f.fiberι (f x) z) = f x := by
    have : f.fiberι (f x) z ∈ f ⁻¹' {f x} := by
      rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self z
    exact this
  obtain ⟨w, rfl⟩ : x' ∈ Set.range (f.fiberι (f x)) := by
    rw [Scheme.Hom.range_fiberι]; exact hfx'.trans hfz
  have hzw : z ⤳ w := (f.fiberι (f x)).isEmbedding.isInducing.specializes_iff.mp hx'
  have : w ∈ ({z} : Set _) := by
    rw [← (show IsClosed {z} from hzc).closure_eq]; exact specializes_iff_mem_closure.mp hzw
  rw [Set.mem_singleton_iff.mp this]

/-- III.3.1, (i) ⇒ (iii): a smooth morphism has the lifting property (iii); this is the case
`Y' = Spec C` of III.5.5, `C` local artinian and `J` nilpotent. -/
theorem LocalArtinianExtensionProperty.of_smooth [Smooth f] : LocalArtinianExtensionProperty f := by
  intro y C _ _ _ φ _ J hJ g₀ hg₀
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot C
  have hJN : J ^ (N + 1) = ⊥ := eq_bot_iff.mpr ((Ideal.pow_le_pow_right N.le_succ).trans
    ((Ideal.pow_right_mono (le_maximalIdeal hJ) N).trans hN.le))
  exact exists_extension_SpecMap_quotient N (R := .of C) J hJN f _ g₀ hg₀

/-- III.3.1, (iii) ⇒ (i). -/
theorem smooth_of_localArtinianExtensionProperty [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (hf : LocalArtinianExtensionProperty f) : Smooth f := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact eq_top_of_forall_isClosed_fiber f _ fun x hx ↦
    formallySmooth_stalkMap_of_localArtinianLiftingProperty f x
      (finite_residueFieldMap_of_isClosed_fiber f x hx) (hf.localArtinianLiftingProperty f x)

/-- Theorem III.3.1, (i) ⇔ (iii): a morphism `f : X → Y` locally of finite type, with `Y` locally
noetherian, is smooth if and only if every `Y`-morphism `Spec (C ⧸ J) → X`, for `C` local artinian
finite over a local ring of `Y` and `J ≠ C`, extends to `Spec C`. The conditions (ii) and (ii bis)
are `exists_extension_of_smooth` (`Schemes.lean`) and III.5.5 (`globalExtensionStatement`). -/
theorem smooth_iff_localArtinianExtensionProperty [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] : Smooth f ↔ LocalArtinianExtensionProperty f :=
  ⟨fun _ ↦ .of_smooth f, smooth_of_localArtinianExtensionProperty f⟩

/-- III.3.1 (ii): for every `Y`-scheme `Y'`, every closed subscheme `Y'₀` of `Y'` with the same
underlying space, every `Y`-morphism `g₀ : Y'₀ → X` and every point `z` of `Y'₀`, the restriction
of `g₀` to a neighbourhood `U` of `z` in `Y'` extends to a `Y`-morphism `U → X`. -/
def LocalExtensionProperty : Prop :=
  ∀ ⦃Y' Y'₀ : Scheme.{u}⦄ (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i],
    Function.Surjective i → ∀ g₀ : Y'₀ ⟶ X, g₀ ≫ f = i ≫ p → ∀ z : Y'₀,
      ∃ (U : Y'.Opens) (_ : i z ∈ U) (g : U.toScheme ⟶ X),
        g ≫ f = U.ι ≫ p ∧ (i ∣_ U) ≫ g = (i ⁻¹ᵁ U).ι ≫ g₀

/-- III.3.1, (i) ⇒ (ii) (`exists_extension_of_smooth`). -/
theorem LocalExtensionProperty.of_smooth [Smooth f] : LocalExtensionProperty f :=
  fun _ _ p i _ hi g₀ hg₀ z ↦ exists_extension_of_smooth f p i hi g₀ hg₀ z

/-- The closed immersion `Spec (C ⧸ J) → Spec C`, for `C` local artinian and `J ≠ C`, is
surjective (`Spec C` is a point). -/
lemma surjective_SpecMap_quotient_of_isArtinianRing {C : Type u} [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] {J : Ideal C} (hJ : J ≠ ⊤) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (C ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : Subsingleton (PrimeSpectrum C) := inferInstance
  exact fun _ ↦ ⟨closedPoint (C ⧸ J), Subsingleton.elim (α := PrimeSpectrum C) _ _⟩

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-- III.3.1, (ii) ⇒ (iii): `Spec C` has only one point, so the neighbourhood in (ii) is all of
`Spec C`. -/
theorem LocalExtensionProperty.localArtinianExtensionProperty (hf : LocalExtensionProperty f) :
    LocalArtinianExtensionProperty f := by
  intro y C _ _ _ φ _ J hJ g₀ hg₀
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of C) J
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (C ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : Subsingleton (PrimeSpectrum C) := inferInstance
  obtain ⟨U, hzU, g, hg₁, hg₂⟩ := hf (Spec.map φ ≫ Y.fromSpecStalk y) _
    (surjective_SpecMap_quotient_of_isArtinianRing hJ) g₀ hg₀ (closedPoint (C ⧸ J))
  have hU : U = ⊤ := eq_top_iff.mpr fun x _ ↦ by
    rwa [Subsingleton.elim (α := PrimeSpectrum C) x
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) (closedPoint (C ⧸ J)))]
  subst hU
  refine ⟨(Spec (.of C)).topIso.inv ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg₁, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · have : IsIso ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ ⊤).ι :=
      inferInstanceAs (IsIso (Spec (.of (C ⧸ J))).topIso.hom)
    rw [← cancel_epi ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ ⊤).ι, ← hg₂,
      ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    congr 1
    rw [← Category.assoc, Scheme.ι_toIso_inv, Category.id_comp]

/-- Theorem III.3.1, (i) ⇔ (ii) ⇔ (iii), for `f` locally of finite type and `Y` locally
noetherian. -/
theorem smooth_tfae [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    List.TFAE [Smooth f, LocalExtensionProperty f, LocalArtinianExtensionProperty f] := by
  tfae_have 1 → 2 := fun _ ↦ .of_smooth f
  tfae_have 2 → 3 := LocalExtensionProperty.localArtinianExtensionProperty
  tfae_have 3 → 1 := smooth_of_localArtinianExtensionProperty f
  tfae_finish

section Etale

/-- III.3.2 (iii): the lifting property III.3.1 (iii) with uniqueness of the extension `g`. -/
def LocalArtinianUniqueExtensionProperty : Prop :=
  ∀ (y : Y) ⦃C : Type u⦄ [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (φ : Y.presheaf.stalk y ⟶ CommRingCat.of C), φ.hom.Finite → ∀ J : Ideal C, J ≠ ⊤ →
    ∀ g₀ : Spec (.of (C ⧸ J)) ⟶ X,
      g₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map φ ≫
        Y.fromSpecStalk y →
      ∃! g : Spec (.of C) ⟶ X, g ≫ f = Spec.map φ ≫ Y.fromSpecStalk y ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g = g₀

variable {f} in
lemma LocalArtinianUniqueExtensionProperty.localArtinianExtensionProperty
    (hf : LocalArtinianUniqueExtensionProperty f) : LocalArtinianExtensionProperty f :=
  fun y _ _ _ _ φ hφ J hJ g₀ hg₀ ↦ (hf y φ hφ J hJ g₀ hg₀).exists

/-- The uniqueness in III.3.2 (iii) for a homomorphism of local rings `A → B`: two local
`A`-homomorphisms `B → C`, with `C` local artinian finite over `A`, which agree modulo a proper
ideal `J` of `C` are equal. -/
def LocalArtinianUniqueLiftingProperty (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Prop :=
  ∀ ⦃C : Type u⦄ [CommRing C] [Algebra A C] [IsLocalRing C] [IsArtinianRing C]
    [Module.Finite A C] (J : Ideal C), J ≠ ⊤ → ∀ g₁ g₂ : B →ₐ[A] C, IsLocalHom g₁ →
      IsLocalHom g₂ → (Ideal.Quotient.mkₐ A J).comp g₁ = (Ideal.Quotient.mkₐ A J).comp g₂ →
        g₁ = g₂

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-- III.3.2, (iii) at the local rings: uniqueness in (iii) gives uniqueness of liftings of local
homomorphisms `𝒪_{X,x} → C ⧸ J`. -/
theorem LocalArtinianUniqueExtensionProperty.localArtinianUniqueLiftingProperty
    (hf : LocalArtinianUniqueExtensionProperty f) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    LocalArtinianUniqueLiftingProperty (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  intro C _ _ _ _ _ J hJ g₁ g₂ hg₁ hg₂ h
  let φ : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C :=
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) C)
  have hφ : φ.hom.Finite :=
    show (algebraMap (Y.presheaf.stalk (f x)) C).Finite from RingHom.finite_algebraMap.mpr ‹_›
  have key (g : X.presheaf.stalk x →ₐ[Y.presheaf.stalk (f x)] C) :
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ X.fromSpecStalk x) ≫ f =
        Spec.map φ ≫ Y.fromSpecStalk (f x) := by
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact g.commutes a
  have hG (g : X.presheaf.stalk x →ₐ[Y.presheaf.stalk (f x)] C) :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ _ J).comp g).toRingHom) ≫
        X.fromSpecStalk x := by
    rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨g, -, hu⟩ := hf (f x) φ hφ J hJ
    (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ _ J).comp g₁).toRingHom) ≫
      X.fromSpecStalk x) (by rw [← hG g₁, Category.assoc, key])
  have e₁ := hu _ ⟨key g₁, hG g₁⟩
  have e₂ := hu _ ⟨key g₂, (hG g₂).trans (by rw [h])⟩
  have : IsLocalHom (CommRingCat.ofHom g₁.toRingHom).hom := ⟨fun a ha ↦ isUnit_of_map_unit g₁ a ha⟩
  have : IsLocalHom (CommRingCat.ofHom g₂.toRingHom).hom := ⟨fun a ha ↦ isUnit_of_map_unit g₂ a ha⟩
  have := SpecMap_fromSpecStalk_injective (e₁.trans e₂.symm)
  exact AlgHom.ext fun b ↦ congrArg (fun h ↦ CommRingCat.Hom.hom h b) this

/-- The homomorphism `b ↦ b̄ + D(b) ε` from `B` to the dual numbers `κ[ε]` over its residue
field, for a derivation `D : B → κ`. -/
noncomputable def dualNumberLift {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] (d : Derivation A B (ResidueField B)) :
    B →ₐ[A] TrivSqZeroExt (ResidueField B) (ResidueField B) where
  toFun b := TrivSqZeroExt.inl (residue B b) + TrivSqZeroExt.inr (d b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, add_zero, zero_add, Derivation.leibniz, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Algebra.smul_def,
        ResidueField.algebraMap_eq]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_add_add_comm]
  commutes' a := by
    rw [TrivSqZeroExt.algebraMap_eq_inl', Derivation.map_algebraMap, TrivSqZeroExt.inr_zero,
      add_zero, IsScalarTower.algebraMap_apply A B (ResidueField B), ResidueField.algebraMap_eq]

lemma dualNumberLift_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing B] (d : Derivation A B (ResidueField B)) (b : B) :
    dualNumberLift d b = TrivSqZeroExt.inl (residue B b) + TrivSqZeroExt.inr (d b) := rfl

/-- The uniqueness of liftings kills the derivations into the residue field, when the residue
extension is finite: a derivation `D : B → κ` gives the lifting `b ↦ b̄ + D(b) ε` of the residue
map to the dual numbers `κ[ε]`, which are local artinian and finite over `A`. -/
theorem LocalArtinianUniqueLiftingProperty.derivation_eq_zero {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B] [Module.Finite A (ResidueField B)]
    (h : LocalArtinianUniqueLiftingProperty A B) (D : Derivation A B (ResidueField B)) :
    D = 0 := by
  have : Module.Finite (ResidueField B) (TrivSqZeroExt (ResidueField B) (ResidueField B)) :=
    inferInstanceAs (Module.Finite (ResidueField B) (ResidueField B × ResidueField B))
  have : IsArtinianRing (TrivSqZeroExt (ResidueField B) (ResidueField B)) :=
    IsArtinianRing.of_finite (ResidueField B) _
  have : Module.Finite A (TrivSqZeroExt (ResidueField B) (ResidueField B)) :=
    .trans (ResidueField B) _
  have : IsLocalRing (TrivSqZeroExt (ResidueField B) (ResidueField B)) :=
    .of_isUnit_or_isUnit_one_sub_self fun x ↦ by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_one]
      exact isUnit_or_isUnit_one_sub_self x.fst
  let J := RingHom.ker (TrivSqZeroExt.fstHom (ResidueField B) (ResidueField B) (ResidueField B))
  have hloc (d : Derivation A B (ResidueField B)) : IsLocalHom (dualNumberLift d) :=
    ⟨fun b hb ↦ by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualNumberLift_apply] at hb
      exact isUnit_of_map_unit (residue B) b (by simpa using hb)⟩
  have hmk : (Ideal.Quotient.mkₐ A J).comp (dualNumberLift 0) =
      (Ideal.Quotient.mkₐ A J).comp (dualNumberLift D) :=
    AlgHom.ext fun b ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      simp [J, dualNumberLift_apply, RingHom.mem_ker]
  have := h J (RingHom.ker_ne_top _) _ _ (hloc 0) (hloc D) hmk
  ext b
  have := congrArg (fun g ↦ (g b).snd) this
  simpa [dualNumberLift_apply] using this.symm

/-- A local essentially finite type algebra `B` over `A` with no nonzero derivation into its
residue field is formally unramified (by Nakayama, `Ω_{B/A} = 0` as soon as `κ ⊗ Ω_{B/A} = 0`). -/
theorem formallyUnramified_of_derivation_eq_zero {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [Algebra.EssFiniteType A B]
    (h : ∀ D : Derivation A B (ResidueField B), D = 0) : Algebra.FormallyUnramified A B := by
  rw [Algebra.formallyUnramified_iff, ← IsLocalRing.subsingleton_tensorProduct (R := B)]
  refine subsingleton_of_forall_eq 0 fun v ↦ ?_
  refine (Module.forall_dual_apply_eq_zero_iff (ResidueField B) v).mp fun φ ↦ ?_
  let ψ : Ω[B⁄A] →ₗ[B] ResidueField B :=
    (φ.restrictScalars B).comp (TensorProduct.mk B (ResidueField B) Ω[B⁄A] 1)
  have hψ : ψ = 0 := (KaehlerDifferential.linearMapEquivDerivation A B).injective
    (by rw [map_zero]; exact h _)
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul k ω =>
    have h₁ : (k ⊗ₜ[B] ω : TensorProduct B (ResidueField B) Ω[B⁄A]) =
        k • ((1 : ResidueField B) ⊗ₜ[B] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h₂ : φ ((1 : ResidueField B) ⊗ₜ[B] ω) = 0 := LinearMap.congr_fun hψ ω
    rw [h₁, φ.map_smul, h₂, smul_zero]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

/-- III.3.2, (iii) ⇒ (i) at a point `x` with `κ(x)` finite over `κ(f x)`: the stalk map is
formally unramified. -/
theorem formallyUnramified_stalkMap_of_localArtinianUniqueLiftingProperty
    [LocallyOfFiniteType f] (x : X) (hfin : (f.residueFieldMap x).hom.Finite)
    (h : letI := (f.stalkMap x).hom.toAlgebra
      LocalArtinianUniqueLiftingProperty (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :
    (f.stalkMap x).hom.FormallyUnramified := by
  let := (f.stalkMap x).hom.toAlgebra
  have := finite_residueField_stalk f x hfin
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  exact formallyUnramified_of_derivation_eq_zero h.derivation_eq_zero

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `f` at `x ∈ V ⊆ f⁻¹ U` (affine opens) is formally unramified if and only if
`Γ(X, V)` is unramified over `Γ(Y, U)` at the prime of `x`. -/
lemma formallyUnramified_stalkMap_iff {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
      .of_isLocalization p.primeCompl
    refine ⟨fun _ ↦ Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) _, fun h ↦ ?_⟩
    have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime q) := h
    exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U) _ _

/-- The set of points at which `f` is (formally) unramified is open, for `f` locally of finite
type. -/
lemma isOpen_formallyUnramified_stalkMap [LocallyOfFiniteType f] :
    IsOpen {x | (f.stalkMap x).hom.FormallyUnramified} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  let := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
  refine ⟨Scheme.Opens.ι V '' (hV.isoSpec.hom ⁻¹' Algebra.unramifiedLocus Γ(Y, U) Γ(X, V)),
    ?_, ?_, ?_⟩
  · rintro _ ⟨⟨x', hx'⟩, hmem, rfl⟩
    exact (formallyUnramified_stalkMap_iff f U hU V hV hVU hx').mpr hmem
  · exact (Scheme.Opens.ι V).isOpenEmbedding.isOpenMap _
      (Algebra.isOpen_unramifiedLocus.preimage hV.isoSpec.hom.continuous)
  · exact ⟨⟨x, hxV⟩, (formallyUnramified_stalkMap_iff f U hU V hV hVU hxV).mp hx, rfl⟩

/-- III.3.2, (i) ⇒ (iii): an étale morphism has the lifting property (iii) with uniqueness. -/
theorem LocalArtinianUniqueExtensionProperty.of_etale [Etale f] :
    LocalArtinianUniqueExtensionProperty f := by
  intro y C _ _ _ φ hφ J hJ g₀ hg₀
  obtain ⟨g, hg⟩ := LocalArtinianExtensionProperty.of_smooth f y φ hφ J hJ g₀ hg₀
  refine ⟨g, hg, fun g' hg' ↦ ?_⟩
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of C) J
  exact ext_of_formallyUnramified f _ _ (surjective_SpecMap_quotient_of_isArtinianRing hJ) hg'.1
    hg.1 (hg'.2.trans hg.2.symm)

/-- III.3.2, (iii) ⇒ (i). As in SGA, (iii) gives smoothness (III.3.1); the uniqueness gives
`Ω_{X/Y} ⊗ κ(x) = 0` at the points closed in their fibre, hence everywhere since the unramified
locus is open. -/
theorem etale_of_localArtinianUniqueExtensionProperty [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (hf : LocalArtinianUniqueExtensionProperty f) : Etale f := by
  have : Smooth f := smooth_of_localArtinianExtensionProperty f hf.localArtinianExtensionProperty
  have hW := eq_top_of_forall_isClosed_fiber f ⟨_, isOpen_formallyUnramified_stalkMap f⟩
    fun x hx ↦ formallyUnramified_stalkMap_of_localArtinianUniqueLiftingProperty f x
      (finite_residueFieldMap_of_isClosed_fiber f x hx) (hf.localArtinianUniqueLiftingProperty x)
  have : FormallyUnramified f :=
    HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x ↦ by
      have : x ∈ (⊤ : X.Opens) := trivial
      rw [← hW] at this
      exact this
  exact Etale.of_formallyUnramified_of_flat f

/-- Corollary III.3.2, (i) ⇔ (iii): a morphism locally of finite type into a locally noetherian
scheme is étale if and only if it has the lifting property III.3.1 (iii) with uniqueness. (For
(ii), see `existsUnique_extension_of_etale` in `Schemes.lean`.) -/
theorem etale_iff_localArtinianUniqueExtensionProperty [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] : Etale f ↔ LocalArtinianUniqueExtensionProperty f :=
  ⟨fun _ ↦ .of_etale f, etale_of_localArtinianUniqueExtensionProperty f⟩

/-- III.3.2 (ii): condition III.3.1 (ii) with uniqueness of the extension on the neighbourhood. -/
def LocalUniqueExtensionProperty : Prop :=
  ∀ ⦃Y' Y'₀ : Scheme.{u}⦄ (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i],
    Function.Surjective i → ∀ g₀ : Y'₀ ⟶ X, g₀ ≫ f = i ≫ p → ∀ z : Y'₀,
      ∃ (U : Y'.Opens) (_ : i z ∈ U), ∃! g : U.toScheme ⟶ X,
        g ≫ f = U.ι ≫ p ∧ (i ∣_ U) ≫ g = (i ⁻¹ᵁ U).ι ≫ g₀

/-- III.3.2, (i) ⇒ (ii) (`existsUnique_extension_of_etale`). -/
theorem LocalUniqueExtensionProperty.of_etale [Etale f] : LocalUniqueExtensionProperty f :=
  fun _ _ p i _ hi g₀ hg₀ z ↦ existsUnique_extension_of_etale f p i hi g₀ hg₀ z

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-- III.3.2, (ii) ⇒ (iii). -/
theorem LocalUniqueExtensionProperty.localArtinianUniqueExtensionProperty
    (hf : LocalUniqueExtensionProperty f) : LocalArtinianUniqueExtensionProperty f := by
  intro y C _ _ _ φ _ J hJ g₀ hg₀
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of C) J
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (C ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : Subsingleton (PrimeSpectrum C) := inferInstance
  obtain ⟨U, hzU, g, ⟨hg₁, hg₂⟩, hu⟩ := hf (Spec.map φ ≫ Y.fromSpecStalk y) _
    (surjective_SpecMap_quotient_of_isArtinianRing hJ) g₀ hg₀ (closedPoint (C ⧸ J))
  have hU : U = ⊤ := eq_top_iff.mpr fun x _ ↦ by
    rwa [Subsingleton.elim (α := PrimeSpectrum C) x
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) (closedPoint (C ⧸ J)))]
  subst hU
  have : IsIso ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ ⊤).ι :=
    inferInstanceAs (IsIso (Spec (.of (C ⧸ J))).topIso.hom)
  -- global extensions are the extensions on `⊤`
  have key (g' : Spec (.of C) ⟶ X) (hg' : g' ≫ f = Spec.map φ ≫ Y.fromSpecStalk y ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g' = g₀) :
      (⊤ : (Spec (.of C)).Opens).ι ≫ g' = g := by
    refine hu _ ⟨by rw [Category.assoc, hg'.1], ?_⟩
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg'.2]
  refine ⟨(Spec (.of C)).topIso.inv ≫ g, ⟨?_, ?_⟩, fun g' hg' ↦ ?_⟩
  · rw [Category.assoc, hg₁, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · rw [← cancel_epi ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ ⊤).ι, ← hg₂,
      ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    congr 1
    rw [← Category.assoc, Scheme.ι_toIso_inv, Category.id_comp]
  · rw [← key g' hg', ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

/-- Corollary III.3.2, (i) ⇔ (ii) ⇔ (iii), for `f` locally of finite type and `Y` locally
noetherian. -/
theorem etale_tfae [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    List.TFAE [Etale f, LocalUniqueExtensionProperty f,
      LocalArtinianUniqueExtensionProperty f] := by
  tfae_have 1 → 2 := fun _ ↦ .of_etale f
  tfae_have 2 → 3 := LocalUniqueExtensionProperty.localArtinianUniqueExtensionProperty
  tfae_have 3 → 1 := etale_of_localArtinianUniqueExtensionProperty f
  tfae_finish

end Etale

end SGA.SGA1.ExposeIII
