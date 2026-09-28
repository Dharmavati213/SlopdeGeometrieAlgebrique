/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.QuotientEtale
import SGA.SGA1.ExposeI.Fundamental

/-!
# SGA 1, Exposé V, §2–§3: decomposition and inertia groups of points of schemes

For a family of endomorphisms `T g` of a scheme `X` (a right action of `G`), the decomposition
group of `x` is its stabilizer (`decompositionGroup`), and the inertia group
(`inertiaGroup`, `inertiaSubgroup`) is the stabilizer of the point `Spec κ(x) ⟶ X`, i.e. of
`x` together with its residue field: SGA's description as the stabilizer of a geometric point.
In the affine case it is mathlib's `Ideal.inertia` (`fromSpecResidueField_comp_eq_of_mem_inertia`).

V.2.1 for schemes: inertia groups do not change under base change (`inertiaGroup_pullback`).

For `p : X ⟶ Y` as in V.1.3 (no noetherian or finiteness hypothesis):
* V.1.3 (iii), surjectivity of `G_d(x) → Aut(κ(x)/κ(y))`, for non-affine `X`
  (`exists_fromSpecResidueField_comp_eq`; the normality of `κ(x)/κ(y)` is in
  `QuotientResidueField.lean`);
* V.2.3: trivial inertia implies `p` étale (`etale_of_inertiaGroup_eq`);
* V.2.4: for `X` connected and `G` faithful, `p` is étale iff the inertia groups are trivial
  (`etale_iff_inertiaGroup_eq`), and then every `Y`-endomorphism of `X` is some `T g`
  (`exists_eq_of_comp_eq`);
* V.3.2 in the case to which SGA reduces (`X` connected, `G` faithful, `X` unramified and
  separated over the base): `p` is étale (`etale_of_unramified_of_faithful`), by I.5.4.
* V.3.3 in the case used by SGA, for schemes (`etale_desc_of_etale`), and V.3.1 for `X`
  connected and `G` faithful (`etale_and_etale_of_faithful`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Inertia

variable {G : Type*} {X Y : Scheme.{u}} (T : G → (X ⟶ X))

/-- V.2: the decomposition group `G_d(x)` of a point `x`, its stabilizer. -/
def decompositionGroup (x : X) : Set G := {g | T g x = x}

/-- V.2: the inertia group `G_i(x)` of a point `x`: the elements fixing the point
`Spec κ(x) ⟶ X`, i.e. fixing `x` and acting trivially on `κ(x)` (SGA: the stabilizer of a
geometric point located at `x`). -/
def inertiaGroup (x : X) : Set G := {g | X.fromSpecResidueField x ≫ T g = X.fromSpecResidueField x}

lemma inertiaGroup_subset_decompositionGroup (x : X) :
    inertiaGroup T x ⊆ decompositionGroup T x := by
  intro g hg
  obtain ⟨z⟩ : Nonempty (Spec (X.residueField x)) := inferInstance
  have := congr($(hg) z)
  change T g x = x
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this

section Unramified

variable {T}

/-- I.5.4 for the action: if `X` is connected and unramified and separated over `Z`, and `G`
acts by `Z`-automorphisms, an element of an inertia group acts trivially on `X`. -/
theorem eq_id_of_mem_inertiaGroup [PreconnectedSpace X] {Z : Scheme.{u}} (f : X ⟶ Z)
    [IsSeparated f] [FormallyUnramified f] [LocallyOfFiniteType f] (hTf : ∀ g, T g ≫ f = f)
    (x : X) (g : G) (hg : g ∈ inertiaGroup T x) : T g = 𝟙 X :=
  SGA.SGA1.ExposeI.hom_eq_of_fromSpecResidueField_comp_eq f f (hTf g) (Category.id_comp f) x
    (by rw [Category.comp_id]; exact hg)

end Unramified

variable {T} [Group G] (hT : IsRightAction T)

/-- The inertia group, as a subgroup. -/
def inertiaSubgroup (x : X) : Subgroup G where
  carrier := inertiaGroup T x
  mul_mem' {g h} hg hh := by
    change _ ≫ T (g * h) = _
    rw [hT.map_mul, ← Category.assoc, hg, hh]
  one_mem' := by
    change _ ≫ T 1 = _
    rw [hT.map_one, Category.comp_id]
  inv_mem' {g} hg := by
    change _ ≫ T g⁻¹ = _
    conv_lhs => rw [← hg]
    rw [Category.assoc, hT.comp_inv, Category.comp_id]

variable {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

/-- An element of the inertia ideal-theoretic group of a prime of `Γ(W, ⊤)`, `W` affine,
fixes the corresponding point `Spec κ(w) ⟶ W`. -/
lemma fromSpecResidueField_comp_eq_of_mem_inertia {W : Scheme.{u}} [IsAffine W]
    {R : G → (W ⟶ W)} (hR : IsRightAction R) (w : W) (g : G)
    (hg : letI := sectionsAction hR ⊤ fun _ ↦ le_top
      g ∈ (W.isoSpec.hom w).asIdeal.inertia G) :
    W.fromSpecResidueField w ≫ R g = W.fromSpecResidueField w := by
  let _ := sectionsAction hR ⊤ fun _ ↦ le_top
  rw [← cancel_mono W.isoSpec.hom, Category.assoc, isoSpec_hom_comp_specAction hR]
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (W.fromSpecResidueField w ≫ W.isoSpec.hom)
  have hker : RingHom.ker ρ.hom = (W.isoSpec.hom w).asIdeal := by
    obtain ⟨t⟩ : Nonempty (Spec (W.residueField w)) := inferInstance
    have := t.isPrime
    have ht : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have h1 : Spec.map ρ t = W.isoSpec.hom w := by
      rw [hρ]
      exact congr_arg W.isoSpec.hom (Scheme.fromSpecResidueField_apply w t)
    have h2 : (Spec.map ρ t).asIdeal = Ideal.comap ρ.hom t.asIdeal := rfl
    rw [← h1, h2, ht, ← RingHom.ker_eq_comap_bot]
  rw [← Category.assoc, ← hρ, specAction, ← Spec.map_comp]
  congr 1
  ext a
  change ρ.hom (g • a) = ρ.hom a
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker]
  exact hg a

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.2.3: under the conditions of V.1.3, if all inertia groups are trivial then `p : X ⟶ Y`
is étale (SGA assumes moreover `Y` locally noetherian and `X` finite over `Y`). -/
theorem etale_of_inertiaGroup_eq [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    (h : ∀ x g, g ∈ inertiaGroup T x → g = 1) : Etale p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top Y)
    fun V ↦ ?_
  let W := p ⁻¹ᵁ V.1
  have : IsAffine W.toScheme := V.2.preimage p
  have hR := isRightAction_restrictAction hTp hT V.1
  have hq := isQuotient_restrict hTp hT (fun U _ ↦ hsec U) V.1
  let A : CommRingCat.{u} := Γ(W.toScheme, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hR ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := .of (FixedPoints.subring A G)
  have hq' : IsQuotient (restrictAction hTp V.1) (W.toScheme.isoSpec.hom ≫ specMap A B) :=
    (isQuotient_specMap (G := G) (B := B) Subtype.val_injective).iso_comp _
      (isoSpec_hom_comp_specAction hR)
  have hpe : p ∣_ V.1 = (W.toScheme.isoSpec.hom ≫ specMap A B) ≫ (hq.uniqueIso hq').inv := by
    rw [Iso.eq_comp_inv]
    exact hq.comp_uniqueIso_hom hq'
  have hfree : ∀ m : Ideal A, m.IsMaximal → ∀ g ∈ m.inertia G, g = 1 := by
    intro m hm g hg
    let w : W.toScheme := W.toScheme.isoSpec.inv ⟨m, hm.isPrime⟩
    have hw : W.toScheme.isoSpec.hom w = ⟨m, hm.isPrime⟩ := by
      simp [w, ← Scheme.Hom.comp_apply]
    have key := fromSpecResidueField_comp_eq_of_mem_inertia hR w g (by rw [hw]; exact hg)
    apply h (W.ι w) g
    have hι := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField W.ι w
    change X.fromSpecResidueField (W.ι w) ≫ T g = X.fromSpecResidueField (W.ι w)
    rw [← cancel_epi (Spec.map (W.ι.residueFieldMap w)), reassoc_of% hι, hι,
      ← Scheme.Hom.resLE_comp_ι (T g) (preimage_le_preimage_of_comp_eq (hTp g) V.1),
      ← Category.assoc]
    exact congr_arg (· ≫ W.ι) key
  have := (etale_of_inertia_eq_bot (B := B) (A := A) (G := G) Subtype.val_injective hfree).1
  have : Etale (specMap A B) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  rw [hpe]
  infer_instance

include hT in
/-- V.1.3 (iii), second half, for any `p` as in V.1.3: every `κ(y)`-endomorphism `σ` of `κ(x)`
(`y = p x`) is induced by an element `g` of the decomposition group `G_d(x)`, i.e.
`Spec κ(x) ⟶ X` composed with `T g` is `Spec(σ)` composed with `Spec κ(x) ⟶ X`. -/
theorem exists_fromSpecResidueField_comp_eq [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) (x : X)
    (σ : X.residueField x ⟶ X.residueField x) (hσ : p.residueFieldMap x ≫ σ = p.residueFieldMap x) :
    ∃ g ∈ decompositionGroup T x,
      X.fromSpecResidueField x ≫ T g = Spec.map σ ≫ X.fromSpecResidueField x := by
  have h : X.fromSpecResidueField x ≫ p = (Spec.map σ ≫ X.fromSpecResidueField x) ≫ p := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, hσ]
  obtain ⟨g, hg⟩ := exists_comp_eq_of_comp_eq hT hTp hsec (X.fromSpecResidueField x)
    (Spec.map σ ≫ X.fromSpecResidueField x) h
  have hg' : X.fromSpecResidueField x ≫ T g = Spec.map σ ≫ X.fromSpecResidueField x := hg
  refine ⟨g, ?_, hg'⟩
  obtain ⟨z⟩ : Nonempty (Spec (X.residueField x)) := inferInstance
  have := congr($(hg') z)
  change T g x = x
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this

include hT in
/-- V.3.3 in the form used for V.3.1: under the conditions of V.1.3, if `p` is étale and `X` is
étale and locally of finite type over a locally noetherian `Z`, then so is `Y = X/G`. The ring
version is `etale_of_etale_of_faithfullyFlat`. -/
theorem etale_desc_of_etale [IsAffineHom p] [Etale p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    {Z : Scheme.{u}} [IsLocallyNoetherian Z] (q : Y ⟶ Z) [Etale (p ≫ q)] : Etale q := by
  rw [HasRingHomProperty.iff_appLE (P := @Etale)]
  intro U V e
  let W := p ⁻¹ᵁ V.1
  have hW : IsAffineOpen W := V.2.preimage p
  have e' : W ≤ (p ≫ q) ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.comp_preimage]
    exact p.preimage_mono e
  let R := Γ(Z, U.1)
  let B := Γ(Y, V.1)
  let A := Γ(X, W)
  let _ : Algebra R B := (q.appLE U V e).hom.toAlgebra
  let _ : Algebra B A := (p.app V.1).hom.toAlgebra
  let _ : Algebra R A := ((p ≫ q).appLE U W e').hom.toAlgebra
  have hcomp : (p ≫ q).appLE U W e' = q.appLE U V e ≫ p.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have : IsScalarTower R B A := .of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      hcomp]
    rfl)
  have hRA : Algebra.Etale R A := RingHom.etale_algebraMap.mp
    (HasRingHomProperty.appLE @Etale (p ≫ q) ‹_› U ⟨W, hW⟩ e')
  have hBA : Algebra.Etale B A := by
    rw [← RingHom.etale_algebraMap]
    have := HasRingHomProperty.appLE @Etale p ‹_› V ⟨W, hW⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  -- `A` is integral and faithfully flat over `B = A^G`
  let _ : MulSemiringAction G A :=
    sectionsAction hT W fun g ↦ preimage_le_preimage_of_comp_eq (hTp g) V.1
  have : SMulCommClass G B A := ⟨fun g r s ↦ by
    change (T g).appLE _ _ _ (p.app V.1 r * s) = p.app V.1 r * (T g).appLE _ _ _ s
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (hTp g) _ _ _ le_rfl]⟩
  have : Algebra.IsInvariant B A G := ⟨fun s hs ↦ (hsec V.1).2 s hs⟩
  have hint := Algebra.IsInvariant.isIntegral B A G
  have hinj : Function.Injective (algebraMap B A) := (hsec V.1).1
  have : Module.FaithfullyFlat B A :=
    Module.FaithfullyFlat.of_comap_surjective (RingHom.IsIntegral.comap_surjective hint.1 hinj)
  -- `B` is of finite presentation over the noetherian ring `R`
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have : Algebra.FiniteType R A := ((p ≫ q).finiteType_appLE U.2 hW e' :)
  have : Algebra.FiniteType R B := finiteType_of_finiteType_of_isIntegral (R := R) hinj
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale R B := etale_of_etale_of_faithfullyFlat (A := A)
  exact RingHom.etale_algebraMap.mpr this

section Connected

variable [PreconnectedSpace X]

include hT in
/-- V.2.4, first assertion: under the conditions of V.1.3, with `X` connected and `G` acting
faithfully, `p` is étale iff the inertia groups are trivial. -/
theorem etale_iff_inertiaGroup_eq [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) (hfaith : ∀ g, T g = 𝟙 X → g = 1) :
    Etale p ↔ ∀ x g, g ∈ inertiaGroup T x → g = 1 :=
  ⟨fun _ x g hg ↦ hfaith g (eq_id_of_mem_inertiaGroup p hTp x g hg),
    etale_of_inertiaGroup_eq hT hTp hsec⟩

include hT in
/-- V.2.4, second assertion: under the conditions of V.1.3, if `X` is connected and `p` is étale,
every `Y`-automorphism (indeed every `Y`-endomorphism) of `X` is some `T g`. -/
theorem exists_eq_of_comp_eq [IsAffineHom p] [Finite G] [Etale p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) (u : X ⟶ X) (hu : u ≫ p = p) :
    ∃ g, T g = u := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact ⟨1, Scheme.hom_ext_of_forall _ _ fun x ↦ (hX.false x).elim⟩
  obtain ⟨g, hg⟩ := exists_comp_eq_of_comp_eq hT hTp hsec (X.fromSpecResidueField x)
    (X.fromSpecResidueField x ≫ u)
    ((congr_arg (fun m ↦ X.fromSpecResidueField x ≫ m) hu).symm.trans (Category.assoc _ _ _).symm)
  exact ⟨g, SGA.SGA1.ExposeI.hom_eq_of_fromSpecResidueField_comp_eq p p (hTp g) hu x hg⟩

include hT in
/-- V.3.2, for `X` connected and `G` faithful: if `X` is étale (indeed unramified) and separated
over `Z` and `G` acts by `Z`-automorphisms, then the quotient morphism `p : X ⟶ Y` of V.1.3 is
étale (V.2.3). -/
theorem etale_of_unramified_of_faithful [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) {Z : Scheme.{u}} (f : X ⟶ Z) [IsSeparated f]
    [FormallyUnramified f] [LocallyOfFiniteType f] (hTf : ∀ g, T g ≫ f = f)
    (hfaith : ∀ g, T g = 𝟙 X → g = 1) : Etale p :=
  etale_of_inertiaGroup_eq hT hTp hsec fun x g hg ↦
    hfaith g (eq_id_of_mem_inertiaGroup f hTf x g hg)

include hT in
/-- V.3.1 and V.3.2 in the case to which SGA reduces: let `f : X ⟶ Z` be étale and separated
with `Z` locally noetherian, `X` connected, and `G` a finite group acting faithfully by
`Z`-automorphisms, and `p : X ⟶ Y` as in V.1.3 with `q : Y ⟶ Z` and `p ≫ q = f`. Then `p` and
`q` are étale. -/
theorem etale_and_etale_of_faithful [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : X ⟶ Z) [Etale f] [IsSeparated f] (hTf : ∀ g, T g ≫ f = f)
    (hfaith : ∀ g, T g = 𝟙 X → g = 1) (q : Y ⟶ Z) (hq : p ≫ q = f) : Etale p ∧ Etale q := by
  have := etale_of_unramified_of_faithful hT hTp hsec f hTf hfaith
  have : Etale (p ≫ q) := by rw [hq]; infer_instance
  exact ⟨inferInstance, etale_desc_of_etale hT hTp hsec q⟩

end Connected

end Inertia

/-- The morphism `Spec κ(x') ⟶ Spec κ(f x')` induced by a morphism `f` is an epimorphism. -/
lemma epi_specMap_residueFieldMap {X X' : Scheme.{u}} (f : X' ⟶ X) (x' : X') :
    Epi (Spec.map (f.residueFieldMap x')) := by
  have : Flat (Spec.map (f.residueFieldMap x')) := HasRingHomProperty.Spec_iff.mpr (by
    let _ := (f.residueFieldMap x').hom.toAlgebra
    exact (inferInstance : Module.Flat (X.residueField (f x')) (X'.residueField x')))
  have : Surjective (Spec.map (f.residueFieldMap x')) :=
    ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  infer_instance

section BaseChange

variable {G : Type*} {X Z Z' : Scheme.{u}} {T : G → (X ⟶ X)} {q : X ⟶ Z} (hTq : ∀ g, T g ≫ q = q)
  (h : Z' ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- V.2.1: inertia groups do not change under base change: for the action of `G` on
`X' = X ×_Z Z'` through the first factor and a point `x'` of `X'` over `x ∈ X`,
`G_i(x') = G_i(x)`. -/
theorem inertiaGroup_pullback (x' : (pullback q h : Scheme.{u})) :
    inertiaGroup (fun g ↦ pullback.map q h q h (T g) (𝟙 Z') (𝟙 Z)
      (by rw [Category.comp_id, hTq]) (by simp)) x' =
      inertiaGroup T (pullback.fst q h x') := by
  ext g
  have := epi_specMap_residueFieldMap (pullback.fst q h) x'
  have hx := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (pullback.fst q h) x'
  change _ ↔ X.fromSpecResidueField (pullback.fst q h x') ≫ T g =
    X.fromSpecResidueField (pullback.fst q h x')
  rw [← cancel_epi (Spec.map ((pullback.fst q h).residueFieldMap x')), reassoc_of% hx, hx]
  change _ ≫ _ = _ ↔ _
  constructor
  · intro e
    have := congr_arg (· ≫ pullback.fst q h) e
    simpa [pullback.map] using this
  · intro e
    apply pullback.hom_ext
    · simpa [pullback.map] using e
    · simp [pullback.map]

end BaseChange

end SGA.SGA1.ExposeV
