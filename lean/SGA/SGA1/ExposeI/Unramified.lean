/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Locus

/-!
# SGA 1, Exposé I, §3: unramified (net) morphisms

SGA says a finite-type morphism is *net* / *unramified* at `x` when the
residue extension is finite separable, equivalently when `Ω¹` vanishes at `x`,
equivalently when the diagonal is an open immersion near `x`. Mathlib splits
this into `FormallyUnramified` (`Ω¹ = 0`) and a finiteness hypothesis
(`FiniteType` / `LocallyOfFiniteType`); together they are SGA's net morphisms.
The historical synonym *net* is not used as a Lean name.

For a morphism of schemes, "unramified at `x`" is taken to mean that the stalk map
`𝒪_{f(x)} → 𝒪_x` is formally unramified; the set of such points is open (I.3.3,
`Scheme.Hom.unramifiedLocus`). SGA states I.3.7 with completions; we prove the
equivalent statement with the truncations `A/𝔪ⁿ → B/𝔪_Bⁿ`, which avoids completions
(`Â → B̂` is surjective iff all these maps are).
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry Algebra CategoryTheory CategoryTheory.Limits IsLocalRing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.3.1(i)↔formally unramified, for a local essentially finite-type homomorphism:
the residue extension is separable and `m_A S = m_S`. -/
theorem formallyUnramified_iff_separable_residue [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S] :
    FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
        (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  FormallyUnramified.iff_map_maximalIdeal_eq

/-- I.3.2 b): a local homomorphism `A → B` is *unramified* (net) if `m_A B = m_B` and the
residue field extension is finite and separable. No finiteness of `B` is assumed. -/
def IsUnramifiedLocalHom (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] : Prop :=
  (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧
    Module.Finite (ResidueField R) (ResidueField S) ∧
    Algebra.IsSeparable (ResidueField R) (ResidueField S)

/-- I.3.2: for a local homomorphism essentially of finite type, the local definition
b) agrees with formal unramifiedness (definition a) applied to the local rings). -/
theorem isUnramifiedLocalHom_iff_formallyUnramified [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S] :
    IsUnramifiedLocalHom R S ↔ FormallyUnramified R S := by
  refine ⟨fun ⟨h₁, _, h₃⟩ ↦ FormallyUnramified.iff_map_maximalIdeal_eq.mpr ⟨h₃, h₁⟩,
    fun _ ↦ ?_⟩
  obtain ⟨h₃, h₁⟩ := FormallyUnramified.iff_map_maximalIdeal_eq.mp ‹_›
  exact ⟨h₁, inferInstance, h₃⟩

/-- I.3.1(ii): unramified at a prime means that `Ω¹` vanishes after localizing. -/
theorem isUnramifiedAt_iff_subsingleton_differentials (q : Ideal S) [q.IsPrime] :
    IsUnramifiedAt R q ↔ Subsingleton Ω[Localization.AtPrime q⁄R] :=
  Algebra.formallyUnramified_iff _ _

/-- I.3.2: SGA's unramified algebras are mathlib's `Algebra.Unramified`
(formally unramified and of finite type). -/
theorem unramified_iff :
    Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- I.3, remark: net implies quasi-finite (mathlib). -/
theorem quasiFinite_of_formallyUnramified [EssFiniteType R S] [FormallyUnramified R S] :
    QuasiFinite R S :=
  inferInstance

/-- I.3, the different ideal: the set of points where `S` is ramified over `R` is the
support of `Ω¹_{S/R}`, i.e. (for `S` essentially of finite type) the closed set defined by
the annihilator of `Ω¹`. -/
theorem unramifiedLocus_eq_compl_support :
    unramifiedLocus R S = (Module.support S Ω[S⁄R])ᶜ :=
  Algebra.unramifiedLocus_eq_compl_support

/-- I.3.3: the unramified locus of an essentially finite-type algebra is open. -/
theorem isOpen_unramifiedLocus [EssFiniteType R S] : IsOpen (unramifiedLocus R S) :=
  Algebra.isOpen_unramifiedLocus

/-- I.3.1, I.3.3: unramifiedness can be checked after localizing away from an element. -/
theorem exists_unramified_away [FiniteType R S] (q : Ideal S) [q.IsPrime]
    [IsUnramifiedAt R q] :
    ∃ f ∉ q, Unramified R (Localization.Away f) :=
  exists_unramified_of_isUnramifiedAt (R := R) q

/-- If `M = N + I M` then `M = N + I^k M` for all `k`. -/
lemma sup_pow_smul_top_eq_top {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {N : Submodule R M} (h : N ⊔ I • ⊤ = ⊤) (k : ℕ) : N ⊔ I ^ k • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine top_le_iff.mp ?_
    calc ⊤ = N ⊔ I ^ k • (N ⊔ I • ⊤) := by rw [h, ih]
      _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by
          rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
      _ ≤ N ⊔ I ^ (k + 1) • ⊤ :=
          sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)

section Local

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- I.3.7, necessity, with completions replaced by their truncations: if `A → B` is
unramified with trivial residue field extension, every `A → B/m_Bⁿ` is surjective (so
`Â → B̂` is surjective). -/
theorem surjective_quotient_pow_of_map_maximalIdeal
    (hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (hk : Function.Surjective (ResidueField.map (algebraMap R S))) (n : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp (algebraMap R S)) := by
  let Q := S ⧸ maximalIdeal S ^ n
  let N : Submodule R Q := LinearMap.range (Algebra.linearMap R Q)
  -- `Q = N + m_A Q`
  have h1 : N ⊔ maximalIdeal R • ⊤ = ⊤ := by
    refine top_le_iff.mp fun q _ ↦ ?_
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨r', hr⟩ := hk (residue S s)
    obtain ⟨r, rfl⟩ := residue_surjective r'
    have hsr : s - algebraMap R S r ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hr, ResidueField.map_residue]
    rw [← hm, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at hsr
    have : Ideal.Quotient.mk (maximalIdeal S ^ n) s =
        algebraMap R Q r + Ideal.Quotient.mk _ (s - algebraMap R S r) := by
      rw [map_sub, Ideal.Quotient.mk_algebraMap, add_sub_cancel]
    rw [this]
    refine Submodule.add_mem_sup ⟨r, rfl⟩ ?_
    exact Submodule.smul_top_le_comap_smul_top (maximalIdeal R)
      ((Ideal.Quotient.mkₐ R (maximalIdeal S ^ n)).toLinearMap) hsr
  -- `m_A^n Q = 0`
  have h2 : maximalIdeal R ^ n • (⊤ : Submodule R Q) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr q _
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Submodule.mem_bot, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have := sup_pow_smul_top_eq_top h1 n
  rw [h2, sup_bot_eq] at this
  intro q
  obtain ⟨r, hr⟩ := (this ▸ Submodule.mem_top : q ∈ N)
  exact ⟨r, hr⟩

/-- I.3.7, sufficiency, with truncations: if every `A → B/m_Bⁿ` is surjective (i.e. `B̂` is
a quotient of `Â`) and `B` is noetherian, then `m_A B = m_B` and the residue extension is
trivial. -/
theorem map_maximalIdeal_of_surjective_quotient_pow [IsNoetherianRing S]
    (h : ∀ n, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp (algebraMap R S))) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧
      Function.Surjective (ResidueField.map (algebraMap R S)) := by
  refine ⟨le_antisymm (map_maximalIdeal_le _) ?_, fun x ↦ ?_⟩
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun x hx ↦ ?_
    obtain ⟨r, hr⟩ := h 2 (Ideal.Quotient.mk _ x)
    simp only [RingHom.comp_apply, Ideal.Quotient.eq] at hr
    have hr' : algebraMap R S r ∈ maximalIdeal S := by
      have : x - (x - algebraMap R S r) = algebraMap R S r := sub_sub_cancel _ _
      rw [← this]
      exact sub_mem hx (Ideal.pow_le_self two_ne_zero (by simpa using neg_mem hr))
    have hrm : r ∈ maximalIdeal R := by
      rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]; exact hr'
    have : x = algebraMap R S r + (x - algebraMap R S r) := by ring
    rw [this]
    refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hrm) ?_
    rw [smul_eq_mul, ← sq]
    simpa using neg_mem hr
  · obtain ⟨s, rfl⟩ := residue_surjective x
    obtain ⟨r, hr⟩ := h 1 (Ideal.Quotient.mk _ s)
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.map_residue]
    simp only [RingHom.comp_apply, Ideal.Quotient.eq, pow_one] at hr
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hr

/-- I.3.7: let `A → B` be a local homomorphism of noetherian local rings whose residue
field extension is trivial, or with `k(A)` algebraically closed. Then `B` is unramified
over `A` iff `B̂` is a quotient of `Â`; here in the equivalent form that every
`A → B/m_Bⁿ` is surjective. -/
theorem isUnramifiedLocalHom_iff_forall_surjective [IsNoetherianRing S]
    (hk : Function.Bijective (ResidueField.map (algebraMap R S)) ∨ IsAlgClosed (ResidueField R)) :
    IsUnramifiedLocalHom R S ↔ ∀ n, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal S ^ n)).comp (algebraMap R S)) := by
  constructor
  · rintro ⟨hm, hfin, -⟩
    refine surjective_quotient_pow_of_map_maximalIdeal hm ?_
    rcases hk with hk | hk
    · exact hk.2
    · exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  · intro h
    obtain ⟨hm, hsurj⟩ := map_maximalIdeal_of_surjective_quotient_pow h
    have hsurj' : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) := hsurj
    refine ⟨hm, .of_surjective (Algebra.linearMap _ _) hsurj', ?_⟩
    let e : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
      AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨RingHom.injective _, hsurj'⟩
    exact Algebra.IsSeparable.of_algHom _ _ e.symm.toAlgHom

end Local

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3, remark, for schemes: an unramified morphism (locally of finite type) is
locally quasi-finite. -/
instance (priority := 100) locallyQuasiFinite_of_formallyUnramified [LocallyOfFiniteType f]
    [FormallyUnramified f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› U V e
  have h₂ := HasRingHomProperty.appLE @FormallyUnramified f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- For affine opens `U ⊆ Y`, `V ⊆ f⁻¹ U` and `x ∈ V`, the stalk map at `x` is formally
unramified iff `Γ(X, V)` is unramified over `Γ(Y, U)` at the prime of `x`. -/
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
  · refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
    · have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime p) :=
        .of_isLocalization p.primeCompl
      exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p) _
    · have : Algebra.FormallyUnramified Γ(Y, U) (Localization.AtPrime q) := h
      exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U) _ _

/-- I.3.3: the set of points where a morphism locally of finite type is unramified is
open. -/
lemma isOpen_setOf_formallyUnramified_stalkMap [LocallyOfFiniteType f] :
    IsOpen {x | (f.stalkMap x).hom.FormallyUnramified} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  let W : Set V := (fun y ↦ hV.primeIdealOf y) ⁻¹' Algebra.unramifiedLocus Γ(Y, U) Γ(X, V)
  have hW : IsOpen W := Algebra.isOpen_unramifiedLocus.preimage hV.isoSpec.hom.continuous
  refine ⟨Subtype.val '' W, ?_, V.isOpenEmbedding'.isOpenMap _ hW,
    ⟨⟨x, hxV⟩, (formallyUnramified_stalkMap_iff f U hU V hV hVU hxV).mp hx, rfl⟩⟩
  rintro _ ⟨⟨y, hy⟩, hyW, rfl⟩
  exact (formallyUnramified_stalkMap_iff f U hU V hV hVU hy).mpr hyW

/-- I.3.3: the unramified locus of a morphism locally of finite type, as an open
subscheme. -/
def unramifiedLocusOpens [LocallyOfFiniteType f] : X.Opens :=
  ⟨{x | (f.stalkMap x).hom.FormallyUnramified}, isOpen_setOf_formallyUnramified_stalkMap f⟩

/-- I.3.1, (iii) ⇒ (i), globally: if the diagonal is an open immersion, `f` is unramified.
The converse is `isOpenImmersion_diagonal_of_formallyUnramified`. -/
theorem formallyUnramified_of_isOpenImmersion_diagonal
    [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f :=
  inferInstance

/-- I.3.1, (i) ⇒ (iii), globally: for `f` locally of finite type and unramified, the diagonal
is an open immersion. -/
theorem isOpenImmersion_diagonal_of_formallyUnramified
    [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.diagonal f) :=
  inferInstance

/-- I.3.5(i): an immersion is unramified. -/
instance (priority := 900) formallyUnramified_of_isImmersion [IsImmersion f] :
    FormallyUnramified f :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.5(ii): the composite of unramified morphisms is unramified. -/
instance formallyUnramified_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [FormallyUnramified f] [FormallyUnramified g] : FormallyUnramified (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.5(iii): unramified is stable under base change. -/
instance formallyUnramified_fst {X' : Scheme.{u}} (g : X' ⟶ Y) [FormallyUnramified g] :
    FormallyUnramified (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g ‹_›

/-- I.3.6(v): if `f ≫ g` is unramified then `f` is unramified. -/
theorem formallyUnramified_of_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  FormallyUnramified.of_comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.6(iv), special case: base change along the other projection. SGA's cartesian product
`X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂` of two unramified morphisms is not stated here; it follows from
I.3.5 (ii) and (iii). -/
instance formallyUnramified_snd {X' : Scheme.{u}} (g : X' ⟶ Y) [FormallyUnramified f] :
    FormallyUnramified (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.6(vi): if `f` is unramified, so is `f_red`. More generally, if `iX : X' ⟶ X` is a
closed immersion (e.g. `X_red ⟶ X`) and `g : X' ⟶ Y'` satisfies `g ≫ iY = iX ≫ f` for
some `iY : Y' ⟶ Y` (e.g. `Y_red ⟶ Y`), then `g` is unramified. -/
theorem formallyUnramified_of_comp_eq {X' Y' : Scheme.{u}} (g : X' ⟶ Y') (iX : X' ⟶ X)
    (iY : Y' ⟶ Y) [IsClosedImmersion iX] (w : g ≫ iY = iX ≫ f) [FormallyUnramified f] :
    FormallyUnramified g := by
  have : FormallyUnramified (g ≫ iY) := w ▸ inferInstance
  exact FormallyUnramified.of_comp g iY

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.4: if `X` is unramified over `Y`, the graph of a `Y`-morphism `X' ⟶ X`
is an open immersion. (The graph is `X' ⟶ X' ×_Y X`, as in the standard
formulation; the source's target `X ×_Y X` is recorded in the translation
README.) -/
instance isOpenImmersion_graph {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.lift (𝟙 X') g (Category.id_comp (g ≫ f))) :=
  MorphismProperty.of_isPullback (pullback_lift_diagonal_isPullback g f) inferInstance

end SGA.SGA1.ExposeI
