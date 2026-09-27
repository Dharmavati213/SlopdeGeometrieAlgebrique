/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeXI.GenericLine
import SGA.SGA1.ExposeXI.ProjectiveLine

/-!
# Projective space is simply connected (XI.1.1): charts

Let `k` be algebraically closed and `P = Proj k[xⱼ : j ∈ σ]` (`σ` finite, with two distinct
indices `n ≠ s`). A connected étale covering `p : Y ⟶ P` is an isomorphism
(`isIso_of_isFinite_of_etale`, in `SGA.SGA1.ExposeXI.ProjectiveSpaceSimplyConnected`), so `P` is
simply connected (`isSimplyConnected_proj`, `projectiveSpaceSimplyConnectedStatement`). This file
contains the geometric preliminaries: normality and connectedness of `P`, and the rings of `Y` over
the charts `D₊(xᵢ)`.

The proof restricts `Y` to the generic line through the point `e = (xₙ = 1, xⱼ = 0)`, a line over
the field `F = k(wⱼ)` (`SGA.SGA1.ExposeXI.GenericLine`), instead of using the genus formula
(SGA's argument for `r = 1` and its induction on hyperplane sections, X.2.10) or the birational
invariance X.3.4 (SGA's second proof):

* `P` is normal, so `Y` is normal and, being connected, integral (I.9.10, I.9.11);
* over the generic line, `Y` is given by finite étale algebras `B₀ = F[t] ⊗ Γ(Y, p⁻¹ D₊(xₙ))` and
  `B₁ = F[u] ⊗ Γ(Y, p⁻¹ D₊(x_s))` with common localization `W` over `F[t, t⁻¹]`
  (`isLocalization_of_isPushout`); `B₁` and `W` are localizations of the domain
  `Γ(Y, p⁻¹ D₊(x_s))`, hence domains (the generic line meets the generic point of `Y`);
* by the Riemann–Roch inequality for the line (`ringHom_eq_of_isDomain_of_isLocalization`), the
  points of `Y` over `e`, which give rational points of `B₀` over `t = 0`, are unique;
* so the fibre of `Y` at `e` is a single point, and `Y ≅ P` (Exposé V).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
  AlgebraicGeometry.ProjectiveSpace

namespace SGA.SGA1.ExposeXI.ProjectiveSpace

section Normal

variable {k : Type u} [Field k] {σ : Type u}

/-- The chart `D₊(xᵢ)` of `Proj k[σ]` is affine. -/
lemma isAffineOpen_basicOpen_X (i : σ) :
    IsAffineOpen (Proj.basicOpen (grading σ k) (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem_grading i) one_pos

/-- `Γ(D₊(xᵢ)) = k[σ]_(xᵢ) = k[xⱼ / xᵢ]`. -/
noncomputable def chartRingEquiv (i : σ) :
    Γ(Proj (grading σ k), Proj.basicOpen (grading σ k) (X i)) ≃+* MvPolynomial {j // j ≠ i} k :=
  (Proj.basicOpenIsoAway (grading σ k) (X i) (X_mem_grading i)
    one_pos).commRingCatIsoToRingEquiv.symm.trans (awayEquiv i rfl)

/-- Projective space over a field is normal. -/
theorem isNormalScheme_proj : ExposeI.IsNormalScheme (Proj (grading σ k)) := by
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ Proj.basicOpen (grading σ k) (X i) := by
    have hx : x ∈ (⊤ : (Proj (grading σ k)).Opens) := trivial
    rw [← iSup_basicOpen_X σ k] at hx
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hU := isAffineOpen_basicOpen_X (k := k) i
  have hΓ : IsDomain Γ(Proj (grading σ k), Proj.basicOpen (grading σ k) (X i)) ∧
      IsIntegrallyClosed Γ(Proj (grading σ k), Proj.basicOpen (grading σ k) (X i)) :=
    ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv (chartRingEquiv i).symm
      ⟨inferInstance, inferInstance⟩
  obtain ⟨_, _⟩ := hΓ
  refine ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
    (ExposeI.stalkEquivLocalization hU x hi).symm ⟨inferInstance, ?_⟩
  exact isIntegrallyClosed_of_isLocalization _
    ((isAffineOpen_basicOpen_X (k := k) i).primeIdealOf ⟨x, hi⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

end Normal

section Basic

variable {k : Type u} [Field k] {σ : Type u} [Finite σ]

instance : IsNoetherianRing (grading σ k 0) :=
  isNoetherianRing_of_surjective k _ (algebraMap k (grading σ k 0))
    (bijective_algebraMap_grading_zero σ k).2

instance : IsLocallyNoetherian (Proj (grading σ k)) :=
  LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero (grading σ k))

instance [Nonempty σ] : Nonempty (Proj (grading σ k)) := by
  obtain ⟨i⟩ := ‹Nonempty σ›
  have : Nontrivial (Away (grading σ k) (X i)) :=
    (awayEquiv i (rfl : (X i : MvPolynomial σ k) = X i)).toEquiv.nontrivial
  exact ⟨Proj.awayι (grading σ k) (X i) (X_mem_grading i) one_pos
    (Classical.arbitrary (Spec (.of (Away (grading σ k) (X i)))))⟩

/-- Projective space over a field is connected: `Γ(P, 𝒪) = k`. -/
instance [Nonempty σ] : ConnectedSpace (Proj (grading σ k)) := by
  refine CohomologyAux.connectedSpace_of_trivialIdempotents _ ?_
  have : IsIso (Proj.toSpecZero (grading σ k)).appTop :=
    projectiveSpace.isIso_toSpecZero_appTop (σ := σ) (A := k)
  let e₁ : Γ(Proj (grading σ k), ⊤) ≃+* grading σ k 0 :=
    (asIso (Proj.toSpecZero (grading σ k)).appTop).commRingCatIsoToRingEquiv.symm.trans
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  let e₂ : k ≃+* grading σ k 0 := RingEquiv.ofBijective _ (bijective_algebraMap_grading_zero σ k)
  refine CohomologyAux.TrivialIdempotents.of_ringEquiv (e₂.trans e₁.symm) fun a ha ↦ ?_
  exact IsIdempotentElem.iff_eq_zero_or_one.mp ha

end Basic

section Covering

variable {k : Type u} [Field k] {σ : Type u} [Finite σ]

/-- A connected étale covering of projective space is integral (I.9.10, I.9.11). -/
theorem isIntegral_of_isFinite_of_etale {Y : Scheme.{u}} (p : Y ⟶ Proj (grading σ k)) [IsFinite p]
    [Etale p] [ConnectedSpace Y] : IsIntegral Y := by
  have hY := ExposeI.isNormalScheme_of_etale p isNormalScheme_proj
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : IrreducibleSpace Y := ExposeI.irreducibleSpace_of_isDomain_stalk fun y ↦ (hY y).1
  have : IsReduced Y := by
    have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
      have := (hY y).1
      infer_instance
    exact isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end Covering

/-- A connected étale covering `p : Y ⟶ X` whose fibre at a geometric point `s̄` has at most one
point is an isomorphism (Exposé V). -/
theorem isIso_of_forall_eq {X Y : Scheme.{u}} [ConnectedSpace X] (p : Y ⟶ X) [IsFinite p]
    [Etale p] [ConnectedSpace Y] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (h : ∀ y₁ y₂ : Spec (.of Ω) ⟶ Y, y₁ ≫ p = s → y₂ ≫ p = s → y₁ = y₂) : IsIso p := by
  let F := ExposeV.FEt.fiber Ω s
  let Y' : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace Y'.left := ‹_›
  have : PreGaloisCategory.IsConnected Y' := ExposeV.FEt.isConnected_of_connectedSpace Y'
  let T : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  have : IsIso (T.hom : T.left ⟶ X) := inferInstanceAs (IsIso (𝟙 X))
  let g : Y' ⟶ T := MorphismProperty.Over.homMk p (Category.comp_id p)
  have hT := ExposeV.subsingleton_fiber_of_isTerminal F (ExposeV.FEt.isTerminalOfIsIso T)
  obtain ⟨y⟩ := PreGaloisCategory.nonempty_fiber_of_isConnected F Y'
  have hY' : Subsingleton (F.obj Y') := ⟨fun a b ↦ (ExposeV.FEt.fiberEquiv Ω s Y').injective
    (CategoryTheory.Over.OverMorphism.ext (h _ _ (ExposeV.FEt.fiberEquiv_w Ω s a)
      (ExposeV.FEt.fiberEquiv_w Ω s b)))⟩
  have : IsIso (F.map g) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨fun a b _ ↦ Subsingleton.elim a b, fun t ↦ ⟨y, Subsingleton.elim _ _⟩⟩
  have : IsIso g := isIso_of_reflects_iso g F
  exact inferInstanceAs
    (IsIso ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).map g))

set_option backward.isDefEq.respectTransparency false in
/-- The ring map `Γ(X, U) → R` of the point `Spec R ⟶ Spec Γ(X, U) ⟶ X` of an affine open `U`. -/
lemma appLE_SpecMap_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {R : CommRingCat.{u}} (φ : Γ(X, U) ⟶ R) (h) :
    (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom = φ := by
  have H := IsAffineOpen.SpecMap_appLE_fromSpec (Spec.map φ ≫ hU.fromSpec) hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, ← Category.assoc, Scheme.isoSpec_Spec_inv] at H
  have H' := (cancel_mono hU.fromSpec).mp H
  rw [← Spec.map_comp] at H'
  rw [Spec.map_injective H', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A finite étale morphism from a nonempty scheme onto a connected scheme is surjective. -/
lemma surjective_of_isFinite_of_etale {X Y : Scheme.{u}} [ConnectedSpace X] [Nonempty Y]
    (p : Y ⟶ X) [IsFinite p] [Etale p] : Function.Surjective p := by
  have h : IsClopen (Set.range p) :=
    ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
  rw [← Set.range_eq_univ]
  exact h.eq_univ (Set.range_nonempty _)

set_option backward.isDefEq.respectTransparency false in
/-- A point `y : Spec R ⟶ X` landing in an affine open `V` is determined by the ring map
`Γ(X, V) → R`. -/
lemma eq_SpecMap_fromSpec {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {R : CommRingCat.{u}} (y : Spec R ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    y = Spec.map (y.appLE V ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hV.fromSpec := by
  have H := IsAffineOpen.SpecMap_appLE_fromSpec y hV (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at H
  rw [Spec.map_comp, Category.assoc, H, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

section Charts

variable {k : Type u} [Field k] {σ : Type u} {Y : Scheme.{u}} (p : Y ⟶ Proj (grading σ k))

lemma awayToSection_bijective (f : MvPolynomial σ k) {d : ℕ} (hf : f ∈ grading σ k d)
    (hd : 0 < d) : Function.Bijective (Proj.awayToSection (grading σ k) f).hom := by
  rw [← ConcreteCategory.isIso_iff_bijective, ← Proj.basicOpenIsoAway_hom _ f hf hd]
  infer_instance

/-- The ring map `k[σ]_(f) = Γ(D₊(f)) → Γ(Y, p⁻¹ D₊(f))`. -/
noncomputable def chartMap (f : MvPolynomial σ k) :
    Away (grading σ k) f →+* Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) f) :=
  (Proj.awayToSection (grading σ k) f ≫ p.app _).hom

lemma chartMap_finite [IsFinite p] (i : σ) : (chartMap p (X i)).Finite :=
  RingHom.Finite.comp (p.finite_app _ (isAffineOpen_basicOpen_X i))
    (RingHom.Finite.of_surjective _ (awayToSection_bijective _ (X_mem_grading i) one_pos).2)

lemma chartMap_etale [Etale p] [IsAffineHom p] (i : σ) : (chartMap p (X i)).Etale := by
  refine RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (awayToSection_bijective _ (X_mem_grading i) one_pos)) ?_
  have := HasRingHomProperty.appLE @Etale p inferInstance ⟨_, isAffineOpen_basicOpen_X i⟩
    ⟨_, (isAffineOpen_basicOpen_X i).preimage p⟩ le_rfl
  rwa [Scheme.Hom.appLE_eq_app] at this

/-- The restriction `Γ(Y, p⁻¹ D₊(f)) → Γ(Y, p⁻¹ D₊(x))` for `D₊(x) ⊆ D₊(f)`. -/
noncomputable def chartRes (f x : MvPolynomial σ k)
    (h : Proj.basicOpen (grading σ k) x ≤ Proj.basicOpen (grading σ k) f) :
    Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) f) →+* Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) x) :=
  (Y.presheaf.map (homOfLE (p.preimage_mono h)).op).hom

lemma chartRes_comp_chartMap {f g x : MvPolynomial σ k} {e : ℕ} (hg : g ∈ grading σ k e)
    (hx : x = f * g) :
    (chartRes p f x (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).comp (chartMap p f) =
      (chartMap p x).comp (awayMap (grading σ k) hg hx) := by
  have h := congrArg (· ≫ p.app (Proj.basicOpen (grading σ k) x))
    (Proj.awayMap_awayToSection (grading σ k) hg hx)
  simp only [Category.assoc, Scheme.Hom.naturality] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isLocalization_chartRes [IsAffineHom p] (i j : σ) {x : MvPolynomial σ k}
    (hx : x = X i * X j) :
    letI := (chartRes p (X i) x (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).toAlgebra
    IsLocalization.Away (chartMap p (X i) (Away.isLocalizationElem (X_mem_grading (R := k) i)
      (X_mem_grading j))) Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) x) := by
  subst hx
  refine ((isAffineOpen_basicOpen_X i).preimage p).isLocalization_of_eq_basicOpen _
    (homOfLE (p.preimage_mono (Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩))) ?_
  change _ = Y.basicOpen (p.app _ (Proj.awayToSection _ _ _))
  rw [← Scheme.preimage_basicOpen, ProjectiveLine.basicOpen_awayToSection_isLocalizationElem _
    (X_mem_grading i) one_pos (X_mem_grading j) one_pos, Proj.basicOpen_mul]

end Charts

end SGA.SGA1.ExposeXI.ProjectiveSpace
