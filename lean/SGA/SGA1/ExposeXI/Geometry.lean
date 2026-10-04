/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé XI, §1–§3: projective spaces, unirational varieties, abelian varieties

We express `π₁(X) = 0` as `IsSimplyConnected X` (every connected finite étale cover is an
isomorphism) and "`π₁(X)` is finite" as `HasFiniteFundamentalGroup X` (the fundamental group of
Exposé V is finite), record the statements of §1–§2, and prove the formal ingredients:

* `isSimplyConnected_iff_subsingleton`: for a connected scheme, `IsSimplyConnected X` means that
  the fundamental group of Exposé V is trivial;
* `isSimplyConnected_spec_of_isSepClosed`: the case `r = 0` of XI.1.1, for any separably
  closed field;
* `mul_comm_of_monoidHom_prod`: the Eckmann–Hilton argument of XI.2;
* `mulN`, `isMonHom_mulN`: multiplication by `n` on a commutative group object is a
  homomorphism;
* mathlib's theorem that a proper geometrically integral group scheme over a field (an abelian
  variety) is commutative.

XI.1.1 is proved in `ProjectiveSpaceSimplyConnected`
(`ProjectiveSpace.isSimplyConnected_projectiveSpace`; the case `r = 1` also in `ProjectiveLine`),
powers of `ℙ¹` are treated in `ProjectiveLinePower`, and the commutativity of `π₁` of an abelian
variety (XI.2) in `AbelianFundamentalGroup`. §3 (projecting cones and Zariski's example) consists
of examples showing that X.1.3, X.1.4 and X.2.4 fail without separability; it is not formalized.
-/

universe u

namespace SGA.SGA1.ExposeXI

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/-- V, XI.1: a scheme `X` is *simply connected* (`π₁(X) = 0`) if it is connected and every
connected finite étale `X`-scheme is isomorphic to `X`, i.e. every finite étale covering of `X`
is completely decomposed. -/
def IsSimplyConnected (X : Scheme.{u}) : Prop :=
  ConnectedSpace X ∧
    ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X) [IsFinite f] [Etale f], ConnectedSpace Y → IsIso f

/-- XI.1.3: the connected scheme `X` has finite fundamental group: `π₁(X, s̄)` (Exposé V) is
finite for every geometric point `s̄ : Spec Ω ⟶ X`, `Ω` separably closed. By V.7 the groups at
different geometric points are isomorphic (`hasFiniteFundamentalGroup_iff_exists`). -/
def HasFiniteFundamentalGroup (X : Scheme.{u}) : Prop :=
  ConnectedSpace X ∧ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
    Finite (ExposeV.etaleFundamentalGroup Ω s)

section FundamentalGroup

open PreGaloisCategory

/-- XI.1: a connected scheme is simply connected if and only if its fundamental group (Exposé V,
at any geometric point) is trivial. -/
theorem isSimplyConnected_iff_subsingleton {X : Scheme.{u}} [ConnectedSpace X]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    IsSimplyConnected X ↔ Subsingleton (ExposeV.etaleFundamentalGroup Ω s) := by
  let F := ExposeV.FEt.fiber Ω s
  constructor
  · rintro ⟨-, h⟩
    have key (Y : ExposeV.FEt X) (hY : IsConnected Y) : Subsingleton (F.obj Y) := by
      have : ConnectedSpace Y.left := ExposeV.FEt.connectedSpace_of_isConnected Y
      have : IsFinite (Y.hom : Y.left ⟶ X) := Y.prop.1
      have : Etale (Y.hom : Y.left ⟶ X) := Y.prop.2
      have : IsIso (Y.hom : Y.left ⟶ X) := h (Y.hom : Y.left ⟶ X) ‹_›
      exact ExposeV.subsingleton_fiber_of_isTerminal F (ExposeV.FEt.isTerminalOfIsIso Y)
    exact ⟨fun σ τ ↦ by
      rw [ExposeV.aut_eq_one_of_forall_isConnected F key σ,
        ExposeV.aut_eq_one_of_forall_isConnected F key τ]⟩
  · intro hπ
    refine ⟨inferInstance, fun Y f _ _ hY ↦ ?_⟩
    let Y' : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
    have : ConnectedSpace Y'.left := hY
    have : IsConnected Y' := ExposeV.FEt.isConnected_of_connectedSpace Y'
    let T : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
    have : IsIso (T.hom : T.left ⟶ X) := inferInstanceAs (IsIso (𝟙 X))
    let g : Y' ⟶ T := MorphismProperty.Over.homMk f (Category.comp_id f)
    have hT := ExposeV.subsingleton_fiber_of_isTerminal F (ExposeV.FEt.isTerminalOfIsIso T)
    obtain ⟨y⟩ := nonempty_fiber_of_isConnected F Y'
    have hY' : Subsingleton (F.obj Y') := ⟨fun a b ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) a b
      rw [← hσ, Subsingleton.elim σ 1, one_smul]⟩
    have : IsIso (F.map g) := (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨fun a b _ ↦ Subsingleton.elim a b, fun t ↦ ⟨y, Subsingleton.elim _ _⟩⟩
    have : IsIso g := isIso_of_reflects_iso g F
    exact inferInstanceAs
      (IsIso ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).map g))

/-- XI.1.3: for a connected scheme, it suffices to check finiteness of `π₁` at one geometric
point. -/
theorem hasFiniteFundamentalGroup_iff_exists {X : Scheme.{u}} [ConnectedSpace X] :
    HasFiniteFundamentalGroup X ↔ ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω)
      (s : Spec (.of Ω) ⟶ X), Finite (ExposeV.etaleFundamentalGroup Ω s) := by
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    let φ : X.residueField x ⟶ CommRingCat.of (AlgebraicClosure (X.residueField x)) :=
      CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))
    exact ⟨_, _, inferInstance, Spec.map φ ≫ X.fromSpecResidueField x, h _ _⟩
  · rintro ⟨Ω, _, _, s, hs⟩
    refine ⟨inferInstance, fun Ω' _ _ s' ↦ ?_⟩
    obtain ⟨e⟩ := ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv Ω Ω' s s'
    exact Finite.of_equiv _ e.toEquiv

/-- XI.1.1, XI.1.3: a simply connected scheme has finite fundamental group. -/
theorem IsSimplyConnected.hasFiniteFundamentalGroup {X : Scheme.{u}} (h : IsSimplyConnected X) :
    HasFiniteFundamentalGroup X := by
  have := h.1
  refine ⟨h.1, fun Ω _ _ s ↦ ?_⟩
  have := (isSimplyConnected_iff_subsingleton Ω s).1 h
  infer_instance

end FundamentalGroup

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective space `ℙʳ_k = Proj k[X₀, …, X_r]`. -/
noncomputable abbrev projectiveSpace (k : Type u) [CommRing k] (r : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k)

/-- XI.1.1: projective space over an algebraically closed field is simply connected. (SGA's proof
uses the genus formula for `r = 1` and X 2.10, or X 1.7 and X 3.4.) It is proved as
`ProjectiveSpace.projectiveSpaceSimplyConnectedStatement`, by the Riemann–Roch inequality on the
generic line through a point (`ProjectiveSpace.isSimplyConnected_projectiveSpace`). -/
def ProjectiveSpaceSimplyConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (r : ℕ), IsSimplyConnected (projectiveSpace k r)

end ProjectiveSpace

section Point

/-- XI.1.1 for `r = 0`, algebraic form: a finite étale algebra over a separably closed field whose
spectrum is connected is the field itself. -/
theorem bijective_algebraMap_of_isSepClosed (k B : Type u) [Field k] [IsSepClosed k]
    [CommRing B] [Algebra k B] [Algebra.Etale k B] [ConnectedSpace (PrimeSpectrum B)] :
    Function.Bijective (algebraMap k B) := by
  have := Algebra.FormallyUnramified.finite_of_free k B
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  have hsub : Subsingleton (PrimeSpectrum B) := subsingleton_of_preconnected_totallyDisconnected
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (PrimeSpectrum B))
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed k B
  have hbij : Function.Bijective (algebraMap k (PrimeSpectrum B → k)) :=
    ⟨fun x y hxy ↦ congrFun hxy p₀, fun v ↦ ⟨v p₀, funext fun p ↦ by
      rw [Subsingleton.elim p p₀]; rfl⟩⟩
  have hcomp : ⇑(algebraMap k B) = e.symm ∘ algebraMap k (PrimeSpectrum B → k) := by
    funext x
    rw [Function.comp_apply, ← e.commutes, e.symm_apply_apply]
  rw [hcomp]
  exact e.symm.bijective.comp hbij

/-- XI.1.1 for `r = 0`: the spectrum of a separably closed (e.g. algebraically closed) field is
simply connected. -/
theorem isSimplyConnected_spec_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k] :
    IsSimplyConnected (Spec (.of k)) := by
  refine ⟨inferInstance, fun Y f _ _ hY ↦ ?_⟩
  have : IsAffine Y := isAffine_of_isAffineHom f
  set ψ := (Scheme.ΓSpecIso (.of k)).inv.hom
  have hψ : Function.Bijective ψ :=
    (ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (.of k)).inv).mp inferInstance
  set φ : k →+* Γ(Y, ⊤) := f.appTop.hom.comp ψ
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition ψ f.appTop.hom
    (RingHom.Etale.of_bijective hψ) (HasRingHomProperty.appTop @Etale f inferInstance)
  let := φ.toAlgebra
  have : Algebra.Etale k Γ(Y, ⊤) := hφ
  have : ConnectedSpace (PrimeSpectrum Γ(Y, ⊤)) :=
    (Scheme.homeoOfIso Y.isoSpec).surjective.connectedSpace
      (Scheme.homeoOfIso Y.isoSpec).continuous
  have hbij : Function.Bijective φ := bijective_algebraMap_of_isSepClosed k Γ(Y, ⊤)
  have hfun : ⇑f.appTop.hom = φ ∘ (Scheme.ΓSpecIso (.of k)).hom.hom := by
    funext x
    simp [φ, ψ]
  have hbij' : Function.Bijective f.appTop.hom := by
    rw [hfun]
    exact hbij.comp ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  have : IsIso (Spec.map f.appTop) := isIso_SpecMap_iff.mpr hbij'
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (arrowIsoSpecΓOfIsAffine f)).mpr this

end Point

section Rational

/-- The ring map from `k` to the function field of an irreducible `k`-scheme. -/
noncomputable def functionFieldMap {k : Type u} [Field k] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom

/-- A field extension `K/k` is purely transcendental if `K` is generated over `k` by an
algebraically independent set. -/
def IsPurelyTranscendental (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ s : Set K, AlgebraicIndependent k ((↑) : s → K) ∧ IntermediateField.adjoin k s = ⊤

/-- XI.1.2: the field `K ⊇ k` is unirational over `k`: it has a finite extension which is
purely transcendental over `k`. -/
def IsUnirational (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    IsPurelyTranscendental k L

/-- A scheme is normal if all its local rings are integrally closed. -/
def IsNormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- XI.1.2: a proper normal rational variety over an algebraically closed field is simply
connected. Proved as `rationalSimplyConnectedStatement` (in `RationalVarieties`). -/
def RationalSimplyConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f], IsNormalScheme X →
    (letI := (functionFieldMap f).toAlgebra; IsPurelyTranscendental k X.functionField) →
    IsSimplyConnected X

/-- XI.1.3: the fundamental group of a normal unirational variety over an algebraically closed
field is finite. Proved as `unirationalFiniteFundamentalGroupStatement` (in
`UnirationalVarieties`). -/
def UnirationalFiniteFundamentalGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f], IsNormalScheme X →
    (letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) →
    HasFiniteFundamentalGroup X

/-- XI.1.4 (Serre): a smooth unirational variety over an algebraically closed field of
characteristic zero is simply connected. SGA says "projective"; we state it for proper varieties,
to which it extends. Not proved unconditionally:
`serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero` (in `SerreUnirational`) derives it
from `HodgeSymmetryZeroStatement` (Hodge symmetry `h^{0,q} = h^{q,0}`, transcendental), its only
open input. -/
def SerreUnirationalSimplyConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f],
    (letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) →
    IsSimplyConnected X

end Rational

section AbelianVarieties

/-- XI.2 (Eckmann–Hilton): `π₁` commutes with products, so the multiplication of a group scheme
induces a homomorphism `m : π₁ × π₁ → π₁` which is unital; this forces `π₁` to be commutative. -/
theorem mul_comm_of_monoidHom_prod {Γ : Type*} [Group Γ] (m : Γ × Γ →* Γ)
    (h₁ : ∀ g, m (g, 1) = g) (h₂ : ∀ g, m (1, g) = g) (a b : Γ) : a * b = b * a := by
  have hab : m (a, b) = a * b := by
    have : ((a, b) : Γ × Γ) = (a, 1) * (1, b) := by simp
    rw [this, map_mul, h₁, h₂]
  have hba : m (a, b) = b * a := by
    have : ((a, b) : Γ × Γ) = (1, b) * (a, 1) := by simp
    rw [this, map_mul, h₁, h₂]
  exact hab.symm.trans hba

open scoped MonObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- The product of two homomorphisms into a commutative monoid object is a homomorphism. -/
instance isMonHom_mul {M N : C} [MonObj M] [MonObj N] [IsCommMonObj N] (f g : M ⟶ N)
    [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem isMonHom_pow {M N : C} [MonObj M] [MonObj N] [IsCommMonObj N] (f : M ⟶ N)
    [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact isMonHom_mul _ _

/-- XI.2: multiplication by `n` on a monoid object, `x ↦ xⁿ`. -/
def mulN (G : C) [MonObj G] (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

/-- XI.2: on a commutative group object (e.g. an abelian variety), multiplication by `n` is a
homomorphism. -/
instance isMonHom_mulN (G : C) [MonObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) :=
  isMonHom_pow _ n

/-- XI.2 (mathlib): an abelian variety, i.e. a proper geometrically integral group scheme over
a field, is commutative. -/
theorem isCommMonObj_of_abelianVariety {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G] : IsCommMonObj G :=
  isCommMonObj_of_isProper_of_geometricallyIntegral G

/-- XI.2.1, key step (Serre–Lang): every connected finite étale covering of an abelian variety `A`
over an algebraically closed field is dominated by multiplication by some `n > 0`. This is the
key step of SGA's proof that `π₁(A) = lim_n K_n` (the Tate module), where `K_n` is the group of
`n`-torsion points. Proved as `serreLangStatement` (in `SerreLang`). SGA's XI.2.1 itself is
`AbelianVarietyFundamentalGroupStatement` (in `TateModule`): proved in characteristic `0`
(`exists_tateModule_equiv_of_charZero`) and from SGA's cited fact that `n_A` is an isogeny
(`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`), with its `ℓ`-primary clause proved for
every prime `ℓ ≠ char k` (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`). In characteristic
`p > 0` it is equivalent to its `p`-primary clause
(`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`), which is open. -/
def SerreLangStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] ⦃Y : Scheme.{u}⦄ (f : Y ⟶ A.left)
    [IsFinite f] [Etale f], ConnectedSpace Y →
      ∃ n : ℕ, 0 < n ∧ ∃ g : A.left ⟶ Y, g ≫ f = (mulN A n).left

end AbelianVarieties

end SGA.SGA1.ExposeXI
