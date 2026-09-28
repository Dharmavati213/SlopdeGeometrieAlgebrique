/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import SGA.SGA1.ExposeXII.Points

/-!
# SGA 1, Exposé XII, §§2–3: comparison statements for affine schemes

Let `K` be an algebraically closed field (for instance `ℂ`) and `X = Spec A` with `A` of finite
type over `K`. The Nullstellensatz identifies `X(K)` with the closed points of `X`
(`equivMaximalSpectrum`, part of XII.1.1), and the Jacobson property of `X` (EGA IV 10.4.8),
used throughout §§2–3, takes the forms `isNilpotent_of_forall_apply_eq_zero`,
`eq_of_isConstructible` and `denseRange_toPrimeSpectrum`.

Proved comparison statements (affine case):
* XII.2.1 (i): `nonempty_iff_nontrivial`; XII.2.1 (i') with (viii) in dimension `0`:
  `discreteTopology_iff`, `discreteTopology_iff_krullDimLE`; XII.3.2 (v), (vi) for `X → Spec K`:
  `compactSpace_iff`, `finite_iff` (via Noether normalization);
* XII.3.1 (vii), one direction: `injective_proj_of_injective_comap`;
* XII.3.2 (i): `surjective_proj_iff` (via Chevalley's theorem);
* XII.2.3, direct implications: `continuous_toPrimeSpectrum`; XII.2.4, one direction:
  `connectedSpace_of_connectedSpace_points`; XII.2.6, surjectivity:
  `connectedComponentsMap_surjective`;
* the faithfulness step of XII.5.1: `algHom_ext_of_map_eq`.

The analytic statements XII.2.2 and XII.2.4 are formulated over `ℂ` as
`ClosureComparisonStatement` and `ConnectedComparisonStatement`; from the former we derive the
rest of XII.2.3 and XII.3.2 (ii) (`isClosed_iff_of_closureComparison`,
`dense_iff_of_closureComparison`, `denseRange_proj_iff_of_closureComparison`). Both are proved
later: XII.2.2 in `Nullstellensatz.lean` (from Rückert's Nullstellensatz) and XII.2.4 in
`Connected.lean` (`Points.connectedComparison`).
-/

noncomputable section

namespace SGA.SGA1.ExposeXII

open Topology Set
open scoped TensorProduct

namespace Points

section Field

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]

/-- The kernel of a point, a maximal ideal: the closed point of `X` underlying a point of
`X(K)`. -/
def ker (φ : Points K A) : Ideal A := RingHom.ker φ.toRingHom

lemma mem_ker {φ : Points K A} {a : A} : a ∈ ker φ ↔ φ a = 0 := RingHom.mem_ker

lemma sub_algebraMap_mem_ker (φ : Points K A) (a : A) : a - algebraMap K A (φ a) ∈ ker φ := by
  simp [mem_ker]

lemma surjective (φ : Points K A) : Function.Surjective φ :=
  fun c ↦ ⟨algebraMap K A c, by simp⟩

instance (φ : Points K A) : (ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ.toRingHom φ.surjective

/-- A point is determined by its kernel. -/
lemma eq_of_ker_eq {φ ψ : Points K A} (h : ker φ = ker ψ) : φ = ψ := by
  ext a
  have := sub_algebraMap_mem_ker φ a
  rw [h, mem_ker, map_sub, apply_algebraMap, sub_eq_zero] at this
  exact this.symm

lemma ker_injective : Function.Injective (ker (K := K) (A := A)) := fun _ _ ↦ eq_of_ker_eq

/-- The map `X(K) → X` sending a `K`-point to the (closed) point of `X` underlying it. -/
def toPrimeSpectrum (φ : Points K A) : PrimeSpectrum A := ⟨ker φ, inferInstance⟩

@[simp] lemma toPrimeSpectrum_asIdeal (φ : Points K A) : (toPrimeSpectrum φ).asIdeal = ker φ := rfl

lemma toPrimeSpectrum_injective : Function.Injective (toPrimeSpectrum (K := K) (A := A)) :=
  fun _ _ h ↦ eq_of_ker_eq (PrimeSpectrum.ext_iff.mp h)

lemma isClosed_toPrimeSpectrum (φ : Points K A) : IsClosed {toPrimeSpectrum φ} :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (inferInstanceAs (ker φ).IsMaximal)

lemma toPrimeSpectrum_mem_basicOpen {φ : Points K A} {f : A} :
    toPrimeSpectrum φ ∈ PrimeSpectrum.basicOpen f ↔ φ f ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, toPrimeSpectrum_asIdeal, mem_ker]

/-- XII.2.3, direct implications: the map `X(K) → X` is continuous, i.e. Zariski open (resp.
closed) subsets of `X` have open (resp. closed) sets of points. -/
theorem continuous_toPrimeSpectrum [TopologicalSpace K] [T1Space K] :
    Continuous (toPrimeSpectrum (K := K) (A := A)) := by
  refine PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr ?_
  rintro _ ⟨f, rfl⟩
  have : toPrimeSpectrum ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) =
      {φ : Points K A | φ f ≠ 0} := by
    ext; exact toPrimeSpectrum_mem_basicOpen
  rw [this]
  exact isOpen_compl_singleton.preimage (continuous_apply f)

/-- A finite `K`-scheme has finitely many `K`-points. -/
instance finite_of_moduleFinite [Module.Finite K A] : Finite (Points K A) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Finite.of_injective (fun φ : Points K A ↦ (⟨ker φ, inferInstance⟩ : MaximalSpectrum A))
    fun _ _ h ↦ eq_of_ker_eq (MaximalSpectrum.ext_iff.mp h)

variable {B : Type*} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

lemma ker_proj (ψ : Points K B) : ker (proj A B ψ) = (ker ψ).comap (algebraMap A B) := by
  ext; simp [mem_ker]

lemma toPrimeSpectrum_proj (ψ : Points K B) :
    toPrimeSpectrum (proj A B ψ) = PrimeSpectrum.comap (algebraMap A B) (toPrimeSpectrum ψ) :=
  PrimeSpectrum.ext (ker_proj ψ)

/-- XII.3.2 (vi), affine case, one direction: if `B` is finite over `A`, the fibres of
`Y(K) → X(K)` are finite (the fibre over `φ` is the set of `K`-points of the finite `K`-algebra
`K ⊗_A B`). -/
theorem finite_proj_preimage_of_finite [Module.Finite A B] (φ : Points K A) :
    (proj A B ⁻¹' {φ} : Set (Points K B)).Finite := by
  let : Algebra A K := φ.toRingHom.toAlgebra
  let e := (fiberEquivAlgHom φ).trans (AlgHom.liftEquiv A K B K)
  have : Finite (Points K (K ⊗[A] B)) := inferInstance
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ e.symm)

/-- XII.3.1 (vii), affine case, one direction: if `Spec B → Spec A` is injective, then so is
`Y(K) → X(K)`. -/
theorem injective_proj_of_injective_comap
    (h : Function.Injective (PrimeSpectrum.comap (algebraMap A B))) :
    Function.Injective (proj A B : Points K B → Points K A) := by
  intro ψ₁ ψ₂ e
  have : PrimeSpectrum.comap (algebraMap A B) ⟨ker ψ₁, inferInstance⟩ =
      PrimeSpectrum.comap (algebraMap A B) ⟨ker ψ₂, inferInstance⟩ := by
    ext1
    simp only [PrimeSpectrum.comap_asIdeal, ← ker_proj, e]
  exact eq_of_ker_eq congr($(h this).asIdeal)

end Field

/-! ### The Nullstellensatz -/

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K] {A : Type*} [CommRing A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- Hilbert's Nullstellensatz: every maximal ideal of a `K`-algebra of finite type, `K`
algebraically closed, is the kernel of a `K`-point. -/
lemma exists_ker_eq (m : Ideal A) [m.IsMaximal] : ∃ φ : Points K A, ker φ = m := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType K (A ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let e : K ≃ₐ[K] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨ofAlgHom (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m)), ?_⟩
  ext a
  simp [mem_ker, Ideal.Quotient.eq_zero_iff_mem]

variable (K A) in
/-- XII.1.1: for `A` of finite type over an algebraically closed field `K`, the `K`-points of
`X = Spec A` are the closed points of `X`. -/
def equivMaximalSpectrum : Points K A ≃ MaximalSpectrum A :=
  Equiv.ofBijective (fun φ ↦ ⟨ker φ, inferInstance⟩)
    ⟨fun _ _ h ↦ eq_of_ker_eq (MaximalSpectrum.ext_iff.mp h),
    fun m ↦ have ⟨φ, hφ⟩ := exists_ker_eq (K := K) m.asIdeal; ⟨φ, MaximalSpectrum.ext hφ⟩⟩

variable (K A) in
/-- XII.2.1 (i), affine case: `X` is nonempty if and only if `X(K)` is. -/
theorem nonempty_iff_nontrivial : Nonempty (Points K A) ↔ Nontrivial A := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨0, 1, fun h ↦ by simpa using congr(φ $h)⟩
  · intro
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    exact (exists_ker_eq (K := K) m).nonempty

/-- XII.1.3.1, the Jacobson property used there: a function vanishing at every point of `X(K)`
is nilpotent. -/
lemma isNilpotent_of_forall_apply_eq_zero {a : A} (h : ∀ φ : Points K A, φ a = 0) :
    IsNilpotent a := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  rw [← mem_nilradical, nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson,
    Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨φ, rfl⟩ := exists_ker_eq (K := K) m
  exact mem_ker.mpr (h φ)

omit [Algebra.FiniteType K A] in
/-- XII.5.1, proof of 1), faithfulness: morphisms from an unramified `A`-algebra `C` to an
`A`-algebra `B` of finite type over `K` are determined by their effect on `K`-points. (Two such
morphisms agree modulo the nilradical of `B` by the Nullstellensatz, hence agree since `C` is
unramified.) -/
theorem algHom_ext_of_map_eq {B C : Type*} [CommRing B] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Algebra.FiniteType K B] [CommRing C] [Algebra K C] [Algebra A C]
    [IsScalarTower K A C] [Algebra.FormallyUnramified A C] {f₁ f₂ : C →ₐ[A] B}
    (h : ∀ ψ : Points K B, map (f₁.restrictScalars K) ψ = map (f₂.restrictScalars K) ψ) :
    f₁ = f₂ := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  refine Algebra.FormallyUnramified.ext _ (IsNoetherianRing.isNilpotent_nilradical B) fun c ↦ ?_
  rw [Ideal.Quotient.eq, mem_nilradical]
  refine isNilpotent_of_forall_apply_eq_zero (K := K) fun ψ ↦ ?_
  have := congr($(h ψ) c)
  simp only [map_apply, AlgHom.coe_restrictScalars'] at this
  rw [map_sub, this, sub_self]

variable {B : Type*} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  [Algebra.FiniteType K B]

omit [Algebra.FiniteType K A] in
/-- A closed point of `X` in the image of `Y → X` lifts to a `K`-point of `Y`: the fibre is a
nonempty `K`-scheme of finite type, hence has a `K`-point. -/
theorem exists_proj_eq_of_mem_range {φ : Points K A}
    (h : toPrimeSpectrum φ ∈ range (PrimeSpectrum.comap (algebraMap A B))) :
    ∃ ψ : Points K B, proj A B ψ = φ := by
  obtain ⟨Q, hQ⟩ := h
  let I : Ideal B := (ker φ).map (algebraMap A B)
  have hI : I ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr (by
    rw [← PrimeSpectrum.comap_asIdeal, hQ]; rfl)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    Q.isPrime.ne_top hI)
  have : Algebra.FiniteType K (B ⧸ I) :=
    .of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  obtain ⟨χ⟩ := (nonempty_iff_nontrivial K (B ⧸ I)).mpr inferInstance
  refine ⟨map (Ideal.Quotient.mkₐ K I) χ, ext fun a ↦ ?_⟩
  have hmem : algebraMap A B (a - algebraMap K A (φ a)) ∈ I :=
    Ideal.mem_map_of_mem _ (sub_algebraMap_mem_ker φ a)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, sub_eq_zero,
    ← IsScalarTower.algebraMap_apply] at hmem
  simp only [map_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom']
  rw [hmem]
  change χ (algebraMap K (B ⧸ I) (φ a)) = φ a
  exact apply_algebraMap χ (φ a)

omit [Algebra.FiniteType K A] in
/-- XII.3.2 (i), affine case, direct implication: if `Spec B → Spec A` is surjective, then so is
`Y(K) → X(K)`. -/
theorem surjective_proj_of_surjective_comap
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Function.Surjective (proj A B : Points K B → Points K A) :=
  fun _ ↦ exists_proj_eq_of_mem_range (h _)

/-- In the spectrum of a `K`-algebra of finite type, a constructible set containing every closed
point is everything. -/
lemma eq_univ_of_isConstructible {s : Set (PrimeSpectrum A)} (hs : IsConstructible s)
    (h : ∀ φ : Points K A, toPrimeSpectrum φ ∈ s) : s = univ := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  by_contra hne
  obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem s).mp hne
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hs.compl
  have hx' : x ∈ S.toSet := hS ▸ hx
  obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx'
  have hlc : IsLocallyClosed C.toSet :=
    (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl.isLocallyClosed
  obtain ⟨y, hyC, hy⟩ := nonempty_inter_closedPoints ⟨x, hxC⟩ hlc
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  obtain ⟨φ, hφ⟩ := exists_ker_eq (K := K) y.asIdeal
  have hyS : y ∈ sᶜ := by
    rw [← hS]; exact mem_iUnion₂.mpr ⟨C, hC, hyC⟩
  have hyφ : y = toPrimeSpectrum φ := PrimeSpectrum.ext (by simp [hφ])
  exact hyS (hyφ ▸ h φ)

/-- The Jacobson property used in XII.2.3: two constructible subsets of `X` with the same
`K`-points are equal. -/
lemma eq_of_isConstructible {s t : Set (PrimeSpectrum A)} (hs : IsConstructible s)
    (ht : IsConstructible t) (h : ∀ φ : Points K A, toPrimeSpectrum φ ∈ s ↔ toPrimeSpectrum φ ∈ t) :
    s = t := by
  have := eq_univ_of_isConstructible (K := K) ((hs.inter ht).union (hs.compl.inter ht.compl))
    fun φ ↦ by by_cases hφ : toPrimeSpectrum φ ∈ s <;> simp_all
  ext x
  have hx : x ∈ (s ∩ t) ∪ (sᶜ ∩ tᶜ) := this ▸ mem_univ x
  rcases hx with hx | hx
  · exact iff_of_true hx.1 hx.2
  · exact iff_of_false hx.1 hx.2

/-- XII.3.2 (i), affine case, converse: if `Y(K) → X(K)` is surjective, then so is
`Spec B → Spec A`. The image is constructible (Chevalley) and contains every closed point, hence
is everything (`X` is Jacobson). -/
theorem surjective_comap_of_surjective_proj
    (h : Function.Surjective (proj A B : Points K B → Points K A)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : Algebra.FiniteType A B := .of_restrictScalars_finiteType K A B
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  rw [← range_eq_univ]
  refine eq_univ_of_isConstructible (K := K)
    (PrimeSpectrum.isConstructible_range_comap
      (RingHom.finitePresentation_algebraMap.mpr ‹_›)) fun φ ↦ ?_
  obtain ⟨ψ, rfl⟩ := h φ
  exact ⟨toPrimeSpectrum ψ, (toPrimeSpectrum_proj ψ).symm⟩

/-- XII.3.2 (i), affine case: `Spec B → Spec A` is surjective if and only if `Y(K) → X(K)` is. -/
theorem surjective_proj_iff :
    Function.Surjective (proj A B : Points K B → Points K A) ↔
      Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
  ⟨surjective_comap_of_surjective_proj, surjective_proj_of_surjective_comap⟩

/-- Noether normalization on points: if `A ≠ 0` is of finite type over `K`, there is a finite
surjective morphism `X → 𝔸^s`, which is surjective on `K`-points; and `X` is finite over `K` when
`s = 0`. -/
lemma exists_surjective_to_affineSpace [TopologicalSpace K] [IsTopologicalRing K] [Nontrivial A] :
    ∃ (s : ℕ) (π : Points K A → (Fin s → K)), Continuous π ∧ Function.Surjective π ∧
      (s = 0 → Module.Finite K A) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin s) K
  let _ : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Algebra.IsIntegral P A := ⟨fun x ↦ hint x⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap P A)) := fun p ↦ by
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal A)
      (by
        rw [← RingHom.ker_eq_comap_bot]
        intro x hx
        have hx : g x = g 0 := by rw [map_zero]; exact RingHom.mem_ker.mp hx
        rw [hinj hx]
        exact zero_mem _)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩
  have hπ := surjective_proj_of_surjective_comap (K := K) (A := P) (B := A) hsurj
  have hid : Function.Surjective (AlgHom.id K P) := Function.surjective_id
  have hcoords : Function.Surjective (coords (AlgHom.id K P)) := by
    rw [← range_eq_univ, range_coords hid]
    refine eq_univ_of_forall fun x p hp ↦ ?_
    have : p = 0 := RingHom.mem_ker.mp hp
    rw [this, map_zero]
  refine ⟨s, coords (AlgHom.id K P) ∘ proj P A,
    (continuous_pi fun i ↦ continuous_apply _).comp (continuous_map _), hcoords.comp hπ, ?_⟩
  rintro rfl
  have : Module.Finite K P := .equiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm.toLinearEquiv
  have : Algebra.IsIntegral K A := .trans P
  exact Algebra.IsIntegral.finite

section Compact

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- XII.3.2 (v), XII.3.2 (vi) for `X → Spec K` with `X` affine: `X(K)` is compact if and only if
`X` is finite over `K`, i.e. (for `X` affine) proper over `K`. -/
theorem compactSpace_iff [NoncompactSpace K] : CompactSpace (Points K A) ↔ Module.Finite K A := by
  refine ⟨fun hc ↦ ?_, fun _ ↦ Finite.compactSpace⟩
  cases subsingleton_or_nontrivial A
  · infer_instance
  obtain ⟨s, π, hπc, hπs, h0⟩ := exists_surjective_to_affineSpace (K := K) (A := A)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact h0 rfl
  have hcK : IsCompact (univ : Set K) := by
    have h₁ := isCompact_range hπc
    rw [hπs.range_eq] at h₁
    have h₂ := h₁.image (_root_.continuous_apply (⟨0, hs⟩ : Fin s))
    rwa [image_univ, range_eq_univ.mpr fun c ↦ ⟨fun _ ↦ c, rfl⟩] at h₂
  exact absurd (isCompact_univ_iff.mp hcK) (not_compactSpace_iff.mpr ‹_›)

/-- XII.2.1 (i'), (viii), affine case (compactness form): `X(K)` is finite if and only if `X` is
finite over `K`. -/
theorem finite_iff [NoncompactSpace K] : Finite (Points K A) ↔ Module.Finite K A :=
  ⟨fun _ ↦ compactSpace_iff.mp Finite.compactSpace, fun _ ↦ inferInstance⟩

/-- XII.2.1 (i'), affine case: `X(K)` is discrete if and only if `X` is finite over `K`, i.e.
has dimension `0` (`Module.finite_iff_krullDimLE_zero`). This uses that `K` is second countable
and uncountable, as `ℂ` is. -/
theorem discreteTopology_iff [T2Space K] [SecondCountableTopology K] [Uncountable K] :
    DiscreteTopology (Points K A) ↔ Module.Finite K A := by
  refine ⟨fun hd ↦ ?_, fun _ ↦ inferInstance⟩
  cases subsingleton_or_nontrivial A
  · infer_instance
  obtain ⟨n, e, he⟩ := exists_isClosedEmbedding (K := K) (A := A)
  have : SecondCountableTopology (Points K A) := he.isEmbedding.secondCountableTopology
  have : Countable (Points K A) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨s, π, -, hπs, h0⟩ := exists_surjective_to_affineSpace (K := K) (A := A)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact h0 rfl
  have : Countable (Fin s → K) := hπs.countable
  have hsurj : Function.Surjective fun x : Fin s → K ↦ x ⟨0, hs⟩ := fun c ↦ ⟨fun _ ↦ c, rfl⟩
  have : Countable K := hsurj.countable
  exact absurd ‹Countable K› not_countable

theorem discreteTopology_iff_krullDimLE [T2Space K] [SecondCountableTopology K] [Uncountable K] :
    DiscreteTopology (Points K A) ↔ Ring.KrullDimLE 0 A :=
  discreteTopology_iff.trans (Module.finite_iff_krullDimLE_zero K A)

end Compact

/-! ### Zariski topology and complex topology -/

section Zariski

variable [TopologicalSpace K] [T1Space K]

omit [TopologicalSpace K] [T1Space K] in
lemma range_toPrimeSpectrum :
    range (toPrimeSpectrum (K := K) (A := A)) = closedPoints (PrimeSpectrum A) := by
  ext x
  constructor
  · rintro ⟨φ, rfl⟩
    exact isClosed_toPrimeSpectrum φ
  · intro hx
    have : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
    obtain ⟨φ, hφ⟩ := exists_ker_eq (K := K) x.asIdeal
    exact ⟨φ, PrimeSpectrum.ext hφ⟩

omit [TopologicalSpace K] [T1Space K] in
/-- The `K`-points are dense in `X` (`X` is a Jacobson scheme, EGA IV 10.4.8). -/
lemma denseRange_toPrimeSpectrum : DenseRange (toPrimeSpectrum (K := K) (A := A)) := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  rw [DenseRange, range_toPrimeSpectrum, dense_iff_closure_eq]
  exact closure_closedPoints

/-- XII.2.4, affine case, one direction: if `X(K)` is connected, so is `X`. -/
theorem connectedSpace_of_connectedSpace_points [ConnectedSpace (Points K A)] :
    ConnectedSpace (PrimeSpectrum A) := by
  have h := (isConnected_range (continuous_toPrimeSpectrum (K := K) (A := A))).closure
  rw [denseRange_toPrimeSpectrum.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

/-- XII.2.6, affine case, surjectivity: the map `π₀(X(K)) → π₀(X)` is surjective, since every
connected component of `X` is closed, hence contains a closed point. -/
theorem connectedComponentsMap_surjective :
    Function.Surjective (continuous_toPrimeSpectrum (K := K) (A := A)).connectedComponentsMap := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨x, mem_connectedComponent⟩
    isClosed_connectedComponent.isLocallyClosed
  rw [← range_toPrimeSpectrum (K := K)] at hyc
  obtain ⟨φ, rfl⟩ := hyc
  refine ⟨φ, ?_⟩
  rw [Continuous.connectedComponentsMap_mk]
  exact ConnectedComponents.coe_eq_coe'.mpr hy

omit [IsAlgClosed K] [Algebra.FiniteType K A] in
/-- XII.2.2, the easy inclusion: `closure T(K) ⊆ (closure T)(K)`. -/
lemma closure_preimage_subset (T : Set (PrimeSpectrum A)) :
    closure (toPrimeSpectrum ⁻¹' T : Set (Points K A)) ⊆ toPrimeSpectrum ⁻¹' closure T :=
  continuous_toPrimeSpectrum.closure_preimage_subset T

end Zariski

end AlgClosed

/-! ### Statements over `ℂ` -/

section Complex

universe u

/-- XII.2.2 (statement only), affine case: for a constructible subset `T` of `X = Spec A`, with
`A` of finite type over `ℂ`, the closure of `T(ℂ)` in `X(ℂ)` is the set of `ℂ`-points of the
Zariski closure of `T`. SGA deduces it from the analytic Nullstellensatz. (On the noetherian
space `X`, locally constructible and constructible agree.) -/
def ClosureComparisonStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (T : Set (PrimeSpectrum A)), IsConstructible T →
      closure (toPrimeSpectrum ⁻¹' T : Set (Points ℂ A)) = toPrimeSpectrum ⁻¹' closure T

/-- XII.2.4, affine case: if `X = Spec A` is connected, with `A` of finite type over `ℂ`, then
`X(ℂ)` is connected (proved as `Points.connectedComparison` in `Connected.lean`, without GAGA;
SGA reduces to `X` normal and uses Serre's GAGA connectedness theorem for a normal projective
compactification). The converse is `connectedSpace_of_connectedSpace_points`. -/
def ConnectedComparisonStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A],
    ConnectedSpace (PrimeSpectrum A) → ConnectedSpace (Points ℂ A)

/-- `ℂ` is uncountable. -/
lemma uncountable_complex : Uncountable ℂ :=
  ⟨fun h ↦ not_countable_complex (@Set.countable_univ ℂ h)⟩

variable {A : Type u} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- XII.2.1 (i'), (viii) in dimension `0`, affine case over `ℂ`: `X(ℂ)` is discrete if and only
if `X` has dimension `≤ 0`. -/
theorem discreteTopology_iff_krullDimLE_complex :
    DiscreteTopology (Points ℂ A) ↔ Ring.KrullDimLE 0 A :=
  have := uncountable_complex
  discreteTopology_iff_krullDimLE

/-- XII.2.4, affine case, from `ConnectedComparisonStatement`. -/
theorem connectedSpace_iff (H : ConnectedComparisonStatement.{u}) :
    ConnectedSpace (Points ℂ A) ↔ ConnectedSpace (PrimeSpectrum A) :=
  ⟨fun _ ↦ connectedSpace_of_connectedSpace_points (K := ℂ), H A⟩

lemma isConstructible_closure (T : Set (PrimeSpectrum A)) : IsConstructible (closure T) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  rw [← isConstructible_compl]
  exact (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl

variable (H : ClosureComparisonStatement.{u})
include H

/-- XII.2.3, closed case, from XII.2.2: a constructible subset `T` of `X` is closed if and only if
`T(ℂ)` is closed in `X(ℂ)`. -/
theorem isClosed_iff_of_closureComparison {T : Set (PrimeSpectrum A)} (hT : IsConstructible T) :
    IsClosed T ↔ IsClosed (toPrimeSpectrum ⁻¹' T : Set (Points ℂ A)) := by
  refine ⟨fun h ↦ h.preimage continuous_toPrimeSpectrum, fun h ↦ ?_⟩
  have hc := H A T hT
  rw [h.closure_eq] at hc
  have : closure T = T := eq_of_isConstructible (K := ℂ) (isConstructible_closure T) hT
    fun φ ↦ by rw [← mem_preimage, ← hc, mem_preimage]
  exact this ▸ isClosed_closure

/-- XII.2.3, open case, from XII.2.2. -/
theorem isOpen_iff_of_closureComparison {T : Set (PrimeSpectrum A)} (hT : IsConstructible T) :
    IsOpen T ↔ IsOpen (toPrimeSpectrum ⁻¹' T : Set (Points ℂ A)) := by
  rw [← isClosed_compl_iff, isClosed_iff_of_closureComparison H hT.compl, preimage_compl,
    isClosed_compl_iff]

/-- XII.2.3, dense case, from XII.2.2. -/
theorem dense_iff_of_closureComparison {T : Set (PrimeSpectrum A)} (hT : IsConstructible T) :
    Dense T ↔ Dense (toPrimeSpectrum ⁻¹' T : Set (Points ℂ A)) := by
  rw [dense_iff_closure_eq, dense_iff_closure_eq, H A T hT]
  constructor
  · intro h; rw [h, preimage_univ]
  · intro h
    exact eq_univ_of_isConstructible (K := ℂ) (isConstructible_closure T) fun φ ↦
      (h ▸ mem_univ φ : φ ∈ toPrimeSpectrum ⁻¹' closure T)

/-- XII.3.2 (ii), affine case, from XII.2.2: `Spec B → Spec A` is dominant if and only if
`Y(ℂ) → X(ℂ)` has dense image. -/
theorem denseRange_proj_iff_of_closureComparison {B : Type u} [CommRing B] [Algebra ℂ B]
    [Algebra A B] [IsScalarTower ℂ A B] [Algebra.FiniteType ℂ B] :
    DenseRange (proj A B : Points ℂ B → Points ℂ A) ↔
      DenseRange (PrimeSpectrum.comap (algebraMap A B)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have : Algebra.FiniteType A B := .of_restrictScalars_finiteType ℂ A B
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hT := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr (inferInstance : Algebra.FinitePresentation A B))
  have : toPrimeSpectrum ⁻¹' range (PrimeSpectrum.comap (algebraMap A B)) =
      range (proj A B : Points ℂ B → Points ℂ A) := by
    ext φ
    refine ⟨exists_proj_eq_of_mem_range, ?_⟩
    rintro ⟨ψ, rfl⟩
    exact ⟨_, (toPrimeSpectrum_proj ψ).symm⟩
  rw [DenseRange, DenseRange, dense_iff_of_closureComparison H hT, this]

end Complex

end Points

end SGA.SGA1.ExposeXII
