/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatResidueExtensionRealize
import SGA.Foundations.CommAlg.FlatResidueExtensionPBasis
import SGA.Foundations.CommAlg.FlatResidueExtensionColimit
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Realizing a purely inseparable residue field extension

EGA 0_III 10.3.1, purely inseparable step (Bourbaki, *Algèbre commutative* IX, Appendice;
`p`-bases: EGA 0_IV 21.4, Matsumura §26): let `A` be a local ring, `K` a field of characteristic
`p > 0` and `φ : k → K` a map from the residue field of `A` such that `K` is purely inseparable
over `E₀ = φ(k)`: every `y ∈ K` has `y^{pⁿ} ∈ E₀` for some `n`. Then `K` is realized over
`(A, φ)` (`IsLocalRing.realizes_top_of_forall_pow_mem`).

## Construction

Let `E n = {y | y^{pⁿ} ∈ E₀}`; then `E n ⊆ E (n+1)`, `E (n+1)^p ⊆ E n` and `K = ⋃ E n`. Choose a
relative `p`-basis `S` of `E (n+1)` over `E n` (`PBasis.exists_bijective_evalRoots`): the map
`E n [Y_s] / (Y_s^p - s^p) → E (n+1)`, `Y_s ↦ s`, is bijective. Starting from `R₀ = A`, put
`R_{n+1} = R_n[Y_s] / (Y_s^p - l_s)` with `l_s ∈ R_n` lifting `s^p ∈ E n` (`AdjoinRoots`). Each
`R_{n+1}` is free over `R_n`, local with maximal ideal `𝔪_A R_{n+1}` and residue field `E (n+1)`
(`InseparableGonflement.step_good`); the colimit of the `R_n`
(`IsLocalRing.SeqColimit`) realizes `K`.
-/

universe u

open IsLocalRing MvPolynomial AdjoinRoots

noncomputable section

namespace IsLocalRing.InseparableGonflement

/-- A stage of the tower: an `A`-algebra `R` with a ring map `R → K`. -/
structure Stage (A : Type u) [CommRing A] (K : Type u) [Field K] where
  /-- The ring of the stage. -/
  R : Type u
  [commRing : CommRing R]
  [algebra : Algebra A R]
  /-- Its map to `K`. -/
  π : R →+* K

attribute [instance] Stage.commRing Stage.algebra

/-- A stage is *good* at level `E` (relative to `φ : k → K`): `R` is flat over `A`, the map
`π : R → K` extends `φ`, has kernel `𝔪_A R` and image `E`, and every element not killed by `π` is
a unit (so `R` is local with maximal ideal `𝔪_A R` and residue field `E`). -/
structure Stage.Good {A : Type u} [CommRing A] [IsLocalRing A] {K : Type u} [Field K]
    (s : Stage A K) (φ : ResidueField A →+* K) (E : Subfield K) : Prop where
  flat : Module.Flat A s.R
  compat : ∀ a : A, s.π (algebraMap A s.R a) = φ (residue A a)
  ker : RingHom.ker s.π = (maximalIdeal A).map (algebraMap A s.R)
  range : ∀ y, y ∈ E ↔ ∃ x, s.π x = y
  isUnit : ∀ x, s.π x ≠ 0 → IsUnit x

/-- The result of a step: the next stage and an `A`-algebra map to it compatible with the maps
to `K`. -/
structure StepData {A : Type u} [CommRing A] {K : Type u} [Field K] (s : Stage A K) where
  /-- The next stage. -/
  next : Stage A K
  /-- The transition map. -/
  map : s.R →ₐ[A] next.R
  compat : ∀ x, next.π (map x) = s.π x

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `E n = {y ∈ K | y^{pⁿ} ∈ E₀}`. -/
def level (E₀ : Subfield K) (n : ℕ) : Subfield K := E₀.comap (iterateFrobenius K p n)

variable {p}

lemma mem_level {E₀ : Subfield K} {n : ℕ} {y : K} : y ∈ level p E₀ n ↔ y ^ p ^ n ∈ E₀ := by
  rw [level, Subfield.mem_comap, iterateFrobenius_def]

lemma level_zero (E₀ : Subfield K) : level p E₀ 0 = E₀ := by
  ext y
  simp [mem_level]

lemma level_mono (E₀ : Subfield K) (n : ℕ) : level p E₀ n ≤ level p E₀ (n + 1) := fun y hy ↦ by
  rw [mem_level] at hy ⊢
  rw [pow_succ, pow_mul]
  exact pow_mem hy p

lemma pow_mem_level (E₀ : Subfield K) {n : ℕ} {y : K} (hy : y ∈ level p E₀ (n + 1)) :
    y ^ p ∈ level p E₀ n := by
  rw [mem_level] at hy ⊢
  rwa [← pow_mul, ← pow_succ']

variable {A : Type u} [CommRing A] [IsLocalRing A]

variable (A) in
/-- The base stage `A → k → K`. -/
def base (φ : ResidueField A →+* K) : Stage A K :=
  { R := A, algebra := Algebra.id A, π := φ.comp (residue A) }

lemma base_good (φ : ResidueField A →+* K) : (base A φ).Good φ φ.fieldRange where
  flat := inferInstanceAs (Module.Flat A A)
  compat _ := rfl
  ker := by
    change RingHom.ker (φ.comp (residue A)) = (maximalIdeal A).map (RingHom.id A)
    rw [Ideal.map_id, RingHom.ker_comp_of_injective _ φ.injective, ker_residue]
  range y := by
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := residue_surjective z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨residue A x, rfl⟩
  isUnit := fun (x : A) hx ↦ by
    by_contra hnu
    apply hx
    change φ (residue A x) = 0
    rw [(residue_eq_zero_iff x).mpr ((mem_maximalIdeal x).mpr hnu), map_zero]

section Step

variable (φ : ResidueField A →+* K) (E₀ : Subfield K) (n : ℕ) (s : Stage A K)
  (hs : s.Good φ (level p E₀ n))

/-- The inclusion `E n → E (n+1)`. -/
abbrev ψ : level p E₀ n →+* level p E₀ (n + 1) := Subfield.inclusion (level_mono E₀ n)

/-- `y ↦ y^p`, from `E (n+1)` to `E n`. -/
abbrev frobDown (y : level p E₀ (n + 1)) : level p E₀ n := ⟨(y : K) ^ p, pow_mem_level E₀ y.2⟩

lemma ψ_frobDown (y : level p E₀ (n + 1)) : ψ E₀ n (frobDown E₀ n y) = y ^ p ^ 1 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_one]; rfl)

/-- A relative `p`-basis of `E (n+1)` over `E n`. -/
def basisSet : Set (level p E₀ (n + 1)) :=
  (PBasis.exists_bijective_evalRoots p (ψ E₀ n) (frobDown E₀ n) (ψ_frobDown E₀ n)
    (Fact.out : p.Prime)).choose

lemma bijective_basisSet :
    Function.Bijective (PBasis.evalRoots p (ψ E₀ n) (frobDown E₀ n) (ψ_frobDown E₀ n)
      (basisSet E₀ n)) :=
  (PBasis.exists_bijective_evalRoots p (ψ E₀ n) (frobDown E₀ n) (ψ_frobDown E₀ n)
    (Fact.out : p.Prime)).choose_spec

include hs in
lemma exists_lift (t : basisSet E₀ n) : ∃ x, s.π x = ((frobDown E₀ n t.1 : level p E₀ n) : K) :=
  (hs.range _).mp (frobDown E₀ n t.1).2

/-- Lifts `l_s ∈ R_n` of `s^p ∈ E n`. -/
def lifts (t : basisSet E₀ n) : s.R := (exists_lift φ E₀ n s hs t).choose

lemma π_lifts (t : basisSet E₀ n) :
    s.π (lifts φ E₀ n s hs t) = ((t : level p E₀ (n + 1)) : K) ^ p :=
  (exists_lift φ E₀ n s hs t).choose_spec

/-- The next ring `R_n[Y_s] / (Y_s^p - l_s)`. -/
abbrev NextRing : Type u := AdjoinRoots (p ^ 1) (lifts φ E₀ n s hs)

/-- The map `R_{n+1} → K`, extending `π_n` by `Y_s ↦ s`. -/
def nextπ : NextRing φ E₀ n s hs →+* K :=
  Ideal.Quotient.lift _ (eval₂Hom s.π fun t : basisSet E₀ n ↦ ((t : level p E₀ (n + 1)) : K))
    fun z hz ↦ by
      have : ideal (p ^ 1) (lifts φ E₀ n s hs) ≤
          RingHom.ker (eval₂Hom s.π fun t : basisSet E₀ n ↦ ((t : level p E₀ (n + 1)) : K)) := by
        rw [ideal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [π_lifts]
      exact this hz

lemma nextπ_mk (P : MvPolynomial (basisSet E₀ n) s.R) :
    nextπ φ E₀ n s hs (mk _ _ P) =
      eval₂ s.π (fun t : basisSet E₀ n ↦ ((t : level p E₀ (n + 1)) : K)) P := rfl

/-- The step of the tower. -/
def step : StepData s where
  next := { R := NextRing φ E₀ n s hs, π := nextπ φ E₀ n s hs }
  map := IsScalarTower.toAlgHom A s.R (NextRing φ E₀ n s hs)
  compat x := by
    change nextπ φ E₀ n s hs (algebraMap s.R _ x) = s.π x
    rw [← AlgHom.commutes (mk _ _), nextπ_mk, algebraMap_eq, eval₂_C]

/-- `π_n`, with values in `E n`. -/
def πBar : s.R →+* level p E₀ n := s.π.codRestrict _ fun x ↦ (hs.range _).mpr ⟨x, rfl⟩

lemma ψ_πBar_lifts (t : basisSet E₀ n) :
    ψ E₀ n (πBar φ E₀ n s hs (lifts φ E₀ n s hs t)) = t ^ p ^ 1 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_one]; exact π_lifts φ E₀ n s hs t)

/-- `π_{n+1}` factors as `R_{n+1} → E n [Y_s] / (Y_s^p - s^p) ≅ E (n+1) ⊆ K`. -/
lemma nextπ_eq (z : NextRing φ E₀ n s hs) :
    nextπ φ E₀ n s hs z = ((PBasis.evalRootsOf p (ψ E₀ n) (basisSet E₀ n)
      (fun t ↦ πBar φ E₀ n s hs (lifts φ E₀ n s hs t)) (ψ_πBar_lifts φ E₀ n s hs)
        (AdjoinRoots.map (lifts φ E₀ n s hs) (πBar φ E₀ n s hs) z) : level p E₀ (n + 1)) :
          K) := by
  obtain ⟨P, rfl⟩ := mk_surjective _ _ z
  rw [AdjoinRoots.map_mk, PBasis.evalRootsOf_mk, nextπ_mk]
  induction P using MvPolynomial.induction_on with
  | C c => simp only [eval₂_C, MvPolynomial.map_C]; rfl
  | add P Q hP hQ => simp only [eval₂_add, map_add, Subfield.coe_add, hP, hQ]
  | mul_X P i hP => simp only [eval₂_mul, eval₂_X, map_mul, MvPolynomial.map_X,
      Subfield.coe_mul, hP]

lemma step_good : (step φ E₀ n s hs).next.Good φ (level p E₀ (n + 1)) := by
  have hbij := PBasis.bijective_evalRootsOf p (ψ E₀ n) (frobDown E₀ n) (ψ_frobDown E₀ n)
    (bijective_basisSet E₀ n) _ (ψ_πBar_lifts φ E₀ n s hs)
  have hπBar : Function.Surjective (πBar φ E₀ n s hs) := fun y ↦ by
    obtain ⟨x, hx⟩ := (hs.range _).mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hkerBar : RingHom.ker (πBar φ E₀ n s hs) = (maximalIdeal A).map (algebraMap A s.R) := by
    rw [← hs.ker]
    ext x
    simp only [RingHom.mem_ker]
    exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  have hkerN : RingHom.ker (nextπ φ E₀ n s hs) =
      (maximalIdeal A).map (algebraMap A (NextRing φ E₀ n s hs)) := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker, nextπ_eq] at hz
      have h0 : AdjoinRoots.map (lifts φ E₀ n s hs) (πBar φ E₀ n s hs) z = 0 :=
        (injective_iff_map_eq_zero _).mp hbij.1 _ (Subtype.ext hz)
      have := mem_map_ker_of_map_eq_zero (lifts φ E₀ n s hs) (πBar φ E₀ n s hs)
        (pow_pos (Fact.out : p.Prime).pos 1) h0
      rwa [hkerBar, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, IsScalarTower.algebraMap_apply A s.R]
      have : nextπ φ E₀ n s hs (algebraMap s.R _ (algebraMap A s.R r)) =
          s.π (algebraMap A s.R r) := (step φ E₀ n s hs).compat _
      rw [this, ← RingHom.mem_ker, hs.ker]
      exact Ideal.mem_map_of_mem _ hr
  -- every maximal ideal of `R_{n+1}` contains `𝔪_A R_{n+1}`; hence the units
  have hint : Algebra.IsIntegral s.R (NextRing φ E₀ n s hs) :=
    AdjoinRoots.isIntegral _ (pow_pos (Fact.out : p.Prime).pos 1)
  have hmaxs : ∀ I : Ideal s.R, I.IsMaximal → I = RingHom.ker s.π := by
    intro I hI
    refine hI.eq_of_le (RingHom.ker_ne_top _) fun x hx ↦ ?_
    by_contra hx'
    exact hI.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (hs.isUnit x hx'))
  have hrange : ∀ y, y ∈ level p E₀ (n + 1) ↔ ∃ x, nextπ φ E₀ n s hs x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := hbij.2 ⟨y, hy⟩
      obtain ⟨z, rfl⟩ :=
        AdjoinRoots.map_surjective (lifts φ E₀ n s hs) (πBar φ E₀ n s hs) hπBar w
      exact ⟨z, by rw [nextπ_eq, hw]⟩
    · rintro ⟨x, rfl⟩
      rw [nextπ_eq]
      exact Subtype.prop _
  have hmaxN : (RingHom.ker (nextπ φ E₀ n s hs)).IsMaximal := by
    let π'' : NextRing φ E₀ n s hs →+* level p E₀ (n + 1) :=
      (nextπ φ E₀ n s hs).codRestrict _ fun x ↦ (hrange _).mpr ⟨x, rfl⟩
    have hsurj : Function.Surjective π'' := fun y ↦ by
      obtain ⟨x, hx⟩ := (hrange y).mp y.2
      exact ⟨x, Subtype.ext hx⟩
    have hk : RingHom.ker π'' = RingHom.ker (nextπ φ E₀ n s hs) := by
      ext x
      simp only [RingHom.mem_ker]
      exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
    rw [← hk]
    exact RingHom.ker_isMaximal_of_surjective π'' hsurj
  refine ⟨?_, fun a ↦ ?_, hkerN, hrange, fun (z : NextRing φ E₀ n s hs) hz ↦ ?_⟩
  · have := hs.flat
    have := AdjoinRoots.flat (lifts φ E₀ n s hs) (pow_pos (Fact.out : p.Prime).pos 1)
    exact Module.Flat.trans A s.R (NextRing φ E₀ n s hs)
  · change nextπ φ E₀ n s hs (algebraMap A (NextRing φ E₀ n s hs) a) = φ (residue A a)
    rw [IsScalarTower.algebraMap_apply A s.R]
    have : nextπ φ E₀ n s hs (algebraMap s.R _ (algebraMap A s.R a)) =
        s.π (algebraMap A s.R a) := (step φ E₀ n s hs).compat _
    rw [this, hs.compat]
  · by_contra hnu
    obtain ⟨M, hM, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {z})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hc := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := s.R) M
    have hc' : M.comap (algebraMap s.R (NextRing φ E₀ n s hs)) = RingHom.ker s.π := hmaxs _ hc
    have hle : RingHom.ker (nextπ φ E₀ n s hs) ≤ M := by
      rw [hkerN, IsScalarTower.algebraMap_eq A s.R, ← Ideal.map_map, ← hs.ker,
        Ideal.map_le_iff_le_comap, hc']
    have hMeq := hmaxN.eq_of_le hM.ne_top hle
    apply hz
    change nextπ φ E₀ n s hs z = 0
    rw [← RingHom.mem_ker (f := nextπ φ E₀ n s hs), hMeq]
    exact hzM (Ideal.mem_span_singleton_self z)

end Step

/-! ### The tower and its colimit -/

variable (p) in
/-- The tower of stages `R_n`, good at level `E n`. -/
def tower (φ : ResidueField A →+* K) :
    (n : ℕ) → {s : Stage A K // s.Good φ (level p φ.fieldRange n)}
  | 0 => ⟨base A φ, by rw [level_zero]; exact base_good φ⟩
  | n + 1 => ⟨(step φ φ.fieldRange n (tower φ n).1 (tower φ n).2).next,
      step_good φ φ.fieldRange n (tower φ n).1 (tower φ n).2⟩

variable (p) in
/-- The rings of the tower. -/
abbrev G (φ : ResidueField A →+* K) (n : ℕ) : Type u := (tower p φ n).1.R

variable (p) in
/-- The transition maps of the tower. -/
def f (φ : ResidueField A →+* K) (n : ℕ) : G p φ n →ₐ[A] G p φ (n + 1) :=
  (step φ φ.fieldRange n (tower p φ n).1 (tower p φ n).2).map

lemma π_f (φ : ResidueField A →+* K) (n : ℕ) (x : G p φ n) :
    (tower p φ (n + 1)).1.π (f p φ n x) = (tower p φ n).1.π x :=
  (step φ φ.fieldRange n (tower p φ n).1 (tower p φ n).2).compat x

end IsLocalRing.InseparableGonflement

namespace IsLocalRing

open InseparableGonflement

/-- EGA 0_III 10.3.1, purely inseparable case: let `A` be a local ring, `K` a field of
characteristic `p > 0` and `φ : k → K` a ring map from the residue field of `A` such that every
`y ∈ K` has `y^{pⁿ} ∈ φ(k)` for some `n`. Then `K` is realized over `(A, φ)`: there is a local
`A`-algebra `C`, flat over `A`, with `𝔪_A C = 𝔪_C`, and an isomorphism of its residue field onto
`K` extending `φ` (the colimit of the tower `InseparableGonflement.tower`). -/
theorem realizes_top_of_forall_pow_mem (A : Type u) [CommRing A] [IsLocalRing A] {K : Type u}
    [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : ResidueField A →+* K)
    (h : ∀ y : K, ∃ n, y ^ p ^ n ∈ φ.fieldRange) : Realizes A φ ⊤ := by
  let π : ∀ n, G p φ n →+* K := fun n ↦ (tower p φ n).1.π
  have hπ : ∀ n x, π (n + 1) (f p φ n x) = π n x := π_f φ
  have hker : ∀ n, RingHom.ker (π n) = (maximalIdeal A).map (algebraMap A (G p φ n)) :=
    fun n ↦ (tower p φ n).2.ker
  have hunit : ∀ n (x : G p φ n), π n x ≠ 0 → IsUnit x := fun n ↦ (tower p φ n).2.isUnit
  let C := SeqColimit.Colim (G p φ) (f p φ)
  let _ : IsLocalRing C := SeqColimit.isLocalRing hπ hker hunit
  have hmC := SeqColimit.maximalIdeal_eq hπ hker hunit
  let ℓ := SeqColimit.lift (G p φ) (f p φ) π hπ
  have hℓker : RingHom.ker ℓ = maximalIdeal C := by
    rw [SeqColimit.ker_lift hπ hker, hmC]
  have : IsLocalHom ℓ := ⟨fun c hc ↦ by
    by_contra hnu
    have : c ∈ RingHom.ker ℓ := hℓker ▸ (mem_maximalIdeal c).mpr hnu
    exact hc.ne_zero this⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance,
    SeqColimit.flat _ _ fun n ↦ (tower p φ n).2.flat, hmC.symm, ResidueField.lift ℓ,
    fun a ↦ ?_, ?_⟩
  · rw [ResidueField.lift_residue_apply, SeqColimit.algebraMap_colim _ _ 0, RingHom.comp_apply,
      SeqColimit.lift_ofStage]
    exact (tower p φ 0).2.compat a
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨n, hn⟩ := h y
    obtain ⟨x, hx⟩ := ((tower p φ n).2.range y).mp (mem_level.mpr hn)
    exact ⟨residue C (SeqColimit.ofStage _ _ n x), by
      rw [ResidueField.lift_residue_apply, SeqColimit.lift_ofStage]
      exact hx⟩

end IsLocalRing
