/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import SGA.Foundations.Dimension.QuasiFinite
import SGA.Foundations.Dimension.LocalDimension

/-!
# Dimension of the fibres of an algebra of finite type

For an `R`-algebra `S` and a prime `q` of `S`, `PrimeSpectrum.fiberDimAt R q` is the dimension at
`q` of the fibre of `Spec S → Spec R` through `q` (EGA IV §13.1).

* `PrimeSpectrum.fiberDimAt_eq`: for `S` of finite type over `R`, it is the height plus the
  coheight of `q` in the fibre.
* `PrimeSpectrum.fiberDimAt_le_of_quasiFinite`: if `S` is quasi-finite over a polynomial ring
  `R[t₁, …, tₙ]`, all fibres of `Spec S → Spec R` have dimension `≤ n` at every point.
* `Algebra.quasiFiniteAt_of_isIntegral_fiberMap`: if `κ(p) ⊗ P → κ(p) ⊗ T` is integral, then `T`
  is quasi-finite over `P` at the primes over `p`.
* `PrimeSpectrum.exists_quasiFiniteAt_mvPolynomial` (relative normalization at a point, the
  "normalization lemma" of SGA 1 II.2.3): if `m = dim_q` of the fibre through `q`, there are
  `s ∉ q` and `R[t₁, …, tₘ] → S_s` quasi-finite at `q`.
* `PrimeSpectrum.isOpen_setOf_fiberDimAt_le`: **Chevalley's semicontinuity theorem**, the fibre
  dimension is upper semicontinuous on `Spec S` (EGA IV 13.1.3; Stacks Project, Tag 02FZ).

The proof of the normalization lemma: choose a basic open `D(1 ⊗ s)` of the fibre on which it has
dimension `m` everywhere, apply Noether normalization to the fibre of `S_s`, clear denominators
to get `R[t₁, …, tₘ] → S_s` whose fibre over `p` is finite, deduce quasi-finiteness at `q` (the
fibre over the image of `q` in `R[t]` is an antichain, hence discrete), and spread it out by
openness of the quasi-finite locus (Zariski's main theorem, in mathlib).
-/

open Order PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace PrimeSpectrum

variable (R) in
/-- The dimension at `q` of the fibre of `Spec S → Spec R` through `q` (EGA IV §13.1). -/
noncomputable def fiberDimAt (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  topologicalKrullDimAt (comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) q}) ⟨q, rfl⟩

/-- For `S` of finite type over `R`, the dimension of the fibre at `q` is the height plus the
coheight of `q` in the fibre (the fibre being ordered by inclusion of primes). -/
theorem fiberDimAt_eq [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    fiberDimAt R q = ((height (⟨q, rfl⟩ : comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) q}) +
      coheight (⟨q, rfl⟩ : comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) q}) : ℕ∞) :
        WithBot ℕ∞) := by
  set p := comap (algebraMap R S) q
  rw [fiberDimAt, ← (preimageHomeomorphFiber R S p).topologicalKrullDimAt_eq,
    Algebra.FiniteType.topologicalKrullDimAt_eq p.asIdeal.ResidueField,
    ← height_orderIso (preimageOrderIsoFiber R S p),
    ← coheight_orderIso (preimageOrderIsoFiber R S p)]
  rfl

/-- In the fibre over `p` of `R → R[t₁, …, tₙ]`, every point `x` has `ht x + coht x = n`. -/
theorem height_add_coheight_preimage_mvPolynomial {n : ℕ} (p : PrimeSpectrum R)
    (x : comap (algebraMap R (MvPolynomial (Fin n) R)) ⁻¹' {p}) :
    height x + coheight x = n := by
  let e := (preimageOrderIsoFiber R (MvPolynomial (Fin n) R) p).trans
    (comapEquiv (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField).toRingEquiv)
  rw [← height_orderIso e, ← coheight_orderIso e]
  exact MvPolynomial.height_add_coheight_eq _

/-- If `S` is of finite type over `R` and quasi-finite over `R[t₁, …, tₙ]`, then all fibres of
`Spec S → Spec R` have dimension at most `n` at every point (EGA IV §13.1). -/
theorem fiberDimAt_le_of_quasiFinite {n : ℕ} [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite (MvPolynomial (Fin n) R) S] (q : PrimeSpectrum S) :
    fiberDimAt R q ≤ n := by
  set P := MvPolynomial (Fin n) R
  set p := comap (algebraMap R S) q
  have hc : ∀ Q ∈ comap (algebraMap R S) ⁻¹' {p},
      comap (algebraMap P S) Q ∈ comap (algebraMap R P) ⁻¹' {p} := by
    intro Q hQ
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hQ ⊢
    rw [← hQ, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq]
  let c : comap (algebraMap R S) ⁻¹' {p} → comap (algebraMap R P) ⁻¹' {p} :=
    fun Q ↦ ⟨comap (algebraMap P S) Q, hc Q Q.2⟩
  have hc : StrictMono c := fun _ _ h ↦ comap_strictMono_of_quasiFinite (R := P) h
  have h := height_add_coheight_preimage_mvPolynomial p (c ⟨q, rfl⟩)
  rw [fiberDimAt_eq]
  calc _ ≤ ((height (c ⟨q, rfl⟩) + coheight (c ⟨q, rfl⟩) : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (add_le_add (height_le_height_apply_of_strictMono c hc _)
          (coheight_le_coheight_apply_of_strictMono c hc _))
    _ = n := by rw [h]; rfl

end PrimeSpectrum

section QuasiFiniteAt

open Algebra.TensorProduct

variable {P T : Type*} [CommRing P] [CommRing T] [Algebra R P] [Algebra P T] [Algebra R T]
  [IsScalarTower R P T]

/-- The map of fibres over `p` induced by `P → T`, as a `κ(p)`-algebra map. -/
noncomputable abbrev fiberMap (p : Ideal R) [p.IsPrime] : p.Fiber P →ₐ[p.ResidueField] p.Fiber T :=
  map (AlgHom.id p.ResidueField p.ResidueField) (IsScalarTower.toAlgHom R P T)

/-- If the map of fibres `κ(p) ⊗ P → κ(p) ⊗ T` over `p` is integral and `T` is of finite type
over `P`, then `T` is quasi-finite over `P` at every prime lying over `p`. -/
theorem Algebra.quasiFiniteAt_of_isIntegral_fiberMap [Algebra.FiniteType P T]
    (pp : PrimeSpectrum R) (hΨ : (fiberMap (P := P) (T := T) pp.asIdeal).toRingHom.IsIntegral)
    (x : PrimeSpectrum T) (hx : comap (algebraMap R T) x = pp) :
    Algebra.QuasiFiniteAt P x.asIdeal := by
  set P₀ := comap (algebraMap P T) x
  set p := pp.asIdeal
  -- the fibres over `p` of `Spec T` and `Spec P`
  set eT := preimageOrderIsoFiber R T pp
  set eP := preimageOrderIsoFiber R P pp
  have hover : ∀ y : PrimeSpectrum T, comap (algebraMap P T) y = P₀ →
      y ∈ comap (algebraMap R T) ⁻¹' {pp} := by
    intro y hy
    have h1 : comap (algebraMap R T) y = comap (algebraMap R P) P₀ := by
      rw [← hy, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq]
    have h2 : comap (algebraMap R P) P₀ = pp := by
      rw [← comap_comp_apply, ← IsScalarTower.algebraMap_eq, hx]
    simp [h1, h2]
  -- compatibility of the fibre map with contraction
  have hcompat : ∀ z : PrimeSpectrum (p.Fiber T),
      (eP.symm (comap (fiberMap (P := P) (T := T) p).toRingHom z) : PrimeSpectrum P) =
        comap (algebraMap P T) (eT.symm z) := by
    intro z
    ext1
    change Ideal.comap _ (Ideal.comap _ z.asIdeal) = Ideal.comap _ (Ideal.comap _ z.asIdeal)
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  -- the fibre of `Spec T → Spec P` over `P₀` is an antichain
  have hanti : ∀ y₁ y₂ : PrimeSpectrum T, comap (algebraMap P T) y₁ = P₀ →
      comap (algebraMap P T) y₂ = P₀ → y₁ ≤ y₂ → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂ hle
    let z₁ := eT ⟨y₁, hover y₁ h₁⟩
    let z₂ := eT ⟨y₂, hover y₂ h₂⟩
    have hz : z₁ ≤ z₂ := eT.monotone hle
    have hc : comap (fiberMap (P := P) (T := T) p).toRingHom z₁ =
        comap (fiberMap (P := P) (T := T) p).toRingHom z₂ := by
      apply eP.symm.injective
      ext1
      rw [hcompat, hcompat]
      simp only [z₁, z₂, OrderIso.symm_apply_apply]
      rw [h₁, h₂]
    by_contra hne
    have hlt : z₁ < z₂ := lt_of_le_of_ne hz fun h ↦ hne
      (congrArg Subtype.val (eT.injective h))
    algebraize [(fiberMap (P := P) (T := T) p).toRingHom]
    exact (comap_strictMono_of_isIntegral (R := p.Fiber P) hlt).ne hc
  -- hence `x` is isolated in its fibre over `P₀`
  rw [Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber x]
  set e := preimageOrderIsoFiber P T P₀
  have : IsNoetherianRing (P₀.asIdeal.Fiber T) :=
    Algebra.FiniteType.isNoetherianRing P₀.asIdeal.ResidueField _
  have : IsJacobsonRing (P₀.asIdeal.Fiber T) :=
    isJacobsonRing_of_finiteType (A := P₀.asIdeal.ResidueField)
  set w := e ⟨x, rfl⟩
  have hw : IsOpen {w} := by
    have key := (isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing w).out 3 1
    refine key.mp ⟨?_, ?_⟩
    · rw [isClosed_singleton_iff_isMaximal, ← isMax_iff]
      intro v hv
      have hle : (⟨x, rfl⟩ : comap (algebraMap P T) ⁻¹' {P₀}) ≤ e.symm v := by
        rw [← e.le_iff_le, e.apply_symm_apply]
        exact hv
      have := hanti x (e.symm v) rfl (e.symm v).2 hle
      have hv' : e.symm v = ⟨x, rfl⟩ := Subtype.ext this.symm
      rw [← e.apply_symm_apply v, hv']
    · intro a b hba ha
      rw [Set.mem_singleton_iff] at ha ⊢
      subst ha
      rw [← le_iff_specializes] at hba
      have hle : e.symm b ≤ (⟨x, rfl⟩ : comap (algebraMap P T) ⁻¹' {P₀}) := by
        rw [← e.le_iff_le, e.apply_symm_apply]
        exact hba
      have := hanti (e.symm b) x (e.symm b).2 rfl hle
      have hb : e.symm b = ⟨x, rfl⟩ := Subtype.ext this
      rw [← e.apply_symm_apply b, hb]
  have h := hw.preimage (preimageHomeomorphFiber P T P₀).continuous
  convert h using 1
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact ⟨fun hy ↦ hy ▸ rfl, fun hy ↦ e.injective hy⟩

/-- The quasi-finite locus is open (a consequence of Zariski's main theorem, in mathlib): if `T`
is of finite type over `P` and quasi-finite at `q`, then `T_g` is quasi-finite over `P` for some
`g ∉ q`. -/
theorem Algebra.QuasiFiniteAt.exists_notMem_quasiFinite [Algebra.FiniteType P T] (q : Ideal T)
    [q.IsPrime] [Algebra.QuasiFiniteAt P q] :
    ∃ g ∉ q, Algebra.QuasiFinite P (Localization.Away g) := by
  obtain ⟨S', hS', r, hrq, H⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := P) q
  have : Module.Finite P S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite P (Localization.Away r) := .trans _ S' _
  exact ⟨r.1, hrq, .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2⟩

end QuasiFiniteAt

namespace PrimeSpectrum

variable {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- If `Spec T → Spec S` is an open embedding (e.g. `T` is a localization `S_g`), the dimension of
the fibres over `Spec R` at a point of `Spec T` and at its image in `Spec S` agree. -/
theorem fiberDimAt_comap_of_isOpenEmbedding (h : Topology.IsOpenEmbedding (comap (algebraMap S T)))
    (Q : PrimeSpectrum T) :
    fiberDimAt R (comap (algebraMap S T) Q) = fiberDimAt R Q := by
  set φ := comap (algebraMap S T)
  set F := comap (algebraMap R S) ⁻¹' {comap (algebraMap R S) (φ Q)}
  have hcomp : comap (algebraMap R T) = (comap (algebraMap R S)).comp φ := by
    rw [IsScalarTower.algebraMap_eq R S T, comap_comp]
  have hset : comap (algebraMap R T) ⁻¹' {comap (algebraMap R T) Q} = φ ⁻¹' F := by
    ext y
    simp [F, hcomp]
  let ι := (F.restrictPreimage φ) ∘ (Homeomorph.setCongr hset)
  have hι : Topology.IsOpenEmbedding ι :=
    (Set.restrictPreimage_isOpenEmbedding F h).comp (Homeomorph.setCongr hset).isOpenEmbedding
  have := hι.topologicalKrullDimAt_eq ⟨Q, rfl⟩
  exact this

end PrimeSpectrum

namespace PrimeSpectrum

open Algebra.TensorProduct

/-- **Relative normalization at a point** (EGA IV §13.1; the
"normalization lemma" invoked in SGA 1 II.2.3): if `S` is of finite type over `R`, `q` a prime of
`S` and `m` the dimension at `q` of the fibre through `q`, there are `s ∉ q` and an `R`-algebra map
`R[t₁, …, tₘ] → S_s` which is quasi-finite at `q`. -/
theorem exists_quasiFiniteAt_mvPolynomial [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    ∃ (m : ℕ) (_ : fiberDimAt R q = m) (s : S) (_ : s ∉ q.asIdeal)
      (ψ : MvPolynomial (Fin m) R →ₐ[R] Localization.Away s)
      (Q : PrimeSpectrum (Localization.Away s)) (_ : comap (algebraMap S _) Q = q),
      letI := ψ.toRingHom.toAlgebra
      Algebra.QuasiFiniteAt (MvPolynomial (Fin m) R) Q.asIdeal := by
  set pp := comap (algebraMap R S) q
  set κ := pp.asIdeal.ResidueField
  set eS := preimageOrderIsoFiber R S pp
  set q' := eS ⟨q, rfl⟩
  have hq : q.asIdeal = q'.asIdeal.comap (includeRight : S →ₐ[R] pp.asIdeal.Fiber S) := by
    have := congrArg (fun y ↦ (Subtype.val y).asIdeal) (eS.symm_apply_apply ⟨q, rfl⟩)
    exact this.symm
  -- a basic open `D(1 ⊗ s)` of the fibre on which the fibre has dimension `dim_q`
  obtain ⟨f, ⟨s, rfl⟩, hfq, hdim⟩ := Algebra.FiniteType.exists_mem_ringKrullDim_localization_away_eq
    κ q' (MonoidHom.mrange (includeRight : S →ₐ[R] pp.asIdeal.Fiber S).toRingHom.toMonoidHom)
    (fun p' hp' hpq ↦ by
      obtain ⟨a, hap, haq⟩ := SetLike.not_le_iff_exists.mp hpq
      obtain ⟨r, hr, t, hrt⟩ := Ideal.Fiber.exists_smul_eq_one_tmul pp.asIdeal a
      refine ⟨1 ⊗ₜ t, ⟨t, rfl⟩, ?_, ?_⟩
      · rw [← hrt, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hap
      · rw [← hrt, Algebra.smul_def]
        intro h
        rcases q'.isPrime.mem_or_mem h with h | h
        · exact hr ((Ideal.mem_of_liesOver q'.asIdeal pp.asIdeal r).mpr h)
        · exact haq h)
  change (includeRight s : pp.asIdeal.Fiber S) ∉ q'.asIdeal at hfq
  change ringKrullDim (Localization.Away (includeRight s : pp.asIdeal.Fiber S)) = _ at hdim
  have hsq : s ∉ q.asIdeal := by
    rw [hq]
    exact hfq
  set T := Localization.Away s
  -- the fibre of `S_s` over `p` is the localization of the fibre of `S` at `1 ⊗ s`
  have : IsLocalization ((Submonoid.powers s).map (includeRight : S →ₐ[R] pp.asIdeal.Fiber S))
      (Localization.Away (includeRight s : pp.asIdeal.Fiber S)) := by
    rw [Submonoid.map_powers]
    infer_instance
  let ε := IsLocalization.tensorProductEquivOfMapIncludeRight R κ (Submonoid.powers s) T
    (Localization.Away (includeRight s : pp.asIdeal.Fiber S))
  have hdimB : ringKrullDim (pp.asIdeal.Fiber T) = ↑(height q' + coheight q') := by
    rw [ringKrullDim_eq_of_ringEquiv ε.toRingEquiv, hdim]
  have : Nontrivial (pp.asIdeal.Fiber T) := by
    rw [← zero_le_ringKrullDim_iff_nontrivial, hdimB]
    exact WithBot.coe_le_coe.mpr zero_le
  -- Noether normalization of the fibre of `S_s`
  obtain ⟨m, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg κ (pp.asIdeal.Fiber T)
  have hφint : φ.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hφfin
  have hm := Algebra.FiniteType.ringKrullDim_eq_of_isIntegral_mvPolynomial κ hφinj hφint
  have hfib : fiberDimAt R q = m := by
    rw [fiberDimAt_eq, ← hm, hdimB, ← height_orderIso eS, ← coheight_orderIso eS]
  refine ⟨m, hfib, s, hsq, ?_⟩
  -- clear denominators in the images of the variables
  have hex : ∀ i : Fin m, ∃ r ∉ pp.asIdeal, ∃ y : T, r • φ (MvPolynomial.X i) = 1 ⊗ₜ[R] y :=
    fun i ↦ Ideal.Fiber.exists_smul_eq_one_tmul pp.asIdeal (φ (MvPolynomial.X i))
  choose r hr y hy using hex
  let ψ : MvPolynomial (Fin m) R →ₐ[R] T := MvPolynomial.aeval y
  obtain ⟨Q, hQ⟩ : q ∈ Set.range (comap (algebraMap S T)) := by
    rw [localization_away_comap_range T s]
    exact hsq
  refine ⟨ψ, Q, hQ, ?_⟩
  let := ψ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin m) R) T := .of_algebraMap_eq' ψ.comp_algebraMap.symm
  have : Algebra.FiniteType (MvPolynomial (Fin m) R) T :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin m) R) T
  refine Algebra.quasiFiniteAt_of_isIntegral_fiberMap pp ?_ Q ?_
  · let θ : MvPolynomial (Fin m) κ →ₐ[κ] pp.asIdeal.Fiber (MvPolynomial (Fin m) R) :=
      MvPolynomial.aeval fun i ↦ (algebraMap R κ (r i))⁻¹ • (1 ⊗ₜ MvPolynomial.X i)
    have hθ : (fiberMap (P := MvPolynomial (Fin m) R) (T := T) pp.asIdeal).comp θ = φ := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      have hri : algebraMap R κ (r i) ≠ 0 := fun h ↦
        hr i (Ideal.algebraMap_residueField_eq_zero.mp h)
      simp only [AlgHom.comp_apply, θ, MvPolynomial.aeval_X, map_smul]
      rw [fiberMap, map_tmul]
      change (algebraMap R κ (r i))⁻¹ • (1 ⊗ₜ[R] ψ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, ← hy i, ← algebraMap_smul κ (r i), smul_smul,
        inv_mul_cancel₀ hri, one_smul]
    have h : ((fiberMap (P := MvPolynomial (Fin m) R) (T := T) pp.asIdeal).comp
        θ).toRingHom.IsIntegral := hθ ▸ hφint
    exact RingHom.IsIntegral.tower_top θ.toRingHom _ h
  · rw [IsScalarTower.algebraMap_eq R S T, comap_comp_apply, hQ]

/-- Every point `q` of `Spec S`, for `S` of finite type over `R`, has an open neighbourhood on
which the dimension of the fibres of `Spec S → Spec R` is at most its value at `q`. -/
theorem exists_isOpen_forall_fiberDimAt_le [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    ∃ U : Set (PrimeSpectrum S), IsOpen U ∧ q ∈ U ∧
      ∀ q₁ ∈ U, fiberDimAt R q₁ ≤ fiberDimAt R q := by
  obtain ⟨m, hm, s, hs, ψ, Q, hQ, hQF⟩ := exists_quasiFiniteAt_mvPolynomial (R := R) q
  set T := Localization.Away s
  let := ψ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin m) R) T := .of_algebraMap_eq' ψ.comp_algebraMap.symm
  have : Algebra.FiniteType (MvPolynomial (Fin m) R) T :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin m) R) T
  obtain ⟨g, hg, hQF'⟩ :=
    Algebra.QuasiFiniteAt.exists_notMem_quasiFinite (P := MvPolynomial (Fin m) R) Q.asIdeal
  set T' := Localization.Away g
  have : Algebra.FiniteType R T' := .trans (S := T) inferInstance inferInstance
  refine ⟨comap (algebraMap S T) '' Set.range (comap (algebraMap T T')), ?_, ?_, ?_⟩
  · exact (localization_away_isOpenEmbedding T s).isOpenMap _
      (localization_away_isOpenEmbedding T' g).isOpen_range
  · obtain ⟨Q', hQ'⟩ : Q ∈ Set.range (comap (algebraMap T T')) := by
      rw [localization_away_comap_range T' g]
      exact hg
    exact ⟨Q, ⟨Q', hQ'⟩, hQ⟩
  · rintro _ ⟨_, ⟨Q₁, rfl⟩, rfl⟩
    rw [fiberDimAt_comap_of_isOpenEmbedding (localization_away_isOpenEmbedding T s),
      fiberDimAt_comap_of_isOpenEmbedding (localization_away_isOpenEmbedding T' g), hm]
    exact fiberDimAt_le_of_quasiFinite Q₁

/-- **Chevalley's semicontinuity theorem** (EGA IV 13.1.3; Stacks Project, Tag 02FZ): for `S` of
finite type over `R`, the dimension of the fibres of `Spec S → Spec R`,
`q ↦ dim_q (Spec S ×_{Spec R} {q ∩ R})`, is upper semicontinuous. -/
theorem isOpen_setOf_fiberDimAt_le [Algebra.FiniteType R S] (n : WithBot ℕ∞) :
    IsOpen {q : PrimeSpectrum S | fiberDimAt R q ≤ n} := by
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  obtain ⟨U, hU, hqU, hle⟩ := exists_isOpen_forall_fiberDimAt_le (R := R) q
  exact ⟨U, fun q₁ hq₁ ↦ (hle q₁ hq₁).trans hq, hU, hqU⟩

end PrimeSpectrum
