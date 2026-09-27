/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import SGA.Foundations.HenselianFinite

/-!
# Quasi-finite algebras over a henselian local ring

Let `A` be a henselian local ring.

* `HenselianLocalRing.of_ringEquiv`: being henselian is invariant under ring isomorphisms.
* `HenselianLocalRing.exists_isIdempotentElem_forall_le_of_finite`: a finite `A`-algebra splits
  off its local factor at a maximal ideal (Stacks 04GG (10)).
* `HenselianLocalRing.exists_notMem_forall_le_and_finite`: if `S` is an `A`-algebra of finite
  type, quasi-finite at a prime `q` over `𝔪_A`, the generizations of `q` form an open subset
  `D(e)` of `Spec S` with `S_e` finite over `A` (Stacks 04GG (13), 04GJ; EGA IV 18.5.11,
  18.12.1). The proof combines Zariski's main theorem (mathlib's
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) with the splitting of
  finite algebras.
* `AlgebraicGeometry.exists_opens_forall_specializes_isFinite_of_quasiFiniteAt`: the scheme
  version. For `g : Y ⟶ Spec A` locally of finite type and quasi-finite at a point `y` of the
  closed fibre, some open neighbourhood `W` of `y` consists of generizations of `y` and is finite
  over `Spec A` (`exists_opens_forall_specializes_isFinite_of_henselian`: the same when the closed
  fibre is finite).

These generalize the complete noetherian case of `SGA.Foundations.CompleteLocalQuasiFinite`.
-/

open CategoryTheory IsLocalRing Polynomial Topology

universe u

namespace HenselianLocalRing

/-- Being a henselian local ring is invariant under ring isomorphisms. -/
theorem of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [HenselianLocalRing A]
    (e : A ≃+* B) : HenselianLocalRing B := by
  have : Nontrivial B := e.symm.toEquiv.nontrivial
  have : IsLocalRing B := .of_surjective' e.toRingHom e.surjective
  refine ⟨fun f hf b₀ h₁ h₂ ↦ ?_⟩
  have hmap (x : B) : x ∈ maximalIdeal B ↔ e.symm x ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff e.symm x]
  have heval (p : B[X]) (x : B) :
      (p.map (e.symm : B →+* A)).eval (e.symm x) = e.symm (p.eval x) := by
    rw [eval_map]
    exact eval₂_at_apply _ _
  obtain ⟨a, ha, ha₀⟩ := HenselianLocalRing.is_henselian (f.map (e.symm : B →+* A))
    (hf.map _) (e.symm b₀) (by rw [heval, ← hmap]; exact h₁) (by
      rw [derivative_map, heval]
      exact h₂.map (e.symm : B →+* A))
  refine ⟨e a, ?_, ?_⟩
  · have : e.symm (f.eval (e a)) = 0 := by
      rw [← heval, e.symm_apply_apply]
      exact ha
    simpa using this
  · rw [hmap, map_sub, e.symm_apply_apply]
    exact ha₀

/-- A nonzero quotient of a henselian local ring is henselian (Stacks 04GH). -/
theorem of_surjective {A B : Type*} [CommRing A] [CommRing B] [HenselianLocalRing A]
    [Nontrivial B] (f : A →+* B) (hf : Function.Surjective f) : HenselianLocalRing B := by
  have : IsLocalRing B := .of_surjective' f hf
  have : IsLocalHom f := .of_surjective f hf
  refine ⟨fun p hp b₀ h₁ h₂ ↦ ?_⟩
  obtain ⟨q, hqp, -, hq⟩ := lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hf p) hp
  obtain ⟨a₀, rfl⟩ := hf b₀
  have heval (r : A[X]) (x : A) : (r.map f).eval (f x) = f (r.eval x) := by
    rw [eval_map]
    exact eval₂_at_apply _ _
  have hq₁ : q.eval a₀ ∈ maximalIdeal A := by
    have : f (q.eval a₀) ∈ maximalIdeal B := by rw [← heval, hqp]; exact h₁
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu ↦ this (hu.map f)
  have hq₂ : IsUnit (q.derivative.eval a₀) := isUnit_of_map_unit f _ (by
    rw [← heval, ← derivative_map, hqp]; exact h₂)
  obtain ⟨a, ha, ha₀⟩ := HenselianLocalRing.is_henselian q hq a₀ hq₁ hq₂
  refine ⟨f a, ?_, ?_⟩
  · change p.eval (f a) = 0
    rw [← hqp, heval, ha.eq_zero, map_zero]
  · have : a - a₀ ∈ maximalIdeal A := ha₀
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    rw [← map_sub]
    exact fun hu ↦ this (isUnit_of_map_unit f _ hu)

/-- A local ring which is henselian at its maximal ideal is a henselian local ring. -/
theorem of_henselianRing (A : Type*) [CommRing A] [IsLocalRing A]
    [HenselianRing A (maximalIdeal A)] : HenselianLocalRing A where
  is_henselian f hf a₀ h₁ h₂ := HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

variable {A : Type u} [CommRing A] [HenselianLocalRing A]

/-- Over a henselian local ring `A`, a finite `A`-algebra `T` splits off the local factor at a
maximal ideal `q`: there is an idempotent `e ∉ q` such that every prime of `T` not containing `e`
is contained in `q` (Stacks 04GG (10)). -/
theorem exists_isIdempotentElem_forall_le_of_finite (T : Type*) [CommRing T] [Algebra A T]
    [Module.Finite A T] (q : Ideal T) [q.IsMaximal] :
    ∃ e : T, IsIdempotentElem e ∧ e ∉ q ∧ ∀ P : Ideal T, P.IsPrime → e ∉ P → P ≤ q := by
  have hover (n : Ideal T) (hn : n.IsMaximal) : n.comap (algebraMap A T) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)
  obtain ⟨e, he, hiff⟩ := exists_isIdempotentElem_notMem_iff (A := A) (B := T)
    ⟨q, inferInstance⟩ (hover q inferInstance)
  have heq : e ∉ q := (hiff ⟨q, inferInstance⟩ (hover q inferInstance)).mpr rfl
  refine ⟨e, he, heq, fun P hP heP ↦ ?_⟩
  obtain ⟨n, hn, hPn⟩ := P.exists_le_maximal hP.ne_top
  by_cases hnq : n = q
  · exact hnq ▸ hPn
  · have hen : e ∈ n := by
      by_contra h
      have := (hiff ⟨n, hn.isPrime⟩ (hover n hn)).mp h
      exact hnq (congrArg PrimeSpectrum.asIdeal this)
    have h1e : 1 - e ∈ P := (hP.mem_or_mem (show e * (1 - e) ∈ P by
      rw [mul_sub, mul_one, he.eq, sub_self]; exact P.zero_mem)).resolve_left heP
    exact absurd (n.eq_top_of_isUnit_mem (by simpa using n.add_mem hen (hPn h1e))
      isUnit_one) hn.ne_top

/-- Over a henselian local ring `A`, let `S` be an `A`-algebra of finite type and `q` a prime of
`S` over the maximal ideal of `A` at which `S` is quasi-finite. Then there is `e ∈ S`, `e ∉ q`,
such that every prime of `S` not containing `e` is contained in `q` and the localization `S_e` is
finite over `A`. Geometrically: the generizations of `q` form the open subset `D(e) = Spec S_e`,
which is finite over `A` (Stacks 04GG (13) and 04GJ, EGA IV 18.5.11 and 18.12.1). -/
theorem exists_notMem_forall_le_and_finite {S : Type u} [CommRing S] [Algebra A S]
    [Algebra.FiniteType A S] (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal A)]
    [Algebra.QuasiFiniteAt A q] :
    ∃ e : S, e ∉ q ∧ (∀ P : Ideal S, P.IsPrime → e ∉ P → P ≤ q) ∧
      ∀ (L : Type u) [CommRing L] [Algebra S L] [IsLocalization.Away e L] [Algebra A L]
        [IsScalarTower A S L], Module.Finite A L := by
  classical
  obtain ⟨S', hS', r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q
  have : Module.Finite A S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  let q' : Ideal S' := q.comap S'.val
  have hq' : q'.IsMaximal := by
    have : (q'.comap (algebraMap A S')).IsMaximal := by
      rw [show q'.comap (algebraMap A S') = maximalIdeal A from
        (Ideal.over_def q (maximalIdeal A)).symm]
      infer_instance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q' this
  obtain ⟨e, he, heq', hle⟩ := exists_isIdempotentElem_forall_le_of_finite (A := A) S' q'
  -- `r` is invertible on `D(e)`
  obtain ⟨r', hr'⟩ : ∃ r' : S', r * r' * e = e := by
    have htop : Ideal.span {r, 1 - e} = ⊤ := by
      by_contra h
      obtain ⟨n, hn, hle'⟩ := Ideal.exists_le_maximal _ h
      have h1e : 1 - e ∈ n := hle' (Ideal.subset_span (by simp))
      have hen : e ∉ n := fun h ↦ hn.ne_top
        (n.eq_top_of_isUnit_mem (by simpa using n.add_mem h h1e) isUnit_one)
      exact hrq (hle n hn.isPrime hen (hle' (Ideal.subset_span (by simp))))
    obtain ⟨a, b, hab⟩ : ∃ a b : S', a * r + b * (1 - e) = 1 := by
      have := htop.ge (Submodule.mem_top (x := 1))
      rw [Ideal.span_insert, Submodule.mem_sup] at this
      obtain ⟨x, hx, y, hy, hxy⟩ := this
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, b, hxy⟩
    refine ⟨a, ?_⟩
    have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    linear_combination e * hab - b * this
  set E : S := e.1
  have hE : E * E = E := congrArg Subtype.val he.eq
  have hrE (j : ℕ) : (r.1 * r'.1) ^ j * E = E := by
    induction j with
    | zero => simp
    | succ j ih =>
      have : r.1 * r'.1 * E = E := congrArg Subtype.val hr'
      rw [pow_succ, mul_assoc, this, ih]
  -- `e S ⊆ S'`
  have key (s : S) : ∃ t : S', E * s = E * t := by
    obtain ⟨x, hx⟩ := hbij.2 (algebraMap S (Localization.Away r.1) s)
    obtain ⟨⟨t, _, m, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
    have hx' : algebraMap S (Localization.Away r.1) t.1 =
        algebraMap S (Localization.Away r.1) (s * r.1 ^ m) := by
      rw [map_mul, ← IsLocalization.mk'_eq_iff_eq_mul (M := Submonoid.powers r.1)
        (y := ⟨r.1 ^ m, m, rfl⟩), ← hx]
      simp only [Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_mk']
      rfl
    rw [IsLocalization.eq_iff_exists (Submonoid.powers r.1)] at hx'
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hx'
    refine ⟨r' ^ m * t, ?_⟩
    have h1 := hrE (k + m)
    have h2 := hrE k
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    linear_combination -(r'.1 ^ (k + m) * E) * hk - s * h1 + (r'.1 ^ m * t.1) * h2
  refine ⟨E, heq', fun P hP hEP ↦ ?_, fun L _ _ _ _ _ ↦ ?_⟩
  · intro s hs
    obtain ⟨t, ht⟩ := key s
    have htP : t ∈ P.comap S'.val := by
      have : E * t ∈ P := ht ▸ Ideal.mul_mem_left _ _ hs
      exact (hP.mem_or_mem this).resolve_left hEP
    have := hle (P.comap S'.val) (Ideal.comap_isPrime _ _) hEP htP
    have : E * s ∈ q := ht ▸ Ideal.mul_mem_left _ _ this
    exact ((inferInstance : q.IsPrime).mem_or_mem this).resolve_left heq'
  · have hunit : IsUnit (algebraMap S L E) := IsLocalization.Away.algebraMap_isUnit E
    have h1 : algebraMap S L E = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (by
        rw [IsIdempotentElem, ← map_mul, hE])
    let f : S' →ₗ[A] L := (IsScalarTower.toAlgHom A S L).toLinearMap ∘ₗ S'.val.toLinearMap
    refine Module.Finite.of_surjective f fun l ↦ ?_
    obtain ⟨⟨s, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers E) l
    obtain ⟨t, ht⟩ := key s
    refine ⟨e * t, ?_⟩
    simp only [f, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Subalgebra.coe_val, Subalgebra.coe_mul, IsScalarTower.coe_toAlgHom']
    rw [← ht, eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_mul]
    simp [h1]

end HenselianLocalRing

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be a henselian local ring and `g : Y ⟶ Spec A` locally of finite type, quasi-finite at
a point `y` of the closed fibre. Then `y` has an open neighbourhood `W`, all of whose points
specialize to `y`, which is finite over `Spec A` (Stacks 04GG (13), 04GJ). -/
theorem exists_opens_forall_specializes_isFinite_of_quasiFiniteAt {A : Type u} [CommRing A]
    [HenselianLocalRing A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [LocallyOfFiniteType g]
    {y : Y} (hy : g y = closedPoint A) (hqf : g.QuasiFiniteAt y) :
    ∃ W : Y.Opens, y ∈ W ∧ (∀ z ∈ W, z ⤳ y) ∧ IsFinite (W.ι ≫ g) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU := isAffineOpen_top (Spec (.of A))
  have hVU : V ≤ g ⁻¹ᵁ ⊤ := by simp
  -- the base ring `Γ(Spec A, ⊤) ≅ A` is henselian local
  let e₀ : A ≃+* Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have : HenselianLocalRing Γ(Spec (.of A), ⊤) := HenselianLocalRing.of_ringEquiv e₀
  let : Algebra Γ(Spec (.of A), ⊤) Γ(Y, V) := (g.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of A), ⊤) Γ(Y, V) := g.finiteType_appLE hU hV hVU
  let q := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have : Algebra.QuasiFiniteAt Γ(Spec (.of A), ⊤) q := hqf.quasiFiniteAt hV hU hVU hyV
  have : q.LiesOver (maximalIdeal Γ(Spec (.of A), ⊤)) := by
    constructor
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := g) ⊤ hU V hV hVU hyV
    have hmax : (hU.primeIdealOf ⟨g y, hVU hyV⟩).asIdeal.IsMaximal :=
      hU.primeIdealOf_isMaximal_of_isClosed _ (by rw [hy]; exact isClosed_singleton_closedPoint A)
    rw [Ideal.under, ← eq_maximalIdeal hmax, ← h]
    rfl
  obtain ⟨e, heq, hle, hfin'⟩ :=
    HenselianLocalRing.exists_notMem_forall_le_and_finite (A := Γ(Spec (.of A), ⊤)) q
  have hmem (z : Y) (hz : z ∈ V) :
      z ∈ Y.basicOpen e ↔ e ∉ (hV.primeIdealOf ⟨z, hz⟩).asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← hV.fromSpec_preimage_basicOpen,
      SetLike.mem_coe, Scheme.Hom.mem_preimage, hV.fromSpec_primeIdealOf]
  have hWV : Y.basicOpen e ≤ V := Y.basicOpen_le e
  have hW := hV.basicOpen e
  refine ⟨Y.basicOpen e, (hmem y hyV).mpr heq, fun z hz ↦ ?_, ?_⟩
  · have hzV := hWV hz
    have hP := hle _ (hV.primeIdealOf ⟨z, hzV⟩).isPrime ((hmem z hzV).mp hz)
    have := ((PrimeSpectrum.le_iff_specializes _ _).mp hP).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
  · have hWU : Y.basicOpen e ≤ g ⁻¹ᵁ ⊤ := by simp
    let : Algebra Γ(Spec (.of A), ⊤) Γ(Y, Y.basicOpen e) :=
      (g.appLE ⊤ (Y.basicOpen e) hWU).hom.toAlgebra
    have : IsScalarTower Γ(Spec (.of A), ⊤) Γ(Y, V) Γ(Y, Y.basicOpen e) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change (g.appLE ⊤ (Y.basicOpen e) hWU).hom x =
          (Y.presheaf.map (homOfLE hWV).op).hom ((g.appLE ⊤ V hVU).hom x)
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have := hV.isLocalization_basicOpen e
    have hfinite : (g.appLE ⊤ (Y.basicOpen e) hWU).hom.Finite := hfin' _
    have : IsFinite (Spec.map (g.appLE ⊤ (Y.basicOpen e) hWU)) :=
      (IsFinite.SpecMap_iff _).mpr hfinite
    rw [← hW.isoSpec_hom_fromSpec_assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec g hU hW hWU,
      IsAffineOpen.fromSpec_top]
    infer_instance

/-- Let `A` be a henselian local ring and `g : Y ⟶ Spec A` locally of finite type with finite
closed fibre. Every point `y` of the closed fibre has an open neighbourhood `W`, all of whose
points specialize to `y`, which is finite over `Spec A` (Stacks 04GG (13), 04GJ). -/
theorem exists_opens_forall_specializes_isFinite_of_henselian {A : Type u} [CommRing A]
    [HenselianLocalRing A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [LocallyOfFiniteType g]
    {y : Y} (hy : g y = closedPoint A) (hfin : (g ⁻¹' {closedPoint A}).Finite) :
    ∃ W : Y.Opens, y ∈ W ∧ (∀ z ∈ W, z ⤳ y) ∧ IsFinite (W.ι ≫ g) := by
  refine exists_opens_forall_specializes_isFinite_of_quasiFiniteAt g hy ?_
  have : Finite (g ⁻¹' {g y}) := by rw [hy]; exact hfin.to_subtype
  have : Finite (g.fiber (g y)) := (g.fiberHomeo (g y)).finite_iff.mpr ‹_›
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end AlgebraicGeometry
