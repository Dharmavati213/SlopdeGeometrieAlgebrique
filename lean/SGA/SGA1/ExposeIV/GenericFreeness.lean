/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Generic freeness

SGA 1 IV.6.7 (Grothendieck's generic freeness, Stacks 051R, EGA IV 6.9.2): let `A` be a
noetherian domain, `B` a finitely generated `A`-algebra and `M` a finite `B`-module. Then there
is `f ≠ 0` in `A` such that `M_f` is a free `A_f`-module.

The proof is by induction on the number of generators of `B`, through the following steps.

* `IsFreeAway f M`: there is a map `φ : F → M` from a free `A`-module whose kernel and
  cokernel are killed by powers of `f`; it implies that `M_f` is free over `A_f`, and it is
  preserved when `f` is replaced by a multiple.
* `isFreeAway_of_filtration`: if `M` has an exhaustive increasing filtration whose successive
  quotients are free after inverting `f`, so is `M`.
* The case of a finite `A`-module, by choosing elements forming a basis over the fraction field.
* The inductive step: a finite module over `R[X]` is filtered by the `R`-submodules
  `N₀ + X N₀ + ⋯ + Xʲ N₀`, whose successive quotients are quotients `N₀ / Lⱼ` of the finite
  `R`-module `N₀` by an increasing, hence eventually constant, chain of submodules.
-/

universe u v

namespace SGA.SGA1.ExposeIV

open Module

variable {A : Type u} [CommRing A]

section IsFreeAway

/-- `M` becomes free after inverting `f`, in the following strong sense: there is a linear map
from a free module to `M` whose kernel and cokernel are killed by powers of `f`. -/
def IsFreeAway (f : A) (M : Type v) [AddCommGroup M] [Module A M] : Prop :=
  ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module A F) (_ : Module.Free A F)
    (φ : F →ₗ[A] M),
    (∀ x, φ x = 0 → ∃ n : ℕ, f ^ n • x = 0) ∧ ∀ m, ∃ n : ℕ, f ^ n • m ∈ LinearMap.range φ

variable {f : A} {M M' : Type v} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

lemma IsFreeAway.of_linearEquiv (h : IsFreeAway f M) (e : M ≃ₗ[A] M') : IsFreeAway f M' := by
  obtain ⟨F, _, _, _, φ, hker, hcoker⟩ := h
  refine ⟨F, _, _, inferInstance, e.toLinearMap ∘ₗ φ, fun x hx ↦ hker x ?_, fun m ↦ ?_⟩
  · simpa using hx
  · obtain ⟨n, x, hx⟩ := hcoker (e.symm m)
    exact ⟨n, x, by simp [hx]⟩

lemma IsFreeAway.mul_right (h : IsFreeAway f M) (g : A) : IsFreeAway (f * g) M := by
  obtain ⟨F, _, _, _, φ, hker, hcoker⟩ := h
  refine ⟨F, _, _, inferInstance, φ, fun x hx ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hker x hx
    exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩
  · obtain ⟨n, hn⟩ := hcoker m
    exact ⟨n, by rw [mul_pow, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hn⟩

lemma IsFreeAway.mul_left (h : IsFreeAway f M) (g : A) : IsFreeAway (g * f) M := by
  rw [mul_comm]; exact h.mul_right g

/-- If `M` is free after inverting `f` in the sense of `IsFreeAway`, then `M_f` is a free
`A_f`-module. -/
theorem IsFreeAway.free_localizedModule (h : IsFreeAway f M) :
    Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨F, _, _, _, φ, hker, hcoker⟩ := h
  let S := Submonoid.powers f
  let φS := LocalizedModule.map S φ
  have hinj : Function.Injective φS := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using LocalizedModule.induction_on with | _ x s
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hx
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hx
    simp only [smul_zero, Submonoid.smul_def] at hk
    obtain ⟨n, hn⟩ := hker (f ^ k • s.1 • x) (by simp [← hk, map_smul])
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨f ^ n * f ^ k, mul_mem (pow_mem (Submonoid.mem_powers f) n)
        (pow_mem (Submonoid.mem_powers f) k)⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hn
  have hsurj : Function.Surjective φS := by
    intro y
    induction y using LocalizedModule.induction_on with | _ m s
    obtain ⟨n, x, hx⟩ := hcoker m
    refine ⟨LocalizedModule.mk x ⟨f ^ n * s.1, mul_mem (pow_mem (Submonoid.mem_powers f) n) s.2⟩,
      ?_⟩
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [hx, mul_smul, smul_comm (f ^ n) (s : A), Submonoid.smul_def]⟩
  have : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.Free.of_equiv
      (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S F)).equiv
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φS ⟨hinj, hsurj⟩)

/-- An exhaustive increasing filtration `0 = N₀ ⊆ N₁ ⊆ ⋯` whose successive quotients are free
after inverting `f` gives a module which is free after inverting `f`. -/
theorem isFreeAway_of_filtration (N : ℕ → Submodule A M) (hN0 : N 0 = ⊥)
    (hmono : Monotone N) (hex : ∀ m, ∃ j, m ∈ N j)
    (h : ∀ j, IsFreeAway f (↥(N (j + 1)) ⧸ Submodule.comap (N (j + 1)).subtype (N j))) :
    IsFreeAway f M := by
  classical
  choose F _ _ _ φ hker hcoker using h
  -- lift `φ j` along `N (j+1) → N (j+1) / N j`
  have hlift (j : ℕ) : ∃ ψ : F j →ₗ[A] N (j + 1), (Submodule.mkQ _) ∘ₗ ψ = φ j :=
    Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)
  choose ψ hψ using hlift
  let Φ : (Π₀ j, F j) →ₗ[A] M := DFinsupp.lsum ℕ fun j ↦ (N (j + 1)).subtype ∘ₗ ψ j
  have hΦ (j : ℕ) (x : F j) : Φ (DFinsupp.single j x) = ψ j x := by
    simp [Φ]
  have hle (k : ℕ) (e : Π₀ j, F j) : (∀ j, k ≤ j → e j = 0) → Φ e ∈ N k := by
    induction e using DFinsupp.induction with
    | h0 => intro _; simp
    | ha i b g hgi hb ih =>
      intro he
      have hik : i < k := by
        by_contra hik
        have := he i (not_lt.1 hik)
        rw [DFinsupp.add_apply, DFinsupp.single_eq_same, hgi, add_zero] at this
        exact hb this
      have hg : ∀ j, k ≤ j → g j = 0 := fun j hj ↦ by
        have := he j hj
        rwa [DFinsupp.add_apply, DFinsupp.single_eq_of_ne (by omega), zero_add] at this
      rw [map_add, hΦ]
      exact add_mem (hmono (Nat.succ_le_of_lt hik) (ψ i b).2) (ih hg)
  refine ⟨Π₀ j, F j, _, _, inferInstance, Φ, ?_, ?_⟩
  · -- the kernel of `Φ` is killed by a power of `f`
    have key (k : ℕ) : ∀ d : Π₀ j, F j, (∀ j, k ≤ j → d j = 0) → Φ d = 0 →
        ∃ n : ℕ, f ^ n • d = 0 := by
      induction k with
      | zero =>
        intro d hd _
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul]
        ext j
        exact hd j (Nat.zero_le j)
      | succ k ih =>
        intro d hd hΦd
        set e := d.erase k
        have hde : d = e + DFinsupp.single k (d k) := (DFinsupp.erase_add_single k d).symm
        have he : ∀ j, k ≤ j → e j = 0 := fun j hj ↦ by
          rcases eq_or_lt_of_le hj with rfl | hj
          · exact DFinsupp.erase_same
          · rw [DFinsupp.erase_ne (by omega)]
            exact hd j hj
        -- the top component is killed by a power of `f`
        have htop : ((ψ k (d k) : N (k + 1)) : M) ∈ N k := by
          have : Φ (DFinsupp.single k (d k)) = -Φ e := by
            rw [eq_neg_iff_add_eq_zero, add_comm, ← map_add, ← hde, hΦd]
          rw [← hΦ, this]
          exact neg_mem (hle k e he)
        obtain ⟨n, hn⟩ := hker k (d k) (by
          rw [← hψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact htop)
        have hdn : f ^ n • d = f ^ n • e := by
          rw [hde, smul_add, ← DFinsupp.single_smul, hn, DFinsupp.single_zero, add_zero]
        have hfe : Φ (f ^ n • e) = 0 := by
          rw [← hdn, map_smul, hΦd, smul_zero]
        obtain ⟨n', hn'⟩ := ih (f ^ n • e) (fun j hj ↦ by
          rw [DFinsupp.smul_apply, he j hj, smul_zero]) hfe
        exact ⟨n' + n, by rw [pow_add, mul_smul, hdn, hn']⟩
    intro d hd
    refine key (d.support.sup id + 1) d (fun j hj ↦ ?_) hd
    by_contra hdj
    have := Finset.le_sup (f := id) (DFinsupp.mem_support_iff.2 hdj)
    simp only [id] at this
    omega
  · -- the cokernel of `Φ` is killed by powers of `f`
    have key (j : ℕ) : ∀ m ∈ N j, ∃ n : ℕ, f ^ n • m ∈ LinearMap.range Φ := by
      induction j with
      | zero =>
        intro m hm
        rw [hN0, Submodule.mem_bot] at hm
        exact ⟨0, by simp [hm]⟩
      | succ j ih =>
        intro m hm
        obtain ⟨n, x, hx⟩ := hcoker j (Submodule.Quotient.mk ⟨m, hm⟩)
        have hmem : f ^ n • m - ψ j x ∈ N j := by
          have : Submodule.mkQ (Submodule.comap (N (j + 1)).subtype (N j))
              (f ^ n • (⟨m, hm⟩ : N (j + 1)) - ψ j x) = 0 := by
            rw [map_sub, ← LinearMap.comp_apply, hψ, hx, map_smul, Submodule.mkQ_apply,
              sub_self]
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
            Submodule.subtype_apply] at this
        obtain ⟨n', hn'⟩ := ih _ hmem
        refine ⟨n' + n, ?_⟩
        have : f ^ (n' + n) • m = f ^ n' • (f ^ n • m - ψ j x) + f ^ n' • (ψ j x : M) := by
          rw [smul_sub, sub_add_cancel, pow_add, mul_smul]
        rw [this]
        exact add_mem hn' (Submodule.smul_mem _ _ ⟨_, hΦ j x⟩)
    intro m
    obtain ⟨j, hj⟩ := hex m
    exact key j m hj

end IsFreeAway

section Base

variable {M : Type v} [AddCommGroup M] [Module A M]

/-- Generic freeness for a finite module over a noetherian domain: after inverting a suitable
`f ≠ 0`, a family of elements of `M` forming a basis over the fraction field becomes a basis. -/
theorem exists_isFreeAway_of_finite [IsDomain A] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧ IsFreeAway f M := by
  classical
  let S := nonZeroDivisors A
  let K := Localization S
  let g := LocalizedModule.mkLinearMap S M
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  -- a subfamily of the generators which is a basis of `M ⊗ K`
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K (g '' s)
  obtain ⟨b', hb', hinj⟩ := Set.exists_image_eq_injOn_of_subset_range
    (hbt.trans (Set.image_subset_range _ _))
  let φ : (b' →₀ A) →ₗ[A] M := Finsupp.linearCombination A Subtype.val
  have hliK : LinearIndependent K (g ∘ (Subtype.val : b' → M)) := by
    let e : b' → b := fun x ↦ ⟨g x, hb' ▸ Set.mem_image_of_mem g x.2⟩
    have he : Function.Injective e := fun x y hxy ↦
      Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
    exact hli.comp e he
  have hliA : LinearIndependent A (g ∘ (Subtype.val : b' → M)) :=
    hliK.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using
      IsFractionRing.injective A K)
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply hliA
    rw [← Finsupp.apply_linearCombination, ← Finsupp.apply_linearCombination]
    exact congrArg g hxy
  -- every generator is in the image after multiplication by a nonzerodivisor
  have hgen : ∀ m ∈ s, ∃ c ∈ S, c • m ∈ LinearMap.range φ := by
    intro m hm
    have hmem : g m ∈ (LinearMap.range φ).localized' K S g := by
      rw [Submodule.localized'_eq_span]
      refine Submodule.span_mono ?_ (hspan ▸ Submodule.subset_span (Set.mem_image_of_mem g hm))
      rw [← hb']
      exact Set.image_mono fun x hx ↦ ⟨Finsupp.single ⟨x, hx⟩ 1, by simp [φ]⟩
    obtain ⟨m', hm', c, hc⟩ := hmem
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hc
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := S) hc
    refine ⟨u * c, mul_mem u.2 c.2, ?_⟩
    rw [mul_smul, ← Submonoid.smul_def u, ← hu]
    exact Submodule.smul_mem _ _ hm'
  choose c hcS hc using hgen
  let f := ∏ m ∈ s.attach, c m.1 m.2
  have hfS : f ∈ S := prod_mem fun m _ ↦ hcS m.1 m.2
  refine ⟨f, nonZeroDivisors.ne_zero hfS, b' →₀ A, _, _, inferInstance, φ,
    fun x hx ↦ ⟨0, by simpa using hφ (hx.trans (map_zero φ).symm)⟩, fun m ↦ ⟨1, ?_⟩⟩
  rw [pow_one]
  have hs' : ∀ m ∈ s, f • m ∈ LinearMap.range φ := fun m hm ↦ by
    rw [show f = (∏ m' ∈ s.attach.erase ⟨m, hm⟩, c m'.1 m'.2) * c m hm from
      (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm, mul_smul]
    exact Submodule.smul_mem _ _ (hc m hm)
  have : (⊤ : Submodule A M) ≤ (LinearMap.range φ).comap (LinearMap.lsmul A M f) := by
    rw [← hs, Submodule.span_le]
    exact fun m hm ↦ hs' m hm
  exact this Submodule.mem_top

end Base

section Step

variable {R : Type*} [CommRing R] [Algebra A R] [IsNoetherianRing R]
  {M : Type v} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]

/-- The inductive step of generic freeness. Let `T` be an `R`-linear endomorphism of `M` and
`N₀` a finite `R`-submodule such that `M` is the union of the `N₀ + T N₀ + ⋯ + T^{j-1} N₀`
(e.g. `M` a finite module over `R[X]` with `T = X`). If generic freeness holds for finite
`R`-modules, it holds for `M`. -/
theorem exists_isFreeAway_of_endomorphism [IsDomain A]
    (IH : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q] [Module R Q] [IsScalarTower A R Q]
      [Module.Finite R Q], ∃ f : A, f ≠ 0 ∧ IsFreeAway f Q)
    (T : M →ₗ[R] M) (N₀ : Submodule R M) (hN₀ : N₀.FG)
    (hex : ∀ m : M, ∃ j, m ∈ (Finset.range j).sup fun i ↦ N₀.map (T ^ i)) :
    ∃ f : A, f ≠ 0 ∧ IsFreeAway f M := by
  classical
  set F : ℕ → Submodule R M := fun j ↦ (Finset.range j).sup fun i ↦ N₀.map (T ^ i) with hF
  have hF0 : F 0 = ⊥ := by simp [hF]
  have hFsucc (j : ℕ) : F (j + 1) = F j ⊔ N₀.map (T ^ j) := by
    simp only [hF, Finset.range_add_one, Finset.sup_insert, sup_comm]
  have hFmono : Monotone F := monotone_nat_of_le_succ fun j ↦ by
    rw [hFsucc]; exact le_sup_left
  have hTF (j : ℕ) : (F j).map T ≤ F (j + 1) := by
    induction j with
    | zero => simp [hF0]
    | succ j ih =>
      rw [hFsucc, Submodule.map_sup, hFsucc (j + 1), ← Submodule.map_comp]
      refine sup_le (ih.trans le_sup_left) (le_of_eq_of_le ?_ le_sup_right)
      rw [pow_succ', Module.End.mul_eq_comp]
  -- the successive quotients are the quotients `N₀ / L j`
  let L (j : ℕ) : Submodule R N₀ := (F j).comap ((T ^ j) ∘ₗ N₀.subtype)
  have hLmono : Monotone L := monotone_nat_of_le_succ fun j n hn ↦ by
    change (T ^ (j + 1)) n ∈ F (j + 1)
    rw [pow_succ', Module.End.mul_apply]
    exact hTF j ⟨_, hn, rfl⟩
  have : IsNoetherian R N₀ := isNoetherian_of_fg_of_noetherian N₀ hN₀
  have : Module.Finite R N₀ := inferInstance
  obtain ⟨J, hJ⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨L, hLmono⟩
  -- generic freeness for the finitely many `N₀ / L i`, `i ≤ J`
  have hIH (i : ℕ) : ∃ f : A, f ≠ 0 ∧ IsFreeAway f (N₀ ⧸ L i) := IH _
  choose g hg0 hg using hIH
  let f := ∏ i ∈ Finset.range (J + 1), g i
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hg0 i
  have hfL (j : ℕ) : IsFreeAway f (N₀ ⧸ L j) := by
    by_cases hj : j ≤ J
    · rw [show f = (∏ i ∈ (Finset.range (J + 1)).erase j, g i) * g j from
        (Finset.prod_erase_mul _ _ (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).symm]
      exact (hg j).mul_left _
    · have : L J = L j := hJ j (le_of_not_ge hj)
      rw [show f = (∏ i ∈ (Finset.range (J + 1)).erase J, g i) * g J from
        (Finset.prod_erase_mul _ _ (Finset.mem_range.2 (Nat.lt_succ_self J))).symm]
      exact ((hg J).mul_left _).of_linearEquiv
        ((Submodule.quotEquivOfEq _ _ this).restrictScalars A)
  -- the filtration by the `A`-submodules `F j`
  let Fa (j : ℕ) : Submodule A M := (F j).restrictScalars A
  refine ⟨f, hf0, isFreeAway_of_filtration Fa (by simp [Fa, hF0])
    (fun i j hij ↦ hFmono hij) hex fun j ↦ ?_⟩
  -- `N₀ → F (j + 1) / F j`, `n ↦ T^j n`, is surjective with kernel `L j`
  let σ : N₀ →ₗ[A] Fa (j + 1) := LinearMap.codRestrict (Fa (j + 1))
    (((T ^ j) ∘ₗ N₀.subtype).restrictScalars A) fun n ↦ by
      change _ ∈ F (j + 1)
      rw [hFsucc]
      exact Submodule.mem_sup_right ⟨n, n.2, rfl⟩
  let π := (Submodule.comap (Fa (j + 1)).subtype (Fa j)).mkQ ∘ₗ σ
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy : (y : M) ∈ F j ⊔ N₀.map (T ^ j) := by rw [← hFsucc]; exact y.2
    obtain ⟨y₁, hy₁, _, ⟨n, hn, rfl⟩, hy⟩ := Submodule.mem_sup.1 hy
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    change ((σ ⟨n, hn⟩ : M) - y) ∈ F j
    simp only [σ, LinearMap.codRestrict_apply, LinearMap.restrictScalars_apply,
      LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hy, sub_add_cancel_right]
    exact neg_mem hy₁
  have hker : LinearMap.ker π = (L j).restrictScalars A := by
    ext n
    simp [π, σ, L, Submodule.Quotient.mk_eq_zero, Fa]
  have h' := (hfL j).of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv A (L j)).symm
  exact h'.of_linearEquiv
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective π hπ))

end Step

section Main

variable [IsDomain A] [IsNoetherianRing A]

/-- Generic freeness for finite modules over polynomial rings `A[X₀, …, X_{n-1}]`. -/
theorem exists_isFreeAway_mvPolynomial (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module A M] [Module (MvPolynomial (Fin n) A) M]
      [IsScalarTower A (MvPolynomial (Fin n) A) M] [Module.Finite (MvPolynomial (Fin n) A) M],
      ∃ f : A, f ≠ 0 ∧ IsFreeAway f M := by
  induction n with
  | zero =>
    intro M _ _ _ _ _
    -- `A[∅] = A`
    have hsurj : Function.Surjective (algebraMap A (MvPolynomial (Fin 0) A)) :=
      MvPolynomial.C_surjective (Fin 0)
    have : Module.Finite A M := by
      obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := MvPolynomial (Fin 0) A) (M := M)
      refine ⟨⟨s, ?_⟩⟩
      rw [← Submodule.restrictScalars_span A _ hsurj, hs, Submodule.restrictScalars_top]
    exact exists_isFreeAway_of_finite
  | succ n ih =>
    intro M _ _ _ _ _
    let P := MvPolynomial (Fin (n + 1)) A
    let R := MvPolynomial (Fin n) A
    let e := MvPolynomial.finSuccEquiv A n
    -- `R → P`, `r ↦ e⁻¹ (C r)`, and the induced `R`-module structure on `M`
    let ψ : R →ₐ[A] P := (e.symm : Polynomial R →ₐ[A] P).comp
      (IsScalarTower.toAlgHom A R (Polynomial R))
    let : Algebra R P := ψ.toRingHom.toAlgebra
    let : Module R M := Module.compHom M ψ.toRingHom
    have : IsScalarTower R P M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun a m ↦ by
      change ψ (algebraMap A R a) • m = a • m
      rw [ψ.commutes, algebraMap_smul]
    let T : M →ₗ[R] M := (LinearMap.lsmul P M (MvPolynomial.X 0)).restrictScalars R
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := P) (M := M)
    let N₀ : Submodule R M := Submodule.span R s
    refine exists_isFreeAway_of_endomorphism (R := R) (fun Q _ _ _ _ _ ↦ ih Q) T N₀
      ⟨s, rfl⟩ fun m ↦ ?_
    -- every element of `M` lies in some `N₀ + X₀ N₀ + ⋯ + X₀^{j-1} N₀`
    set F : ℕ → Submodule R M := fun j ↦ (Finset.range j).sup fun i ↦ N₀.map (T ^ i) with hF
    have hFsucc (j : ℕ) : F (j + 1) = F j ⊔ N₀.map (T ^ j) := by
      simp only [hF, Finset.range_add_one, Finset.sup_insert, sup_comm]
    have hFmono : Monotone F := monotone_nat_of_le_succ fun j ↦ by
      rw [hFsucc]; exact le_sup_left
    have hTF1 (j : ℕ) : (F j).map T ≤ F (j + 1) := by
      induction j with
      | zero => simp [hF]
      | succ j ih =>
        rw [hFsucc, Submodule.map_sup, hFsucc (j + 1), ← Submodule.map_comp]
        refine sup_le (ih.trans le_sup_left) (le_of_eq_of_le ?_ le_sup_right)
        rw [pow_succ', Module.End.mul_eq_comp]
    have hTF (k j : ℕ) : (F j).map (T ^ k) ≤ F (j + k) := by
      induction k with
      | zero => rw [pow_zero, Module.End.one_eq_id, Submodule.map_id]; rfl
      | succ k ih =>
        rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp, ← add_assoc]
        exact (Submodule.map_mono ih).trans (hTF1 _)
    have hTpow (k : ℕ) (m : M) : (T ^ k) m = (MvPolynomial.X 0 : P) ^ k • m := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]
        rfl
    let W : Submodule P M :=
      { carrier := {m | ∃ j, m ∈ F j}
        add_mem' := fun {a b} ⟨i, hi⟩ ⟨j, hj⟩ ↦ ⟨max i j,
          add_mem (hFmono (le_max_left i j) hi) (hFmono (le_max_right i j) hj)⟩
        zero_mem' := ⟨0, zero_mem _⟩
        smul_mem' := fun p m ⟨j, hj⟩ ↦ by
          obtain ⟨q, rfl⟩ := e.symm.surjective p
          induction q using Polynomial.induction_on' with
          | add q₁ q₂ h₁ h₂ =>
            obtain ⟨i₁, hi₁⟩ := h₁
            obtain ⟨i₂, hi₂⟩ := h₂
            refine ⟨max i₁ i₂, ?_⟩
            rw [map_add, add_smul]
            exact add_mem (hFmono (le_max_left _ _) hi₁) (hFmono (le_max_right _ _) hi₂)
          | monomial k r =>
            refine ⟨j + k, ?_⟩
            have hX : e.symm Polynomial.X = MvPolynomial.X 0 := by
              rw [AlgEquiv.symm_apply_eq, MvPolynomial.finSuccEquiv_X_zero]
            have : e.symm (Polynomial.monomial k r) • m = r • (T ^ k) m := by
              rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hX, mul_smul, hTpow]
              rfl
            rw [this]
            exact Submodule.smul_mem _ _ (hTF k j ⟨m, hj, rfl⟩) }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← hs, Submodule.span_le]
      intro m hm
      refine ⟨1, ?_⟩
      rw [hFsucc, pow_zero]
      exact Submodule.mem_sup_right ⟨m, Submodule.subset_span hm, rfl⟩
    have hm : m ∈ W := hW ▸ Submodule.mem_top
    exact hm

/-- Generic freeness, in the form `IsFreeAway`: for a finitely generated algebra `B` over a
noetherian domain `A` and a finite `B`-module `M`, there is `f ≠ 0` such that `M` is free after
inverting `f` (and then also after inverting any multiple of `f`). -/
theorem exists_isFreeAway_of_finiteType {B : Type*} [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (M : Type v) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] : ∃ f : A, f ≠ 0 ∧ IsFreeAway f M := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  let : Algebra (MvPolynomial (Fin n) A) B := π.toRingHom.toAlgebra
  let : Module (MvPolynomial (Fin n) A) M := Module.compHom M π.toRingHom
  have : IsScalarTower (MvPolynomial (Fin n) A) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := IsScalarTower.of_algebraMap_smul fun a m ↦ by
    change π (algebraMap A _ a) • m = a • m
    rw [π.commutes, algebraMap_smul]
  have : Module.Finite (MvPolynomial (Fin n) A) M := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
    refine ⟨⟨s, ?_⟩⟩
    rw [← Submodule.restrictScalars_span _ B hπ, hs, Submodule.restrictScalars_top]
  exact exists_isFreeAway_mvPolynomial n M

/-- IV.6.7 (generic freeness): let `A` be a noetherian integral domain, `B` a finitely generated
`A`-algebra and `M` a finite `B`-module. There is `f ≠ 0` in `A` such that `M_f` is a free
`A_f`-module. -/
theorem exists_free_localizedModule_of_finiteType {B : Type*} [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (M : Type v) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] :
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨f, hf, h⟩ := exists_isFreeAway_of_finiteType (A := A) (B := B) M
  exact ⟨f, hf, h.free_localizedModule⟩

end Main

end SGA.SGA1.ExposeIV
