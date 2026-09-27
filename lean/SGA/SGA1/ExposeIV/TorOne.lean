/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Tensor

/-!
# SGA 1, Exposé IV: vanishing of `Tor₁`

Exposé IV uses `Tor₁^A(M, N)` only through its vanishing. Mathlib has no `Tor` functor on
modules, so we define the predicate `TorOneVanishes A M N` directly: `Tor₁^A(M, N)` is the
kernel of `M ⊗ K → M ⊗ A^(N)`, where `0 → K → A^(N) → N → 0` is the canonical free
presentation of `N`.

The facts of the long exact `Tor` sequence that the exposé uses are proved by hand:

* the vanishing can be tested on any presentation `0 → K → P → N → 0` with `P` flat
  (`torOneVanishes_iff_lTensor_injective`), and then gives injectivity of `M ⊗ K → M ⊗ P` for
  every short exact sequence (`TorOneVanishes.lTensor_injective`);
* `Tor₁` is balanced: it can also be computed from a flat presentation of `M`
  (`torOneVanishes_iff_rTensor_injective`);
* vanishing is stable under extensions (`TorOneVanishes.of_exact`);
* the criteria of the beginning of IV.1: `M` is flat iff `Tor₁^A(M, N) = 0` for all `N`, iff
  `Tor₁^A(M, A/I) = 0` for all ideals `I`, iff `I ⊗ M → M` is injective for all `I`.
-/

universe u v w

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

section Presentation

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
  (N : Type w) [AddCommGroup N] [Module A N]

/-- The canonical surjection `A^(N) → N`. -/
noncomputable abbrev presentationMap : (N →₀ A) →ₗ[A] N :=
  Finsupp.linearCombination A (id : N → N)

/-- The module of relations of the canonical free presentation of `N`. -/
noncomputable abbrev presentationKer : Submodule A (N →₀ A) :=
  LinearMap.ker (presentationMap A N)

lemma presentationMap_surjective : Surjective (presentationMap A N) :=
  Finsupp.linearCombination_surjective _ surjective_id

lemma exact_presentationKer :
    Exact (presentationKer A N).subtype (presentationMap A N) :=
  LinearMap.exact_subtype_ker_map _

/-- `Tor₁^A(M, N) = 0`: for the canonical free presentation `0 → K → A^(N) → N → 0`, the map
`M ⊗ K → M ⊗ A^(N)` is injective (its kernel is `Tor₁^A(M, N)`). -/
def TorOneVanishes : Prop :=
  Injective ((presentationKer A N).subtype.lTensor M)

end Presentation

section Comparison

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  {N : Type w} [AddCommGroup N] [Module A N]

/-- `a ⊗ 1` and `1 ⊗ b` commute. -/
lemma rTensor_lTensor_apply {X Y X' Y' : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup X'] [Module A X'] [AddCommGroup Y'] [Module A Y']
    (a : X →ₗ[A] X') (b : Y →ₗ[A] Y') (x : X ⊗[A] Y) :
    a.rTensor Y' (b.lTensor X x) = b.lTensor X' (a.rTensor Y x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

variable {K P K' P' : Type*} [AddCommGroup K] [Module A K] [AddCommGroup P] [Module A P]
  [AddCommGroup K'] [Module A K'] [AddCommGroup P'] [Module A P']

/-- Comparison of two presentations `0 → K → P → N → 0` and `0 → K' → P' → N → 0`, the first
one flat: if tensoring the first with `M` stays injective, so does tensoring the second.
The proof goes through the fibre product `P ×_N P'`. -/
theorem lTensor_injective_of_lTensor_injective [Module.Flat A P]
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hfg : Exact f g) (hg : Surjective g)
    (f' : K' →ₗ[A] P') (g' : P' →ₗ[A] N) (hf' : Injective f') (hfg' : Exact f' g')
    (hg' : Surjective g') (h : Injective (f.lTensor M)) : Injective (f'.lTensor M) := by
  -- the fibre product `Q = P ×_N P'` and its two projections
  let Q : Submodule A (P × P') := LinearMap.ker (g.coprod (-g'))
  have memQ (p : P) (p' : P') : (p, p') ∈ Q ↔ g p = g' p' := by
    simp [Q, add_neg_eq_zero]
  let pr₁ : Q →ₗ[A] P := (LinearMap.fst A P P').comp Q.subtype
  let pr₂ : Q →ₗ[A] P' := (LinearMap.snd A P P').comp Q.subtype
  let ι : K →ₗ[A] Q := LinearMap.codRestrict Q ((LinearMap.inl A P P').comp f) fun k ↦ by
    simp [memQ, hfg.apply_apply_eq_zero]
  let ι' : K' →ₗ[A] Q := LinearMap.codRestrict Q ((LinearMap.inr A P P').comp f') fun k ↦ by
    simp [memQ, hfg'.apply_apply_eq_zero]
  have hι (k : K) : (ι k : P × P') = (f k, 0) := rfl
  have hι' (k' : K') : (ι' k' : P × P') = (0, f' k') := rfl
  have hpr₁ : Surjective pr₁ := fun p ↦ by
    obtain ⟨p', hp'⟩ := hg' (g p)
    exact ⟨⟨(p, p'), (memQ _ _).2 hp'.symm⟩, rfl⟩
  have hpr₂ : Surjective pr₂ := fun p' ↦ by
    obtain ⟨p, hp⟩ := hg (g' p')
    exact ⟨⟨(p, p'), (memQ _ _).2 hp⟩, rfl⟩
  have inj' : Injective ι' := fun a b hab ↦ hf' (by
    simpa [hι'] using congrArg (fun q : Q ↦ (q : P × P').2) hab)
  have exact₁ : Exact ι' pr₁ := by
    rintro ⟨⟨p, p'⟩, hq⟩
    have hq' := (memQ p p').1 hq
    change p = 0 ↔ _
    constructor
    · rintro rfl
      obtain ⟨k', hk'⟩ := (hfg' p').1 (by simpa using hq'.symm)
      exact ⟨k', Subtype.ext (Prod.ext rfl hk')⟩
    · rintro ⟨k', hk'⟩
      simpa [hι'] using (congrArg (fun q : Q ↦ (q : P × P').1) hk').symm
  have exact₂ : Exact ι pr₂ := by
    rintro ⟨⟨p, p'⟩, hq⟩
    have hq' := (memQ p p').1 hq
    change p' = 0 ↔ _
    constructor
    · rintro rfl
      obtain ⟨k, hk⟩ := (hfg p).1 (by simpa using hq')
      exact ⟨k, Subtype.ext (Prod.ext hk rfl)⟩
    · rintro ⟨k, hk⟩
      simpa [hι] using (congrArg (fun q : Q ↦ (q : P × P').2) hk).symm
  have h₁ : pr₁ ∘ₗ ι' = 0 := by ext; rfl
  have h₂ : pr₂ ∘ₗ ι' = f' := by ext; rfl
  have h₃ : pr₁ ∘ₗ ι = f := by ext; rfl
  -- `M ⊗ K' → M ⊗ Q` is injective since `P` is flat
  have inj : Injective (ι'.lTensor M) :=
    LinearMap.lTensor_injective_of_exact_of_flat pr₁ hpr₁ ι' inj' exact₁ M
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, hz⟩ := (_root_.lTensor_exact M exact₂ hpr₂ (ι'.lTensor M x)).1 (by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h₂, hx])
  have hz' : f.lTensor M z = 0 := by
    rw [← h₃, LinearMap.lTensor_comp, LinearMap.comp_apply, hz, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, h₁, LinearMap.lTensor_zero, LinearMap.zero_apply]
  rw [injective_iff_map_eq_zero] at h inj
  exact inj x (by rw [← hz, h z hz', map_zero])

/-- If `Tor₁^A(M, N) = 0`, then every short exact sequence `0 → K → P → N → 0` stays exact
after tensoring with `M`. -/
theorem TorOneVanishes.lTensor_injective (h : TorOneVanishes A M N)
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hf : Injective f) (hfg : Exact f g) (hg : Surjective g) :
    Injective (f.lTensor M) := by
  have := lTensor_injective_of_lTensor_injective (M := M) (K := presentationKer A N)
    (P := N →₀ A) (presentationKer A N).subtype (presentationMap A N)
    (exact_presentationKer A N) (presentationMap_surjective A N) f g hf hfg hg
  exact this h

/-- IV.1: `Tor₁^A(M, N)` can be computed from any flat presentation `0 → K → P → N → 0`. -/
theorem torOneVanishes_iff_lTensor_injective [Module.Flat A P]
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hf : Injective f) (hfg : Exact f g) (hg : Surjective g) :
    TorOneVanishes A M N ↔ Injective (f.lTensor M) := by
  refine ⟨fun h ↦ h.lTensor_injective f g hf hfg hg, fun h ↦ ?_⟩
  have := lTensor_injective_of_lTensor_injective (K' := presentationKer A N) (P' := N →₀ A)
    f g hfg hg (presentationKer A N).subtype (presentationMap A N) Subtype.val_injective
    (exact_presentationKer A N) (presentationMap_surjective A N) h
  exact this

/-- Invariance of `Tor₁` under isomorphism in the second variable. -/
theorem TorOneVanishes.of_linearEquiv {N' : Type*} [AddCommGroup N'] [Module A N']
    (h : TorOneVanishes A M N) (e : N ≃ₗ[A] N') : TorOneVanishes A M N' := by
  have := h.lTensor_injective (K := presentationKer A N') (P := N' →₀ A)
    (presentationKer A N').subtype (e.symm.toLinearMap ∘ₗ presentationMap A N')
    Subtype.val_injective
    ((exact_presentationKer A N').comp_injective _ e.symm.injective (by simp))
    (e.symm.surjective.comp (presentationMap_surjective A N'))
  exact this

end Comparison

section Balance

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  {N : Type w} [AddCommGroup N] [Module A N]
  {K P R L : Type*} [AddCommGroup K] [Module A K] [AddCommGroup P] [Module A P]
  [AddCommGroup R] [Module A R] [AddCommGroup L] [Module A L]

/-- The diagram chase behind the balance of `Tor₁`: given presentations `0 → K → P → N → 0`
with `P` flat and `0 → R → L → M → 0`, if `M ⊗ K → M ⊗ P` is injective then so is
`R ⊗ N → L ⊗ N`. -/
theorem rTensor_injective_of_lTensor_injective [Module.Flat A P]
    (f : K →ₗ[A] P) (g : P →ₗ[A] N) (hfg : Exact f g) (hg : Surjective g)
    (i : R →ₗ[A] L) (p : L →ₗ[A] M) (hi : Injective i) (hip : Exact i p) (hp : Surjective p)
    (h : Injective (f.lTensor M)) : Injective (i.rTensor N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective R hg x
  obtain ⟨z, hz⟩ := (_root_.lTensor_exact L hfg hg (i.rTensor P y)).1 (by
    rw [← rTensor_lTensor_apply, hx])
  have hz' : p.rTensor K z = 0 := by
    apply (injective_iff_map_eq_zero _).1 h
    rw [← rTensor_lTensor_apply, hz, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      hip.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨w, rfl⟩ := (_root_.rTensor_exact K hip hp z).1 hz'
  have hy : f.lTensor R w = y := Module.Flat.rTensor_preserves_injective_linearMap i hi
    (by rw [rTensor_lTensor_apply, hz])
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hfg.linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- Balance of `Tor₁`: `Tor₁^A(M, N)` can also be computed from a flat presentation
`0 → R → L → M → 0` of the first variable. -/
theorem torOneVanishes_iff_rTensor_injective [Module.Flat A L]
    (i : R →ₗ[A] L) (p : L →ₗ[A] M) (hi : Injective i) (hip : Exact i p) (hp : Surjective p) :
    TorOneVanishes A M N ↔ Injective (i.rTensor N) := by
  have hK := exact_presentationKer A N
  have hF := presentationMap_surjective A N
  constructor
  · intro h
    have := rTensor_injective_of_lTensor_injective (K := presentationKer A N) (P := N →₀ A)
      (presentationKer A N).subtype (presentationMap A N) hK hF i p hi hip hp
    exact this h
  · intro h
    have h' : Injective (i.lTensor N) :=
      (LinearMap.lTensor_inj_iff_rTensor_inj (M := N) (f := i)).2 h
    have := rTensor_injective_of_lTensor_injective (K := R) (P := L) (N := M) (M := N)
      (R := presentationKer A N) (L := N →₀ A)
      i p hip hp (presentationKer A N).subtype (presentationMap A N) Subtype.val_injective hK hF h'
    unfold TorOneVanishes
    exact (LinearMap.lTensor_inj_iff_rTensor_inj (M := M)
      (f := (presentationKer A N).subtype)).2 this

end Balance

section Criteria

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  {N : Type w} [AddCommGroup N] [Module A N]

variable (N) in
/-- IV.1: `Tor₁^A(M, N) = 0` for all `N` when `M` is flat. -/
theorem torOneVanishes_of_flat [Module.Flat A M] : TorOneVanishes A M N :=
  Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

variable (M) in
/-- `Tor₁^A(M, N) = 0` when `N` is flat (symmetry of `Tor`). -/
theorem torOneVanishes_of_flat_right [Module.Flat A N] : TorOneVanishes A M N := by
  have := LinearMap.lTensor_injective_of_exact_of_flat (M := presentationKer A N)
    (N := N →₀ A) (P := N) (presentationMap A N) (presentationMap_surjective A N)
    (presentationKer A N).subtype Subtype.val_injective (exact_presentationKer A N) M
  exact this

/-- IV.1: `Tor₁^A(M, A/I) = 0` if and only if `M ⊗ I → M ⊗ A` is injective. -/
theorem torOneVanishes_quotient_iff (I : Ideal A) :
    TorOneVanishes A M (A ⧸ I) ↔ Injective (I.subtype.lTensor M) := by
  have := torOneVanishes_iff_lTensor_injective (M := M) (K := I) (P := A) I.subtype I.mkQ
    Subtype.val_injective (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  exact this

variable (A M) in
/-- IV.1: `M` is flat if and only if `Tor₁^A(M, A/I) = 0` for every ideal `I`. -/
theorem flat_iff_forall_torOneVanishes_quotient :
    Module.Flat A M ↔ ∀ I : Ideal A, TorOneVanishes A M (A ⧸ I) := by
  simp_rw [torOneVanishes_quotient_iff, Module.Flat.iff_lTensor_injective']

variable (A M) in
/-- IV.1: `M` is flat if and only if `Tor₁^A(M, N) = 0` for every module `N`. -/
theorem flat_iff_forall_torOneVanishes :
    Module.Flat A M ↔ ∀ (N : Type u) [AddCommGroup N] [Module A N], TorOneVanishes A M N :=
  ⟨fun _ N _ _ ↦ torOneVanishes_of_flat N, fun h ↦
    (flat_iff_forall_torOneVanishes_quotient A M).2 fun I ↦ h (A ⧸ I)⟩

/-- `Tor₁^A(M, -)` vanishing is stable under extensions: this is the part of the long exact
`Tor` sequence `Tor₁(M, N') → Tor₁(M, N) → Tor₁(M, N'')` used in IV.5.3. -/
theorem TorOneVanishes.of_exact {N' N'' : Type*} [AddCommGroup N'] [Module A N']
    [AddCommGroup N''] [Module A N''] (a : N' →ₗ[A] N) (b : N →ₗ[A] N'') (ha : Injective a)
    (hab : Exact a b) (hb : Surjective b) (h' : TorOneVanishes A M N')
    (h'' : TorOneVanishes A M N'') : TorOneVanishes A M N := by
  let π := presentationMap A N
  let K := presentationKer A N
  let F₁ : Submodule A (N →₀ A) := (LinearMap.range a).comap π
  have hKF₁ : K ≤ F₁ := fun x hx ↦ by
    simp only [F₁, Submodule.mem_comap]
    rw [LinearMap.mem_ker.1 hx]
    exact zero_mem _
  -- `0 → F₁ → A^(N) → N'' → 0`
  have e₁ : Exact F₁.subtype (b ∘ₗ π) := by
    intro x
    rw [LinearMap.comp_apply, hab (π x)]
    constructor
    · rintro ⟨n', hn'⟩
      exact ⟨⟨x, n', hn'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  have s₁ : Surjective (b ∘ₗ π) := hb.comp (presentationMap_surjective A N)
  -- `0 → K → F₁ → N' → 0`
  let e : LinearMap.range a ≃ₗ[A] N' := (LinearEquiv.ofInjective a ha).symm
  let q : F₁ →ₗ[A] N' := e.toLinearMap ∘ₗ (π.restrict fun x hx ↦ hx)
  have hq (x : F₁) : a (q x) = π x := by
    have := LinearEquiv.ofInjective_apply a (h := ha) (q x)
    simp only [q, e, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have e₂ : Exact (Submodule.inclusion hKF₁) q := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := hq x
      rw [hx, map_zero] at this
      exact LinearMap.mem_ker.2 this.symm
    · rintro ⟨k, rfl⟩
      apply ha
      rw [hq, map_zero]
      exact LinearMap.mem_ker.1 k.2
  have s₂ : Surjective q := fun n' ↦ by
    obtain ⟨x, hx⟩ := presentationMap_surjective A N (a n')
    refine ⟨⟨x, ⟨n', hx.symm⟩⟩, ha ?_⟩
    rw [hq]
    exact hx
  have i₁ := h''.lTensor_injective (K := F₁) (P := N →₀ A) F₁.subtype (b ∘ₗ π)
    Subtype.val_injective e₁ s₁
  have i₂ := h'.lTensor_injective (K := K) (P := F₁) (Submodule.inclusion hKF₁) q
    (Submodule.inclusion_injective hKF₁) e₂ s₂
  have : K.subtype = F₁.subtype ∘ₗ Submodule.inclusion hKF₁ := rfl
  change Injective (K.subtype.lTensor M)
  rw [this, LinearMap.lTensor_comp, LinearMap.coe_comp]
  exact i₁.comp i₂

end Criteria

end SGA.SGA1.ExposeIV
