/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.PrincipalCovering
import SGA.SGA1.ExposeXI.ArtinSchreier
import SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup

/-!
# XIII.2.13: `p`-groups and central `p`-extensions are quotients of `π₁(𝔸¹)`

Remark XIII.2.13 recalls Abhyankar's conjecture for the affine line, proved by M. Raynaud: over
an algebraically closed field `k` of characteristic `p`, a finite group `G` is a continuous
quotient of `π₁(𝔸¹_k)` iff `G^{(p')} = 1` (`AbhyankarAffineLineStatement`). The necessary
condition is `sylowSup_eq_top_of_affineLine`. Here we prove the sufficient condition for
`p`-groups, and more generally that the finite quotients of `π₁(𝔸¹_k)` are closed under
extensions by central `p`-groups, for any field `k` of characteristic `p`:

* `exists_lift_of_central_ker`: central `ℤ/p` embedding problems for `π₁(Spec R)` have weak
  solutions, for every ring `R` of characteristic `p` with connected spectrum (the concrete form
  of `cd_p π₁ ≤ 1`). If `B` is the Galois algebra of `ψ : π₁ ↠ H` and `G → H` has central kernel
  `ℤ/p`, the lift is the Artin–Schreier covering `B[T]/(Tᵖ - T + a)`, on which `G` acts by
  semilinear automorphisms `T ↦ T + u(g)` (`AffineLinePGroups.semilinearAut`). The element `a`
  and the cochain `u` come from the vanishing of additive Galois cohomology of `B`, through an
  element of trace one (`AffineLinePGroups.exists_sum_smul_eq_one`,
  `AffineLinePGroups.exists_eq_sub_smul_of_cocycle`, `AffineLinePGroups.liftCochain`).
* `exists_surjective_lift_of_central`: a lift becomes surjective after twisting by a character
  `π₁ → ℤ/p` that does not factor through `ψ`; there is one since `Hom_cont(π₁(𝔸¹_k), ℤ/p)` is
  infinite (`infinite_continuousMonoidHom_aut_fiberFunctor`, Artin–Schreier theory, in
  `SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup`).
* `exists_surjective_fundamentalGroup_affineLine_of_ker_le_center`,
  `exists_surjective_fundamentalGroup_affineLine_of_isPGroup`, `abhyankarAffineLine_of_isPGroup`:
  the consequences for `π₁(𝔸¹_k, x)`.

Serre's theorem for arbitrary (not necessarily central) `p`-group kernels is proved in
`SGA.SGA1.ExposeXIII.SerrePKernel` (`SerrePKernel.affineLinePExtension`), and the full statement
is reduced there to Raynaud's two remaining cases, patching and degeneration
(`SerrePKernel.abhyankarAffineLine_of_patching_of_caseB`, statements in
`SGA.SGA1.ExposeXIII.AbhyankarAffineLine`).
-/
universe u

namespace SGA.SGA1.ExposeXIII

open Polynomial

namespace AffineLinePGroups

/-- Elements of Chase–Harrison–Rosenberg (`∑ xᵢ yᵢ = 1` and `∑ xᵢ σ(yᵢ) = 0` for `σ ≠ 1`) for a
faithful action of a finite group `H` on an unramified `R`-algebra `B` without non-trivial
idempotents: the inertia groups are trivial (V.2.4), so `ExposeV.exists_galois_elements`
applies. -/
theorem exists_galois_elements_of_faithful {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H B] [SMulCommClass H R B]
    [Algebra.FormallyUnramified R B] [Algebra.EssFiniteType R B]
    (hB : ∀ c : B, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ h : H, (∀ b : B, h • b = b) → h = 1) :
    ∃ (n : ℕ) (x y : Fin n → B), ∑ i, x i * y i = 1 ∧
      ∀ σ : H, σ ≠ 1 → ∑ i, x i * σ • y i = 0 :=
  ExposeV.exists_galois_elements fun m hm g hg ↦
    ExposeV.eq_one_of_mem_inertia (B := R) hB hfaith m hm.ne_top g hg

section Trace

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  {H : Type*} [Group H] [Fintype H] [MulSemiringAction H B] [SMulCommClass H R B]

/-- Elements of Chase–Harrison–Rosenberg for an action of a finite group `H` on `B`
(`∑ xᵢ yᵢ = 1` and `∑ xᵢ σ(yᵢ) = 0` for `σ ≠ 1`) give an element `θ` of trace one:
`∑_{h ∈ H} h θ = 1`. -/
theorem exists_sum_smul_eq_one_of_galois_elements {n : ℕ} {x y : Fin n → B}
    (h1 : ∑ i, x i * y i = 1) (h2 : ∀ σ : H, σ ≠ 1 → ∑ i, x i * σ • y i = 0) :
    ∃ θ : B, ∑ h : H, h • θ = 1 := by
  classical
  let F := FixedPoints.subring B H
  have hS : ∀ b : B, (∑ h : H, h • b) ∈ F := fun b g ↦ by
    change g • ∑ h : H, h • b = ∑ h : H, h • b
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h ↦ by simp [mul_smul])
  let s : Fin n → F := fun i ↦ ⟨∑ h : H, h • y i, hS _⟩
  have hsum : ∑ i, x i * (s i : B) = 1 := by
    simp only [s, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))]
    rw [Finset.sum_eq_zero (fun h hh ↦ h2 h (Finset.ne_of_mem_erase hh)), add_zero]
    simpa using h1
  let I : Ideal F := Ideal.span (Set.range s)
  have hint : (algebraMap F B).IsIntegral := by
    have : Algebra.IsInvariant F B H := ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
    have : Algebra.IsIntegral F B := Algebra.IsInvariant.isIntegral F B H
    exact Algebra.IsIntegral.isIntegral
  have hI : I = ⊤ := by
    rw [← Ideal.map_eq_top_iff (algebraMap F B) Subtype.val_injective hint, Ideal.eq_top_iff_one]
    rw [← hsum]
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))
  have h1I : (1 : F) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Ideal.mem_span_range_iff_exists_fun).mp h1I
  refine ⟨∑ i, (r i : B) * y i, ?_⟩
  have hr' : ∑ i, (r i : B) * (s i : B) = 1 := by
    have := congrArg Subtype.val hr
    simpa using this
  rw [← hr']
  simp only [Finset.smul_sum, s, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun h _ ↦ ?_
  rw [smul_mul', (r i).2 h]

/-- A finite group `H` acting faithfully on an unramified `R`-algebra `B` with connected spectrum
admits an element `θ` of trace one: `∑_{h ∈ H} h θ = 1`. This is the normal-basis substitute
used for the vanishing of additive Galois cohomology (V.2.4: the inertia groups are trivial, so
the elements of Chase–Harrison–Rosenberg exist). -/
theorem exists_sum_smul_eq_one [Algebra.FormallyUnramified R B] [Algebra.EssFiniteType R B]
    (hB : ∀ c : B, IsIdempotentElem c → c = 0 ∨ c = 1)
    (hfaith : ∀ h : H, (∀ b : B, h • b = b) → h = 1) :
    ∃ θ : B, ∑ h : H, h • θ = 1 := by
  obtain ⟨n, x, y, h1, h2⟩ := exists_galois_elements_of_faithful (R := R) hB hfaith
  exact exists_sum_smul_eq_one_of_galois_elements h1 h2

end Trace

section Cocycle

variable {B : Type*} [CommRing B] {H : Type*} [Group H] [Fintype H] [MulSemiringAction H B]
  {θ : B} {W : Type*} [AddCommGroup W] [Module B W] [DistribMulAction H W]
  (hW : ∀ (σ : H) (b : B) (w : W), σ • (b • w) = (σ • b) • (σ • w))

include hW in
/-- Additive Hilbert 90 for a `B`-module `W` with a semilinear action of `H`: if
`∑_h h θ = 1`, every `1`-cocycle `H → W` is a coboundary, `g σ = a - σ a` with
`a = ∑_ρ ρ(θ) g(ρ)`. -/
theorem exists_eq_sub_smul_of_cocycle_of_semilinear (hθ : ∑ h : H, h • θ = 1) (g : H → W)
    (hg : ∀ σ τ, g (σ * τ) = σ • g τ + g σ) : ∃ a : W, ∀ σ, g σ = a - σ • a := by
  refine ⟨∑ ρ : H, (ρ • θ) • g ρ, fun σ ↦ ?_⟩
  have h1 : σ • ∑ ρ : H, (ρ • θ) • g ρ = ∑ ρ : H, ((σ * ρ) • θ) • (g (σ * ρ) - g σ) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    rw [hW, hg, mul_smul, add_sub_cancel_right]
  have h2 : ∑ ρ : H, ((σ * ρ) • θ) • (g (σ * ρ) - g σ) =
      ∑ ρ : H, (ρ • θ) • g ρ - (∑ ρ : H, ρ • θ) • g σ := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_smul]
    congr 1
    · exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ ↦ rfl)
    · exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ ↦ rfl)
  rw [h1, h2, hθ, one_smul, sub_sub_cancel]

omit [Fintype H] in
lemma smul_mul_eq_smul_smul (σ : H) (b c : B) : σ • (b * c) = (σ • b) • (σ • c) :=
  smul_mul' σ b c

/-- Additive Hilbert 90: if `∑_h h θ = 1`, every `1`-cocycle `H → B` is a coboundary,
`g σ = a - σ a` with `a = ∑_ρ g(ρ) ρ(θ)`. -/
theorem exists_eq_sub_smul_of_cocycle (hθ : ∑ h : H, h • θ = 1) (g : H → B)
    (hg : ∀ σ τ, g (σ * τ) = σ • g τ + g σ) : ∃ a : B, ∀ σ, g σ = a - σ • a :=
  exists_eq_sub_smul_of_cocycle_of_semilinear (W := B) smul_mul_eq_smul_smul hθ g hg

variable {G : Type*} [Group G] (π : G →* H) (s : H → G) (hs : ∀ σ, π (s σ) = σ)

include hs in
omit [Fintype H] in
lemma mul_section_mem_ker (g : G) (ρ : H) : g * s ρ * (s (π g * ρ))⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, mul_inv_cancel]

variable (κ : G → W)

/-- The `1`-cochain `G → W` extending `κ` on `ker π`:
`u(g) = ∑_ρ (π(g)ρ)(θ) κ(g s(ρ) s(π(g)ρ)⁻¹)`, for a set-theoretic section `s` of `π` and `θ` of
trace one. -/
noncomputable def liftCochain (θ : B) (g : G) : W :=
  ∑ ρ : H, ((π g * ρ) • θ) • κ (g * s ρ * (s (π g * ρ))⁻¹)

include hs hW in
/-- `liftCochain` is a `1`-cocycle for the action of `G` on `W` through `π`, if `κ` is additive
on `ker π` and equivariant for conjugation. -/
theorem liftCochain_mul
    (hκ : ∀ z ∈ π.ker, ∀ w ∈ π.ker, κ (z * w) = κ z + κ w)
    (hκc : ∀ g, ∀ z ∈ π.ker, κ (g * z * g⁻¹) = π g • κ z) (g h : G) :
    liftCochain π s κ θ (g * h) = π g • liftCochain π s κ θ h + liftCochain π s κ θ g := by
  unfold liftCochain
  have hsplit : ∀ ρ : H, κ (g * h * s ρ * (s (π (g * h) * ρ))⁻¹) =
      π g • κ (h * s ρ * (s (π h * ρ))⁻¹) + κ (g * s (π h * ρ) * (s (π g * (π h * ρ)))⁻¹) := by
    intro ρ
    have heq : g * h * s ρ * (s (π (g * h) * ρ))⁻¹ =
        g * (h * s ρ * (s (π h * ρ))⁻¹) * g⁻¹ * (g * s (π h * ρ) * (s (π g * (π h * ρ)))⁻¹) := by
      rw [map_mul, mul_assoc (π g)]
      group
    rw [heq, hκ _ ((MonoidHom.normal_ker π).conj_mem _ (mul_section_mem_ker π s hs h ρ) g) _
      (mul_section_mem_ker π s hs g _), hκc g _ (mul_section_mem_ker π s hs h ρ)]
  simp_rw [hsplit, smul_add, Finset.sum_add_distrib, Finset.smul_sum, hW, ← mul_smul, map_mul,
    mul_assoc]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (π h)) _ _ (fun _ ↦ rfl)

omit [DistribMulAction H W] in
/-- On `ker π`, `liftCochain` is `κ`. -/
theorem liftCochain_of_mem_ker (hθ : ∑ h : H, h • θ = 1) {z : G} (hz : z ∈ π.ker) :
    liftCochain π s κ θ z = κ z := by
  unfold liftCochain
  rw [MonoidHom.mem_ker] at hz
  simp_rw [hz, one_mul, mul_inv_cancel_right, ← Finset.sum_smul, hθ, one_smul]

include hs hW in
/-- The Artin–Schreier step, for an additive map `F` of `W` commuting with `H` and fixing the
values of `κ` (in practice `F` is the Frobenius and `κ` takes values in `𝔽_p`-points): for
`u = liftCochain π s κ θ`, the cocycle `F u - u` of `G` is inflated from `H`, so it is the
coboundary of some `a ∈ W`: `F(u(g)) - u(g) = a - π(g) a`. -/
theorem exists_liftCochain_sub (F : W →+ W) (hF : ∀ (σ : H) w, F (σ • w) = σ • F w)
    (hθ : ∑ h : H, h • θ = 1)
    (hκ : ∀ z ∈ π.ker, ∀ w ∈ π.ker, κ (z * w) = κ z + κ w)
    (hκc : ∀ g, ∀ z ∈ π.ker, κ (g * z * g⁻¹) = π g • κ z)
    (hκF : ∀ z ∈ π.ker, F (κ z) = κ z) :
    ∃ a : W, ∀ g, F (liftCochain π s κ θ g) - liftCochain π s κ θ g = a - π g • a := by
  set u := liftCochain π s κ θ
  set w : G → W := fun g ↦ F (u g) - u g with hw
  have hwmul : ∀ g h, w (g * h) = π g • w h + w g := by
    intro g h
    simp only [hw, u, liftCochain_mul hW π s hs κ hκ hκc, map_add, hF, smul_sub]
    abel
  have hwker : ∀ z ∈ π.ker, w z = 0 := by
    intro z hz
    simp only [hw, u, liftCochain_of_mem_ker π s κ hθ hz, hκF z hz, sub_self]
  have hwright : ∀ g, ∀ z ∈ π.ker, w (g * z) = w g := by
    intro g z hz
    rw [hwmul, hwker z hz, smul_zero, zero_add]
  have hws : ∀ g, w g = w (s (π g)) := by
    intro g
    have hz : (s (π g))⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    rw [← hwright (s (π g)) _ hz, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := exists_eq_sub_smul_of_cocycle_of_semilinear hW hθ (fun σ ↦ w (s σ)) (by
    intro σ τ
    calc w (s (σ * τ)) = w (s σ * s τ) := by rw [hws (s σ * s τ), map_mul, hs, hs]
      _ = σ • w (s τ) + w (s σ) := by rw [hwmul, hs])
  refine ⟨a, fun g ↦ ?_⟩
  change w g = _
  rw [hws, ha]

end Cocycle

section ArtinSchreierCocycle

variable (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] [CharP B p] {H : Type*} [Group H]
  [Fintype H] [MulSemiringAction H B] {θ : B} {G : Type*} [Group G] (π : G →* H) (s : H → G)
  (hs : ∀ σ, π (s σ) = σ) (κ : G → B)

include hs in
/-- The Artin–Schreier step for `B`: for `u = liftCochain π s κ θ`, `u(g)ᵖ - u(g) = a - π(g) a`
for some `a ∈ B`, when `κ` takes values in `𝔽_p` on `ker π`. -/
theorem exists_liftCochain_pow_sub (hθ : ∑ h : H, h • θ = 1)
    (hκ : ∀ z ∈ π.ker, ∀ w ∈ π.ker, κ (z * w) = κ z + κ w)
    (hκc : ∀ g, ∀ z ∈ π.ker, κ (g * z * g⁻¹) = π g • κ z)
    (hκp : ∀ z ∈ π.ker, κ z ^ p = κ z) :
    ∃ a : B, ∀ g, liftCochain π s κ θ g ^ p - liftCochain π s κ θ g = a - π g • a :=
  exists_liftCochain_sub (W := B) smul_mul_eq_smul_smul π s hs κ (frobenius B p).toAddMonoidHom
    (fun σ w ↦ (smul_pow' σ w p).symm) hθ hκ hκc hκp

end ArtinSchreierCocycle

section Semilinear

open ExposeXI

variable (p : ℕ) [hp : Fact p.Prime] {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [CharP B p] {G : Type*} [Group G] (ρ : G →* (B ≃ₐ[R] B)) (a : B) (u : G → B)
  (hu : ∀ g, u g ^ p - u g = a - ρ g a)

/-- The inclusion `B → B[T]/(Tᵖ - T + a)` as an `R`-algebra map. -/
noncomputable abbrev artinSchreierInclusion :
    B →ₐ[R] ArtinSchreierAlgebra B p a :=
  IsScalarTower.toAlgHom R B (ArtinSchreierAlgebra B p a)

include hu in
lemma eval₂_root_add_eq_zero (g : G) :
    (X ^ p - X + C a : B[X]).eval₂
      (((artinSchreierInclusion p a).comp (ρ g).toAlgHom : B →ₐ[R] _) :
        B →+* ArtinSchreierAlgebra B p a)
      (AdjoinRoot.root _ + algebraMap B _ (u g)) = 0 := by
  have hpB : ((p : ℕ) : B) = 0 := CharP.cast_eq_zero B p
  rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C,
    ArtinSchreier.add_pow_of_natCast_eq_zero hp.out (ArtinSchreier.natCast_eq_zero hpB),
    ArtinSchreier.root_pow, ← map_pow]
  change _ + algebraMap B _ (ρ g a) = 0
  have := congrArg (algebraMap B (ArtinSchreierAlgebra B p a)) (hu g)
  rw [map_sub, map_sub, map_pow] at this
  rw [map_pow]
  linear_combination this

/-- The semilinear Artin–Schreier map: it acts on `B` by `ρ g` and sends the root `T` to
`T + u(g)`. It is well defined because `u(g)ᵖ - u(g) = a - ρ(g)(a)`. -/
noncomputable def semilinearHom (g : G) :
    ArtinSchreierAlgebra B p a →ₐ[R] ArtinSchreierAlgebra B p a :=
  AdjoinRoot.liftAlgHom _ ((artinSchreierInclusion p a).comp (ρ g).toAlgHom)
    (AdjoinRoot.root _ + algebraMap B _ (u g)) (eval₂_root_add_eq_zero p ρ a u hu g)

lemma semilinearHom_algebraMap (g : G) (b : B) :
    semilinearHom p ρ a u hu g (algebraMap B _ b) = algebraMap B _ (ρ g b) :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ b

lemma semilinearHom_root (g : G) :
    semilinearHom p ρ a u hu g (AdjoinRoot.root _) =
      AdjoinRoot.root _ + algebraMap B _ (u g) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma semilinearHom_comp_inclusion (g : G) :
    (semilinearHom p ρ a u hu g).comp (artinSchreierInclusion p a) =
      (artinSchreierInclusion p a).comp (ρ g).toAlgHom :=
  AlgHom.ext fun b ↦ semilinearHom_algebraMap p ρ a u hu g b

omit hp [CharP B p] in
lemma algHom_ext_artinSchreier {T : Type*} [CommRing T] [Algebra R T]
    {f₁ f₂ : ArtinSchreierAlgebra B p a →ₐ[R] T}
    (h₁ : ∀ b, f₁ (algebraMap B _ b) = f₂ (algebraMap B _ b))
    (h₂ : f₁ (AdjoinRoot.root _) = f₂ (AdjoinRoot.root _)) : f₁ = f₂ :=
  AdjoinRoot.algHom_ext' (AlgHom.ext h₁) h₂

variable (hmul : ∀ g h, u (g * h) = ρ g (u h) + u g)
include hmul

lemma semilinearHom_mul (g h : G) :
    semilinearHom p ρ a u hu (g * h) =
      (semilinearHom p ρ a u hu g).comp (semilinearHom p ρ a u hu h) := by
  refine algHom_ext_artinSchreier p a (fun b ↦ ?_) ?_
  · rw [AlgHom.comp_apply, semilinearHom_algebraMap, semilinearHom_algebraMap,
      semilinearHom_algebraMap, map_mul, AlgEquiv.mul_apply]
  · rw [AlgHom.comp_apply, semilinearHom_root, semilinearHom_root, map_add,
      semilinearHom_root, semilinearHom_algebraMap, hmul, map_add]
    ring

lemma semilinearHom_one : semilinearHom p ρ a u hu 1 = AlgHom.id R _ := by
  have h1 : u 1 = 0 := by
    have := hmul 1 1
    rw [mul_one, map_one, AlgEquiv.one_apply, left_eq_add] at this
    exact this
  refine algHom_ext_artinSchreier p a (fun b ↦ ?_) ?_
  · rw [semilinearHom_algebraMap, map_one, AlgEquiv.one_apply, AlgHom.id_apply]
  · rw [semilinearHom_root, h1, map_zero, add_zero, AlgHom.id_apply]

/-- The action of `G` on `B[T]/(Tᵖ - T + a)` by semilinear Artin–Schreier automorphisms. -/
noncomputable def semilinearAut :
    G →* (ArtinSchreierAlgebra B p a ≃ₐ[R] ArtinSchreierAlgebra B p a) where
  toFun g := AlgEquiv.ofAlgHom (semilinearHom p ρ a u hu g) (semilinearHom p ρ a u hu g⁻¹)
    (by rw [← semilinearHom_mul p ρ a u hu hmul, mul_inv_cancel,
      semilinearHom_one p ρ a u hu hmul])
    (by rw [← semilinearHom_mul p ρ a u hu hmul, inv_mul_cancel,
      semilinearHom_one p ρ a u hu hmul])
  map_one' := AlgEquiv.coe_toAlgHom_injective (semilinearHom_one p ρ a u hu hmul)
  map_mul' g h := AlgEquiv.coe_toAlgHom_injective (semilinearHom_mul p ρ a u hu hmul g h)

lemma semilinearAut_apply (g : G) (y : ArtinSchreierAlgebra B p a) :
    semilinearAut p ρ a u hu hmul g y = semilinearHom p ρ a u hu g y :=
  rfl

end Semilinear

section Points

open ExposeXI

variable (p : ℕ) [hp : Fact p.Prime] {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [CharP B p] {H G : Type*} [Group H] [Group G] (ρ : H →* (B ≃ₐ[R] B)) (π : G →* H)
  (a : B) (u : G → B) (hu : ∀ g, u g ^ p - u g = a - (ρ.comp π) g a)
  (hmul : ∀ g h, u (g * h) = (ρ.comp π) g (u h) + u g)
  (Ω : Type*) [Field Ω] [Algebra R Ω] [CharP Ω p]

omit hp [CharP B p] [CharP Ω p] in
lemma root_pow_sub_root_eq (x : ArtinSchreierAlgebra B p a →ₐ[R] Ω) :
    x (AdjoinRoot.root _) ^ p - x (AdjoinRoot.root _) =
      -(x.comp (artinSchreierInclusion p a)) a := by
  have h := congrArg x (AdjoinRoot.eval₂_root (X ^ p - X + C a : B[X]))
  rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, map_add, map_sub, map_pow,
    map_zero] at h
  change _ = -x (algebraMap B _ a)
  rw [← AdjoinRoot.algebraMap_eq] at h
  linear_combination h

/-- The geometric points of the Artin–Schreier covering `B' = B[T]/(Tᵖ - T + a)`: if `H` acts
simply transitively on `Hom_R(B, Ω)`, `π : G → H` is onto, and `u` restricts on `ker π` to a
bijection onto `𝔽_p ⊂ B`, then `G` acts simply transitively on `Hom_R(B', Ω)` through the
semilinear Artin–Schreier automorphisms. -/
theorem existsUnique_comp_semilinearAut
    (hH : ∀ x y : B →ₐ[R] Ω, ∃! σ : H, x.comp (ρ σ).toAlgHom = y)
    (hπ : Function.Surjective π) (χ : G → ZMod p)
    (hχ : ∀ z ∈ π.ker, u z = ZMod.castHom (dvd_refl p) B (χ z))
    (hχinj : ∀ z ∈ π.ker, χ z = 0 → z = 1) (hχsurj : ∀ k, ∃ z ∈ π.ker, χ z = k)
    (x y : ArtinSchreierAlgebra B p a →ₐ[R] Ω) :
    ∃! g : G, x.comp (semilinearAut p (ρ.comp π) a u hu hmul g).toAlgHom = y := by
  set e := semilinearAut p (ρ.comp π) a u hu hmul
  set ι := artinSchreierInclusion (R := R) p a
  have he_ι : ∀ g, (e g).toAlgHom.comp ι = ι.comp (ρ (π g)).toAlgHom := fun g ↦
    semilinearHom_comp_inclusion p (ρ.comp π) a u hu g
  have hcast : ∀ k : ZMod p, ∀ f : ArtinSchreierAlgebra B p a →ₐ[R] Ω,
      f (algebraMap B _ (ZMod.castHom (dvd_refl p) B k)) = ZMod.castHom (dvd_refl p) Ω k := by
    intro k f
    exact RingHom.congr_fun (RingHom.ext_zmod ((f.toRingHom.comp (algebraMap B _)).comp
      (ZMod.castHom (dvd_refl p) B)) (ZMod.castHom (dvd_refl p) Ω)) k
  have hroot : ∀ g, e g (AdjoinRoot.root _) = AdjoinRoot.root _ + algebraMap B _ (u g) :=
    fun g ↦ semilinearHom_root p (ρ.comp π) a u hu g
  have hB : ∀ g b, e g (algebraMap B _ b) = algebraMap B _ (ρ (π g) b) :=
    fun g b ↦ semilinearHom_algebraMap p (ρ.comp π) a u hu g b
  -- restriction of `x ∘ e g` to `B`
  have hres : ∀ (f : ArtinSchreierAlgebra B p a →ₐ[R] Ω) g,
      (f.comp (e g).toAlgHom).comp ι = (f.comp ι).comp (ρ (π g)).toAlgHom := by
    intro f g
    rw [AlgHom.comp_assoc, he_ι, ← AlgHom.comp_assoc]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨σ, hσ, -⟩ := hH (x.comp ι) (y.comp ι)
    obtain ⟨g₀, rfl⟩ := hπ σ
    set x' := x.comp (e g₀).toAlgHom
    have hx'B : x'.comp ι = y.comp ι := by rw [hres, hσ]
    set d := y (AdjoinRoot.root _) - x' (AdjoinRoot.root _)
    have hd : d ^ p - d + 0 = 0 := by
      have h₁ := root_pow_sub_root_eq p a Ω x'
      have h₂ := root_pow_sub_root_eq p a Ω y
      rw [hx'B] at h₁
      rw [sub_pow_char]
      linear_combination h₂ - h₁
    have hprod := congrArg (Polynomial.eval d)
      (ExposeXI.ArtinSchreier.X_pow_sub_X_eq_prod (A := Ω) (p := p))
    rw [eval_add, eval_sub, eval_pow, eval_X, eval_C, hd, eval_prod] at hprod
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
    obtain ⟨z, hz, hzk⟩ := hχsurj k
    refine ⟨g₀ * z, algHom_ext_artinSchreier p a (fun b ↦ ?_) ?_⟩
    · rw [map_mul]
      change x' (e z (algebraMap B _ b)) = y (algebraMap B _ b)
      rw [hB, (MonoidHom.mem_ker).mp hz, map_one, AlgEquiv.one_apply]
      exact congrArg (fun f ↦ f b) hx'B
    · rw [map_mul]
      change x' (e z (AdjoinRoot.root _)) = y (AdjoinRoot.root _)
      rw [hroot, map_add, hχ z hz, hcast, hzk, ← hk]
      ring
  · intro g g' hg hg'
    obtain ⟨σ, -, hσ⟩ := hH (x.comp ι) (y.comp ι)
    have h₁ : π g = σ := hσ (π g) (by beta_reduce; rw [← hres, hg])
    have h₂ : π g' = σ := hσ (π g') (by beta_reduce; rw [← hres, hg'])
    have hz : g⁻¹ * g' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, h₂, inv_mul_cancel]
    have hyz : ∀ t, y (e (g⁻¹ * g') t) = y t := by
      intro t
      calc y (e (g⁻¹ * g') t) = (x.comp (e g).toAlgHom) (e (g⁻¹ * g') t) := by rw [hg]
        _ = x (e g (e (g⁻¹ * g') t)) := rfl
        _ = x (e g' t) := by rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
        _ = y t := by rw [← hg']; rfl
    have h0 := hyz (AdjoinRoot.root _)
    rw [hroot, map_add, add_eq_left, hχ _ hz, hcast] at h0
    have hz1 : g⁻¹ * g' = 1 :=
      hχinj _ hz ((ZMod.castHom (dvd_refl p) Ω).injective (by rw [h0, map_zero]))
    rw [← mul_inv_cancel_left g g', hz1, mul_one]

end Points

section Galois

open CategoryTheory PreGaloisCategory CommAlgCat

variable {R : Type u} [CommRing R]

/-- The automorphisms of an étale covering `Spec A → Spec R`, in the opposite group, are the
`R`-algebra automorphisms of `A` (`autOpEquivAlgEquiv` as a group isomorphism). -/
noncomputable def autOpMulEquivAlgEquiv (A : FiniteEtale.{u} R) :
    (Aut (Opposite.op A))ᵐᵒᵖ ≃* (A.obj ≃ₐ[R] A.obj) where
  toEquiv := MulOpposite.opEquiv.symm.trans (autOpEquivAlgEquiv A)
  map_mul' φ ψ := by
    ext y
    rfl

lemma fiberFunctor_map_autOpMulEquivAlgEquiv_symm (Ω : Type u) [Field Ω] [Algebra R Ω]
    (A : FiniteEtale.{u} R) (e : A.obj ≃ₐ[R] A.obj) (x : A.obj →ₐ[R] Ω) :
    (ExposeV.fiberFunctor R Ω).map ((autOpMulEquivAlgEquiv A).symm e).unop.hom x =
      x.comp e.toAlgHom :=
  rfl

lemma fiberFunctor_map_unop_hom (Ω : Type u) [Field Ω] [Algebra R Ω]
    (A : FiniteEtale.{u} R) (φ : (Aut (Opposite.op A))ᵐᵒᵖ) (x : A.obj →ₐ[R] Ω) :
    (ExposeV.fiberFunctor R Ω).map φ.unop.hom x = x.comp (autOpMulEquivAlgEquiv A φ).toAlgHom :=
  rfl

end Galois

section Helpers

variable (p : ℕ)

lemma separable_artinSchreier {K : Type*} [Field K] [CharP K p] (c : K) :
    (X ^ p - X + C c : K[X]).Separable := by
  refine ⟨0, -1, ?_⟩
  rw [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
    CharP.cast_eq_zero K p, map_zero]
  ring

lemma zmod_cast_smul {B H : Type*} [CommRing B] [CharP B p] [Group H] [MulSemiringAction H B]
    (σ : H) (k : ZMod p) : σ • ZMod.castHom (dvd_refl p) B k = ZMod.castHom (dvd_refl p) B k :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((MulSemiringAction.toRingHom H B σ).comp (ZMod.castHom (dvd_refl p) B))
    (ZMod.castHom (dvd_refl p) B)) k

variable {Γ : Type*} [Group Γ] {G H : Type*} [Group G] [Group H]

/-- If `φ : Γ → G` lifts a surjection `Γ → H` through `π : G → H` whose kernel has prime order
and `φ` is not surjective, then `φ` meets `ker π` trivially: it is determined by `π ∘ φ`. -/
lemma eq_of_not_surjective {p : ℕ} [hp : Fact p.Prime] (π : G →* H) (hcard : Nat.card π.ker = p)
    (φ : Γ →* G) (hφ : Function.Surjective (π.comp φ)) (hns : ¬ Function.Surjective φ)
    {γ δ : Γ} (h : π (φ γ) = π (φ δ)) : φ γ = φ δ := by
  by_contra hne
  have : Finite π.ker := Nat.finite_of_card_ne_zero (hcard ▸ hp.out.ne_zero)
  set K := φ.range ⊓ π.ker
  have hzK : (φ γ)⁻¹ * φ δ ∈ K :=
    ⟨⟨γ⁻¹ * δ, by rw [map_mul, map_inv]⟩, (MonoidHom.mem_ker).mpr (by rw [map_mul, map_inv, h,
      inv_mul_cancel])⟩
  have hK : K ≠ ⊥ := fun hK ↦ hne (by
    have := (Subgroup.mem_bot.mp (hK ▸ hzK))
    rwa [inv_mul_eq_one] at this)
  have hle : K ≤ π.ker := inf_le_right
  have hKeq : K = π.ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard]
    rcases hp.out.eq_one_or_self_of_dvd _ (hcard ▸ Subgroup.card_dvd_of_le hle) with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hK
    · exact h1.ge
  refine hns fun g ↦ ?_
  obtain ⟨γ', hγ'⟩ := hφ (π g)
  have hk : (φ γ')⁻¹ * g ∈ K := by
    rw [hKeq, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, hγ', inv_mul_cancel]
  obtain ⟨⟨γ'', hγ''⟩, -⟩ := hk
  exact ⟨γ' * γ'', by rw [map_mul, hγ'', mul_inv_cancel_left]⟩

end Helpers

end AffineLinePGroups

open AffineLinePGroups

section Lift

open CategoryTheory PreGaloisCategory CommAlgCat ExposeXI

variable (p : ℕ) [hp : Fact p.Prime]



variable {p} in
/-- The Galois covering of a continuous surjection `ψ : π₁(Spec R) → H` (V.5.11, through
`ExposeV.exists_torsorHom_eq`) is connected. -/
lemma isConnected_of_torsorHom (R : Type u) [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] {H : Type u} [Group H]
    [TopologicalSpace H]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    {P : (FiniteEtale.{u} R)ᵒᵖ} {α : H →* (Aut P)ᵐᵒᵖ}
    (hα : ExposeV.IsPrincipalHomogeneous (ExposeV.fiberFunctor R Ω) α)
    (x₀ : (ExposeV.fiberFunctor R Ω).obj P) (hx₀ : ExposeV.torsorHom hα x₀ = ψ.toMonoidHom) :
    IsConnected P := by
  let F := ExposeV.fiberFunctor R Ω
  have : Nonempty (F.obj P) := ⟨x₀⟩
  have htrans : ∀ y : F.obj P, ∃ τ : Aut F, τ • x₀ = y := by
    intro y
    obtain ⟨σ, hσ, -⟩ := hα x₀ y
    obtain ⟨τ, rfl⟩ := hψ σ
    refine ⟨τ, ?_⟩
    rw [← hσ, ← ExposeV.torsorHom_spec hα x₀ τ, hx₀]
    rfl
  have : MulAction.IsPretransitive (Aut F) (F.obj P) := ⟨fun x y ↦ by
    obtain ⟨τx, rfl⟩ := htrans x
    obtain ⟨τy, rfl⟩ := htrans y
    exact ⟨τy * τx⁻¹, by rw [smul_smul, inv_mul_cancel_right]⟩⟩
  exact ExposeV.isConnected_of_isPretransitive F P

variable {p} in
/-- The Galois algebra of a continuous surjection `ψ : π₁(Spec R) → H` is nontrivial and its only
idempotents are `0` and `1` (its spectrum is connected). -/
lemma galoisAlgebra_nontrivial_and_idempotent (R : Type u) [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] {H : Type u} [Group H]
    [TopologicalSpace H]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    {P : (FiniteEtale.{u} R)ᵒᵖ} {α : H →* (Aut P)ᵐᵒᵖ}
    (hα : ExposeV.IsPrincipalHomogeneous (ExposeV.fiberFunctor R Ω) α)
    (x₀ : (ExposeV.fiberFunctor R Ω).obj P) (hx₀ : ExposeV.torsorHom hα x₀ = ψ.toMonoidHom) :
    Nontrivial P.unop.obj ∧ (∀ e : P.unop.obj, IsIdempotentElem e → e = 0 ∨ e = 1) :=
  (ExposeV.isConnected_op_iff R P.unop).mp (isConnected_of_torsorHom R Ω ψ hψ hα x₀ hx₀)

/-- Elements of Chase–Harrison–Rosenberg for the Galois algebra `A` of a continuous surjection
onto `H` (`H` acting through `ρH`, simply transitively on the points of `A`, and `A` without
non-trivial idempotents): `∑ xᵢ yᵢ = 1` and `∑ xᵢ ρH(σ)(yᵢ) = 0` for `σ ≠ 1`. The action is
faithful, so the inertia groups are trivial (V.2.4). -/
lemma galoisAlgebra_exists_galois_elements (R : Type u) [CommRing R]
    (Ω : Type u) [Field Ω] [Algebra R Ω] {H : Type u} [Group H] [Finite H]
    (A : FiniteEtale.{u} R) (ρH : H →* (A.obj ≃ₐ[R] A.obj)) (x₀ : A.obj →ₐ[R] Ω)
    (hH : ∀ x y : A.obj →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y)
    (hidem : ∀ e : A.obj, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∃ (n : ℕ) (x y : Fin n → A.obj), ∑ i, x i * y i = 1 ∧
      ∀ σ : H, σ ≠ 1 → ∑ i, x i * ρH σ (y i) = 0 := by
  let : MulSemiringAction H A.obj := MulSemiringAction.compHom A.obj ρH
  have hsmul : ∀ (σ : H) (b : A.obj), σ • b = ρH σ b := fun _ _ ↦ rfl
  have : SMulCommClass H R A.obj := ⟨fun σ r b ↦ by rw [hsmul, hsmul, map_smul]⟩
  have hfaith : ∀ σ : H, (∀ b : A.obj, σ • b = b) → σ = 1 := by
    intro σ hσ
    refine (hH x₀ x₀).unique (AlgHom.ext fun b ↦ ?_) (AlgHom.ext fun b ↦ ?_)
    · change x₀ (σ • b) = x₀ b
      rw [hσ]
    · change x₀ (ρH 1 b) = x₀ b
      rw [map_one, AlgEquiv.one_apply]
  exact exists_galois_elements_of_faithful (R := R) hidem hfaith

/-- An element of trace one for the Galois algebra of a continuous surjection onto `H`. -/
lemma galoisAlgebra_exists_sum_smul_eq_one (R : Type u) [CommRing R]
    (Ω : Type u) [Field Ω] [Algebra R Ω] {H : Type u} [Group H] [Fintype H]
    (A : FiniteEtale.{u} R) (ρH : H →* (A.obj ≃ₐ[R] A.obj)) (x₀ : A.obj →ₐ[R] Ω)
    (hH : ∀ x y : A.obj →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y)
    (hidem : ∀ e : A.obj, IsIdempotentElem e → e = 0 ∨ e = 1) :
    letI := MulSemiringAction.compHom A.obj ρH
    ∃ θ : A.obj, ∑ h : H, h • θ = 1 := by
  let : MulSemiringAction H A.obj := MulSemiringAction.compHom A.obj ρH
  obtain ⟨n, x, y, h1, h2⟩ := galoisAlgebra_exists_galois_elements R Ω A ρH x₀ hH hidem
  exact exists_sum_smul_eq_one_of_galois_elements h1 h2

/-- The last step of the lifting construction (V.5.11): a principal homogeneous `G`-covering
`A'` over the Galois `H`-covering `A` of `ψ`, compatible with `π : G → H` and with a point over
the base point, defines a continuous lift `ψ' : π₁ → G` of `ψ`. If moreover `ker ψ ⊆ ker ψ'`, the
covering `A'` is dominated by `A`: there is an `A`-algebra map `A' → A`. -/
theorem exists_lift_of_principal' (R : Type u) [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] {H G : Type u} [Group H] [Group G]
    [TopologicalSpace H] [TopologicalSpace G] [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    (π : G →* H) {P : (FiniteEtale.{u} R)ᵒᵖ} {α : H →* (Aut P)ᵐᵒᵖ}
    (hα : ExposeV.IsPrincipalHomogeneous (ExposeV.fiberFunctor R Ω) α)
    (x₀ : (ExposeV.fiberFunctor R Ω).obj P) (hx₀ : ExposeV.torsorHom hα x₀ = ψ.toMonoidHom)
    (A' : FiniteEtale.{u} R) (incl : P.unop.obj →ₐ[R] A'.obj)
    (ρG : G →* (A'.obj ≃ₐ[R] A'.obj))
    (hcompat : ∀ g, (ρG g).toAlgHom.comp incl =
      incl.comp ((autOpMulEquivAlgEquiv P.unop) (α (π g))).toAlgHom)
    (hprinc : ∀ x y : A'.obj →ₐ[R] Ω, ∃! g : G, x.comp (ρG g).toAlgHom = y)
    (x₀' : A'.obj →ₐ[R] Ω) (hx₀' : x₀'.comp incl = x₀) :
    ∃ ψ' : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G,
      π.comp ψ'.toMonoidHom = ψ.toMonoidHom ∧
      (ψ.toMonoidHom.ker ≤ ψ'.toMonoidHom.ker →
        ∃ φ : A'.obj →ₐ[R] P.unop.obj, φ.comp incl = AlgHom.id R _) := by
  let F := ExposeV.fiberFunctor R Ω
  let α' : G →* (Aut (Opposite.op A'))ᵐᵒᵖ := (autOpMulEquivAlgEquiv A').symm.toMonoidHom.comp ρG
  have hα' : ExposeV.IsPrincipalHomogeneous F α' := hprinc
  let i : Opposite.op A' ⟶ P :=
    (ObjectProperty.homMk (CommAlgCat.ofHom incl) : P.unop ⟶ A').op
  let y₀ : F.obj (Opposite.op A') := x₀'
  have hi : F.map i y₀ = x₀ := hx₀'
  refine ⟨⟨ExposeV.torsorHom hα' x₀', ExposeV.continuous_torsorHom hα' x₀'⟩,
    MonoidHom.ext fun τ ↦ ?_, fun hker ↦ ?_⟩
  · change π (ExposeV.torsorHom hα' x₀' τ) = ψ.toMonoidHom τ
    rw [← hx₀]
    symm
    rw [ExposeV.torsorHom_eq_iff]
    set g := ExposeV.torsorHom hα' x₀' τ
    have hspec := ExposeV.torsorHom_spec hα' x₀' τ
    calc F.map (α (π g)).unop.hom x₀ = F.map (α (π g)).unop.hom (F.map i y₀) := by rw [hi]
      _ = F.map i (F.map (α' g).unop.hom y₀) := by
          change (x₀'.comp incl).comp ((autOpMulEquivAlgEquiv P.unop) (α (π g))).toAlgHom =
            (x₀'.comp (ρG g).toAlgHom).comp incl
          rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hcompat]
      _ = F.map i (τ • y₀) := by rw [hspec]
      _ = τ • F.map i y₀ := (mulAction_naturality F τ i y₀).symm
      _ = τ • x₀ := by rw [hi]
  · have hP := isConnected_of_torsorHom R Ω ψ hψ hα x₀ hx₀
    have hstab : MulAction.stabilizer (Aut F) x₀ ≤ MulAction.stabilizer (Aut F) y₀ := by
      intro τ hτ
      have h1 : ψ τ = 1 := by
        change ψ.toMonoidHom τ = 1
        rw [← hx₀, ExposeV.torsorHom_eq_iff, map_one]
        exact (congrArg (fun f ↦ F.map f x₀) (show (MulOpposite.unop (1 : (Aut P)ᵐᵒᵖ)).hom =
          𝟙 P from rfl)).trans (by rw [F.map_id]; exact (MulAction.mem_stabilizer_iff.mp hτ).symm)
      have h2 : ExposeV.torsorHom hα' x₀' τ = 1 := hker (MonoidHom.mem_ker.mpr h1)
      rw [MulAction.mem_stabilizer_iff, ← ExposeV.torsorHom_spec hα' x₀' τ, h2, map_one]
      exact congrArg (fun f ↦ F.map f y₀)
        (show (MulOpposite.unop (1 : (Aut (Opposite.op A'))ᵐᵒᵖ)).hom = 𝟙 _ from rfl) |>.trans
          (by rw [F.map_id]; rfl)
    obtain ⟨f, hf⟩ := exists_hom_of_stabilizer_le F x₀ y₀ hstab
    have hfi : f ≫ i = 𝟙 P := by
      apply evaluation_injective_of_isConnected F P P x₀
      change F.map (f ≫ i) x₀ = F.map (𝟙 P) x₀
      rw [F.map_comp, FintypeCat.comp_apply, hf, hi, F.map_id]
      rfl
    refine ⟨f.unop.hom.hom, ?_⟩
    have := congrArg (fun g ↦ g.unop.hom.hom) hfi
    exact this

/-- The last step of the lifting construction (V.5.11), without the domination statement. -/
theorem exists_lift_of_principal (R : Type u) [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] {H G : Type u} [Group H] [Group G]
    [TopologicalSpace H] [TopologicalSpace G] [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    (π : G →* H) {P : (FiniteEtale.{u} R)ᵒᵖ} {α : H →* (Aut P)ᵐᵒᵖ}
    (hα : ExposeV.IsPrincipalHomogeneous (ExposeV.fiberFunctor R Ω) α)
    (x₀ : (ExposeV.fiberFunctor R Ω).obj P) (hx₀ : ExposeV.torsorHom hα x₀ = ψ.toMonoidHom)
    (A' : FiniteEtale.{u} R) (incl : P.unop.obj →ₐ[R] A'.obj)
    (ρG : G →* (A'.obj ≃ₐ[R] A'.obj))
    (hcompat : ∀ g, (ρG g).toAlgHom.comp incl =
      incl.comp ((autOpMulEquivAlgEquiv P.unop) (α (π g))).toAlgHom)
    (hprinc : ∀ x y : A'.obj →ₐ[R] Ω, ∃! g : G, x.comp (ρG g).toAlgHom = y)
    (x₀' : A'.obj →ₐ[R] Ω) (hx₀' : x₀'.comp incl = x₀) :
    ∃ ψ' : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G,
      π.comp ψ'.toMonoidHom = ψ.toMonoidHom :=
  (exists_lift_of_principal' R Ω ψ hψ π hα x₀ hx₀ A' incl ρG hcompat hprinc x₀' hx₀').imp
    fun _ h ↦ h.1

/-- Weak solvability of central `ℤ/p` embedding problems for `π₁(Spec R)` (the concrete form of
`cd_p ≤ 1` in characteristic `p`): let `R` be a ring of characteristic `p` with connected
spectrum, `R → Ω` a geometric point and `π = Aut F` for the fibre functor `F` of finite étale
`R`-algebras. If `ψ : π → H` is a continuous surjection and `G → H` is a surjection whose kernel
is central of order `p`, then `ψ` lifts to a continuous homomorphism `π → G`.

The lift is the Artin–Schreier covering `B[T]/(Tᵖ - T + a)` of the Galois algebra `B` of `ψ`,
with `a` chosen so that `G` acts on it by semilinear automorphisms. -/
theorem exists_lift_of_central_ker (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    {H G : Type u} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G]
    [TopologicalSpace G] [DiscreteTopology G]
    (ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H) (hψ : Function.Surjective ψ)
    (π : G →* H) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hcard : Nat.card π.ker = p) :
    ∃ ψ' : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G,
      π.comp ψ'.toMonoidHom = ψ.toMonoidHom := by
  classical
  have : CharP Ω p := charP_of_algebra p R Ω
  obtain ⟨P, α, hα, x₀, hx₀⟩ := ExposeV.exists_torsorHom_eq
    (F := ExposeV.fiberFunctor R Ω) ψ.toMonoidHom ψ.continuous
  let A := P.unop
  let ρH : H →* (A.obj ≃ₐ[R] A.obj) := (autOpMulEquivAlgEquiv A).toMonoidHom.comp α
  have hH : ∀ x y : A.obj →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y := hα
  let x₀a : A.obj →ₐ[R] Ω := x₀
  obtain ⟨hnt, hidem⟩ := galoisAlgebra_nontrivial_and_idempotent R Ω ψ hψ hα x₀ hx₀
  have : CharP A.obj p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap R A.obj), CharP.cast_eq_zero, map_zero])
  have : Fintype H := Fintype.ofFinite H
  let : MulSemiringAction H A.obj := MulSemiringAction.compHom A.obj ρH
  obtain ⟨θ, hθ⟩ := galoisAlgebra_exists_sum_smul_eq_one R Ω A ρH x₀a hH hidem
  -- the section and the character of the kernel
  choose s hs using hπ
  have : Fact (Nat.card π.ker).Prime := ⟨hcard ▸ hp.out⟩
  have : IsCyclic π.ker := isCyclic_of_prime_card rfl
  have : IsCyclic (Multiplicative (ZMod p)) := inferInstance
  let e : π.ker ≃* Multiplicative (ZMod p) := mulEquivOfCyclicCardEq (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let χ : G → ZMod p := fun g ↦ if h : g ∈ π.ker then Multiplicative.toAdd (e ⟨g, h⟩) else 0
  have hχ : ∀ z (hz : z ∈ π.ker), χ z = Multiplicative.toAdd (e ⟨z, hz⟩) := fun z hz ↦ by
    simp only [χ]
    split_ifs
    rfl
  let κ : G → A.obj := fun g ↦ ZMod.castHom (dvd_refl p) A.obj (χ g)
  have hκ : ∀ z ∈ π.ker, ∀ w ∈ π.ker, κ (z * w) = κ z + κ w := by
    intro z hz w hw
    simp only [κ]
    rw [hχ _ (mul_mem hz hw), hχ z hz, hχ w hw, ← map_add, ← toAdd_mul, ← map_mul]
    rfl
  have hκc : ∀ g, ∀ z ∈ π.ker, κ (g * z * g⁻¹) = π g • κ z := by
    intro g z hz
    rw [Subgroup.mem_center_iff.mp (hker hz) g, mul_inv_cancel_right]
    exact (zmod_cast_smul p _ _).symm
  have hκp : ∀ z ∈ π.ker, κ z ^ p = κ z := fun z _ ↦ ArtinSchreier.castHom_pow p _
  obtain ⟨a, ha⟩ := exists_liftCochain_pow_sub p π s hs κ hθ hκ hκc hκp
  set u := liftCochain π s κ θ
  have hmul : ∀ g h, u (g * h) = (ρH.comp π) g (u h) + u g :=
    liftCochain_mul smul_mul_eq_smul_smul π s hs κ hκ hκc
  have hu : ∀ g, u g ^ p - u g = a - (ρH.comp π) g a := ha
  -- the Artin–Schreier covering `B'` and its `G`-action
  have := ArtinSchreier.etale hp.out (CharP.cast_eq_zero A.obj p) a
  have : Algebra.Etale R (ArtinSchreierAlgebra A.obj p a) := Algebra.Etale.comp R A.obj _
  have : Module.Finite R (ArtinSchreierAlgebra A.obj p a) := Module.Finite.trans A.obj _
  let A' : FiniteEtale.{u} R := FiniteEtale.of R (ArtinSchreierAlgebra A.obj p a)
  -- a geometric point of `B'` over `x₀`
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root (X ^ p - X + C (x₀a a) : Polynomial Ω) (by
      rw [degree_eq_natDegree (ArtinSchreier.monic hp.out _).ne_zero,
        ArtinSchreier.natDegree_eq hp.out]
      exact_mod_cast hp.out.ne_zero)
    (separable_artinSchreier p _)
  have hev : (X ^ p - X + C a : A.obj[X]).eval₂ (x₀a : A.obj →+* Ω) r = 0 := by
    rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simpa using hr
  exact exists_lift_of_principal R Ω ψ hψ π hα x₀ hx₀ A' (artinSchreierInclusion p a)
    (semilinearAut p (ρH.comp π) a u hu hmul)
    (fun g ↦ semilinearHom_comp_inclusion p (ρH.comp π) a u hu g)
    (fun x y ↦ existsUnique_comp_semilinearAut p ρH π a u hu hmul Ω hH (fun σ ↦ ⟨s σ, hs σ⟩) χ
      (fun z hz ↦ liftCochain_of_mem_ker π s κ hθ hz) (fun z hz h0 ↦ by
        rw [hχ z hz, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff,
          MulEquiv.map_eq_one_iff] at h0
        exact congrArg Subtype.val h0)
      (fun k ↦ ⟨(e.symm (Multiplicative.ofAdd k) : G), (e.symm _).2, by
        rw [hχ _ (e.symm _).2]
        simp⟩) x y)
    (AdjoinRoot.liftAlgHom _ x₀a r hev) (AlgHom.ext fun b ↦ AdjoinRoot.liftAlgHom_of _ x₀a r hev b)

end Lift


section Twist

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {G H : Type*} [Group G] [Group H]

variable [TopologicalSpace G] [DiscreteTopology G] [Finite H] {Z : Type*} [Group Z] [Finite Z]
  [TopologicalSpace Z] [DiscreteTopology Z]

/-- The twist that turns a lift into a surjective lift: if `Hom_cont(Γ, Z)` is infinite, where `Z`
maps isomorphically onto the central kernel (of prime order) of `π : G → H`, and `φ₀ : Γ → G`
lifts a continuous surjection `ψ : Γ → H`, then some `φ₀ · (ι ∘ χ)` is a surjective lift. -/
theorem exists_surjective_lift_of_central {p : ℕ} [Fact p.Prime]
    (hinf : Infinite (ContinuousMonoidHom Γ Z)) (ψ : Γ →* H) (hψ : Function.Surjective ψ)
    (π : G →* H) (hcard : Nat.card π.ker = p) (ι : Z →* G) (hι : Function.Injective ι)
    (hιc : ∀ z g, ι z * g = g * ι z) (hιker : ∀ z, π (ι z) = 1)
    (φ₀ : ContinuousMonoidHom Γ G) (hφ₀ : π.comp φ₀.toMonoidHom = ψ) :
    ∃ φ : ContinuousMonoidHom Γ G, Function.Surjective φ ∧ π.comp φ.toMonoidHom = ψ := by
  classical
  let twist : ContinuousMonoidHom Γ Z → ContinuousMonoidHom Γ G := fun χ ↦
    { toFun := fun γ ↦ φ₀ γ * ι (χ γ)
      map_one' := by simp
      map_mul' := fun γ δ ↦ by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (ι (χ γ)), hιc (χ γ) (φ₀ δ), mul_assoc]
      continuous_toFun := φ₀.continuous.mul
        ((continuous_of_discreteTopology (f := ι)).comp χ.continuous) }
  have htwist : ∀ χ, π.comp (twist χ).toMonoidHom = ψ := fun χ ↦ by
    ext γ
    change π (φ₀ γ * ι (χ γ)) = ψ γ
    rw [map_mul, hιker, mul_one, ← hφ₀]
    rfl
  by_contra hcon
  push Not at hcon
  have hbad : ∀ χ, ¬ Function.Surjective (twist χ) := fun χ hs ↦ hcon _ hs (htwist χ)
  -- every `χ` factors through `ψ`
  have hfac : ∀ (χ : ContinuousMonoidHom Γ Z) γ δ, ψ γ = ψ δ → χ γ = χ δ := by
    intro χ γ δ h
    have hsurj : ∀ φ : ContinuousMonoidHom Γ G, π.comp φ.toMonoidHom = ψ →
        Function.Surjective (π.comp φ.toMonoidHom) := fun φ hφ ↦ hφ ▸ hψ
    have h₀ := eq_of_not_surjective π hcard φ₀.toMonoidHom (hsurj φ₀ hφ₀)
      (fun hs ↦ hcon φ₀ hs hφ₀) (γ := γ) (δ := δ) (by
        rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hφ₀, h])
    have h₁ := eq_of_not_surjective π hcard (twist χ).toMonoidHom (hsurj _ (htwist χ)) (hbad χ)
      (γ := γ) (δ := δ) (by rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, htwist, h])
    change φ₀ γ * ι (χ γ) = φ₀ δ * ι (χ δ) at h₁
    change φ₀ γ = φ₀ δ at h₀
    rw [h₀, mul_left_cancel_iff] at h₁
    exact hι h₁
  choose s hs using hψ
  have hinj : Function.Injective fun χ : ContinuousMonoidHom Γ Z ↦ fun h ↦ χ (s h) := by
    intro χ χ' he
    ext γ
    rw [hfac χ γ (s (ψ γ)) (hs _).symm, hfac χ' γ (s (ψ γ)) (hs _).symm]
    exact congrFun he (ψ γ)
  have := Finite.of_injective _ hinj
  exact _root_.not_finite (ContinuousMonoidHom Γ Z)

end Twist

section Realization

open CategoryTheory PreGaloisCategory CommAlgCat

variable (p : ℕ) [hp : Fact p.Prime]

/-- Central `ℤ/p`-extensions of continuous quotients of `π₁(Spec R)` are continuous quotients,
when `π₁(Spec R)` has infinitely many continuous homomorphisms to `ℤ/p` (for instance
`R = k[T]`, `infinite_continuousMonoidHom_aut_fiberFunctor`). -/
theorem exists_surjective_of_ker_le_center_of_card_eq (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (hinf : Infinite (ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) (DiscreteZMod.{u} p)))
    {H G : Type u} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G]
    [TopologicalSpace G] [DiscreteTopology G] (π : G →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hcard : Nat.card π.ker = p)
    (hH : ∃ ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H, Function.Surjective ψ) :
    ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G, Function.Surjective φ := by
  obtain ⟨ψ, hψ⟩ := hH
  obtain ⟨φ₀, hφ₀⟩ := exists_lift_of_central_ker p R Ω ψ hψ π hπ hker hcard
  have : Fact (Nat.card π.ker).Prime := ⟨hcard ▸ hp.out⟩
  have : IsCyclic π.ker := isCyclic_of_prime_card rfl
  let e : π.ker ≃* Multiplicative (ZMod p) := mulEquivOfCyclicCardEq (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let ι : DiscreteZMod.{u} p →* G :=
    π.ker.subtype.comp (e.symm.toMonoidHom.comp (DiscreteZMod.equiv.{u} p).toMonoidHom)
  have hι : Function.Injective ι := fun z w h ↦ (DiscreteZMod.equiv.{u} p).injective
    (e.symm.injective (Subtype.ext h))
  have hιker : ∀ z, π (ι z) = 1 := fun z ↦ (e.symm _).2
  have hιc : ∀ z g, ι z * g = g * ι z := fun z g ↦
    (Subgroup.mem_center_iff.mp (hker (e.symm _).2) g).symm
  obtain ⟨φ, hφ, -⟩ := exists_surjective_lift_of_central hinf ψ.toMonoidHom hψ π hcard ι hι hιc
    hιker φ₀ hφ₀
  exact ⟨φ, hφ⟩


/-- Extensions by central `p`-groups of continuous quotients of `π₁(Spec R)` are continuous
quotients, when `π₁(Spec R)` has infinitely many continuous homomorphisms to `ℤ/p`. -/
theorem exists_surjective_of_ker_le_center_of_isPGroup (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (hinf : Infinite (ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) (DiscreteZMod.{u} p)))
    {H : Type u} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (hH : ∃ ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) H, Function.Surjective ψ)
    (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G) (hpk : IsPGroup p π.ker) :
    ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G, Function.Surjective φ := by
  suffices h : ∀ n (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
      (π : G →* H), Nat.card G = n → Function.Surjective π → π.ker ≤ Subgroup.center G →
      IsPGroup p π.ker →
      ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G, Function.Surjective φ from
    h _ G π rfl hπ hker hpk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ _ π hn hπ hker hpk
  by_cases hN : π.ker = ⊥
  · let eπ := MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hN, hπ⟩
    obtain ⟨ψ, hψ⟩ := hH
    exact ⟨⟨eπ.symm.toMonoidHom.comp ψ.toMonoidHom,
      (continuous_of_discreteTopology (f := eπ.symm)).comp ψ.continuous⟩,
      eπ.symm.surjective.comp hψ⟩
  · have : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hN
    obtain ⟨m, hm, hcardN⟩ := hpk.nontrivial_iff_card.mp this
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p (by
      rw [hcardN]
      exact dvd_pow_self p hm.ne')
    let Z := Subgroup.zpowers (z : G)
    have hZker : Z ≤ π.ker := (Subgroup.zpowers_le).mpr z.2
    have hZc : Z ≤ Subgroup.center G := hZker.trans hker
    have : Z.Normal := ⟨fun x hx g ↦ by
      rw [Subgroup.mem_center_iff.mp (hZc hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hZcard : Nat.card Z = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
    let : TopologicalSpace (G ⧸ Z) := ⊥
    have : DiscreteTopology (G ⧸ Z) := ⟨rfl⟩
    let π' : G ⧸ Z →* H := QuotientGroup.lift Z π hZker
    have hπ' : Function.Surjective π' := by
      intro h
      obtain ⟨g, rfl⟩ := hπ h
      exact ⟨QuotientGroup.mk g, rfl⟩
    have hmem : ∀ g : G, (g : G ⧸ Z) ∈ π'.ker ↔ g ∈ π.ker := fun g ↦ Iff.rfl
    have hker' : π'.ker ≤ Subgroup.center (G ⧸ Z) := by
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Subgroup.mem_center_iff]
      intro q'
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp (hker ((hmem g).mp hq)) g']
    have hpk' : IsPGroup p π'.ker := by
      intro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := hpk ⟨g, (hmem g).mp hq⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have hlt : Nat.card (G ⧸ Z) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZcard]
      have : 0 < Nat.card (G ⧸ Z) := Nat.card_pos
      nlinarith [hp.out.two_le]
    have hG' := ih _ hlt (G ⧸ Z) π' rfl hπ' hker' hpk'
    exact exists_surjective_of_ker_le_center_of_card_eq p R Ω hinf (QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z) (by rw [QuotientGroup.ker_mk']; exact hZc)
      (by rw [QuotientGroup.ker_mk']; exact hZcard) hG'

/-- Every finite `p`-group is a continuous quotient of `π₁(Spec R)`, when `π₁(Spec R)` has
infinitely many continuous homomorphisms to `ℤ/p`. -/
theorem exists_surjective_of_isPGroup_of_infinite (R : Type u) [CommRing R] [CharP R p]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (hinf : Infinite (ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) (DiscreteZMod.{u} p)))
    (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (hG : IsPGroup p G) :
    ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G, Function.Surjective φ := by
  suffices h : ∀ n (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G],
      Nat.card G = n → IsPGroup p G →
      ∃ φ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) G, Function.Surjective φ from
    h _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ _ hn hG
  rcases subsingleton_or_nontrivial G with hs | hnt
  · exact ⟨1, fun g ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  · have := hG.center_nontrivial
    let : TopologicalSpace (G ⧸ Subgroup.center G) := ⊥
    have : DiscreteTopology (G ⧸ Subgroup.center G) := ⟨rfl⟩
    have hlt : Nat.card (G ⧸ Subgroup.center G) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)]
      have : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
      have : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
      nlinarith
    have hQ := ih _ hlt (G ⧸ Subgroup.center G) rfl (hG.to_quotient _)
    exact exists_surjective_of_ker_le_center_of_isPGroup p R Ω hinf hQ G
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hG.to_subgroup _)
end Realization

section AffineLine

open CategoryTheory AlgebraicGeometry

/-- Continuous surjections onto `G` transport along an isomorphism of topological groups. -/
lemma AffineLinePGroups.exists_surjective_of_continuousMulEquiv {Γ Γ' G : Type*} [Group Γ]
    [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [Group G] [TopologicalSpace G]
    (e : Γ ≃ₜ* Γ')
    (h : ∃ φ : ContinuousMonoidHom Γ G, Function.Surjective φ) :
    ∃ φ : ContinuousMonoidHom Γ' G, Function.Surjective φ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm), hφ.comp e.symm.surjective⟩

/-- For a ring `R` with connected spectrum and a geometric point `x` of `Spec R`, `π₁(Spec R, x)`
is the automorphism group of the fibre functor of finite étale `R`-algebras at `x` (V.7), as a
topological group. -/
noncomputable def fundamentalGroupSpecContinuousMulEquiv (R : Type u) [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of R)) :
    letI := ExposeV.algebraOfPoint (CommRingCat.of R) Ω x
    Aut (ExposeV.fiberFunctor R Ω) ≃ₜ* FundamentalGroup x :=
  letI := ExposeV.algebraOfPoint (CommRingCat.of R) Ω x
  ExposeV.autContinuousMulEquiv (ExposeV.specEquivalence (CommRingCat.of R)).inverse
    (ExposeV.FEt.fiberSpecIso (CommRingCat.of R) Ω x).symm

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ Spec (.of k[X]))

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- XIII.2.13, the case of `p`-groups: over a field `k` of characteristic `p` (algebraically
closed in SGA; no hypothesis on `k` is needed here), every finite `p`-group is the Galois group of
a connected étale covering of `𝔸¹_k`, i.e. a continuous quotient of `π₁(𝔸¹_k, x)`. -/
theorem exists_surjective_fundamentalGroup_affineLine_of_isPGroup (G : Type u) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (hG : IsPGroup p G) :
    ∃ φ : ContinuousMonoidHom (FundamentalGroup x) G, Function.Surjective φ := by
  let := ExposeV.algebraOfPoint (CommRingCat.of k[X]) Ω x
  exact exists_surjective_of_continuousMulEquiv (fundamentalGroupSpecContinuousMulEquiv k[X] Ω x)
    (exists_surjective_of_isPGroup_of_infinite p k[X] Ω
      (infinite_continuousMonoidHom_aut_fiberFunctor p k Ω) G hG)

/-- XIII.2.13 (towards Abhyankar's conjecture for `𝔸¹`): over a field `k` of characteristic `p`,
the finite continuous quotients of `π₁(𝔸¹_k, x)` are closed under extensions by central
`p`-groups: if `H` is a quotient and `G → H` is onto with kernel a central `p`-subgroup, then
`G` is a quotient. -/
theorem exists_surjective_fundamentalGroup_affineLine_of_ker_le_center {H G : Type u} [Group H]
    [Finite H] [TopologicalSpace H] [DiscreteTopology H] [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] (π : G →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hpk : IsPGroup p π.ker)
    (hH : ∃ ψ : ContinuousMonoidHom (FundamentalGroup x) H, Function.Surjective ψ) :
    ∃ φ : ContinuousMonoidHom (FundamentalGroup x) G, Function.Surjective φ := by
  let := ExposeV.algebraOfPoint (CommRingCat.of k[X]) Ω x
  exact exists_surjective_of_continuousMulEquiv (fundamentalGroupSpecContinuousMulEquiv k[X] Ω x)
    (exists_surjective_of_ker_le_center_of_isPGroup p k[X] Ω
      (infinite_continuousMonoidHom_aut_fiberFunctor p k Ω)
      (exists_surjective_of_continuousMulEquiv
        (fundamentalGroupSpecContinuousMulEquiv k[X] Ω x).symm hH)
      G π hπ hker hpk)

/-- XIII.2.13, Abhyankar's conjecture for the affine line (`AbhyankarAffineLineStatement`) for
`p`-groups `G`: `G` is a continuous quotient of `π₁(𝔸¹_k, x)` iff `G^{(p')} = 1` (both hold). -/
theorem abhyankarAffineLine_of_isPGroup [IsAlgClosed k] (G : Type u) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (hG : IsPGroup p G) :
    (∃ φ : ContinuousMonoidHom (FundamentalGroup x) G, Function.Surjective φ) ↔
      sylowSup p G = ⊤ :=
  ⟨fun ⟨φ, hφ⟩ ↦ sylowSup_eq_top_of_affineLine p k Ω x G φ hφ,
    fun _ ↦ exists_surjective_fundamentalGroup_affineLine_of_isPGroup k Ω x p G hG⟩
end AffineLine

end SGA.SGA1.ExposeXIII
