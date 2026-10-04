/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristicGeneric
import SGA.Foundations.Cohomology.EulerCharacteristicClopen
import SGA.Foundations.Cohomology.EulerCharacteristicFiniteEtale
import SGA.Foundations.Cohomology.ThickeningReduction

/-!
# Multiplicativity of the Euler characteristic in finite étale coverings

Let `X` be proper over a field `k` and `π : Y ⟶ X` finite étale whose geometric fibres all have
`d` points (`Scheme.Hom.geometricFiberCard`). Then `χ(Y, π^* F) = d · χ(X, F)` for every coherent
`F` (`Scheme.Modules.eulerChar_pullback_eq_mul`), in particular `χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)`
(`eulerCharFiniteEtaleStatement`), in every characteristic and without Riemann–Roch.

The proof is by induction on `d`, by dévissage (EGA III 3.1.2; Stacks Tag 01YF):

* `d = 0`: `Y` is empty.
* `χ(Y, π^* π_* H) = d · χ(Y, H)` (`eulerChar_pullback_pushforward_self`): by affine base change,
  `χ(Y, π^* π_* H) = χ(Y ×_X Y, p₁^* H)`, and `Y ×_X Y` is the disjoint union of the diagonal and
  of its complement, whose first projection to `Y` is finite étale of degree `d - 1`
  (`Scheme.Hom.geometricFiberCard_diagonalComplFst_add_one`).
* Both sides of `χ(Y, π^* F) = d · χ(X, F)` are additive in `F`; for `F = ι_* G` with
  `ι : Z ⟶ X` an integral closed subscheme they are the two sides for the base change
  `Z ×_X Y ⟶ Z`, and on an integral `Z` the difference is `rk(G)` times its value on `𝒪_Z`
  (`CohomologyAux.exists_additive_eq_mul_unitModule`), which vanishes since `p_* 𝒪` has positive
  rank `r` and `r` times it is `0` by the previous step
  (`eulerChar_pullback_eq_mul_of_isIntegral`, `eulerChar_pullback_eq_mul_of_pushforwardUnit`).

## References

* [EGA III, 3.1.2][ega-iii-1]
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open CohomologyAux

namespace Scheme.Modules

variable {k : Type u} [Field k]

/-- A zero module has Euler characteristic `0`. -/
lemma eulerChar_eq_zero_of_isZero {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (M : X.Modules) [hc : M.IsCoherent] (hM : IsZero M) : eulerChar f M = 0 := by
  have hS : (ShortComplex.mk (0 : M ⟶ M) (0 : M ⟶ M) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hM
      mono_f := ⟨fun g h _ ↦ hM.eq_of_tgt g h⟩
      epi_g := ⟨fun g h _ ↦ hM.eq_of_src g h⟩ }
  have h := @eulerChar_of_shortExact k _ X f _
    (ShortComplex.mk (0 : M ⟶ M) (0 : M ⟶ M) (by simp)) hS hc hc hc
  exact add_eq_left.mp h.symm

/-- A module with no nonzero section is a zero object. -/
lemma isZero_of_forall_eq_zero {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ (V : X.Opens) (s : Γ(M, V)), s = 0) : IsZero M :=
  (IsZero.iff_id_eq_zero M).mpr (Scheme.Modules.hom_ext _ _ fun V ↦ by
    ext s
    exact hM V s)

end Scheme.Modules

open Scheme.Modules

section Diagonal

variable {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Etale π]

/-- The first projection `Y ×_X Y ∖ Δ ⟶ Y`. -/
noncomputable abbrev Scheme.Hom.diagonalComplFst : (π.diagonalCompl : Scheme) ⟶ Y :=
  π.diagonalCompl.ι ≫ pullback.fst π π

/-- For `π` unramified, the complement of the (open) diagonal is closed in `Y ×_X Y`. -/
lemma Scheme.Hom.isClosedImmersion_diagonalCompl_ι : IsClosedImmersion π.diagonalCompl.ι := by
  have := FormallyUnramified.isOpenImmersion_diagonal π
  exact .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (pullback.diagonal π).isOpenEmbedding.isOpen_range.isClosed_compl)

/-- `Y ×_X Y` is the disjoint union of the diagonal and of its complement. -/
lemma Scheme.Hom.isCompl_opensRange_diagonal_diagonalCompl :
    IsCompl (pullback.diagonal π).opensRange π.diagonalCompl.ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · rw [disjoint_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange, Set.mem_inter_iff,
      Set.mem_range, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨y, rfl⟩, h⟩
    exact h ⟨y, rfl⟩
  · rw [codisjoint_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, Scheme.Hom.coe_opensRange, Set.mem_union,
      Set.mem_range, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    by_cases h : x ∈ Set.range (pullback.diagonal π)
    · exact Or.inl h
    · exact Or.inr h

instance : IsFinite π.diagonalComplFst := by
  have := π.isClosedImmersion_diagonalCompl_ι
  infer_instance

instance : Etale π.diagonalComplFst := by
  infer_instance

/-- The swap of the factors of `Y ×_X Y`, restricted to the complement of the diagonal. -/
noncomputable def Scheme.Hom.diagonalComplSwap : (π.diagonalCompl : Scheme) ⟶ π.diagonalCompl :=
  IsOpenImmersion.lift π.diagonalCompl.ι (π.diagonalCompl.ι ≫ (pullbackSymmetry π π).hom) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨y, hy⟩
    apply z.2
    refine ⟨y, ?_⟩
    have hsym : pullback.diagonal π ≫ (pullbackSymmetry π π).inv = pullback.diagonal π := by
      apply pullback.hom_ext <;> simp
    calc pullback.diagonal π y = (pullback.diagonal π ≫ (pullbackSymmetry π π).inv) y := by
          rw [hsym]
      _ = (pullbackSymmetry π π).inv (pullback.diagonal π y) := rfl
      _ = (pullbackSymmetry π π).inv
          ((π.diagonalCompl.ι ≫ (pullbackSymmetry π π).hom) z) := by rw [hy]
      _ = ((π.diagonalCompl.ι ≫ (pullbackSymmetry π π).hom) ≫ (pullbackSymmetry π π).inv) z :=
          rfl
      _ = z.1 := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl)

omit [Etale π] in
@[reassoc (attr := simp)]
lemma Scheme.Hom.diagonalComplSwap_ι :
    π.diagonalComplSwap ≫ π.diagonalCompl.ι = π.diagonalCompl.ι ≫ (pullbackSymmetry π π).hom :=
  IsOpenImmersion.lift_fac _ _ _

omit [Etale π] in
lemma Scheme.Hom.diagonalComplSwap_comp_self :
    π.diagonalComplSwap ≫ π.diagonalComplSwap = 𝟙 _ := by
  rw [← cancel_mono π.diagonalCompl.ι]
  simp only [Category.assoc, diagonalComplSwap_ι, diagonalComplSwap_ι_assoc, Category.id_comp]
  have : (pullbackSymmetry π π).hom ≫ (pullbackSymmetry π π).hom = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [this, Category.comp_id]

omit [Etale π] in
lemma Scheme.Hom.diagonalComplSwap_comp_diagonalComplSnd :
    π.diagonalComplSwap ≫ π.diagonalComplSnd = π.diagonalComplFst := by
  rw [Scheme.Hom.diagonalComplSnd, diagonalComplSwap_ι_assoc, pullbackSymmetry_hom_comp_snd]

omit [Etale π] in
instance : IsIso π.diagonalComplSwap :=
  ⟨⟨π.diagonalComplSwap, π.diagonalComplSwap_comp_self, π.diagonalComplSwap_comp_self⟩⟩

/-- The geometric number of points of the first projection `Y ×_X Y ∖ Δ ⟶ Y` at `y` is
`n(π y) - 1` (by symmetry, from `Scheme.Hom.geometricFiberCard_diagonalComplSnd_add_one`). -/
lemma Scheme.Hom.geometricFiberCard_diagonalComplFst_add_one (y : Y) :
    π.diagonalComplFst.geometricFiberCard y + 1 = π.geometricFiberCard (π y) := by
  have h : IsPullback π.diagonalComplSwap π.diagonalComplFst π.diagonalComplSnd (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by rw [π.diagonalComplSwap_comp_diagonalComplSnd, Category.comp_id]⟩
  rw [Scheme.Hom.geometricFiberCard_of_isPullback π.diagonalComplSnd
    π.diagonalComplSnd.finite_preimage_singleton h y]
  exact π.geometricFiberCard_diagonalComplSnd_add_one π.finite_preimage_singleton y

end Diagonal

namespace Scheme.Modules

section Proof

variable {k : Type u} [Field k]

/-- **`χ(Y, π^* π_* H) = d χ(Y, H)`**, given the multiplicativity in degree `d - 1`: by affine base
change, `χ(Y, π^* π_* H) = χ(Y ×_X Y, p₁^* H)`, and `Y ×_X Y = Δ(Y) ⊔ (Y ×_X Y ∖ Δ)`, where the
first projection `Y ×_X Y ∖ Δ ⟶ Y` is finite étale of degree `d - 1`. -/
theorem eulerChar_pullback_pushforward_self {d : ℕ}
    (IH : ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (π : Y ⟶ X) [IsFinite π]
      [Etale π], (∀ x, π.geometricFiberCard x = d) → ∀ (F : X.Modules) [F.IsCoherent],
        eulerChar (π ≫ f) ((Scheme.Modules.pullback π).obj F) = d * eulerChar f F)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (π : Y ⟶ X) [IsFinite π] [Etale π]
    (hπ : ∀ x, π.geometricFiberCard x = d + 1) (H : Y.Modules) [H.IsCoherent] :
    eulerChar (π ≫ f) ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pushforward π).obj H)) =
      (d + 1) * eulerChar (π ≫ f) H := by
  have : H.IsQuasicoherent := IsCoherent.isQuasicoherent
  rw [eulerChar_pullback_pushforward π π f H]
  have := FormallyUnramified.isOpenImmersion_diagonal π
  have := π.isClosedImmersion_diagonalCompl_ι
  have : ((Scheme.Modules.pullback (pullback.fst π π)).obj H).IsCoherent := isCoherent_pullback _ H
  rw [eulerChar_eq_add_of_isCompl (pullback.snd π π ≫ π ≫ f) (pullback.diagonal π)
    π.diagonalCompl.ι π.isCompl_opensRange_diagonal_diagonalCompl]
  -- the diagonal
  have e₁ : pullback.diagonal π ≫ pullback.snd π π ≫ π ≫ f = π ≫ f := by simp
  rw [e₁, eulerChar_congr (π ≫ f) ((pullbackCompIso' (pullback.diagonal π) (pullback.fst π π)
    (𝟙 Y) (by simp) H).symm ≪≫ (Scheme.Modules.pullbackId Y).app H)]
  -- the complement of the diagonal
  have e₂ : π.diagonalCompl.ι ≫ pullback.snd π π ≫ π ≫ f = π.diagonalComplFst ≫ π ≫ f := by
    rw [Scheme.Hom.diagonalComplFst, Category.assoc, pullback.condition_assoc]
  have hd : ∀ y, π.diagonalComplFst.geometricFiberCard y = d := fun y ↦ by
    have := π.geometricFiberCard_diagonalComplFst_add_one y
    rw [hπ] at this
    omega
  rw [e₂, eulerChar_congr _ (pullbackCompIso' π.diagonalCompl.ι (pullback.fst π π)
    π.diagonalComplFst rfl H).symm, IH (π ≫ f) π.diagonalComplFst hd H, Functor.id_obj]
  ring

/-- **The integral case**: let `Z` be integral and proper over `k`, and `p : W ⟶ Z` finite étale
of degree `d ≠ 0` with `χ(W, p^* p_* 𝒪_W) = d χ(W, 𝒪_W)`. If `χ(W, p^* G) = d χ(Z, G)` holds for
the coherent `G` supported in proper closed subsets, it holds for all coherent `G`: the difference
is `rk(G)` times its value on `𝒪_Z`, and `p_* 𝒪_W` has positive rank. -/
theorem eulerChar_pullback_eq_mul_of_isIntegral {d : ℕ} (hd : d ≠ 0) {Z W : Scheme.{u}}
    [IsIntegral Z] (g : Z ⟶ Spec (.of k)) [IsProper g] (p : W ⟶ Z) [IsFinite p] [Etale p]
    (hp : ∀ z, p.geometricFiberCard z = d)
    (hpush : eulerChar (p ≫ g) ((Scheme.Modules.pullback p).obj (pushforwardUnit p)) =
      d * eulerChar (p ≫ g) (unitModule W))
    (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → eulerChar (p ≫ g) ((Scheme.Modules.pullback p).obj N) = d * eulerChar g N)
    (G : Z.Modules) [G.IsCoherent] :
    eulerChar (p ≫ g) ((Scheme.Modules.pullback p).obj G) = d * eulerChar g G := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := {}
  let lam : Z.Modules → ℤ := fun N ↦
    eulerChar (p ≫ g) ((Scheme.Modules.pullback p).obj N) - d * eulerChar g N
  have hadd : ∀ S : ShortComplex Z.Modules, S.ShortExact → S.X₁.IsCoherent → S.X₂.IsCoherent →
      S.X₃.IsCoherent → lam S.X₂ = lam S.X₁ + lam S.X₃ := by
    intro S hS h₁ h₂ h₃
    simp only [lam]
    rw [eulerChar_pullback_of_shortExact g p hS, eulerChar_of_shortExact g hS]
    ring
  have IH' : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → lam N = 0 := fun N hN T' h₁ h₂ h₃ ↦ by
    simp only [lam]
    rw [IH N hN T' h₁ h₂ h₃, sub_self]
  -- `p_* 𝒪_W` has positive rank, and `λ(p_* 𝒪_W) = 0`
  have : (pushforwardUnit p).IsCoherent := isCoherent_pushforwardUnit p
  obtain ⟨n, U, -, hne, -, -, hn0, hn⟩ :=
    exists_additive_eq_mul_unitModule lam hadd IH' (pushforwardUnit p)
  have hpush' : lam (pushforwardUnit p) = 0 := by
    simp only [lam]
    rw [hpush, eulerChar_pushforward g p, sub_self]
  have hn' : n ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hw⟩ := p.nonempty_preimage_of_geometricFiberCard_ne_zero z (by rw [hp]; exact hd)
    have hwU : w ∈ p ⁻¹ᵁ U := by
      change p w ∈ U
      rw [show p w = z from hw]
      exact hz
    have h1 : (1 : Γ(W, p ⁻¹ᵁ U)) = 0 := hn0 h (1 : Γ(W, p ⁻¹ᵁ U))
    have h2 := congrArg (W.presheaf.germ (p ⁻¹ᵁ U) w hwU).hom h1
    rw [map_one, map_zero] at h2
    exact one_ne_zero h2
  have hO : lam (unitModule Z) = 0 :=
    (mul_eq_zero.mp (hn.symm.trans hpush')).resolve_left (by exact_mod_cast hn')
  obtain ⟨m, -, -, -, -, -, -, hm⟩ := exists_additive_eq_mul_unitModule lam hadd IH' G
  rw [hO, mul_zero] at hm
  exact sub_eq_zero.mp hm

/-- **Dévissage**: if `χ(W, p^* p_* 𝒪_W) = d χ(W, 𝒪_W)` for every finite étale `p : W ⟶ Z` of
degree `d ≠ 0` over a proper `k`-scheme, then `χ(Y, π^* F) = d χ(X, F)` for every finite étale
`π : Y ⟶ X` of degree `d` over a proper `k`-scheme and every coherent `F` (EGA III 3.1.2;
Stacks Tag 01YF): both sides are additive, and for `F = ι_* G` with `ι : Z ⟶ X` a closed
immersion, they are the two sides for the base change `Z ×_X Y ⟶ Z` of `π`. -/
theorem eulerChar_pullback_eq_mul_of_pushforwardUnit {d : ℕ} (hd : d ≠ 0)
    (hstep : ∀ {Z W : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsProper g] (p : W ⟶ Z) [IsFinite p]
      [Etale p], (∀ z, p.geometricFiberCard z = d) →
        eulerChar (p ≫ g) ((Scheme.Modules.pullback p).obj (pushforwardUnit p)) =
          d * eulerChar (p ≫ g) (unitModule W))
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (π : Y ⟶ X) [IsFinite π] [Etale π]
    (hπ : ∀ x, π.geometricFiberCard x = d) (F : X.Modules) [F.IsCoherent] :
    eulerChar (π ≫ f) ((Scheme.Modules.pullback π).obj F) = d * eulerChar f F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  refine prop_of_integral_step
    (fun N ↦ eulerChar (π ≫ f) ((Scheme.Modules.pullback π).obj N) = d * eulerChar f N) ?_ ?_ ?_ F
  · intro N hN hs
    have hz := isZero_of_forall_eq_zero N hs
    have : ((Scheme.Modules.pullback π).obj N).IsCoherent := isCoherent_pullback π N
    rw [eulerChar_eq_zero_of_isZero f N hz,
      eulerChar_eq_zero_of_isZero (π ≫ f) _ ((Scheme.Modules.pullback π).map_isZero hz), mul_zero]
  · intro S hS h₁ h₂ h₃ hP₁ hP₃
    rw [eulerChar_pullback_of_shortExact f π hS, eulerChar_of_shortExact f hS, hP₁, hP₃]
    ring
  · intro Z ι _ _ hIH G hG
    have key : ∀ G : Z.Modules, G.IsCoherent →
        (eulerChar (π ≫ f)
            ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pushforward ι).obj G)) =
            d * eulerChar f ((Scheme.Modules.pushforward ι).obj G) ↔
          eulerChar (pullback.fst ι π ≫ ι ≫ f)
            ((Scheme.Modules.pullback (pullback.fst ι π)).obj G) = d * eulerChar (ι ≫ f) G) := by
      intro G hG
      have : G.IsQuasicoherent := IsCoherent.isQuasicoherent
      rw [eulerChar_pullback_pushforward ι π f G, eulerChar_pushforward f ι G,
        ← pullback.condition_assoc]
    have hp : ∀ z, (pullback.fst ι π).geometricFiberCard z = d := fun z ↦ by
      rw [Scheme.Hom.geometricFiberCard_of_isPullback π π.finite_preimage_singleton
        (IsPullback.of_hasPullback ι π).flip z, hπ]
    rw [key G hG]
    exact eulerChar_pullback_eq_mul_of_isIntegral hd (ι ≫ f) (pullback.fst ι π) hp
      (hstep (ι ≫ f) (pullback.fst ι π) hp)
      (fun N hN T' h₁ h₂ h₃ ↦ (key N hN).mp (hIH N hN T' h₁ h₂ h₃)) G

/-- **Multiplicativity of `χ` in finite étale coverings** (strong form): for `X` proper over a field
`k` and `π : Y ⟶ X` finite étale with all geometric fibres of `d` points,
`χ(Y, π^* F) = d · χ(X, F)` for every coherent `F`. By induction on `d`. -/
theorem eulerChar_pullback_eq_mul (d : ℕ) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (π : Y ⟶ X) [IsFinite π]
      [Etale π], (∀ x, π.geometricFiberCard x = d) → ∀ (F : X.Modules) [F.IsCoherent],
        eulerChar (π ≫ f) ((Scheme.Modules.pullback π).obj F) = d * eulerChar f F := by
  induction d with
  | zero =>
    intro X Y f _ π _ _ hπ F _
    have : IsEmpty Y := π.isEmpty_of_geometricFiberCard_eq_zero π.finite_preimage_singleton hπ
    have : ((Scheme.Modules.pullback π).obj F).IsQuasicoherent :=
      (isCoherent_pullback π F).isQuasicoherent
    rw [eulerChar_eq_zero_of_isEmpty, Nat.cast_zero, zero_mul]
  | succ d ih =>
    intro X Y f _ π _ _ hπ F _
    refine eulerChar_pullback_eq_mul_of_pushforwardUnit (Nat.succ_ne_zero d)
      (fun g _ p _ _ hp ↦ ?_) f π hπ F
    push_cast
    exact eulerChar_pullback_pushforward_self ih g p hp (unitModule _)

end Proof

end Scheme.Modules

/-- **`EulerCharFiniteEtaleStatement` holds**: for `X` proper over a field `k` and `π : Y ⟶ X`
finite étale whose geometric fibres all have `d` points, `χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)`, in every
characteristic. -/
theorem eulerCharFiniteEtaleStatement : EulerCharFiniteEtaleStatement.{u} := by
  intro k _ X Y f _ π _ _ d hd
  rw [← eulerChar_congr (π ≫ f) (Scheme.Modules.pullbackObjUnitIso π)]
  exact eulerChar_pullback_eq_mul d f π hd (unitModule X)

end AlgebraicGeometry
