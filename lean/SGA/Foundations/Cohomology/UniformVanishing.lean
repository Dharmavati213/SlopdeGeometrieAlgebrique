/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.GradedSheaf
import SGA.Foundations.Cohomology.LerayTransfer
import SGA.Foundations.Cohomology.TwistProjection
import SGA.Foundations.Cohomology.AffineOpenVanishing
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Cohomology.HProjective


/-!
# Uniform vanishing on the graded pieces of an adic system

For an adic system `(G_n)` (`AdicSystem`) on `X` over `Spec A` and a line bundle `L` on `X`, the
graded pieces `I^{k+1} G_{k+1} = ker(G_{k+1} → G_k)` are direct summands of `q_* grSheaf`
(`SGA.Foundations.Cohomology.GradedSheaf`), so Serre vanishing for the single coherent module
`grSheaf` on `Y = X ×_A A[y]` gives vanishing for all of them at once (EGA III 5.2.x; the key step
of Hartshorne II.9.6):

* `subsingleton_H'_of_retract`, `subsingleton_H'_of_iso`: vanishing passes to retracts;
* `subsingleton_H_pushforward_of_isAffineHom`: `Hᵖ(Y, M) = 0 ⇒ Hᵖ(X, j_* M) = 0` for `j` affine;
* `GradedSetup.subsingleton_H_twist_grSucc`,
  `GradedSetup.exists_forall_subsingleton_H_twist_grSucc`: the abstract statement;
* `GradedSetup.exists_subsingleton_H_twist_of_isClosedImmersion`: Serre vanishing on `Y` when
  `X` is closed in `ℙ(τ; Spec A)`, `A` noetherian (`Y` is closed in `ℙ(τ; Spec A[y])`);
* `AdicSystem.exists_subsingleton_H_twist_grSucc`: for `X` closed in `ℙ(τ; Spec A)`, there is
  `d₀` with `H^{p+1}(X, I^{k+1} G_{k+1}(d)) = 0` for all `d ≥ d₀`, `k` and `p`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section Retract

variable {X : Scheme.{u}}

lemma H'_map_id_apply' (M : X.Modules) {p : ℕ} {U : X.Opens} (x : M.H' p U) :
    Scheme.Modules.H'.map (𝟙 M) p U x = x := by
  rw [Scheme.Modules.H'.map_apply]
  have h : Scheme.Modules.Hom.toAbSheaf (𝟙 M) = 𝟙 M.toAbSheaf :=
    (Scheme.Modules.toAbSheafFunctor X).map_id M
  rw [h]
  exact Sheaf.H'.map_id_apply _

/-- A retract of a module with vanishing cohomology has vanishing cohomology. -/
lemma subsingleton_H'_of_retract {M N : X.Modules} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (p : ℕ) (U : X.Opens) [Subsingleton (N.H' p U)] : Subsingleton (M.H' p U) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [← H'_map_id_apply' M x, ← H'_map_id_apply' M y, ← h, Scheme.Modules.H'.map_comp_apply,
    Scheme.Modules.H'.map_comp_apply, Subsingleton.elim (Scheme.Modules.H'.map i p U x)]

/-- Vanishing of cohomology is invariant under isomorphism. -/
lemma subsingleton_H'_of_iso {M N : X.Modules} (e : M ≅ N) (p : ℕ) (U : X.Opens)
    [Subsingleton (N.H' p U)] : Subsingleton (M.H' p U) :=
  subsingleton_H'_of_retract e.hom e.inv e.hom_inv_id p U

end Retract

section Affine

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsAffineHom j]

/-- **Cohomology along affine morphisms**: for `j` affine and `M` quasi-coherent, if `Hᵖ(Y, M)`
vanishes then so does `Hᵖ(X, j_* M)` (`X` quasi-compact with affine diagonal). -/
lemma subsingleton_H_pushforward_of_isAffineHom [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : Y.Modules) [M.IsQuasicoherent]
    (p : ℕ) [Subsingleton (M.H p)] :
    Subsingleton (((Scheme.Modules.pushforward j).obj M).H p) := by
  have : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := isQuasicoherent_pushforward j M
  obtain ⟨n, U, hcov, hU⟩ := exists_cechCover X
  exact (pushforwardHAddEquiv j M U hcov hU
    (fun x q ↦ M.H'_subsingleton_of_isAffineOpen ((hU x).preimage j) q)
    p).symm.injective.subsingleton

end Affine

section Uniform

variable {A : CommRingCat.{u}} {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec A}
  (S : GradedSetup I f) (G : AdicSystem I f)
  [CompactSpace X] [IsLocallyNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [(G.obj 0).IsFiniteType]

/-- **Vanishing on the graded pieces from vanishing on the graded sheaf** (EGA III 5.2.x,
Hartshorne II.9.6): if `Hᵖ(Y, grSheaf ⊗ (q^* L)^{⊗d}) = 0`, then
`Hᵖ(X, I^{k+1} G_{k+1} ⊗ L^{⊗d}) = 0` for every `k`. Indeed `I^{k+1} G_{k+1}` is a direct summand
of `q_* grSheaf`, `q` is affine, and `q_*(grSheaf ⊗ (q^* L)^{⊗d}) ≅ q_* grSheaf ⊗ L^{⊗d}`. -/
theorem GradedSetup.subsingleton_H_twist_grSucc (L : X.LineBundle) (p : ℕ) (d : ℤ)
    [Subsingleton (((L.pullback S.q).twist (S.grSheaf G) d).H p)] (k : ℕ) :
    Subsingleton ((L.twist (G.grSucc k) d).H p) := by
  have h1 : Subsingleton (((Scheme.Modules.pushforward S.q).obj
      ((L.pullback S.q).twist (S.grSheaf G) d)).H p) :=
    subsingleton_H_pushforward_of_isAffineHom S.q _ p
  have h2 : Subsingleton ((L.twist ((Scheme.Modules.pushforward S.q).obj (S.grSheaf G)) d).H p) :=
    subsingleton_H'_of_iso (L.twistPushforwardIso S.q (S.grSheaf G) d).symm p ⊤
  exact subsingleton_H'_of_retract (L.twistMap d (S.iMap G k)) (L.twistMap d (S.πMap G k))
    (by rw [← Scheme.LineBundle.twistMap_comp, GradedSetup.iMap_πMap,
      Scheme.LineBundle.twistMap_id]) p ⊤

/-- **Uniform vanishing** on the graded pieces of an adic system: if `Hᵖ(Y, grSheaf(d))`
vanishes for `d ≥ d₀` (Serre vanishing on `Y`), then `Hᵖ(X, I^{k+1} G_{k+1}(d)) = 0` for all
`k` and all `d ≥ d₀`. -/
theorem GradedSetup.exists_forall_subsingleton_H_twist_grSucc (L : X.LineBundle) (p : ℕ)
    (hSerre : ∃ d₀ : ℤ, ∀ d ≥ d₀,
      Subsingleton (((L.pullback S.q).twist (S.grSheaf G) d).H p)) :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ k, Subsingleton ((L.twist (G.grSucc k) d).H p) := by
  obtain ⟨d₀, hd₀⟩ := hSerre
  exact ⟨d₀, fun d hd k ↦
    have := hd₀ d hd
    S.subsingleton_H_twist_grSucc G L p d k⟩

end Uniform

section HProjective

open ProjectiveSpace

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} {τ : Type u}

/-- The graded setup `Y = X ×_A A[y_j]` on the chosen generators `gens I 1` of `I`. -/
def GradedSetup.ofGens [IsNoetherianRing A] (f : X ⟶ Spec A) : GradedSetup I f where
  σ := Fin (numGens I 1)
  a := gens I 1
  mem i := by simpa only [pow_one] using gens_mem I 1 i
  span := by rw [span_gens, pow_one]
  Y := pullback f (Spec.map (mvC (Fin (numGens I 1)) A))
  q := pullback.fst _ _
  g' := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _

lemma twistingSheaf_eq_pullback_map {S S' : Scheme.{u}} (g : S' ⟶ S) :
    twistingSheaf τ S' = (twistingSheaf τ S).pullback (ProjectiveSpace.map S g) := by
  rw [twistingSheaf, twistingSheaf, ← Scheme.LineBundle.pullback_comp, map_toProj]

lemma cechOpen_const_top {Z : Scheme.{u}} {m : ℕ} (x : Fin (m + 1) → Fin 1) :
    TopCat.Presheaf.cechOpen (fun _ : Fin 1 ↦ (⊤ : Z.Opens)) x = ⊤ :=
  le_antisymm le_top (le_iInf fun _ ↦ le_rfl)

variable [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Serre vanishing on `Y = X ×_A A[y]`** for `X` closed in `ℙ(τ; Spec A)`, `A` noetherian:
for `𝒢` coherent on `Y`, `Hᵖ(Y, 𝒢 ⊗ (q^* 𝒪_X(1))^{⊗d}) = 0` for `p > 0` and `d ≫ 0`. Indeed
`Y` is closed in `ℙ(τ; Spec A[y])` and `q^* 𝒪_X(1)` is the restriction of `𝒪(1)`. -/
theorem GradedSetup.exists_subsingleton_H_twist_of_isClosedImmersion [IsNoetherianRing A]
    (S : GradedSetup I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)) (𝒢 : S.Y.Modules) [𝒢.IsCoherent] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ p : ℕ, Subsingleton
      ((((twistingSheaf τ (Spec A)).pullback κ).pullback S.q |>.twist 𝒢 d).H (p + 1)) := by
  classical
  have : 𝒢.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  rcases isEmpty_or_nonempty τ with hτ | hτ
  · have : IsEmpty S.Y := ⟨fun y ↦ (isEmpty_proj_of_isEmpty (σ := τ) (R := ULift.{u} ℤ)).false
      ((S.q ≫ κ ≫ toProj τ _).base y)⟩
    exact ⟨0, fun d _ p ↦ Scheme.Modules.subsingleton_H_of_isEmpty _ _⟩
  let Z := Spec (CommRingCat.of (MvPolynomial S.σ A))
  let m := ProjectiveSpace.map (σ := τ) (Spec A) (Spec.map (mvC S.σ A))
  have hm := ProjectiveSpace.isPullback_map (σ := τ) (S := Spec A) (Spec.map (mvC S.σ A))
  let κY : S.Y ⟶ ℙ(τ; Z) := hm.lift (S.q ≫ κ) S.g' (by rw [Category.assoc, S.isPullback.w])
  have h1 : κY ≫ m = S.q ≫ κ := hm.lift_fst _ _ _
  have h2 : κY ≫ ℙ(τ; Z) ↘ Z = S.g' := hm.lift_snd _ _ _
  have hsq : IsPullback S.q κY κ m := by
    refine IsPullback.of_bot ?_ h1.symm hm
    rw [h2]
    exact S.isPullback
  have : IsClosedImmersion κY := MorphismProperty.of_isPullback hsq ‹IsClosedImmersion κ›
  have : IsAffineHom (pullback.diagonal (terminal.from ℙ(τ; Z))) :=
    isAffineHom_diagonal_of_isSeparated (ℙ(τ; Z) ↘ Z)
  have hL : ((twistingSheaf τ (Spec A)).pullback κ).pullback S.q =
      (twistingSheaf τ Z).pullback κY := by
    rw [← Scheme.LineBundle.pullback_comp, ← h1, twistingSheaf_eq_pullback_map (τ := τ)
      (Spec.map (mvC S.σ A)), Scheme.LineBundle.pullback_comp]
  obtain ⟨n₀, hn₀⟩ := exists_twist_acyclic κY 𝒢 (fun _ : Fin 1 ↦ (⊤ : Z.Opens))
    (fun x ↦ by rw [cechOpen_const_top]; exact isAffineOpen_top Z)
  refine ⟨n₀, fun d hd p ↦ ?_⟩
  have h := hn₀ d hd (m := 0) (fun _ ↦ 0) p
  rw [cechOpen_const_top, Scheme.Hom.preimage_top] at h
  rw [hL]
  exact h

/-- **Uniform vanishing on the graded pieces of an adic system** on a closed subscheme `X` of
`ℙ(τ; Spec A)`, `A` noetherian (the key step of EGA III 5.2 / Hartshorne II.9.6): there is `d₀`
with `H^{p+1}(X, I^{k+1} G_{k+1} ⊗ 𝒪_X(d)) = 0` for all `d ≥ d₀`, all `k` and all `p`. -/
theorem AdicSystem.exists_subsingleton_H_twist_grSucc [IsNoetherianRing A]
    (G : AdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)) [(G.obj 0).IsFiniteType] :
    ∃ d₀ : ℤ, ∀ d ≥ d₀, ∀ k p : ℕ, Subsingleton
      ((((twistingSheaf τ (Spec A)).pullback κ).twist (G.grSucc k) d).H (p + 1)) := by
  have : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    isAffineHom_diagonal_of_isSeparated (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  let S := GradedSetup.ofGens I (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  obtain ⟨d₀, hd₀⟩ := S.exists_subsingleton_H_twist_of_isClosedImmersion I κ (S.grSheaf G)
  refine ⟨d₀, fun d hd k p ↦ ?_⟩
  have := hd₀ d hd p
  exact S.subsingleton_H_twist_grSucc G _ (p + 1) d k

end HProjective

end AlgebraicGeometry.CohomologyAux
