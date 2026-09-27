/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.GlobalExtension
import SGA.SGA1.ExposeIII.Thickening

/-!
# SGA 1, Exposé III, 5.8: extending isomorphisms of formal schemes

Proposition III.5.8: let `A` be a complete local ring and `𝔛`, `𝔜` formal schemes over `A`, flat
over `A`, with `X₀` smooth over `k` and `H¹(X₀, 𝔤_{X₀/k}) = 0`. Every `k`-isomorphism `Y₀ ≅ X₀`
extends to an `A`-isomorphism `𝔜 ≅ 𝔛`.

A formal scheme is given here by its truncations `Xₙ` over `Sₙ` (for SGA, `Sₙ = Spec (A ⧸ 𝔪ⁿ⁺¹)`),
with cartesian squares `Xₙ = Xₙ₊₁ ×_{Sₙ₊₁} Sₙ`; the thickenings `Sₙ → Sₙ₊₁` may be any surjective
closed immersions of affine locally noetherian schemes with square-zero ideal. We prove III.5.8
when `𝔜` is affine, i.e. all `Yₙ` are affine, so that the `H¹` in SGA vanishes
(`exists_isoSeq_of_isAffine`). As in SGA the isomorphism `Yₙ ≅ Xₙ` extends to `Yₙ₊₁ → Xₙ₊₁` over
`Sₙ₊₁` (III.5.5, `exists_extension_of_isSqZeroOn`), which is an isomorphism by III.4.2
(`isIso_of_isPullback`, using the flatness of `Yₙ₊₁`).

Differences with SGA: we assume the `Xₙ` smooth over `Sₙ` (in SGA this follows from the flatness of
`Xₙ` and the smoothness of `X₀`, II.2.1), and do not formalize the uniqueness statement (when
`H⁰(X₀, 𝔤) = 0`). The general case needs the `H¹` obstruction theory of III.5.3 for non-affine
`Y₀` together with the identification `𝒢ₙ = 𝒢₀ ⊗ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` of III.5.6.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

/-- The base change of a closed immersion of affine schemes with square-zero ideal, to an affine
scheme, again has square-zero ideal. -/
lemma ker_appTop_sq_of_isPullback {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y} {i : Y₀ ⟶ Y}
    {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀} (hX : IsPullback iX fX f i) [IsClosedImmersion i] [IsAffine Y]
    [IsAffine X] (h : RingHom.ker i.appTop.hom ^ 2 = ⊥) :
    RingHom.ker iX.appTop.hom ^ 2 = ⊥ := by
  obtain ⟨-, hker⟩ := surjective_appLE_and_ker_eq_map hX (isAffineOpen_top Y)
    (isAffineOpen_top X) le_top
  change RingHom.ker (i.app ⊤).hom ^ 2 = ⊥ at h
  change RingHom.ker (iX.app ⊤).hom ^ 2 = ⊥
  rw [Scheme.Hom.app_eq_appLE] at h ⊢
  rw [hker, ← Ideal.map_pow, h, Ideal.map_bot]

/-- III.5.8 for an affine formal scheme `𝔜`: let `Sₙ → Sₙ₊₁` be thickenings (surjective closed
immersions with square-zero ideal) of affine locally noetherian schemes, and `(Xₙ)`, `(Yₙ)`
compatible systems over `(Sₙ)` (cartesian squares `Xₙ = Xₙ₊₁ ×_{Sₙ₊₁} Sₙ`), with the `Xₙ` smooth,
the `Yₙ` flat and affine. Then every isomorphism `Y₀ ≅ X₀` over `S₀` extends to a compatible
system of isomorphisms `Yₙ ≅ Xₙ` over `Sₙ`, i.e. to an isomorphism of formal schemes `𝔜 ≅ 𝔛`. -/
theorem exists_isoSeq_of_isAffine {S : ℕ → Scheme.{u}} (s : ∀ n, S n ⟶ S (n + 1))
    [∀ n, IsAffine (S n)] [∀ n, IsLocallyNoetherian (S n)] [∀ n, IsClosedImmersion (s n)]
    [∀ n, Surjective (s n)] (hs : ∀ n, RingHom.ker (s n).appTop.hom ^ 2 = ⊥)
    {X Y : ℕ → Scheme.{u}} (p : ∀ n, X n ⟶ S n) (q : ∀ n, Y n ⟶ S n)
    (iX : ∀ n, X n ⟶ X (n + 1)) (iY : ∀ n, Y n ⟶ Y (n + 1))
    (hX : ∀ n, IsPullback (iX n) (p n) (p (n + 1)) (s n))
    (hY : ∀ n, IsPullback (iY n) (q n) (q (n + 1)) (s n))
    [∀ n, Smooth (p n)] [∀ n, Flat (q n)] [∀ n, IsAffine (Y n)]
    (e₀ : Y 0 ≅ X 0) (he₀ : e₀.hom ≫ p 0 = q 0) :
    ∃ e : ∀ n, Y n ≅ X n, e 0 = e₀ ∧ (∀ n, (e n).hom ≫ p n = q n) ∧
      ∀ n, iY n ≫ (e (n + 1)).hom = (e n).hom ≫ iX n := by
  have step (n : ℕ) (e : Y n ≅ X n) (he : e.hom ≫ p n = q n) :
      ∃ e' : Y (n + 1) ≅ X (n + 1), e'.hom ≫ p (n + 1) = q (n + 1) ∧
        iY n ≫ e'.hom = e.hom ≫ iX n := by
    have : IsClosedImmersion (iY n) := MorphismProperty.of_isPullback (hY n).flip inferInstance
    have : Surjective (iY n) :=
      MorphismProperty.of_isPullback (P := @Surjective) (hY n).flip inferInstance
    have hsq : IsSqZeroOn (iY n) :=
      isSqZeroOn_of_ker_appTop_sq _ (ker_appTop_sq_of_isPullback (hY n) (hs n))
    obtain ⟨u, hu₁, hu₂⟩ := exists_extension_of_isSqZeroOn (p (n + 1)) (q (n + 1)) (iY n) hsq
      (e.hom ≫ iX n) (by rw [Category.assoc, (hX n).w, reassoc_of% he, (hY n).w])
    have : IsIso u := isIso_of_isPullback (q (n + 1)) (p (n + 1)) (s n) (s n).surjective (hY n)
      (hX n) u hu₁ e.hom hu₂.symm
    exact ⟨asIso u, hu₁, hu₂⟩
  choose E hE₁ hE₂ using step
  let seq : ∀ n, {e : Y n ≅ X n // e.hom ≫ p n = q n} := fun n ↦
    Nat.rec ⟨e₀, he₀⟩ (fun n e ↦ ⟨E n e.1 e.2, hE₁ n e.1 e.2⟩) n
  exact ⟨fun n ↦ (seq n).1, rfl, fun n ↦ (seq n).2, fun n ↦ hE₂ n (seq n).1 (seq n).2⟩

end SGA.SGA1.ExposeIII
