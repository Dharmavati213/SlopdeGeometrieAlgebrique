/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.GlobalExtension
import SGA.Foundations.Formal.Completion

/-!
# SGA 1, Exposé III, 5.4–5.6: extension of morphisms to formal completions

Let `f : X → S` be smooth and `Y₀ ⊆ Y₁ ⊆ ⋯` a thickening sequence over `S` (for instance the
infinitesimal neighbourhoods `Yₙ = V(𝓘ⁿ⁺¹)` of a closed subscheme of `Y`). SGA 1 III.5.4 shows
that the obstruction to extending an `S`-morphism `gₙ : Yₙ → X` to `Yₙ₊₁` lies in
`H¹(Y₀, 𝒢ₙ)`, and III.5.6 that when these groups vanish, `g₀` extends step by step to a
morphism `ĝ : Ŷ → X` from the formal completion.

When the `Yₙ` are affine, the obstructions vanish by III.5.5 (`exists_extension_of_isNilpotent`):

* `exists_extension_formalColimit`: a morphism `g₀ : Y₀ → X` extends to the formal scheme
  `lim→ Yₙ` of a thickening sequence of affine schemes with nilpotent ideals;
* `exists_extension_formalCompletion`: for `Y` affine and a quasi-coherent ideal `𝓘`, every
  `S`-morphism `V(𝓘) → X` extends to the formal completion `Ŷ` of `Y` along `V(𝓘)`
  (III.5.6 for affine `Y`, where `H¹(Y₀, 𝒢₀) = 0`).

The ring-theoretic form (with the formal completion `Â` of the ring of `Y`) is
`exists_lift_adicCompletion` in `Deformation.lean`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- III.5.4–III.5.6 for affine thickenings: let `F` be a thickening sequence `Y₀ ⊆ Y₁ ⊆ ⋯` of affine
schemes with nilpotent ideals, over `S` via compatible morphisms `pₙ`. For `f : X → S` smooth,
every `S`-morphism `g₀ : Y₀ → X` extends to compatible `S`-morphisms `gₙ : Yₙ → X`. -/
theorem exists_compatible_extensions (F : ℕ ⥤ Scheme.{u}) [Scheme.IsThickeningSequence F]
    [∀ n, IsAffine (F.obj n)] (hnil : ∀ n : ℕ, IsNilpotent (F.map (homOfLE n.le_succ)).ker)
    (p : ∀ n, F.obj n ⟶ S) (hp : ∀ n : ℕ, F.map (homOfLE n.le_succ) ≫ p (n + 1) = p n)
    (g₀ : F.obj 0 ⟶ X) (hg₀ : g₀ ≫ f = p 0) :
    ∃ g : ∀ n, F.obj n ⟶ X, g 0 = g₀ ∧ (∀ n, g n ≫ f = p n) ∧
      ∀ n, F.map (homOfLE n.le_succ) ≫ g (n + 1) = g n := by
  have step (n : ℕ) (g : F.obj n ⟶ X) (hg : g ≫ f = p n) :
      ∃ g' : F.obj (n + 1) ⟶ X, g' ≫ f = p (n + 1) ∧ F.map (homOfLE n.le_succ) ≫ g' = g :=
    exists_extension_of_isNilpotent f (p (n + 1)) _ (hnil n) g (by rw [hg, hp])
  choose G hG₁ hG₂ using step
  let seq : ∀ n, {g : F.obj n ⟶ X // g ≫ f = p n} := fun n ↦
    Nat.rec ⟨g₀, hg₀⟩ (fun n g ↦ ⟨G n g.1 g.2, hG₁ n g.1 g.2⟩) n
  exact ⟨fun n ↦ (seq n).1, rfl, fun n ↦ (seq n).2, fun n ↦ hG₂ n (seq n).1 (seq n).2⟩

/-- III.5.6 for affine thickenings, formal form: `g₀ : Y₀ → X` extends to a morphism
`ĝ : lim→ Yₙ → X` of locally ringed spaces over `S`. -/
theorem exists_extension_formalColimit (F : ℕ ⥤ Scheme.{u}) [Scheme.IsThickeningSequence F]
    [∀ n, IsAffine (F.obj n)] (hnil : ∀ n : ℕ, IsNilpotent (F.map (homOfLE n.le_succ)).ker)
    (p : ∀ n, F.obj n ⟶ S) (hp : ∀ n : ℕ, F.map (homOfLE n.le_succ) ≫ p (n + 1) = p n)
    (g₀ : F.obj 0 ⟶ X) (hg₀ : g₀ ≫ f = p 0) :
    ∃ ĝ : Scheme.formalColimit F ⟶ X.toLocallyRingedSpace,
      Scheme.formalColimit.ι F 0 ≫ ĝ = g₀.toLRSHom ∧
      ĝ ≫ f.toLRSHom = Scheme.formalColimit.desc F (fun n ↦ (p n).toLRSHom)
        (fun n ↦ by rw [← Scheme.Hom.comp_toLRSHom, hp]) := by
  obtain ⟨g, hg₀', hgf, hgc⟩ := exists_compatible_extensions f F hnil p hp g₀ hg₀
  refine ⟨Scheme.formalColimit.desc F (fun n ↦ (g n).toLRSHom)
    (fun n ↦ by rw [← Scheme.Hom.comp_toLRSHom, hgc]), ?_, ?_⟩
  · rw [Scheme.formalColimit.ι_desc, hg₀']
  · refine Scheme.formalColimit.hom_ext F fun n ↦ ?_
    rw [Scheme.formalColimit.ι_desc_assoc, Scheme.formalColimit.ι_desc,
      ← Scheme.Hom.comp_toLRSHom, hgf]

section Completion

variable {Y : Scheme.{u}} [IsAffine Y] (𝓘 : Y.IdealSheafData)

instance (n : ℕ) : IsAffine (𝓘.infinitesimalDiagram.obj n) :=
  isAffine_of_isAffineHom (𝓘 ^ (n + 1)).subschemeι

omit [IsAffine Y] in
/-- For ideals `I ≤ J` on an affine scheme with `J(Y)² ⊆ I(Y)`, the closed immersion
`V(J) → V(I)` has an ideal of square zero. -/
lemma isNilpotent_ker_inclusion [IsAffine Y] {I J : Y.IdealSheafData} (h : I ≤ J)
    (hsq : J.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ 2 ≤ I.ideal ⟨⊤, isAffineOpen_top Y⟩) :
    IsNilpotent (Scheme.IdealSheafData.inclusion h).ker := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  set i := Scheme.IdealSheafData.inclusion h
  have hcomp (a : Γ(Y, ⊤)) : i.appTop (I.subschemeι.appTop a) = J.subschemeι.appTop a := by
    have := congrArg (fun φ : J.subscheme ⟶ Y ↦ φ.appTop)
      (Scheme.IdealSheafData.inclusion_subschemeι h)
    simp only [Scheme.Hom.comp_appTop] at this
    rw [← this]
    rfl
  have hker (K : Y.IdealSheafData) (x : Γ(Y, ⊤)) :
      K.subschemeι.appTop x = 0 ↔ x ∈ K.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
    rw [← Scheme.IdealSheafData.ker_subschemeι_app K ⟨⊤, isAffineOpen_top Y⟩, RingHom.mem_ker]
    rfl
  have hsurj := Scheme.IdealSheafData.subschemeι_app_surjective I ⟨⊤, isAffineOpen_top Y⟩
  have hsq' : RingHom.ker i.appTop.hom ^ 2 = ⊥ := by
    rw [eq_bot_iff, pow_two, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have ha : a ∈ J.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
      rw [← hker, ← hcomp]; exact hx
    have hb : b ∈ J.ideal ⟨⊤, isAffineOpen_top Y⟩ := by
      rw [← hker, ← hcomp]; exact hy
    rw [Ideal.mem_bot]
    have h' := (hker I (a * b)).mpr (hsq (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb))
    rw [map_mul] at h'
    exact h'
  refine ⟨2, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
  exact hsq'

/-- The ideal of `V(𝓘ⁿ⁺¹) ⊆ V(𝓘ⁿ⁺²)` has square zero, for `Y` affine. -/
lemma isNilpotent_ker_infinitesimalDiagram_map (n : ℕ) :
    IsNilpotent (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)).ker := by
  refine isNilpotent_ker_inclusion _ ?_
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ← pow_mul]
  exact Ideal.pow_le_pow_right (by omega)

/-- III.5.6 for an affine `Y`: let `f : X → S` be smooth, `Y` an affine `S`-scheme and `𝓘` a
quasi-coherent ideal of `Y`. Every `S`-morphism `g₀ : V(𝓘) → X` extends to a morphism
`ĝ : Ŷ → X` over `S` from the formal completion `Ŷ` of `Y` along `V(𝓘)`. (SGA assumes `Y` flat
over `S` and `H¹(Y₀, 𝒢₀) = 0`; for affine `Y` the obstructions vanish without flatness.) -/
theorem exists_extension_formalCompletion (p : Y ⟶ S)
    (g₀ : (𝓘 ^ (0 + 1)).subscheme ⟶ X) (hg₀ : g₀ ≫ f = (𝓘 ^ (0 + 1)).subschemeι ≫ p) :
    ∃ ĝ : 𝓘.formalCompletion ⟶ X.toLocallyRingedSpace,
      Scheme.formalColimit.ι _ 0 ≫ ĝ = g₀.toLRSHom ∧
      ĝ ≫ f.toLRSHom = 𝓘.formalCompletionι ≫ p.toLRSHom := by
  have hp (n : ℕ) : 𝓘.infinitesimalDiagram.map (homOfLE n.le_succ) ≫
      ((𝓘 ^ (n + 1 + 1)).subschemeι ≫ p) = (𝓘 ^ (n + 1)).subschemeι ≫ p := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  obtain ⟨ĝ, h₁, h₂⟩ := exists_extension_formalColimit f 𝓘.infinitesimalDiagram
    (isNilpotent_ker_infinitesimalDiagram_map 𝓘) (fun n ↦ (𝓘 ^ (n + 1)).subschemeι ≫ p) hp g₀
    hg₀
  refine ⟨ĝ, h₁, h₂.trans (Scheme.formalColimit.hom_ext _ fun n ↦ ?_)⟩
  rw [Scheme.formalColimit.ι_desc, Scheme.IdealSheafData.ι_formalCompletionι_assoc,
    Scheme.Hom.comp_toLRSHom]

end Completion

end SGA.SGA1.ExposeIII
