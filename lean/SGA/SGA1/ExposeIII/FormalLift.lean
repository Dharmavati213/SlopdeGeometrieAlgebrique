/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.AffineLift
import SGA.SGA1.ExposeIII.FormalExtension

/-!
# SGA 1, Exposé III, 6.10: formal smooth lifts of affine schemes

Let `Y` be a scheme with a quasi-coherent ideal `𝓘`, `Yₙ = V(𝓘ⁿ⁺¹)`, and `X₀` smooth over `Y₀`.
SGA 1 III.6.10 constructs, when `H²(X₀, 𝔤_{X₀/Y₀}) = 0`, smooth `Yₙ`-schemes `Xₙ` reducing to
each other, hence a formal scheme `𝔛 = lim Xₙ` smooth over the formal completion `Ŷ`.

For `Y` and `X₀` affine the obstructions vanish (III.6.8, `exists_smooth_lift_of_isAffine`):

* `exists_smooth_lift_seq`: the successive smooth lifts `Xₙ → Yₙ`, with cartesian squares
  `Xₙ = Xₙ₊₁ ×_{Yₙ₊₁} Yₙ`;
* `exists_formal_smooth_lift`: the corresponding thickening sequence `X₀ ⊆ X₁ ⊆ ⋯`, whose formal
  colimit `𝔛` maps to `Ŷ`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

variable {Y : Scheme.{u}} [IsAffine Y] (𝓘 : Y.IdealSheafData)

/-- III.6.10 (affine case): an affine smooth `X₀ → Y₀ = V(𝓘)` extends to successive affine
smooth lifts `Xₙ → Yₙ = V(𝓘ⁿ⁺¹)`, with `Xₙ = Xₙ₊₁ ×_{Yₙ₊₁} Yₙ`. -/
theorem exists_smooth_lift_seq {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ 𝓘.infinitesimalDiagram.obj 0)
    [Smooth f₀] [IsAffine X₀] :
    ∃ (X : ℕ → Scheme.{u}) (f : ∀ n, X n ⟶ 𝓘.infinitesimalDiagram.obj n)
      (k : ∀ n, X n ⟶ X (n + 1)) (e : X 0 ≅ X₀),
      (∀ n, Smooth (f n)) ∧ (∀ n, IsAffine (X n)) ∧ e.hom ≫ f₀ = f 0 ∧
        ∀ n, IsPullback (k n) (f n) (f (n + 1))
          (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)) := by
  have step (n : ℕ) (X : Scheme.{u}) (f : X ⟶ 𝓘.infinitesimalDiagram.obj n) (_ : Smooth f)
      (_ : IsAffine X) :
      ∃ (X' : Scheme.{u}) (f' : X' ⟶ 𝓘.infinitesimalDiagram.obj (n + 1)) (_ : Smooth f')
        (_ : IsAffine X') (k : X ⟶ X'),
        IsPullback k f f' (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)) :=
    exists_smooth_lift_of_isAffine _ (isNilpotent_ker_infinitesimalDiagram_map 𝓘 n) f
  choose X' f' hf' hX' k hk using step
  let seq : ∀ n, Σ X : Scheme.{u}, Σ' (f : X ⟶ 𝓘.infinitesimalDiagram.obj n),
      Smooth f ∧ IsAffine X := fun n ↦
    Nat.rec ⟨X₀, f₀, inferInstance, inferInstance⟩
      (fun n d ↦ ⟨X' n d.1 d.2.1 d.2.2.1 d.2.2.2, f' n _ _ d.2.2.1 d.2.2.2,
        hf' n _ _ _ _, hX' n _ _ _ _⟩) n
  exact ⟨fun n ↦ (seq n).1, fun n ↦ (seq n).2.1,
    fun n ↦ k n (seq n).1 (seq n).2.1 (seq n).2.2.1 (seq n).2.2.2, Iso.refl _,
    fun n ↦ (seq n).2.2.1, fun n ↦ (seq n).2.2.2, Category.id_comp _,
    fun n ↦ hk n (seq n).1 (seq n).2.1 (seq n).2.2.1 (seq n).2.2.2⟩

/-- III.6.10 (affine case), formal form: an affine smooth `X₀ → Y₀ = V(𝓘)` is the reduction of a
thickening sequence `X₀ ⊆ X₁ ⊆ ⋯` of smooth `Yₙ`-schemes, with `Xₙ = Xₙ₊₁ ×_{Yₙ₊₁} Yₙ`; its formal
colimit `𝔛` is a formal scheme over the formal completion `Ŷ` of `Y` along `V(𝓘)`. -/
theorem exists_formal_smooth_lift {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ 𝓘.infinitesimalDiagram.obj 0)
    [Smooth f₀] [IsAffine X₀] :
    ∃ (F : ℕ ⥤ Scheme.{u}) (_ : Scheme.IsThickeningSequence F)
      (f : ∀ n, F.obj n ⟶ 𝓘.infinitesimalDiagram.obj n) (e : F.obj 0 ≅ X₀),
      (∀ n, Smooth (f n)) ∧ e.hom ≫ f₀ = f 0 ∧
        (∀ n, IsPullback (F.map (homOfLE n.le_succ)) (f n) (f (n + 1))
          (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ))) ∧
        ∃ φ : Scheme.formalColimit F ⟶ 𝓘.formalCompletion,
          ∀ n, Scheme.formalColimit.ι F n ≫ φ =
            (f n).toLRSHom ≫ Scheme.formalColimit.ι _ n := by
  obtain ⟨X, f, k, e, hf, -, he, hk⟩ := exists_smooth_lift_seq 𝓘 f₀
  let F := Functor.ofSequence k
  have hFk (n : ℕ) : F.map (homOfLE n.le_succ) = k n := Functor.ofSequence_map_homOfLE_succ k n
  have hk' (n : ℕ) : IsPullback (F.map (homOfLE n.le_succ)) (f n) (f (n + 1))
      (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)) := by
    rw [hFk]; exact hk n
  have : Scheme.IsThickeningSequence F :=
    { isClosedImmersion n := MorphismProperty.of_isPullback (hk' n).flip inferInstance
      surjective n := MorphismProperty.of_isPullback (P := @Surjective) (hk' n).flip
        (Scheme.IsThickeningSequence.surjective (F := 𝓘.infinitesimalDiagram) n) }
  refine ⟨F, this, f, e, hf, he, hk', Scheme.formalColimit.desc F
    (fun n ↦ (f n).toLRSHom ≫ Scheme.formalColimit.ι _ n) fun n ↦ ?_, fun n ↦ ?_⟩
  · have h := congrArg Scheme.Hom.toLRSHom (hk' n).w
    have hw := Scheme.formalColimit.w 𝓘.infinitesimalDiagram (homOfLE n.le_succ)
    simp only at h
    change (F.map (homOfLE n.le_succ)).toLRSHom ≫ (f (n + 1)).toLRSHom ≫
      Scheme.formalColimit.ι _ (n + 1) = (f n).toLRSHom ≫ Scheme.formalColimit.ι _ n
    rw [← hw]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
      (Category.assoc _ _ _))
  · exact Scheme.formalColimit.ι_desc _ _ _ n

end SGA.SGA1.ExposeIII
