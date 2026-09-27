/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Formal.AdicInverseLimit
import SGA.Foundations.Formal.FormalScheme
import SGA.Foundations.Formal.OpenImmersion

/-!
# Formal spectra of limits of adic inverse systems

Let `⋯ → A₂ → A₁ → A₀` be an adic inverse system of rings (`Ring.IsAdicInverseSystem`) with
`ker (A₁ → A₀)` finitely generated, `A = lim Aₙ` and `J = ker (A → A₀)`. By EGA 0_I, 7.2.7,
`A ⧸ Jⁿ⁺¹ ≅ Aₙ`, so the sequence of affine schemes `Spec A₀ ⟶ Spec A₁ ⟶ ⋯` is isomorphic to the
thickening sequence of `Spf A` (`Ring.IsAdicInverseSystem.diagramIso`), and its formal colimit is
`Spf A` (`Ring.IsAdicInverseSystem.formalColimitIso`, EGA I, §10.6). If `A₀` is noetherian, this
is a locally noetherian formal scheme (`isLocallyNoetherianFormalScheme_formalColimit`).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {A : ℕ → Type u} [∀ n, CommRing (A n)] (π : ∀ n, A (n + 1) →+* A n)

/-- The sequence of affine schemes `Spec A₀ ⟶ Spec A₁ ⟶ ⋯` of an inverse system of rings
`⋯ → A₁ → A₀`. -/
noncomputable def specSequence : ℕ ⥤ Scheme.{u} :=
  Functor.ofSequence (X := fun n ↦ Spec (.of (A n)))
    fun n ↦ Spec.map (CommRingCat.ofHom (π n))

@[simp]
lemma specSequence_obj (n : ℕ) : (specSequence π).obj n = Spec (.of (A n)) := rfl

lemma specSequence_map_succ (n : ℕ) :
    (specSequence π).map (homOfLE n.le_succ) = Spec.map (CommRingCat.ofHom (π n)) :=
  Functor.ofSequence_map_homOfLE_succ _ n

end AlgebraicGeometry.Scheme

namespace Ring.IsAdicInverseSystem

open AlgebraicGeometry Ring.inverseLimit

variable {A : ℕ → Type u} [∀ n, CommRing (A n)] {π : ∀ n, A (n + 1) →+* A n}
  (h : IsAdicInverseSystem π) (hJ : (RingHom.ker (π 0)).FG)

/-- For an adic inverse system, the thickening sequence of `Spf (lim Aₙ)` is
`Spec A₀ ⟶ Spec A₁ ⟶ ⋯` (EGA 0_I, 7.2.7). -/
noncomputable def diagramIso :
    Spf.diagram (inverseLimit π) (RingHom.ker (proj π 0)) ≅ Scheme.specSequence π := by
  let e (n : ℕ) := Scheme.Spec.mapIso (h.quotientEquiv hJ n).toCommRingCatIso.op
  have hnat (n : ℕ) : (Spf.diagram (inverseLimit π) (RingHom.ker (proj π 0))).map
      (homOfLE n.le_succ) ≫ (e (n + 1)).inv =
        (e n).inv ≫ (Scheme.specSequence π).map (homOfLE n.le_succ) := by
    rw [Scheme.specSequence_map_succ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    apply (h.quotientEquiv hJ n).injective
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((h.quotientEquiv hJ (n + 1)).symm x)
    have hx : x = proj π (n + 1) z := by
      rw [← quotientEquiv_mk h hJ, hz, RingEquiv.apply_symm_apply]
    change h.quotientEquiv hJ n (Ideal.Quotient.factorPow _ (Nat.le_succ (n + 1))
        ((h.quotientEquiv hJ (n + 1)).symm x)) =
      h.quotientEquiv hJ n ((h.quotientEquiv hJ n).symm (π n x))
    rw [RingEquiv.apply_symm_apply, ← hz, Ideal.Quotient.factor_mk, quotientEquiv_mk, hx,
      π_proj]
  let α := NatTrans.ofSequence (F := Spf.diagram (inverseLimit π) (RingHom.ker (proj π 0)))
    (G := Scheme.specSequence π) (fun n ↦ (e n).inv) hnat
  have (n : ℕ) : IsIso (α.app n) := inferInstanceAs (IsIso (e n).inv)
  have : IsIso α := NatIso.isIso_of_isIso_app _
  exact asIso α

/-- EGA I, §10.6: the formal colimit of `Spec A₀ ⟶ Spec A₁ ⟶ ⋯` for an adic inverse system is
the formal spectrum of `lim Aₙ`. -/
noncomputable def formalColimitIso :
    Spf (inverseLimit π) (RingHom.ker (proj π 0)) ≅ Scheme.formalColimit (Scheme.specSequence π) :=
  have : IsIso (Functor.whiskerRight (h.diagramIso hJ).hom Scheme.forgetToLocallyRingedSpace) :=
    inferInstance
  have : IsIso (Scheme.formalColimit.map (h.diagramIso hJ).hom) :=
    inferInstanceAs (IsIso (colimMap _))
  asIso (Scheme.formalColimit.map (h.diagramIso hJ).hom)

include h hJ in
/-- EGA I, §10.6: for an adic inverse system with `A₀` noetherian and `ker (A₁ → A₀)` finitely
generated, `lim→ Spec Aₙ` is a locally noetherian formal scheme. -/
theorem isLocallyNoetherianFormalScheme_formalColimit [IsNoetherianRing (A 0)] :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme
      (Scheme.formalColimit (Scheme.specSequence π)) := by
  have := h.isNoetherianRing hJ
  have := h.isAdicComplete hJ
  exact LocallyRingedSpace.IsLocallyNoetherianFormalScheme.prop_of_iso (h.formalColimitIso hJ)
    (Spf.isLocallyNoetherianFormalScheme _ _)

end Ring.IsAdicInverseSystem
