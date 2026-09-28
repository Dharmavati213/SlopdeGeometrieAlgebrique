/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Image

/-!
# SGA 1, Exposé XIII, Appendix II: finiteness for direct images of stacks

Appendix II (XIII.6) proves that the direct image `f_*Φ` of a `1`-constructible stack under a
proper morphism of locally noetherian schemes is `1`-constructible (XIII.6.2), deducing it
(XIII.6.1) from the finiteness of `f_*` for constructible sheaves of sets and of `R¹f_*` for
constructible sheaves of groups (SGA 4 XIV), via the sheaf of maximal subgerbes (XIII.6.1.1) and
a gluing lemma for constructible sheaves (XIII.6.1.2). XIII.6.3 is the analogue for the tame
direct image `i_*^t Φ`.

Stacks and gerbes on the étale site, constructible sheaves and `R¹f_*` for sheaves of groups are
not available, so XIII.6.1–6.3 are not formalized. What is formalized is the stalkwise step of
the proof of XIII.6.1.2: a map of stalks `F_s̃ → F_s̄` lying over a bijection `G_s̃ ≅ G_s̄`, which
is bijective on the fibres over each `q̄ᵢ` (these fibres being the stalks of the locally constant
sheaves `Fᵢ`), is bijective.
-/

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace SGA.SGA1.ExposeXIII

/-- XIII.6.1.2, stalkwise step of the proof. Let `b : Fs → Fb` (the specialization map
`F_s̃ → F_s̄`) lie over a bijection `c : Gs ≃ Gb` (`G_s̃ ≅ G_s̄`), via `as' : Fs → Gs` and
`ab : Fb → Gb`. Let the `q i` exhaust `Gs`, and let `asi i : Fsi i → Fs`, `abi i : Fbi i → Fb`
identify the stalks of `Fᵢ` with the fibres of `as'` over `q i` and of `ab` over `c (q i)`,
compatibly with bijections `Fsi i ≃ Fbi i` (the `Fᵢ` being locally constant). Then `b` is
bijective. -/
theorem bijective_of_bijective_on_fibres {Fs : Type u₁} {Fb : Type u₂} {Gs : Type u₃}
    {Gb : Type u₄} {κ : Type u₅} (b : Fs → Fb) (c : Gs ≃ Gb) (as' : Fs → Gs) (ab : Fb → Gb)
    (hcomm : ∀ x, ab (b x) = c (as' x)) (q : κ → Gs) (hq : Function.Surjective q)
    {Fsi : κ → Type u₆} {Fbi : κ → Type u₇} (e : ∀ i, Fsi i ≃ Fbi i)
    (asi : ∀ i, Fsi i → Fs) (abi : ∀ i, Fbi i → Fb)
    (hasi : ∀ i, Function.Injective (asi i) ∧ Set.range (asi i) = as' ⁻¹' {q i})
    (habi : ∀ i, Function.Injective (abi i) ∧ Set.range (abi i) = ab ⁻¹' {c (q i)})
    (hcommi : ∀ i y, b (asi i y) = abi i (e i y)) : Function.Bijective b := by
  refine ⟨fun x x' h ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hq (as' x)
    have hx' : as' x' = q i := c.injective (by rw [← hcomm, ← h, hcomm, hi])
    obtain ⟨y, rfl⟩ : x ∈ Set.range (asi i) := by rw [(hasi i).2]; exact hi.symm
    obtain ⟨y', rfl⟩ : x' ∈ Set.range (asi i) := by rw [(hasi i).2]; exact hx'
    rw [hcommi, hcommi] at h
    rw [(e i).injective ((habi i).1 h)]
  · obtain ⟨i, hi⟩ := hq (c.symm (ab z))
    obtain ⟨w, rfl⟩ : z ∈ Set.range (abi i) := by
      rw [(habi i).2, Set.mem_preimage, Set.mem_singleton_iff, hi, Equiv.apply_symm_apply]
    exact ⟨asi i ((e i).symm w), by rw [hcommi, Equiv.apply_symm_apply]⟩

end SGA.SGA1.ExposeXIII
