/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeX.Purity
import SGA.Foundations.CommAlg.PurityStalk

/-!
# SGA 1, Exposé X, 3.1: the purity theorem of Zariski–Nagata

X.3.1 (`purity : PurityStatement`) is deduced from its local form X.3.2 (`localPurity`), as in
SGA: at a generic point `z` of an irreducible component of the non-étale locus `Z` of
`f : X ⟶ Y`, the local ring `𝒪_{X,z}` is quasi-finite over the regular local ring `𝒪_{Y,f z}` and
étale over it at every non-maximal prime (these are the proper generizations of `z`, which lie
outside `Z`). If `dim 𝒪_{X,z} ≥ 2`, then `dim 𝒪_{Y,f z} ≥ 2` and X.3.2 makes `f` étale at `z`; and
`dim 𝒪_{X,z} ≠ 0` since otherwise `z` would be the generic point of `X` and `Z = X`.

The translation between étaleness of `f` on a neighbourhood of a point and formal étaleness of the
stalk map is in `SGA.Foundations.CommAlg.PurityStalk`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeX

/-- The set of points at which a morphism is étale is open. -/
lemma isOpen_setOf_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) : IsOpen {x : X | EtaleAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hxU, hU⟩
  exact ⟨U, fun w hw ↦ ⟨U, hw, hU⟩, U.2, hxU⟩

/-- A morphism locally of finite presentation is étale at `x` iff its stalk map at `x` is formally
étale. -/
lemma etaleAt_iff_formallyEtale_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X) :
    EtaleAt f x ↔ (f.stalkMap x).hom.FormallyEtale :=
  ⟨fun ⟨U, hxU, _⟩ ↦ formallyEtale_stalkMap_of_etale_ι f U hxU,
    exists_etale_of_formallyEtale_stalkMap f x⟩

/-- X.3.1, purity theorem of Zariski–Nagata (SGA 2 X.3.4). Let `f : X ⟶ Y` be a quasi-finite
dominant morphism of integral schemes, `X` normal and `Y` regular and locally noetherian, and let
`Z` be the set of points where `f` is not étale. If `Z ≠ X`, then `Z` has codimension `1` at each
of its points: the local ring of `X` at the generic point `z` of any irreducible component of `Z`
has dimension `1`. -/
theorem purity : PurityStatement.{u} := by
  intro X Y f _ _ _ _ _ _ hX hY hZ z hz hmin
  have hclosed : IsClosed {x : X | ¬ EtaleAt f x} := (isOpen_setOf_etaleAt f).isClosed_compl
  rw [ringKrullDim_stalk_eq_coheight]
  -- `z` is not the generic point of `X`, since `Z ≠ X`
  have h1 : Order.coheight z ≠ 0 := by
    intro h0
    rw [Order.coheight_eq_zero] at h0
    have hzη : z ⤳ genericPoint X := h0 (genericPoint_specializes z)
    apply hZ
    refine Set.eq_univ_of_forall fun w ↦ ?_
    have hη : genericPoint X ∈ {x : X | ¬ EtaleAt f x} := hzη.mem_closed hclosed hz
    exact (genericPoint_specializes w).mem_closed hclosed hη
  -- `dim 𝒪_{X,z} ≤ 1`, by X.3.2
  have h2 : ¬ 2 ≤ Order.coheight z := by
    intro h2
    apply hz
    have : LocallyOfFinitePresentation f :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    refine exists_etale_of_formallyEtale_stalkMap f z ?_
    let A := Y.presheaf.stalk (f z)
    let B := X.presheaf.stalk z
    let _ : Algebra A B := (f.stalkMap z).hom.toAlgebra
    change Algebra.FormallyEtale A B
    have : IsRegularLocalRing A := hY (f z)
    have : IsDomain B := (hX z).1
    have : IsIntegrallyClosed B := (hX z).2
    have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
    have : Algebra.EssFiniteType A B := LocallyOfFiniteType.stalkMap f z
    have : Algebra.QuasiFinite A B := f.quasiFiniteAt z
    have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
    have hinj : Function.Injective (algebraMap A B) := f.stalkMap_injective_of_isDominant z
    have hdimA : 2 ≤ ringKrullDim A := by
      have := IsLocalRing.ringKrullDim_le_of_quasiFinite (A := A) (B := B)
      rw [ringKrullDim_stalk_eq_coheight] at this
      exact le_trans (WithBot.coe_le_coe.mpr h2) this
    refine localPurity A B hinj hdimA fun p _ hp ↦ ?_
    refine isEtaleAt_stalk_of_forall_specializes (fun w hwz hwne ↦ ?_) p hp
    by_contra hw
    exact hwne (hmin w hw hwz)
  -- hence `dim 𝒪_{X,z} = 1`
  induction h : Order.coheight z using ENat.recTopCoe with
  | top => exact absurd (h ▸ le_top) h2
  | coe n =>
    rw [h] at h1 h2
    have hn1 : n ≠ 0 := by exact_mod_cast h1
    have hn2 : n < 2 := by
      by_contra hn
      exact h2 (by exact_mod_cast not_lt.mp hn)
    have : n = 1 := by omega
    subst this
    rfl

end SGA.SGA1.ExposeX
