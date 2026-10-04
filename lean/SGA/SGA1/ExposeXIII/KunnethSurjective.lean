/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup

/-!
# SGA 1, XIII.4.6: the surjectivity half of the Künneth formula

For connected schemes `X`, `Y` over an algebraically closed field `k` and any geometric point `c`
of `X ×ₖ Y`, the map `π₁(X ×ₖ Y, c) → π₁(X, c) × π₁(Y, c)` is surjective
(`surjective_map_prod_of_isAlgClosed`), in every characteristic and with no finiteness
hypothesis. This is the "easy half" of XIII.4.6; the injectivity is the content of
`KunnethCharZeroStatement` (in characteristic `0`).

Let `y = pr₂ ∘ c` and `X_y = (X ×ₖ Y) ×_Y Spec Ω ≅ X ⊗ₖ Ω` the fibre of `pr₂` at `y`. Then:

* `π₁(X ×ₖ Y) → π₁(Y)` is surjective (V.6.9): for a connected étale covering `E → Y`,
  `E ×_Y (X ×ₖ Y) ≅ X ×ₖ E` is connected
  (`connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`);
* `π₁(X_y) → π₁(X ×ₖ Y) → π₁(X)` is surjective (V.6.9): for a connected étale covering `E → X`,
  `E ×_X X_y ≅ E ⊗ₖ Ω` is connected, as `E` is geometrically connected over `k`
  (`geometricallyConnected_of_isAlgClosed`);
* `π₁(X_y) → π₁(X ×ₖ Y) → π₁(Y)` is trivial (XIII.4.0, `FundamentalGroup.map_comp_map_fst_eq_one`);

and group theory concludes (`surjective_prod_of_surjective_comp`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

section Group

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]

/-- Let `i : A → B`, `p : B → C`, `q : B → D` with `p` surjective, `p ∘ i` trivial and `q ∘ i`
surjective. Then `(q, p) : B → D × C` is surjective. -/
theorem surjective_prod_of_surjective_comp (i : A →* B) (p : B →* C) (q : B →* D)
    (hqi : Function.Surjective (q.comp i)) (hpi : p.comp i = 1) (hp : Function.Surjective p) :
    Function.Surjective (q.prod p) := by
  rintro ⟨d, c⟩
  obtain ⟨b, rfl⟩ := hp c
  obtain ⟨a, ha⟩ := hqi ((q b)⁻¹ * d)
  refine ⟨b * i a, Prod.ext ?_ ?_⟩
  · change q (b * i a) = d
    rw [map_mul, ← MonoidHom.comp_apply, ha, mul_inv_cancel_left]
  · change p (b * i a) = p b
    rw [map_mul, ← MonoidHom.comp_apply, hpi, MonoidHom.one_apply, mul_one]

end Group

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  (fY : Y ⟶ Spec (.of k))

/-- The inverse image in `X ×ₖ Y` of a connected scheme `E` over `Y` is connected, if `X` is
connected. -/
theorem connectedSpace_pullback_pullback_snd [ConnectedSpace X] {E : Scheme.{u}} (e : E ⟶ Y)
    [ConnectedSpace E] : ConnectedSpace ↥(pullback e (pullback.snd fX fY)) := by
  have h := (IsPullback.of_hasPullback e (pullback.snd fX fY)).paste_vert
    (IsPullback.of_hasPullback fX fY).flip
  have := connectedSpace_pullback_of_isAlgClosed_of_connectedSpace (e ≫ fY) fX
  exact (Scheme.homeoOfIso h.isoPullback.symm).surjective.connectedSpace
    (Scheme.homeoOfIso h.isoPullback.symm).continuous

/-- XIII.4.6, surjectivity half only (in every characteristic, with no finiteness or
desingularization hypothesis), for `k` algebraically closed: let `X`, `Y` be connected schemes over
an algebraically closed field `k` and `c` a geometric point of `X ×ₖ Y`. Then
`π₁(X ×ₖ Y, c) → π₁(X, c) × π₁(Y, c)` is surjective.

Deviation: SGA assumes only `k` separably closed. The reduction of that case to `k̄` (a purely
inseparable base change does not change the étale coverings, SGA 4 VIII 1.1) is not formalized
here. In characteristic `0`, the case of `KunnethCharZeroStatement`, separably closed fields are
algebraically closed. -/
theorem surjective_map_prod_of_isAlgClosed [ConnectedSpace X] [ConnectedSpace Y] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (c : Spec (.of Ω) ⟶ pullback fX fY) :
    Function.Surjective ((FundamentalGroup.map (pullback.fst fX fY) c).prod
      (FundamentalGroup.map (pullback.snd fX fY) c)) := by
  let y := c ≫ pullback.snd fX fY
  let i := pullback.fst (pullback.snd fX fY) y
  let c' : Spec (.of Ω) ⟶ pullback (pullback.snd fX fY) y :=
    pullback.lift c (𝟙 _) (by simp [y])
  have hc' : c' ≫ i = c := pullback.lift_fst _ _ _
  -- the fibre `X_y` is a base change of `X` along `y ≫ fY : Spec Ω ⟶ Spec k`
  have hXy := (IsPullback.of_hasPullback (pullback.snd fX fY) y).paste_horiz
    (IsPullback.of_hasPullback fX fY)
  have : ConnectedSpace ↥(pullback fX fY) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace fX fY
  have : ConnectedSpace ↥(pullback (pullback.snd fX fY) y) :=
    (geometricallyConnected_of_isAlgClosed fX).geometrically_connectedSpace (y ≫ fY) _ _ hXy
  suffices h : Function.Surjective ((FundamentalGroup.map (pullback.fst fX fY) (c' ≫ i)).prod
      (FundamentalGroup.map (pullback.snd fX fY) (c' ≫ i))) by
    rwa [hc'] at h
  refine surjective_prod_of_surjective_comp (FundamentalGroup.map i c') _ _ ?_
    (FundamentalGroup.map_comp_map_fst_eq_one (pullback.snd fX fY) y Ω c') ?_
  · -- `π₁(X_y) → π₁(X)` is surjective: `E ×_X X_y ≅ E ⊗ₖ Ω` is connected
    rw [FundamentalGroup.map, FundamentalGroup.map, ExposeV.etaleFundamentalGroup.map,
      ExposeV.etaleFundamentalGroup.map, ExposeV.autMap_comp]
    refine ExposeV.autMap_surjective _ _ fun E hE ↦ ?_
    have : ConnectedSpace ↥((𝟭 Scheme).obj E.left) := ExposeV.FEt.connectedSpace_of_isConnected E
    rw [ExposeV.FEt.isConnected_iff_connectedSpace]
    have hsq := ((IsPullback.of_hasPullback (pullback.snd E.hom (pullback.fst fX fY)) i).paste_horiz
      (IsPullback.of_hasPullback E.hom (pullback.fst fX fY))).paste_vert hXy
    exact (geometricallyConnected_of_isAlgClosed (E.hom ≫ fX)).geometrically_connectedSpace
      (y ≫ fY) _ _ hsq
  · -- `π₁(X ×ₖ Y) → π₁(Y)` is surjective: `E ×_Y (X ×ₖ Y) ≅ X ×ₖ E` is connected
    refine ExposeV.autMap_surjective _ _ fun E hE ↦ ?_
    have : ConnectedSpace ↥((𝟭 Scheme).obj E.left) := ExposeV.FEt.connectedSpace_of_isConnected E
    rw [ExposeV.FEt.isConnected_iff_connectedSpace]
    exact connectedSpace_pullback_pullback_snd fX fY E.hom

end SGA.SGA1.ExposeXIII
