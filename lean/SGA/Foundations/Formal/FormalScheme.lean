/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import SGA.Foundations.Formal.Spf

/-!
# Locally noetherian formal schemes

A *locally noetherian formal scheme* (EGA I, §10.4) is a locally ringed space which is
locally isomorphic to the formal spectrum `Spf A` of a noetherian ring `A` complete for an
`I`-adic topology. They form a full subcategory of locally ringed spaces.

EGA defines formal schemes as *topologically* ringed spaces and morphisms as morphisms of
topologically ringed spaces whose stalk maps are local. For locally noetherian formal schemes the
topology of the rings of sections is determined by the locally ringed space (on `Spf A` it is the
`I`-adic topology, and `I` may be replaced by any ideal with the same radical, `Spf.isoOfPowLE`),
so we do not record it.

## Main definitions and results

* `AlgebraicGeometry.LocallyRingedSpace.IsLocallyNoetherianFormalScheme`: the property.
* `AlgebraicGeometry.LocallyNoetherianFormalScheme`: the full subcategory.
* `AlgebraicGeometry.Spf.isLocallyNoetherianFormalScheme`: `Spf A` is one.
* `AlgebraicGeometry.Spf.isoSpecOfIsNilpotent`: for `I` nilpotent, `Spf A = Spec A`.
* `AlgebraicGeometry.Scheme.isLocallyNoetherianFormalScheme`: locally noetherian schemes are
  locally noetherian formal schemes (with the zero ideal of definition, EGA I, §10.4).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A locally ringed space is a *locally noetherian formal scheme* if every point has an open
neighbourhood isomorphic to `Spf A` for a noetherian ring `A` which is `I`-adically complete. -/
def LocallyRingedSpace.IsLocallyNoetherianFormalScheme :
    ObjectProperty LocallyRingedSpace.{u} := fun X ↦
  ∀ x : X, ∃ (U : OpenNhds x) (A : Type u) (_ : CommRing A) (I : Ideal A),
    IsNoetherianRing A ∧ IsAdicComplete I A ∧ Nonempty (X.restrict U.isOpenEmbedding ≅ Spf A I)

/-- The category of locally noetherian formal schemes, a full subcategory of locally ringed
spaces. -/
abbrev LocallyNoetherianFormalScheme :=
  LocallyRingedSpace.IsLocallyNoetherianFormalScheme.{u}.FullSubcategory

namespace LocallyRingedSpace

/-- Two open immersions with the same range have isomorphic sources. -/
noncomputable def isoOfRangeEq {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) :
    X ≅ Y where
  hom := IsOpenImmersion.lift g f e.le
  inv := IsOpenImmersion.lift f g e.ge
  hom_inv_id := by
    rw [← cancel_mono f, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono g, Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac,
      Category.id_comp]

namespace IsLocallyNoetherianFormalScheme

instance : IsLocallyNoetherianFormalScheme.{u}.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX y := by
    obtain ⟨U, A, _, I, hA, hI, ⟨f⟩⟩ := hX (e.inv.base y)
    let V : OpenNhds y := ⟨(Opens.map e.inv.base).obj U.1, U.2⟩
    refine ⟨V, A, inferInstance, I, hA, hI, ⟨?_ ≪≫ f⟩⟩
    refine isoOfRangeEq (Y.ofRestrict V.isOpenEmbedding ≫ e.inv)
      (X.ofRestrict U.isOpenEmbedding) ?_
    rw [comp_base, TopCat.coe_comp, Set.range_comp]
    change e.inv.base '' Set.range (Opens.inclusion' V.1) = Set.range (Opens.inclusion' U.1)
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact Set.image_preimage_eq _ (TopCat.homeoOfIso (forgetToTop.mapIso e.symm)).surjective

end IsLocallyNoetherianFormalScheme

end LocallyRingedSpace


namespace Spf

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- `Spf A` is a locally noetherian formal scheme when `A` is noetherian and `I`-adically
complete. -/
theorem isLocallyNoetherianFormalScheme [IsNoetherianRing A] [IsAdicComplete I A] :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme (Spf A I) := fun _ ↦
  ⟨⟨⊤, trivial⟩, A, inferInstance, I, inferInstance, inferInstance,
    ⟨LocallyRingedSpace.restrictTopIso _⟩⟩

/-- For the zero ideal all transition maps of `Spf.diagram` are isomorphisms. -/
instance isIso_diagram_bot_map {m n : ℕ} (f : m ⟶ n) :
    IsIso ((diagram A ⊥ ⋙ Scheme.forgetToLocallyRingedSpace).map f) := by
  have : IsIso ((ringDiagram A ⊥).map f.op) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun x y hxy ↦ ?_, Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f)))⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hxy : Ideal.Quotient.mk ((⊥ : Ideal A) ^ (m + 1)) a =
        Ideal.Quotient.mk ((⊥ : Ideal A) ^ (m + 1)) b := hxy
    rw [Ideal.Quotient.eq, Ideal.bot_pow (Nat.succ_ne_zero m)] at hxy
    rw [Ideal.Quotient.eq, Ideal.bot_pow (Nat.succ_ne_zero n)]
    exact hxy
  change IsIso (Scheme.forgetToLocallyRingedSpace.map (Spec.map ((ringDiagram A ⊥).map f.op)))
  infer_instance

/-- For the zero ideal, `Spf A` is `Spec A`. -/
noncomputable def isoSpecOfBot : Spf A ⊥ ≅ (Spec (.of A)).toLocallyRingedSpace := by
  have : IsIso (ι A ⊥ 0) := isIso_ι_of_isInitial isInitialBot _
  refine (asIso (ι A ⊥ 0)).symm ≪≫ Scheme.forgetToLocallyRingedSpace.mapIso
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso ?_).op)
  exact ((Ideal.quotEquivOfEq (by simp)).trans (RingEquiv.quotientBot A)).symm

/-- If `I` is nilpotent, `Spf A` computed with `I` is `Spec A` (EGA I, §10.1): a scheme is a
formal scheme with a nilpotent ideal of definition. -/
noncomputable def isoSpecOfIsNilpotent (hI : IsNilpotent I) :
    Spf A I ≅ (Spec (.of A)).toLocallyRingedSpace :=
  isoOfPowLE (J := ⊥) (by obtain ⟨k, hk⟩ := hI; exact ⟨k, hk.le⟩) ⟨1, by simp⟩ ≪≫
    isoSpecOfBot A

end Spf

/-- Locally noetherian schemes are locally noetherian formal schemes (with the zero ideal of
definition, EGA I, §10.4). -/
theorem Scheme.isLocallyNoetherianFormalScheme (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme X.toLocallyRingedSpace := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine ⟨⟨U, hxU⟩, Γ(X, U), inferInstance, ⊥, inferInstance, inferInstance, ⟨?_⟩⟩
  exact Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫ (Spf.isoSpecOfBot _).symm

end AlgebraicGeometry
