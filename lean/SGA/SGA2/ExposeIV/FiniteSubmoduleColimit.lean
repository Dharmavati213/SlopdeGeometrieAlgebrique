/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Every module is the actual filtered colimit of its finite submodules

This is the genuine finite-submodule presentation used to extend IV.1.1
to arbitrary modules in IV.1.2. Its universal property is proved directly
using actual inclusions of finite cyclic submodules and finite spans.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Actual finitely generated submodules, ordered by inclusion. -/
abbrev FiniteSubmoduleIndex (M : ModuleCat.{u} R) := {P : Submodule R M // P.FG}

instance (M : ModuleCat.{u} R) : Nonempty (FiniteSubmoduleIndex M) :=
  ⟨⟨⊥, Submodule.fg_bot⟩⟩

instance (M : ModuleCat.{u} R) : IsDirectedOrder (FiniteSubmoduleIndex M) where
  directed P Q := ⟨⟨P.val ⊔ Q.val, P.property.sup Q.property⟩, le_sup_left, le_sup_right⟩

instance (M : ModuleCat.{u} R) : IsFiltered (FiniteSubmoduleIndex M) := inferInstance

instance {M : ModuleCat.{u} R} (P : FiniteSubmoduleIndex M) : Module.Finite R P.val :=
  Module.Finite.iff_fg.mpr P.property

/-- The original finite-submodule inclusion diagram. -/
def finiteSubmoduleDiagram (M : ModuleCat.{u} R) :
    FiniteSubmoduleIndex M ⥤ ModuleCat.{u} R where
  obj P := ModuleCat.of R P.val
  map f := ModuleCat.ofHom (Submodule.inclusion (leOfHom f))
  map_id P := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The original module with the actual submodule inclusions. -/
def finiteSubmoduleCocone (M : ModuleCat.{u} R) : Cocone (finiteSubmoduleDiagram M) where
  pt := M
  ι :=
    { app P := ModuleCat.ofHom P.val.subtype
      naturality {P Q} f := by ext x; rfl }

/-- Every element has its canonical finite cyclic stage. -/
def finiteCyclicIndex {M : ModuleCat.{u} R} (x : M) : FiniteSubmoduleIndex M :=
  ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩

/-- The value of a cocone on an element, computed in its cyclic submodule. -/
def finiteSubmoduleCoconeValue {M : ModuleCat.{u} R}
    (s : Cocone (finiteSubmoduleDiagram M)) (x : M) : s.pt :=
  s.ι.app (finiteCyclicIndex x) ⟨x, Submodule.mem_span_singleton_self x⟩

/-- Any finite submodule containing an element computes the same value. -/
theorem finiteSubmoduleCoconeValue_eq {M : ModuleCat.{u} R}
    (s : Cocone (finiteSubmoduleDiagram M)) (P : FiniteSubmoduleIndex M)
    (x : M) (hx : x ∈ P.val) :
    finiteSubmoduleCoconeValue s x = s.ι.app P ⟨x, hx⟩ := by
  have h : (finiteCyclicIndex x).val ≤ P.val := Submodule.span_le.mpr (by simpa using hx)
  exact (ConcreteCategory.congr_hom (s.w (homOfLE h))
    (⟨x, Submodule.mem_span_singleton_self x⟩ : (finiteCyclicIndex x).val)).symm

/-- The canonical cocone descent map is genuinely linear. -/
def finiteSubmoduleCoconeDesc {M : ModuleCat.{u} R}
    (s : Cocone (finiteSubmoduleDiagram M)) : M ⟶ s.pt :=
  ModuleCat.ofHom
    { toFun := finiteSubmoduleCoconeValue s
      map_add' x y := by
        let P : FiniteSubmoduleIndex M :=
          ⟨Submodule.span R {x, y}, Submodule.fg_span ((Set.finite_singleton y).insert x)⟩
        have hx : x ∈ P.val := Submodule.subset_span (by simp)
        have hy : y ∈ P.val := Submodule.subset_span (by simp)
        rw [finiteSubmoduleCoconeValue_eq s P (x + y) (P.val.add_mem hx hy),
          finiteSubmoduleCoconeValue_eq s P x hx, finiteSubmoduleCoconeValue_eq s P y hy]
        exact (s.ι.app P).hom.map_add ⟨x, hx⟩ ⟨y, hy⟩
      map_smul' r x := by
        let P := finiteCyclicIndex x
        have hx : x ∈ P.val := Submodule.mem_span_singleton_self x
        rw [finiteSubmoduleCoconeValue_eq s P (r • x) (P.val.smul_mem r hx),
          finiteSubmoduleCoconeValue_eq s P x hx]
        exact (s.ι.app P).hom.map_smul r ⟨x, hx⟩ }

/-- Every actual module is the categorical filtered colimit of its actual
finite submodules; no noetherianity assumption is needed. -/
def finiteSubmoduleCoconeIsColimit (M : ModuleCat.{u} R) :
    IsColimit (finiteSubmoduleCocone M) where
  desc s := finiteSubmoduleCoconeDesc s
  fac s P := by
    ext x
    exact finiteSubmoduleCoconeValue_eq s P x.val x.property
  uniq s f hf := by
    ext x
    exact ConcreteCategory.congr_hom (hf (finiteCyclicIndex x))
      (⟨x, Submodule.mem_span_singleton_self x⟩ : (finiteCyclicIndex x).val)

end SGA.SGA2.ExposeIV
