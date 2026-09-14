/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFiniteModules

/-!
# Full faithfulness of Hom restricted to finite supported modules

Arbitrary supported modules are detected, with all their morphisms, by their
actual additive Hom functors on finite supported modules. The recovered map
is defined on each finite cyclic submodule. Naturality on larger finite spans
proves linearity; naturality on finite images proves the original natural
transformation is postcomposition by that map. No representation theorem is
assumed, and the argument does not require a noetherian ring.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual category of arbitrary modules supported on `V(J)`. -/
abbrev SupportedModuleCat (J : Ideal R) := (supportedModuleProperty J).FullSubcategory

/-- Actual restricted additive Yoneda, before restricting its target module. -/
abbrev supportedModuleRepresentations (J : Ideal R) : ModuleCat.{u} R ⥤
    ((SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  preadditiveYoneda ⋙
    (whiskeringLeft (SupportedFGModuleCat J)ᵒᵖ (ModuleCat R)ᵒᵖ AddCommGrpCat).obj
      (supportedFiniteToModule J).op

/-- The same restricted Hom functor on the actual supported source category. -/
def supportedModuleRestrictedHom (J : Ideal R) : SupportedModuleCat J ⥤
    ((SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (supportedModuleProperty J).ι ⋙ supportedModuleRepresentations J

/-- Every actual finite submodule of a supported module is a finite supported
test object, with no chosen presentation. -/
def finiteSupportedSubmodule (J : Ideal R) (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty J H) (P : Submodule R H) [Module.Finite R P] :
    SupportedFGModuleCat J :=
  ⟨FGModuleCat.of R P,
    (Module.support_subset_of_injective P.subtype Subtype.val_injective).trans hH⟩

/-- The actual inclusion of this finite test submodule. -/
def finiteSupportedSubmoduleι (J : Ideal R) (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty J H) (P : Submodule R H) [Module.Finite R P] :
    (finiteSupportedSubmodule J H hH P).obj.obj ⟶ H :=
  ModuleCat.ofHom P.subtype

variable (J : Ideal R) {H K : ModuleCat.{u} R}
  (hH : supportedModuleProperty J H)
  (α : (supportedModuleRepresentations J).obj H ⟶ (supportedModuleRepresentations J).obj K)

/-- Recover the value on `x` from its actual finite cyclic submodule. -/
def supportedRestrictedHomValue (x : H) : K :=
  ModuleCat.Hom.hom (α.app (op (finiteSupportedSubmodule J H hH (Submodule.span R {x})))
    (finiteSupportedSubmoduleι J H hH (Submodule.span R {x})))
      ⟨x, Submodule.mem_span_singleton_self x⟩

/-- Any finite submodule containing `x` computes this same value. This is
the independence statement needed to combine cyclic tests. -/
theorem supportedRestrictedHomValue_eq (P : Submodule R H) [Module.Finite R P]
    (x : H) (hx : x ∈ P) :
    supportedRestrictedHomValue J hH α x =
      ModuleCat.Hom.hom (α.app (op (finiteSupportedSubmodule J H hH P))
        (finiteSupportedSubmoduleι J H hH P)) ⟨x, hx⟩ := by
  let Q := Submodule.span R ({x} : Set H)
  have hQP : Q ≤ P := Submodule.span_le.mpr (by simpa using hx)
  let j : finiteSupportedSubmodule J H hH Q ⟶ finiteSupportedSubmodule J H hH P :=
    ObjectProperty.homMk (FGModuleCat.ofHom (Submodule.inclusion hQP))
  have h := ConcreteCategory.congr_hom (α.naturality j.op)
    (finiteSupportedSubmoduleι J H hH P)
  have h' := congrArg (fun f : (finiteSupportedSubmodule J H hH Q).obj.obj ⟶ K ↦
    f ⟨x, Submodule.mem_span_singleton_self x⟩) h
  exact h'

/-- Recover a genuine `R`-linear map. Linearity follows from the linearity
of the component maps on finite spans, not an assumption on `α`. -/
def supportedRestrictedHomPreimage : H ⟶ K :=
  ModuleCat.ofHom
    { toFun := supportedRestrictedHomValue J hH α
      map_add' x y := by
        let P := Submodule.span R ({x, y} : Set H)
        have : Module.Finite R P :=
          Module.Finite.span_of_finite R ((Set.finite_singleton y).insert x)
        have hx : x ∈ P := Submodule.subset_span (by simp)
        have hy : y ∈ P := Submodule.subset_span (by simp)
        rw [supportedRestrictedHomValue_eq J hH α P (x + y) (P.add_mem hx hy),
          supportedRestrictedHomValue_eq J hH α P x hx,
          supportedRestrictedHomValue_eq J hH α P y hy]
        exact (ModuleCat.Hom.hom (α.app (op (finiteSupportedSubmodule J H hH P))
          (finiteSupportedSubmoduleι J H hH P))).map_add ⟨x, hx⟩ ⟨y, hy⟩
      map_smul' r x := by
        let P := Submodule.span R ({x} : Set H)
        have hx : x ∈ P := Submodule.mem_span_singleton_self x
        rw [supportedRestrictedHomValue_eq J hH α P (r • x) (P.smul_mem r hx),
          supportedRestrictedHomValue_eq J hH α P x hx]
        exact (ModuleCat.Hom.hom (α.app (op (finiteSupportedSubmodule J H hH P))
          (finiteSupportedSubmoduleι J H hH P))).map_smul r ⟨x, hx⟩ }

/-- On every finite supported test module, the original transformation is
postcomposition by the recovered map. The proof uses the actual finite image. -/
theorem supportedRestrictedHomPreimage_naturality (M : SupportedFGModuleCat J)
    (g : M.obj.obj ⟶ H) (x : M.obj) :
    ModuleCat.Hom.hom (α.app (op M) g) x = supportedRestrictedHomPreimage J hH α (g x) := by
  let P := g.hom.range
  have : Module.Finite R P := Module.Finite.range g.hom
  let j : M ⟶ finiteSupportedSubmodule J H hH P :=
    ObjectProperty.homMk (FGModuleCat.ofHom g.hom.rangeRestrict)
  have h := ConcreteCategory.congr_hom (α.naturality j.op)
    (finiteSupportedSubmoduleι J H hH P)
  have h' := congrArg (fun f : M.obj.obj ⟶ K ↦ f x) h
  change ModuleCat.Hom.hom (α.app (op M) g) x =
    ModuleCat.Hom.hom (α.app (op (finiteSupportedSubmodule J H hH P))
      (finiteSupportedSubmoduleι J H hH P)) ⟨g x, ⟨x, rfl⟩⟩ at h'
  exact h'.trans (supportedRestrictedHomValue_eq J hH α P (g x) ⟨x, rfl⟩).symm

@[simp] theorem supportedModuleRepresentations_map_preimage :
    (supportedModuleRepresentations J).map (supportedRestrictedHomPreimage J hH α) = α := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  apply ModuleCat.hom_ext
  ext x
  exact (supportedRestrictedHomPreimage_naturality J hH α M.unop g x).symm

@[simp] theorem supportedModuleRepresentations_preimage_map (f : H ⟶ K) :
    supportedRestrictedHomPreimage J hH ((supportedModuleRepresentations J).map f) = f := by
  ext x
  rfl

/-- Full faithfulness of actual restricted Hom on arbitrary supported modules.
Neither source nor target module is assumed finitely generated. -/
def supportedModuleRestrictedHomFullyFaithful : (supportedModuleRestrictedHom J).FullyFaithful where
  preimage {H _K} α := ObjectProperty.homMk
    (supportedRestrictedHomPreimage J H.property α)
  map_preimage α := supportedModuleRepresentations_map_preimage J _ α
  preimage_map f := ObjectProperty.hom_ext _ (supportedModuleRepresentations_preimage_map J _ f.hom)

instance : (supportedModuleRestrictedHom J).Full :=
  (supportedModuleRestrictedHomFullyFaithful J).full

instance : (supportedModuleRestrictedHom J).Faithful :=
  (supportedModuleRestrictedHomFullyFaithful J).faithful

end SGA.SGA2.ExposeIV
