/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedExcision
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.Limits

/-! # Sections of the actual supported-section kernel sheaf -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The naive open pullback is left adjoint to the actual pushforward, by the
image/preimage adjunction on open sets. -/
def naiveOpenPullbackAdjunction (V : Opens X) :
    V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⊣
      Sheaf.pushforward AddCommGrpCat.{u} V.inclusion' :=
  ((V.isOpenEmbedding.isOpenMap.adjunction.op).whiskerLeft AddCommGrpCat.{u}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (fullyFaithfulSheafToPresheaf
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) AddCommGrpCat.{u})
    (Iso.refl _) (Iso.refl _)

/-- Comparison of actual and naive open pullback, chosen to intertwine their
adjunction units. Both pullback functors and the original unit remain unchanged. -/
def openPullbackUnitIso (V : Opens X) :
    Sheaf.pullback AddCommGrpCat.{u} V.inclusion' ≅
      V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} V.inclusion').leftAdjointUniq
    (naiveOpenPullbackAdjunction V)

/-- The unit of the naive open adjunction is explicitly restriction to the
image of the preimage of the open. -/
theorem naiveOpenPullbackAdjunction_unit_app (V U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((naiveOpenPullbackAdjunction V).unit.app F).hom.app (op U) =
      F.presheaf.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app U).op := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
      (L := V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})
      (R := Sheaf.pushforward AddCommGrpCat.{u} V.inclusion')
      ((V.isOpenEmbedding.isOpenMap.adjunction.op).whiskerLeft AddCommGrpCat.{u})
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fullyFaithfulSheafToPresheaf
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) AddCommGrpCat.{u})
      (Iso.refl _) (Iso.refl _) F
  have h' := congrArg (fun k => k.app (op U)) h
  simpa [naiveOpenPullbackAdjunction] using h'

/-- The actual pullback-pushforward unit becomes explicit restriction under
the unit-compatible isomorphism with naive pullback. -/
theorem openPullbackUnitIso_unit_app (V U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} V.inclusion').unit.app F).hom.app
        (op U) ≫
      ((openPullbackUnitIso V).hom.app F).hom.app
        (op ((Opens.map V.inclusion').obj U)) =
      F.presheaf.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app U).op := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} V.inclusion')
    (naiveOpenPullbackAdjunction V) F
  have h' := congrArg (fun k => k.hom.app (op U)) h
  exact h'.trans (naiveOpenPullbackAdjunction_unit_app V U F)

/-- Sections of the actual complement pushforward are sections over the open
complement inside `U`. -/
def complementPushforwardSectionsIso (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) :
    ((Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).obj
      ((Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z)).obj F)).presheaf.obj (op U) ≅
      F.presheaf.obj (op (U ⊓ Z.compl)) :=
  (((sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj Z.compl))
      AddCommGrpCat.{u}).mapIso ((openPullbackUnitIso Z.compl).app F)).app
    (op ((Opens.map Z.compl.inclusion').obj U))) ≪≫
      F.presheaf.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf Z.compl U)))

/-- The original unit defining `underlineGammaZ` corresponds to the explicit
restriction to `U ∩ (X \ Z)`. -/
theorem toComplementPushforward_comp_sectionsIso (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) :
    (toComplementPushforward F Z).hom.app (op U) ≫
      (complementPushforwardSectionsIso F Z U).hom = restrictToComplement F Z U := by
  let k := eqToHom (congrArg op (Opens.functor_map_eq_inf Z.compl U))
  change ((Sheaf.pullbackPushforwardAdjunction
      AddCommGrpCat.{u} Z.compl.inclusion').unit.app F).hom.app
      (op U) ≫
    (((openPullbackUnitIso Z.compl).hom.app F).hom.app
      (op ((Opens.map Z.compl.inclusion').obj U)) ≫ F.presheaf.map k) = _
  rw [← Category.assoc, openPullbackUnitIso_unit_app, ← F.presheaf.map_comp]
  congr 1

/-- Evaluation of the existing kernel sheaf is the kernel of the evaluated
actual unit; this uses preservation of kernels by sheaf sections. -/
def underlineGammaZSectionsIsoKernel (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) :
    (underlineGammaZ F Z).presheaf.obj (op U) ≅
      kernel ((toComplementPushforward F Z).hom.app (op U)) := by
  have : PreservesLimits ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)) := inferInstanceAs (PreservesLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)))
  exact PreservesKernel.iso
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))
    (toComplementPushforward F Z)

/-- Sections of the original supported-section kernel sheaf are precisely the
concrete supported sections. -/
def underlineGammaZSectionsEquiv (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) :
    (underlineGammaZ F Z).presheaf.obj (op U) ≃+ gammaZSections F Z U :=
  (((underlineGammaZSectionsIsoKernel F Z U) ≪≫
    AddCommGrpCat.kernelIsoKer ((toComplementPushforward F Z).hom.app
      (op U))).addCommGroupIsoToAddEquiv).trans
    (kerAddEquivOfCommSq ((toComplementPushforward F Z).hom.app (op U)).hom
      (restrictToComplement F Z U).hom (AddEquiv.refl _)
      (complementPushforwardSectionsIso F Z U).addCommGroupIsoToAddEquiv
      (fun x => ConcreteCategory.congr_hom (toComplementPushforward_comp_sectionsIso F Z U) x))

/-- The supported-section equivalence respects the original inclusion of the
kernel sheaf into `F`. -/
theorem underlineGammaZSectionsEquiv_val (F : Sheaf AddCommGrpCat.{u} X)
    (Z : Closeds X) (U : Opens X) (s : (underlineGammaZ F Z).presheaf.obj (op U)) :
    (underlineGammaZSectionsEquiv F Z U s).val = (underlineGammaZ_ι F Z).hom.app (op U) s := by
  have : PreservesLimits ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)) := inferInstanceAs (PreservesLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)))
  change (kernel.ι ((toComplementPushforward F Z).hom.app (op U)))
    ((underlineGammaZSectionsIsoKernel F Z U).hom s) = _
  simp only [underlineGammaZSectionsIsoKernel, PreservesKernel.iso_hom]
  exact ConcreteCategory.congr_hom
    (kernelComparison_comp_ι (toComplementPushforward F Z)
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))) s

/-- Naturality of the original supported-sheaf inclusion. -/
@[reassoc (attr := simp)]
theorem underlineGammaZMap_comp_ι {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    (Z : Closeds X) :
    underlineGammaZMap φ Z ≫ underlineGammaZ_ι G Z = underlineGammaZ_ι F Z ≫ φ := by
  simp [underlineGammaZMap, kernel.map]

/-- The section comparison is natural in the coefficient sheaf. -/
theorem underlineGammaZSectionsEquiv_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G) (Z : Closeds X) (U : Opens X)
    (s : (underlineGammaZ F Z).presheaf.obj (op U)) :
    underlineGammaZSectionsEquiv G Z U ((underlineGammaZMap φ Z).hom.app (op U) s) =
      gammaZSectionsMap φ Z U (underlineGammaZSectionsEquiv F Z U s) := by
  apply Subtype.ext
  rw [underlineGammaZSectionsEquiv_val, gammaZSectionsMap_apply, underlineGammaZSectionsEquiv_val]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.hom.app (op U)) (underlineGammaZMap_comp_ι φ Z)) s

/-- Restriction of the concrete supported-section subgroups. -/
def gammaZSectionsRestriction (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X)
    {V U : Opens X} (i : V ⟶ U) : gammaZSections F Z U →+ gammaZSections F Z V where
  toFun s := ⟨F.presheaf.map i.op s.val, restrict_mem_gammaZSections F (leOfHom i) s.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _s _t := Subtype.ext (map_add _ _ _)

/-- The section comparison commutes with restriction to smaller opens. -/
theorem underlineGammaZSectionsEquiv_restrict (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X)
    {V U : Opens X} (i : V ⟶ U) (s : (underlineGammaZ F Z).presheaf.obj (op U)) :
    underlineGammaZSectionsEquiv F Z V ((underlineGammaZ F Z).presheaf.map i.op s) =
      gammaZSectionsRestriction F Z i (underlineGammaZSectionsEquiv F Z U s) := by
  apply Subtype.ext
  change (underlineGammaZSectionsEquiv F Z V ((underlineGammaZ F Z).presheaf.map i.op s)).val =
    F.presheaf.map i.op (underlineGammaZSectionsEquiv F Z U s).val
  rw [underlineGammaZSectionsEquiv_val, underlineGammaZSectionsEquiv_val]
  exact (underlineGammaZ_ι F Z).hom.naturality_apply i.op s

/-- The original supported-sheaf functor is additive. -/
instance underlineGammaZFunctor_additive (Z : Closeds X) :
    (underlineGammaZFunctor Z).Additive where
  map_add {F G} φ ψ := by
    apply (cancel_mono (underlineGammaZ_ι G Z)).mp
    change underlineGammaZMap (φ + ψ) Z ≫ underlineGammaZ_ι G Z =
      (underlineGammaZMap φ Z + underlineGammaZMap ψ Z) ≫ underlineGammaZ_ι G Z
    simp only [Preadditive.add_comp, underlineGammaZMap_comp_ι, Preadditive.comp_add]

/-- Naturality of sections of the actual supported sheaf, packaged as an
isomorphism of coefficient functors. -/
def underlineGammaZSectionsFunctorIso (Z : Closeds X) (U : Opens X) :
    underlineGammaZFunctor Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U) ≅
        gammaZSectionsFunctor Z U :=
  NatIso.ofComponents (fun F => (underlineGammaZSectionsEquiv F Z U).toAddCommGrpIso)
    (fun φ => by ext s; exact underlineGammaZSectionsEquiv_naturality φ Z U s)

/-- The actual supported-sheaf functor preserves finite limits, as can be
checked after evaluation on every open using concrete supported sections. -/
instance underlineGammaZFunctor_preservesFiniteLimits (Z : Closeds X) :
    PreservesFiniteLimits (underlineGammaZFunctor Z) := by
  let P := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have : ReflectsFiniteLimits P :=
    reflectsFiniteLimits_of_reflectsIsomorphisms P
  have : PreservesFiniteLimits (underlineGammaZFunctor Z ⋙ P) :=
    preservesFiniteLimits_of_evaluation _ (fun U => by
      change PreservesFiniteLimits (underlineGammaZFunctor Z ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U.unop))
      exact preservesFiniteLimits_of_natIso (underlineGammaZSectionsFunctorIso Z U.unop).symm)
  exact preservesFiniteLimits_of_reflects_of_preserves (underlineGammaZFunctor Z) P

/-- The concrete presheaf whose sections on `U` are `gammaZSections F Z U`. -/
def gammaZSectionsPresheaf (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X) :
    X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (gammaZSections F Z U.unop)
  map i := AddCommGrpCat.ofHom (gammaZSectionsRestriction F Z i.unop)
  map_id U := by
    ext s
    change F.presheaf.map (𝟙 U) s.val = s.val
    rw [F.presheaf.map_id]
    rfl
  map_comp i j := by
    ext s
    change F.presheaf.map (i ≫ j) s.val = F.presheaf.map j (F.presheaf.map i s.val)
    rw [F.presheaf.map_comp]
    rfl

/-- The concrete supported presheaf, functorially in the coefficient sheaf. -/
def gammaZSectionsPresheafFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ X.Presheaf AddCommGrpCat.{u} where
  obj F := gammaZSectionsPresheaf F Z
  map φ :=
    { app U := AddCommGrpCat.ofHom (gammaZSectionsMap φ Z U.unop)
      naturality {U V} i := by
        ext s
        apply Subtype.ext
        exact φ.hom.naturality_apply i s.val }
  map_id F := by ext U s; rfl
  map_comp φ ψ := by ext U s; rfl

instance gammaZSectionsPresheafFunctor_additive (Z : Closeds X) :
    (gammaZSectionsPresheafFunctor Z).Additive where
  map_add {F G} φ ψ := by ext U s; rfl

/-- The underlying presheaf of the original kernel sheaf is naturally the
concrete supported-section presheaf, in both coefficients and opens. -/
def underlineGammaZPresheafFunctorIso (Z : Closeds X) :
    underlineGammaZFunctor Z ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
      gammaZSectionsPresheafFunctor Z :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun U => (underlineGammaZSectionsEquiv F Z U.unop).toAddCommGrpIso)
      (fun i => by ext s; exact underlineGammaZSectionsEquiv_restrict F Z i.unop s))
    (fun φ => by
      apply NatTrans.ext
      funext U
      ext s
      exact underlineGammaZSectionsEquiv_naturality φ Z U.unop s)

end SGA.SGA2.ExposeI
