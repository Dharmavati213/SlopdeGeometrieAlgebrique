/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.ExtCoefficientSequence
import SGA.SGA2.ExposeII.InjectiveLocalCohomology

/-!
# SGA 2, Exposé II, (7.6): connecting maps on Ext colimits

An inverse sequence of modules gives coefficient functors by taking the
filtered colimit of Ext. The finite coefficient boundaries are natural in
the inverse sequence, so they induce actual connecting maps on the colimit.
Exactness passes through the filtered colimit, and positive degrees vanish
on injective coefficients. This applies in particular to the quotient
system defined by powers of a finite list of generators.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The Ext diagram of an inverse module sequence, functorially in the
coefficient module. -/
def extColimitDiagramFunctor (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.{u} R ⥤ (ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Q.op ⋙ Ext R (ModuleCat.{u} R) i).flip

instance extColimitDiagramFunctor_additive (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (extColimitDiagramFunctor Q i).Additive where
  map_add := by
    intro E F f g
    apply NatTrans.ext
    funext j
    exact ((Ext R (ModuleCat.{u} R) i).obj (op (Q.obj j.unop))).map_add

/-- The filtered Ext colimit as a coefficient functor. -/
def extColimitFunctor (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  extColimitDiagramFunctor Q i ⋙ colim

instance extColimitFunctor_additive (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (extColimitFunctor Q i).Additive :=
  inferInstanceAs ((extColimitDiagramFunctor Q i ⋙ colim).Additive)

section Connecting

variable (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)

/-- The finite Ext coefficient boundaries form a morphism of direct
systems. -/
def extCoefficientδDiagram :
    (extColimitDiagramFunctor Q i).obj S.X₃ ⟶
      (extColimitDiagramFunctor Q (i + 1)).obj S.X₁ where
  app j := extCoefficientδ (Q.obj j.unop) S hS i
  naturality _ _ f := (extCoefficientδ_naturality (Q.map f.unop) S hS i).symm

@[reassoc (attr := simp)]
theorem extCoefficientδDiagram_comp :
    extCoefficientδDiagram Q S hS i ≫ (extColimitDiagramFunctor Q (i + 1)).map S.f = 0 := by
  apply NatTrans.ext
  funext j
  exact extCoefficientδ_comp (Q.obj j.unop) S hS i

@[reassoc (attr := simp)]
theorem comp_extCoefficientδDiagram :
    (extColimitDiagramFunctor Q i).map S.g ≫ extCoefficientδDiagram Q S hS i = 0 := by
  apply NatTrans.ext
  funext j
  exact comp_extCoefficientδ (Q.obj j.unop) S hS i

/-- The actual boundary on a filtered Ext colimit. -/
def extColimitδ :
    (extColimitFunctor Q i).obj S.X₃ ⟶ (extColimitFunctor Q (i + 1)).obj S.X₁ :=
  colim.map (extCoefficientδDiagram Q S hS i)

@[reassoc (attr := simp)]
theorem extColimitδ_comp :
    extColimitδ Q S hS i ≫ (extColimitFunctor Q (i + 1)).map S.f = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, extCoefficientδDiagram_comp, Functor.map_zero]

@[reassoc (attr := simp)]
theorem comp_extColimitδ :
    (extColimitFunctor Q i).map S.g ≫ extColimitδ Q S hS i = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, comp_extCoefficientδDiagram, Functor.map_zero]

/-- Exactness after the filtered Ext boundary. -/
theorem extColimit_exact₁ :
    (ShortComplex.mk _ _ (extColimitδ_comp Q S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (extCoefficientδDiagram_comp Q S hS i))
    (fun j => extCoefficient_exact₁ (Q.obj j.unop) S hS i)

include hS in
/-- Exactness at the middle coefficient module in the filtered Ext sequence. -/
theorem extColimit_exact₂ :
    (S.map (extColimitFunctor Q i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (S.map (extColimitDiagramFunctor Q i))
    (fun j => extCoefficient_exact₂ (Q.obj j.unop) S hS i)

/-- Exactness before the filtered Ext boundary. -/
theorem extColimit_exact₃ :
    (ShortComplex.mk _ _ (comp_extColimitδ Q S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (comp_extCoefficientδDiagram Q S hS i))
    (fun j => extCoefficient_exact₃ (Q.obj j.unop) S hS i)

end Connecting

/-- The filtered Ext boundary is natural in short exact coefficient
sequences. -/
theorem extColimitδ_naturality_coefficients
    (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (i : ℕ) :
    extColimitδ Q S hS i ≫ (extColimitFunctor Q (i + 1)).map φ.τ₁ =
      (extColimitFunctor Q i).map φ.τ₃ ≫ extColimitδ Q T hT i := by
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg colim.map
  apply NatTrans.ext
  funext j
  let P := projectiveResolution (Q.obj j.unop)
  change extCoefficientδ (Q.obj j.unop) S hS i ≫
      ((Ext R (ModuleCat.{u} R) (i + 1)).obj (op (Q.obj j.unop))).map φ.τ₁ =
    ((Ext R (ModuleCat.{u} R) i).obj (op (Q.obj j.unop))).map φ.τ₃ ≫
      extCoefficientδ (Q.obj j.unop) T hT i
  apply (cancel_mono (P.isoExt (i + 1) T.X₁).hom).mp
  simp only [extCoefficientδ, P, Category.assoc,
    projectiveResolution_isoExt_coeff_naturality, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp only [← Category.assoc]
  rw [projectiveResolution_isoExt_coeff_naturality]
  simp only [Category.assoc]
  exact congrArg (fun t => (P.isoExt i S.X₃).hom ≫ t)
    (homCohomologyδ_naturality_coefficients P.complex φ hS hT i)

/-- Filtered Ext colimits have coefficient boundaries with the exactness
required for the dimension-shifting comparison argument. -/
def extColimitConnectingSequence (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) where
  obj := extColimitFunctor Q
  δ := extColimitδ Q
  map_δ := comp_extColimitδ Q
  δ_map := extColimitδ_comp Q
  exact_left := extColimit_exact₃ Q
  exact_right := extColimit_exact₁ Q

/-- Every positive degree of a filtered Ext colimit vanishes on injective
coefficient modules. -/
theorem isZero_extColimitFunctor_succ_of_injective
    (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (E : ModuleCat.{u} R) [Injective E] (i : ℕ) :
    IsZero ((extColimitFunctor Q (i + 1)).obj E) := by
  apply isZero_colimit_of_zero_transitions
  intro j
  exact ⟨j, 𝟙 j, (isZero_Ext_succ_of_injective (Q.obj j.unop) E i).eq_of_src _ _⟩

/-- Positive-degree injective vanishing, in the form used by comparison
of connecting sequences. -/
theorem extColimitConnectingSequence_vanishesOnInjectives
    (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    (extColimitConnectingSequence Q).VanishesOnInjectives :=
  fun E _ i => isZero_extColimitFunctor_succ_of_injective Q E i

/-- The Ext side of II.(7.6), with its actual coefficient connecting maps. -/
def stableKoszulExtConnectingSequence (fs : List R) :
    ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) :=
  extColimitConnectingSequence (koszulQuotientSystem fs)

/-- The generic construction recovers the previously defined
generator-power Ext coefficient functor. -/
def stableKoszulExtConnectingSequenceObjIso (fs : List R) (i : ℕ) :
    (stableKoszulExtConnectingSequence fs).obj i ≅ stableKoszulExtFunctor fs i :=
  Iso.refl _

/-- Objectwise, the Ext coefficient functor is the colimit in II.(7.6). -/
def stableKoszulExtFunctorObjIso (fs : List R) (i : ℕ) (E : ModuleCat.{u} R) :
    (stableKoszulExtFunctor fs i).obj E ≅ colimit (koszulExtDiagram fs E i) :=
  Iso.refl _

/-- The generator-power Ext connecting sequence vanishes on injectives
in every positive degree, without a noetherian hypothesis. -/
theorem stableKoszulExtConnectingSequence_vanishesOnInjectives (fs : List R) :
    (stableKoszulExtConnectingSequence fs).VanishesOnInjectives :=
  extColimitConnectingSequence_vanishesOnInjectives _

end SGA.SGA2.ExposeII
