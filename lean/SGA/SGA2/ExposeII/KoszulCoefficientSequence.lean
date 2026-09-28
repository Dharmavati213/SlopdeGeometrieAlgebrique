/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulCohomology
import SGA.SGA2.ExposeII.KoszulAugmentation
import SGA.SGA2.ExposeII.CohomologicalComparison
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-!
# SGA 2, Exposé II, (7.6) and Lemma 9: coefficient exact sequences

The Hom cochain complex is functorial in its coefficient module. Projective
terms of the original chain complex send short exact coefficient sequences
to short exact sequences of cochain complexes, yielding the usual connecting
maps in cohomology. These constructions respect the power transitions,
and exactness of filtered module colimits gives the stable coefficient
long exact sequence. Its actual boundaries and exactness are packaged as
`stableKoszulConnectingSequence` for the dimension-shifting comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

instance linearCoyoneda_preservesZeroMorphisms :
    (linearCoyoneda R (ModuleCat.{u} R)).PreservesZeroMorphisms where
  map_zero := by
    intro X Y
    ext E t
    simp [linearCoyoneda, Linear.leftComp]
    rfl

/-- The Hom cochain complex, contravariantly in the chain complex and
covariantly in its coefficient module. -/
def homCochainBifunctor : (ChainComplex (ModuleCat.{u} R) ℕ)ᵒᵖ ⥤
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  HomologicalComplex.opFunctor _ (ComplexShape.down ℕ) ⋙
    (linearCoyoneda R (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- Hom from a fixed chain complex as a functor of the coefficients. -/
abbrev homCochainCoefficientFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  homCochainBifunctor.obj (op K)

instance homCochainCoefficientFunctor_additive (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (homCochainCoefficientFunctor K).Additive where
  map_add := by
    intro E F f g
    ext i t
    rfl

/-- The coefficient functor gives the same cochain complex used in the
definition of Koszul cohomology. -/
def homCochainCoefficientFunctorObjIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (E : ModuleCat.{u} R) :
    (homCochainCoefficientFunctor K).obj E ≅ K.linearYonedaObj R E := Iso.refl _

/-- Covariant module-valued Hom preserves limits. -/
instance linearCoyonedaObj_preservesLimits (P : ModuleCat.{u} R) :
    PreservesLimits ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) := by
  have : PreservesLimits
      (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙ forget (ModuleCat.{u} R)) :=
    inferInstanceAs (PreservesLimits (coyoneda.obj (op P)))
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Hom from a projective module preserves epimorphisms. -/
instance linearCoyonedaObj_preservesEpimorphisms (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesEpimorphisms := by
  have : (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj P).mp inferInstance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget (ModuleCat.{u} R))

/-- Hom from a projective module preserves exact sequences. -/
instance linearCoyonedaObj_preservesHomology (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Projective terms give degreewise short exact Hom cochain sequences. -/
theorem homCochainCoefficientFunctor_degreewise_shortExact
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    ((S.map (homCochainCoefficientFunctor K)).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) i)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.X i)))

/-- A termwise projective chain complex sends a short exact coefficient
sequence to a short exact sequence of Hom cochain complexes. -/
theorem homCochainCoefficientFunctor_shortExact
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (homCochainCoefficientFunctor K)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    (homCochainCoefficientFunctor_degreewise_shortExact K S hS)

/-- Cohomology of Hom as a bifunctor of the complex and coefficients. -/
def homCohomologyBifunctor (i : ℕ) : (ChainComplex (ModuleCat.{u} R) ℕ)ᵒᵖ ⥤
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  homCochainBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) i)

instance homCohomologyBifunctor_obj_additive (i : ℕ)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((homCohomologyBifunctor i).obj (op K)).Additive :=
  inferInstanceAs ((homCochainCoefficientFunctor K ⋙
    HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) i).Additive)

/-- Finite-stage Koszul cohomology is a functor of the coefficient module. -/
def koszulCohomologyFunctor (fs : List R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (homCohomologyBifunctor i).obj (op (koszulComplex (ModuleCat.of R R) fs))

/-- The connecting map for Hom cohomology of a projective-term complex. -/
def homCohomologyδ (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    ((homCohomologyBifunctor i).obj (op K)).obj S.X₃ ⟶
      ((homCohomologyBifunctor (i + 1)).obj (op K)).obj S.X₁ :=
  (homCochainCoefficientFunctor_shortExact K S hS).δ i (i + 1) rfl

@[reassoc (attr := simp)]
theorem homCohomologyδ_comp (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    homCohomologyδ K S hS i ≫ ((homCohomologyBifunctor (i + 1)).obj (op K)).map S.f = 0 :=
  (homCochainCoefficientFunctor_shortExact K S hS).δ_comp i (i + 1) rfl

@[reassoc (attr := simp)]
theorem comp_homCohomologyδ (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    ((homCohomologyBifunctor i).obj (op K)).map S.g ≫ homCohomologyδ K S hS i = 0 :=
  (homCochainCoefficientFunctor_shortExact K S hS).comp_δ i (i + 1) rfl

/-- Exactness immediately after the connecting map. -/
theorem homCohomology_exact₁ (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (homCohomologyδ_comp K S hS i)).Exact :=
  (homCochainCoefficientFunctor_shortExact K S hS).homology_exact₁ i (i + 1) rfl

/-- Exactness at the middle coefficient module. -/
theorem homCohomology_exact₂ (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (S.map ((homCohomologyBifunctor i).obj (op K))).Exact :=
  (homCochainCoefficientFunctor_shortExact K S hS).homology_exact₂ i

/-- Exactness immediately before the connecting map. -/
theorem homCohomology_exact₃ (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (comp_homCohomologyδ K S hS i)).Exact :=
  (homCochainCoefficientFunctor_shortExact K S hS).homology_exact₃ i (i + 1) rfl

/-- Connecting maps are natural in morphisms of coefficient sequences. -/
theorem homCohomologyδ_naturality_coefficients (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] {S T : ShortComplex (ModuleCat.{u} R)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) (i : ℕ) :
    homCohomologyδ K S hS i ≫ ((homCohomologyBifunctor (i + 1)).obj (op K)).map φ.τ₁ =
      ((homCohomologyBifunctor i).obj (op K)).map φ.τ₃ ≫ homCohomologyδ K T hT i :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((homCochainCoefficientFunctor K).mapShortComplex.map φ)
    (homCochainCoefficientFunctor_shortExact K S hS)
    (homCochainCoefficientFunctor_shortExact K T hT) i (i + 1) rfl

/-- Connecting maps are natural in chain maps, in particular in Koszul
power transitions. -/
theorem homCohomologyδ_naturality_complex
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)] (f : K ⟶ L)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    homCohomologyδ L S hS i ≫ ((homCohomologyBifunctor (i + 1)).map f.op).app S.X₁ =
      ((homCohomologyBifunctor i).map f.op).app S.X₃ ≫ homCohomologyδ K S hS i :=
  HomologicalComplex.HomologySequence.δ_naturality
    (S.mapNatTrans (homCochainBifunctor.map f.op))
    (homCochainCoefficientFunctor_shortExact L S hS)
    (homCochainCoefficientFunctor_shortExact K S hS) i (i + 1) rfl

/-- The genuine finite-stage Koszul connecting homomorphism. -/
def koszulCohomologyδ (fs : List R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) : koszulCohomology fs S.X₃ i ⟶
      koszulCohomology fs S.X₁ (i + 1) :=
  homCohomologyδ (koszulComplex (ModuleCat.of R R) fs) S hS i

/-- A projective-term complex gives a cohomological connecting sequence. -/
def homCohomologyConnectingSequence (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ i, Projective (K.X i)] : ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) where
  obj i := (homCohomologyBifunctor i).obj (op K)
  δ := homCohomologyδ K
  map_δ := comp_homCohomologyδ K
  δ_map := homCohomologyδ_comp K
  exact_left := homCohomology_exact₃ K
  exact_right := homCohomology_exact₁ K

/-- The cohomology diagram of an inverse chain system, as a functor
of the coefficient module. -/
def homCohomologyDiagramFunctor
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ModuleCat.{u} R ⥤ (ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) :=
  (K.op ⋙ homCohomologyBifunctor i).flip

instance homCohomologyDiagramFunctor_additive
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (homCohomologyDiagramFunctor K i).Additive where
  map_add := by
    intro E F f g
    apply NatTrans.ext
    funext j
    exact ((homCohomologyBifunctor i).obj (op (K.obj j.unop))).map_add

/-- Stable Hom cohomology as a coefficient functor. -/
def stableHomCohomologyFunctor
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  homCohomologyDiagramFunctor K i ⋙ colim

instance stableHomCohomologyFunctor_additive
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (stableHomCohomologyFunctor K i).Additive :=
  inferInstanceAs ((homCohomologyDiagramFunctor K i ⋙ colim).Additive)

/-- Stable Koszul cohomology as a coefficient functor. -/
def stableKoszulCohomologyFunctor (fs : List R) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  stableHomCohomologyFunctor (koszulSystem (ModuleCat.of R R) fs) i

/-- This coefficient functor recovers the original stable Koszul cohomology. -/
def stableKoszulCohomologyFunctorObjIso (fs : List R) (i : ℕ) (E : ModuleCat.{u} R) :
    (stableKoszulCohomologyFunctor fs i).obj E ≅ stableKoszulCohomology fs E i :=
  Iso.refl _

section StableConnecting

variable (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ j i, Projective ((K.obj j).X i)]
  (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)

/-- The finite connecting maps form a natural transformation of the
direct cohomology diagrams. -/
def homCohomologyδDiagram :
    (homCohomologyDiagramFunctor K i).obj S.X₃ ⟶
      (homCohomologyDiagramFunctor K (i + 1)).obj S.X₁ where
  app j := homCohomologyδ (K.obj j.unop) S hS i
  naturality _ _ f :=
    (homCohomologyδ_naturality_complex (K.map f.unop) S hS i).symm

@[reassoc (attr := simp)]
theorem homCohomologyδDiagram_comp :
    homCohomologyδDiagram K S hS i ≫ (homCohomologyDiagramFunctor K (i + 1)).map S.f = 0 := by
  apply NatTrans.ext
  funext j
  exact homCohomologyδ_comp (K.obj j.unop) S hS i

@[reassoc (attr := simp)]
theorem comp_homCohomologyδDiagram :
    (homCohomologyDiagramFunctor K i).map S.g ≫ homCohomologyδDiagram K S hS i = 0 := by
  apply NatTrans.ext
  funext j
  exact comp_homCohomologyδ (K.obj j.unop) S hS i

/-- The connecting homomorphism on stable cohomology is the colimit
of the actual finite-stage connecting homomorphisms. -/
def stableHomCohomologyδ :
    (stableHomCohomologyFunctor K i).obj S.X₃ ⟶
      (stableHomCohomologyFunctor K (i + 1)).obj S.X₁ :=
  colim.map (homCohomologyδDiagram K S hS i)

@[reassoc (attr := simp)]
theorem stableHomCohomologyδ_comp :
    stableHomCohomologyδ K S hS i ≫ (stableHomCohomologyFunctor K (i + 1)).map S.f = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, homCohomologyδDiagram_comp, Functor.map_zero]
  rfl

@[reassoc (attr := simp)]
theorem comp_stableHomCohomologyδ :
    (stableHomCohomologyFunctor K i).map S.g ≫ stableHomCohomologyδ K S hS i = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, comp_homCohomologyδDiagram, Functor.map_zero]
  rfl

end StableConnecting

private theorem exact_of_module_diagram_evaluations
    (S : ShortComplex (ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R))
    (hS : ∀ j, (S.map ((evaluation _ _).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext j
  have h := (ShortComplex.exact_iff_isZero_homology _).mp (hS j)
  exact (h.of_iso (S.mapHomologyIso ((evaluation _ _).obj j)).symm).eq_of_src _ _

/-- Exactness of a sequence of countable filtered module diagrams passes
to the sequence of their colimits. -/
theorem exact_colimit_of_module_diagram_evaluations
    (S : ShortComplex (ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R))
    (hS : ∀ j, (S.map ((evaluation _ _).obj j)).Exact) : (S.map colim).Exact := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  exact (exact_of_module_diagram_evaluations S hS).map colim

/-- Filtered colimits preserve exactness immediately after the boundary. -/
theorem stableHomCohomology_exact₁
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j i, Projective ((K.obj j).X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (stableHomCohomologyδ_comp K S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (homCohomologyδDiagram_comp K S hS i))
    (fun j => homCohomology_exact₁ (K.obj j.unop) S hS i)

/-- Filtered colimits preserve exactness at the middle coefficient module. -/
theorem stableHomCohomology_exact₂
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j i, Projective ((K.obj j).X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    (S.map (stableHomCohomologyFunctor K i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (S.map (homCohomologyDiagramFunctor K i))
    (fun j => homCohomology_exact₂ (K.obj j.unop) S hS i)

/-- Filtered colimits preserve exactness immediately before the boundary. -/
theorem stableHomCohomology_exact₃
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j i, Projective ((K.obj j).X i)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (comp_stableHomCohomologyδ K S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (comp_homCohomologyδDiagram K S hS i))
    (fun j => homCohomology_exact₃ (K.obj j.unop) S hS i)

/-- The stable boundaries remain natural in morphisms of short exact
coefficient sequences. -/
theorem stableHomCohomologyδ_naturality_coefficients
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j i, Projective ((K.obj j).X i)]
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (i : ℕ) :
    stableHomCohomologyδ K S hS i ≫ (stableHomCohomologyFunctor K (i + 1)).map φ.τ₁ =
      (stableHomCohomologyFunctor K i).map φ.τ₃ ≫ stableHomCohomologyδ K T hT i := by
  change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg colim.map
  apply NatTrans.ext
  funext j
  exact homCohomologyδ_naturality_coefficients (K.obj j.unop) φ hS hT i

/-- Stable cohomology of a projective-term inverse chain system has
actual connecting maps and exactness suitable for dimension shifting. -/
def stableHomCohomologyConnectingSequence
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j i, Projective ((K.obj j).X i)] :
    ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) where
  obj := stableHomCohomologyFunctor K
  δ := stableHomCohomologyδ K
  map_δ := comp_stableHomCohomologyδ K
  δ_map := stableHomCohomologyδ_comp K
  exact_left := stableHomCohomology_exact₃ K
  exact_right := stableHomCohomology_exact₁ K

/-- The actual stable Koszul cohomology connecting sequence in II.9. -/
def stableKoszulConnectingSequence (fs : List R) :
    ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) := by
  have (j : ℕᵒᵖ) (i : ℕ) : Projective
      (((koszulSystem (ModuleCat.of R R) fs).obj j).X i) :=
    koszulComplex_X_projective _ _ _
  exact stableHomCohomologyConnectingSequence (koszulSystem (ModuleCat.of R R) fs)

end SGA.SGA2.ExposeII
