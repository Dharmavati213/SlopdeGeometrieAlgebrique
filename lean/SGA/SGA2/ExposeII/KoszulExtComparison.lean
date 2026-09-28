/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulAugmentation
import SGA.SGA2.ExposeII.KoszulCohomology
import SGA.SGA2.ExposeII.ProjectiveComplexLift
import SGA.SGA2.ExposeII.KoszulCoefficientSequence

/-!
# SGA 2, Exposé II, (7.6): the Ext-to-Koszul comparison

The augmentation of a projective Koszul complex lifts to a projective
resolution of the quotient by the generators. Applying Hom and taking
cohomology gives the actual comparison from Ext to Koszul cohomology.
Homotopy uniqueness makes the induced cohomology map independent of the lift.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Homotopic chain maps induce the same map on Hom-complex cohomology. -/
theorem homComplexCohomologyMap_eq_of_homotopy
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) (E : ModuleCat.{u} R) (i : ℕ) :
    homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map f.op) i =
      homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map g.op) i :=
  (((linearYoneda R (ModuleCat.{u} R)).obj E).mapHomotopy h.op).homologyMap_eq i

private theorem homologyUnop_inv_naturality
    {A B : ChainComplex (ModuleCat.{u} R)ᵒᵖ ℕ} (f : A ⟶ B) (i : ℕ) :
    (homologyMap f i).unop ≫ (homologyUnop A i).inv =
      (homologyUnop B i).inv ≫
        homologyMap ((unopFunctor _ _).map f.op) i := by
  apply (cancel_epi (homologyUnop B i).hom).mp
  apply (cancel_mono (homologyUnop A i).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact congrArg Quiver.Hom.unop
    (homologyOp_hom_naturality ((unopFunctor _ _).map f.op) i)

/-- The projective-resolution model of Ext is natural in the resolved object. -/
@[reassoc]
theorem projectiveResolution_isoExt_hom_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (g : P.complex ⟶ Q.complex)
    (comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f)
    (E : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).map f.op).app E ≫ (P.isoExt i E).hom =
      (Q.isoExt i E).hom ≫
        homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map g.op) i := by
  let H := ((linearYoneda R (ModuleCat.{u} R)).obj E).rightOp
  have hcomm : g.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f := by
    simpa using HomologicalComplex.congr_hom comm 0
  have h := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q g hcomm H i)
  change ((H.leftDerived i).map f).unop ≫ (P.isoLeftDerivedObj H i).inv.unop =
    (Q.isoLeftDerivedObj H i).inv.unop ≫
      (homologyMap ((H.mapHomologicalComplex _).map g) i).unop at h
  change ((H.leftDerived i).map f).unop ≫
      (P.isoLeftDerivedObj H i).inv.unop ≫
        (homologyUnop ((H.mapHomologicalComplex _).obj P.complex) i).inv =
    ((Q.isoLeftDerivedObj H i).inv.unop ≫
      (homologyUnop ((H.mapHomologicalComplex _).obj Q.complex) i).inv) ≫ _
  rw [← Category.assoc, h]
  simp only [Category.assoc, homologyUnop_inv_naturality]
  rfl

/-- The projective-resolution model of Ext is natural in its coefficient module. -/
@[reassoc]
theorem projectiveResolution_isoExt_coeff_naturality
    {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    {E E' : ModuleCat.{u} R} (f : E ⟶ E') (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).map f ≫ (P.isoExt i E').hom =
      (P.isoExt i E).hom ≫ ((homCohomologyBifunctor i).obj (op P.complex)).map f := by
  let H := ((linearYoneda R (ModuleCat.{u} R)).obj E).rightOp
  let H' := ((linearYoneda R (ModuleCat.{u} R)).obj E').rightOp
  let α : H' ⟶ H := ((linearYoneda R (ModuleCat.{u} R)).map f).rightOp
  have h : (P.isoLeftDerivedObj H' i).inv ≫ (α.leftDerived i).app X =
      homologyMap ((NatTrans.mapHomologicalComplex α _).app P.complex) i ≫
        (P.isoLeftDerivedObj H i).inv := by
    rw [P.leftDerived_app_eq α i]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  have hh := congrArg Quiver.Hom.unop h
  change ((α.leftDerived i).app X).unop ≫ (P.isoLeftDerivedObj H' i).inv.unop =
    (P.isoLeftDerivedObj H i).inv.unop ≫
      (homologyMap ((NatTrans.mapHomologicalComplex α _).app P.complex) i).unop at hh
  change ((α.leftDerived i).app X).unop ≫ (P.isoLeftDerivedObj H' i).inv.unop ≫
      (homologyUnop ((H'.mapHomologicalComplex _).obj P.complex) i).inv =
    ((P.isoLeftDerivedObj H i).inv.unop ≫
      (homologyUnop ((H.mapHomologicalComplex _).obj P.complex) i).inv) ≫ _
  rw [← Category.assoc, hh]
  simp only [Category.assoc, homologyUnop_inv_naturality]
  rfl

variable (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ n, Projective (K.X n)]
variable {X : ModuleCat.{u} R} (a : K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj X)

/-- The Ext comparison induced by an augmented projective complex. -/
def extToHomComplexCohomology (E : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).obj E ⟶
      ((homComplexFunctor (ComplexShape.down ℕ) E).obj (op K)).homology i :=
  ((projectiveResolution X).isoExt i E).hom ≫
    homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map
      (liftToResolution K a (projectiveResolution X)).op) i

/-- Any lift of the augmentation into the chosen resolution gives the same
comparison on cohomology. -/
theorem extToHomComplexCohomology_eq (E : ModuleCat.{u} R) (i : ℕ)
    (g : K ⟶ (projectiveResolution X).complex)
    (comm : g ≫ (projectiveResolution X).π = a) :
    extToHomComplexCohomology K a E i =
      ((projectiveResolution X).isoExt i E).hom ≫
        homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map g.op) i := by
  dsimp only [extToHomComplexCohomology]
  congr 1
  apply homComplexCohomologyMap_eq_of_homotopy
  exact homotopyToResolutionOfAugmentationEq K (projectiveResolution X)
    (liftToResolution K a (projectiveResolution X)) g (by simp [comm])

/-- The comparison from an augmented projective complex commutes with
morphisms of augmented complexes. -/
@[reassoc]
theorem extToHomComplexCohomology_naturality
    (L : ChainComplex (ModuleCat.{u} R) ℕ) [∀ n, Projective (L.X n)]
    {Y : ModuleCat.{u} R} (b : L ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj Y)
    (f : K ⟶ L) (g : X ⟶ Y)
    (comm : a ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map g = f ≫ b)
    (E : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).map g.op).app E ≫ extToHomComplexCohomology K a E i =
      extToHomComplexCohomology L b E i ≫
        homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map f.op) i := by
  let P := projectiveResolution X
  let Q := projectiveResolution Y
  let k := liftToResolution K a P
  let l := liftToResolution L b Q
  let t := ProjectiveResolution.lift g P Q
  have hπ : (k ≫ t) ≫ Q.π = (f ≫ l) ≫ Q.π := by
    simp only [k, l, t, Category.assoc, ProjectiveResolution.lift_commutes,
      liftToResolution_commutes, liftToResolution_commutes_assoc]
    exact comm
  have hh := homComplexCohomologyMap_eq_of_homotopy
    (homotopyToResolutionOfAugmentationEq K Q (k ≫ t) (f ≫ l) hπ) E i
  change ((Ext R (ModuleCat.{u} R) i).map g.op).app E ≫ (P.isoExt i E).hom ≫
      homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map k.op) i =
    ((Q.isoExt i E).hom ≫
      homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map l.op) i) ≫ _
  rw [← Category.assoc, projectiveResolution_isoExt_hom_naturality g P Q t
    (ProjectiveResolution.lift_commutes g P Q) E i]
  simp only [Category.assoc]
  rw [← homologyMap_comp, ← Functor.map_comp, ← op_comp, hh,
    op_comp, Functor.map_comp, homologyMap_comp]

/-- The comparison induced by an augmentation is natural in coefficients. -/
@[reassoc]
theorem extToHomComplexCohomology_coeff_naturality
    {E E' : ModuleCat.{u} R} (f : E ⟶ E') (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).map f ≫ extToHomComplexCohomology K a E' i =
      extToHomComplexCohomology K a E i ≫ ((homCohomologyBifunctor i).obj (op K)).map f := by
  dsimp only [extToHomComplexCohomology]
  rw [← Category.assoc, projectiveResolution_isoExt_coeff_naturality]
  simp only [Category.assoc]
  congr 1
  exact ((homCohomologyBifunctor i).map
    (liftToResolution K a (projectiveResolution X)).op).naturality f

/-- The augmented-projective-complex comparison as a natural transformation
of coefficient functors. -/
def extToHomComplexCohomologyNatTrans (i : ℕ) :
    (Ext R (ModuleCat.{u} R) i).obj (op X) ⟶
      (homCohomologyBifunctor i).obj (op K) where
  app E := extToHomComplexCohomology K a E i
  naturality _ _ f := extToHomComplexCohomology_coeff_naturality K a f i

/-- The actual Ext comparison commutes with coefficient connecting maps,
where the Ext boundary is transported through its projective-resolution model. -/
@[reassoc]
theorem extToHomComplexCohomology_δ
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    ((projectiveResolution X).isoExt i S.X₃).hom ≫
      homCohomologyδ (projectiveResolution X).complex S hS i ≫
        ((projectiveResolution X).isoExt (i + 1) S.X₁).inv ≫
          extToHomComplexCohomology K a S.X₁ (i + 1) =
    extToHomComplexCohomology K a S.X₃ i ≫ homCohomologyδ K S hS i := by
  simp only [extToHomComplexCohomology, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  exact (homCohomologyδ_naturality_complex
    (liftToResolution K a (projectiveResolution X)) S hS i)

/-- II.(7.6), at a finite stage: the augmentation of the actual Koszul
complex induces the canonical map from quotient Ext to Koszul cohomology. -/
def koszulExtComparison (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj
      (op (ModuleCat.of R (R ⧸ koszulIdeal fs)))).obj E ⟶ koszulCohomology fs E i :=
  extToHomComplexCohomology (koszulComplex (ModuleCat.of R R) fs)
    (koszulAugmentation fs) E i

/-- The finite-stage comparison is natural in the coefficient module. -/
def koszulExtComparisonNatTrans (fs : List R) (i : ℕ) :
    (Ext R (ModuleCat.{u} R) i).obj (op (ModuleCat.of R (R ⧸ koszulIdeal fs))) ⟶
      koszulCohomologyFunctor fs i :=
  extToHomComplexCohomologyNatTrans _ (koszulAugmentation fs) i

/-- The finite-stage Ext-to-Koszul comparisons commute with the power transitions. -/
@[reassoc]
theorem koszulExtComparison_naturality (fs : List R) {n m : ℕ} (hnm : n ≤ m)
    (E : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).map (koszulPowerQuotientMap fs hnm).op).app E ≫
      koszulExtComparison (fs.map fun f => f ^ m) E i =
    koszulExtComparison (fs.map fun f => f ^ n) E i ≫
      homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map
        (koszulTransition (ModuleCat.of R R) fs hnm).op) i :=
  extToHomComplexCohomology_naturality _ (koszulAugmentation (fs.map fun f => f ^ m))
    _ (koszulAugmentation (fs.map fun f => f ^ n))
    (koszulTransition (ModuleCat.of R R) fs hnm) (koszulPowerQuotientMap fs hnm)
    (koszulAugmentation_naturality fs hnm).symm E i

/-- The decreasing ideals generated by powers of a finite list. -/
def koszulGeneratorIdeals (fs : List R) : ℕᵒᵖ ⥤ Ideal R where
  obj n := koszulIdeal (fs.map fun f => f ^ n.unop)
  map h := homOfLE (koszulIdeal_pow_antitone fs (leOfHom h.unop))

/-- The quotient inverse system underlying the Ext-to-Koszul comparison. -/
def koszulQuotientSystem (fs : List R) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  localCohomology.ringModIdeals (koszulGeneratorIdeals fs)

@[simp]
theorem koszulQuotientSystem_map (fs : List R) {m n : ℕᵒᵖ} (h : m ⟶ n) :
    (koszulQuotientSystem fs).map h = koszulPowerQuotientMap fs (leOfHom h.unop) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro r
  rfl

/-- The Ext direct system occurring on the left of II.(7.6). -/
def koszulExtDiagram (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R :=
  (koszulQuotientSystem fs).op ⋙ (Ext R (ModuleCat.{u} R) i).flip.obj E

/-- The finite-stage comparisons form a morphism of the actual power diagrams. -/
def koszulExtComparisonDiagram (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    koszulExtDiagram fs E i ⟶ koszulCohomologyDiagram fs E i where
  app n := koszulExtComparison (fs.map fun f => f ^ n.unop.unop) E i
  naturality {n m} h := by
    change ((Ext R (ModuleCat.{u} R) i).map ((koszulQuotientSystem fs).map h.unop).op).app E ≫
      koszulExtComparison (fs.map fun f => f ^ m.unop.unop) E i =
      koszulExtComparison (fs.map fun f => f ^ n.unop.unop) E i ≫ _
    rw [koszulQuotientSystem_map]
    exact koszulExtComparison_naturality fs (leOfHom h.unop.unop) E i

/-- II.(7.6): the actual comparison from the generator-power Ext colimit
to stable Koszul cohomology, obtained from augmented projective complexes. -/
def stableKoszulExtComparison (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    colimit (koszulExtDiagram fs E i) ⟶ stableKoszulCohomology fs E i :=
  colimMap (koszulExtComparisonDiagram fs E i)

@[reassoc (attr := simp)]
theorem stableKoszulExtComparison_ι (fs : List R) (E : ModuleCat.{u} R) (i : ℕ)
    (n : ℕᵒᵖᵒᵖ) :
    colimit.ι (koszulExtDiagram fs E i) n ≫ stableKoszulExtComparison fs E i =
      koszulExtComparison (fs.map fun f => f ^ n.unop.unop) E i ≫
        colimit.ι (koszulCohomologyDiagram fs E i) n :=
  ι_colimMap (koszulExtComparisonDiagram fs E i) n

/-- The generator-power Ext diagram, functorially in its coefficients. -/
def koszulExtCoefficientDiagram (fs : List R) (i : ℕ) :
    ModuleCat.{u} R ⥤ (ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R) :=
  ((koszulQuotientSystem fs).op ⋙ Ext R (ModuleCat.{u} R) i).flip

/-- The generator-power Ext colimit as a coefficient functor. -/
def stableKoszulExtFunctor (fs : List R) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  koszulExtCoefficientDiagram fs i ⋙ colim

/-- The finite comparisons are natural in coefficients and in the power index. -/
def koszulExtComparisonCoefficientDiagram (fs : List R) (i : ℕ) :
    koszulExtCoefficientDiagram fs i ⟶
      homCohomologyDiagramFunctor (koszulSystem (ModuleCat.of R R) fs) i where
  app E := koszulExtComparisonDiagram fs E i
  naturality {E E'} f := by
    apply NatTrans.ext
    funext n
    exact (koszulExtComparisonNatTrans (fs.map fun r => r ^ n.unop.unop) i).naturality f

/-- II.(7.6), naturally in the coefficient module. -/
def stableKoszulExtComparisonNatTrans (fs : List R) (i : ℕ) :
    stableKoszulExtFunctor fs i ⟶ stableKoszulCohomologyFunctor fs i :=
  Functor.whiskerRight (koszulExtComparisonCoefficientDiagram fs i) colim

@[simp]
theorem stableKoszulExtComparisonNatTrans_app (fs : List R) (i : ℕ) (E : ModuleCat.{u} R) :
    (stableKoszulExtComparisonNatTrans fs i).app E = stableKoszulExtComparison fs E i := rfl

end SGA.SGA2.ExposeII
