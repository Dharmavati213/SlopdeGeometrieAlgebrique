/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.ConnectingSequenceExtension
import SGA.SGA2.ExposeII.AffineComparisonZero
import SGA.SGA2.ExposeII.AffineExactness
import SGA.SGA2.ExposeII.InjectiveFlasque
import SGA.SGA2.ExposeII.ExtColimitSequence
import SGA.SGA2.ExposeII.LocalCohomologyReindexing
import SGA.SGA2.ExposeI.SupportedCohomologyComparison
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Algebraic and supported sheaf cohomology on a noetherian affine scheme

The degree-zero torsion comparison extends naturally to every degree using
the genuine coefficient exact sequences. Injective modules are acyclic on
the algebraic side, and their associated sheaves are flasque and hence
acyclic for the actual Ext-defined supported sheaf cohomology.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Abelian

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- Pointwise Ext colimits compute the original ideal-power local cohomology. -/
def affineExtColimitIsoLocalCohomology (I : Ideal R) (n : ℕ) :
    extColimitFunctor (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)) n ≅
      _root_.localCohomology I n :=
  (colimitIsoFlipCompColim (localCohomology.diagram
    (localCohomology.idealPowersDiagram I) n)).symm

/-- Pointwise evaluation of the defining Ext colimit respects the actual
ideal-power coefficient boundary. -/
@[reassoc]
theorem affineExtColimitIsoLocalCohomology_δ (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    extColimitδ (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)) S hS n ≫
      (affineExtColimitIsoLocalCohomology I (n + 1)).hom.app S.X₁ =
    (affineExtColimitIsoLocalCohomology I n).hom.app S.X₃ ≫ localCohomologyδ I S hS n := by
  simp only [affineExtColimitIsoLocalCohomology, Iso.symm_hom,
    colimitIsoFlipCompColim_inv_app, localCohomologyδ, idealExtColimitδ,
    Iso.inv_hom_id_assoc]
  rfl

/-- The algebraic coefficient sequence, forgetting only the scalar action. -/
def affineAlgebraicConnectingSequence (I : Ideal R) :
    ConnectingSequence (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  ConnectingSequence.postcompose
    (extColimitConnectingSequence
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)))
    (forget₂ (ModuleCat R) AddCommGrpCat)

theorem affineAlgebraicConnectingSequence_boundaryNatural (I : Ideal R) :
    (affineAlgebraicConnectingSequence I).BoundaryNatural :=
  ConnectingSequence.postcompose_boundaryNatural
    (extColimitConnectingSequence
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)))
    (forget₂ (ModuleCat R) AddCommGrpCat)
    (extColimitδ_naturality_coefficients
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)))

theorem affineAlgebraicConnectingSequence_vanishesOnInjectives (I : Ideal R) :
    (affineAlgebraicConnectingSequence I).VanishesOnInjectives :=
  ConnectingSequence.postcompose_vanishesOnInjectives
    (extColimitConnectingSequence
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)))
    (forget₂ (ModuleCat R) AddCommGrpCat)
    (extColimitConnectingSequence_vanishesOnInjectives
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)))

/-- The geometric coefficient sequence uses actual Ext-based supported
cohomology of the actual associated abelian sheaf. -/
def affineGeometricConnectingSequence (I : Ideal R) :
    ConnectingSequence (ModuleCat.{u} R) AddCommGrpCat.{u} :=
  ConnectingSequence.precompose
    (ConnectingSequence.extSequence (ExposeI.zZX_closed (affineSupportClosed I)))
    affineTildeAbFunctor affineTildeAb_shortExact

theorem affineGeometricConnectingSequence_boundaryNatural (I : Ideal R) :
    (affineGeometricConnectingSequence I).BoundaryNatural :=
  ConnectingSequence.precompose_boundaryNatural _ _ _
    (ConnectingSequence.extSequence_boundaryNatural _)

theorem affineGeometricConnectingSequence_vanishesOnInjectives [IsNoetherianRing R]
    (I : Ideal R) : (affineGeometricConnectingSequence I).VanishesOnInjectives := by
  intro E hE n
  have : TopCat.Sheaf.IsFlasque (affineTildeAbSheaf E) :=
    affineTildeAbSheaf_isFlasque_of_injective E
  exact ExposeI.H_Z_pos_isZero_of_isFlasque (affineSupportClosed I) (affineTildeAbSheaf E) n

/-- The torsion comparison in degree zero, as an isomorphism of the actual
abelian-group-valued coefficient functors. -/
def affinePowerTorsionIsoGammaZFunctor (I : Ideal R) (hI : I.FG) :
    powerTorsionFunctor I ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      affineTildeAbFunctor ⋙ ExposeI.gammaZSectionsFunctor (affineSupportClosed I) ⊤ :=
  NatIso.ofComponents (fun M ↦ (powerTorsionEquivGammaZ M I hI).toAddCommGrpIso) (by
    intro M N f
    ext x
    change powerTorsion I M at x
    apply Subtype.ext
    change (tilde.isoTop N).hom (f x) =
      (modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) ((tilde.isoTop M).hom x)
    exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x).symm)

/-- The starting isomorphism uses existing supported cohomology in degree zero. -/
def affineCohomologyComparisonZero (I : Ideal R) (hI : I.FG) :
    (affineAlgebraicConnectingSequence I).obj 0 ≅
      (affineGeometricConnectingSequence I).obj 0 :=
  Functor.isoWhiskerRight
    (affineExtColimitIsoLocalCohomology I 0 ≪≫ localCohomologyZeroIsoPowerTorsionFunctor I)
    (forget₂ (ModuleCat R) AddCommGrpCat) ≪≫
  affinePowerTorsionIsoGammaZFunctor I hI ≪≫
  Functor.isoWhiskerLeft affineTildeAbFunctor
    ((ExposeI.derivedGammaZSectionsZeroIso (affineSupportClosed I) ⊤).symm ≪≫
      ExposeI.derivedGammaZSectionsIsoH_Z (affineSupportClosed I) 0)

/-- The constructed comparison on the pointwise Ext-colimit model. -/
def affineExtColimitComparisonNatIso [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    (affineAlgebraicConnectingSequence I).obj n ≅
      (affineGeometricConnectingSequence I).obj n :=
  ConnectingSequence.extendNatIso
    (affineAlgebraicConnectingSequence I) (affineGeometricConnectingSequence I)
    (affineAlgebraicConnectingSequence_vanishesOnInjectives I)
    (affineGeometricConnectingSequence_vanishesOnInjectives I)
    (affineAlgebraicConnectingSequence_boundaryNatural I)
    (affineGeometricConnectingSequence_boundaryNatural I)
    (affineCohomologyComparisonZero I (IsNoetherian.noetherian I)) n

/-- The comparison commutes with boundaries for every short exact coefficient
sequence, not only for the chosen injective presentations. -/
@[reassoc]
theorem affineExtColimitComparisonNatIso_δ [IsNoetherianRing R] (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    (affineAlgebraicConnectingSequence I).δ S hS n ≫
      (affineExtColimitComparisonNatIso I (n + 1)).hom.app S.X₁ =
    (affineExtColimitComparisonNatIso I n).hom.app S.X₃ ≫
      (affineGeometricConnectingSequence I).δ S hS n :=
  ConnectingSequence.extendNatIso_comm
    (affineAlgebraicConnectingSequence I) (affineGeometricConnectingSequence I)
    (affineAlgebraicConnectingSequence_vanishesOnInjectives I)
    (affineGeometricConnectingSequence_vanishesOnInjectives I)
    (affineAlgebraicConnectingSequence_boundaryNatural I)
    (affineGeometricConnectingSequence_boundaryNatural I)
    (affineCohomologyComparisonZero I (IsNoetherian.noetherian I)) S hS n

/-- **SGA 2, II.(7.3):** on a noetherian affine scheme, algebraic local
cohomology agrees naturally in every degree with actual supported sheaf
cohomology of the associated sheaf. -/
def affineLocalCohomologyNatIso [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    _root_.localCohomology I n ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      affineTildeAbFunctor ⋙ extFunctorObj (ExposeI.zZX_closed (affineSupportClosed I)) n :=
  (Functor.isoWhiskerRight (affineExtColimitIsoLocalCohomology I n)
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm ≪≫
    affineExtColimitComparisonNatIso I n

private theorem boundaryNatIso_inv
    {C D : Type*} [Category C] [Category D] {X Y : C}
    {A₀ A₁ B₀ B₁ : C ⥤ D} {e₀ : A₀ ≅ B₀} {e₁ : A₁ ≅ B₁}
    {dA : A₀.obj X ⟶ A₁.obj Y} {dB : B₀.obj X ⟶ B₁.obj Y}
    (h : dA ≫ e₁.hom.app Y = e₀.hom.app X ≫ dB) :
    dB ≫ e₁.inv.app Y = e₀.inv.app X ≫ dA := by
  rw [← cancel_epi (e₀.hom.app X), ← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    Iso.hom_inv_id_app_assoc]

private theorem boundaryNatIso_comp
    {C D : Type*} [Category C] [Category D] {X Y : C}
    {A₀ A₁ B₀ B₁ C₀ C₁ : C ⥤ D}
    {e₀ : A₀ ≅ B₀} {e₁ : A₁ ≅ B₁} {f₀ : B₀ ≅ C₀} {f₁ : B₁ ≅ C₁}
    {dA : A₀.obj X ⟶ A₁.obj Y} {dB : B₀.obj X ⟶ B₁.obj Y}
    {dC : C₀.obj X ⟶ C₁.obj Y}
    (he : dA ≫ e₁.hom.app Y = e₀.hom.app X ≫ dB)
    (hf : dB ≫ f₁.hom.app Y = f₀.hom.app X ≫ dC) :
    dA ≫ (e₁ ≪≫ f₁).hom.app Y = (e₀ ≪≫ f₀).hom.app X ≫ dC := by
  change dA ≫ (e₁.hom.app Y ≫ f₁.hom.app Y) =
    (e₀.hom.app X ≫ f₀.hom.app X) ≫ dC
  rw [← Category.assoc, he, Category.assoc, hf, ← Category.assoc]

/-- The all-degree affine comparison respects the actual ideal-power
local-cohomology boundary and the actual supported Ext boundary. -/
@[reassoc]
theorem affineLocalCohomologyNatIso_δ [IsNoetherianRing R] (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (localCohomologyδ I S hS n) ≫
      (affineLocalCohomologyNatIso I (n + 1)).hom.app S.X₁ =
    (affineLocalCohomologyNatIso I n).hom.app S.X₃ ≫
      AddCommGrpCat.ofHom ((affineTildeAb_shortExact hS).extClass.postcomp
        (ExposeI.zZX_closed (affineSupportClosed I)) rfl) := by
  have h : (affineAlgebraicConnectingSequence I).δ S hS n ≫
      (Functor.isoWhiskerRight (affineExtColimitIsoLocalCohomology I (n + 1))
        (forget₂ (ModuleCat R) AddCommGrpCat)).hom.app S.X₁ =
      (Functor.isoWhiskerRight (affineExtColimitIsoLocalCohomology I n)
        (forget₂ (ModuleCat R) AddCommGrpCat)).hom.app S.X₃ ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map (localCohomologyδ I S hS n) :=
    ((forget₂ (ModuleCat R) AddCommGrpCat).map_comp _ _).symm.trans
      ((congrArg (forget₂ (ModuleCat R) AddCommGrpCat).map
        (affineExtColimitIsoLocalCohomology_δ I S hS n)).trans
        ((forget₂ (ModuleCat R) AddCommGrpCat).map_comp _ _))
  exact boundaryNatIso_comp
    (e₀ := (Functor.isoWhiskerRight (affineExtColimitIsoLocalCohomology I n)
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm)
    (e₁ := (Functor.isoWhiskerRight (affineExtColimitIsoLocalCohomology I (n + 1))
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm)
    (boundaryNatIso_inv h)
    (affineExtColimitComparisonNatIso_δ I S hS n)

/-- The affine comparison with the precise Exposé I supported cohomology group. -/
def affineLocalCohomologyIso [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((_root_.localCohomology I n).obj M) ≅
      AddCommGrpCat.of (ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n) :=
  (affineLocalCohomologyNatIso I n).app M

/-- Naturality against the existing module maps and existing supported
cohomology maps, with no transported replacement for either one. -/
theorem affineLocalCohomologyIso_naturality [IsNoetherianRing R]
    (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map ((_root_.localCohomology I n).map f) ≫
      (affineLocalCohomologyIso I N n).hom =
    (affineLocalCohomologyIso I M n).hom ≫
      AddCommGrpCat.ofHom (ExposeI.H_Z_map (affineSupportClosed I)
        (affineTildeAbFunctor.map f) n) :=
  (affineLocalCohomologyNatIso I n).hom.naturality f

/-- The actual cohomology groups are additively equivalent. -/
def affineLocalCohomologyAddEquiv [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    ((_root_.localCohomology I n).obj M) ≃+
      ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n :=
  (affineLocalCohomologyIso I M n).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeII
