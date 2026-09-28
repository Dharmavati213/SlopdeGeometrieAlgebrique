/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulCohomologyZero
import SGA.SGA2.ExposeII.AffineSupport
import SGA.SGA2.ExposeII.LocalizationCokernelColimit

/-!
# SGA 2, Exposé II: the principal Koszul and Čech comparison

The singleton Koszul Hom complex has first cohomology `M / f M` and no
cohomology above degree one. Its power transitions act by multiplication
by the missing power of `f` on these quotient modules. Their direct limit
is the cokernel of `M → M_f`, hence also the cokernel of restriction from
the actual associated sheaf's global sections to `D(f)`. These results
hold over every commutative ring.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite HomologicalComplex AlgebraicGeometry

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A finite Koszul Hom complex has no terms above the length of the list. -/
theorem koszulHomComplex_isZero_X (fs : List R) (M : ModuleCat.{u} R)
    (i : ℕ) (hi : fs.length < i) :
    IsZero (((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R M).X i) := by
  have h := koszulComplex_isZero_X (ModuleCat.of R R) fs i hi
  have : Subsingleton ((koszulComplex (ModuleCat.of R R) fs).X i ⟶ M) :=
    ⟨fun a b ↦ h.eq_of_src a b⟩
  change IsZero (ModuleCat.of R ((koszulComplex (ModuleCat.of R R) fs).X i ⟶ M))
  exact ModuleCat.isZero_of_subsingleton _

/-- Finite Koszul cohomology vanishes above the length of its generator list. -/
theorem koszulCohomology_isZero_above_length (fs : List R) (M : ModuleCat.{u} R)
    (i : ℕ) (hi : fs.length < i) : IsZero (koszulCohomology fs M i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (koszulHomComplex_isZero_X fs M i hi)

/-- Stable Koszul cohomology also vanishes above the number of generators. -/
theorem stableKoszulCohomology_isZero_above_length (fs : List R) (M : ModuleCat.{u} R)
    (i : ℕ) (hi : fs.length < i) : IsZero (stableKoszulCohomology fs M i) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  exact (koszulCohomology_isZero_above_length
    (fs.map (fun f ↦ f ^ n.unop.unop)) M i (by simpa using hi)).eq_of_src _ _

/-- Degree one of the singleton Koszul chain complex is the coefficient module. -/
def koszulSingletonOneIso (M : ModuleCat.{u} R) (f : R) :
    (koszulComplex M [f]).X 1 ≅ M where
  hom := homotopyCofiber.fstX (f • 𝟙 (koszulComplex M [])) 1 0 (by simp) ≫
    (koszulZeroIso M []).hom
  inv := (koszulZeroIso M []).inv ≫
    homotopyCofiber.inlX (f • 𝟙 (koszulComplex M [])) 0 1 (by simp)
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply homotopyCofiber.ext_to_X (f • 𝟙 (koszulComplex M [])) 1 0 (by simp)
    · simp
    · exact (koszulComplex_isZero_X M [] 1 (by simp)).eq_of_tgt _ _
  inv_hom_id := by simp

/-- With the canonical identifications in degrees zero and one, the sole
singleton Koszul differential is multiplication by its generator. -/
theorem koszulSingleton_d_one_zero (M : ModuleCat.{u} R) (f : R) :
    (koszulComplex M [f]).d 1 0 ≫ (koszulZeroIso M [f]).hom =
      (koszulSingletonOneIso M f).hom ≫ (f • 𝟙 M) := by
  have hs : (homotopyCofiber.XIso (f • 𝟙 (koszulComplex M [])) 0 (by simp)).hom =
      homotopyCofiber.sndX (f • 𝟙 (koszulComplex M [])) 0 := by
    symm
    exact dite_eq_right (by simp)
  change (homotopyCofiber (f • 𝟙 (koszulComplex M []))).d 1 0 ≫
      (homotopyCofiber.XIso (f • 𝟙 (koszulComplex M [])) 0 (by simp)).hom ≫
        (koszulZeroIso M []).hom =
    (homotopyCofiber.fstX (f • 𝟙 (koszulComplex M [])) 1 0 (by simp) ≫
      (koszulZeroIso M []).hom) ≫ (f • 𝟙 M)
  rw [hs, ← Category.assoc, homotopyCofiber_d,
    homotopyCofiber.d_sndX (f • 𝟙 (koszulComplex M [])) 1 0 (by simp)]
  simp [koszulComplex, Linear.comp_smul, Linear.smul_comp]

/-- Evaluation at `1`, after identifying a free rank-one source with the ring. -/
def homFromRingIso (M : ModuleCat.{u} R) : ModuleCat.of R (ModuleCat.of R R ⟶ M) ≅ M :=
  (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R M)).toModuleIso

/-- The degree-zero singleton Koszul Hom term is the coefficient module. -/
def koszulSingletonHomZeroIso (f : R) (M : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).X 0 ≅ M :=
  ((linearYoneda R (ModuleCat.{u} R)).obj M).mapIso
    (koszulZeroIso (ModuleCat.of R R) [f]).op.symm ≪≫ homFromRingIso M

/-- The degree-one singleton Koszul Hom term is the coefficient module. -/
def koszulSingletonHomOneIso (f : R) (M : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).X 1 ≅ M :=
  ((linearYoneda R (ModuleCat.{u} R)).obj M).mapIso
    (koszulSingletonOneIso (ModuleCat.of R R) f).op.symm ≪≫ homFromRingIso M

private theorem koszulSingleton_inv_d (M : ModuleCat.{u} R) (f : R) :
    (koszulSingletonOneIso M f).inv ≫ (koszulComplex M [f]).d 1 0 =
      f • (koszulZeroIso M [f]).inv := by
  apply (cancel_mono (koszulZeroIso M [f]).hom).mp
  rw [Category.assoc, koszulSingleton_d_one_zero]
  simp [Linear.smul_comp]

/-- The differential in the singleton Hom complex is multiplication by `f`. -/
theorem koszulSingletonHom_d_zero_one (f : R) (M : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).d 0 1 ≫
      (koszulSingletonHomOneIso f M).hom =
    (koszulSingletonHomZeroIso f M).hom ≫ (f • 𝟙 M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (koszulComplex (ModuleCat.of R R) [f]).X 0 ⟶ M at h
  change h ((koszulComplex (ModuleCat.of R R) [f]).d 1 0
      ((koszulSingletonOneIso (ModuleCat.of R R) f).inv 1)) =
    f • h ((koszulZeroIso (ModuleCat.of R R) [f]).inv 1)
  have he := ConcreteCategory.congr_hom (koszulSingleton_inv_d (ModuleCat.of R R) f) 1
  change (koszulComplex (ModuleCat.of R R) [f]).d 1 0
      ((koszulSingletonOneIso (ModuleCat.of R R) f).inv 1) =
    f • ((koszulZeroIso (ModuleCat.of R R) [f]).inv 1) at he
  rw [he]
  exact h.hom.map_smul f _

private theorem koszulSingletonHom_boundary_range (f : R) (M : ModuleCat.{u} R) :
    LinearMap.range ((((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).d 0 1 ≫
      (koszulSingletonHomOneIso f M).hom).hom) =
      LinearMap.range (f • (LinearMap.id : M →ₗ[R] M)) := by
  rw [koszulSingletonHom_d_zero_one]
  exact LinearMap.range_comp_of_range_eq_top _
    (koszulSingletonHomZeroIso f M).toLinearEquiv.range

/-- The degree-one quotient of the singleton Hom complex is `M / fM`. -/
def koszulSingletonHomOpcyclesOneEquiv (f : R) (M : ModuleCat.{u} R) :
    (((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).X 1 ⧸
      LinearMap.range
        (((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).d 0 1).hom) ≃ₗ[R]
        M ⧸ LinearMap.range (f • (LinearMap.id : M →ₗ[R] M)) :=
  Submodule.Quotient.equiv _ _ (koszulSingletonHomOneIso f M).toLinearEquiv (by
    rw [CategoryTheory.Iso.toLinearMap_toLinearEquiv, ← LinearMap.range_comp]
    exact koszulSingletonHom_boundary_range f M)

/-- First cohomology of the actual singleton Koszul Hom complex is `M / fM`. -/
def koszulCohomologySingletonOneIso (f : R) (M : ModuleCat.{u} R) :
    koszulCohomology [f] M 1 ≅
      ModuleCat.of R (M ⧸ LinearMap.range (f • (LinearMap.id : M →ₗ[R] M))) :=
  ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).homologyIsoSc'
      0 1 2 (by simp) (by simp) ≪≫
    (((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).sc' 0 1 2).asIsoHomologyι
      ((koszulHomComplex_isZero_X [f] M 2 (by simp)).eq_of_tgt _ _) ≪≫
    (((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).sc' 0 1 2).moduleCatOpcyclesIso ≪≫
    (koszulSingletonHomOpcyclesOneEquiv f M).toModuleIso

/-- The singleton chain transition is multiplication by the missing power
in degree one, under its canonical identification with the coefficient module. -/
@[reassoc]
theorem koszulTransition_singleton_one_naturality (M : ModuleCat.{u} R) (f : R)
    {n m : ℕ} (hnm : n ≤ m) :
    (koszulTransition M [f] hnm).f 1 ≫ (koszulSingletonOneIso M (f ^ n)).hom =
      (koszulSingletonOneIso M (f ^ m)).hom ≫ (f ^ (m - n) • 𝟙 M) := by
  change (homotopyCofiber.mapArrowHom (f ^ m • 𝟙 (koszulComplex M []))
      (f ^ n • 𝟙 (koszulComplex M [])) chainShape_hasPredecessor
      (scalarPowerArrow f hnm (𝟙 (koszulComplex M [])))).f 1 ≫
        (homotopyCofiber.fstX (f ^ n • 𝟙 (koszulComplex M [])) 1 0 (by simp) ≫
          (koszulZeroIso M []).hom) =
    (homotopyCofiber.fstX (f ^ m • 𝟙 (koszulComplex M [])) 1 0 (by simp) ≫
      (koszulZeroIso M []).hom) ≫ (f ^ (m - n) • 𝟙 M)
  rw [← Category.assoc, homotopyCofiber_mapArrowHom_fstX _ _ _ 0]
  simp [scalarPowerArrow, Linear.smul_comp, Linear.comp_smul]

private theorem koszulTransition_singleton_inv_one (M : ModuleCat.{u} R) (f : R)
    {n m : ℕ} (hnm : n ≤ m) :
    (koszulSingletonOneIso M (f ^ m)).inv ≫ (koszulTransition M [f] hnm).f 1 =
      f ^ (m - n) • (koszulSingletonOneIso M (f ^ n)).inv := by
  apply (cancel_mono (koszulSingletonOneIso M (f ^ n)).hom).mp
  rw [Category.assoc, koszulTransition_singleton_one_naturality]
  simp [Linear.smul_comp]

/-- The direct transition on degree-one Hom terms multiplies by the missing power. -/
@[reassoc]
theorem koszulSingletonHom_one_naturality (f : R) (M : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) :
    (((homComplexFunctor (ComplexShape.down ℕ) M).map
      (koszulTransition (ModuleCat.of R R) [f] hnm).op).f 1) ≫
        (koszulSingletonHomOneIso (f ^ m) M).hom =
      (koszulSingletonHomOneIso (f ^ n) M).hom ≫ (f ^ (m - n) • 𝟙 M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (koszulComplex (ModuleCat.of R R) [f ^ n]).X 1 ⟶ M at h
  change h ((koszulTransition (ModuleCat.of R R) [f] hnm).f 1
      ((koszulSingletonOneIso (ModuleCat.of R R) (f ^ m)).inv 1)) =
    f ^ (m - n) • h ((koszulSingletonOneIso (ModuleCat.of R R) (f ^ n)).inv 1)
  have he := ConcreteCategory.congr_hom
    (koszulTransition_singleton_inv_one (ModuleCat.of R R) f hnm) 1
  change (koszulTransition (ModuleCat.of R R) [f] hnm).f 1
      ((koszulSingletonOneIso (ModuleCat.of R R) (f ^ m)).inv 1) =
    f ^ (m - n) • ((koszulSingletonOneIso (ModuleCat.of R R) (f ^ n)).inv 1) at he
  rw [he]
  exact h.hom.map_smul _ _

/-- The degree-one cohomology comparison sends a cycle to the residue class
of its evaluation at `1`. -/
@[reassoc (attr := simp)]
theorem koszulCohomologySingletonOneIso_homologyπ (f : R) (M : ModuleCat.{u} R) :
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).homologyπ 1 ≫
      (koszulCohomologySingletonOneIso f M).hom =
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).iCycles 1 ≫
      (koszulSingletonHomOneIso f M).hom ≫
        ModuleCat.ofHom (LinearMap.range (f • (LinearMap.id : M →ₗ[R] M))).mkQ := by
  have he : ModuleCat.ofHom (LinearMap.range
      (((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).d 0 1).hom).mkQ ≫
      (koszulSingletonHomOpcyclesOneEquiv f M).toModuleIso.hom =
    (koszulSingletonHomOneIso f M).hom ≫
      ModuleCat.ofHom (LinearMap.range (f • (LinearMap.id : M →ₗ[R] M))).mkQ := by
    ext x
    rfl
  dsimp only [koszulCohomologySingletonOneIso, Iso.trans_hom]
  simp only [HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.asIsoHomologyι_hom, ShortComplex.homology_π_ι_assoc,
    ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_assoc]
  rw [HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]
  exact congrArg (fun t ↦
    ((koszulComplex (ModuleCat.of R R) [f]).linearYonedaObj R M).iCycles 1 ≫ t) he

/-- Multiplication by the missing power induces the principal direct quotient transition. -/
theorem principalScalarRange_le_comap (M : ModuleCat.{u} R) (f : R)
    {n m : ℕ} (hnm : n ≤ m) :
    LinearMap.range (f ^ n • (LinearMap.id : M →ₗ[R] M)) ≤
      (LinearMap.range (f ^ m • (LinearMap.id : M →ₗ[R] M))).comap
        (f ^ (m - n) • (LinearMap.id : M →ₗ[R] M)) := by
  rintro x ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  change f ^ m • y = f ^ (m - n) • (f ^ n • y)
  rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hnm]

/-- The first-cohomology quotient identification commutes with the actual
power transition of the singleton Koszul system. -/
theorem koszulCohomologySingletonOneIso_naturality (f : R) (M : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) :
    HomologicalComplex.homologyMap ((homComplexFunctor (ComplexShape.down ℕ) M).map
      (koszulTransition (ModuleCat.of R R) [f] hnm).op) 1 ≫
        (koszulCohomologySingletonOneIso (f ^ m) M).hom =
      (koszulCohomologySingletonOneIso (f ^ n) M).hom ≫
        ModuleCat.ofHom ((LinearMap.range (f ^ n • (LinearMap.id : M →ₗ[R] M))).mapQ
          (LinearMap.range (f ^ m • (LinearMap.id : M →ₗ[R] M)))
          (f ^ (m - n) • (LinearMap.id : M →ₗ[R] M))
          (principalScalarRange_le_comap M f hnm)) := by
  apply (cancel_epi
    (((koszulComplex (ModuleCat.of R R) [f ^ n]).linearYonedaObj R M).homologyπ 1)).mp
  simp only [HomologicalComplex.homologyπ_naturality_assoc]
  change HomologicalComplex.cyclesMap
    ((homComplexFunctor (ComplexShape.down ℕ) M).map
      (koszulTransition (ModuleCat.of R R) [f] hnm).op) 1 ≫
      ((koszulComplex (ModuleCat.of R R) [f ^ m]).linearYonedaObj R M).homologyπ 1 ≫
        (koszulCohomologySingletonOneIso (f ^ m) M).hom = _
  simp only [koszulCohomologySingletonOneIso_homologyπ,
    koszulCohomologySingletonOneIso_homologyπ_assoc]
  have hc : HomologicalComplex.cyclesMap
      ((homComplexFunctor (ComplexShape.down ℕ) M).map
        (koszulTransition (ModuleCat.of R R) [f] hnm).op) 1 ≫
        ((koszulComplex (ModuleCat.of R R) [f ^ m]).linearYonedaObj R M).iCycles 1 =
      ((koszulComplex (ModuleCat.of R R) [f ^ n]).linearYonedaObj R M).iCycles 1 ≫
        ((homComplexFunctor (ComplexShape.down ℕ) M).map
          (koszulTransition (ModuleCat.of R R) [f] hnm).op).f 1 :=
    HomologicalComplex.cyclesMap_i _ _
  rw [reassoc_of% hc, koszulSingletonHom_one_naturality_assoc]
  rfl

/-- The singleton first-cohomology diagram is the quotient diagram `M/fⁿM`
with its scalar transition maps. -/
def koszulCohomologySingletonOneDiagramIso (f : R) (M : ModuleCat.{u} R) :
    koszulCohomologyDiagram [f] M 1 ≅
      (opOpEquivalence ℕ).functor ⋙ principalLocalizationQuotientDiagram M f :=
  NatIso.ofComponents (fun n ↦ koszulCohomologySingletonOneIso (f ^ n.unop.unop) M)
    (fun h ↦ koszulCohomologySingletonOneIso_naturality f M (leOfHom h.unop.unop))

/-- II.(4.2) and II.(5.1), principal case: stable first Koszul cohomology
is the categorical cokernel of the actual module localization map. -/
def stableKoszulSingletonOneIsoLocalizationCokernel (f : R) (M : ModuleCat.{u} R) :
    stableKoszulCohomology [f] M 1 ≅
      cokernel (ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) :=
  HasColimit.isoOfEquivalence (opOpEquivalence ℕ)
    (koszulCohomologySingletonOneDiagramIso f M).symm ≪≫
      principalLocalizationCokernelColimitIso M f

/-- Stable singleton Koszul cohomology has no terms above degree one,
over an arbitrary commutative ring and for arbitrary coefficients. -/
theorem stableKoszulSingleton_isZero_above_one (f : R) (M : ModuleCat.{u} R)
    (i : ℕ) (hi : 1 < i) : IsZero (stableKoszulCohomology [f] M i) :=
  stableKoszulCohomology_isZero_above_length [f] M i (by simpa using hi)

/-- II.(4.2) and II.(5.1), principal geometric comparison in degree one:
stable Koszul cohomology is the cokernel of restriction from global
associated-sheaf sections to the actual principal open. -/
def stableKoszulSingletonOneIsoRestrictionCokernel {A : CommRingCat.{u}}
    (f : A) (M : ModuleCat.{u} A) :
    stableKoszulCohomology [f] M 1 ≅
      cokernel ((affineTildeSheaf M).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op) :=
  stableKoszulSingletonOneIsoLocalizationCokernel f M ≪≫
    cokernel.mapIso (ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers f) M))
      ((affineTildeSheaf M).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op)
      (tilde.isoTop M)
      (IsLocalizedModule.iso (Submonoid.powers f)
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom).toModuleIso (by
          change ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers f) M) ≫
              (IsLocalizedModule.iso (Submonoid.powers f)
                (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom).toModuleIso.hom =
            tilde.toOpen M ⊤ ≫ (affineTildeSheaf M).presheaf.map
              (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
          rw [tilde.toOpen_res]
          ext x
          exact IsLocalizedModule.iso_mk_one (Submonoid.powers f)
            (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom x)

end SGA.SGA2.ExposeII
