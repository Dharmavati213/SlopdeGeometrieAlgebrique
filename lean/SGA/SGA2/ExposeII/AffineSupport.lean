/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.LocalizationKernel
import SGA.SGA2.ExposeII.InjectiveLocalization
import SGA.SGA2.ExposeI.GammaZ
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# SGA 2, Exposé II, (4.2) and (7.5): supported sections on an affine scheme

The sections of the actual associated sheaf on `D(f)` form a localization
of the coefficient module. A section coming from an element of the module
vanishes there exactly when a power of `f` annihilates that element. Sheaf
separation over a union of principal opens identifies the kernel of restriction
to the complement of a finitely generated closed support with ideal-power
torsion.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The associated sheaf, regarded as a sheaf of modules over the original ring. -/
abbrev affineTildeSheaf : TopCat.Sheaf (ModuleCat R) (Spec R) :=
  modulesSpecToSheaf.obj (tilde M)

/-- Vanishing of the associated section on a principal open is exactly
annihilation by some power of its defining element. -/
theorem tilde_toOpen_basicOpen_eq_zero_iff (f : R) (x : M) :
    tilde.toOpen M (PrimeSpectrum.basicOpen f) x = 0 ↔ ∃ n : ℕ, f ^ n • x = 0 := by
  rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom]
  constructor
  · rintro ⟨⟨a, n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩

/-- The open complement of the closed subset defined by an ideal. -/
def affineSupportComplement (I : Ideal R) : (Spec R).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The complement of a generated closed subset is the union of the
principal opens of its generators. -/
theorem affineSupportComplement_span {ι : Type v} (f : ι → R) :
    affineSupportComplement (Ideal.span (Set.range f)) = ⨆ a, PrimeSpectrum.basicOpen (f a) := by
  change (⟨(PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R))ᶜ, _⟩ :
    Opens (PrimeSpectrum R)) = ⨆ a, PrimeSpectrum.basicOpen (f a)
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff]

/-- Sheaf separation detects vanishing on a union of principal opens. -/
theorem tilde_toOpen_iSup_eq_zero_iff {ι : Type v} (f : ι → R) (x : M) :
    tilde.toOpen M (⨆ a, PrimeSpectrum.basicOpen (f a)) x = 0 ↔
      ∀ a, tilde.toOpen M (PrimeSpectrum.basicOpen (f a)) x = 0 := by
  constructor
  · intro hx a
    have hres := ConcreteCategory.congr_hom (tilde.toOpen_res M
      (⨆ a, PrimeSpectrum.basicOpen (f a)) (PrimeSpectrum.basicOpen (f a))
      (homOfLE (le_iSup (fun a ↦ PrimeSpectrum.basicOpen (f a)) a))) x
    rw [← hres]
    change (affineTildeSheaf M).presheaf.map _ (tilde.toOpen M _ x) = 0
    rw [hx, map_zero]
  · intro hx
    apply (affineTildeSheaf M).eq_of_locally_eq (fun a ↦ PrimeSpectrum.basicOpen (f a))
    intro a
    have hres := ConcreteCategory.congr_hom (tilde.toOpen_res M
      (⨆ a, PrimeSpectrum.basicOpen (f a)) (PrimeSpectrum.basicOpen (f a))
      (homOfLE (le_iSup (fun a ↦ PrimeSpectrum.basicOpen (f a)) a))) x
    exact hres.trans ((hx a).trans (map_zero
      ((affineTildeSheaf M).presheaf.map
        (homOfLE (le_iSup (fun a ↦ PrimeSpectrum.basicOpen (f a)) a)).op).hom).symm)

/-- II.(7.5), the geometric degree-zero comparison for a finite generating family. -/
theorem tilde_toOpen_complement_span_eq_zero_iff {ι : Type v} [Finite ι]
    (f : ι → R) (x : M) :
    tilde.toOpen M (affineSupportComplement (Ideal.span (Set.range f))) x = 0 ↔
      x ∈ powerTorsion (Ideal.span (Set.range f)) M := by
  rw [affineSupportComplement_span, tilde_toOpen_iSup_eq_zero_iff,
    mem_powerTorsion_span_iff_forall]
  simp only [tilde_toOpen_basicOpen_eq_zero_iff]

/-- II.(4.2), the actual associated-sheaf restriction has ideal-power torsion
as its kernel for any finitely generated ideal. -/
theorem tilde_toOpen_complement_eq_zero_iff (I : Ideal R) (hI : I.FG) (x : M) :
    tilde.toOpen M (affineSupportComplement I) x = 0 ↔ x ∈ powerTorsion I M := by
  obtain ⟨s, hs⟩ := hI
  have hspan : Ideal.span (Set.range (fun a : s ↦ (a : R))) = I := by
    rw [show Set.range (fun a : s ↦ (a : R)) = (s : Set R) by ext x; simp]
    exact hs
  rw [← hspan]
  exact tilde_toOpen_complement_span_eq_zero_iff M _ x

/-- The associated-sheaf sections supported on `V(I)`, as the kernel of the
restriction from global sections to `Spec R \ V(I)`. -/
def affineSupportedSections (I : Ideal R) :
    Submodule R ((affineTildeSheaf M).presheaf.obj (op ⊤)) :=
  LinearMap.ker ((affineTildeSheaf M).presheaf.map
    (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op).hom

/-- A global section corresponding to `x : M` is supported on `V(I)`
exactly when an ideal power annihilates `x`. -/
theorem tilde_isoTop_mem_affineSupportedSections_iff (I : Ideal R) (hI : I.FG) (x : M) :
    (tilde.isoTop M).hom x ∈ affineSupportedSections M I ↔ x ∈ powerTorsion I M := by
  change ((tilde.toOpen M ⊤) ≫ (affineTildeSheaf M).presheaf.map
    (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op) x = 0 ↔ _
  rw [tilde.toOpen_res]
  exact tilde_toOpen_complement_eq_zero_iff M I hI x

/-- II.(7.5): ideal-power torsion is the module of global sections of the
associated sheaf supported on the finitely generated closed subset. -/
def powerTorsionEquivAffineSupportedSections (I : Ideal R) (hI : I.FG) :
    powerTorsion I M ≃ₗ[R] affineSupportedSections M I :=
  (tilde.isoTop M).toLinearEquiv.submoduleMap (powerTorsion I M) |>.trans
    (LinearEquiv.ofEq _ _ (by
      ext s
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (tilde_isoTop_mem_affineSupportedSections_iff M I hI x).mpr hx
      · intro hs
        have he : (tilde.isoTop M).hom ((tilde.isoTop M).inv s) = s :=
          (tilde.isoTop M).inv_hom_id_apply s
        refine ⟨(tilde.isoTop M).inv s, ?_, he⟩
        exact (tilde_isoTop_mem_affineSupportedSections_iff M I hI _).mp (he.symm ▸ hs)))

/-- The closed subset `V(I)` in the support convention of Exposé I. -/
def affineSupportClosed (I : Ideal R) : Closeds (Spec R) :=
  ⟨PrimeSpectrum.zeroLocus (I : Set R), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- The abelian sheaf underlying the actual associated module sheaf. -/
def affineTildeAbSheaf : TopCat.Sheaf AddCommGrpCat.{u} (Spec R) :=
  (sheafCompose (Opens.grothendieckTopology (Spec R))
    (forget₂ (ModuleCat R) AddCommGrpCat)).obj (affineTildeSheaf M)

/-- The module kernel above is exactly the supported-section group `Γ_Z`
defined in Exposé I after forgetting scalar multiplication. -/
theorem affineSupportedSections_toAddSubgroup (I : Ideal R) :
    (affineSupportedSections M I).toAddSubgroup =
      ExposeI.gammaZ (affineTildeAbSheaf M) (affineSupportClosed I) := by
  change
    (LinearMap.ker ((affineTildeSheaf M).presheaf.map
      (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op).hom).toAddSubgroup =
    (LinearMap.ker ((affineTildeSheaf M).presheaf.map
      (homOfLE (show ⊤ ⊓ affineSupportComplement I ≤ ⊤ from inf_le_left)).op).hom).toAddSubgroup
  exact congrArg (fun U : (Spec R).Opens ↦
    (LinearMap.ker ((affineTildeSheaf M).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op).hom).toAddSubgroup)
      (top_inf_eq _ : (⊤ : (Spec R).Opens) ⊓ affineSupportComplement I =
        affineSupportComplement I).symm

/-- The global section attached to a module element is supported on `V(I)`
in the precise Exposé I sense if and only if that element is ideal-power torsion. -/
theorem tilde_isoTop_mem_gammaZ_iff (I : Ideal R) (hI : I.FG) (x : M) :
    (tilde.isoTop M).hom x ∈ ExposeI.gammaZ (affineTildeAbSheaf M) (affineSupportClosed I) ↔
      x ∈ powerTorsion I M := by
  rw [← affineSupportedSections_toAddSubgroup]
  exact tilde_isoTop_mem_affineSupportedSections_iff M I hI x

/-- The degree-zero geometric comparison as an additive equivalence with
the supported sections defined in Exposé I. -/
def powerTorsionEquivGammaZ (I : Ideal R) (hI : I.FG) :
    powerTorsion I M ≃+ ExposeI.gammaZ (affineTildeAbSheaf M) (affineSupportClosed I) :=
  (powerTorsionEquivAffineSupportedSections M I hI).toAddEquiv.trans
    (AddEquiv.addSubgroupCongr (affineSupportedSections_toAddSubgroup M I))

/-- A module map acts on supported sections through the associated sheaf map. -/
def affineSupportedSectionsMap {M N : ModuleCat.{u} R} (f : M ⟶ N) (I : Ideal R) :
    ModuleCat.of R (affineSupportedSections M I) ⟶
      ModuleCat.of R (affineSupportedSections N I) :=
  ModuleCat.ofHom
    { toFun := fun s ↦
        ⟨(modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) s, by
          have hs : ((affineTildeSheaf M).presheaf.map
              (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op) s = 0 :=
            s.property
          change ((affineTildeSheaf N).presheaf.map
              (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op)
            ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) s) = 0
          have h := ConcreteCategory.congr_hom
            ((modulesSpecToSheaf.map (tilde.map f)).hom.naturality
              (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op) s
          exact h.symm.trans (by
            change (modulesSpecToSheaf.map (tilde.map f)).hom.app
              (op (affineSupportComplement I))
              (((affineTildeSheaf M).presheaf.map
                (homOfLE (show affineSupportComplement I ≤ ⊤ from le_top)).op) s) = 0
            rw [hs]
            exact map_zero ((modulesSpecToSheaf.map (tilde.map f)).hom.app _).hom)⟩
      map_add' := fun s t ↦ Subtype.ext
        (((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤)).hom.map_add s t)
      map_smul' := fun r s ↦ Subtype.ext
        (((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤)).hom.map_smul r s) }

/-- Supported sections of associated module sheaves, functorially in the module. -/
def affineSupportedSectionsFunctor (I : Ideal R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (affineSupportedSections M I)
  map f := affineSupportedSectionsMap f I
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (modulesSpecToSheaf.map (tilde.map (𝟙 M))).hom.app (op ⊤) s = s
    simp only [tilde.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (modulesSpecToSheaf.map (tilde.map (f ≫ g))).hom.app (op ⊤) s =
      (modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)
        ((modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) s)
    simp only [tilde.map_comp, Functor.map_comp]
    rfl

/-- II.10 on principal opens: an injective module over a noetherian ring
surjects onto the sections of its associated sheaf on `D(f)`. -/
theorem tilde_toOpen_basicOpen_surjective_of_injective [IsNoetherianRing R] [Injective M]
    (f : R) : Function.Surjective (tilde.toOpen M (PrimeSpectrum.basicOpen f)) :=
  away_localization_surjective_of_injective M f (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom

/-- The corresponding restriction of actual global sheaf sections to a
principal open is surjective. -/
theorem tilde_globalRestriction_basicOpen_surjective_of_injective
    [IsNoetherianRing R] [Injective M] (f : R) :
    Function.Surjective ((affineTildeSheaf M).presheaf.map
      (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op) := by
  intro s
  obtain ⟨x, hx⟩ := tilde_toOpen_basicOpen_surjective_of_injective M f s
  exact ⟨tilde.toOpen M ⊤ x,
    (ConcreteCategory.congr_hom (tilde.toOpen_res M ⊤ (PrimeSpectrum.basicOpen f)
      (homOfLE le_top)) x).trans hx⟩

end SGA.SGA2.ExposeII
