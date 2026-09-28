/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.Restrict
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The first fundamental exact sequence

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the sequence of `𝒪_X`-modules
`f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` is exact
(`Scheme.Hom.relativeDifferentialsShortComplex_exact`; EGA IV 16.4.19, Stacks Project,
Tag 01UW). The proof is formal: `Ω_{X/Z} ⟶ Ω_{X/Y}` is the cokernel of the first map because a
`Z`-derivation of `𝒪_X` is a `Y`-derivation exactly when it vanishes on `f⁻¹ 𝒪_Y`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules.Derivation

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {M : X.Modules}

/-- A derivation relative to `f ≫ g` which vanishes on the sections `f^♯ s` is a derivation
relative to `f`. -/
def ofRestrictScalarsOfAppEqZero (D : M.Derivation (f ≫ g))
    (h : ∀ (V : Y.Opens) (s : Γ(Y, V)), D.app (f ⁻¹ᵁ V) (f.app V s) = 0) : M.Derivation f where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {V} s := h V.unop s

@[simp]
lemma ofRestrictScalarsOfAppEqZero_app (D : M.Derivation (f ≫ g))
    (h : ∀ (V : Y.Opens) (s : Γ(Y, V)), D.app (f ⁻¹ᵁ V) (f.app V s) = 0) (U : X.Opens)
    (a : Γ(X, U)) : (D.ofRestrictScalarsOfAppEqZero h).app U a = D.app U a :=
  rfl

end Scheme.Modules.Derivation

namespace Scheme.Hom

open Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The adjoint `Ω_{Y/Z} ⟶ f_* Ω_{X/Z}` of the canonical map `f^* Ω_{Y/Z} ⟶ Ω_{X/Z}`: it sends
`d s` to `d (f^♯ s)`. -/
def relativeDifferentialsToPushforward :
    g.relativeDifferentials ⟶ (pushforward f).obj (f ≫ g).relativeDifferentials :=
  g.isUniversal.desc (f ≫ g).universalDerivation.pushforward

@[simp]
lemma relativeDifferentialsToPushforward_app (V : Y.Opens) (s : Γ(Y, V)) :
    (relativeDifferentialsToPushforward f g).app V (g.universalDerivation.app V s) =
      (f ≫ g).universalDerivation.app (f ⁻¹ᵁ V) (f.app V s) :=
  g.isUniversal.desc_app_app _ V s

/-- The canonical map `f^* Ω_{Y/Z} ⟶ Ω_{X/Z}`. -/
def pullbackRelativeDifferentialsMap :
    (Scheme.Modules.pullback f).obj g.relativeDifferentials ⟶ (f ≫ g).relativeDifferentials :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm (relativeDifferentialsToPushforward f g)

/-- The canonical map `Ω_{X/Z} ⟶ Ω_{X/Y}`, sending `d a` to `d a`. -/
def relativeDifferentialsMap : (f ≫ g).relativeDifferentials ⟶ f.relativeDifferentials :=
  (f ≫ g).isUniversal.desc (f.universalDerivation.restrictScalars f g)

@[simp]
lemma relativeDifferentialsMap_app (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsMap f g).app U ((f ≫ g).universalDerivation.app U a) =
      f.universalDerivation.app U a :=
  (f ≫ g).isUniversal.desc_app_app _ U a

lemma relativeDifferentialsToPushforward_comp_eq_zero {M : X.Modules}
    (α : (f ≫ g).relativeDifferentials ⟶ M) :
    relativeDifferentialsToPushforward f g ≫ (pushforward f).map α = 0 ↔
      ∀ (V : Y.Opens) (s : Γ(Y, V)),
        ((f ≫ g).universalDerivation.postcomp α).app (f ⁻¹ᵁ V) (f.app V s) = 0 := by
  constructor
  · intro h V s
    have := congr($(h).app V (g.universalDerivation.app V s))
    rwa [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      relativeDifferentialsToPushforward_app] at this
  · intro h
    refine g.isUniversal.hom_ext fun V s ↦ ?_
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      relativeDifferentialsToPushforward_app]
    exact h V s

lemma pullbackRelativeDifferentialsMap_comp_eq_zero_iff {M : X.Modules}
    (α : (f ≫ g).relativeDifferentials ⟶ M) :
    pullbackRelativeDifferentialsMap f g ≫ α = 0 ↔
      ∀ (V : Y.Opens) (s : Γ(Y, V)),
        ((f ≫ g).universalDerivation.postcomp α).app (f ⁻¹ᵁ V) (f.app V s) = 0 := by
  rw [← relativeDifferentialsToPushforward_comp_eq_zero,
    ← ((pullbackPushforwardAdjunction f).homEquiv _ _).injective.eq_iff,
    Adjunction.homEquiv_naturality_right, pullbackRelativeDifferentialsMap,
    Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

@[reassoc (attr := simp)]
lemma pullbackRelativeDifferentialsMap_comp_relativeDifferentialsMap :
    pullbackRelativeDifferentialsMap f g ≫ relativeDifferentialsMap f g = 0 := by
  rw [pullbackRelativeDifferentialsMap_comp_eq_zero_iff]
  intro V s
  rw [Derivation.postcomp_app, relativeDifferentialsMap_app, Derivation.app_app]

/-- The complex `f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y}`. -/
@[simps!]
def relativeDifferentialsShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk _ _ (pullbackRelativeDifferentialsMap_comp_relativeDifferentialsMap f g)

/-- `Ω_{X/Z} ⟶ Ω_{X/Y}` is the cokernel of `f^* Ω_{Y/Z} ⟶ Ω_{X/Z}`. -/
def relativeDifferentialsMapIsCokernel :
    IsColimit (CokernelCofork.ofπ _
      (pullbackRelativeDifferentialsMap_comp_relativeDifferentialsMap f g)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun α hα ↦ f.isUniversal.desc
      (((f ≫ g).universalDerivation.postcomp α).ofRestrictScalarsOfAppEqZero
        ((pullbackRelativeDifferentialsMap_comp_eq_zero_iff f g α).mp hα)))
    (fun α hα ↦ (f ≫ g).isUniversal.hom_ext fun U a ↦ by
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, relativeDifferentialsMap_app,
        Derivation.Universal.desc_app_app, Derivation.ofRestrictScalarsOfAppEqZero_app,
        Derivation.postcomp_app])
    (fun α hα m hm ↦ f.isUniversal.hom_ext fun U a ↦ by
      rw [Derivation.Universal.desc_app_app, Derivation.ofRestrictScalarsOfAppEqZero_app,
        Derivation.postcomp_app, ← hm, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        relativeDifferentialsMap_app])

/-- The first fundamental exact sequence `f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`
(EGA IV 16.4.19; Stacks Project, Tag 01UW). -/
theorem relativeDifferentialsShortComplex_exact :
    (relativeDifferentialsShortComplex f g).Exact ∧ Epi (relativeDifferentialsMap f g) :=
  (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).mpr ⟨relativeDifferentialsMapIsCokernel f g⟩

instance : Epi (relativeDifferentialsMap f g) :=
  (relativeDifferentialsShortComplex_exact f g).2

end Scheme.Hom

end AlgebraicGeometry
