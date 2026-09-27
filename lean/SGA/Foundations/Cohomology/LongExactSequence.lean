/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Modules
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The long exact cohomology sequence of `𝒪_X`-modules

The functor `M ↦ M.toAbSheaf` from `𝒪_X`-modules to abelian sheaves is exact: it preserves finite
limits (mathlib) and epimorphisms (`Scheme.Modules.epi_toAbSheaf`, since cokernels of sheaves of
modules are sheafifications of presheaf cokernels, computed on underlying abelian presheaves).
Hence a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `𝒪_X`-modules gives a long exact sequence
of `Γ(X, 𝒪_X)`-modules
`⋯ → Hⁿ(U, M₁) → Hⁿ(U, M₂) → Hⁿ(U, M₃) → H^{n+1}(U, M₁) → ⋯`
(EGA 0_III 12.1; Hartshorne III.1.1A, III.2).

## Main results

* `AlgebraicGeometry.Scheme.Modules.epi_toAbSheaf`, `shortExact_toAbSheaf`.
* `AlgebraicGeometry.Scheme.Modules.H'.δ`: the connecting map, `Γ(X, 𝒪_X)`-linear.
* `AlgebraicGeometry.Scheme.Modules.H'.exact_map_map`, `exact_map_δ`, `exact_δ_map`: exactness.
-/

universe u

open CategoryTheory Limits TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The underlying abelian sheaf functor `X.Modules ⥤ Ab(X)` preserves epimorphisms. -/
lemma epi_toAbSheaf {M N : X.Modules} (g : M ⟶ N) [Epi g] : Epi (Hom.toAbSheaf g) := by
  let P := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let Φ := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h1 : IsZero (cokernel g) := isZero_cokernel_of_epi g
  have e1 : cokernel (P.map (Φ.map g)) ≅ cokernel g :=
    cokernel.mapIso _ _ (ε.app M) (ε.app N) (ε.hom.naturality g)
  have e2 : P.obj (cokernel (Φ.map g)) ≅ cokernel (P.map (Φ.map g)) := PreservesCokernel.iso P _
  have h2 : IsZero ((SheafOfModules.toSheaf _).obj (P.obj (cokernel (Φ.map g)))) :=
    Functor.map_isZero _ (h1.of_iso (e2 ≪≫ e1))
  let K := cokernel (Φ.map g)
  let η := asIso (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).counit
  have e3 : (SheafOfModules.toSheaf _).obj (P.obj K) ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((PresheafOfModules.toPresheaf _).obj K) :=
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 X.ringCatSheaf.obj)).app K
  have e4 : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      ((PresheafOfModules.toPresheaf _).obj K) ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (cokernel ((PresheafOfModules.toPresheaf _).map (Φ.map g))) :=
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
      (PreservesCokernel.iso _ _)
  have e5 : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (cokernel ((PresheafOfModules.toPresheaf _).map (Φ.map g))) ≅
      cokernel ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map (Φ.map g))) :=
    PreservesCokernel.iso _ _
  have e6 : cokernel ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf _).map (Φ.map g))) ≅ cokernel (Hom.toAbSheaf g) :=
    cokernel.mapIso _ _ (η.app M.toAbSheaf) (η.app N.toAbSheaf)
      (η.hom.naturality (Hom.toAbSheaf g))
  exact Preadditive.epi_of_isZero_cokernel _ (h2.of_iso (e3 ≪≫ e4 ≪≫ e5 ≪≫ e6).symm)

variable (X) in
/-- The underlying abelian sheaf functor `X.Modules ⥤ Ab(X)`. -/
noncomputable abbrev toAbSheafFunctor :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance : (toAbSheafFunctor X).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ CategoryTheory.Sheaf.hom_ext rfl⟩

instance : PreservesFiniteLimits (toAbSheafFunctor X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

/-- The underlying abelian sheaves of a short exact sequence of `𝒪_X`-modules form a short exact
sequence. -/
lemma shortExact_toAbSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheafFunctor X)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono ((toAbSheafFunctor X).map S.f) := inferInstance
  exact
    { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
      mono_f := hmono
      epi_g := epi_toAbSheaf S.g }

/-- The short complex of underlying abelian sheaves of a short complex of `𝒪_X`-modules. -/
noncomputable abbrev abShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Hom.toAbSheaf S.f) (Hom.toAbSheaf S.g)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg _ S.zero).trans (Functor.map_zero _ _ _)))

lemma shortExact_abShortComplex {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (abShortComplex S).ShortExact :=
  shortExact_toAbSheaf hS

/-- The free abelian sheaf `ℤ_U` on an open `U`, so that `Hⁿ(U, F) = Extⁿ(ℤ_U, F)`. -/
noncomputable abbrev freeSheaf (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- A class in `Hⁿ(U, M)`, as an element of `Extⁿ(ℤ_U, M)`. -/
abbrev H'.toExt {M : X.Modules} {n : ℕ} {U : X.Opens} (x : M.H' n U) :
    Ext (freeSheaf U) M.toAbSheaf n :=
  x

lemma comp_extClass_naturality
    {C : Type*} [Category* C] [Abelian C] [HasExt.{u} C] {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {A : C} {n : ℕ}
    (x : Ext A S₁.X₃ n) :
    (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass rfl =
      (x.comp h₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    h₁.extClass_naturality h₂ φ]

section LongExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

/-- Multiplication by `r ∈ Γ(X, 𝒪_X)` as an endomorphism of the short exact sequence of underlying
abelian sheaves. -/
noncomputable def smulShortComplexHom (r : Γ(X, ⊤)) : abShortComplex S ⟶ abShortComplex S where
  τ₁ := S.X₁.smulHom r
  τ₂ := S.X₂.smulHom r
  τ₃ := S.X₃.smulHom r
  comm₁₂ := (Hom.toAbSheaf_smulHom S.f r).symm
  comm₂₃ := (Hom.toAbSheaf_smulHom S.g r).symm

/-- The connecting map `Hⁿ(U, M₃) → H^{n+1}(U, M₁)` of a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `𝒪_X`-modules. -/
noncomputable def H'.δ (n : ℕ) (U : X.Opens) : S.X₃.H' n U →ₗ[Γ(X, ⊤)] S.X₁.H' (n + 1) U where
  toFun x := (H'.toExt x).comp (shortExact_abShortComplex hS).extClass rfl
  map_add' _ _ := Ext.add_comp _ _ _ _
  map_smul' r x := comp_extClass_naturality.{u}
    (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (shortExact_abShortComplex hS)
    (shortExact_abShortComplex hS) (smulShortComplexHom r) (H'.toExt x)

lemma H'.δ_apply {n : ℕ} {U : X.Opens} (x : S.X₃.H' n U) :
    H'.δ hS n U x = (H'.toExt x).comp (shortExact_abShortComplex hS).extClass rfl :=
  rfl

include hS in
/-- Exactness of `Hⁿ(U, M₁) → Hⁿ(U, M₂) → Hⁿ(U, M₃)`. -/
lemma H'.exact_map_map (n : ℕ) (U : X.Opens) :
    Function.Exact (H'.map S.f n U) (H'.map S.g n U) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ (freeSheaf U) (shortExact_abShortComplex hS)
      (H'.toExt y) hy
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    rw [← H'.map_comp_apply, S.zero]
    change Sheaf.H'.map ((toAbSheafFunctor X).map (0 : S.X₁ ⟶ S.X₃)) n U x = 0
    rw [Functor.map_zero]
    exact Sheaf.H'.map_zero_apply x

/-- Exactness of `Hⁿ(U, M₂) → Hⁿ(U, M₃) → H^{n+1}(U, M₁)`. -/
lemma H'.exact_map_δ (n : ℕ) (U : X.Opens) :
    Function.Exact (H'.map S.g n U) (H'.δ hS n U) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf U) (shortExact_abShortComplex hS)
      (H'.toExt y) rfl hy
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    change ((H'.toExt x).comp (Ext.mk₀ (abShortComplex S).g) (add_zero n)).comp
      (shortExact_abShortComplex hS).extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, (shortExact_abShortComplex hS).comp_extClass,
      Ext.comp_zero]

/-- Exactness of `Hⁿ(U, M₃) → H^{n+1}(U, M₁) → H^{n+1}(U, M₂)`. -/
lemma H'.exact_δ_map (n : ℕ) (U : X.Opens) :
    Function.Exact (H'.δ hS n U) (H'.map S.f (n + 1) U) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ (freeSheaf U) (shortExact_abShortComplex hS)
      (H'.toExt y) hy rfl
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    change ((H'.toExt x).comp (shortExact_abShortComplex hS).extClass rfl).comp
      (Ext.mk₀ (abShortComplex S).f) (add_zero (n + 1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, (shortExact_abShortComplex hS).extClass_comp,
      Ext.comp_zero]

end LongExact

end AlgebraicGeometry.Scheme.Modules
