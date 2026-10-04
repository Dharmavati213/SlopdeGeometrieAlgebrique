/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Modules
import SGA.Foundations.Analytic.Morphisms
import SGA.Foundations.Cohomology.Modules

/-!
# The `Γ(X, 𝒪_X)`-module structure on the cohomology of `𝒪_X`-modules

For a locally ringed space `X` (e.g. a complex analytic space) and an `𝒪_X`-module `M`, a global
section `r ∈ Γ(X, 𝒪_X)` acts on `M` by multiplication, an endomorphism `M.smulHom r` of the
underlying abelian sheaf; hence it acts on the cohomology `Hⁿ(U, M)` (computed, as in
`SGA.Foundations.Cohomology.Basic`, as `Extⁿ(ℤ_U, M)` in abelian sheaves). This makes `Hⁿ(U, M)` a
`Γ(X, 𝒪_X)`-module (`LocallyRingedSpace.Modules.cohomologyModule`), and, along a ring map
`R → Γ(X, 𝒪_X)`, an `R`-module. For a complex analytic space with structure morphism
`s : X ⟶ Spec ℂ`, the ring map `ℂ → Γ(X, 𝒪_X)` is `LocallyRingedSpace.structureRingHom s`; the
resulting `ℂ`-vector space structure on `Hⁿ(X, M)` is the one in which the Cartan–Serre finiteness
theorem is stated (`AnalyticGeometry.CartanSerreFinitenessStatement`).

This is, for locally ringed spaces, the scheme-theoretic construction of
`SGA.Foundations.Cohomology.Basic` and `SGA.Foundations.Cohomology.Modules` (EGA III 1.4.1;
EGA 0_III 12.1). For a scheme the two agree: `Scheme.Modules.smulHom_eq_locallyRingedSpace` and
`Scheme.Modules.cohomologyModule_id_eq` (the module structure of `Scheme.Modules.H'`).
-/

universe u

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- The ring map `R → Γ(X, 𝒪_X)` corresponding to a morphism `X ⟶ Spec R`. -/
def structureRingHom {R : CommRingCat.{u}} (s : X ⟶ Spec.locallyRingedSpaceObj R) :
    R →+* X.presheaf.obj (op ⊤) :=
  (toSpecΓ R ≫ Γ.map s.op).hom

namespace Modules

/-- Multiplication by a global section `r` of `𝒪_X`, as an endomorphism of the underlying abelian
sheaf of an `𝒪_X`-module. -/
def smulHom (M : X.Modules) (r : X.presheaf.obj (op ⊤)) : M.toAbSheaf ⟶ M.toAbSheaf :=
  ObjectProperty.homMk
    { app V := AddCommGrpCat.ofHom (show M.val.obj V →+ M.val.obj V from
        DistribSMul.toAddMonoidHom _
          (show X.ringCatSheaf.obj.obj V from
            X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op r))
      naturality V W f := AddCommGrpCat.ext fun (s : M.val.obj V) ↦ by
        change (show X.ringCatSheaf.obj.obj W from
            X.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op r) • M.val.map f s =
          M.val.map f ((show X.ringCatSheaf.obj.obj V from
            X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op r) • s)
        rw [PresheafOfModules.map_smul]
        congr 1
        change _ = (X.presheaf.map _ ≫ X.presheaf.map f) r
        rw [← X.presheaf.map_comp]
        rfl }

lemma smulHom_app_apply (M : X.Modules) (r : X.presheaf.obj (op ⊤)) {V : Opens X}
    (s : M.val.obj (op V)) :
    (M.smulHom r).hom.app (op V) s =
      (show X.ringCatSheaf.obj.obj (op V) from
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) • s :=
  rfl

lemma toAbSheaf_hom_ext {M N : X.Modules} {f g : M.toAbSheaf ⟶ N.toAbSheaf}
    (h : ∀ (V : Opens X) (s : M.val.obj (op V)), f.hom.app (op V) s = g.hom.app (op V) s) :
    f = g :=
  CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ AddCommGrpCat.ext fun s ↦ h V.unop s))

@[simp]
lemma smulHom_one (M : X.Modules) : M.smulHom 1 = 𝟙 _ :=
  toAbSheaf_hom_ext fun V s ↦ by
    rw [smulHom_app_apply]
    have h1 : (show X.ringCatSheaf.obj.obj (op V) from
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op 1) = 1 := map_one _
    rw [h1]
    exact one_smul _ s

lemma smulHom_mul (M : X.Modules) (r s : X.presheaf.obj (op ⊤)) :
    M.smulHom (r * s) = M.smulHom s ≫ M.smulHom r :=
  toAbSheaf_hom_ext fun V t ↦ by
    simp only [smulHom_app_apply, map_mul]
    exact mul_smul _ _ t

lemma smulHom_add (M : X.Modules) (r s : X.presheaf.obj (op ⊤)) :
    M.smulHom (r + s) = M.smulHom r + M.smulHom s :=
  toAbSheaf_hom_ext fun V t ↦ by
    rw [smulHom_app_apply]
    have h1 : (show X.ringCatSheaf.obj.obj (op V) from
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (r + s)) =
        (show X.ringCatSheaf.obj.obj (op V) from X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) +
          (show X.ringCatSheaf.obj.obj (op V) from
            X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) := map_add _ _ _
    rw [h1]
    exact add_smul _ _ t

@[simp]
lemma smulHom_zero (M : X.Modules) : M.smulHom 0 = 0 :=
  toAbSheaf_hom_ext fun V t ↦ by
    simp only [smulHom_app_apply, map_zero]
    exact zero_smul _ t

/-- The action of `Γ(X, 𝒪_X)` on the underlying abelian sheaf of an `𝒪_X`-module. -/
def smulRingHom (M : X.Modules) : X.presheaf.obj (op ⊤) →+* End M.toAbSheaf where
  toFun := M.smulHom
  map_one' := M.smulHom_one
  map_mul' := M.smulHom_mul
  map_zero' := M.smulHom_zero
  map_add' := M.smulHom_add

/-- The `R`-module structure on `Hⁿ(U, M)` induced by a ring map `φ : R → Γ(X, 𝒪_X)`: `r` acts
through multiplication by `φ r` on `M`. (A definition, to be used with `letI`.) -/
abbrev cohomologyModule {R : Type*} [Semiring R] (φ : R →+* X.presheaf.obj (op ⊤))
    (M : X.Modules) (n : ℕ) (U : Opens X) : Module R (M.toAbSheaf.H' n U) :=
  Module.compHom (M.toAbSheaf.H' n U)
    (((CategoryTheory.Sheaf.H'.endRingHom M.toAbSheaf n U).comp M.smulRingHom).comp φ)

lemma cohomologyModule_smul_def {R : Type*} [Semiring R] (φ : R →+* X.presheaf.obj (op ⊤))
    (M : X.Modules) (n : ℕ) (U : Opens X) (r : R) (x : M.toAbSheaf.H' n U) :
    letI := cohomologyModule φ M n U
    r • x = CategoryTheory.Sheaf.H'.map (M.smulHom (φ r)) n U x :=
  rfl

end Modules

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- For a scheme, multiplication by a global section of `𝒪_X` is the same endomorphism whether `X`
is seen as a scheme or as a locally ringed space. -/
lemma smulHom_eq_locallyRingedSpace (M : X.Modules) (r : Γ(X, ⊤)) :
    LocallyRingedSpace.Modules.smulHom (X := X.toLocallyRingedSpace) M r = M.smulHom r :=
  toAbSheaf_hom_ext fun _ _ ↦ rfl

/-- For a scheme, the `Γ(X, 𝒪_X)`-module structure on `Hⁿ(U, M)` of
`LocallyRingedSpace.Modules.cohomologyModule` (along the identity) is the instance of
`SGA.Foundations.Cohomology.Basic`. -/
lemma cohomologyModule_id_eq (M : X.Modules) (n : ℕ) (U : X.Opens) :
    LocallyRingedSpace.Modules.cohomologyModule (X := X.toLocallyRingedSpace)
      (RingHom.id Γ(X, ⊤)) M n U = (inferInstance : Module Γ(X, ⊤) (M.H' n U)) := by
  refine Module.ext' _ _ fun r x ↦ ?_
  change CategoryTheory.Sheaf.H'.map
      (LocallyRingedSpace.Modules.smulHom (X := X.toLocallyRingedSpace) M r) n U x =
    CategoryTheory.Sheaf.H'.map (M.smulHom r) n U x
  rw [smulHom_eq_locallyRingedSpace]

end AlgebraicGeometry.Scheme.Modules
