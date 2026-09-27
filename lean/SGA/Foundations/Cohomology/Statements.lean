/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Modules
import SGA.Foundations.Cohomology.Cech
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Statements for stages II and III of the cohomology of coherent sheaves

This file records, as `Prop`-valued definitions, the theorems of EGA III that SGA 1 X (and
SGA 1 IX.1.10, XIII) relies on and that are not yet proved here. They are formulated with the
framework of `SGA.Foundations.Cohomology.Basic` / `Modules` (cohomology of `𝒪_X`-modules as
`Γ(X, 𝒪_X)`-modules). Each docstring cites the reference and says how the statement differs from
it, if at all.

Auxiliary definitions:
* `AlgebraicGeometry.Scheme.Modules.IsCoherent`: quasi-coherent of finite type (on a locally
  noetherian scheme, this is coherence);
* `AlgebraicGeometry.Scheme.Hom.specStructureRingHom`: for `f : X ⟶ Spec A`, the ring map
  `A → Γ(X, 𝒪_X)`, and `Scheme.Modules.moduleOver`, the resulting `A`-module structure on `Hⁿ`;
* `AlgebraicGeometry.projectiveSpace A r = Proj A[x₀, …, x_r]`;
* `AlgebraicGeometry.Scheme.Modules.quotientIdealPow`: `F / I^{n+1} F` for an ideal `I` of the
  base ring, with its transition maps, and the inverse limit `formalLimit` of the cohomology
  groups `Hⁱ(X, F / I^{n+1} F)`;
* `AlgebraicGeometry.thickening`: `X_n = X ×_{Spec A} Spec (A / I^{n+1})`.

The statements, in the order in which they should be proved:
1. `ProjectiveSpaceStructureSheafStatement` (Stacks 01XT, the case `d = 0`; EGA III 2.1.12):
   proved, `AlgebraicGeometry.projectiveSpaceStructureSheafStatement` in
   `SGA.Foundations.Cohomology.ProjectiveSpace`.
2. `ProperFinitenessStatement` (EGA III 3.2.1; Stacks 02O5), which contains Serre's finiteness
   theorem for projective schemes (EGA III 2.2.1 (i); Hartshorne III.5.2 (a)): proved,
   `AlgebraicGeometry.properFinitenessStatement` in `SGA.Foundations.Cohomology.ProperFiniteness`
   (the H-projective case is `AlgebraicGeometry.properFiniteness_of_isHProjective`).
3. `FormalFunctionsStatement` (EGA III 4.1.5; Stacks 02OC): proved,
   `AlgebraicGeometry.formalFunctionsStatement` in `SGA.Foundations.Cohomology.FormalFunctions`.
4. `ZariskiConnectednessStatement` (EGA III 4.3.1), `SteinFactorizationStatement`
   (EGA III 4.3.3): proved, `AlgebraicGeometry.zariskiConnectednessStatement` in
   `SGA.Foundations.Cohomology.ZariskiConnectedness` and
   `AlgebraicGeometry.steinFactorizationStatement` in
   `SGA.Foundations.Cohomology.SteinFactorization`.
5. `GrothendieckExistenceStatement` (EGA III 5.1.4; Stacks 088C): the fully faithful half is
   proved, `AlgebraicGeometry.grothendieckExistence_fullyFaithful` in
   `SGA.Foundations.Cohomology.ExistenceFullyFaithful`; essential surjectivity remains.

The comparison of Čech cohomology with cohomology (Stacks 01XD) is proved, `Γ(X, 𝒪_X)`-linearly,
in `SGA.Foundations.Cohomology.AffineOpenVanishing` (`Scheme.Modules.cechHomologyLinearEquiv`).
The twisting sheaves `𝒪(d)` on `ℙʳ_A` and their cohomology (Stacks 01XT) are in
`SGA.Foundations.Cohomology.ProjectiveSpaceTwist`; Serre's vanishing `Hⁱ(ℙʳ_A, F(d)) = 0` for
`i > 0`, `d ≫ 0` (EGA III 2.2.1 (ii); Hartshorne III.5.2 (b)) is
`AlgebraicGeometry.projectiveSpace.exists_H_twist_subsingleton` in
`SGA.Foundations.Cohomology.Serre`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

section Preliminaries

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *coherent* if it is quasi-coherent and of finite type. On a locally
noetherian scheme this agrees with coherence (EGA 0_I 5.3, EGA I 1.5.1); we only use it there. -/
class Scheme.Modules.IsCoherent (M : X.Modules) : Prop where
  isQuasicoherent : M.IsQuasicoherent
  isFiniteType : SheafOfModules.IsFiniteType.{u} M

/-- For a morphism `f : X ⟶ Spec A`, the ring map `A → Γ(X, 𝒪_X)`. -/
noncomputable def Scheme.Hom.specStructureRingHom {A : CommRingCat.{u}} (f : X ⟶ Spec A) :
    A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom

/-- For `f : X ⟶ Spec A`, the `A`-module structure on `Hⁿ(U, M)` induced by `A → Γ(X, 𝒪_X)`
(EGA III 1.4.1). -/
noncomputable abbrev Scheme.Modules.moduleOver {A : CommRingCat.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) (n : ℕ) (U : X.Opens) : Module A (M.H' n U) :=
  Module.compHom (M.H' n U) f.specStructureRingHom

end Preliminaries

/-! ## Stage II -/

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Projective space `ℙʳ_A = Proj A[x₀, …, x_r]` over a commutative ring `A`, for the grading by
total degree. -/
noncomputable def projectiveSpace (A : CommRingCat.{u}) (r : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The structure morphism `ℙʳ_A ⟶ Spec A₀`, where `A₀ ≅ A` is the degree-zero part of
`A[x₀, …, x_r]`. -/
noncomputable def projectiveSpace.toSpecZero (A : CommRingCat.{u}) (r : ℕ) :
    projectiveSpace A r ⟶ Spec (.of (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A 0)) :=
  Proj.toSpecZero _

/-- **Cohomology of the structure sheaf of projective space** (Stacks Tag 01XT for `d = 0`;
EGA III 2.1.12; Hartshorne III.5.1): `Γ(ℙʳ_A, 𝒪) = A` and `Hᵖ(ℙʳ_A, 𝒪) = 0` for `p > 0`. It is
proved as `AlgebraicGeometry.projectiveSpaceStructureSheafStatement`
(`SGA.Foundations.Cohomology.ProjectiveSpace`); the cohomology of `𝒪(d)` is in
`SGA.Foundations.Cohomology.ProjectiveSpaceTwist`. -/
def ProjectiveSpaceStructureSheafStatement : Prop :=
  ∀ (A : CommRingCat.{u}) (r : ℕ),
    IsIso (projectiveSpace.toSpecZero A r).appTop ∧
      ∀ p : ℕ, Subsingleton
        (Scheme.Modules.H (SheafOfModules.unit (projectiveSpace A r).ringCatSheaf) (p + 1))

/-- **Finiteness of cohomology of coherent sheaves under proper morphisms** (EGA III 3.2.1, in the
form of EGA III 3.2.3 over an affine base; Stacks Tag 02O5), statement only: if `A` is noetherian,
`f : X ⟶ Spec A` is proper and `M` is coherent, then every `Hᵖ(X, M)` is a finite `A`-module.
Together with Čech comparison this is equivalent to the coherence of `Rᵖf_* M` for proper `f` over
a locally noetherian base (EGA III 1.4.11). It contains Serre's finiteness theorem for projective
schemes (EGA III 2.2.1; Hartshorne III.5.2 (a)), which is the first step of its proof. Proved as
`AlgebraicGeometry.properFinitenessStatement` (`SGA.Foundations.Cohomology.ProperFiniteness`). -/
def ProperFinitenessStatement : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f]
    (M : X.Modules) [M.IsCoherent] (p : ℕ),
    letI := M.moduleOver f p ⊤
    Module.Finite A (M.H p)

/-! ## Stage III -/

section FormalFunctions

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) (I : Ideal A) (M : X.Modules)

/-- The map `⊕_{a ∈ I^{n+1}} M → M` given by multiplication by the elements of `I^{n+1}`. -/
noncomputable def Scheme.Modules.idealPowSMul (n : ℕ) :
    ∐ (fun _ : (I ^ (n + 1) : Ideal A) ↦ M) ⟶ M :=
  Sigma.desc fun a ↦ M.smulEnd (f.specStructureRingHom a)

/-- The `𝒪_X`-module `M / I^{n+1} M`, for an ideal `I` of the base ring `A` of `f : X ⟶ Spec A`. -/
noncomputable abbrev Scheme.Modules.quotientIdealPow (n : ℕ) : X.Modules :=
  cokernel (M.idealPowSMul f I n)

/-- The projection `M → M / I^{n+1} M`. -/
noncomputable abbrev Scheme.Modules.toQuotientIdealPow (n : ℕ) : M ⟶ M.quotientIdealPow f I n :=
  cokernel.π _

lemma Scheme.Modules.smulEnd_toQuotientIdealPow {n : ℕ} (a : A) (ha : a ∈ I ^ (n + 1)) :
    M.smulEnd (f.specStructureRingHom a) ≫ M.toQuotientIdealPow f I n = 0 := by
  have : M.smulEnd (f.specStructureRingHom a) =
      Sigma.ι (fun _ : (I ^ (n + 1) : Ideal A) ↦ M) ⟨a, ha⟩ ≫ M.idealPowSMul f I n := by
    simp [Scheme.Modules.idealPowSMul]
  rw [this, Category.assoc, cokernel.condition, comp_zero]

/-- The transition map `M / I^{n+2} M → M / I^{n+1} M`. -/
noncomputable def Scheme.Modules.quotientIdealPowMap (n : ℕ) :
    M.quotientIdealPow f I (n + 1) ⟶ M.quotientIdealPow f I n :=
  cokernel.desc _ (M.toQuotientIdealPow f I n) (Sigma.hom_ext _ _ fun a ↦ by
    simp only [Scheme.Modules.idealPowSMul, Sigma.ι_desc_assoc, comp_zero]
    exact M.smulEnd_toQuotientIdealPow f I a.1 (Ideal.pow_le_pow_right (Nat.le_succ _) a.2))

@[reassoc (attr := simp)]
lemma Scheme.Modules.toQuotientIdealPow_comp_map (n : ℕ) :
    M.toQuotientIdealPow f I (n + 1) ≫ M.quotientIdealPowMap f I n =
      M.toQuotientIdealPow f I n :=
  cokernel.π_desc _ _ _

variable (p : ℕ)

/-- The inverse limit `lim_n Hᵖ(X, M / I^{n+1} M)`, as a `Γ(X, 𝒪_X)`-submodule of the product. -/
noncomputable def Scheme.Modules.formalLimit :
    Submodule Γ(X, ⊤) (∀ n : ℕ, (M.quotientIdealPow f I n).H p) where
  carrier := {x | ∀ n, Scheme.Modules.H'.map (M.quotientIdealPowMap f I n) p ⊤ (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by simp only [Pi.add_apply, map_add, hx n, hy n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  smul_mem' a x hx n := by simp only [Pi.smul_apply, LinearMap.map_smul, hx n]

/-- The canonical map `Hᵖ(X, M) → lim_n Hᵖ(X, M / I^{n+1} M)`. -/
noncomputable def Scheme.Modules.toFormalLimit : M.H p →ₗ[Γ(X, ⊤)] M.formalLimit f I p where
  toFun x := ⟨fun n ↦ Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) p ⊤ x, fun n ↦ by
    rw [← Scheme.Modules.H'.map_comp_apply, Scheme.Modules.toQuotientIdealPow_comp_map]⟩
  map_add' x y := by ext n; simp
  map_smul' a x := by ext n; simp

end FormalFunctions

/-- **The theorem on formal functions** (EGA III 4.1.5; Stacks Tag 02OC; Hartshorne III.11.1),
statement only. Let `A` be noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper and `M` coherent.
Then `lim_n Hᵖ(X, M / I^{n+1} M)` is the `I`-adic completion of `Hᵖ(X, M)`: there is an
`A`-linear isomorphism from `AdicCompletion I (Hᵖ(X, M))` to the inverse limit which is the
canonical map `toFormalLimit` on `Hᵖ(X, M)`. (EGA asserts that the canonical, continuous, map is an
isomorphism; here the isomorphism is only required to extend the canonical map on `Hᵖ(X, M)`.
Note also that `Hᵖ(X, M / I^{n+1} M) = Hᵖ(X_n, M|_{X_n})` for `X_n = X ×_A A/I^{n+1}`, which is how
EGA states it.) Proved as `AlgebraicGeometry.formalFunctionsStatement`
(`SGA.Foundations.Cohomology.FormalFunctions`). -/
def FormalFunctionsStatement : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (I : Ideal A) (X : Scheme.{u}) (f : X ⟶ Spec A)
    [IsProper f] (M : X.Modules) [M.IsCoherent] (p : ℕ),
    letI := M.moduleOver f p ⊤
    letI := Module.compHom (M.formalLimit f I p) f.specStructureRingHom
    ∃ e : AdicCompletion I (M.H p) ≃ₗ[A] M.formalLimit f I p,
      ∀ x, e (AdicCompletion.of I (M.H p) x) = M.toFormalLimit f I p x

/-- **Zariski's connectedness theorem** (EGA III 4.3.1; part of Stacks Tag 03H0;
Hartshorne III.11.3),
statement only: if `f : X ⟶ Y` is proper, `Y` is locally noetherian and `𝒪_Y → f_* 𝒪_X` is an
isomorphism, then every fibre of `f` is connected (and non-empty). Proved as
`AlgebraicGeometry.zariskiConnectednessStatement`
(`SGA.Foundations.Cohomology.ZariskiConnectedness`). -/
def ZariskiConnectednessStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y],
    (∀ V : Y.Opens, IsIso (f.app V)) → ∀ y : Y, ConnectedSpace (f.fiber y)

/-- **Stein factorization** (EGA III 4.3.3; Stacks Tag 03H0; Hartshorne III.11.5), statement only:
a proper morphism `f : X ⟶ Y` to a locally noetherian scheme factors as `X ⟶ Y' ⟶ Y` with
`Y' ⟶ Y` finite and `g : X ⟶ Y'` proper with `𝒪_{Y'} ≅ g_* 𝒪_X` and connected fibres. (EGA also
identifies `Y' = Spec_Y f_* 𝒪_X` and shows the fibres of `g` are geometrically connected.) Proved as
`AlgebraicGeometry.steinFactorizationStatement` (`SGA.Foundations.Cohomology.SteinFactorization`),
with `Y'` the relative normalization of `Y` in `X`. -/
def SteinFactorizationStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y],
    ∃ (Y' : Scheme.{u}) (g : X ⟶ Y') (h : Y' ⟶ Y), IsProper g ∧ IsFinite h ∧ g ≫ h = f ∧
      (∀ V : Y'.Opens, IsIso (g.app V)) ∧ ∀ y : Y', ConnectedSpace (g.fiber y)

section Existence

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) (I : Ideal A)

/-- The `n`-th infinitesimal neighbourhood `X_n = X ×_{Spec A} Spec (A / I^{n+1})` of the fibre of
`f : X ⟶ Spec A` over `V(I)`. -/
noncomputable def thickening (n : ℕ) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))

/-- The closed immersion `X_n ⟶ X`. -/
noncomputable def thickening.ι (n : ℕ) : thickening f I n ⟶ X :=
  pullback.fst _ _

/-- The transition morphism `X_n ⟶ X_{n+1}`. -/
noncomputable def thickening.transition (n : ℕ) : thickening f I n ⟶ thickening f I (n + 1) :=
  pullback.map _ _ _ _ (𝟙 X)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
    (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp]
      rfl)

lemma thickening.transition_ι (n : ℕ) :
    thickening.transition f I n ≫ thickening.ι f I (n + 1) = thickening.ι f I n := by
  simp only [thickening.transition, thickening.ι, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

/-- `ι_n^* F ≅ j_n^* ι_{n+1}^* F`. -/
noncomputable def thickening.pullbackIso (n : ℕ) (F : X.Modules) :
    (Scheme.Modules.pullback (thickening.ι f I n)).obj F ≅
      (Scheme.Modules.pullback (thickening.transition f I n)).obj
        ((Scheme.Modules.pullback (thickening.ι f I (n + 1))).obj F) :=
  ((Scheme.Modules.pullbackCongr (thickening.transition_ι f I n)).app F).symm ≪≫
    ((Scheme.Modules.pullbackComp _ _).app F).symm

end Existence

/-- **Grothendieck's existence theorem** (EGA III 5.1.4; Stacks Tag 088C), statement only. Let
`A` be a noetherian ring, complete for the `I`-adic topology, `f : X ⟶ Spec A` proper and
`X_n = X ×_A A/I^{n+1}`. Then `F ↦ (F|_{X_n})_n` is an equivalence between coherent `𝒪_X`-modules
and compatible systems of coherent `𝒪_{X_n}`-modules:
* (fully faithful) every compatible family of morphisms `F|_{X_n} ⟶ G|_{X_n}` comes from a unique
  morphism `F ⟶ G`;
* (essentially surjective) every compatible system `(G_n, G_{n+1}|_{X_n} ≅ G_n)` of coherent
  modules is isomorphic, compatibly, to `(F|_{X_n})_n` for a coherent `F`.

The first half is proved as `AlgebraicGeometry.grothendieckExistence_fullyFaithful`
(`SGA.Foundations.Cohomology.ExistenceFullyFaithful`). -/
def GrothendieckExistenceStatement : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f],
    (∀ (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
      (u : ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).obj F ⟶
        (Scheme.Modules.pullback (thickening.ι f I n)).obj G),
      (∀ n, u n = (thickening.pullbackIso f I n F).hom ≫
        (Scheme.Modules.pullback (thickening.transition f I n)).map (u (n + 1)) ≫
          (thickening.pullbackIso f I n G).inv) →
      ∃! u₀ : F ⟶ G, ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).map u₀ = u n) ∧
    (∀ (G : ∀ n, (thickening f I n).Modules) [∀ n, (G n).IsCoherent]
      (e : ∀ n, (Scheme.Modules.pullback (thickening.transition f I n)).obj (G (n + 1)) ≅ G n),
      ∃ (F : X.Modules) (_ : F.IsCoherent)
        (g : ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).obj F ≅ G n),
        ∀ n, (g n).hom = (thickening.pullbackIso f I n F).hom ≫
          (Scheme.Modules.pullback (thickening.transition f I n)).map (g (n + 1)).hom ≫
            (e n).hom)

end AlgebraicGeometry
