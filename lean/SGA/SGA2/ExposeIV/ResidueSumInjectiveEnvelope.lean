/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.EssentialModuleExtensions
import SGA.SGA2.ExposeIV.FiniteLengthHomDuality
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The injective envelope of the sum of all residue fields

There is exactly one summand for each maximal ideal. The actual injective
envelope has the expected Hom test at every residue field. Thus it produces
the nonlocal finite-length duality without an assumed dualizing coefficient.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open scoped DirectSum

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Every simple submodule of an essential extension lies in the original submodule. -/
theorem EssentialModuleMap.simple_range_le {M E S : ModuleCat.{u} R}
    {i : M ⟶ E} (hi : EssentialModuleMap i) [IsSimpleModule R S] (f : S ⟶ E) :
    LinearMap.range f.hom ≤ LinearMap.range i.hom := by
  by_cases hf : f.hom = 0
  · simp [hf]
  · have hfInj := LinearMap.injective_of_ne_zero hf
    have : IsSimpleModule R (LinearMap.range f.hom) :=
      IsSimpleModule.congr (LinearEquiv.ofInjective f.hom hfInj).symm
    have ha := IsSimpleModule.isAtom (R := R) (m := LinearMap.range f.hom)
    by_contra hn
    have hd := ha.not_le_iff_disjoint.mp hn
    exact ha.ne_bot ((essentialIn_iff_disjoint _ _).mp hi.2 |>.2 _ le_top hd.symm)

/-- An essential embedding induces an isomorphism on Hom from a simple module.
The forward map is the original postcomposition by that embedding. -/
def essentialSimpleHomIso {M E : ModuleCat.{u} R} (i : M ⟶ E)
    (hi : EssentialModuleMap i) (S : ModuleCat.{u} R) [IsSimpleModule R S] :
    (moduleHomDual M).obj (op S) ≅ (moduleHomDual E).obj (op S) := by
  let p := ((linearYoneda R (ModuleCat R)).map i).app (op S)
  have hp : Function.Bijective p.hom := by
    constructor
    · intro f g hfg
      apply ModuleCat.hom_ext
      ext x
      apply hi.1
      exact congrArg (fun t : S ⟶ E => t.hom x) hfg
    · intro f
      let g : S ⟶ M := ModuleCat.ofHom
        ((LinearEquiv.ofInjective i.hom hi.1).symm.toLinearMap.comp
          (f.hom.codRestrict (LinearMap.range i.hom) (fun x =>
            hi.simple_range_le f ⟨x, rfl⟩)))
      refine ⟨g, ?_⟩
      apply ModuleCat.hom_ext
      ext x
      exact congrArg Subtype.val ((LinearEquiv.ofInjective i.hom hi.1).apply_symm_apply
        ⟨f.hom x, hi.simple_range_le f ⟨x, rfl⟩⟩)
  exact (LinearEquiv.ofBijective p.hom hp).toModuleIso

/-- The actual collection of maximal ideals, with no finiteness assumption. -/
abbrev MaximalIdealIndex (R : Type u) [CommRing R] := {m : Ideal R // m.IsMaximal}

/-- One copy of each actual residue field. -/
abbrev residueFieldFamily (m : MaximalIdealIndex R) : ModuleCat.{u} R :=
  ModuleCat.of R (R ⧸ m.val)

instance residueFieldFamily_simple (m : MaximalIdealIndex R) :
    IsSimpleModule R (residueFieldFamily m) := by
  exact isSimpleModule_iff_quot_maximal.mpr ⟨m.val, m.property, ⟨LinearEquiv.refl _ _⟩⟩

/-- The direct sum of all actual residue fields. -/
abbrev allResidueFieldSum (R : Type u) [CommRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (⨁ m : MaximalIdealIndex R, residueFieldFamily m)

/-- Distinct residue fields have no nonzero original linear morphisms. -/
theorem residueFieldHom_eq_zero {m n : MaximalIdealIndex R} (hmn : m ≠ n)
    (f : residueFieldFamily m ⟶ residueFieldFamily n) : f = 0 := by
  apply ModuleCat.hom_ext
  by_contra hf
  let e := LinearEquiv.ofBijective f.hom (LinearMap.bijective_of_ne_zero hf)
  have heq := e.annihilator_eq
  change Module.annihilator R (R ⧸ m.val) = Module.annihilator R (R ⧸ n.val) at heq
  rw [Ideal.annihilator_quotient, Ideal.annihilator_quotient] at heq
  exact hmn (Subtype.ext heq)

/-- Hom from a residue field into the residue sum sees exactly its own summand. -/
def residueHomSumIso (m : MaximalIdealIndex R) :
    (moduleHomDual (allResidueFieldSum R)).obj (op (residueFieldFamily m)) ≅
      (moduleHomDual (residueFieldFamily m)).obj (op (residueFieldFamily m)) := by
  classical
  let π : allResidueFieldSum R ⟶ residueFieldFamily m :=
    ModuleCat.ofHom (DirectSum.component R (MaximalIdealIndex R) (fun j => residueFieldFamily j) m)
  let ι : residueFieldFamily m ⟶ allResidueFieldSum R :=
    ModuleCat.ofHom (DirectSum.lof R (MaximalIdealIndex R) (fun j => residueFieldFamily j) m)
  let p := ((linearYoneda R (ModuleCat R)).map π).app (op (residueFieldFamily m))
  have hp : Function.Bijective p.hom := by
    constructor
    · intro f g hfg
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro n
      by_cases hmn : m = n
      · subst n
        exact congrArg (fun t : residueFieldFamily m ⟶ residueFieldFamily m => t.hom x) hfg
      · let πn : allResidueFieldSum R ⟶ residueFieldFamily n :=
          ModuleCat.ofHom (DirectSum.component R (MaximalIdealIndex R)
            (fun j => residueFieldFamily j) n)
        have hf := congrArg (fun t : residueFieldFamily m ⟶ residueFieldFamily n => t.hom x)
          (residueFieldHom_eq_zero hmn (f ≫ πn))
        have hg := congrArg (fun t : residueFieldFamily m ⟶ residueFieldFamily n => t.hom x)
          (residueFieldHom_eq_zero hmn (g ≫ πn))
        exact hf.trans hg.symm
    · intro f
      refine ⟨f ≫ ι, ?_⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact DirectSum.component.lof_self (M := fun j : MaximalIdealIndex R =>
        (residueFieldFamily j : Type u)) R m (f.hom x)
  exact (LinearEquiv.ofBijective p.hom hp).toModuleIso

/-- Endomorphisms of the original residue field are scalars, by evaluation at one. -/
def residueEndIso (m : MaximalIdealIndex R) :
    (moduleHomDual (residueFieldFamily m)).obj (op (residueFieldFamily m)) ≅
      residueFieldFamily m := by
  let p : (moduleHomDual (residueFieldFamily m)).obj (op (residueFieldFamily m)) ⟶
      residueFieldFamily m := ModuleCat.ofHom
    { toFun f := f.hom 1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hp : Function.Bijective p.hom := by
    constructor
    · intro f g hfg
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hf := f.hom.map_smul r (1 : R ⧸ m.val)
      have hg := g.hom.map_smul r (1 : R ⧸ m.val)
      change f.hom 1 = g.hom 1 at hfg
      rw [hfg] at hf
      simpa [Algebra.smul_def] using hf.trans hg.symm
    · intro y
      refine ⟨ModuleCat.ofHom
        { toFun x := x * y
          map_add' _ _ := add_mul _ _ _
          map_smul' _ _ := smul_mul_assoc _ _ _ }, ?_⟩
      exact one_mul y
  exact (LinearEquiv.ofBijective p.hom hp).toModuleIso

/-- The genuine injective envelope of the sum, not a postulated representing object. -/
def allResidueFieldEnvelope (R : Type u) [CommRing R] :
    ModuleInjectiveEnvelope (allResidueFieldSum R) := moduleInjectiveEnvelope _

/-- The constructed coefficient satisfies the original test at every maximal ideal. -/
theorem allResidueFieldEnvelope_residueTests :
    moduleHomDualResidueTests (⊥ : Ideal R) (allResidueFieldEnvelope R).obj := by
  intro m hm _
  let j : MaximalIdealIndex R := ⟨m, hm⟩
  have : IsSimpleModule R (residueFieldFamily j) := residueFieldFamily_simple j
  exact ⟨(essentialSimpleHomIso (allResidueFieldEnvelope R).ι
    (allResidueFieldEnvelope R).essential (residueFieldFamily j)).symm ≪≫
      residueHomSumIso j ≪≫ residueEndIso j⟩

end SGA.SGA2.ExposeIV
