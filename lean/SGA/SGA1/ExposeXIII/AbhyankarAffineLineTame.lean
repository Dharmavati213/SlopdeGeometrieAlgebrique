/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.AbhyankarAffineLineExpand

/-!
# XIII.2.13, case A: geometric points fixed by `π₁` of an extension (towards Abhyankar's lemma)

First step of the local half of Abhyankar's lemma at `∞` (`AbhyankarLemmaAtInfinityStatement`).
Base change of finite étale algebras along a ring homomorphism `f : R → S` (`bcRingHom`)
induces `π₁(S, ω) → π₁(R, ω ∘ f)` (`ExposeV.autMap` with `bcFiberIso`). A geometric point of a
finite étale `R`-algebra `A` which factors through `ω : S → Ω` (via an `R`-algebra map
`A → S`) is fixed by the image of `π₁(S, ω)` (`AffineLinePGroups.autMap_bcFiberIso_fiberPoint`):
the corresponding point of `S ⊗_R A` factors through the terminal covering `S`.

The fibre functors are given by ring homomorphisms (`AffineLinePGroups.fiberOfRingHom`, points
`AffineLinePGroups.fiberPoint`), because in the application `R` and `S` are the same ring
`LaurentSeries k` (`S = k((w)) ⊇ R = k((y))`, `y = wᵐ`, `LaurentSeries.expand k m`) with two
different structures, so that instance arguments would clash.

Not yet here (plan in `notes/now/xiii213.md`): the local lemma itself, i.e. for `|G| ∣ m` and a
continuous `ψ : π₁(k((y))) → G`, the image of `π₁(k((w))) → π₁(k((y))) → G` is a `p`-group.
-/

universe u

open CategoryTheory CommAlgCat

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

section RingHom

variable {R S : Type u} [CommRing R] [CommRing S] {Ω : Type u} [Field Ω]

/-- The fibre functor of finite étale `R`-algebras at a geometric point given by a ring
homomorphism `ω : R → Ω` (`ExposeV.fiberFunctor` for `ω.toAlgebra`). -/
noncomputable abbrev fiberOfRingHom (ω : R →+* Ω) : (FiniteEtale.{u} R)ᵒᵖ ⥤ FintypeCat.{u} :=
  letI := ω.toAlgebra
  ExposeV.fiberFunctor R Ω

/-- The fibre of a base change along `f : R → S` at `ω : S → Ω` is the fibre at `ω ∘ f`
(`FiniteEtale.fiberIsoBaseChangeFiber`). -/
noncomputable def bcFiberIso (f : R →+* S) (ω : S →+* Ω) :
    (bcRingHom f).op ⋙ fiberOfRingHom ω ≅ fiberOfRingHom (ω.comp f) :=
  letI := f.toAlgebra
  letI := ω.toAlgebra
  letI := (ω.comp f).toAlgebra
  haveI : IsScalarTower R S Ω := IsScalarTower.of_algebraMap_eq' rfl
  (FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S).symm

/-- The point of the fibre at `ω` given by a ring homomorphism `x : A → Ω` over `ω`. -/
noncomputable def fiberPoint (ω : R →+* Ω) (A : FiniteEtale.{u} R) (x : A →+* Ω)
    (hx : x.comp (algebraMap R A) = ω) : (fiberOfRingHom ω).obj (Opposite.op A) :=
  letI := ω.toAlgebra
  ({ x with commutes' := fun r ↦ congrArg (· r) hx } : A →ₐ[R] Ω)

/-- Every point of the fibre at `ω` is a `fiberPoint`. -/
lemma exists_eq_fiberPoint (ω : R →+* Ω) (A : FiniteEtale.{u} R)
    (y : (fiberOfRingHom ω).obj (Opposite.op A)) :
    ∃ (x : A →+* Ω) (hx : x.comp (algebraMap R A) = ω), y = fiberPoint ω A x hx := by
  let := ω.toAlgebra
  let y' : A →ₐ[R] Ω := y
  exact ⟨y'.toRingHom, RingHom.ext fun r ↦ y'.commutes r, rfl⟩

/-- A geometric point of `A` over `ω ∘ f` which factors through `ω : S → Ω` (through an
`R`-algebra map `x₀ : A → S`) is fixed by the image of `π₁(S, ω) → π₁(R, ω ∘ f)`: the
corresponding point of `S ⊗_R A` factors through the terminal covering `S`. -/
theorem autMap_bcFiberIso_fiberPoint (f : R →+* S) (ω : S →+* Ω) (A : FiniteEtale.{u} R)
    (x₀ : A →+* S) (hx₀ : x₀.comp (algebraMap R A) = f) (τ : Aut (fiberOfRingHom ω)) :
    (ExposeV.autMap (bcRingHom f).op (bcFiberIso f ω) τ).hom.app (Opposite.op A)
        (fiberPoint (ω.comp f) A (ω.comp x₀) (by rw [RingHom.comp_assoc, hx₀])) =
      fiberPoint (ω.comp f) A (ω.comp x₀) (by rw [RingHom.comp_assoc, hx₀]) := by
  let := f.toAlgebra
  let := ω.toAlgebra
  let := (ω.comp f).toAlgebra
  have : IsScalarTower R S Ω := IsScalarTower.of_algebraMap_eq' rfl
  let e := FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S
  set x := fiberPoint (ω.comp f) A (ω.comp x₀) (by rw [RingHom.comp_assoc, hx₀])
  -- the `S`-algebra map `S ⊗_R A → S` induced by `x₀`
  let x₀' : A →ₐ[R] S := { x₀ with commutes' := fun r ↦ congrArg (· r) hx₀ }
  let μ : TensorProduct R S A →ₐ[S] S := Algebra.TensorProduct.lift (AlgHom.id S S) x₀'
    fun _ _ ↦ Commute.all _ _
  let μ' : (FiniteEtale.baseChange.{u} R S).obj A ⟶ FiniteEtale.of S S :=
    ObjectProperty.homMk (CommAlgCat.ofHom μ)
  let pt : (ExposeV.fiberFunctor S Ω).obj (Opposite.op (FiniteEtale.of S S)) := Algebra.ofId S Ω
  have hpt : e.hom.app (Opposite.op A) x = (ExposeV.fiberFunctor S Ω).map μ'.op pt := by
    apply Algebra.TensorProduct.ext'
    intro s a
    change Algebra.TensorProduct.lift (Algebra.ofId S Ω) _ (fun _ _ ↦ Commute.all _ _) (s ⊗ₜ a) =
      Algebra.ofId S Ω (Algebra.TensorProduct.lift (AlgHom.id S S) x₀'
        (fun _ _ ↦ Commute.all _ _) (s ⊗ₜ a))
    refine (Algebra.TensorProduct.lift_tmul (Algebra.ofId S Ω) (show A →ₐ[R] Ω from x)
      (fun _ _ ↦ Commute.all _ _) s a).trans ?_
    rw [Algebra.TensorProduct.lift_tmul, map_mul]
    rfl
  have hsub : ∀ a b : (ExposeV.fiberFunctor S Ω).obj (Opposite.op (FiniteEtale.of S S)), a = b :=
    fun a b ↦ Subsingleton.elim (α := S →ₐ[S] Ω) a b
  change e.inv.app (Opposite.op A) (τ.hom.app _ (e.hom.app (Opposite.op A) x)) = x
  rw [hpt, FunctorToFintypeCat.naturality, hsub (τ.hom.app _ pt) pt, ← hpt]
  exact FintypeCat.hom_inv_id_apply (e.app (Opposite.op A)) x

end RingHom

end SGA.SGA1.ExposeXIII.AffineLinePGroups
