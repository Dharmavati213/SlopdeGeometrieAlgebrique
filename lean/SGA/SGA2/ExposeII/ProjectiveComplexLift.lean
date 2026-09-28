/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou,
  SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# SGA 2, Exposé II, (7.6): lifting an augmented projective complex

An augmentation from a termwise projective nonnegative chain complex to `X`
lifts to any projective resolution of `X`. Two maps into that resolution which
induce the same augmentation are homotopic. The source complex need not be
exact. This is the comparison construction required when a Koszul complex
maps to a projective resolution of its zeroth homology.

The degreewise induction is the one used for projective-resolution comparison
in mathlib, with source exactness removed from the hypotheses.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace SGA.SGA2.ExposeII

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)]
variable {X : C} (a : K ⟶ (ChainComplex.single₀ C).obj X) (Q : ProjectiveResolution X)

omit [∀ n, Projective (K.X n)] in
private theorem augmentation_d_zero : K.d 1 0 ≫ a.f 0 = 0 := by
  rw [← a.comm]
  simp

private def liftToResolutionZero : K.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (a.f 0) (Q.π.f 0)

private def liftToResolutionOne : K.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (K.d 1 0 ≫ liftToResolutionZero K a Q) (by
    simp [liftToResolutionZero, augmentation_d_zero])

@[simp]
private theorem liftToResolutionOne_comm :
    liftToResolutionOne K a Q ≫ Q.complex.d 1 0 = K.d 1 0 ≫ liftToResolutionZero K a Q :=
  Q.exact₀.liftFromProjective_comp _ _

private def liftToResolutionSucc (n : ℕ)
    (g : K.X n ⟶ Q.complex.X n) (g' : K.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = K.d (n + 1) n ≫ g) :
    Σ' g'' : K.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = K.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective (K.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- Any augmented complex of projective objects maps to a resolution of
the augmentation target; exactness of the source is not required. -/
def liftToResolution : K ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftToResolutionZero K a Q) (liftToResolutionOne K a Q)
    (liftToResolutionOne_comm K a Q) fun n ⟨g, g', w⟩ =>
      ⟨(liftToResolutionSucc K Q n g g' w).1, (liftToResolutionSucc K Q n g g' w).2⟩

/-- The comparison map lifts the given augmentation. -/
@[reassoc (attr := simp)]
theorem liftToResolution_commutes : liftToResolution K a Q ≫ Q.π = a := by
  ext
  simp [liftToResolution, liftToResolutionZero, liftToResolutionOne]

variable {K Q}

private def homotopyToResolutionZeroZero
    (f : K ⟶ Q.complex) (comm : f ≫ Q.π = 0) : K.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
private theorem homotopyToResolutionZeroZero_comp
    (f : K ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    homotopyToResolutionZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

private def homotopyToResolutionZeroOne
    (f : K ⟶ Q.complex) (comm : f ≫ Q.π = 0) : K.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - K.d 1 0 ≫ homotopyToResolutionZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
      homotopyToResolutionZeroZero_comp, sub_self])

@[reassoc (attr := simp)]
private theorem homotopyToResolutionZeroOne_comp
    (f : K ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    homotopyToResolutionZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - K.d 1 0 ≫ homotopyToResolutionZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

private def homotopyToResolutionZeroSucc (f : K ⟶ Q.complex) (n : ℕ)
    (g : K.X n ⟶ Q.complex.X (n + 1)) (g' : K.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = K.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    K.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - K.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]
private theorem homotopyToResolutionZeroSucc_comp (f : K ⟶ Q.complex) (n : ℕ)
    (g : K.X n ⟶ Q.complex.X (n + 1)) (g' : K.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = K.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    homotopyToResolutionZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - K.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- A chain map from a termwise projective complex to a resolution is
null-homotopic if its augmentation vanishes. -/
def homotopyToResolutionZero (f : K ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (homotopyToResolutionZeroZero f comm) (by simp)
    (homotopyToResolutionZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
      ⟨homotopyToResolutionZeroSucc f n g g' w, by simp⟩

variable (K Q)

/-- Comparison maps from a projective complex into a resolution are unique
up to homotopy once their augmentation is fixed. -/
def homotopyToResolutionOfAugmentationEq (g h : K ⟶ Q.complex)
    (comm : g ≫ Q.π = h ≫ Q.π) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (homotopyToResolutionZero _ (by simp [comm]))

end SGA.SGA2.ExposeII
