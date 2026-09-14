/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Noetherian.Basic
import SGA.SGA2.ExposeII.NoetherianHomology

/-!
# SGA 2, Exposé II, Lemma 11: finite Koszul complexes

The Koszul complex of a finite list is built recursively as the homotopy
cofiber of multiplication by its first element on the Koszul complex of the
remaining list. The empty list gives the coefficient module in degree zero.
The inverse transitions for powers multiply the shifted summand by the
appropriate power of the first element, together with the transitions for
the remaining list.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite HomologicalComplex

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Every natural degree has a predecessor in the chain-complex shape. -/
theorem chainShape_hasPredecessor (j : ℕ) :
    ∃ i : ℕ, (ComplexShape.down ℕ).Rel i j := ⟨j + 1, rfl⟩

section CofiberMaps

variable {F G F' G' : ChainComplex (ModuleCat.{u} R) ℕ}
  (φ : F ⟶ G) (φ' : F' ⟶ G') (α : Arrow.mk φ ⟶ Arrow.mk φ')

/-- Cofiber maps preserve the inclusion of the unshifted complex. -/
@[reassoc (attr := simp)]
theorem homotopyCofiber_inr_mapArrowHom :
    homotopyCofiber.inr φ ≫
      homotopyCofiber.mapArrowHom φ φ' chainShape_hasPredecessor α =
    α.right ≫ homotopyCofiber.inr φ' := by
  simp [homotopyCofiber.mapArrowHom]

/-- On the shifted summand, a cofiber map induces the left side of its square. -/
@[reassoc (attr := simp)]
theorem homotopyCofiber_mapArrowHom_fstX (i : ℕ) :
    (homotopyCofiber.mapArrowHom φ φ' chainShape_hasPredecessor α).f (i + 1) ≫
      homotopyCofiber.fstX φ' (i + 1) i rfl =
    homotopyCofiber.fstX φ (i + 1) i rfl ≫ α.left.f i := by
  simp [homotopyCofiber.mapArrowHom,
    homotopyCofiber.desc_f φ _ _ (i + 1) i rfl,
    homotopyCofiber.inrCompHomotopy_hom φ' _ i (i + 1) rfl]

end CofiberMaps

variable {K L P : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The square defining a transition between scalar cofibers. -/
def scalarPowerArrow (f : R) {n m : ℕ} (hnm : n ≤ m) (t : K ⟶ L) :
    Arrow.mk (f ^ m • 𝟙 K) ⟶ Arrow.mk (f ^ n • 𝟙 L) :=
  Arrow.homMk (f ^ (m - n) • t) t (by
    change (f ^ (m - n) • t) ≫ (f ^ n • 𝟙 L) = (f ^ m • 𝟙 K) ≫ t
    simp only [Linear.smul_comp, Linear.comp_smul, Category.comp_id,
      Category.id_comp, smul_smul, ← pow_add, Nat.add_sub_of_le hnm])

@[simp]
theorem scalarPowerArrow_self (f : R) (n : ℕ) :
    scalarPowerArrow f (le_refl n) (𝟙 K) = 𝟙 _ := by
  ext <;> simp [scalarPowerArrow]

/-- The scalar squares compose with the inverse-system transitions. -/
theorem scalarPowerArrow_comp (f : R) {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (t : K ⟶ L) (s : L ⟶ P) :
    scalarPowerArrow f hmk t ≫ scalarPowerArrow f hnm s =
      scalarPowerArrow f (hnm.trans hmk) (t ≫ s) := by
  have he : m - n + (k - m) = k - n := by omega
  ext
  · simp [scalarPowerArrow, Linear.smul_comp, Linear.comp_smul, smul_smul, ← pow_add, he]
  · rfl

variable (M : ModuleCat.{u} R)

/-- The Koszul chain complex of a finite list, with coefficients in `M`. -/
def koszulComplex : List R → ChainComplex (ModuleCat.{u} R) ℕ
  | [] => (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj M
  | f :: fs => homotopyCofiber (f • 𝟙 (koszulComplex fs))

/-- The Koszul complex on the powers of a fixed list of generators. -/
abbrev koszulPowerComplex (fs : List R) (n : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  koszulComplex M (fs.map fun f ↦ f ^ n)

/-- The actual chain map from exponent `m` to exponent `n`. -/
def koszulTransition : (fs : List R) → {n m : ℕ} → (hnm : n ≤ m) →
    koszulPowerComplex M fs m ⟶ koszulPowerComplex M fs n
  | [], _, _, _ => 𝟙 _
  | f :: fs, _, _, hnm =>
    homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor
      (scalarPowerArrow f hnm (koszulTransition fs hnm))

@[simp]
theorem koszulTransition_nil {n m : ℕ} (hnm : n ≤ m) :
    koszulTransition M [] hnm = 𝟙 _ := rfl

@[simp]
theorem koszulTransition_cons (f : R) (fs : List R) {n m : ℕ} (hnm : n ≤ m) :
    koszulTransition M (f :: fs) hnm =
      homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor
        (scalarPowerArrow f hnm (koszulTransition M fs hnm)) := rfl

@[simp]
theorem koszulTransition_self (fs : List R) (n : ℕ) :
    koszulTransition M fs (le_refl n) = 𝟙 _ := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [koszulTransition_cons, ih, scalarPowerArrow_self, homotopyCofiber.mapArrowHom_id]
    rfl

/-- The Koszul power transitions compose as inverse-system maps. -/
theorem koszulTransition_comp (fs : List R) {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    koszulTransition M fs hmk ≫ koszulTransition M fs hnm =
      koszulTransition M fs (hnm.trans hmk) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [koszulTransition_cons, ← homotopyCofiber.mapArrowHom_comp,
      scalarPowerArrow_comp, ih]

/-- The inverse system of genuine Koszul complexes used in II.11. -/
def koszulSystem (fs : List R) : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj n := koszulPowerComplex M fs n.unop
  map h := koszulTransition M fs (leOfHom h.unop)
  map_id n := koszulTransition_self M fs n.unop
  map_comp h k := (koszulTransition_comp M fs (leOfHom k.unop) (leOfHom h.unop)).symm

/-- The inverse system of degree-`i` Koszul homology modules in II.11. -/
def koszulHomologySystem (fs : List R) (i : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  koszulSystem M fs ⋙ HomologicalComplex.homologyFunctor _ _ i

/-- A Koszul complex has zero terms above the number of generators. -/
theorem koszulComplex_isZero_X (fs : List R) (i : ℕ) (hi : fs.length < i) :
    IsZero ((koszulComplex M fs).X i) := by
  induction fs generalizing i with
  | nil => exact HomologicalComplex.isZero_single_obj_X _ 0 M i (by simpa using hi.ne')
  | cons f fs ih =>
    change IsZero (homotopyCofiber.X (f • 𝟙 (koszulComplex M fs)) i)
    apply homotopyCofiber.isZero_X
    · exact ih i (by simpa using Nat.lt_of_succ_lt hi)
    · intro j hj
      apply ih j
      simp only [ComplexShape.down_Rel] at hj
      simp only [List.length_cons] at hi
      omega

/-- A Koszul complex has no homology above the number of generators. -/
theorem koszulComplex_isZero_homology (fs : List R) (i : ℕ) (hi : fs.length < i) :
    IsZero ((koszulComplex M fs).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (koszulComplex_isZero_X M fs i hi)

/-- Koszul complexes with noetherian coefficients have noetherian terms. -/
instance koszulComplex_X_isNoetherian [IsNoetherian R M] (fs : List R) (i : ℕ) :
    IsNoetherian R ((koszulComplex M fs).X i) := by
  induction fs generalizing i with
  | nil =>
    cases i with
    | zero =>
      exact isNoetherian_of_linearEquiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 M).symm.toLinearEquiv
    | succ i =>
      have := ModuleCat.subsingleton_of_isZero (koszulComplex_isZero_X M [] (i + 1) (by simp))
      exact isNoetherian_of_finite R _
  | cons f fs ih =>
    cases i with
    | zero =>
      have := ih 0
      exact isNoetherian_of_linearEquiv
        (homotopyCofiber.XIso (f • 𝟙 (koszulComplex M fs)) 0 (by simp)).symm.toLinearEquiv
    | succ i =>
      have := ih i
      have := ih (i + 1)
      exact isNoetherian_of_linearEquiv
        ((homotopyCofiber.XIsoBiprod (f • 𝟙 (koszulComplex M fs)) (i + 1) i rfl) ≪≫
          ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv

/-- The Koszul homology modules used as coefficients in II.11 are noetherian. -/
instance koszulComplex_homology_isNoetherian [IsNoetherian R M] (fs : List R) (i : ℕ) :
    IsNoetherian R ((koszulComplex M fs).homology i) :=
  isNoetherian_homology _ _

end SGA.SGA2.ExposeII
