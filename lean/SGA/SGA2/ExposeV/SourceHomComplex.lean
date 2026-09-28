/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# V.1: the displayed Hom-complex differential and its signs

On the original graded families of morphisms, the displayed source
differential is `h d_F + (-1)^(n+1) d_G h`. It differs from Mathlib's
differential by `(-1)^(n+1)` in degree `n`. We construct that actual complex,
prove its square-zero and Leibniz identities, and give an explicit chain
isomorphism to Mathlib's Hom complex. The isomorphism multiplies degree `n`
by `(-1)^(n(n+1)/2)` and is the identity in degree zero.

In particular, precomposition by an augmentation lands in the displayed
single-source Hom complex, whose differential has the same degree-dependent
sign. It does not land without a sign correction in the unsigned ordinary
Hom complex, as the source's subsequent augmentation calculation suggests.
-/

noncomputable section
universe v u
open CategoryTheory Limits Preadditive CochainComplex
open CochainComplex.HomComplex

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F G K : CochainComplex C ℤ}

/-- The literal displayed differential of V.1 on the original cochains. -/
def sourceHomδ (n m : ℤ) (z : Cochain F G n) : Cochain F G m :=
  m.negOnePow • δ n m z

/-- The displayed formula, with its actual component morphisms. -/
theorem sourceHomδ_v (n : ℤ) (z : Cochain F G n) (p q : ℤ)
    (hpq : p + (n + 1) = q) :
    (sourceHomδ n (n + 1) z).v p q hpq =
      F.d p (p + 1) ≫ z.v (p + 1) q (by omega) +
        (n + 1).negOnePow • (z.v p (q - 1) (by omega) ≫ G.d (q - 1) q) := by
  rw [sourceHomδ, Cochain.units_smul_v, δ_v n (n + 1) rfl z p q hpq
    (q - 1) (p + 1) rfl rfl, smul_add, smul_smul]
  simp only [Int.units_mul_self, one_smul]
  exact add_comm _ _

@[simp]
theorem sourceHomδ_add (n m : ℤ) (z w : Cochain F G n) :
    sourceHomδ n m (z + w) = sourceHomδ n m z + sourceHomδ n m w := by
  simp [sourceHomδ, smul_add]

@[simp]
theorem sourceHomδ_smul (n m : ℤ) (a : ℤ) (z : Cochain F G n) :
    sourceHomδ n m (a • z) = a • sourceHomδ n m z := by
  simp only [sourceHomδ, δ_smul]
  exact smul_comm _ _ _

@[simp]
theorem sourceHomδ_units_smul (n m : ℤ) (a : ℤˣ) (z : Cochain F G n) :
    sourceHomδ n m (a • z) = a • sourceHomδ n m z := by
  simp only [sourceHomδ, δ_units_smul]
  exact smul_comm _ _ _

@[simp]
theorem sourceHomδ_zero (n m : ℤ) : sourceHomδ n m (0 : Cochain F G n) = 0 := by
  simp [sourceHomδ]

/-- No differential occurs outside successive degrees. -/
theorem sourceHomδ_shape (n m : ℤ) (h : ¬ n + 1 = m) (z : Cochain F G n) :
    sourceHomδ n m z = 0 := by simp [sourceHomδ, δ_shape n m h]

/-- The literal source differential squares to zero. -/
@[simp]
theorem sourceHomδ_squared (n m k : ℤ) (z : Cochain F G n) :
    sourceHomδ m k (sourceHomδ n m z) = 0 := by
  simp [sourceHomδ, δ_δ]

/-- The source differential as an actual additive map. -/
def sourceHomδ_hom (F G : CochainComplex C ℤ) (n m : ℤ) :
    Cochain F G n →+ Cochain F G m where
  toFun := sourceHomδ n m
  map_zero' := sourceHomδ_zero n m
  map_add' := sourceHomδ_add n m

/-- **V.1.1:** the Hom complex with the displayed source differential. -/
def sourceHomComplex (F G : CochainComplex C ℤ) : CochainComplex AddCommGrpCat ℤ where
  X n := AddCommGrpCat.of (Cochain F G n)
  d n m := AddCommGrpCat.ofHom (sourceHomδ_hom F G n m)
  shape n m h := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (sourceHomδ_shape n m h)
  d_comp_d' n m k _ _ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (sourceHomδ_squared n m k)

/-- The explicit sign change from the source to Mathlib convention. -/
def sourceHomSign (n : ℤ) : ℤˣ := (n * (n + 1) / 2).negOnePow

@[simp]
theorem sourceHomSign_zero : sourceHomSign 0 = 1 := by norm_num [sourceHomSign]

/-- The degreewise sign recurrence, valid for negative degrees as well. -/
theorem sourceHomSign_succ (n : ℤ) :
    sourceHomSign (n + 1) = sourceHomSign n * (n + 1).negOnePow := by
  unfold sourceHomSign
  have heq : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [heq, Int.add_mul_ediv_right, Int.negOnePow_add]
  norm_num

/-- The normalization sign under addition of arbitrary integer degrees. -/
theorem sourceHomSign_add (i j : ℤ) :
    sourceHomSign (i + j) = sourceHomSign i * sourceHomSign j * (i * j).negOnePow := by
  have heq : (i + j) * (i + j + 1) = i * (i + 1) + j * (j + 1) + i * j * 2 := by
    ring
  unfold sourceHomSign
  rw [heq, Int.add_mul_ediv_right,
    Int.add_ediv_of_dvd_left (Int.two_dvd_mul_add_one i), Int.negOnePow_add,
    Int.negOnePow_add]
  norm_num

/-- On the original cochain composition the change of convention contributes
the Koszul factor `(-1)^(ij)`. In particular, normalizing each factor alone
does not silently identify the two product conventions. -/
theorem sourceHomSign_smul_comp {i j : ℤ} (z : Cochain F G i) (w : Cochain G K j) :
    sourceHomSign (i + j) • z.comp w rfl =
      (i * j).negOnePow • (sourceHomSign i • z).comp (sourceHomSign j • w) rfl := by
  simp only [sourceHomSign_add, Cochain.units_smul_comp, Cochain.comp_units_smul,
    smul_smul]
  congr 1
  ac_rfl

/-- Multiplication by the sign in a fixed degree, as an actual isomorphism. -/
def sourceHomDegreeIso (F G : CochainComplex C ℤ) (n : ℤ) :
    (sourceHomComplex F G).X n ≅ (CochainComplex.HomComplex F G).X n :=
  (LinearEquiv.smulOfUnit (M := Cochain F G n) (sourceHomSign n)).toAddEquiv.toAddCommGrpIso

/-- The explicit chain isomorphism between the two Hom-complex conventions. -/
def sourceHomComplexIso (F G : CochainComplex C ℤ) :
    sourceHomComplex F G ≅ CochainComplex.HomComplex F G :=
  HomologicalComplex.Hom.isoOfComponents (sourceHomDegreeIso F G) (by
    intro n m h
    have hm : n + 1 = m := h
    subst m
    ext z
    change δ n (n + 1) ((sourceHomSign n) • z) =
      (sourceHomSign (n + 1)) • sourceHomδ n (n + 1) z
    simp only [sourceHomδ, sourceHomSign_succ, smul_smul, mul_assoc,
      Int.units_mul_self, mul_one]
    exact δ_units_smul n (n + 1) (sourceHomSign n) z)

/-- The actual Hom-complex homology agrees with the original standard
cohomology classes through the specified degreewise sign correction. -/
def sourceHomologyAddEquiv (F G : CochainComplex C ℤ) (n : ℤ) :
    (sourceHomComplex F G).homology n ≃+ CohomologyClass F G n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n).mapIso
    (sourceHomComplexIso F G)).addCommGroupIsoToAddEquiv.trans
      (CochainComplex.HomComplex.homologyAddEquiv F G n)

/-- The source and standard differentials have exactly the same cocycles. -/
theorem sourceHomδ_eq_zero_iff (n m : ℤ) (z : Cochain F G n) :
    sourceHomδ n m z = 0 ↔ δ n m z = 0 :=
  smul_eq_zero_iff_eq m.negOnePow

/-- They also have the same actual coboundaries, with a corrected primitive. -/
theorem exists_sourceHomδ_eq_iff (n m : ℤ) (z : Cochain F G m) :
    (∃ w : Cochain F G n, sourceHomδ n m w = z) ↔
      ∃ w : Cochain F G n, δ n m w = z := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨m.negOnePow • w, by simpa [sourceHomδ] using hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨m.negOnePow • w, by simp [sourceHomδ, smul_smul, hw]⟩

/-- The actual Leibniz identity for the displayed source convention.
The sign is attached to the degree of the first composed cochain. -/
theorem sourceHomδ_comp {i j : ℤ} (z : Cochain F G i) (w : Cochain G K j) :
    sourceHomδ (i + j) (i + j + 1) (z.comp w rfl) =
      (sourceHomδ i (i + 1) z).comp w (by omega) +
        i.negOnePow • z.comp (sourceHomδ j (j + 1) w) (by omega) := by
  have ha : (i + j + 1).negOnePow = i.negOnePow * (j + 1).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    omega
  have hb : (i + j + 1).negOnePow * j.negOnePow = (i + 1).negOnePow := by
    rw [show i + j + 1 = (i + 1) + j by omega, Int.negOnePow_add, mul_assoc,
      Int.units_mul_self, mul_one]
  simp only [sourceHomδ, δ_comp z w rfl (i + 1) (j + 1) (i + j + 1) rfl rfl rfl,
    smul_add, Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  rw [hb, ha]
  exact add_comm _ _

/-- Composition of actual source cocycles is a source cocycle. -/
theorem sourceHomδ_comp_eq_zero {i j : ℤ} (z : Cochain F G i) (w : Cochain G K j)
    (hz : sourceHomδ i (i + 1) z = 0) (hw : sourceHomδ j (j + 1) w = 0) :
    sourceHomδ (i + j) (i + j + 1) (z.comp w rfl) = 0 := by
  simp [sourceHomδ_comp, hz, hw]

/-- Postcomposing a coboundary with a cocycle has the original composite
primitive, with no sign inserted. -/
theorem sourceHomδ_comp_cocycle {i j : ℤ} (z : Cochain F G i) (w : Cochain G K j)
    (hw : sourceHomδ j (j + 1) w = 0) :
    sourceHomδ (i + j) (i + j + 1) (z.comp w rfl) =
      (sourceHomδ i (i + 1) z).comp w (by omega) := by
  simp [sourceHomδ_comp, hw]

/-- Precomposing a coboundary with a cocycle has the sign prescribed
by the displayed differential, exhibited on its actual primitive. -/
theorem sourceHomδ_cocycle_comp {i j : ℤ} (z : Cochain F G i) (w : Cochain G K j)
    (hz : sourceHomδ i (i + 1) z = 0) :
    sourceHomδ (i + j) (i + j + 1) (i.negOnePow • z.comp w rfl) =
      z.comp (sourceHomδ j (j + 1) w) (by omega) := by
  simp [sourceHomδ_comp, hz, smul_smul]

/-- **V.1.2:** the source differential of an actual homotopy is the
difference of the original complex morphisms. -/
theorem sourceHomδ_ofHomotopy {f g : F ⟶ G} (h : Homotopy f g) :
    sourceHomδ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom f - Cochain.ofHom g := by
  simp [sourceHomδ, δ_ofHomotopy]

/-- The source differential on a cochain from a single object has the
displayed degree-dependent sign, even though the source differential is zero. -/
theorem sourceHomδ_fromSingleMk [HasZeroObject C] {X : C} {p q n : ℤ} (f : X ⟶ G.X q)
    (h : p + n = q) (q' : ℤ) (hq : q + 1 = q') :
    sourceHomδ n (n + 1) (Cochain.fromSingleMk f h) =
      (n + 1).negOnePow • Cochain.fromSingleMk (f ≫ G.d q q') (by omega) := by
  rw [sourceHomδ, Cochain.δ_fromSingleMk f h (n + 1) q' (by omega)]

end SGA.SGA2.ExposeV
