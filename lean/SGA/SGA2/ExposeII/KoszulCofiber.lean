/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Module.Torsion.Basic
import SGA.SGA2.ExposeII.HomologyLinear

/-!
# SGA 2, Exposé II, Lemma 11: the scalar cofiber homology sequence

For a map of chain complexes `φ : F ⟶ G`, the projection from its actual
homotopy cofiber induces `H_(i+1)(Cone φ) → H_i(F)`. We prove exactness of
`H_(i+1)(G) → H_(i+1)(Cone φ) → H_i(F)` directly on cycle representatives,
and show that the projection is killed by `H_i(φ)` and is natural in squares.

For scalar endomorphisms, this gives the short exact sequence
`0 → H_(i+1)(K)/a → H_(i+1)(Cone(a)) → Ann(a, H_i(K)) → 0` used in the
induction in II.11. We also retain the exact middle sequence before taking
the quotient. Exactness and surjectivity are proved from the cofiber
differential; they are not assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]
variable {F G : ChainComplex (ModuleCat.{u} R) ℕ} (φ : F ⟶ G)

/-- The signed projection of the three terms computing cofiber homology to
the three terms computing homology one degree lower. -/
def cofiberProjectionSC (i : ℕ) :
    (homotopyCofiber φ).sc' (i + 2) (i + 1) i ⟶ F.sc' (i + 1) i (i - 1) where
  τ₁ := -homotopyCofiber.fstX φ (i + 2) (i + 1) (by simp)
  τ₂ := homotopyCofiber.fstX φ (i + 1) i (by simp)
  τ₃ := if hi : i = 0 then 0 else
    -homotopyCofiber.fstX φ i (i - 1) (by simpa using Nat.sub_add_cancel (by omega : 1 ≤ i))
  comm₁₂ := by
    change (-homotopyCofiber.fstX φ (i + 2) (i + 1) _) ≫ F.d (i + 1) i =
      homotopyCofiber.d φ (i + 2) (i + 1) ≫ homotopyCofiber.fstX φ (i + 1) i _
    simpa only [Preadditive.neg_comp] using
      (homotopyCofiber.d_fstX φ (i + 2) (i + 1) i (by simp) (by simp)).symm
  comm₂₃ := by
    change homotopyCofiber.fstX φ (i + 1) i _ ≫ F.d i (i - 1) =
      homotopyCofiber.d φ (i + 1) i ≫ _
    split_ifs with hi
    · subst i
      simp
    · rw [Preadditive.comp_neg, homotopyCofiber.d_fstX φ (i + 1) i (i - 1)
        (by simp) (by simpa using Nat.sub_add_cancel (by omega : 1 ≤ i)), neg_neg]

/-- The homology projection from a cofiber to the preceding source homology. -/
def cofiberHomologyProjection (i : ℕ) :
    (homotopyCofiber φ).homology (i + 1) ⟶ F.homology i :=
  ((homotopyCofiber φ).homologyIsoSc' (i + 2) (i + 1) i (by simp) (by simp)).hom ≫
    ShortComplex.homologyMap (cofiberProjectionSC φ i) ≫
      (F.homologyIsoSc' (i + 1) i (i - 1) (by simp) (by cases i <;> simp)).inv

@[reassoc]
theorem cofiberHomologyProjection_π_ι (i : ℕ) :
    (homotopyCofiber φ).homologyπ (i + 1) ≫ cofiberHomologyProjection φ i ≫
      F.homologyι i =
    (homotopyCofiber φ).iCycles (i + 1) ≫
      homotopyCofiber.fstX φ (i + 1) i (by simp) ≫ F.pOpcycles i := by
  simp only [cofiberHomologyProjection, Category.assoc,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    HomologicalComplex.homologyIsoSc'_inv_ι,
    ShortComplex.homologyι_naturality_assoc,
    ShortComplex.homology_π_ι_assoc]
  simp [cofiberProjectionSC]

@[reassoc (attr := simp)]
theorem cofiberHomologyInr_projection (i : ℕ) :
    homologyMap (homotopyCofiber.inr φ) (i + 1) ≫ cofiberHomologyProjection φ i = 0 := by
  apply (cancel_mono (F.homologyι i)).mp
  apply (cancel_epi (G.homologyπ (i + 1))).mp
  simp only [Category.assoc]
  rw [homologyπ_naturality_assoc, cofiberHomologyProjection_π_ι]
  simp only [← Category.assoc, HomologicalComplex.cyclesMap_i]
  simp [Category.assoc]

@[reassoc (attr := simp)]
theorem cofiberHomologyProjection_map (i : ℕ) :
    cofiberHomologyProjection φ i ≫ homologyMap φ i = 0 := by
  apply (cancel_mono (G.homologyι i)).mp
  apply (cancel_epi ((homotopyCofiber φ).homologyπ (i + 1))).mp
  simp only [Category.assoc, homologyι_naturality, zero_comp, comp_zero]
  rw [cofiberHomologyProjection_π_ι_assoc]
  simp only [p_opcyclesMap]
  have h := congrArg (fun t => (homotopyCofiber φ).iCycles (i + 1) ≫ t ≫ G.pOpcycles i)
    (homotopyCofiber.d_sndX φ (i + 1) i (by simp))
  simpa only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
    d_pOpcycles, comp_zero, add_zero, ← homotopyCofiber_d, iCycles_d_assoc, zero_comp] using h.symm

private def chainCycle (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (x : K.X i) (hx : K.d i (i - 1) x = 0) : K.cycles i :=
  (K.sc i).moduleCatCyclesIso.inv ⟨x, by
    change K.d i ((ComplexShape.down ℕ).next i) x = 0
    have hi : (ComplexShape.down ℕ).next i = i - 1 := by cases i <;> simp
    rw [hi]
    exact hx⟩

@[simp]
private theorem chainCycle_i (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (x : K.X i) (hx : K.d i (i - 1) x = 0) :
    K.iCycles i (chainCycle K i x hx) = x := by
  exact ConcreteCategory.congr_hom (K.sc i).moduleCatCyclesIso_inv_iCycles ⟨x, _⟩

private theorem chainHomologyπ_eq_zero_iff (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (i : ℕ) (x : K.cycles i) :
    K.homologyπ i x = 0 ↔ ∃ y : K.X (i + 1), K.d (i + 1) i y = K.iCycles i x := by
  have heq := ConcreteCategory.congr_hom (K.homology_π_ι i) x
  change K.homologyι i (K.homologyπ i x) = K.pOpcycles i (K.iCycles i x) at heq
  have hinj := (ModuleCat.mono_iff_injective (K.homologyι i)).mp inferInstance
  have hp := (K.sc i).moduleCat_pOpcycles_eq_zero_iff (K.iCycles i x)
  change K.pOpcycles i (K.iCycles i x) = 0 ↔
    ∃ y : K.X ((ComplexShape.down ℕ).prev i),
      K.d ((ComplexShape.down ℕ).prev i) i y = K.iCycles i x at hp
  have hi : (ComplexShape.down ℕ).prev i = i + 1 := by simp
  rw [hi] at hp
  rw [← heq] at hp
  exact ((map_eq_zero_iff (K.homologyι i).hom hinj).symm).trans hp

private theorem chainHomologyπ_eq_iff (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (i : ℕ) (x y : K.cycles i) :
    K.homologyπ i x = K.homologyπ i y ↔
      ∃ z : K.X (i + 1), K.d (i + 1) i z = K.iCycles i x - K.iCycles i y := by
  rw [← sub_eq_zero, ← map_sub, chainHomologyπ_eq_zero_iff]
  simp only [map_sub]

private theorem cofiber_decomposition (i : ℕ) :
    homotopyCofiber.fstX φ (i + 1) i (by simp) ≫
      homotopyCofiber.inlX φ i (i + 1) (by simp) +
    homotopyCofiber.sndX φ (i + 1) ≫ homotopyCofiber.inrX φ (i + 1) = 𝟙 _ := by
  apply homotopyCofiber.ext_from_X φ i (i + 1) (by simp)
  · simp
  · simp

/-- The cofiber homology sequence is exact at its middle homology term. -/
theorem cofiberHomology_exact (i : ℕ) :
    (ShortComplex.mk (homologyMap (homotopyCofiber.inr φ) (i + 1))
      (cofiberHomologyProjection φ i) (cofiberHomologyInr_projection φ i)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((homotopyCofiber φ).homologyπ (i + 1))).mp inferInstance x
  let u := (homotopyCofiber φ).iCycles (i + 1) z
  have hproj : F.pOpcycles i (homotopyCofiber.fstX φ (i + 1) i (by simp) u) = 0 := by
    have h := ConcreteCategory.congr_hom (cofiberHomologyProjection_π_ι φ i) z
    change F.homologyι i (cofiberHomologyProjection φ i
      ((homotopyCofiber φ).homologyπ (i + 1) z)) = _ at h
    rw [hx, map_zero] at h
    exact h.symm
  have hb := (F.sc i).moduleCat_pOpcycles_eq_zero_iff
    (homotopyCofiber.fstX φ (i + 1) i (by simp) u)
  change _ ↔ ∃ y : F.X ((ComplexShape.down ℕ).prev i),
    F.d ((ComplexShape.down ℕ).prev i) i y = _ at hb
  have hi : (ComplexShape.down ℕ).prev i = i + 1 := by simp
  rw [hi] at hb
  obtain ⟨y, hy⟩ := hb.mp hproj
  let b := homotopyCofiber.inlX φ (i + 1) (i + 2) (by simp) y
  let u' := u + (homotopyCofiber φ).d (i + 2) (i + 1) b
  have hu : (homotopyCofiber φ).d (i + 1) i u = 0 := by
    exact ConcreteCategory.congr_hom ((homotopyCofiber φ).iCycles_d (i + 1) i) z
  have hu' : (homotopyCofiber φ).d (i + 1) i u' = 0 := by
    dsimp only [u']
    rw [map_add, hu, zero_add]
    exact ConcreteCategory.congr_hom ((homotopyCofiber φ).d_comp_d _ _ _) b
  have hf : homotopyCofiber.fstX φ (i + 1) i (by simp) u' = 0 := by
    have hd := ConcreteCategory.congr_hom
      (homotopyCofiber.d_fstX φ (i + 2) (i + 1) i (by simp) (by simp)) b
    change homotopyCofiber.fstX φ (i + 1) i _
      ((homotopyCofiber φ).d (i + 2) (i + 1) b) = _ at hd
    dsimp only [u']
    rw [map_add, hd]
    simp [b, ← ModuleCat.comp_apply, ← hy]
  let w := homotopyCofiber.sndX φ (i + 1) u'
  have hw : G.d (i + 1) i w = 0 := by
    have hd := ConcreteCategory.congr_hom
      (homotopyCofiber.d_sndX φ (i + 1) i (by simp)) u'
    change homotopyCofiber.sndX φ i ((homotopyCofiber φ).d (i + 1) i u') =
      φ.f i (homotopyCofiber.fstX φ (i + 1) i _ u') + G.d (i + 1) i w at hd
    simpa only [hu', hf, map_zero, zero_add] using hd.symm
  let z' := chainCycle G (i + 1) w (by simpa using hw)
  refine ⟨G.homologyπ (i + 1) z', ?_⟩
  have hn := ConcreteCategory.congr_hom
    (homologyπ_naturality (homotopyCofiber.inr φ) (i + 1)) z'
  change homologyMap (homotopyCofiber.inr φ) (i + 1) (G.homologyπ (i + 1) z') = _ at hn
  rw [hn]
  apply (chainHomologyπ_eq_iff (homotopyCofiber φ) (i + 1) _ z).mpr
  refine ⟨b, ?_⟩
  have hv := ConcreteCategory.congr_hom
    (cyclesMap_i (homotopyCofiber.inr φ) (i + 1)) z'
  change (homotopyCofiber φ).iCycles (i + 1)
    (cyclesMap (homotopyCofiber.inr φ) (i + 1) z') =
      homotopyCofiber.inrX φ (i + 1) (G.iCycles (i + 1) z') at hv
  change (homotopyCofiber φ).d (i + 2) (i + 1) b =
    (homotopyCofiber φ).iCycles (i + 1)
      (cyclesMap (homotopyCofiber.inr φ) (i + 1) z') - (homotopyCofiber φ).iCycles (i + 1) z
  rw [hv, chainCycle_i]
  have hd := ConcreteCategory.congr_hom (cofiber_decomposition φ i) u'
  change homotopyCofiber.inlX φ i (i + 1) _
    (homotopyCofiber.fstX φ (i + 1) i _ u') + homotopyCofiber.inrX φ (i + 1) w = u' at hd
  rw [hf, map_zero, zero_add] at hd
  rw [hd]
  dsimp only [u', u]
  abel

/-- The cofiber projection is natural in a commutative square. Its target
map is induced by the left side of the square. -/
@[reassoc]
theorem cofiberHomologyProjection_naturality
    {F' G' : ChainComplex (ModuleCat.{u} R) ℕ} (φ' : F' ⟶ G')
    (α : Arrow.mk φ ⟶ Arrow.mk φ')
    (hc : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j) (i : ℕ) :
    homologyMap (homotopyCofiber.mapArrowHom φ φ' hc α) (i + 1) ≫
      cofiberHomologyProjection φ' i =
    cofiberHomologyProjection φ i ≫ homologyMap α.left i := by
  have hf : (homotopyCofiber.mapArrowHom φ φ' hc α).f (i + 1) ≫
      homotopyCofiber.fstX φ' (i + 1) i rfl =
      homotopyCofiber.fstX φ (i + 1) i rfl ≫ α.left.f i := by
    simp [homotopyCofiber.mapArrowHom,
      homotopyCofiber.desc_f φ _ _ (i + 1) i rfl,
      homotopyCofiber.inrCompHomotopy_hom φ' _ i (i + 1) rfl]
  apply (cancel_mono (F'.homologyι i)).mp
  apply (cancel_epi ((homotopyCofiber φ).homologyπ (i + 1))).mp
  simp only [Category.assoc]
  have hι : homologyMap α.left i ≫ F'.homologyι i =
      F.homologyι i ≫ opcyclesMap α.left i := homologyι_naturality α.left i
  have hp : F.pOpcycles i ≫ opcyclesMap α.left i = α.left.f i ≫ F'.pOpcycles i :=
    p_opcyclesMap α.left i
  rw [homologyπ_naturality_assoc, cofiberHomologyProjection_π_ι,
    hι, cofiberHomologyProjection_π_ι_assoc, hp]
  rw [← Category.assoc, cyclesMap_i]
  simp only [Category.assoc, reassoc_of% hf]

variable (K : ChainComplex (ModuleCat.{u} R) ℕ) (a : R)

/-- In the scalar cofiber sequence the homology projection lands in the
annihilator of the scalar on preceding homology. -/
def scalarCofiberHomologyProjection (i : ℕ) :
    (homotopyCofiber (a • 𝟙 K)).homology (i + 1) ⟶
      ModuleCat.of R (Submodule.torsionBy R (K.homology i) a) :=
  ModuleCat.ofHom ((cofiberHomologyProjection (a • 𝟙 K) i).hom.codRestrict _ (fun x => by
    have h := ConcreteCategory.congr_hom (cofiberHomologyProjection_map (a • 𝟙 K) i) x
    simpa [ModuleCat.comp_apply] using h))

@[reassoc (attr := simp)]
theorem scalarCofiberHomologyProjection_subtype (i : ℕ) :
    scalarCofiberHomologyProjection K a i ≫
      ModuleCat.ofHom (Submodule.torsionBy R (K.homology i) a).subtype =
      cofiberHomologyProjection (a • 𝟙 K) i := rfl

@[reassoc (attr := simp)]
theorem scalarCofiberHomologyInr_projection (i : ℕ) :
    homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1) ≫
      scalarCofiberHomologyProjection K a i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (cofiberHomologyInr_projection (a • 𝟙 K) i) x

/-- The exact middle sequence required in the induction in II.11:
`H_(i+1)(K) → H_(i+1)(Cone(a)) → Ann(a, H_i(K))`. -/
theorem scalarCofiberHomology_exact (i : ℕ) :
    (ShortComplex.mk (homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1))
      (scalarCofiberHomologyProjection K a i)
      (scalarCofiberHomologyInr_projection K a i)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have h := (ShortComplex.moduleCat_exact_iff _).mp
    (cofiberHomology_exact (a • 𝟙 K) i)
  exact h x (congrArg Subtype.val hx)

/-- Every scalar-annihilated homology class lifts to a class in the scalar cofiber. -/
theorem scalarCofiberHomologyProjection_surjective (i : ℕ) :
    Function.Surjective (scalarCofiberHomologyProjection K a i) := by
  intro x
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x.val
  have haz : K.homologyπ i (a • z) = 0 := by
    rw [map_smul, hz]
    exact x.property
  obtain ⟨v, hv⟩ := (chainHomologyπ_eq_zero_iff K i (a • z)).mp haz
  let u := K.iCycles i z
  have hu : K.d i (i - 1) u = 0 :=
    ConcreteCategory.congr_hom (K.iCycles_d i (i - 1)) z
  have hav : K.d (i + 1) i v = a • u := by simpa only [map_smul] using hv
  let φ : K ⟶ K := a • 𝟙 K
  let c := homotopyCofiber.inlX φ i (i + 1) (by simp) u -
    homotopyCofiber.inrX φ (i + 1) v
  have hl : (homotopyCofiber φ).d (i + 1) i
      (homotopyCofiber.inlX φ i (i + 1) (by simp) u) =
      homotopyCofiber.inrX φ i (a • u) := by
    by_cases hi : i = 0
    · subst i
      have h := ConcreteCategory.congr_hom
        (homotopyCofiber.inlX_d' φ 1 0 (by simp) (by simp)) u
      simpa [ModuleCat.comp_apply, φ] using h
    · have h := ConcreteCategory.congr_hom
        (homotopyCofiber.inlX_d φ (i + 1) i (i - 1) (by simp)
          (by simpa using Nat.sub_add_cancel (by omega : 1 ≤ i))) u
      simpa [ModuleCat.comp_apply, hu, φ] using h
  have hc : (homotopyCofiber φ).d (i + 1) i c = 0 := by
    dsimp only [c]
    rw [map_sub, hl]
    have hr := ConcreteCategory.congr_hom (homotopyCofiber.inrX_d φ (i + 1) i) v
    change (homotopyCofiber φ).d (i + 1) i (homotopyCofiber.inrX φ (i + 1) v) =
      homotopyCofiber.inrX φ i (K.d (i + 1) i v) at hr
    rw [hr, hav, sub_self]
  let z' := chainCycle (homotopyCofiber φ) (i + 1) c (by simpa using hc)
  refine ⟨(homotopyCofiber φ).homologyπ (i + 1) z', ?_⟩
  apply Subtype.ext
  change cofiberHomologyProjection φ i ((homotopyCofiber φ).homologyπ (i + 1) z') = x.val
  apply (ModuleCat.mono_iff_injective (K.homologyι i)).mp inferInstance
  have hp := ConcreteCategory.congr_hom (cofiberHomologyProjection_π_ι φ i) z'
  change K.homologyι i (cofiberHomologyProjection φ i
      ((homotopyCofiber φ).homologyπ (i + 1) z')) =
    K.pOpcycles i (homotopyCofiber.fstX φ (i + 1) i _
      ((homotopyCofiber φ).iCycles (i + 1) z')) at hp
  rw [hp, chainCycle_i]
  have hf : homotopyCofiber.fstX φ (i + 1) i (by simp) c = u := by
    simp [c, ← ModuleCat.comp_apply]
  rw [hf, ← hz]
  exact (ConcreteCategory.congr_hom (K.homology_π_ι i) z).symm

instance scalarCofiberHomologyProjection_epi (i : ℕ) :
    Epi (scalarCofiberHomologyProjection K a i) :=
  (ModuleCat.epi_iff_surjective _).mpr (scalarCofiberHomologyProjection_surjective K a i)

@[reassoc (attr := simp)]
theorem cofiberHomologyMap_inr (i : ℕ) :
    homologyMap φ i ≫ homologyMap (homotopyCofiber.inr φ) i = 0 := by
  rw [← homologyMap_comp]
  simpa using (homotopyCofiber.inrCompHomotopy φ (fun j => ⟨j + 1, rfl⟩)).homologyMap_eq i

/-- The cofiber homology sequence is exact at the homology of its unshifted target. -/
theorem cofiberHomology_left_exact (i : ℕ) :
    (ShortComplex.mk (homologyMap φ i) (homologyMap (homotopyCofiber.inr φ) i)
      (cofiberHomologyMap_inr φ i)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (G.homologyπ i)).mp inferInstance x
  have hn := ConcreteCategory.congr_hom (homologyπ_naturality (homotopyCofiber.inr φ) i) z
  change homologyMap (homotopyCofiber.inr φ) i (G.homologyπ i z) =
    (homotopyCofiber φ).homologyπ i (cyclesMap (homotopyCofiber.inr φ) i z) at hn
  have hz : (homotopyCofiber φ).homologyπ i (cyclesMap (homotopyCofiber.inr φ) i z) = 0 :=
    hn.symm.trans hx
  obtain ⟨b, hb⟩ := (chainHomologyπ_eq_zero_iff (homotopyCofiber φ) i _).mp hz
  have hi := ConcreteCategory.congr_hom (cyclesMap_i (homotopyCofiber.inr φ) i) z
  change (homotopyCofiber φ).iCycles i (cyclesMap (homotopyCofiber.inr φ) i z) =
    homotopyCofiber.inrX φ i (G.iCycles i z) at hi
  rw [hi] at hb
  let v := homotopyCofiber.fstX φ (i + 1) i (by simp) b
  have hv : F.d i (i - 1) v = 0 := by
    by_cases h : i = 0
    · subst i
      simp
    · have hd := ConcreteCategory.congr_hom
        (homotopyCofiber.d_fstX φ (i + 1) i (i - 1) (by simp)
          (by simpa using Nat.sub_add_cancel (by omega : 1 ≤ i))) b
      change homotopyCofiber.fstX φ i (i - 1) _ ((homotopyCofiber φ).d (i + 1) i b) =
        -(F.d i (i - 1) v) at hd
      rw [hb] at hd
      have hrel : (ComplexShape.down ℕ).Rel i (i - 1) := by
        simpa using Nat.sub_add_cancel (by omega : 1 ≤ i)
      have hh : homotopyCofiber.fstX φ i (i - 1) hrel
          (homotopyCofiber.inrX φ i (G.iCycles i z)) = 0 := by
        exact ConcreteCategory.congr_hom (homotopyCofiber.inrX_fstX φ i (i - 1) hrel)
          (G.iCycles i z)
      rw [hh] at hd
      exact neg_eq_zero.mp hd.symm
  let z' := chainCycle F i v hv
  refine ⟨F.homologyπ i z', ?_⟩
  have hm := ConcreteCategory.congr_hom (homologyπ_naturality φ i) z'
  change homologyMap φ i (F.homologyπ i z') = G.homologyπ i (cyclesMap φ i z') at hm
  rw [hm]
  apply (chainHomologyπ_eq_iff G i _ z).mpr
  refine ⟨-homotopyCofiber.sndX φ (i + 1) b, ?_⟩
  have hm' := ConcreteCategory.congr_hom (cyclesMap_i φ i) z'
  change G.iCycles i (cyclesMap φ i z') = φ.f i (F.iCycles i z') at hm'
  rw [hm', chainCycle_i]
  have hs := ConcreteCategory.congr_hom (homotopyCofiber.d_sndX φ (i + 1) i (by simp)) b
  change homotopyCofiber.sndX φ i ((homotopyCofiber φ).d (i + 1) i b) =
    φ.f i v + G.d (i + 1) i (homotopyCofiber.sndX φ (i + 1) b) at hs
  rw [hb] at hs
  have hh : homotopyCofiber.sndX φ i (homotopyCofiber.inrX φ i (G.iCycles i z)) =
      G.iCycles i z :=
    ConcreteCategory.congr_hom (homotopyCofiber.inrX_sndX φ i) (G.iCycles i z)
  rw [hh] at hs
  rw [map_neg, hs]
  abel

private theorem scalarCofiberHomologyMap_inr (i : ℕ) :
    (a • 𝟙 (K.homology (i + 1))) ≫
      homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1) = 0 := by
  simpa only [homologyMap_smul, homologyMap_id] using
    cofiberHomologyMap_inr (a • 𝟙 K) (i + 1)

/-- The inclusion of target homology factors through its quotient by the scalar. -/
def scalarCofiberHomologyCokernelInr (i : ℕ) :
    cokernel (a • 𝟙 (K.homology (i + 1))) ⟶
      (homotopyCofiber (a • 𝟙 K)).homology (i + 1) :=
  cokernel.desc _ (homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1))
    (scalarCofiberHomologyMap_inr K a i)

@[reassoc (attr := simp)]
theorem scalarCofiberHomologyCokernelInr_π (i : ℕ) :
    cokernel.π (a • 𝟙 (K.homology (i + 1))) ≫ scalarCofiberHomologyCokernelInr K a i =
      homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1) := by
  simp [scalarCofiberHomologyCokernelInr]

instance scalarCofiberHomologyCokernelInr_mono (i : ℕ) :
    Mono (scalarCofiberHomologyCokernelInr K a i) := by
  have h : (ShortComplex.mk (a • 𝟙 (K.homology (i + 1)))
      (homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1))
      (scalarCofiberHomologyMap_inr K a i)).Exact := by
    simpa only [homologyMap_smul, homologyMap_id] using
      cofiberHomology_left_exact (a • 𝟙 K) (i + 1)
  exact h.mono_cokernelDesc

private theorem scalarCofiberHomologyCokernelInr_projection (i : ℕ) :
    scalarCofiberHomologyCokernelInr K a i ≫ scalarCofiberHomologyProjection K a i = 0 := by
  apply (cancel_epi (cokernel.π (a • 𝟙 (K.homology (i + 1))))).mp
  simp

/-- The quotient/annihilator sequence in II.11, with the quotient expressed
as the categorical cokernel of scalar multiplication. -/
def scalarCofiberHomologyShortComplex (i : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (scalarCofiberHomologyCokernelInr K a i)
    (scalarCofiberHomologyProjection K a i)
    (scalarCofiberHomologyCokernelInr_projection K a i)

/-- II.11's scalar cofiber sequence is short exact:
`0 → H_(i+1)(K)/a → H_(i+1)(Cone(a)) → Ann(a,H_i(K)) → 0`. -/
theorem scalarCofiberHomologyShortComplex_shortExact (i : ℕ) :
    (scalarCofiberHomologyShortComplex K a i).ShortExact := by
  refine { exact := ?_
           mono_f := scalarCofiberHomologyCokernelInr_mono K a i
           epi_g := scalarCofiberHomologyProjection_epi K a i }
  let S := ShortComplex.mk (homologyMap (homotopyCofiber.inr (a • 𝟙 K)) (i + 1))
    (scalarCofiberHomologyProjection K a i) (scalarCofiberHomologyInr_projection K a i)
  let α : S ⟶ scalarCofiberHomologyShortComplex K a i :=
    { τ₁ := cokernel.π (a • 𝟙 (K.homology (i + 1)))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, scalarCofiberHomologyShortComplex]
      comm₂₃ := by simp [S, scalarCofiberHomologyShortComplex] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
    (scalarCofiberHomology_exact K a i)

end SGA.SGA2.ExposeII
