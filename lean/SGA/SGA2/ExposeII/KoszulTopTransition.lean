/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulTopCohomology

/-!
# The original Koszul transition in top degree

We compute the actual transition between the Koszul complexes of powers,
using the ordered top generator of `koszulTopIso`. Under the original top
cohomology quotient isomorphism, the original stable Koszul diagram sends
`[y]` at exponent `r` to `[(∏ f ∈ fs, f^s) • y]` at exponent `r+s`.
This is the parameter-power transition calculation in Exposé IV.5.5.

The calculation needs neither regularity nor noetherian hypotheses. The
monomial-shift formula is proved as an equality of classes; it does not
assert that those classes form a basis or construct the residue pairing.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The existing ordered top-term identification, with the length of a
power list written as the length of the original list. -/
def koszulPowerTopIso (M : ModuleCat.{u} R) (fs : List R) (n : ℕ) :
    (koszulPowerComplex M fs n).X fs.length ≅ M :=
  (koszulPowerComplex M fs n).XIsoOfEq (List.length_map ..).symm ≪≫
    koszulTopIso M (fs.map (fun f => f ^ n))

theorem koszulPowerTopIso_cons (M : ModuleCat.{u} R) (f : R) (fs : List R) (n : ℕ) :
    (koszulPowerTopIso M (f :: fs) n).hom =
      homotopyCofiber.fstX (f ^ n • 𝟙 (koszulPowerComplex M fs n))
        (fs.length + 1) fs.length rfl ≫ (koszulPowerTopIso M fs n).hom := by
  have aux (g : R) (gs : List R) (i : ℕ) (hi : gs.length = i) :
      ((koszulComplex M (g :: gs)).XIsoOfEq (congrArg (· + 1) hi).symm).hom ≫
        (koszulTopIso M (g :: gs)).hom =
      homotopyCofiber.fstX (g • 𝟙 (koszulComplex M gs)) (i + 1) i rfl ≫
        ((koszulComplex M gs).XIsoOfEq hi.symm).hom ≫ (koszulTopIso M gs).hom := by
    subst i
    simp only [XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    rfl
  exact aux (f ^ n) (fs.map (fun f => f ^ n)) fs.length (List.length_map ..)

/-- On the actual ordered top term, the original transition is multiplication
by the product of the differences of powers. -/
@[reassoc]
theorem koszulTransition_top (M : ModuleCat.{u} R) (fs : List R)
    {n m : ℕ} (hnm : n ≤ m) :
    (koszulTransition M fs hnm).f fs.length ≫ (koszulPowerTopIso M fs n).hom =
      (fs.map (fun f => f ^ (m - n))).prod • (koszulPowerTopIso M fs m).hom := by
  induction fs with
  | nil => simp only [koszulTransition_nil, List.length_nil, HomologicalComplex.id_f,
      Category.id_comp, List.map_nil, List.prod_nil, one_smul]; rfl
  | cons f fs ih =>
    rw [koszulPowerTopIso_cons, koszulPowerTopIso_cons]
    change (koszulTransition M (f :: fs) hnm).f (fs.length + 1) ≫ _ = _
    rw [koszulTransition_cons, homotopyCofiber_mapArrowHom_fstX_assoc]
    change _ ≫ (f ^ (m - n) • (koszulTransition M fs hnm).f fs.length) ≫ _ = _
    rw [Linear.smul_comp, ih]
    simp only [List.map_cons, List.prod_cons, Linear.comp_smul, smul_smul]

/-- Evaluation on the ordered top generator after the genuine transition
multiplies top Hom by the same product. -/
theorem koszulTransition_top_hom (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m)
    (g : (koszulPowerComplex (ModuleCat.of R R) fs n).X fs.length ⟶ E) :
    ((koszulTransition (ModuleCat.of R R) fs hnm).f fs.length ≫ g)
        ((koszulPowerTopIso (ModuleCat.of R R) fs m).inv 1) =
      (fs.map (fun f => f ^ (m - n))).prod •
        g ((koszulPowerTopIso (ModuleCat.of R R) fs n).inv 1) := by
  have h := koszulTransition_top (ModuleCat.of R R) fs hnm
  have h' := congrArg (fun t => (koszulPowerTopIso (ModuleCat.of R R) fs m).inv ≫
    t ≫ (koszulPowerTopIso (ModuleCat.of R R) fs n).inv ≫ g) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Linear.smul_comp,
    Linear.comp_smul, Iso.inv_hom_id_assoc] at h'
  exact congrArg (fun t => t 1) h'

/-- The canonical projection from a term with zero outgoing differential
to its cohomology, using the original opcycles and homology maps. -/
def zeroOutgoingCohomologyProjection (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (i : ℕ) (h : C.d i (i + 1) = 0) : C.X i ⟶ C.homology i :=
  C.pOpcycles i ≫ (C.isoHomologyι i (i + 1) (by simp) h).inv

instance zeroOutgoingCohomologyProjection_epi
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) (h : C.d i (i + 1) = 0) :
    Epi (zeroOutgoingCohomologyProjection C i h) := by
  unfold zeroOutgoingCohomologyProjection
  infer_instance

@[reassoc]
theorem zeroOutgoingCohomologyProjection_naturality
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D) (i : ℕ)
    (hC : C.d i (i + 1) = 0) (hD : D.d i (i + 1) = 0) :
    zeroOutgoingCohomologyProjection C i hC ≫ homologyMap φ i =
      φ.f i ≫ zeroOutgoingCohomologyProjection D i hD := by
  have := D.isIso_homologyι i (i + 1) (by simp) hD
  apply (cancel_mono (D.homologyι i)).mp
  simp only [zeroOutgoingCohomologyProjection, Category.assoc,
    homologyι_naturality, isoHomologyι_inv_hom_id_assoc,
    isoHomologyι_inv_hom_id, Category.comp_id, p_opcyclesMap]

/-- The existing top cohomology isomorphism sends the cohomology class of
a top cochain to its value on the ordered top generator modulo the ideal. -/
@[reassoc]
theorem koszulTopCohomologyProjection_comp_iso (fs : List R) (E : ModuleCat.{u} R) :
    zeroOutgoingCohomologyProjection
        ((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E) fs.length
        (koszulTopCochain_d_eq_zero fs E) ≫ (koszulTopCohomologyIsoQuotient fs E).hom =
      ModuleCat.ofHom (((koszulIdeal fs • (⊤ : Submodule R E)).mkQ).comp
        (koszulTopHomEquiv fs E).toLinearMap) := by
  unfold zeroOutgoingCohomologyProjection koszulTopCohomologyIsoQuotient
  simp only [Iso.trans_hom, Category.assoc, ShortComplex.asIsoHomologyι_hom,
    homologyIsoSc'_hom_ι_assoc, isoHomologyι_inv_hom_id_assoc,
    pOpcycles_opcyclesIsoSc'_hom_assoc,
    ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_assoc]
  ext g
  rfl

/-- The existing top Hom equivalence for a power list, with its length
normalized to the length of the original list. -/
def koszulPowerTopHomEquiv (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    ((koszulPowerComplex (ModuleCat.of R R) fs n).X fs.length ⟶ E) ≃ₗ[R] E :=
  (Linear.homCongr R (koszulPowerTopIso (ModuleCat.of R R) fs n) (Iso.refl E)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R E))

/-- The original top cohomology quotient identification; only its degree
index is rewritten using `List.length_map`. -/
def koszulPowerTopCohomologyIsoQuotient (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    koszulCohomology (fs.map (fun f => f ^ n)) E fs.length ≅
      ModuleCat.of R (E ⧸ koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)) :=
  eqToIso (congrArg (koszulCohomology (fs.map (fun f => f ^ n)) E)
    (List.length_map ..).symm) ≪≫
      koszulTopCohomologyIsoQuotient (fs.map (fun f => f ^ n)) E

theorem koszulPowerTopCochain_d_eq_zero (fs : List R) (E : ModuleCat.{u} R) (n : ℕ) :
    ((koszulPowerComplex (ModuleCat.of R R) fs n).linearYonedaObj R E).d
      fs.length (fs.length + 1) = 0 := by
  have hK := koszulComplex_isZero_X (ModuleCat.of R R) (fs.map (fun f => f ^ n))
    (fs.length + 1) (by simp)
  exact (((linearYoneda R (ModuleCat.{u} R)).obj E).map_isZero hK.op).eq_of_tgt _ 0

/-- The class of a top cochain under the original power-list comparison
is its evaluation modulo the power-generated ideal. -/
@[reassoc]
theorem koszulPowerTopCohomologyProjection_comp_iso (fs : List R)
    (E : ModuleCat.{u} R) (n : ℕ) :
    zeroOutgoingCohomologyProjection
        ((koszulPowerComplex (ModuleCat.of R R) fs n).linearYonedaObj R E) fs.length
        (koszulPowerTopCochain_d_eq_zero fs E n) ≫
      (koszulPowerTopCohomologyIsoQuotient fs E n).hom =
      ModuleCat.ofHom (((koszulIdeal (fs.map (fun f => f ^ n)) •
        (⊤ : Submodule R E)).mkQ).comp (koszulPowerTopHomEquiv fs E n).toLinearMap) := by
  have aux (gs : List R) (i : ℕ) (hi : gs.length = i) :
      zeroOutgoingCohomologyProjection
          ((koszulComplex (ModuleCat.of R R) gs).linearYonedaObj R E) i
          (by subst i; exact koszulTopCochain_d_eq_zero gs E) ≫
        (eqToIso (congrArg (koszulCohomology gs E) hi.symm) ≪≫
          koszulTopCohomologyIsoQuotient gs E).hom =
        ModuleCat.ofHom (((koszulIdeal gs • (⊤ : Submodule R E)).mkQ).comp
          (((Linear.homCongr R
            (((koszulComplex (ModuleCat.of R R) gs).XIsoOfEq hi.symm) ≪≫
              koszulTopIso (ModuleCat.of R R) gs) (Iso.refl E)).trans
            (ModuleCat.homLinearEquiv.trans
              (LinearMap.ringLmapEquivSelf R R E))).toLinearMap)) := by
    subst i
    simpa only [eqToIso_refl, Iso.refl_trans, XIsoOfEq_rfl, koszulTopHomEquiv] using
      koszulTopCohomologyProjection_comp_iso gs E
  exact aux (fs.map (fun f => f ^ n)) fs.length (List.length_map ..)

/-- The actual Hom–Koszul cochain map, obtained by precomposing with the
already defined Koszul transition. -/
abbrev koszulHomTransition (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) :
    (koszulPowerComplex (ModuleCat.of R R) fs n).linearYonedaObj R E ⟶
      (koszulPowerComplex (ModuleCat.of R R) fs m).linearYonedaObj R E :=
  (homComplexFunctor (ComplexShape.down ℕ) E).map
    (koszulTransition (ModuleCat.of R R) fs hnm).op

/-- On top cochains, the actual Hom transition and the original top Hom
equivalences give multiplication by the product of the power differences. -/
theorem koszulHomTransition_top (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m)
    (g : (koszulPowerComplex (ModuleCat.of R R) fs n).X fs.length ⟶ E) :
    koszulPowerTopHomEquiv fs E m ((koszulHomTransition fs E hnm).f fs.length g) =
      (fs.map (fun f => f ^ (m - n))).prod • koszulPowerTopHomEquiv fs E n g :=
  koszulTransition_top_hom fs E hnm g

/-- The actual cohomology transition, expressed through the original top
Hom–Koszul quotient isomorphisms, multiplies a representative by the product
of the parameter-power differences. No regularity hypothesis is needed. -/
theorem koszulTopCohomology_transition_apply (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) (y : E) :
    (koszulPowerTopCohomologyIsoQuotient fs E m).hom
        (homologyMap (koszulHomTransition fs E hnm) fs.length
          ((koszulPowerTopCohomologyIsoQuotient fs E n).inv
            ((koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mkQ y))) =
      (koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)).mkQ
        ((fs.map (fun f => f ^ (m - n))).prod • y) := by
  let C := (koszulPowerComplex (ModuleCat.of R R) fs n).linearYonedaObj R E
  let D := (koszulPowerComplex (ModuleCat.of R R) fs m).linearYonedaObj R E
  let πn := zeroOutgoingCohomologyProjection C fs.length (koszulPowerTopCochain_d_eq_zero fs E n)
  let πm := zeroOutgoingCohomologyProjection D fs.length (koszulPowerTopCochain_d_eq_zero fs E m)
  let g := (koszulPowerTopHomEquiv fs E n).symm y
  have hg : koszulPowerTopHomEquiv fs E n g = y := LinearEquiv.apply_symm_apply _ _
  have hn : πn g = (koszulPowerTopCohomologyIsoQuotient fs E n).inv
      ((koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mkQ y) := by
    apply (ModuleCat.mono_iff_injective (koszulPowerTopCohomologyIsoQuotient fs E n).hom).mp
      inferInstance
    have he := congrArg (fun t => t g) (koszulPowerTopCohomologyProjection_comp_iso fs E n)
    change (koszulPowerTopCohomologyIsoQuotient fs E n).hom (πn g) =
      (koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R E)).mkQ
        (koszulPowerTopHomEquiv fs E n g) at he
    simpa only [hg, Iso.inv_hom_id_apply] using he
  rw [← hn]
  have hnat := congrArg (fun t => t g)
    (zeroOutgoingCohomologyProjection_naturality (koszulHomTransition fs E hnm) fs.length
      (koszulPowerTopCochain_d_eq_zero fs E n) (koszulPowerTopCochain_d_eq_zero fs E m))
  change homologyMap (koszulHomTransition fs E hnm) fs.length (πn g) =
    πm ((koszulHomTransition fs E hnm).f fs.length g) at hnat
  rw [hnat]
  have he := congrArg (fun t => t ((koszulHomTransition fs E hnm).f fs.length g))
    (koszulPowerTopCohomologyProjection_comp_iso fs E m)
  change (koszulPowerTopCohomologyIsoQuotient fs E m).hom
    (πm ((koszulHomTransition fs E hnm).f fs.length g)) =
      (koszulIdeal (fs.map (fun f => f ^ m)) • (⊤ : Submodule R E)).mkQ
        (koszulPowerTopHomEquiv fs E m ((koszulHomTransition fs E hnm).f fs.length g)) at he
  rw [he, koszulHomTransition_top, hg]

/-- The `r` to `r+s` transition of IV.5.5 is multiplication by
`∏ f ∈ fs, f^s`, on the actual top Koszul cohomology quotient. -/
theorem koszulTopCohomology_transition_add_apply (fs : List R) (E : ModuleCat.{u} R)
    (r s : ℕ) (y : E) :
    (koszulPowerTopCohomologyIsoQuotient fs E (r + s)).hom
        (homologyMap (koszulHomTransition fs E (Nat.le_add_right r s)) fs.length
          ((koszulPowerTopCohomologyIsoQuotient fs E r).inv
            ((koszulIdeal (fs.map (fun f => f ^ r)) • (⊤ : Submodule R E)).mkQ y))) =
      (koszulIdeal (fs.map (fun f => f ^ (r + s))) • (⊤ : Submodule R E)).mkQ
        ((fs.map (fun f => f ^ s)).prod • y) := by
  simpa only [Nat.add_sub_cancel_left] using
    koszulTopCohomology_transition_apply fs E (Nat.le_add_right r s) y

/-- The Hom–Koszul map used above is literally the map in the original
cohomology diagram defining stable Koszul cohomology. -/
theorem koszulCohomologyDiagram_map_eq_homologyMap (fs : List R) (E : ModuleCat.{u} R)
    {n m : ℕ} (hnm : n ≤ m) (i : ℕ) :
    (koszulCohomologyDiagram fs E i).map (homOfLE hnm).op.op =
      homologyMap (koszulHomTransition fs E hnm) i := rfl

/-- With ring coefficients, the original top quotient is the literal
quotient ring, with its original `R`-module structure. -/
def koszulPowerTopCohomologyRingIsoQuotient (fs : List R) (n : ℕ) :
    koszulCohomology (fs.map (fun f => f ^ n)) (ModuleCat.of R R) fs.length ≅
      ModuleCat.of R (R ⧸ koszulIdeal (fs.map (fun f => f ^ n))) :=
  eqToIso (congrArg (koszulCohomology (fs.map (fun f => f ^ n)) (ModuleCat.of R R))
    (List.length_map ..).symm) ≪≫
      koszulTopCohomologyRingIsoQuotient (fs.map (fun f => f ^ n))

theorem koszulPowerTopCohomologyRingIsoQuotient_eq (fs : List R) (n : ℕ) :
    koszulPowerTopCohomologyRingIsoQuotient fs n =
      koszulPowerTopCohomologyIsoQuotient fs (ModuleCat.of R R) n ≪≫
        (Submodule.quotEquivOfEq _ (koszulIdeal (fs.map (fun f => f ^ n)))
          (by simp only [Ideal.smul_eq_mul, Ideal.mul_top])).toModuleIso := by
  ext
  simp only [koszulPowerTopCohomologyRingIsoQuotient, koszulPowerTopCohomologyIsoQuotient,
    koszulTopCohomologyRingIsoQuotient, Iso.trans_hom, Category.assoc]

/-- The original stable Koszul diagram, under the original top quotient
identification with the actual quotient rings, has the product transition
specified in IV.5.5. -/
theorem koszulTopCohomologyRing_transition_apply (fs : List R)
    {n m : ℕ} (hnm : n ≤ m) (y : R) :
    (koszulPowerTopCohomologyRingIsoQuotient fs m).hom
        ((koszulCohomologyDiagram fs (ModuleCat.of R R) fs.length).map (homOfLE hnm).op.op
          ((koszulPowerTopCohomologyRingIsoQuotient fs n).inv
            (Ideal.Quotient.mk (koszulIdeal (fs.map (fun f => f ^ n))) y))) =
      Ideal.Quotient.mk (koszulIdeal (fs.map (fun f => f ^ m)))
        ((fs.map (fun f => f ^ (m - n))).prod * y) := by
  rw [koszulCohomologyDiagram_map_eq_homologyMap,
    koszulPowerTopCohomologyRingIsoQuotient_eq,
    koszulPowerTopCohomologyRingIsoQuotient_eq]
  change (Submodule.quotEquivOfEq _ _ (by simp only [Ideal.smul_eq_mul, Ideal.mul_top]))
    ((koszulPowerTopCohomologyIsoQuotient fs (ModuleCat.of R R) m).hom
      (homologyMap (koszulHomTransition fs (ModuleCat.of R R) hnm) fs.length
        ((koszulPowerTopCohomologyIsoQuotient fs (ModuleCat.of R R) n).inv
          ((koszulIdeal (fs.map (fun f => f ^ n)) • (⊤ : Submodule R R)).mkQ y)))) = _
  rw [koszulTopCohomology_transition_apply]
  rfl

/-- The source's `I_r → I_(r+s)` is multiplication by
`x₁^s ⋯ x_d^s`, using the genuine maps defining stable Koszul cohomology. -/
theorem koszulTopCohomologyRing_transition_add_apply (fs : List R)
    (r s : ℕ) (y : R) :
    (koszulPowerTopCohomologyRingIsoQuotient fs (r + s)).hom
        ((koszulCohomologyDiagram fs (ModuleCat.of R R) fs.length).map
          (homOfLE (Nat.le_add_right r s)).op.op
          ((koszulPowerTopCohomologyRingIsoQuotient fs r).inv
            (Ideal.Quotient.mk (koszulIdeal (fs.map (fun f => f ^ r))) y))) =
      Ideal.Quotient.mk (koszulIdeal (fs.map (fun f => f ^ (r + s))))
        ((fs.map (fun f => f ^ s)).prod * y) := by
  simpa only [Nat.add_sub_cancel_left] using
    koszulTopCohomologyRing_transition_apply fs (Nat.le_add_right r s) y

/-- For a monomial, the source's transition increases every exponent by
`s`. This is an equality of actual quotient classes, independent of any
monomial-basis assertion. -/
theorem koszulTopCohomologyRing_transition_monomial (xs : List (R × ℕ))
    (r s : ℕ) :
    (koszulPowerTopCohomologyRingIsoQuotient (xs.map Prod.fst) (r + s)).hom
        ((koszulCohomologyDiagram (xs.map Prod.fst) (ModuleCat.of R R)
          (xs.map Prod.fst).length).map (homOfLE (Nat.le_add_right r s)).op.op
          ((koszulPowerTopCohomologyRingIsoQuotient (xs.map Prod.fst) r).inv
            (Ideal.Quotient.mk (koszulIdeal ((xs.map Prod.fst).map (fun f => f ^ r)))
              ((xs.map (fun x => x.1 ^ x.2)).prod)))) =
      Ideal.Quotient.mk (koszulIdeal ((xs.map Prod.fst).map (fun f => f ^ (r + s))))
        ((xs.map (fun x => x.1 ^ (x.2 + s))).prod) := by
  rw [koszulTopCohomologyRing_transition_add_apply]
  congr 1
  simp only [List.map_map, pow_add, List.prod_map_mul]
  exact mul_comm _ _

end SGA.SGA2.ExposeII
