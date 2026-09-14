/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomologicalRegularParameter
import SGA.SGA2.ExposeV.RegularParameterResidueRetract
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# The homological regularity criterion and prime localizations

A noetherian local ring is regular if its residue field has finite
projective dimension. The proof constructs a regular first parameter,
lowers the residue-field bound over its actual quotient, and lifts the
quotient's minimal generators. Applying the criterion to the already proved
localized residue-field bound shows that every prime localization of a
regular local ring is regular, without assuming this as an extra hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Lifting minimal generators through a principal quotient requires
at most one additional generator, namely the original quotient element. -/
theorem maximalIdeal_spanFinrank_le_quotient_add_one (x : R)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
  let A := R ⧸ Ideal.span {x}
  let q : R →+* A := Ideal.Quotient.mk _
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q hq
  let g : A → R := Function.surjInv hq
  have hg (a : A) : q (g a) = a := Function.surjInv_eq hq a
  let t := (maximalIdeal A).generators
  let J : Ideal R := Ideal.span (insert x (g '' t))
  have hker : RingHom.ker q ≤ J := by
    rw [show RingHom.ker q = Ideal.span {x} from Ideal.mk_ker]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hmap : J.map q = maximalIdeal A := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_image]
    have himage : (fun a ↦ q (g a)) '' t = t := by simp only [hg, Set.image_id']
    rw [himage, show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton x)), Ideal.span_insert,
      Ideal.span_singleton_zero, bot_sup_eq]
    exact (maximalIdeal A).span_generators
  have hJ : J = maximalIdeal R := by
    have h := congrArg (Ideal.comap q) hmap
    rw [Ideal.comap_map_of_surjective q hq, maximalIdeal_comap q] at h
    exact (sup_of_le_left hker).symm.trans h
  rw [← hJ]
  have ht : t.Finite := Submodule.FG.finite_generators (maximalIdeal A).fg_of_isNoetherianRing
  exact (Submodule.spanFinrank_span_le_ncard_of_finite ((ht.image g).insert x)).trans
    ((Set.ncard_insert_le x (g '' t)).trans ((Nat.add_le_add_right
      (Set.ncard_image_le ht) 1).trans_eq
        (congrArg (· + 1) (Submodule.FG.generators_ncard
          (maximalIdeal A).fg_of_isNoetherianRing))))

/-- Regularity lifts from the quotient by a genuine regular element in
the maximal ideal. Its dimension increases by exactly one. -/
theorem isRegularLocalRing_of_regular_principal_quotient (x : R)
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) := by
      exact_mod_cast maximalIdeal_spanFinrank_le_quotient_add_one x
    _ = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxR hx

/-- The homological regularity criterion: a finite projective-dimension
bound on the actual residue field forces a noetherian local ring to be
regular in the original cotangent/Krull-dimension sense. -/
theorem isRegularLocalRing_of_residueField_bound (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n] :
    IsRegularLocalRing R := by
  induction n generalizing R with
  | zero =>
    let : Field R := isField_of_projective_residueField.toField
    infer_instance
  | succ n ih =>
    by_cases hfield : IsField R
    · let : Field R := hfield.toField
      infer_instance
    obtain ⟨x, hx, hx2, hxR⟩ := local_exists_regular_parameter_of_residueField_bound
      (n + 1) hfield
    have hI : Ideal.span {x} ≤ maximalIdeal R :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    let : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    let : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have := quotient_residueField_hasProjectiveDimensionLE n x hx hx2 hxR
    have := ih (R := R ⧸ Ideal.span {x})
    exact isRegularLocalRing_of_regular_principal_quotient x hx hxR

/-- The same criterion stated as finiteness of the original extended
projective dimension, rather than a chosen natural bound. -/
theorem isRegularLocalRing_of_residueField_projectiveDimension_ne_top
    (h : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    IsRegularLocalRing R := by
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff _).mp h
  have := hn
  exact isRegularLocalRing_of_residueField_bound n

/-- The full residue-field formulation of the homological criterion. -/
theorem isRegularLocalRing_iff_residueField_projectiveDimension_ne_top :
    IsRegularLocalRing R ↔
      projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤ := by
  refine ⟨fun hreg ↦ ?_, isRegularLocalRing_of_residueField_projectiveDimension_ne_top⟩
  have := hreg
  rw [SGA.SGA2.ExposeIV.regularLocal_residueField_projectiveDimension
    (maximalIdeal R).spanFinrank IsRegularLocalRing.spanFinrank_maximalIdeal.symm]
  exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Every actual prime localization of a regular local ring is regular
local. The homological criterion is proved, not supplied as an assumption. -/
theorem regularLocal_atPrime_isRegularLocalRing [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  have := regularLocal_residueField_atPrime_hasProjectiveDimensionLE
    (maximalIdeal R).spanFinrank IsRegularLocalRing.spanFinrank_maximalIdeal.symm p
  exact isRegularLocalRing_of_residueField_bound (maximalIdeal R).spanFinrank

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Regular local rings are regular rings in Mathlib's original sense:
all of their prime localizations are regular local rings. -/
theorem regularLocal_isRegularRing [IsRegularLocalRing R] : IsRegularRing R :=
  ⟨regularLocal_atPrime_isRegularLocalRing⟩

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- The global dimension at a prime is its own Krull dimension, sharpening
the earlier bound by the dimension of the original regular local ring. -/
theorem regularLocal_atPrime_moduleGlobalDimension_eq_ringKrullDim [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    moduleGlobalDimension (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime p) := by
  have := regularLocal_atPrime_isRegularLocalRing p
  exact regularLocal_moduleGlobalDimension_eq_ringKrullDim

end SGA.SGA2.ExposeV
