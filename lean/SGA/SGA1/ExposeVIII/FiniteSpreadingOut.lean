/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.SpecStalkLimit
import SGA.SGA1.ExposeVIII.FiniteDescent

/-!
# SGA 1, Exposé VIII, 6.5 for "finite": spreading out finiteness from a local scheme

Let `f : X ⟶ Y` be of finite type and quasi-compact, `Y` locally noetherian and `y ∈ Y`. If
`X ×_Y Spec 𝒪_{Y,y}` is finite over `Spec 𝒪_{Y,y}`, then `X` is finite over a neighbourhood of `y`
(EGA IV 8.10.5). This proves `IsFiniteSpreadingOutStatement`.

The proof: `X ×_Y Spec 𝒪_{Y,y}` is affine and is the limit of the inverse images of the affine
open neighbourhoods of `y` (`AlgebraicGeometry.Scheme.isLimitPreimageCone`), so one of them is
affine (Stacks 01Z6). Over an affine open `V` with affine inverse image, `f` is given by a ring map
`R ⟶ A` of finite type, and `A ⊗_R R_p` is finite over `R_p`; the integral equations of finitely
many generators of `A` spread out to some `R_s`, `s ∉ p`
(`exists_finite_away_of_finite_localization`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace SGA.SGA1.ExposeVIII

section Algebra

set_option backward.isDefEq.respectTransparency false in
/-- Spreading out finiteness from a prime (EGA IV 8.10.5 for finite morphisms, affine case): let
`A` be an `R`-algebra of finite type and `p` a prime of `R` such that `A_p = A ⊗_R R_p` is finite
over `R_p`. Then there is `s ∉ p` such that `A_s` is finite over `R_s`. -/
theorem exists_finite_away_of_finite_localization {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (p : Ideal R) [p.IsPrime] (Rp Ap : Type u)
    [CommRing Rp] [CommRing Ap] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [Algebra A Ap]
    [Algebra Rp Ap] [Algebra R Ap] [IsScalarTower R A Ap] [IsScalarTower R Rp Ap]
    [IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) Ap] [Module.Finite Rp Ap] :
    ∃ s ∉ p, ∀ (Rs As : Type u) [CommRing Rs] [CommRing As] [Algebra R Rs] [Algebra A As]
      [Algebra Rs As] [Algebra R As] [IsScalarTower R A As] [IsScalarTower R Rs As]
      [IsLocalization.Away s Rs] [IsLocalization.Away (algebraMap R A s) As],
      Module.Finite Rs As := by
  classical
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have hint (t : A) : ∃ m ∈ p.primeCompl, IsIntegral R (m • t) := by
    have h1 : IsIntegral Rp (algebraMap A Ap t) := Algebra.IsIntegral.isIntegral _
    obtain ⟨⟨m, hm⟩, hm'⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      p.primeCompl _ h1
    have e : (m : R) • algebraMap A Ap t = algebraMap A Ap (m • t) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [Submonoid.smul_def, e] at hm'
    obtain ⟨m', hm'p, hm''⟩ :=
      IsLocalization.exists_isIntegral_smul_of_isIntegral_map p.primeCompl (Sₘ := Ap) hm'
    exact ⟨m' * m, p.primeCompl.mul_mem hm'p hm, by rw [mul_smul]; exact hm''⟩
  choose m hmp hmint using hint
  refine ⟨∏ t ∈ T, m t, fun h ↦ ?_, ?_⟩
  · exact (p.primeCompl.prod_mem fun t _ ↦ hmp t) h
  intro Rs As _ _ _ _ _ _ _ _ _ _
  set s := ∏ t ∈ T, m t
  have hsu : IsUnit (algebraMap R Rs s) := IsLocalization.Away.algebraMap_isUnit s
  have hmu (t : A) (ht : t ∈ T) : IsUnit (algebraMap R Rs (m t)) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R Rs) (Finset.dvd_prod_of_mem m ht)) hsu
  -- the images of the generators are integral over `R_s`
  have hi (t : A) (ht : t ∈ T) : IsIntegral Rs (algebraMap A As t) := by
    have h2 : IsIntegral Rs (algebraMap A As (m t • t)) :=
      ((hmint t).map (IsScalarTower.toAlgHom R A As)).tower_top
    obtain ⟨u, hu⟩ := hmu t ht
    have e : algebraMap A As t =
        algebraMap Rs As (u⁻¹ : Rsˣ) * algebraMap A As (m t • t) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R Rs As, ← hu, ← mul_assoc, ← map_mul,
        Units.inv_mul, map_one, one_mul]
    rw [e]
    exact isIntegral_algebraMap.mul h2
  have hA (a : A) : IsIntegral Rs (algebraMap A As a) := by
    have ha : a ∈ Algebra.adjoin R (T : Set A) := hT ▸ Algebra.mem_top
    have hmem : algebraMap A As a ∈ Algebra.adjoin R
        ((IsScalarTower.toAlgHom R A As) '' (T : Set A)) := by
      rw [Algebra.adjoin_image]
      exact ⟨a, ha, rfl⟩
    have hle : Algebra.adjoin R ((IsScalarTower.toAlgHom R A As) '' (T : Set A)) ≤
        (integralClosure Rs As).restrictScalars R :=
      Algebra.adjoin_le (by
        rintro _ ⟨t, ht, rfl⟩
        exact hi t ht)
    exact hle hmem
  have : Algebra.IsIntegral Rs As := ⟨fun x ↦ by
    obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R A s)) x
    change x * algebraMap A As (algebraMap R A s ^ n) = algebraMap A As a at e
    obtain ⟨v, hv⟩ := hsu.pow n
    have e' : x = algebraMap A As a * algebraMap Rs As (v⁻¹ : Rsˣ) :=
      calc x = x * algebraMap Rs As ((v : Rs) * (v⁻¹ : Rsˣ)) := by
            rw [Units.mul_inv, map_one, mul_one]
        _ = x * algebraMap A As (algebraMap R A s ^ n) * algebraMap Rs As (v⁻¹ : Rsˣ) := by
            rw [map_mul, ← mul_assoc, hv, map_pow, map_pow, ← IsScalarTower.algebraMap_apply,
              ← IsScalarTower.algebraMap_apply]
        _ = _ := by rw [e]
    rw [e']
    exact (hA a).mul isIntegral_algebraMap⟩
  have : Algebra.FiniteType R As := Algebra.FiniteType.trans (S := A) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap R A s)) As)
  have : Algebra.FiniteType Rs As := Algebra.FiniteType.of_restrictScalars_finiteType R Rs As
  exact Algebra.IsIntegral.finite

end Algebra

section Schemes

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- Let `f` be of finite type and quasi-compact over a locally noetherian `Y`. If
`X ×_Y Spec 𝒪_{Y,y}` is affine, then `f⁻¹(V)` is affine for some affine open neighbourhood `V` of
`y` (Stacks 01Z6, applied to the limit `X ×_Y Spec 𝒪_{Y,y} = lim f⁻¹(V)`). -/
theorem exists_isAffineOpen_preimage_of_isAffine_pullback [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y)
    [IsAffine (pullback f (Y.fromSpecStalk y))] :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ IsAffineOpen (f ⁻¹ᵁ V) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit (Scheme.preimageDiagram y f)
    (Scheme.preimageCone y f) (Scheme.isLimitPreimageCone y f)
  exact ⟨V.1, V.2.1, V.2.2, hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- VIII.6.5 for "finite", the direction from the local scheme to a neighbourhood (EGA IV 8.10.5):
if `f` is of finite type and quasi-compact, `Y` is locally noetherian and
`X ×_Y Spec 𝒪_{Y,y}` is finite over `Spec 𝒪_{Y,y}`, then `X` is finite over a neighbourhood of
`y`. -/
theorem exists_isFinite_morphismRestrict_of_isFinite_pullback [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y)
    (hf : IsFinite (pullback.snd f (Y.fromSpecStalk y))) :
    ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) := by
  have : IsAffine (pullback f (Y.fromSpecStalk y)) :=
    isAffine_of_isAffineHom (pullback.snd f (Y.fromSpecStalk y))
  obtain ⟨V, hV, hyV, hXV⟩ := exists_isAffineOpen_preimage_of_isAffine_pullback f y
  -- the ring map `R = Γ(Y, V) ⟶ A = Γ(X, f⁻¹(V))`
  let φ : Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V) := f.appLE V (f ⁻¹ᵁ V) le_rfl
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := φ.hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hXV⟩ le_rfl
  -- the stalk `R_p`
  set p := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  let _ : Algebra Γ(Y, V) (Y.presheaf.stalk y) := (Y.presheaf.germ V y hyV).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hV.isLocalization_stalk ⟨y, hyV⟩
  -- `X ×_Y Spec R_p = Spec (A ⊗_R R_p)`
  have S1 := (IsOpenImmersion.isPullback (Spec.map φ) hXV.fromSpec hV.fromSpec f
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hXV le_rfl).symm
    (by rw [hV.opensRange_fromSpec, hXV.opensRange_fromSpec])).flip
  have S := (IsPullback.of_hasPullback (Spec.map φ)
    (Spec.map (Y.presheaf.germ V y hyV))).paste_horiz S1
  have hfs : Spec.map (Y.presheaf.germ V y hyV) ≫ hV.fromSpec = Y.fromSpecStalk y :=
    hV.fromSpecStalk_eq_fromSpecStalk hyV
  rw [hfs] at S
  have h₁ : IsFinite (pullback.snd (Spec.map φ) (Spec.map (Y.presheaf.germ V y hyV))) := by
    rw [← S.isoPullback_hom_snd]
    infer_instance
  have h₁' : IsFinite (pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)))) (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, V) (Y.presheaf.stalk y))))) := h₁
  have h₂ : IsFinite ((pullbackSpecIso (↑Γ(Y, V) : Type u) (↑Γ(X, f ⁻¹ᵁ V))
      (↑(Y.presheaf.stalk y))).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ inferInstance h₁'
  rw [pullbackSpecIso_inv_snd] at h₂
  let _ : Algebra (Y.presheaf.stalk y) (Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] Y.presheaf.stalk y) :=
    Algebra.TensorProduct.rightAlgebra
  have : Module.Finite (Y.presheaf.stalk y) (Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] Y.presheaf.stalk y) :=
    (IsFinite.SpecMap_iff _).mp h₂
  obtain ⟨s, hsp, hfin⟩ := exists_finite_away_of_finite_localization (R := Γ(Y, V))
    (A := Γ(X, f ⁻¹ᵁ V)) p (Y.presheaf.stalk y)
    (Γ(X, f ⁻¹ᵁ V) ⊗[Γ(Y, V)] Y.presheaf.stalk y)
  -- `X` is finite over the basic open `Y_s ∋ y`
  have hyU : y ∈ Y.basicOpen s := by
    rw [Scheme.mem_basicOpen Y s y hyV]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) p s).mpr hsp
  refine ⟨Y.basicOpen s, hyU, ?_⟩
  have hpre : f ⁻¹ᵁ Y.basicOpen s = X.basicOpen (φ s) := by
    change f ⁻¹ᵁ Y.basicOpen s = X.basicOpen (f.appLE V (f ⁻¹ᵁ V) le_rfl s)
    rw [Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE]
  let ψ : Γ(Y, Y.basicOpen s) ⟶ Γ(X, X.basicOpen (φ s)) :=
    f.appLE (Y.basicOpen s) (X.basicOpen (φ s)) hpre.ge
  let _ : Algebra Γ(Y, Y.basicOpen s) Γ(X, X.basicOpen (φ s)) := ψ.hom.toAlgebra
  let _ : Algebra Γ(Y, V) Γ(X, X.basicOpen (φ s)) :=
    ((algebraMap Γ(X, f ⁻¹ᵁ V) Γ(X, X.basicOpen (φ s))).comp
      (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V))).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, X.basicOpen (φ s)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen s) Γ(X, X.basicOpen (φ s)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change X.presheaf.map _ (f.appLE V (f ⁻¹ᵁ V) le_rfl r) =
        f.appLE (Y.basicOpen s) (X.basicOpen (φ s)) hpre.ge (Y.presheaf.map _ r)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
  have : IsLocalization.Away s Γ(Y, Y.basicOpen s) := hV.isLocalization_basicOpen s
  have : IsLocalization.Away (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) s)
      Γ(X, X.basicOpen (φ s)) := hXV.isLocalization_basicOpen (φ s)
  have hψ : ψ.hom.Finite := hfin _ _
  have : IsAffine (Y.basicOpen s) := hV.basicOpen s
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  refine ⟨?_, ?_⟩
  · change IsAffineOpen (f ⁻¹ᵁ Y.basicOpen s)
    rw [hpre]
    exact hXV.basicOpen (φ s)
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f _ _ le_rfl)]
    have e : f.appLE (Y.basicOpen s) (f ⁻¹ᵁ Y.basicOpen s) le_rfl =
        ψ ≫ X.presheaf.map (homOfLE hpre.le).op := (Scheme.Hom.appLE_map _ _ _).symm
    have : IsIso (X.presheaf.map (homOfLE hpre.le).op) := by
      rw [Subsingleton.elim (homOfLE hpre.le) (eqToHom hpre)]
      infer_instance
    change (f.appLE (Y.basicOpen s) (f ⁻¹ᵁ Y.basicOpen s) le_rfl).hom.Finite
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2) hψ

/-- VIII.6.5 for the property "finite" (EGA IV 8.10.5): for `f : X ⟶ Y` of finite type and
quasi-compact over a locally noetherian `Y` and `y ∈ Y`, `X` is finite over a neighbourhood of `y`
iff `X ×_Y Spec 𝒪_{Y,y}` is finite over `Spec 𝒪_{Y,y}`. -/
theorem isFiniteSpreadingOutStatement : IsFiniteSpreadingOutStatement.{u} := by
  intro X Y f _ _ _ y
  refine ⟨fun ⟨U, hy, hU⟩ ↦ ?_, fun h ↦ exists_isFinite_morphismRestrict_of_isFinite_pullback f y h⟩
  have := hU
  exact isFinite_pullback_fromSpecStalk f hy

end Schemes

end SGA.SGA1.ExposeVIII
