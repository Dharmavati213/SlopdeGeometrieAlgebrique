/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalk
import SGA.Foundations.Etale.StructureSheaf

/-!
# The stalk of the étale structure sheaf is the strict localization

Let `x̄ : Spec Ω ⟶ X` be a geometric point, `Ω` separably closed. The stalk at `x̄` of the
structure sheaf `𝒪_{X_et} : V ↦ Γ(V, 𝒪_V)` of the small étale site, i.e. the filtered colimit of
`Γ(V, 𝒪_V)` over the étale neighbourhoods `(V, v)` of `x̄`, is the strict localization
`𝒪^{sh}_{X,x̄}` (EGA IV 18.8, SGA 4 VIII 4, Stacks 04HX):
`AlgebraicGeometry.Scheme.Hom.etaleStructureStalkIso`.

The comparison map sends a section `s` over `(V, v)` to its pullback along the morphism
`Spec 𝒪^{sh}_{X,x̄} ⟶ V` given by `v` (`AlgebraicGeometry.Scheme.Hom.etaleNbhdHom`).
* Injectivity: on an affine chart `Spec T ⊆ V` over `Spec Γ(X, U) ⊆ X`, the map
  `T → 𝒪^{sh}_{X,x̄}` factors through the local ring `T_𝔮` of the point, and `𝒪^{sh}_{X,x̄}` is
  faithfully flat over `T_𝔮` (it is flat over `Γ(X, U)` and `T_𝔮` is unramified over it), so a
  section killed in `𝒪^{sh}_{X,x̄}` vanishes on a basic open neighbourhood of the point.
* Surjectivity: every element of `𝒪^{sh}_{X,x̄}` comes from a standard étale neighbourhood of the
  stalk `𝒪_{X,x}`; its equations spread out to an affine open neighbourhood of `x`, which gives an
  étale neighbourhood of `x̄` whose sections, together with the germs of functions, generate it.
-/

universe u

open CategoryTheory Limits Opposite IsLocalRing TensorProduct Polynomial

noncomputable section

-- As in `SGA.Foundations.Etale.Functoriality`: points of spectra are only defeq to prime ideals
-- beyond instance transparency.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- Finitely many germs at `x` are germs of sections over a common affine open neighbourhood. -/
lemma exists_affine_germ_eq (x : X) {n : ℕ} (c : Fin n → X.presheaf.stalk x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (a : Fin n → Γ(X, U)),
      ∀ i, X.presheaf.germ U x hx (a i) = c i := by
  induction n with
  | zero =>
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU, Fin.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨U, hU, hx, a, ha⟩ := ih (Fin.tail c)
    obtain ⟨U', hU'U, hx', b, hb⟩ := X.presheaf.exists_le_germ_eq (c 0) hx
    obtain ⟨_, ⟨U'', hU'', rfl⟩, hx'', hU''U'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hx' U'.isOpen
    have h₁ : U'' ≤ U' := hU''U'
    refine ⟨U'', hU'', hx'', Fin.cons (X.presheaf.map (homOfLE h₁).op b)
      (fun i ↦ X.presheaf.map (homOfLE (h₁.trans hU'U)).op (a i)), fun i ↦ ?_⟩
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp only [Fin.cons_zero, TopCat.Presheaf.germ_res_apply, hb]
    · simp only [Fin.cons_succ, TopCat.Presheaf.germ_res_apply, ha]
      rfl

/-- Finitely many sections with zero germs at `x` vanish on an affine open neighbourhood. -/
lemma exists_affine_map_eq_zero (x : X) {U : X.Opens} (hx : x ∈ U) {n : ℕ} (a : Fin n → Γ(X, U))
    (h : ∀ i, X.presheaf.germ U x hx (a i) = 0) :
    ∃ (U' : X.Opens) (_ : IsAffineOpen U') (_ : x ∈ U') (hle : U' ≤ U),
      ∀ i, X.presheaf.map (homOfLE hle).op (a i) = 0 := by
  induction n with
  | zero =>
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hx U.isOpen
    exact ⟨U', hU', hxU', hle, fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨U₁, hU₁, hx₁, hle₁, h₁⟩ := ih (Fin.tail a) (fun i ↦ h i.succ)
    obtain ⟨W, hxW, iU, iV, e⟩ := X.presheaf.germ_eq x hx hx (a 0) 0 (by rw [h 0, map_zero])
    rw [map_zero] at e
    obtain ⟨_, ⟨U', hU', rfl⟩, hx', hU'W⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ W ⊓ U₁ from ⟨hxW, hx₁⟩) (W ⊓ U₁).isOpen
    have hW : U' ≤ W := hU'W.trans inf_le_left
    have hU₁' : U' ≤ U₁ := hU'W.trans inf_le_right
    refine ⟨U', hU', hx', hU₁'.trans hle₁, fun i ↦ ?_⟩
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · have := congrArg (X.presheaf.map (homOfLE hW).op) e
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
      exact this
    · have := congrArg (X.presheaf.map (homOfLE hU₁').op) (h₁ i)
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
      exact this

/-- Finitely many polynomials over the stalk at `x` are images of polynomials over `Γ(X, U)` for a
common affine open neighbourhood `U` of `x`. -/
lemma exists_affine_polynomial_map_eq (x : X) {m : ℕ} (p : Fin m → (X.presheaf.stalk x)[X]) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (q : Fin m → Γ(X, U)[X]),
      ∀ j, (q j).map (X.presheaf.germ U x hx).hom = p j := by
  classical
  set d := Finset.univ.sup fun j ↦ (p j).natDegree
  obtain ⟨U, hU, hx, a, ha⟩ := exists_affine_germ_eq x
    (fun k : Fin (m * (d + 1)) ↦ (p (finProdFinEquiv.symm k).1).coeff (finProdFinEquiv.symm k).2)
  refine ⟨U, hU, hx,
    fun j ↦ ∑ i : Fin (d + 1), C (a (finProdFinEquiv (j, i))) * Polynomial.X ^ (i : ℕ), fun j ↦ ?_⟩
  have hd : (p j).natDegree < d + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j ↦ (p j).natDegree) (Finset.mem_univ j))
  conv_rhs => rw [(p j).as_sum_range' (d + 1) hd, ← Fin.sum_univ_eq_sum_range]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ha, C_mul_X_pow_eq_monomial]
  simp

lemma _root_.StandardEtalePair.ext' {R : Type*} [CommRing R] {P Q : StandardEtalePair R}
    (hf : P.f = Q.f) (hg : P.g = Q.g) : P = Q := by
  cases P
  cases Q
  simp_all

/-- A standard étale pair over the stalk `𝒪_{X,x}` is the base change of a standard étale pair over
`Γ(X, U)` for some affine open neighbourhood `U` of `x` (EGA IV 8.8.2). -/
lemma exists_standardEtalePair_map_eq (x : X) (P : StandardEtalePair (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (P' : StandardEtalePair Γ(X, U)),
      P'.map (X.presheaf.germ U x hx).hom = P := by
  obtain ⟨p₁, p₂, n, hc⟩ := P.cond
  obtain ⟨U, hU, hx, q, hq⟩ := exists_affine_polynomial_map_eq x ![P.f, P.g, p₁, p₂]
  set germ := (X.presheaf.germ U x hx).hom
  set d := P.f.natDegree
  let f' : Γ(X, U)[X] := Polynomial.X ^ d + ∑ i : Fin d, C ((q 0).coeff i) * Polynomial.X ^ (i : ℕ)
  have hf' : f'.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hq0 : (q 0).map germ = P.f := hq 0
  have hf'map : f'.map germ = P.f := by
    conv_rhs => rw [P.monic_f.as_sum, ← Fin.sum_univ_eq_sum_range]
    simp only [f', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Polynomial.coeff_map, hq0]
  let D : Γ(X, U)[X] := derivative f' * q 2 + f' * q 3 - q 1 ^ n
  have hD : D.map germ = 0 := by
    have h1 : (q 1).map germ = P.g := hq 1
    have h2 : (q 2).map germ = p₁ := hq 2
    have h3 : (q 3).map germ = p₂ := hq 3
    simp only [D, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      ← Polynomial.derivative_map, hf'map, h1, h2, h3, hc, sub_self]
  obtain ⟨U', hU', hx', hle, hzero⟩ := exists_affine_map_eq_zero x hx
    (fun i : Fin (D.natDegree + 1) ↦ D.coeff i) (fun i ↦ by
      rw [← Polynomial.coeff_map, hD, coeff_zero])
  set res := (X.presheaf.map (homOfLE hle).op).hom
  have hres : (X.presheaf.germ U' x hx').hom.comp res = germ := by
    ext a
    exact X.presheaf.germ_res_apply (homOfLE hle) x hx' a
  have hDres : D.map res = 0 := by
    ext i
    rw [coeff_map, coeff_zero]
    by_cases hi : i ≤ D.natDegree
    · exact hzero ⟨i, Nat.lt_succ_of_le hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), map_zero]
  refine ⟨U', hU', hx', ⟨f'.map res, hf'.map res, (q 1).map res,
    ⟨(q 2).map res, (q 3).map res, n, ?_⟩⟩, ?_⟩
  · have := hDres
    simp only [D, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      ← Polynomial.derivative_map, sub_eq_zero] at this
    exact this
  · refine StandardEtalePair.ext' ?_ ?_
    · simp only [StandardEtalePair.map_f, Polynomial.map_map, hres, hf'map]
    · simp only [StandardEtalePair.map_g, Polynomial.map_map, hres]
      exact hq 1

end Scheme

namespace Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)

attribute [local instance] residueFieldAlgebra stalkAlgebra isScalarTower_stalkAlgebra

lemma fromSpecStrictLocalization_eq_SpecMap {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : ξ.imagePoint ∈ U) :
    ξ.fromSpecStrictLocalization =
      Spec.map (X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization) ≫ hU.fromSpec := by
  rw [fromSpecStrictLocalization, Scheme.fromSpecStalk_eq_SpecMap_germ hU hxU, Spec.map_comp,
    Category.assoc]

lemma eq_SpecMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U) :
    ξ = Spec.map (X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding) ≫
      hU.fromSpec := by
  conv_lhs => rw [← ξ.fromSpecResidueField_eq]
  rw [Scheme.fromSpecResidueField, Scheme.fromSpecStalk_eq_SpecMap_germ hU hxU]
  simp only [Spec.map_comp, Category.assoc]

/-- The étale neighbourhood `Spec T ⟶ Spec Γ(X, U) ⟶ X` of an étale `Γ(X, U)`-algebra `T`. -/
def affineEtaleNbhd {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{u}}
    (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale) : X.Etale :=
  haveI : Etale (Spec.map ρ) := HasRingHomProperty.Spec_iff.mpr hρ
  Etale.mk (Spec.map ρ ≫ hU.fromSpec)

variable [IsSepClosed Ω]

/-- The point of `affineEtaleNbhd` over `x̄` given by a ring map `τ : T → Ω` over the point. -/
def affineEtaleNbhdPoint {U : X.Opens} (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U)
    {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale) (τ : T ⟶ .of Ω)
    (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding) :
    (pointSmallEtale ξ).fiber.obj (affineEtaleNbhd hU ρ hρ) :=
  Over.homMk (Spec.map τ) (by
    change Spec.map τ ≫ Spec.map ρ ≫ hU.fromSpec = ξ
    rw [← Category.assoc, ← Spec.map_comp, hτ, ← eq_SpecMap_fromSpec])

lemma etaleNbhdHom_affineEtaleNbhd {U : X.Opens} (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U)
    {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale) (τ : T ⟶ .of Ω)
    (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding)
    (φ : T ⟶ ξ.strictLocalization)
    (hφ₁ : ρ ≫ φ = X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization)
    (hφ₂ : φ ≫ ξ.strictLocalizationToField = τ) :
    ξ.etaleNbhdHom _ (ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ) = Spec.map φ := by
  refine ξ.etaleNbhdHom_eq _ ?_ ?_
  · change Spec.map φ ≫ Spec.map ρ ≫ hU.fromSpec = _
    rw [← Category.assoc, ← Spec.map_comp, hφ₁, ← fromSpecStrictLocalization_eq_SpecMap]
  · change Spec.map ξ.strictLocalizationToField ≫ Spec.map φ = Spec.map τ
    rw [← Spec.map_comp, hφ₂]

/-- The comparison map from the stalk at `x̄` of the étale structure sheaf to the strict
localization: a section over an étale neighbourhood `(V, v)` is pulled back along
`etaleNbhdHom V v : Spec 𝒪^{sh}_{X,x̄} ⟶ V`. -/
def etaleStructureStalkHom :
    (pointSmallEtale ξ).presheafFiber.obj X.etaleStructurePresheaf ⟶ ξ.strictLocalization :=
  (pointSmallEtale ξ).presheafFiberDesc
    (fun V v ↦ (ξ.etaleNbhdHom V v).appTop ≫ (ΓSpecIso ξ.strictLocalization).hom)
    (fun V W g v ↦ by
      change g.left.appTop ≫ _ = _
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, etaleNbhdHom_naturality])

lemma etaleStructureStalkHom_toPresheafFiber (V : X.Etale) (v : (pointSmallEtale ξ).fiber.obj V)
    (s : Γ(V.left, ⊤)) :
    ξ.etaleStructureStalkHom ((pointSmallEtale ξ).toPresheafFiber V v X.etaleStructurePresheaf s) =
      (ΓSpecIso ξ.strictLocalization).hom ((ξ.etaleNbhdHom V v).appTop s) :=
  ConcreteCategory.congr_hom
    ((pointSmallEtale ξ).toPresheafFiber_presheafFiberDesc (P := X.etaleStructurePresheaf)
      (fun V v ↦ (ξ.etaleNbhdHom V v).appTop ≫ (ΓSpecIso ξ.strictLocalization).hom)
      (fun V W g v ↦ by
        change g.left.appTop ≫ _ = _
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop, etaleNbhdHom_naturality]) V v) s

lemma etaleStructureStalkHom_affineEtaleNbhd {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : ξ.imagePoint ∈ U) {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale)
    (τ : T ⟶ .of Ω)
    (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding)
    (φ : T ⟶ ξ.strictLocalization)
    (hφ₁ : ρ ≫ φ = X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization)
    (hφ₂ : φ ≫ ξ.strictLocalizationToField = τ) (t : T) :
    ξ.etaleStructureStalkHom ((pointSmallEtale ξ).toPresheafFiber _
      (ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ) X.etaleStructurePresheaf ((ΓSpecIso T).inv t)) =
        φ t := by
  rw [etaleStructureStalkHom_toPresheafFiber,
    ξ.etaleNbhdHom_affineEtaleNbhd hU hxU ρ hρ τ hτ φ hφ₁ hφ₂]
  change ((ΓSpecIso T).inv ≫ (Spec.map φ).appTop ≫ (ΓSpecIso ξ.strictLocalization).hom) t = φ t
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma _root_.Subring.eval₂_mem {A B : Type*} [CommRing A] [CommRing B] (S : Subring B)
    (f : A →+* B) (hf : ∀ a, f a ∈ S) {b : B} (hb : b ∈ S) (p : A[X]) : p.eval₂ f b ∈ S := by
  rw [eval₂_eq_sum]
  exact Subring.sum_mem _ fun n _ ↦ S.mul_mem (hf _) (S.pow_mem hb n)

/-- The comparison map from the stalk of the étale structure sheaf to the strict localization is
surjective: every element of `𝒪^{sh}_{X,x̄}` is a section over an étale neighbourhood of `x̄`. -/
theorem etaleStructureStalkHom_surjective :
    Function.Surjective ξ.etaleStructureStalkHom := by
  set R := X.presheaf.stalk ξ.imagePoint
  set S := ξ.etaleStructureStalkHom.hom.range
  suffices h : ∀ z, z ∈ S from fun z ↦ h z
  -- germs of functions
  have hgerm (r : R) : algebraMap R (StrictHenselization R Ω) r ∈ S := by
    obtain ⟨U, hU, hx, a, ha⟩ := Scheme.exists_affine_germ_eq ξ.imagePoint ![r]
    have hρ : (𝟙 Γ(X, U) : Γ(X, U) ⟶ Γ(X, U)).hom.Etale :=
      RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale Γ(X, U) Γ(X, U))
    have := ξ.etaleStructureStalkHom_affineEtaleNbhd hU hx (𝟙 _) hρ
      (X.presheaf.germ U _ hx ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding) (by simp)
      (X.presheaf.germ U _ hx ≫ ξ.toStrictLocalization) (by simp)
      (by rw [Category.assoc, toStrictLocalization_strictLocalizationToField]) (a 0)
    refine ⟨_, this.trans ?_⟩
    have h0 : X.presheaf.germ U _ hx (a 0) = r := ha 0
    rw [CommRingCat.comp_apply, h0]
    rfl
  intro z
  obtain ⟨N, y, hy⟩ := IsLocalRing.StrictHenselization.exists_of_algebraMap (R := R) (K := Ω)
    (fun _ : Unit ↦ z)
  obtain ⟨U, hU, hx, P', hP'⟩ := Scheme.exists_standardEtalePair_map_eq ξ.imagePoint N.pair
  let : Algebra Γ(X, U) R := (X.presheaf.germ U _ hx).hom.toAlgebra
  let : Algebra Γ(X, U) Ω := ((algebraMap R Ω).comp (algebraMap Γ(X, U) R)).toAlgebra
  have : IsScalarTower Γ(X, U) R Ω := .of_algebraMap_eq' rfl
  let : Algebra Γ(X, U) N.pair.Ring :=
    ((algebraMap R N.pair.Ring).comp (algebraMap Γ(X, U) R)).toAlgebra
  have : IsScalarTower Γ(X, U) R N.pair.Ring := .of_algebraMap_eq' rfl
  have hmapf : P'.f.map (algebraMap Γ(X, U) R) = N.pair.f := congrArg StandardEtalePair.f hP'
  have hmapg : P'.g.map (algebraMap Γ(X, U) R) = N.pair.g := congrArg StandardEtalePair.g hP'
  have hpt : P'.HasMap N.point := by
    refine ⟨?_, ?_⟩
    · rw [← aeval_map_algebraMap R, hmapf]
      exact N.hasMap.1
    · rw [← aeval_map_algebraMap R, hmapg]
      exact N.hasMap.2
  have hX : P'.HasMap N.pair.X := by
    refine ⟨?_, ?_⟩
    · rw [← aeval_map_algebraMap R, hmapf]
      exact StandardEtalePair.hasMap_X.1
    · rw [← aeval_map_algebraMap R, hmapg]
      exact StandardEtalePair.hasMap_X.2
  let ρ' := P'.lift N.pair.X hX
  let τ' := P'.lift N.point hpt
  let ρ : Γ(X, U) ⟶ CommRingCat.of P'.Ring := CommRingCat.ofHom (algebraMap Γ(X, U) P'.Ring)
  have hρ : ρ.hom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let τ : CommRingCat.of P'.Ring ⟶ .of Ω := CommRingCat.ofHom τ'.toRingHom
  have hτ : ρ ≫ τ =
      X.presheaf.germ U _ hx ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
    ext a
    exact τ'.commutes a
  let Φ : N.pair.Ring →+* StrictHenselization R Ω :=
    (IsLocalRing.StrictHenselization.of N).toRingHom.comp (algebraMap N.pair.Ring N.Stalk)
  let φ : CommRingCat.of P'.Ring ⟶ ξ.strictLocalization :=
    CommRingCat.ofHom (Φ.comp ρ'.toRingHom)
  have hφ₁ : ρ ≫ φ = X.presheaf.germ U _ hx ≫ ξ.toStrictLocalization := by
    ext a
    change IsLocalRing.StrictHenselization.of N (algebraMap N.pair.Ring N.Stalk
      (ρ' (algebraMap Γ(X, U) P'.Ring a))) = algebraMap R _ (algebraMap Γ(X, U) R a)
    rw [ρ'.commutes, IsScalarTower.algebraMap_apply Γ(X, U) R N.pair.Ring,
      ← IsScalarTower.algebraMap_apply R N.pair.Ring N.Stalk, AlgHom.commutes]
  have hcomm (a : Γ(X, U)) : (φ ≫ ξ.strictLocalizationToField).hom
      (algebraMap Γ(X, U) P'.Ring a) = algebraMap Γ(X, U) Ω a := by
    have h1 := ConcreteCategory.congr_hom hφ₁ a
    have h2 := ConcreteCategory.congr_hom (toStrictLocalization_strictLocalizationToField ξ)
      (X.presheaf.germ U _ hx a)
    rw [CommRingCat.comp_apply] at h1 h2
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg ξ.strictLocalizationToField.hom h1).trans h2
  have hφ₂ : φ ≫ ξ.strictLocalizationToField = τ := by
    let φA : P'.Ring →ₐ[Γ(X, U)] Ω := ⟨(φ ≫ ξ.strictLocalizationToField).hom, hcomm⟩
    have hφA : φA = τ' := P'.hom_ext (by
      rw [StandardEtalePair.lift_X]
      change IsLocalRing.StrictHenselization.pointHom
        (Φ (ρ' P'.X)) = N.point
      rw [StandardEtalePair.lift_X]
      change IsLocalRing.StrictHenselization.pointHom (IsLocalRing.StrictHenselization.of N
        (algebraMap N.pair.Ring N.Stalk N.pair.X)) = N.point
      rw [IsLocalRing.StrictHenselization.pointHom_of, IsLocalRing.EtaleNbhd.pointHom_algebraMap,
        IsLocalRing.EtaleNbhd.toField_X])
    ext t
    exact DFunLike.congr_fun hφA t
  have hφS (t : P'.Ring) : φ t ∈ S :=
    ⟨_, ξ.etaleStructureStalkHom_affineEtaleNbhd hU hx ρ hρ τ hτ φ hφ₁ hφ₂ t⟩
  -- the elements of the neighbourhood generate
  let Pr : StandardEtalePresentation R N.pair.Ring :=
    ⟨N.pair, N.pair.X, StandardEtalePair.hasMap_X, by simpa using Function.bijective_id⟩
  obtain ⟨p, m, hpm⟩ := Pr.exists_mul_aeval_x_g_pow_eq_aeval_x (y ())
  set u := (StandardEtalePair.hasMap_X (P := N.pair)).2.unit
  set u' := (StandardEtalePair.hasMap_X (P := P')).2.unit
  have hu : ρ' (↑u'⁻¹ : P'.Ring) = ↑u⁻¹ := by
    have hu' : ρ' (u' : P'.Ring) = u := by
      change ρ' (aeval P'.X P'.g) = aeval N.pair.X N.pair.g
      rw [← aeval_algHom_apply, StandardEtalePair.lift_X, ← aeval_map_algebraMap R, hmapg]
    apply Units.eq_inv_of_mul_eq_one_left
    rw [← hu', ← map_mul, Units.mul_inv, map_one]
  have hy' : y () = aeval N.pair.X p * ↑u⁻¹ ^ m := by
    rw [← hpm, mul_assoc, ← mul_pow]
    simp [u]
  rw [← hy ()]
  change Φ (y ()) ∈ S
  rw [hy', map_mul, map_pow]
  refine S.mul_mem ?_ (S.pow_mem ?_ m)
  · have hΦ : Φ.comp (algebraMap R N.pair.Ring) = algebraMap R (StrictHenselization R Ω) := by
      ext r
      change IsLocalRing.StrictHenselization.of N
        (algebraMap N.pair.Ring N.Stalk (algebraMap R N.pair.Ring r)) = _
      rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    have : Φ (aeval N.pair.X p) = p.eval₂ (algebraMap R _) (Φ N.pair.X) := by
      rw [aeval_def, hom_eval₂, hΦ]
    change Φ (aeval N.pair.X p) ∈ S
    rw [this]
    refine Subring.eval₂_mem S _ hgerm ?_ p
    have h := hφS P'.X
    have e : φ P'.X = Φ N.pair.X := by
      change Φ (ρ' P'.X) = _
      rw [StandardEtalePair.lift_X]
    rw [e] at h
    exact h
  · change Φ ↑u⁻¹ ∈ S
    rw [← hu]
    exact hφS _

/-- The ring map `T → 𝒪^{sh}_{X,x̄}` of an affine étale neighbourhood `Spec T` of `x̄`. -/
lemma exists_affineEtaleNbhd_ringHom {U : X.Opens} (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U)
    {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale) (τ : T ⟶ .of Ω)
    (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding) :
    ∃ φ : T ⟶ ξ.strictLocalization,
      ρ ≫ φ = X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization ∧
        φ ≫ ξ.strictLocalizationToField = τ := by
  refine ⟨Spec.preimage (ξ.etaleNbhdHom _ (ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ)), ?_, ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
      ← fromSpecStrictLocalization_eq_SpecMap]
    exact ξ.etaleNbhdHom_comp_hom _ _
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact ξ.toSpecStrictLocalization_etaleNbhdHom _ _

/-- Every étale neighbourhood of `x̄` is refined by an affine one `Spec T ⟶ Spec Γ(X, U) ⊆ X`. -/
lemma exists_affineEtaleNbhd_hom (V : X.Etale) (v : (pointSmallEtale ξ).fiber.obj V) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : ξ.imagePoint ∈ U) (T : CommRingCat.{u})
      (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale) (τ : T ⟶ .of Ω)
      (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding)
      (g : affineEtaleNbhd hU ρ hρ ⟶ V),
      (pointSmallEtale ξ).fiber.map g (ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ) = v := by
  obtain ⟨U, hU, hxU, -, -⟩ := Scheme.exists_affine_germ_eq ξ.imagePoint (n := 0) Fin.elim0
  have hw : v.left ≫ V.hom = ξ := Over.w v
  set v₀ : V.left := v.left (default : Spec (.of Ω))
  have hv₀ : V.hom v₀ = ξ.imagePoint := by
    rw [← ξ.apply_eq_imagePoint (default : Spec (.of Ω)), ← hw]
    rfl
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hv₀V₀, hle⟩ := V.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show v₀ ∈ V.hom ⁻¹ᵁ U from by rw [Scheme.Hom.mem_preimage, hv₀]; exact hxU)
    (V.hom ⁻¹ᵁ U).isOpen
  have hle' : V₀ ≤ V.hom ⁻¹ᵁ U := hle
  let ρ := V.hom.appLE U V₀ hle'
  have hρ : ρ.hom.Etale :=
    HasRingHomProperty.appLE @Etale V.hom inferInstance ⟨U, hU⟩ ⟨V₀, hV₀⟩ hle'
  have htop : ⊤ ≤ v.left ⁻¹ᵁ V₀ := fun y _ ↦ by
    have hy : ∀ z : Spec (.of Ω), z = default := fun z ↦ Subsingleton.elim _ _
    change v.left y ∈ V₀
    rw [hy y]
    exact hv₀V₀
  let τ := v.left.appLE V₀ ⊤ htop ≫ (ΓSpecIso (.of Ω)).hom
  have hτv : Spec.map τ ≫ hV₀.fromSpec = v.left :=
    Scheme.Hom.SpecMap_appLE_ΓSpecIso_fromSpec v.left hV₀ htop
  have hfromSpec : Spec.map ρ ≫ hU.fromSpec = hV₀.fromSpec ≫ V.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec V.hom hU hV₀ hle'
  have hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hfromSpec, reassoc_of% hτv, hw,
      ← eq_SpecMap_fromSpec]
  refine ⟨U, hU, hxU, _, ρ, hρ, τ, hτ, MorphismProperty.Over.homMk hV₀.fromSpec hfromSpec.symm, ?_⟩
  exact Over.OverMorphism.ext hτv

omit [IsSepClosed Ω] in
/-- A section of an affine étale neighbourhood `Spec T` of `x̄` which vanishes in `𝒪^{sh}_{X,x̄}` is
killed by an element of `T` not vanishing at the point: `𝒪^{sh}_{X,x̄}` is faithfully flat over the
local ring of `Spec T` at the point, being flat over `Γ(X, U)` while `T` is unramified over
`Γ(X, U)`. -/
lemma exists_mul_eq_zero_of_affineEtaleNbhd {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : ξ.imagePoint ∈ U) {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale)
    (φ : T ⟶ ξ.strictLocalization)
    (hφ₁ : ρ ≫ φ = X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization) (t : T) (ht : φ t = 0) :
    ∃ u : T, ξ.strictLocalizationToField (φ u) ≠ 0 ∧ u * t = 0 := by
  classical
  let τ : T →+* Ω := (φ ≫ ξ.strictLocalizationToField).hom
  let q : Ideal T := RingHom.ker τ
  have : q.IsPrime := RingHom.ker_isPrime τ
  let Tq := Localization.AtPrime q
  let : Algebra Γ(X, U) T := ρ.hom.toAlgebra
  have : Algebra.Etale Γ(X, U) T := hρ
  have hunit (y : q.primeCompl) : IsUnit (φ.hom y) := by
    by_contra h
    refine y.2 ?_
    change τ y = 0
    by_contra h0
    exact h (IsLocalHom.map_nonunit (f := ξ.strictLocalizationToField.hom) _
      (isUnit_iff_ne_zero.mpr h0))
  let ψ : Tq →+* ξ.strictLocalization :=
    IsLocalization.lift (M := q.primeCompl) (g := φ.hom) hunit
  let : Algebra Tq ξ.strictLocalization := ψ.toAlgebra
  -- `𝒪^{sh}_{X,x̄}` is flat over `Γ(X, U)`, through the localization `𝒪_{X,x}` of `Γ(X, U)`
  let : Algebra Γ(X, U) (X.presheaf.stalk ξ.imagePoint) :=
    X.presheaf.algebra_section_stalk ⟨_, hxU⟩
  let : Algebra Γ(X, U) ξ.strictLocalization :=
    ((algebraMap (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization).comp
      (algebraMap Γ(X, U) (X.presheaf.stalk ξ.imagePoint))).toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization :=
    .of_algebraMap_eq' rfl
  have : IsLocalization.AtPrime (X.presheaf.stalk ξ.imagePoint)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨_, hxU⟩
  have : Module.Flat Γ(X, U) (X.presheaf.stalk ξ.imagePoint) :=
    IsLocalization.flat _ (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl
  have : Module.Flat Γ(X, U) ξ.strictLocalization :=
    Module.Flat.trans Γ(X, U) (X.presheaf.stalk ξ.imagePoint) ξ.strictLocalization
  -- hence over the local ring `T_𝔮`, which is unramified over `Γ(X, U)`
  have : IsScalarTower Γ(X, U) Tq ξ.strictLocalization := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) T Tq a]
    change (X.presheaf.germ U _ hxU ≫ ξ.toStrictLocalization) a = ψ (algebraMap T Tq (ρ a))
    rw [IsLocalization.lift_eq, ← hφ₁]
    rfl
  have : Algebra.FormallyUnramified T Tq := .of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified Γ(X, U) Tq := .comp Γ(X, U) T Tq
  have : Module.Flat Tq ξ.strictLocalization :=
    Algebra.FormallyUnramified.flat_of_restrictScalars Γ(X, U) Tq ξ.strictLocalization
  have : IsLocalHom ψ := ⟨fun a ha ↦ by
    obtain ⟨⟨t', s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl a
    have h1 : φ t' = ψ (IsLocalization.mk' Tq t' s) * φ s := by
      rw [← IsLocalization.lift_eq (M := q.primeCompl) (S := Tq) hunit t',
        ← IsLocalization.mk'_spec Tq t' s, map_mul, IsLocalization.lift_eq]
    have h2 : IsUnit (φ t') := h1 ▸ ha.mul (hunit s)
    refine (IsLocalization.AtPrime.isUnit_mk'_iff Tq q t' s).mpr fun h ↦ ?_
    have h3 : τ t' = 0 := h
    exact not_isUnit_zero (h3 ▸ h2.map ξ.strictLocalizationToField.hom)⟩
  have : IsLocalHom (algebraMap Tq ξ.strictLocalization) := inferInstanceAs (IsLocalHom ψ)
  have : Module.FaithfullyFlat Tq ξ.strictLocalization := .of_flat_of_isLocalHom
  have hzero : algebraMap T Tq t = 0 := by
    refine FaithfulSMul.algebraMap_injective Tq ξ.strictLocalization ?_
    rw [map_zero]
    change ψ (algebraMap T Tq t) = 0
    rw [IsLocalization.lift_eq]
    exact ht
  obtain ⟨⟨u, hu⟩, hut⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl Tq t).mp hzero
  exact ⟨u, hu, hut⟩

/-- A section of an affine étale neighbourhood `Spec T` of `x̄` killed by an element `u` not
vanishing at the point has zero germ at `x̄`: it vanishes on the neighbourhood `Spec T_u`. -/
lemma toPresheafFiber_affineEtaleNbhd_eq_zero {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : ξ.imagePoint ∈ U) {T : CommRingCat.{u}} (ρ : Γ(X, U) ⟶ T) (hρ : ρ.hom.Etale)
    (τ : T ⟶ .of Ω)
    (hτ : ρ ≫ τ = X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding)
    (t u : T) (hu : τ u ≠ 0) (hut : u * t = 0) :
    (pointSmallEtale ξ).toPresheafFiber _ (ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ)
      X.etaleStructurePresheaf ((ΓSpecIso T).inv t) = 0 := by
  let ι : T ⟶ CommRingCat.of (Localization.Away u) :=
    CommRingCat.ofHom (algebraMap T (Localization.Away u))
  have hι : ι.hom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway u)
  have hρ' : (ρ ≫ ι).hom.Etale := RingHom.Etale.stableUnderComposition _ _ hρ hι
  let τ' : CommRingCat.of (Localization.Away u) ⟶ .of Ω :=
    CommRingCat.ofHom (IsLocalization.Away.lift u (g := τ.hom) (isUnit_iff_ne_zero.mpr hu))
  have hιτ : ι ≫ τ' = τ := by
    ext a
    exact IsLocalization.lift_eq _ a
  have hτ' : (ρ ≫ ι) ≫ τ' =
      X.presheaf.germ U _ hxU ≫ X.residue ξ.imagePoint ≫ ξ.residueFieldEmbedding := by
    rw [Category.assoc, hιτ, hτ]
  let g : affineEtaleNbhd hU (ρ ≫ ι) hρ' ⟶ affineEtaleNbhd hU ρ hρ :=
    MorphismProperty.Over.homMk (Spec.map ι) (by
      change Spec.map ι ≫ Spec.map ρ ≫ hU.fromSpec = Spec.map (ρ ≫ ι) ≫ hU.fromSpec
      rw [Spec.map_comp, Category.assoc])
  have hg : (pointSmallEtale ξ).fiber.map g (ξ.affineEtaleNbhdPoint hU hxU _ hρ' τ' hτ') =
      ξ.affineEtaleNbhdPoint hU hxU ρ hρ τ hτ := by
    refine Over.OverMorphism.ext ?_
    change Spec.map τ' ≫ Spec.map ι = Spec.map τ
    rw [← Spec.map_comp, hιτ]
  have hιt : ι t = 0 := by
    change algebraMap T (Localization.Away u) t = 0
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers u) _ t).mpr
      ⟨⟨u, Submonoid.mem_powers u⟩, hut⟩
  have hres : X.etaleStructurePresheaf.map g.op ((ΓSpecIso T).inv t) = 0 := by
    change (Spec.map ι).appTop ((ΓSpecIso T).inv t) = 0
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, hιt,
      map_zero]
  rw [← hg, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hres, map_zero]

/-- The comparison map from the stalk of the étale structure sheaf to the strict localization is
injective. -/
theorem etaleStructureStalkHom_injective :
    Function.Injective ξ.etaleStructureStalkHom := by
  refine (injective_iff_map_eq_zero ξ.etaleStructureStalkHom.hom).mpr fun p hp ↦ ?_
  obtain ⟨V, v, s, rfl⟩ := (pointSmallEtale ξ).toPresheafFiber_jointly_surjective p
  obtain ⟨U, hU, hxU, T, ρ, hρ, τ, hτ, g, rfl⟩ := ξ.exists_affineEtaleNbhd_hom V v
  change ξ.etaleStructureStalkHom _ = 0 at hp
  rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply] at hp ⊢
  have hs : X.etaleStructurePresheaf.map g.op s =
      (ΓSpecIso T).inv ((ΓSpecIso T).hom (X.etaleStructurePresheaf.map g.op s)) := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [hs] at hp ⊢
  obtain ⟨φ, hφ₁, hφ₂⟩ := ξ.exists_affineEtaleNbhd_ringHom hU hxU ρ hρ τ hτ
  rw [ξ.etaleStructureStalkHom_affineEtaleNbhd hU hxU ρ hρ τ hτ φ hφ₁ hφ₂] at hp
  obtain ⟨u, hu, hut⟩ := ξ.exists_mul_eq_zero_of_affineEtaleNbhd hU hxU ρ hρ φ hφ₁ _ hp
  refine ξ.toPresheafFiber_affineEtaleNbhd_eq_zero hU hxU ρ hρ τ hτ _ u ?_ hut
  rwa [← hφ₂]

theorem etaleStructureStalkHom_bijective :
    Function.Bijective ξ.etaleStructureStalkHom :=
  ⟨ξ.etaleStructureStalkHom_injective, ξ.etaleStructureStalkHom_surjective⟩

/-- EGA IV 18.8, SGA 4 VIII 4 (Stacks 04HX): the stalk at a geometric point `x̄` of the
structure sheaf of the small étale site, i.e. the filtered colimit of `Γ(V, 𝒪_V)` over the étale
neighbourhoods `(V, v)` of `x̄`, is the strict localization `𝒪^{sh}_{X,x̄}`. -/
def etaleStructureStalkIso :
    (pointSmallEtale ξ).presheafFiber.obj X.etaleStructurePresheaf ≅ ξ.strictLocalization :=
  (RingEquiv.ofBijective ξ.etaleStructureStalkHom.hom
    ξ.etaleStructureStalkHom_bijective).toCommRingCatIso

@[simp]
lemma etaleStructureStalkIso_hom : ξ.etaleStructureStalkIso.hom = ξ.etaleStructureStalkHom :=
  rfl

end Scheme.Hom

end AlgebraicGeometry
