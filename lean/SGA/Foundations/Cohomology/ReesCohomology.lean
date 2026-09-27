/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ReesMaps
import SGA.Foundations.Cohomology.LerayNaturality

/-!
# Cohomology of the Rees module

Let `f : X ⟶ Spec A` with `A` noetherian, `I ⊆ A` an ideal, `B = ⊕ Iᵏ tᵏ` the Rees algebra,
`q_B : X_B ⟶ X` the base change and `M` quasi-coherent on `X`.

* `CohomologyAux.reesMul b`: multiplication by `b ∈ B` on `q_{B*}(⊕ Iᵐ M tᵐ)`, i.e. the direct image
  of multiplication by the image of `b` in `Γ(X_B, 𝒪)`. Multiplication by `a tᵏ` (`a ∈ Iᵏ`) shifts
  the graded pieces: `reesMul (a tᵏ) ≫ reesPi (j + k) = reesPi j ≫ (a : Iʲ M → Iʲ⁺ᵏ M)`
  (`reesMul_reesPi_monomial`), and `reesMul (a tᵏ) ≫ reesPi m = 0` for `m < k`.
* `CohomologyAux.exists_H'_map_eq_zero`: on a quasi-compact scheme with affine diagonal, if every
  section over an affine open is killed by all but finitely many `πₘ`, then so is every
  cohomology class (via Čech cohomology for a finite affine cover). Applied to the `reesPi m`, this
  is the fact that cohomology commutes with the direct sum `⊕ Iᵐ M` (EGA III 3.3.1, 0_III 12.4.6
  used there).
* Quasi-coherence and coherence of the Rees module (`isCoherent_reesSheaf`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf Polynomial

namespace AlgebraicGeometry.CohomologyAux

section Instances

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules)

include I in
lemma isQuasicoherent_IPow [IsNoetherianRing A] [M.IsQuasicoherent] (n : ℕ) :
    (IPow f I M n).IsQuasicoherent := by
  have : (⨁ fun _ : Fin (numGens I n) ↦ M).IsQuasicoherent := isQuasicoherent_biproduct _
  exact isQuasicoherent_image _

lemma isQuasicoherent_reesSheaf [M.IsQuasicoherent] : (reesSheaf I f M).IsQuasicoherent := by
  have : ((Scheme.Modules.pushforward (reesBaseChange I f)).obj
      ((Scheme.Modules.pullback (polyFst I f)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward _ _
  exact isQuasicoherent_image _

lemma isQuasicoherent_reesPush [M.IsQuasicoherent] : (reesPush I f M).IsQuasicoherent := by
  have := isQuasicoherent_reesSheaf I f M
  exact isQuasicoherent_pushforward _ _

/-- **The Rees module of a coherent module is coherent** (EGA III 3.3.1): it is a quotient of
`q_B^* M`. -/
lemma isCoherent_reesSheaf [M.IsCoherent] : (reesSheaf I f M).IsCoherent := by
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : SheafOfModules.IsFiniteType.{u} M := Scheme.Modules.IsCoherent.isFiniteType
  have hS := shortExact_kernelSequence (Abelian.factorThruImage (reesUnit I f M))
  have : (ShortComplex.kernelSequence
      (Abelian.factorThruImage (reesUnit I f M))).X₂.IsCoherent :=
    ⟨inferInstanceAs ((Scheme.Modules.pullback (reesFst I f)).obj M).IsQuasicoherent,
      inferInstanceAs (SheafOfModules.IsFiniteType.{u}
        ((Scheme.Modules.pullback (reesFst I f)).obj M))⟩
  have : (ShortComplex.kernelSequence
      (Abelian.factorThruImage (reesUnit I f M))).X₂.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback (reesFst I f)).obj M).IsQuasicoherent
  have : (ShortComplex.kernelSequence
      (Abelian.factorThruImage (reesUnit I f M))).X₃.IsQuasicoherent :=
    isQuasicoherent_reesSheaf I f M
  have : (ShortComplex.kernelSequence
      (Abelian.factorThruImage (reesUnit I f M))).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS
  exact isCoherent_X₃_of_shortExact hS

end Instances

section Maps

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]

/-- Multiplication by `b` in the Rees algebra, on `q_{B*}(⊕ Iᵐ M tᵐ)`. -/
noncomputable def reesMul (b : reesAlgebra I) :
    (reesPush I f M).toAbSheaf ⟶ (reesPush I f M).toAbSheaf :=
  Scheme.Modules.Hom.toAbSheaf ((Scheme.Modules.pushforward (reesFst I f)).map
    ((reesSheaf I f M).smulEnd ((reesSnd I f).specStructureRingHom b)))

omit [IsNoetherianRing A] in
lemma reesSecMap_reesMul {V : X.Opens} (hV : IsAffineOpen V) (b : reesAlgebra I)
    (s : Γ(reesPush I f M, V)) :
    reesSecMap I f M hV ((reesMul I f M b).hom.app (op V) s) =
      (b : A[X]).map (structMap f (V := V)).hom • reesSecMap I f M hV s := by
  have e : (reesMul I f M b).hom.app (op V) s =
      (smulA (reesSheaf I f M) (reesSnd I f) b).app (reesFst I f ⁻¹ᵁ V)
        (@id Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) s) := rfl
  rw [e, smulA_app, reesSecMap_smul]
  congr 1
  exact reesRingMap_structure I f hV b

set_option maxRecDepth 20000 in
lemma reesMul_reesPi_monomial {k : ℕ} {a : A} (ha : a ∈ I ^ k) (b : reesAlgebra I)
    (hb : (b : A[X]) = Polynomial.monomial k a) (j : ℕ) :
    reesMul I f M b ≫ reesPi I f M (j + k) =
      reesPi I f M j ≫ Scheme.Modules.Hom.toAbSheaf (multPow f I M ha) := by
  refine toAbSheaf_hom_ext_affine fun V hV s ↦ app_injective_of_mono' (ιPow f I M (j + k)) V ?_
  have e1 : (reesMul I f M b ≫ reesPi I f M (j + k)).hom.app (op V) s =
      reesPiApp I f M hV (j + k) ((reesMul I f M b).hom.app (op V) s) :=
    (toAbSheaf_comp_app_apply (reesMul I f M b) (reesPi I f M _) V s).trans
      (reesPi_app' I f M hV _ _)
  have e2 : (reesPi I f M j ≫ Scheme.Modules.Hom.toAbSheaf (multPow f I M ha)).hom.app (op V) s =
      (multPow f I M ha).app V (reesPiApp I f M hV j s) :=
    (toAbSheaf_comp_app_apply _ _ V s).trans
      (congrArg ((multPow f I M ha).app V) (reesPi_app I f M hV j s))
  have hL : (ιPow f I M (j + k)).app V
      (reesPiApp I f M hV (j + k) ((reesMul I f M b).hom.app (op V) s)) =
      structMapV f V a • (ιPow f I M j).app V (reesPiApp I f M hV j s) := by
    refine Eq.trans ?_ (congrArg _ (ιPow_reesPiApp I f M hV j s)).symm
    refine (ιPow_reesPiApp I f M hV (j + k) ((reesMul I f M b).hom.app (op V) s)).trans ?_
    refine (congrArg (fun p ↦ PolynomialModule.coeff p (j + k))
      (reesSecMap_reesMul I f M hV b s)).trans ?_
    rw [hb, Polynomial.map_monomial, PolynomialModule.monomial_smul_apply]
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
  have hR : (ιPow f I M (j + k)).app V ((multPow f I M ha).app V (reesPiApp I f M hV j s)) =
      structMapV f V a • (ιPow f I M j).app V (reesPiApp I f M hV j s) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, multPow_ιPow,
      Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulA_app]
  exact (congrArg ((ιPow f I M (j + k)).app V) e1).trans
    (hL.trans (hR.symm.trans (congrArg ((ιPow f I M (j + k)).app V) e2).symm))

set_option maxRecDepth 20000 in
lemma reesMul_reesPi_monomial_of_lt {k : ℕ} {a : A} (b : reesAlgebra I)
    (hb : (b : A[X]) = Polynomial.monomial k a) {m : ℕ} (hm : m < k) :
    reesMul I f M b ≫ reesPi I f M m = 0 := by
  refine toAbSheaf_hom_ext_affine fun V hV s ↦ app_injective_of_mono' (ιPow f I M m) V ?_
  have e1 : (reesMul I f M b ≫ reesPi I f M m).hom.app (op V) s =
      reesPiApp I f M hV m ((reesMul I f M b).hom.app (op V) s) :=
    (toAbSheaf_comp_app_apply (reesMul I f M b) (reesPi I f M _) V s).trans
      (reesPi_app' I f M hV _ _)
  have hL : (ιPow f I M m).app V
      (reesPiApp I f M hV m ((reesMul I f M b).hom.app (op V) s)) =
      0 := by
    refine (ιPow_reesPiApp I f M hV m ((reesMul I f M b).hom.app (op V) s)).trans ?_
    refine (congrArg (fun p ↦ PolynomialModule.coeff p m)
      (reesSecMap_reesMul I f M hV b s)).trans ?_
    rw [hb, Polynomial.map_monomial, PolynomialModule.monomial_smul_apply]
    simp only [show ¬ k ≤ m by omega, ↓reduceIte]
  exact (congrArg ((ιPow f I M m).app V) e1).trans (hL.trans (map_zero _).symm)

/-- The sections of `q_{B*}(⊕ Iᵐ M tᵐ)` over an affine open have bounded support. -/
lemma exists_reesPi_eq_zero {V : X.Opens} (hV : IsAffineOpen V) (s : Γ(reesPush I f M, V)) :
    ∃ N, ∀ p, N < p → (reesPi I f M p).hom.app (op V) s = 0 := by
  classical
  refine ⟨(reesSecMap I f M hV s).coeff.support.sup id, fun p hp ↦ ?_⟩
  apply app_injective_of_mono' (ιPow f I M p) V
  rw [reesPi_app I f M hV, ιPow_reesPiApp]
  refine Eq.trans ?_ (map_zero _).symm
  rw [← Finsupp.notMem_support_iff]
  intro h
  exact absurd (Finset.le_sup (f := id) h) (not_le.mpr hp)

end Maps

section Support

variable {X : Scheme.{u}}

/-- **Cohomology classes have bounded support.** Let `πₘ : F ⟶ Gₘ` be morphisms of abelian
sheaves between quasi-coherent modules on a quasi-compact scheme with affine diagonal such that
every section of `F` over an affine open is killed by all but finitely many `πₘ`. Then every
class in `H^q(X, F)` is killed by all but finitely many `H^q(πₘ)`. (Computed by a Čech complex
of a finite affine cover, on which only finitely many sections occur.) -/
lemma exists_H'_map_eq_zero [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {F : X.Modules} [F.IsQuasicoherent] {G : ℕ → X.Modules} [∀ m, (G m).IsQuasicoherent]
    (π : ∀ m, F.toAbSheaf ⟶ (G m).toAbSheaf)
    (hπ : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V),
      ∃ N, ∀ m, N < m → (π m).hom.app (op V) s = 0)
    (q : ℕ) (h : F.H q) :
    ∃ N, ∀ m, N < m → CategoryTheory.Sheaf.H'.map (π m) q ⊤ h = 0 := by
  classical
  obtain ⟨n, U, hcov, hU⟩ := exists_cechCover X
  let hLF : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) U F.toAbSheaf :=
    ⟨fun x q ↦ F.H'_subsingleton_of_isAffineOpen (hU x) q⟩
  let hLG (m : ℕ) : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) U (G m).toAbSheaf :=
    ⟨fun x q ↦ (G m).H'_subsingleton_of_isAffineOpen (hU x) q⟩
  let eF := TopCat.Sheaf.cechHomologyIso q F.toAbSheaf hLF
  -- move to `⨆ i, U i`
  obtain ⟨h', rfl⟩ : ∃ h' : F.H' q (⨆ i, U i), h = H'CongrOpens F q hcov h' :=
    ⟨(H'CongrOpens F q hcov).symm h, by rw [LinearEquiv.apply_symm_apply]⟩
  obtain ⟨c, rfl⟩ : ∃ c, h' = eF.hom c := ⟨eF.inv h', by rw [← ConcreteCategory.comp_apply,
    Iso.inv_hom_id, ConcreteCategory.id_apply]⟩
  have hπsurj : Function.Surjective
      ((cechComplex U F.toAbSheaf.obj).homologyπ q) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπsurj c
  -- a bound for the finitely many components of the cocycle
  let z' := (cechComplex U F.toAbSheaf.obj).iCycles q z
  have hN : ∀ x : Fin (q + 1) → Fin n, ∃ N, ∀ m, N < m →
      (π m).hom.app (op (cechOpen U x)) (@id (CechCochain U F.toAbSheaf.obj q) z' x) = 0 :=
    fun x ↦ hπ _ (hU x) _
  choose N hN using hN
  refine ⟨Finset.univ.sup N, fun m hm ↦ ?_⟩
  have hz : (cechComplexMap U (π m).hom).f q z' = 0 := by
    funext x
    exact hN x m (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ x)) hm)
  have hcyc : HomologicalComplex.cyclesMap (cechComplexMap U (π m).hom) q z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective
      ((cechComplex U (G m).toAbSheaf.obj).iCycles q)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      map_zero]
    exact hz
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.cechHomologyIso_naturality q hLF (hLG m) (π m))
    ((cechComplex U F.toAbSheaf.obj).homologyπ q z)
  have h1 : (HomologicalComplex.homologyMap (cechComplexMap U (π m).hom) q)
      ((cechComplex U F.toAbSheaf.obj).homologyπ q z) = 0 := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply, hcyc, map_zero]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h1, map_zero] at hnat
  rw [← H'CongrOpens_map]
  exact (congrArg (H'CongrOpens (G m) q hcov) hnat.symm).trans (map_zero _)

end Support

end AlgebraicGeometry.CohomologyAux
