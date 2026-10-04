/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.Henselian
import SGA.SGA1.ExposeX.SpecializationGeometric
import SGA.SGA1.ExposeX.TameLifting
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeXIII.ProperHomotopySequence

/-!
# SGA 1, Exposé X, 3.8: from coverings to fundamental groups

The proof of X.3.8 in SGA is about coverings: a principal covering of `X_η̄` whose group has order
prime to `p` comes from a covering of `X` (X.3.7). This file translates such a statement into the
group-theoretic form `FactorsPrimeTo` used in `TameLiftingDVRStatement`.

* `factorsPrimeTo_of_forall_ker_le`: for a continuous surjection `sp : G₁ → G₀` of a compact group
  onto a Hausdorff group, `FactorsPrimeTo sp q` holds as soon as the kernel of `sp` lies in the
  kernel of every continuous homomorphism of `G₁` to a finite group of order prime to `q`.
* `factorsPrimeTo_autHom_of_forall_isGalois`: for a functor `H : C ⥤ C'` of Galois categories
  compatible with fibre functors and inducing a surjection `Aut F' → Aut F`, `FactorsPrimeTo`
  holds for that surjection if every Galois object of `C'` whose fibre has cardinality prime to
  `q` is isomorphic to the image of an object of `C`.
* `surjective_map_fst_of_isSepClosed_residueField`: over a complete local base with separably
  closed residue field, `π₁(X_s̄) → π₁(X)` is surjective (X.1.4, `π₁` of the base being trivial).
* `factorsPrimeTo_of_forall_isGalois`: hence `TameLiftingDVRStatement` reduces to a statement on
  Galois coverings of `X_η̄`.
-/

universe u u₁ u₂ u₃ u₄ w

open CategoryTheory Limits PreGaloisCategory

namespace SGA.SGA1.ExposeX

section Group

variable {G₁ : Type u} {G₀ : Type*} [Group G₁] [TopologicalSpace G₁] [CompactSpace G₁]
  [Group G₀] [TopologicalSpace G₀] [T2Space G₀]

/-- If `sp : G₁ → G₀` is a continuous surjection of a compact group onto a Hausdorff group whose
kernel lies in the kernel of every continuous homomorphism of `G₁` into a finite group of order
prime to `q`, then every such homomorphism factors through `sp` (X.3.8 in the form
`FactorsPrimeTo`). -/
theorem factorsPrimeTo_of_forall_ker_le {sp : G₁ →* G₀} (hc : Continuous sp)
    (hs : Function.Surjective sp) (q : ℕ)
    (h : ∀ (Q : Type u) [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
      (Nat.card Q).Coprime q → ∀ φ : G₁ →* Q, Continuous φ → sp.ker ≤ φ.ker) :
    FactorsPrimeTo sp q := by
  intro Q _ _ _ _ hQ φ hφ
  let e : G₁ ⧸ sp.ker ≃* G₀ := QuotientGroup.quotientKerEquivOfSurjective sp hs
  let g : G₀ →* Q := (QuotientGroup.lift sp.ker φ (h Q hQ φ hφ)).comp e.symm.toMonoidHom
  have hg : g.comp sp = φ := by
    ext x
    change QuotientGroup.lift sp.ker φ (h Q hQ φ hφ) (e.symm (sp x)) = φ x
    have : e.symm (sp x) = (x : G₁ ⧸ sp.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this, QuotientGroup.lift_mk]
  have hq : Topology.IsQuotientMap sp :=
    hc.isClosedMap.isQuotientMap hc hs
  refine ⟨g, ?_, hg⟩
  rw [hq.continuous_iff]
  change Continuous (g.comp sp)
  rw [hg]
  exact hφ

end Group

section Galois

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

variable {C' : Type u₃} [Category.{u₄} C'] [GaloisCategory C'] {F' : C' ⥤ FintypeCat.{w}}
  [FiberFunctor F'] (H : C ⥤ C') (v : H ⋙ F' ≅ F)

omit [GaloisCategory C] [FiberFunctor F] in
/-- The Galois-category step of the proof of X.3.8: if `H : C ⥤ C'` (with `H ⋙ F' ≅ F`) induces a
surjection `Aut F' → Aut F`, and every Galois object of `C'` whose fibre has cardinality prime to
`q` is isomorphic to `H X` for some `X`, then every continuous homomorphism of `Aut F'` to a
finite group of order prime to `q` factors through `Aut F' → Aut F`. -/
theorem factorsPrimeTo_autHom_of_forall_isGalois
    (hs : Function.Surjective (ExposeXIII.autHom H v)) (q : ℕ)
    (h : ∀ Z : C', IsGalois Z → (Nat.card (F'.obj Z)).Coprime q →
      ∃ X : C, Nonempty (H.obj X ≅ Z)) :
    FactorsPrimeTo (ExposeXIII.autHom H v) q := by
  refine factorsPrimeTo_of_forall_ker_le (ExposeXIII.continuous_autHom H v) hs q ?_
  intro Q _ _ _ _ hQ φ hφ
  -- the open normal subgroup `ker φ` is the stabilizer of a point of a connected object
  have hopen : IsOpen (φ.ker : Set (Aut F')) := by
    have : (φ.ker : Set (Aut F')) = φ ⁻¹' {1} := rfl
    rw [this]
    exact (isOpen_discrete _).preimage hφ
  obtain ⟨Z, z, hZ, hstab⟩ := ExposeXIII.exists_isConnected_stabilizer_eq F' ⟨φ.ker, hopen⟩
  change MulAction.stabilizer (Aut F') z = φ.ker at hstab
  have : IsGalois Z :=
    (ExposeV.isGalois_iff_normal_stabilizer F' Z z).mpr (by rw [hstab]; infer_instance)
  -- the fibre of `Z` has cardinality `[Aut F' : ker φ] = |φ(Aut F')|`, which divides `|Q|`
  have hcard : Nat.card (F'.obj Z) = φ.ker.index := by
    rw [← hstab, MulAction.index_stabilizer]
    have : MulAction.orbit (Aut F') z = Set.univ := by
      rw [MulAction.orbit_eq_univ]
    rw [this, Set.ncard_univ]
  have hdvd : Nat.card (F'.obj Z) ∣ Nat.card Q := by
    rw [hcard, Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨X, ⟨e⟩⟩ := h Z this (Nat.Coprime.coprime_dvd_left hdvd hQ)
  -- the kernel of `Aut F' → Aut F` fixes the fibre of `H X ≅ Z`
  intro σ hσ
  rw [← hstab, MulAction.mem_stabilizer_iff]
  have hz : F'.map e.hom (F'.map e.inv z) = z := by
    rw [← FintypeCat.comp_apply, ← F'.map_comp, e.inv_hom_id, F'.map_id, FintypeCat.id_apply]
  rw [← hz, mulAction_naturality, ExposeXIII.smul_eq_of_mem_ker H v hσ]

end Galois

section Scheme

open AlgebraicGeometry IsLocalRing

/-- Over a henselian local ring with separably closed residue field, every étale covering is a
finite sum of copies of the base. -/
theorem FEt.exists_iso_sigma_terminal_of_henselianLocalRing (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (E : ExposeV.FEt (Spec (.of A))) :
    ∃ n : ℕ, Nonempty (E ≅ ∐ fun _ : Fin n ↦ ⊤_ (ExposeV.FEt (Spec (.of A)))) := by
  let P := ExposeV.FEt.pullback (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A))))
  have : P.IsEquivalence := isEquivalence_pullback_spec_residueField A
  obtain ⟨n, ⟨i⟩⟩ := ExposeV.FEt.exists_iso_sigma_terminal (ResidueField A) (P.obj E)
  let e := P.asEquivalence
  exact ⟨n, ⟨e.unitIso.app E ≪≫ e.inverse.mapIso i ≪≫ PreservesCoproduct.iso e.inverse _ ≪≫
    Sigma.mapIso fun _ ↦ PreservesTerminal.iso e.inverse⟩⟩

/-- Over a complete local ring `R` with separably closed residue field, `π₁(Spec R)` is trivial at
every geometric point. -/
theorem etaleFundamentalGroup_eq_one_of_isSepClosed_residueField (R : Type u) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (b : Spec (.of Ω) ⟶ Spec (.of R))
    (σ : ExposeV.etaleFundamentalGroup Ω b) : σ = 1 :=
  have := ExposeIX.henselianLocalRing_of_isAdicComplete R
  ExposeV.aut_eq_one_of_forall_iso_sigma_terminal _
    (FEt.exists_iso_sigma_terminal_of_henselianLocalRing R) σ

/-- X.1.4 over a complete local base with separably closed residue field: for `f : X ⟶ Spec R`
proper, flat, with separable connected geometric fibres, `π₁(X_s̄) → π₁(X)` is surjective at
every geometric point `s̄`, since `π₁(Spec R)` is trivial. -/
theorem surjective_map_fst_of_isSepClosed_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyConnected f]
    [GeometricallyReduced f] (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ Spec (.of R)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f s) a) := by
  obtain ⟨-, -, hr⟩ := ExposeXIII.properHomotopyExactSequenceFull f Ω₀ s Ω a
  intro σ
  have hσ : σ ∈ (ExposeXIII.FundamentalGroup.map f (a ≫ pullback.fst f s)).ker :=
    etaleFundamentalGroup_eq_one_of_isSepClosed_residueField R Ω _ _
  rw [← hr] at hσ
  exact hσ

/-- Reduction of X.3.8 to coverings, over a complete local base with separably closed residue
field:
if every Galois covering `Z` of `X_s̄` whose degree is prime to `q` is the inverse image of an étale
covering of `X`, then every continuous homomorphism of `π₁(X_s̄)` into a finite group of order
prime to `q` factors through `π₁(X_s̄) → π₁(X)`. -/
theorem factorsPrimeTo_of_forall_isGalois (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyConnected f]
    [GeometricallyReduced f] (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ Spec (.of R)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) (q : ℕ)
    (h : ∀ Z : ExposeV.FEt (pullback f s), IsGalois Z →
      (Nat.card ((ExposeV.FEt.fiber Ω a).obj Z)).Coprime q →
      ∃ E : ExposeV.FEt X, Nonempty ((ExposeV.FEt.pullback (pullback.fst f s)).obj E ≅ Z)) :
    FactorsPrimeTo (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f s) a) q := by
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : ConnectedSpace ↥(pullback f s) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) s _ _
      (IsPullback.of_hasPullback f s)
  exact factorsPrimeTo_autHom_of_forall_isGalois _ (ExposeV.FEt.pullback (pullback.fst f s))
    (ExposeV.FEt.pullbackFiberIso Ω _ a)
    (surjective_map_fst_of_isSepClosed_residueField R f Ω₀ s Ω a) q h

end Scheme

end SGA.SGA1.ExposeX
