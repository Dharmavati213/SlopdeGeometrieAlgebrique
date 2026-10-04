/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeX.TameLiftingGalois
import SGA.SGA1.ExposeX.TameLiftingKummer
import SGA.SGA1.ExposeX.TameLiftingLocal
import SGA.SGA1.ExposeX.TameLiftingPurity
import SGA.SGA1.ExposeXIII.RootAdjunction


/-!
# SGA 1, Exposé X, 3.8: extending a Galois covering after a Kummer base change

The geometric heart of the proof of X.3.8 (X.3.7–3.8). Let `V` be a discrete valuation ring with
uniformizer `π`, `n` an integer prime to the residue characteristic, `V_n = V[T]/(Tⁿ - π)` and
`f : X ⟶ Spec V` proper and smooth with geometrically connected fibres. Let `Z` be a Galois étale
covering of the generic fibre `U = X[1/π]` with `n` automorphisms (so of degree `n`). Then the
inverse image of `Z` on the generic fibre `Uₙ` of `X_n = X ×_V V_n` extends to an étale covering of
`X_n` (`exists_iso_pullback_adjoinRoot_of_isGalois`).

As in SGA: `X_n` is regular, so by purity (X.3.1,
`SGA.SGA1.ExposeX.finite_etale_fromNormalization_of_isRegularScheme`) it suffices that the
normalization of `X_n` in the covering be étale over the generic points of the closed fibre. On an
affine chart `Spec A'` of `X`, the function field of `Z` is a Galois extension of degree `n` of
that of `X` (`isGalois_op_finiteEtale_of_isGalois`, `isDomain_and_finrank_eq_card_aut_of_isGalois`),
hence tamely ramified over the discrete valuation rings `A'_q` at the generic points `q` of the
closed fibre, with ramification indices dividing `n`, and Abhyankar's lemma X.3.6 applies on the
chart `A' ⊗_V V_n` of `X_n` (`isEtaleAt_integralClosure_of_isGalois`). The extension is the
normalization (`exists_iso_pullback_of_fromNormalization`).

The chart computation uses flat base change for the sections over affine opens in the form of an
arbitrary pullback square (`AlgebraicGeometry.CohomologyAux.isPushout_app_of_isPullback`); working
with abstract pullback squares keeps its elaboration fast.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing Polynomial TensorProduct

namespace SGA.SGA1.ExposeX

section Kummer

variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {π : V}
  [hπ : Fact (Irreducible π)] {n : ℕ} [NeZero n]

local notation "Vn" => AdjoinRoot ((Polynomial.X : V[X]) ^ n - Polynomial.C π)

local notation "gn" => Spec.map (CommRingCat.ofHom (algebraMap V Vn))

set_option maxHeartbeats 400000 in
-- the chart computation below is long: ring structures on the sections of five schemes
set_option backward.isDefEq.respectTransparency false in
/-- The chart computation in `exists_iso_pullback_adjoinRoot_of_isGalois`: on the chart
`pr⁻¹ V'` of `X_n` (`V'` a nonempty affine open of `X`), the normalization of `Γ(X_n, pr⁻¹ V')` in
the covering is étale at the primes over the height-one primes containing `T` (X.3.6). -/
private theorem isEtaleAt_chart (hn : (n : V) ∉ maximalIdeal V) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of V)) [Smooth f] [IsLocallyNoetherian X] [IsIntegral X]
    (hreg : IsRegularScheme X) (U : X.Opens)
    (hU : U = X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv π))) [ConnectedSpace U]
    (Z : ExposeV.FEt U) [PreGaloisCategory.IsGalois Z] (hZ : Nat.card (Aut Z) = n)
    {Xn : Scheme.{u}} (pr : Xn ⟶ X) (fn : Xn ⟶ Spec (.of Vn)) (hsq : IsPullback fn pr gn f)
    (hUn : pr ⁻¹ᵁ U = Xn.basicOpen (fn.appTop ((Scheme.ΓSpecIso (.of Vn)).inv
      (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π)))))
    {W : Scheme.{u}} (w : W ⟶ pr ⁻¹ᵁ U) (fst : W ⟶ Z.left) (hW : IsPullback fst w Z.hom (pr ∣_ U))
    (V' : X.Opens) (hV' : IsAffineOpen V') (hV'ne : (V' : Set X).Nonempty) :
    letI := ((w ≫ (pr ⁻¹ᵁ U).ι).app (pr ⁻¹ᵁ V')).hom.toAlgebra
    ∀ (q : Ideal (integralClosure Γ(Xn, pr ⁻¹ᵁ V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')))
      [q.IsPrime], Xn.presheaf.map (homOfLE le_top).op (fn.appTop ((Scheme.ΓSpecIso (.of Vn)).inv
        (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π)))) ∈
        q.comap (algebraMap Γ(Xn, pr ⁻¹ᵁ V') _) →
      (q.comap (algebraMap Γ(Xn, pr ⁻¹ᵁ V') _)).height = 1 →
      Algebra.IsEtaleAt Γ(Xn, pr ⁻¹ᵁ V') q := by
  intro q _ htq hq1
  classical
  set tV : Γ(Xn, pr ⁻¹ᵁ V') := Xn.presheaf.map (homOfLE le_top).op (fn.appTop
    ((Scheme.ΓSpecIso (.of Vn)).inv (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n -
      Polynomial.C π)))) with htV
  have : Nonempty V' := hV'ne.to_subtype
  have : IsFinite gn := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat gn := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : IsFinite pr := MorphismProperty.of_isPullback hsq ‹_›
  have : Flat pr := MorphismProperty.of_isPullback hsq ‹_›
  have : IsFinite Z.hom := Z.prop.1
  have : Etale Z.hom := Z.prop.2
  have hcond : fn ≫ gn = pr ≫ f := hsq.w
  have hnat' : CommRingCat.ofHom (algebraMap V Vn) ≫ (Scheme.ΓSpecIso (.of Vn)).inv =
      (Scheme.ΓSpecIso (.of V)).inv ≫ (gn).appTop := by
    rw [Iso.comp_inv_eq, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have : ConnectedSpace Z.left := (ExposeV.FEt.isConnected_iff_connectedSpace Z).mp inferInstance
  obtain ⟨z⟩ : Nonempty Z.left := inferInstance
  have ht : Xn.basicOpen tV = pr ⁻¹ᵁ V' ⊓ pr ⁻¹ᵁ U := by
    rw [htV, Scheme.basicOpen_res, hUn]
  have : Nonempty V' := hV'ne.to_subtype
  -- the chart `A' = Γ(X, V')` of `X`, smooth over `V`
  let : Algebra V Γ(X, V') :=
    ((f.appLE ⊤ V' le_top).hom.comp (Scheme.ΓSpecIso (.of V)).inv.hom).toAlgebra
  have : Algebra.Smooth V Γ(X, V') := by
    rw [← RingHom.smooth_algebraMap]
    exact RingHom.Smooth.comp
      (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩
        ⟨V', hV'⟩ le_top)
  -- the chart `A = Γ(Xn, pr⁻¹ V') = A' ⊗_V Vn` of `Xn`
  let : Algebra Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V') := (pr.app V').hom.toAlgebra
  let : Algebra Vn Γ(Xn, pr ⁻¹ᵁ V') :=
    ((fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top).hom.comp (Scheme.ΓSpecIso (.of Vn)).inv.hom).toAlgebra
  let : Algebra V Γ(Xn, pr ⁻¹ᵁ V') :=
    ((algebraMap Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V')).comp
      (algebraMap V Γ(X, V'))).toAlgebra
  have : IsScalarTower V Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V') :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hnat : (gn).appTop ≫ (Scheme.ΓSpecIso (.of Vn)).hom =
      (Scheme.ΓSpecIso (.of V)).hom ≫ CommRingCat.ofHom (algebraMap V Vn) :=
    Scheme.ΓSpecIso_naturality _
  have hcomp1 : f.appLE ⊤ V' le_top ≫ pr.app V' = (pr ≫ f).appLE ⊤ (pr ⁻¹ᵁ V') le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hcomp2 : (gn).appTop ≫ fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top =
      (fn ≫ gn).appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
    (Scheme.Hom.comp_appLE fn gn ⊤ (pr ⁻¹ᵁ V') le_top).symm
  have key : (Scheme.ΓSpecIso (.of V)).inv ≫ f.appLE ⊤ V' le_top ≫ pr.app V' =
      CommRingCat.ofHom (algebraMap V Vn) ≫ (Scheme.ΓSpecIso (.of Vn)).inv ≫
        fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
    calc (Scheme.ΓSpecIso (.of V)).inv ≫ f.appLE ⊤ V' le_top ≫ pr.app V'
        = (Scheme.ΓSpecIso (.of V)).inv ≫ (pr ≫ f).appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
          congrArg _ hcomp1
      _ = (Scheme.ΓSpecIso (.of V)).inv ≫ (fn ≫ gn).appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
          congrArg _ (Scheme.Hom.appLE_congr_hom hcond.symm _ _ _ _)
      _ = (Scheme.ΓSpecIso (.of V)).inv ≫ (gn).appTop ≫ fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
          congrArg _ hcomp2.symm
      _ = ((Scheme.ΓSpecIso (.of V)).inv ≫ (gn).appTop) ≫ fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom (algebraMap V Vn) ≫ (Scheme.ΓSpecIso (.of Vn)).inv) ≫
          fn.appLE ⊤ (pr ⁻¹ᵁ V') le_top := congrArg (· ≫ _) hnat'.symm
      _ = _ := Category.assoc _ _ _
  have : IsScalarTower V Vn Γ(Xn, pr ⁻¹ᵁ V') := .of_algebraMap_eq fun v ↦
    congrArg (fun φ : CommRingCat.of V ⟶ Γ(Xn, pr ⁻¹ᵁ V') ↦ φ v) key
  have : Algebra.IsPushout V Γ(X, V') Vn Γ(Xn, pr ⁻¹ᵁ V') := by
    have h := CohomologyAux.isPushout_app_of_isPullback hsq (isAffineOpen_top _) hV'
      (le_top.trans_eq (Scheme.Hom.preimage_top f).symm)
    have h' : IsPushout (CommRingCat.ofHom (algebraMap V Γ(X, V')))
        (CommRingCat.ofHom (algebraMap V Vn))
        (CommRingCat.ofHom (algebraMap Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V')))
        (CommRingCat.ofHom (algebraMap Vn Γ(Xn, pr ⁻¹ᵁ V'))) := by
      refine h.flip.of_iso (Scheme.ΓSpecIso (.of V)) (Iso.refl _) (Scheme.ΓSpecIso (.of Vn))
        (Iso.refl _) ?_ ?_ ?_ ?_
      · ext x
        simp [RingHom.algebraMap_toAlgebra]
      · exact hnat
      · rfl
      · ext x
        simp [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.isPushout_iff_isPushout.mp h'
  -- `π` is nonzero in the domain `A'`
  have hπ0 : algebraMap V Γ(X, V') π ≠ 0 := by
    have : Module.IsTorsionFree V Γ(X, V') := inferInstance
    exact (map_ne_zero_iff _ (Module.isTorsionFree_iff_algebraMap_injective.mp this)).mpr
      hπ.out.ne_zero
  have : IsNoetherianRing Γ(X, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  have : IsRegularRing Γ(X, V') :=
    ExposeII.isRegularRing_of_isRegularLocalRing_stalk hV' fun x ↦ hreg x
  have : IsIntegrallyClosed Γ(X, V') := IsRegularRing.isIntegrallyClosed
  -- the chart `A'π = Γ(U, U ∩ V') = A'[1/π]` of the generic fibre
  have hUV' : U.ι ''ᵁ U.ι ⁻¹ᵁ V' = X.basicOpen (algebraMap V Γ(X, V') π) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hU]
    change _ = X.basicOpen (X.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (.of V)).inv π)))
    rw [Scheme.basicOpen_res, inf_comm]
  let : Algebra Γ(X, V') Γ(U, U.ι ⁻¹ᵁ V') := (U.ι.app V').hom.toAlgebra
  have : IsLocalization.Away (algebraMap V Γ(X, V') π) Γ(U, U.ι ⁻¹ᵁ V') :=
    hV'.isLocalization_of_eq_basicOpen _ (homOfLE (Set.image_preimage_subset _ _)) hUV'
  have hUV'aff : IsAffineOpen (U.ι ⁻¹ᵁ V') := by
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, hUV']
    exact hV'.basicOpen _
  have hpowle : Submonoid.powers (algebraMap V Γ(X, V') π) ≤ nonZeroDivisors Γ(X, V') :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hπ0
  have : IsDomain Γ(U, U.ι ⁻¹ᵁ V') :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hpowle
  have : IsIntegrallyClosed Γ(U, U.ι ⁻¹ᵁ V') :=
    isIntegrallyClosed_of_isLocalization _ _ hpowle
  have : IsNoetherianRing Γ(U, U.ι ⁻¹ᵁ V') :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap V Γ(X, V') π)) _
      inferInstance
  -- the chart `W₀ = Γ(Z, Z⁻¹(U ∩ V'))` of the covering `Z` of the generic fibre
  have : IsFinite Z.hom := Z.prop.1
  have : Etale Z.hom := Z.prop.2
  let : Algebra Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') :=
    (Z.hom.app (U.ι ⁻¹ᵁ V')).hom.toAlgebra
  let : Algebra Γ(X, V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') :=
    ((algebraMap Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')).comp
      (algebraMap Γ(X, V') Γ(U, U.ι ⁻¹ᵁ V'))).toAlgebra
  have : IsScalarTower Γ(X, V') Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') :=
    Z.hom.finite_app _ hUV'aff
  have : Algebra.Etale Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') := by
    rw [← RingHom.etale_algebraMap]
    change (Z.hom.app _).hom.Etale
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Etale) Z.hom inferInstance ⟨_, hUV'aff⟩
      ⟨_, hUV'aff.preimage Z.hom⟩ le_rfl
  -- `Z` is integral and meets the chart, so `W₀` is a domain
  have : IsLocallyNoetherian Z.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.hom ≫ U.ι ≫ f)
  have : IsIntegral Z.left :=
    isIntegral_of_isRegularScheme (isRegularScheme_of_smooth V (Z.hom ≫ U.ι ≫ f))
  have hZsurj : Function.Surjective Z.hom := by
    have hcl : IsClosed (Set.range Z.hom : Set U) := Z.hom.isClosedMap.isClosed_range
    have hop : IsOpen (Set.range Z.hom : Set U) :=
      (isOpenMap_of_generalizingMap Z.hom (Flat.generalizingMap Z.hom)).isOpen_range
    exact Set.range_eq_univ.mp ((isClopen_iff.mp ⟨hcl, hop⟩).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, z, rfl⟩))
  have : Nonempty (Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') := by
    obtain ⟨x, hxV', hxU⟩ := nonempty_preirreducible_inter V'.isOpen U.isOpen hV'ne
      ⟨U.ι (Z.hom z), (Z.hom z).2⟩
    obtain ⟨z', hz'⟩ := hZsurj ⟨x, hxU⟩
    exact ⟨z', show U.ι (Z.hom z') ∈ V' by rw [hz']; exact hxV'⟩
  -- `W₀` is generically Galois of degree `n`
  have hgal (K : Type u) [Field K] [Algebra Γ(U, U.ι ⁻¹ᵁ V') K]
      [IsFractionRing Γ(U, U.ι ⁻¹ᵁ V') K] :
      IsDomain (K ⊗[Γ(U, U.ι ⁻¹ᵁ V')] Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')) ∧
        Module.finrank K (K ⊗[Γ(U, U.ι ⁻¹ᵁ V')] Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')) = n ∧
        Module.finrank K (K ⊗[Γ(U, U.ι ⁻¹ᵁ V')] Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')) ≤
          Nat.card ((K ⊗[Γ(U, U.ι ⁻¹ᵁ V')] Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')) ≃ₐ[K]
            (K ⊗[Γ(U, U.ι ⁻¹ᵁ V')] Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V'))) := by
    obtain ⟨hG, hcard⟩ := isGalois_op_finiteEtale_of_isGalois Z hUV'aff rfl
    obtain ⟨h1, h2, h3⟩ := isDomain_and_finrank_eq_card_aut_of_isGalois
      (CommAlgCat.FiniteEtale.of Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')) K
    exact ⟨h1, h2.trans (hcard.trans hZ), h3⟩
  -- the chart `Wc = Γ(W, (w ≫ ι)⁻¹ pr⁻¹ V')` of the pulled back covering
  have hmor : fst ≫ Z.hom ≫ U.ι = w ≫ (pr ⁻¹ᵁ U).ι ≫ pr := by
    rw [← Category.assoc, hW.w, Category.assoc, morphismRestrict_ι]
  have hO : (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V' ≤
      fst ⁻¹ᵁ Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V' :=
    (congrArg (fun φ : W ⟶ X ↦ φ ⁻¹ᵁ V') hmor).symm.le
  let : Algebra Γ(Xn, pr ⁻¹ᵁ V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
    ((w ≫ (pr ⁻¹ᵁ U).ι).app (pr ⁻¹ᵁ V')).hom.toAlgebra
  let : Algebra Γ(X, V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
    ((algebraMap Γ(Xn, pr ⁻¹ᵁ V')
      Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')).comp
      (algebraMap Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V'))).toAlgebra
  have : IsScalarTower Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V')
      Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
      Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
    ((fst).appLE _ _ hO).hom.toAlgebra
  have hWsq : pr.app V' ≫ (w ≫ (pr ⁻¹ᵁ U).ι).app (pr ⁻¹ᵁ V') =
      U.ι.app V' ≫ Z.hom.app (U.ι ⁻¹ᵁ V') ≫ (fst).appLE _ _ hO := by
    have e1 : ((w ≫ (pr ⁻¹ᵁ U).ι) ≫ pr).appLE V' ((w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') le_rfl =
        pr.app V' ≫ (w ≫ (pr ⁻¹ᵁ U).ι).appLE (pr ⁻¹ᵁ V') _ le_rfl :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have e2 : ((fst ≫ Z.hom) ≫ U.ι).appLE V'
        ((w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') hO =
        U.ι.app V' ≫ (fst ≫ Z.hom).appLE (U.ι ⁻¹ᵁ V') _ hO :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have e3 : (fst ≫ Z.hom).appLE (U.ι ⁻¹ᵁ V') _ hO =
        Z.hom.app _ ≫ (fst).appLE _ _ hO :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    have e4 : (w ≫ (pr ⁻¹ᵁ U).ι).appLE (pr ⁻¹ᵁ V') _ le_rfl =
        (w ≫ (pr ⁻¹ᵁ U).ι).app (pr ⁻¹ᵁ V') := Scheme.Hom.appLE_eq_app _
    have hmor' : (w ≫ (pr ⁻¹ᵁ U).ι) ≫ pr = (fst ≫ Z.hom) ≫ U.ι := by
      simp only [Category.assoc]
      exact hmor.symm
    exact (e1.trans (congrArg (fun φ ↦ pr.app V' ≫ φ) e4)).symm.trans
      ((Scheme.Hom.appLE_congr_hom hmor' _ _ _ _).trans
        (e2.trans (congrArg (fun φ ↦ U.ι.app V' ≫ φ) e3)))
  have : IsScalarTower Γ(X, V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
      Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') := .of_algebraMap_eq fun a ↦
    (congrArg (fun φ : Γ(X, V') ⟶ _ ↦ φ a) hWsq : _)
  have hgen : ∀ c : Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V'),
      c ∈ Algebra.adjoin Γ(Xn, pr ⁻¹ᵁ V')
        (Set.range (algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
          Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V'))) := by
    -- `T` is a unit in `Wc`, with inverse in `A[W₀]`
    have hπu := IsLocalization.Away.algebraMap_isUnit (S := Γ(U, U.ι ⁻¹ᵁ V'))
      (algebraMap V Γ(X, V') π)
    have ht0 : tV = algebraMap Vn Γ(Xn, pr ⁻¹ᵁ V')
        (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π)) := rfl
    have hr : AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π) ^ n =
        algebraMap V Vn π := ExposeXIII.root_X_pow_sub_C_pow π n
    have ht' : (algebraMap Vn Γ(Xn, pr ⁻¹ᵁ V')
        (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π))) ^ n =
        algebraMap Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V') (algebraMap V Γ(X, V') π) :=
      (map_pow _ _ _).symm.trans ((congrArg _ hr).trans
        (IsScalarTower.algebraMap_apply V Vn Γ(Xn, pr ⁻¹ᵁ V') π).symm)
    have hpi : algebraMap Γ(Xn, pr ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')
        (algebraMap Γ(X, V') Γ(Xn, pr ⁻¹ᵁ V') (algebraMap V Γ(X, V') π)) =
        algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')
          (algebraMap Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
            (algebraMap Γ(X, V') Γ(U, U.ι ⁻¹ᵁ V') (algebraMap V Γ(X, V') π))) :=
      IsScalarTower.algebraMap_apply Γ(X, V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') _
    let τ := algebraMap Γ(Xn, pr ⁻¹ᵁ V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')
      (algebraMap Vn Γ(Xn, pr ⁻¹ᵁ V')
        (AdjoinRoot.root ((Polynomial.X : V[X]) ^ n - Polynomial.C π)))
    let u := algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
      Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')
      (algebraMap Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') ↑hπu.unit⁻¹)
    have e1 : τ ^ n = algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')
          (algebraMap Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
            (algebraMap Γ(X, V') Γ(U, U.ι ⁻¹ᵁ V') (algebraMap V Γ(X, V') π))) :=
      (map_pow _ _ _).symm.trans ((congrArg _ ht').trans hpi)
    have hτn : τ ^ n * u = 1 :=
      (congrArg (· * u) e1).trans ((map_mul _ _ _).symm.trans
        ((congrArg _ (map_mul _ _ _).symm).trans
          ((congrArg _ (congrArg _ hπu.mul_val_inv)).trans
            ((congrArg _ (map_one _)).trans (map_one _)))))
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have hττ : τ * τ ^ (n - 1) = τ ^ n :=
      (pow_succ' τ (n - 1)).symm.trans (congrArg (τ ^ ·) hn1)
    have hτu : τ * (τ ^ (n - 1) * u) = 1 :=
      (mul_assoc _ _ _).symm.trans ((congrArg (· * u) hττ).trans hτn)
    have hτ' : τ ^ (n - 1) * u ∈
        Algebra.adjoin Γ(Xn, pr ⁻¹ᵁ V')
          (Set.range (algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
            Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V'))) :=
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _)
        (Algebra.subset_adjoin ⟨_, rfl⟩)
    -- `Aπ = Γ(Uₙ, Uₙ ∩ pr⁻¹ V') = A[1/T]`, and `Wc = W₀ ⊗_{A'π} Aπ`
    have hVb : (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V' ≤ (pr ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V' :=
      (congrArg (fun φ : (pr ⁻¹ᵁ U).toScheme ⟶ X ↦ φ ⁻¹ᵁ V')
        (morphismRestrict_ι pr U)).symm.le
    have hVbe : (pr ⁻¹ᵁ U).ι ''ᵁ (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V' =
        Xn.basicOpen (tV) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, ht,
        inf_comm]
    have hVbaff : IsAffineOpen ((pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V') := by
      rw [← (pr ⁻¹ᵁ U).ι.isAffineOpen_iff_of_isOpenImmersion, hVbe]
      exact (hV'.preimage pr).basicOpen _
    have : Flat (pr ∣_ U) := inferInstance
    have h := CohomologyAux.isPushout_app_of_isPullback hW hUV'aff hVbaff hVb
    let : Algebra Γ(U, U.ι ⁻¹ᵁ V') Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      ((pr ∣_ U).appLE _ _ hVb).hom.toAlgebra
    let : Algebra Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      (w.app ((pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')).hom.toAlgebra
    let : Algebra Γ(U, U.ι ⁻¹ᵁ V') Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      ((algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')).comp
        (algebraMap Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V'))).toAlgebra
    have : IsScalarTower Γ(U, U.ι ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') := .of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower Γ(U, U.ι ⁻¹ᵁ V') Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      .of_algebraMap_eq fun a ↦ congrArg (fun φ ↦ φ a) h.w
    have hpush : Algebra.IsPushout Γ(U, U.ι ⁻¹ᵁ V')
        Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V') Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      CommRingCat.isPushout_iff_isPushout.mp h.flip
    -- `Wc` is generated over `Aπ` by the image of `W₀`
    have h1 (c : Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')) :
        c ∈ Algebra.adjoin Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
          (Set.range (algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
            Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V'))) :=
      hpush.out.inductionOn c _ (Subalgebra.zero_mem _)
        (fun m ↦ Algebra.subset_adjoin ⟨m, rfl⟩) (fun s n hn ↦ Subalgebra.smul_mem _ hn s)
        (fun _ _ ↦ Subalgebra.add_mem _)
    -- `Aπ = A[1/T]`
    let : Algebra Γ(Xn, pr ⁻¹ᵁ V') Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      ((pr ⁻¹ᵁ U).ι.app (pr ⁻¹ᵁ V')).hom.toAlgebra
    have : IsLocalization.Away (tV)
        Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V') :=
      (hV'.preimage pr).isLocalization_of_eq_basicOpen _
        (homOfLE (hVbe.le.trans (Xn.basicOpen_le _))) hVbe
    have : IsScalarTower Γ(Xn, pr ⁻¹ᵁ V') Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') := .of_algebraMap_eq fun _ ↦ rfl
    -- `T` is a unit in `Wc`, with inverse in `A[W₀]`
    have h2 (y : Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')) :
        algebraMap Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
          Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') y ∈
        Algebra.adjoin Γ(Xn, pr ⁻¹ᵁ V')
          (Set.range (algebraMap Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V')
            Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V'))) := by
      obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hy⟩ :=
        IsLocalization.surj (Submonoid.powers (tV)) y
      have hy' := congrArg (algebraMap Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
        Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V')) hy
      rw [map_mul, map_pow, map_pow] at hy'
      have hy'' : algebraMap Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
          Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') y * τ ^ k =
          algebraMap Γ(Xn, pr ⁻¹ᵁ V')
            Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') a := hy'
      have key : algebraMap Γ(pr ⁻¹ᵁ U, (pr ⁻¹ᵁ U).ι ⁻¹ᵁ pr ⁻¹ᵁ V')
          Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') y =
          algebraMap Γ(Xn, pr ⁻¹ᵁ V')
            Γ(W, (w ≫ (pr ⁻¹ᵁ U).ι) ⁻¹ᵁ pr ⁻¹ᵁ V') a * (τ ^ (n - 1) * u) ^ k :=
        (mul_one _).symm.trans ((congrArg (_ * ·) ((one_pow k).symm.trans
          (congrArg (· ^ k) hτu.symm))).trans ((congrArg (_ * ·) (mul_pow τ _ k)).trans
            ((mul_assoc _ _ _).symm.trans (congrArg (· * _) hy''))))
      rw [key]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hτ' _)
    intro c
    induction h1 c using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap r => exact h2 r
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  -- the prime `q'` of `A'` below `q`: a generic point of the closed fibre
  have htq' : algebraMap Vn Γ(Xn, pr ⁻¹ᵁ V') (AdjoinRoot.root _) ∈
      q.comap (algebraMap Γ(Xn, pr ⁻¹ᵁ V') _) := htq
  have hq' := comap_mem_minimalPrimes_of_height_eq_one (A' := Γ(X, V')) hπ0 _ htq' hq1
  exact isEtaleAt_integralClosure_of_isGalois hn _ hq' Γ(U, U.ι ⁻¹ᵁ V')
    Γ(Z.left, Z.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V') hgal _ hgen q le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extension step of the proof of X.3.8 (by X.3.6 and X.3.1; the core statement is
`TameLiftingDVRStatement`): let `V` be a discrete valuation ring with
uniformizer `π`, `n` prime to the residue characteristic, `f : X ⟶ Spec V` proper and smooth with
geometrically connected fibres, `U = X[1/π]` its generic fibre and `Z` a Galois étale covering of
`U` with `n` automorphisms. After the Kummer base change `V_n = V[T]/(Tⁿ - π)`, the inverse image of
`Z` on the generic fibre `pr⁻¹ U` of `X_n = Spec V_n ×_V X` is the restriction of an étale covering
`E` of `X_n`. (The residue field and the completeness of `V` play no role here.) -/
theorem exists_iso_pullback_adjoinRoot_of_isGalois (hn : (n : V) ∉ maximalIdeal V) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of V)) [Smooth f] [IsProper f] [GeometricallyConnected f] (U : X.Opens)
    (hU : U = X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv π))) [ConnectedSpace U]
    (Z : ExposeV.FEt U) [PreGaloisCategory.IsGalois Z] (hZ : Nat.card (Aut Z) = n) :
    ∃ E : ExposeV.FEt (pullback gn f),
      Nonempty ((ExposeV.FEt.pullback (pullback.snd gn f ⁻¹ᵁ U).ι).obj E ≅
        (ExposeV.FEt.pullback (pullback.snd gn f ∣_ U)).obj Z) := by
  classical
  set pr := pullback.snd gn f with hpr
  set fn := pullback.fst gn f with hfn
  -- the Kummer base change `gn : Spec Vn ⟶ Spec V`
  have : IsFinite gn := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat gn := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective gn := by
    have : Module.FaithfullyFlat V Vn := inferInstance
    exact ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2
  have : IsFinite pr := MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective pr := MorphismProperty.pullback_snd _ _ inferInstance
  -- `Xn` is regular and integral
  have : IsLocallyNoetherian (pullback gn f) := LocallyOfFiniteType.isLocallyNoetherian fn
  have hregn : IsRegularScheme (pullback gn f) := isRegularScheme_of_smooth Vn fn
  have : ConnectedSpace ↥(pullback gn f) :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap fn
      (ExposeIX.universally_isQuotientMap_of_universallyClosed fn)
  have : IsIntegral (pullback gn f) := isIntegral_of_isRegularScheme hregn
  -- `X` is regular and integral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hreg : IsRegularScheme X := isRegularScheme_of_smooth V f
  have : ConnectedSpace X :=
    ExposeIX.connectedSpace_of_universally_isQuotientMap f
      (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : IsIntegral X := isIntegral_of_isRegularScheme hreg
  -- the generic fibre `Uₙ = pr⁻¹ U` of `Xn` is the basic open of `T`
  set T : Γ(pullback gn f, ⊤) :=
    fn.appTop ((Scheme.ΓSpecIso (.of Vn)).inv (AdjoinRoot.root _)) with hT
  have hcond : fn ≫ gn = pr ≫ f := pullback.condition
  have hnat' : CommRingCat.ofHom (algebraMap V Vn) ≫ (Scheme.ΓSpecIso (.of Vn)).inv =
      (Scheme.ΓSpecIso (.of V)).inv ≫ (gn).appTop := by
    rw [Iso.comp_inv_eq, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hUn : pr ⁻¹ᵁ U = (pullback gn f).basicOpen T := by
    have hnat0 : (gn).appTop ((Scheme.ΓSpecIso (.of V)).inv π) =
        (Scheme.ΓSpecIso (.of Vn)).inv (algebraMap V Vn π) :=
      (congrArg (fun φ : CommRingCat.of V ⟶ _ ↦ φ π) hnat').symm
    rw [hU, ← Scheme.preimage_basicOpen_top, ← Scheme.Hom.comp_preimage, ← hcond,
      Scheme.Hom.comp_preimage, Scheme.preimage_basicOpen_top, hnat0,
      ← ExposeXIII.root_X_pow_sub_C_pow, map_pow,
      Scheme.basicOpen_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne n)), Scheme.preimage_basicOpen_top]
  -- `U` and `Uₙ` are nonempty
  have : ConnectedSpace Z.left := (ExposeV.FEt.isConnected_iff_connectedSpace Z).mp inferInstance
  obtain ⟨z⟩ : Nonempty Z.left := inferInstance
  have hUne : ((pr ⁻¹ᵁ U : (pullback gn f).Opens) : Set ↥(pullback gn f)).Nonempty := by
    obtain ⟨x, hx⟩ := pr.surjective (U.ι (Z.hom z))
    exact ⟨x, by change pr x ∈ U; rw [hx]; exact (Z.hom z).2⟩
  -- the covering `W` of `Uₙ`
  let W := (ExposeV.FEt.pullback (pr ∣_ U)).obj Z
  let w : W.left ⟶ (pr ⁻¹ᵁ U : (pullback gn f).Opens) := W.hom
  have : IsFinite w := W.prop.1
  have : Etale w := W.prop.2
  -- the charts `pr⁻¹ V'`, `V'` a nonempty affine open of `X`
  let ι := {O : X.Opens // IsAffineOpen O ∧ (O : Set X).Nonempty}
  have hcov : ⨆ i : ι, pr ⁻¹ᵁ i.1 = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨O, hO, hxO, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show pr x ∈ (⊤ : X.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨O, hO, ⟨_, hxO⟩⟩, hxO⟩
  have hne (i : ι) : ((pr ⁻¹ᵁ i.1 : (pullback gn f).Opens) : Set ↥(pullback gn f)).Nonempty := by
    obtain ⟨x, hx⟩ := i.2.2
    obtain ⟨y, hy⟩ := pr.surjective x
    exact ⟨y, by change pr y ∈ i.1; rw [hy]; exact hx⟩
  let t (i : ι) : Γ(pullback gn f, pr ⁻¹ᵁ i.1) :=
    (pullback gn f).presheaf.map (homOfLE le_top).op T
  have ht (i : ι) : (pullback gn f).basicOpen (t i) = pr ⁻¹ᵁ i.1 ⊓ pr ⁻¹ᵁ U := by
    rw [Scheme.basicOpen_res, hUn]
  obtain ⟨hfin, het⟩ := finite_etale_fromNormalization_of_isRegularScheme w hregn hUne
    (fun i : ι ↦ pr ⁻¹ᵁ i.1) (fun i ↦ i.2.1.preimage pr) hne hcov t ht
    (fun i ↦ isEtaleAt_chart hn f hreg U hU Z hZ pr fn (IsPullback.of_hasPullback gn f) hUn
      w (pullback.fst Z.hom (pr ∣_ U)) (IsPullback.of_hasPullback Z.hom (pr ∣_ U)) i.1 i.2.1
      i.2.2)
  obtain ⟨E, ⟨e⟩⟩ := exists_iso_pullback_of_fromNormalization w
  have hw : (Iso.refl W.left).hom ≫ W.hom = w := Category.id_comp _
  exact ⟨E, ⟨e ≪≫ MorphismProperty.Over.isoMk (Iso.refl _) hw⟩⟩

/-- A step of the proof of X.3.8 over a complete discrete valuation ring (the core statement is
`TameLiftingDVRStatement`), from X.3.6, X.3.1 and the comparison `π₁(X_{V_n}) ≅ π₁(X)` used in
X.3.7: let `V` be a complete discrete valuation ring
with uniformizer `π`, `n` prime to the residue characteristic, `f : X ⟶ Spec V` proper and smooth
with geometrically connected fibres, `U = X[1/π]` its generic fibre and `Z` a Galois étale covering
of `U` with `n` automorphisms. Then `Z` becomes, on the generic fibre of
`X_n = Spec V[T]/(Tⁿ - π) ×_V X`, the inverse image of an étale covering `E` of `X` itself. -/
theorem exists_iso_pullback_of_isGalois_of_isAdicComplete [IsAdicComplete (maximalIdeal V) V]
    (hn : (n : V) ∉ maximalIdeal V) {X : Scheme.{u}} (f : X ⟶ Spec (.of V)) [Smooth f]
    [IsProper f] [GeometricallyConnected f] (U : X.Opens)
    (hU : U = X.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv π))) [ConnectedSpace U]
    (Z : ExposeV.FEt U) [PreGaloisCategory.IsGalois Z] (hZ : Nat.card (Aut Z) = n) :
    ∃ E : ExposeV.FEt X,
      Nonempty ((ExposeV.FEt.pullback ((pullback.snd gn f ⁻¹ᵁ U).ι ≫ pullback.snd gn f)).obj E ≅
        (ExposeV.FEt.pullback (pullback.snd gn f ∣_ U)).obj Z) := by
  obtain ⟨En, ⟨e⟩⟩ := exists_iso_pullback_adjoinRoot_of_isGalois hn f U hU Z hZ
  let σ := pullbackSymmetry gn f
  have hσ : σ.hom ≫ pullback.fst f gn = pullback.snd gn f := pullbackSymmetry_hom_comp_fst _ _
  have := isEquivalence_pullback_adjoinRoot π n f
  let P := ExposeV.FEt.pullback (pullback.fst f gn)
  let E := P.objPreimage ((ExposeV.FEt.pullback σ.inv).obj En)
  let eE : P.obj E ≅ (ExposeV.FEt.pullback σ.inv).obj En := P.objObjPreimageIso _
  let i₁ : (ExposeV.FEt.pullback (pullback.snd gn f)).obj E ≅ En :=
    (MorphismProperty.Over.pullbackCongr hσ.symm).app E ≪≫
      (MorphismProperty.Over.pullbackComp σ.hom (pullback.fst f gn)).app E ≪≫
      (ExposeV.FEt.pullback σ.hom).mapIso eE ≪≫
      (MorphismProperty.Over.pullbackComp σ.hom σ.inv).symm.app En ≪≫
      (MorphismProperty.Over.pullbackCongr σ.hom_inv_id).app En ≪≫
      (ExposeV.FEt.pullbackId _).app En
  exact ⟨E, ⟨(MorphismProperty.Over.pullbackComp _ _).app E ≪≫
    (ExposeV.FEt.pullback (pullback.snd gn f ⁻¹ᵁ U).ι).mapIso i₁ ≪≫ e⟩⟩

end Kummer

end SGA.SGA1.ExposeX
